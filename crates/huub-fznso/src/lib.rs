//! The Huub lazy clause generation solver, as an FZnSO solver library.
//!
//! The library is loaded as `huub`, and reads the application's model through
//! the FZnSO interface: nothing is serialised, and nothing of the model is kept
//! beyond the Huub solver its constraints are posted into.
//!
//! # Layers
//!
//! One Huub solver is kept from run to run, so that it keeps what it has
//! learned. The layers the application marks permanent are simplified together
//! as a Huub model before they are lowered. Every other layer is lowered into
//! the solver as its own model, conditioned on a Boolean *activation* literal
//! that the run assumes: retracting the layer adds the negation of that literal
//! as a clause, which leaves every clause learned from the layer satisfied.
//!
//! Huub has no propagator for a global constraint that can be conditioned on a
//! literal, so such a constraint is posted unconditionally. A layer holding one
//! cannot be retracted without undoing it, so retracting it rebuilds the solver
//! from the model instead.

mod declarations;
mod post;

#[cfg(test)]
mod tests;

use std::{
	cell::Cell,
	mem,
	time::{Duration, Instant},
};

use fznso::{
	ConstraintIdx, DecisionIdx, Model, Solution, Solver, SolverType, Status, Value, ValueExt,
	ValueView,
};
use huub_lib::{
	actions::IntDecisionActions,
	solver::{
		self, AnyView, IntLitMeaning, SearchStrategy, SolverStatistics, SwitchTrigger,
		TerminationSignal, Valuation, View,
		branchers::{
			BoolBrancher, DecisionSelection, DomainSelection, IntBrancher, WarmStartBrancher,
		},
	},
};

use crate::post::{PostError, Poster};

/// The value a solution gives a decision.
#[derive(Clone, Copy, Debug)]
#[expect(
	variant_size_differences,
	reason = "an integer cannot be as small as a Boolean"
)]
enum Assigned {
	/// The decision is not one the application asked for.
	Absent,
	/// The value of a Boolean decision.
	Bool(bool),
	/// The value of an integer decision.
	Int(i64),
}

/// A solution reported by [`HuubSolver`].
///
/// Huub hands over a solution only for the duration of a callback, and a value
/// crosses the interface as a reference, so the values the application asked
/// for are copied out when the solution is found.
#[derive(Debug)]
pub struct HuubSolution {
	/// The value of each decision, by index.
	values: Vec<Assigned>,
	/// The value of the objective, if there is one.
	objective: Option<i64>,
	/// How many solutions were reported before this one.
	index: i64,
}

/// The Huub solver, holding the layers of the model it has posted.
#[derive(Debug, Default)]
pub struct HuubSolver {
	/// The options the next run uses.
	options: Options,
	/// The solver holding the posted layers, if any.
	live: Option<Live>,
	/// The search statistics of the solvers that have been rebuilt.
	retired: SolverStatistics,
	/// The statistics as they were at the end of the last run.
	statistics: Statistics,
	/// How many times a solver was built from the model.
	builds: usize,
}

/// A layer of the model that [`Live`] has posted.
#[derive(Debug)]
struct Layer {
	/// The literal assumed while the layer is part of the model, or `None` once
	/// the layer is permanent.
	activation: Option<View<bool>>,
	/// Whether the layer posted a constraint that its activation literal does
	/// not condition.
	tainted: bool,
}

/// A Huub solver, with what is needed to post further layers into it.
#[derive(Debug)]
struct Live {
	/// The solver.
	solver: solver::Solver,
	/// The view of each decision of the posted layers, by index.
	views: Vec<AnyView>,
	/// The posted layers.
	layers: Vec<Layer>,
	/// Whether the SAT solver was configured to restart, which only a rebuild
	/// can change.
	restart: bool,
	/// Whether the search strategy of the model's annotations has been added.
	branched: bool,
	/// Whether the solver holds something that no layer accounts for, such as
	/// the nogoods of enumerating solutions, so that it must be rebuilt.
	stale: bool,
}

/// The options of a run.
#[derive(Debug, Default)]
struct Options {
	/// Report every solution, or every one that ties with the optimum.
	all_solutions: bool,
	/// Follow the search annotations of the model, without restarts.
	fixed_search: bool,
	/// Report every improving solution.
	intermediate: bool,
	/// The number of milliseconds a run may take.
	time_limit: Option<i64>,
}

/// The statistics readable from the solver instance.
#[derive(Debug, Default)]
struct Statistics {
	/// Boolean decisions of the current solver.
	bool_decisions: i64,
	/// Literals created eagerly to represent integer decisions.
	eager_literals: i64,
	/// Conflicts found in all searches.
	failures: i64,
	/// Seconds the last run spent posting the model.
	init_time: f64,
	/// Integer decisions of the current solver.
	int_decisions: i64,
	/// Literals created lazily to represent integer decisions.
	lazy_literals: i64,
	/// The greatest depth reached by a search.
	peak_depth: i64,
	/// Propagator calls in all searches.
	propagations: i64,
	/// Propagators of the current solver.
	propagators: i64,
	/// Restarts of all searches.
	restarts: i64,
	/// Search decisions made by the SAT solver.
	sat_search_directives: i64,
	/// Solutions reported by all runs.
	solutions: i64,
	/// Seconds the last run spent searching.
	solve_time: f64,
	/// Search decisions made by the search annotations.
	user_search_directives: i64,
}

/// Clamp a counter into a statistic.
fn counter(count: impl TryInto<i64>) -> i64 {
	count.try_into().unwrap_or(i64::MAX)
}

/// Resolve the name of a search annotation's decision selection.
fn decision_selection(name: &str) -> Option<DecisionSelection> {
	Some(match name {
		"anti_first_fail" => DecisionSelection::AntiFirstFail,
		"dom_w_deg" => DecisionSelection::DomWDeg,
		"first_fail" => DecisionSelection::FirstFail,
		"input_order" => DecisionSelection::InputOrder,
		"largest" => DecisionSelection::Largest,
		"max_regret" => DecisionSelection::MaxRegret,
		"most_constrained" => DecisionSelection::MostConstrained,
		"occurrence" => DecisionSelection::Occurrence,
		"smallest" => DecisionSelection::Smallest,
		_ => return None,
	})
}

/// Resolve the name of a search annotation's domain selection.
fn domain_selection(name: &str) -> Option<DomainSelection> {
	Some(match name {
		"indomain" | "indomain_min" => DomainSelection::IndomainMin,
		"indomain_interval" => DomainSelection::IndomainInterval,
		"indomain_max" => DomainSelection::IndomainMax,
		"indomain_median" => DomainSelection::IndomainMedian,
		"indomain_middle" => DomainSelection::IndomainMiddle,
		"indomain_reverse_split" => DomainSelection::IndomainReverseSplit,
		"indomain_split" => DomainSelection::IndomainSplit,
		"outdomain_max" => DomainSelection::OutdomainMax,
		"outdomain_median" => DomainSelection::OutdomainMedian,
		"outdomain_min" => DomainSelection::OutdomainMin,
		_ => return None,
	})
}

/// The first index of layer `layer`, given the exclusive end of each layer.
fn layer_start(layer: usize, end: impl Fn(usize) -> usize) -> usize {
	if layer == 0 { 0 } else { end(layer - 1) }
}

impl Solution for HuubSolution {
	fn statistic(&self, name: &str) -> Value<'_> {
		match (name, &self.objective) {
			("solutions", _) => (&self.index).into(),
			("int_objective", Some(objective)) => objective.into(),
			_ => Value::absent(),
		}
	}

	fn value(&self, decision_idx: usize) -> Value<'_> {
		match self.values.get(decision_idx) {
			Some(Assigned::Bool(b)) => (*b).into(),
			Some(Assigned::Int(i)) => i.into(),
			Some(Assigned::Absent) | None => Value::absent(),
		}
	}
}

impl HuubSolver {
	/// Add the search strategy of the model's annotations to the solver.
	///
	/// An annotation that asks for a strategy Huub does not have is reported
	/// through the `warn` scope, and replaced by the one Huub's FlatZinc
	/// frontend would use.
	fn branch<M: Model, G: FnMut(&str, Value<'_>)>(
		live: &mut Live,
		model: &M,
		on_message: &mut Option<&mut G>,
	) {
		let mut warn = |text: String| {
			if let Some(emit) = on_message.as_deref_mut() {
				emit("warn", (&text).into());
			}
		};
		let views = &live.views;
		let solver = &mut live.solver;
		let decisions = |value: Value<'_>| -> Vec<AnyView> {
			match value.view() {
				ValueView::List(list) => list
					.iter()
					.filter_map(|v| match v.view() {
						ValueView::Decision(d) => views.get(d.0).copied(),
						_ => None,
					})
					.collect(),
				_ => Vec::new(),
			}
		};
		let name = |value: Value<'_>| match value.view() {
			ValueView::Str(s) => s.to_owned(),
			other => format!("{other:?}"),
		};

		for ann in model.objective().annotations() {
			match ann.ident() {
				ident @ ("int_search" | "bool_search") if ann.argument_len() >= 3 => {
					let vars = decisions(ann.argument(0));
					let var_sel = name(ann.argument(1));
					let val_sel = name(ann.argument(2));
					let var_sel = decision_selection(&var_sel).unwrap_or_else(|| {
						warn(format!(
							"`{ident}`: Huub has no decision selection `{var_sel}`, and uses `first_fail`"
						));
						DecisionSelection::FirstFail
					});
					let val_sel = domain_selection(&val_sel).unwrap_or_else(|| {
						warn(format!(
							"`{ident}`: Huub has no domain selection `{val_sel}`, and uses `indomain_min`"
						));
						DomainSelection::IndomainMin
					});
					if ident == "int_search" {
						let vars = vars
							.into_iter()
							.map(|v| match v {
								AnyView::Int(v) => v,
								AnyView::Bool(b) => b.into(),
							})
							.collect();
						IntBrancher::new_in(solver, vars, var_sel, val_sel);
					} else {
						let vars = vars
							.into_iter()
							.filter_map(|v| match v {
								AnyView::Bool(b) => Some(b),
								AnyView::Int(_) => None,
							})
							.collect();
						BoolBrancher::new_in(solver, vars, var_sel, val_sel);
					}
				}
				ident @ ("warm_start_bool" | "warm_start_int") if ann.argument_len() == 2 => {
					let vars = decisions(ann.argument(0));
					let ValueView::List(values) = ann.argument(1).view() else {
						continue;
					};
					let literals = vars
						.into_iter()
						.zip(values.iter())
						.filter_map(|(var, value)| match (var, value.view()) {
							(AnyView::Bool(b), ValueView::Bool(val)) => {
								Some(if val { b } else { !b })
							}
							(AnyView::Int(v), ValueView::Int(val)) => {
								Some(v.lit(solver, IntLitMeaning::Eq(val)))
							}
							_ => None,
						})
						.collect();
					debug_assert!(ident.starts_with("warm_start"));
					WarmStartBrancher::new_in(solver, literals);
				}
				_ => {}
			}
		}
		live.branched = true;
	}

	/// Build a solver from the permanent layers of `model`.
	fn build<M: Model>(&mut self, model: &M, permanent: usize) -> Result<Live, PostError> {
		self.builds += 1;
		let restart = !self.options.fixed_search;
		let decisions = layer_start(permanent, |l| model.decision_layer_end(l));
		let constraints = layer_start(permanent, |l| model.constraint_layer_end(l));

		let mut poster = Poster::new(model, 0, decisions, &[], None)?;
		for con in 0..constraints {
			let _ = poster.post(ConstraintIdx::from(con))?;
		}
		let (mut huub, created, _) = poster.finish();
		let (mut solver, map): (solver::Solver, _) = huub
			.lower()
			.restart(restart)
			.to_solver()
			.map_err(|_| PostError::Unsatisfiable)?;
		let views = created
			.into_iter()
			.map(|v| map.get_any(&mut solver, v))
			.collect();
		let layers = (0..permanent)
			.map(|_| Layer {
				activation: None,
				tainted: false,
			})
			.collect();
		Ok(Live {
			solver,
			views,
			layers,
			restart,
			branched: false,
			stale: false,
		})
	}

	/// Post layer `layer` of `model` into the solver.
	fn extend<M: Model>(
		live: &mut Live,
		model: &M,
		layer: usize,
		permanent: bool,
	) -> Result<(), PostError> {
		let first = layer_start(layer, |l| model.decision_layer_end(l));
		let activation = (!permanent).then(|| View::from(live.solver.new_bool_decision()));

		let mut poster = Poster::new(
			model,
			first,
			model.decision_layer_end(layer),
			&live.views,
			activation,
		)?;
		let mut tainted = false;
		for con in
			layer_start(layer, |l| model.constraint_layer_end(l))..model.constraint_layer_end(layer)
		{
			tainted |= !poster.post(ConstraintIdx::from(con))?;
		}
		let (mut huub, created, bindings) = poster.finish();
		let map = huub
			.lower()
			.extend_solver(&mut live.solver, bindings)
			.map_err(|_| PostError::Unsatisfiable)?;
		live.views.extend(
			created
				.into_iter()
				.map(|v| map.get_any(&mut live.solver, v)),
		);
		live.layers.push(Layer {
			activation,
			tainted,
		});
		Ok(())
	}

	/// Bring the solver in line with the layers of `model`: retract the layers
	/// it no longer has, commit to those that became permanent, and post the
	/// ones the solver has not seen.
	fn prepare<M: Model, G: FnMut(&str, Value<'_>)>(
		&mut self,
		model: &M,
		on_message: &mut Option<&mut G>,
	) -> Result<(), PostError> {
		let len = model.layer_len();
		let permanent = model.layer_permanent().min(len);

		let restart = !self.options.fixed_search;
		let kept = model.layer_unchanged();
		let rebuild = self.live.as_ref().is_some_and(|live| {
			// A layer can only be retracted by negating its activation literal,
			// which undoes nothing that the literal does not condition.
			live.stale
				|| live.restart != restart
				|| live.layers[kept.min(live.layers.len())..]
					.iter()
					.any(|layer| layer.tainted || layer.activation.is_none())
		});
		if rebuild {
			self.retire();
		}
		if let Some(live) = &mut self.live {
			let kept = kept.min(live.layers.len());
			for layer in live.layers.drain(kept..) {
				let activation = layer
					.activation
					.expect("a permanent layer is never retracted");
				live.solver.add_clause([!activation])?;
			}
			live.views
				.truncate(layer_start(kept, |l| model.decision_layer_end(l)));
			// A layer that became permanent can never be retracted, so the
			// solver may commit to it.
			for layer in live.layers.iter_mut().take(permanent) {
				if let Some(activation) = layer.activation.take() {
					live.solver.add_clause([activation])?;
				}
			}
		}

		if self.live.is_none() {
			self.live = Some(self.build(model, permanent)?);
		}
		let live = self.live.as_mut().unwrap();
		for layer in live.layers.len()..len {
			Self::extend(live, model, layer, layer < permanent)?;
		}
		if !live.branched {
			Self::branch(live, model, on_message);
		}
		Ok(())
	}

	/// Update the statistics readable from the solver instance.
	fn refresh_statistics(&mut self) {
		let search = match &self.live {
			Some(live) => self.retired.clone() + live.solver.solver_statistics(),
			None => self.retired.clone(),
		};
		let statistics = &mut self.statistics;
		statistics.failures = counter(search.conflicts);
		statistics.restarts = counter(search.restarts);
		statistics.peak_depth = counter(search.peak_depth);
		statistics.propagations = counter(search.cp_propagator_calls);
		statistics.eager_literals = counter(search.eager_literals);
		statistics.lazy_literals = counter(search.lazy_literals);
		statistics.sat_search_directives = counter(search.sat_search_directives);
		statistics.user_search_directives = counter(search.user_search_directives);
		if let Some(live) = &self.live {
			let init = live.solver.init_statistics();
			statistics.bool_decisions = counter(init.bool_decisions);
			statistics.int_decisions = counter(init.int_decisions);
			statistics.propagators = counter(init.propagators);
		}
	}

	/// Drop the solver, keeping its search statistics.
	fn retire(&mut self) {
		if let Some(live) = self.live.take() {
			self.retired = self.retired.clone() + live.solver.solver_statistics();
		}
	}

	/// Search the prepared solver.
	fn search<M, F, H>(&mut self, model: &M, on_solution: &mut F, should_stop: Option<&H>) -> Status
	where
		M: Model,
		F: for<'s> FnMut(&'s HuubSolution),
		H: Fn() -> bool + Send + Sync,
	{
		let Options {
			all_solutions,
			fixed_search,
			intermediate,
			time_limit,
		} = self.options;
		let live = self.live.as_mut().expect("a run prepares the solver first");

		let objective = match model.objective_ident() {
			"" => None,
			ident @ ("int_maximize" | "int_minimize") => {
				let view: View<i64> = match model.objective_arg().view() {
					ValueView::Decision(d) => match live.views[d.0] {
						AnyView::Int(v) => v,
						AnyView::Bool(b) => b.into(),
					},
					ValueView::Int(c) => c.into(),
					other => {
						return Status::Error(format!(
							"`{ident}` expects an integer, found {other:?}"
						));
					}
				};
				Some((view, ident == "int_maximize"))
			}
			other => {
				return Status::Error(format!(
					"`{other}` is not an objective this library declares"
				));
			}
		};

		let len = model.decision_len();
		let wanted: Vec<(usize, AnyView)> = (0..len)
			.filter(|&i| model.decision_in_solution(DecisionIdx::from(i)))
			.map(|i| (i, live.views[i]))
			.collect();
		let assumptions: Vec<View<bool>> = live
			.layers
			.iter()
			.filter_map(|layer| layer.activation)
			.collect();

		live.solver.set_search_strategy(if fixed_search {
			SearchStrategy::Branchers
		} else {
			SearchStrategy::Transition(SwitchTrigger::Conflicts(1000))
		});

		let deadline =
			time_limit.map(|ms| Instant::now() + Duration::from_millis(ms.unsigned_abs()));
		let stop = should_stop.map(|s| -> &(dyn Fn() -> bool + Send + Sync) { s });
		// SAFETY: Huub requires a terminate callback that lives forever, but
		// the predicate is only borrowed for this run. The callback is
		// removed below, before the borrow ends, and nothing calls it outside
		// a search.
		let stop: Option<&'static (dyn Fn() -> bool + Send + Sync)> =
			unsafe { mem::transmute(stop) };
		if deadline.is_some() || stop.is_some() {
			live.solver.set_terminate_callback(Some(move || {
				if deadline.is_some_and(|d| Instant::now() >= d) || stop.is_some_and(|s| s()) {
					TerminationSignal::Terminate
				} else {
					TerminationSignal::Continue
				}
			}));
		}

		let reported = Cell::new(self.statistics.solutions);
		let solution = |sol: solver::Solution<'_>, objective: Option<i64>| {
			let mut values = vec![Assigned::Absent; len];
			for &(i, view) in &wanted {
				values[i] = match view {
					AnyView::Bool(b) => Assigned::Bool(b.val(sol)),
					AnyView::Int(v) => Assigned::Int(v.val(sol)),
				};
			}
			HuubSolution {
				values,
				objective,
				index: 0,
			}
		};
		let mut report = |mut solution: HuubSolution| {
			solution.index = reported.get();
			reported.set(reported.get() + 1);
			on_solution(&solution);
		};
		let enumerate = all_solutions.then(|| wanted.iter().map(|&(_, v)| v).collect::<Vec<_>>());
		if all_solutions {
			// Enumeration adds nogoods that no layer accounts for.
			live.stale = true;
		}

		let status = match objective {
			None => {
				let status = live
					.solver
					.solve()
					.assuming(assumptions)
					.on_solution(|sol| report(solution(sol, None)))
					.maybe_all_solutions(enumerate)
					.satisfy();
				// One solution of a satisfaction problem leaves the rest of the
				// search space unexplored, so other solutions may exist.
				match status {
					solver::Status::Complete | solver::Status::Unsatisfiable => Status::Complete,
					solver::Status::Satisfied | solver::Status::Unknown => Status::Incomplete,
				}
			}
			Some((view, maximize)) => {
				// Without `intermediate`, only the last of the improving
				// solutions is reported, followed by the solutions that tie
				// with it.
				let mut pending: Option<HuubSolution> = None;
				let mut last = None;
				let solve = live
					.solver
					.solve()
					.assuming(assumptions)
					.on_solution(|sol| {
						let value = view.val(sol);
						let found = solution(sol, Some(value));
						if intermediate {
							report(found);
						} else if last == Some(value) {
							if let Some(best) = pending.take() {
								report(best);
							}
							report(found);
						} else {
							pending = Some(found);
							last = Some(value);
						}
					})
					.maybe_all_solutions(enumerate);
				let (status, _) = if maximize {
					solve.maximize(view)
				} else {
					solve.minimize(view)
				};
				if let Some(best) = pending {
					report(best);
				}
				match status {
					solver::Status::Complete | solver::Status::Unsatisfiable => Status::Complete,
					solver::Status::Satisfied | solver::Status::Unknown => Status::Incomplete,
				}
			}
		};

		live.solver
			.set_terminate_callback(None::<fn() -> TerminationSignal>);
		self.statistics.solutions = reported.get();
		status
	}
}

impl Solver for HuubSolver {
	type Solution<'s> = HuubSolution;

	fn option_get(&self, name: &str) -> Value<'_> {
		match name {
			"all_solutions" => self.options.all_solutions.into(),
			"fixed_search" => self.options.fixed_search.into(),
			"intermediate" => self.options.intermediate.into(),
			"time_limit" => (&self.options.time_limit).into(),
			_ => Value::absent(),
		}
	}

	fn option_set(&mut self, name: &str, value: Value<'_>) -> Result<(), String> {
		let flag =
			|| bool::try_from(&value).map_err(|()| format!("option `{name}` expects a Boolean"));
		match name {
			"all_solutions" => self.options.all_solutions = flag()?,
			"fixed_search" => self.options.fixed_search = flag()?,
			"intermediate" => self.options.intermediate = flag()?,
			"time_limit" => {
				self.options.time_limit = match value.view() {
					ValueView::Absent => None,
					ValueView::Int(ms) if ms > 0 => Some(ms),
					_ => {
						return Err(
							"option `time_limit` expects a positive number of milliseconds"
								.to_owned(),
						);
					}
				};
			}
			_ => return Err(format!("unknown option `{name}`")),
		}
		Ok(())
	}

	fn run<M, F, G, H>(
		&mut self,
		model: &M,
		on_solution: &mut F,
		mut on_message: Option<&mut G>,
		should_stop: Option<&H>,
	) -> Status
	where
		M: Model + Sync,
		F: for<'s> FnMut(&'s Self::Solution<'s>) + Send,
		G: FnMut(&str, Value<'_>) + Send,
		H: Fn() -> bool + Send + Sync,
	{
		// The times describe this run, as the registry defines them and as the
		// other adapters report them, even when it posts or searches nothing.
		self.statistics.init_time = 0.0;
		self.statistics.solve_time = 0.0;
		if should_stop.is_some_and(|stop| stop()) {
			return Status::Incomplete;
		}

		let start = Instant::now();
		let prepared = self.prepare(model, &mut on_message);
		self.statistics.init_time = start.elapsed().as_secs_f64();
		let status = match prepared {
			Ok(()) => {
				let start = Instant::now();
				let status = self.search(model, on_solution, should_stop);
				self.statistics.solve_time = start.elapsed().as_secs_f64();
				status
			}
			Err(err) => {
				// The solver may hold part of what failed to post.
				if let Some(live) = &mut self.live {
					live.stale = true;
				}
				match err {
					PostError::Unsatisfiable => Status::Complete,
					PostError::Invalid(message) => Status::Error(message),
				}
			}
		};
		self.refresh_statistics();
		status
	}

	fn statistic(&self, name: &str) -> Value<'_> {
		let statistics = &self.statistics;
		match name {
			"bool_decisions" => (&statistics.bool_decisions).into(),
			"failures" => (&statistics.failures).into(),
			"huub_eager_literals" => (&statistics.eager_literals).into(),
			"huub_lazy_literals" => (&statistics.lazy_literals).into(),
			"huub_sat_search_directives" => (&statistics.sat_search_directives).into(),
			"huub_user_search_directives" => (&statistics.user_search_directives).into(),
			"init_time" => (&statistics.init_time).into(),
			"int_decisions" => (&statistics.int_decisions).into(),
			"peak_depth" => (&statistics.peak_depth).into(),
			"propagations" => (&statistics.propagations).into(),
			"propagators" => (&statistics.propagators).into(),
			"restarts" => (&statistics.restarts).into(),
			"solutions" => (&statistics.solutions).into(),
			"solve_time" => (&statistics.solve_time).into(),
			_ => Value::absent(),
		}
	}
}

impl SolverType for HuubSolver {
	const CONSTRAINT_LIST: fznso::ConstraintList<'static> = declarations::CONSTRAINT_LIST;
	const DECISION_LIST: fznso::TypeList<'static> = declarations::DECISION_LIST;
	const OBJECTIVE_LIST: fznso::ObjectiveList<'static> = declarations::OBJECTIVE_LIST;
	const OPTION_LIST: fznso::OptionList<'static> = declarations::OPTION_LIST;
	const STATISTIC_LIST: fznso::StatisticList<'static> = declarations::STATISTIC_LIST;

	fn new() -> Self {
		Self::default()
	}
}

/// The entry points of the library.
mod export {
	fznso::fznso_export!(crate::HuubSolver, "huub");
}
