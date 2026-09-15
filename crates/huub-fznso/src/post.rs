//! Posting the constraints of an FZnSO model into a Huub [`HuubModel`].
//!
//! The constraints of one layer are read straight from the application's model
//! and posted into a Huub model of their own, which is then lowered: the first
//! into a new solver, every later one into the solver that already holds the
//! layers before it. A decision from an earlier layer is created in the Huub
//! model the first time a constraint refers to it, and bound to the solver view
//! it stands in for.

use fznso::{ConstraintIdx, DecisionIdx, Model, TypeBase, Value, ValueExt, ValueView};
use huub_lib::{
	actions::{BoolSimplificationActions, IntInspectionActions, IntSimplificationActions},
	constraints::Nogood,
	model::{
		Model as HuubModel, View,
		deserialize::AnyView,
		expressions::{IntLinearExp, Proposition},
	},
	solver,
};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::FxHashMap;

/// How a linear constraint compares its sum to its right-hand side.
#[derive(Clone, Copy, Debug)]
enum Comparator {
	/// The sum equals the right-hand side.
	Equal,
	/// The sum is at most the right-hand side.
	LessEqual,
	/// The sum differs from the right-hand side.
	NotEqual,
}

/// Why a constraint could not be posted.
#[derive(Debug)]
pub(crate) enum PostError {
	/// Simplification proved that the model has no solution.
	Unsatisfiable,
	/// An argument does not have the shape its declaration promised.
	Invalid(String),
}

/// A Huub model receiving the constraints of one layer of an FZnSO model.
#[derive(Debug)]
pub(crate) struct Poster<'a, M> {
	/// The application's model.
	model: &'a M,
	/// The model the constraints are posted into.
	huub: HuubModel,
	/// The index of the first decision this model creates. Every decision
	/// before it already exists in the solver.
	first: usize,
	/// The decisions this model creates, from [`Self::first`] on.
	created: Vec<AnyView>,
	/// The decisions before [`Self::first`] that a constraint has referred to.
	bound: FxHashMap<usize, AnyView>,
	/// The solver views of the decisions before [`Self::first`].
	existing: &'a [solver::AnyView],
	/// Each decision of this model that stands in for a solver view, with that
	/// view.
	bindings: Vec<(AnyView, solver::AnyView)>,
	/// The literal that must be true for the constraints to hold, when the
	/// layer they belong to can be retracted.
	guard: Option<View<bool>>,
}

/// The Boolean decision that (half-)reifies a constraint, if any.
#[derive(Clone, Copy, Debug)]
enum Reification {
	/// The constraint must hold.
	None,
	/// The constraint must hold when the decision is true.
	Half(View<bool>),
	/// The constraint holds exactly when the decision is true.
	Full(View<bool>),
}

/// Create a decision of `huub` with the type and domain of decision `idx` of
/// the application's `model`.
fn new_decision<M: Model>(
	huub: &mut HuubModel,
	model: &M,
	idx: usize,
) -> Result<AnyView, PostError> {
	let decision = DecisionIdx::from(idx);
	let ty = model.decision_type(decision);
	if ty.list_of || ty.set_of {
		return Err(PostError::Invalid(format!(
			"decision {idx} has type `{ty}`, which is not a declared decision type"
		)));
	}
	match ty.base {
		TypeBase::FznsoTypeBaseBool => Ok(AnyView::Bool(huub.new_bool_decision())),
		TypeBase::FznsoTypeBaseInt => {
			let domain: RangeList<i64> = match model.decision_domain(decision).view() {
				ValueView::IntSet(ranges) => ranges.iter().map(|(min, max)| min..=max).collect(),
				ValueView::Absent => (i64::MIN..=i64::MAX).into(),
				other => {
					return Err(PostError::Invalid(format!(
						"decision {idx} has domain {other:?}, which is not a set of integers"
					)));
				}
			};
			match domain.card() {
				Some(0) => Err(PostError::Unsatisfiable),
				Some(1) => Ok(AnyView::Int((*domain.min().unwrap()).into())),
				_ => Ok(AnyView::Int(huub.new_int_decision(domain))),
			}
		}
		_ => Err(PostError::Invalid(format!(
			"decision {idx} has type `{ty}`, which is not a declared decision type"
		))),
	}
}

/// The error for a value that is not of the expected kind.
fn unexpected(expected: &str, found: &ValueView<'_>) -> PostError {
	PostError::Invalid(format!("expected {expected}, found {found:?}"))
}

impl<T> From<Nogood<T>> for PostError {
	fn from(_: Nogood<T>) -> Self {
		PostError::Unsatisfiable
	}
}

impl<'a, M: Model> Poster<'a, M> {
	/// Resolve an argument that is a Boolean.
	fn bool(&mut self, value: Value<'_>) -> Result<View<bool>, PostError> {
		match value.view() {
			ValueView::Bool(b) => Ok(b.into()),
			ValueView::Decision(d) => match self.decision(d.0)? {
				AnyView::Bool(b) => Ok(b),
				_ => Err(PostError::Invalid(format!(
					"expected a Boolean, found integer decision {}",
					d.0
				))),
			},
			other => Err(unexpected("a Boolean", &other)),
		}
	}

	/// Resolve a list of Boolean arguments, as formulas.
	fn bool_atoms(&mut self, value: Value<'_>) -> Result<Vec<Proposition<View<bool>>>, PostError> {
		self.list(value, |poster, value| {
			poster.bool(value).map(Proposition::Atom)
		})
	}

	/// Resolve the view of decision `idx`, creating it in the Huub model on
	/// first use if it belongs to an earlier layer.
	fn decision(&mut self, idx: usize) -> Result<AnyView, PostError> {
		if idx >= self.first {
			return self.created.get(idx - self.first).cloned().ok_or_else(|| {
				PostError::Invalid(format!(
					"decision {idx} belongs to a later layer than the constraint"
				))
			});
		}
		if let Some(view) = self.bound.get(&idx) {
			return Ok(view.clone());
		}
		let view = new_decision(&mut self.huub, self.model, idx)?;
		// A decision with one value is a constant, and so is the solver view it
		// would stand in for: it has nothing to bind.
		if !matches!(&view, AnyView::Int(v) if v.val(&self.huub).is_some()) {
			self.bindings.push((view.clone(), self.existing[idx]));
		}
		let _ = self.bound.insert(idx, view.clone());
		Ok(view)
	}

	/// Make the constraints posted so far fail, unless the layer is retracted.
	fn fail(&mut self) -> Result<bool, PostError> {
		match self.guard {
			Some(guard) => {
				self.huub.proposition(Proposition::Atom(!guard)).post()?;
				Ok(true)
			}
			None => Err(PostError::Unsatisfiable),
		}
	}

	/// Give up the Huub model, the views of the decisions it created, and the
	/// bindings to lower it with.
	pub(crate) fn finish(self) -> (HuubModel, Vec<AnyView>, Vec<(AnyView, solver::AnyView)>) {
		(self.huub, self.created, self.bindings)
	}

	/// Resolve an argument that is an integer.
	fn int(&mut self, value: Value<'_>) -> Result<View<i64>, PostError> {
		match value.view() {
			ValueView::Int(i) => Ok(i.into()),
			ValueView::Decision(d) => match self.decision(d.0)? {
				AnyView::Int(v) => Ok(v),
				AnyView::Bool(b) => Ok(b.into()),
				_ => unreachable!("a decision is either a Boolean or an integer"),
			},
			other => Err(unexpected("an integer", &other)),
		}
	}

	/// Post a linear constraint, (half-)reified as asked.
	fn linear(
		&mut self,
		expr: IntLinearExp,
		comparator: Comparator,
		rhs: i64,
		reification: Reification,
	) -> Result<bool, PostError> {
		/// Complete the builder with the comparator.
		macro_rules! compare {
			($builder:expr) => {
				match comparator {
					Comparator::Equal => $builder.eq(rhs),
					Comparator::LessEqual => $builder.le(rhs),
					Comparator::NotEqual => $builder.ne(rhs),
				}
			};
		}

		let guard = self.guard;
		let huub = &mut self.huub;
		match (reification, guard) {
			(Reification::None, None) => compare!(huub.linear(expr)).post()?,
			(Reification::None, Some(b)) | (Reification::Half(b), None) => {
				compare!(huub.linear(expr)).implied_by(b).post()?;
			}
			(Reification::Half(r), Some(guard)) => {
				let both = huub
					.proposition(Proposition::And(vec![r.into(), guard.into()]))
					.reify();
				compare!(huub.linear(expr)).implied_by(both).post()?;
			}
			(Reification::Full(r), None) => compare!(huub.linear(expr)).reified_by(r).post()?,
			(Reification::Full(r), Some(guard)) => {
				// The reification of a new decision can always be satisfied, so
				// it is only the equivalence with `r` that the guard must
				// condition.
				let holds = compare!(huub.linear(expr)).reify();
				huub.proposition(Proposition::Equiv(vec![r.into(), holds.into()]))
					.implied_by(guard)
					.post()?;
			}
		}
		Ok(true)
	}

	/// Resolve an argument that is a list, resolving each element with
	/// `element`.
	fn list<T>(
		&mut self,
		value: Value<'_>,
		mut element: impl FnMut(&mut Self, Value<'_>) -> Result<T, PostError>,
	) -> Result<Vec<T>, PostError> {
		match value.view() {
			ValueView::List(list) => list.iter().map(|v| element(self, v)).collect(),
			other => Err(unexpected("a list", &other)),
		}
	}

	/// Create the poster for the layer whose decisions are numbered from
	/// `first` up to `end`, all earlier ones having the solver views
	/// `existing`.
	///
	/// When `guard` is given, every constraint that can be conditioned on it is
	/// posted to hold only when it is true.
	pub(crate) fn new(
		model: &'a M,
		first: usize,
		end: usize,
		existing: &'a [solver::AnyView],
		guard: Option<solver::View<bool>>,
	) -> Result<Self, PostError> {
		debug_assert_eq!(existing.len(), first);
		let mut huub = HuubModel::default();
		let created = (first..end)
			.map(|idx| new_decision(&mut huub, model, idx))
			.collect::<Result<_, _>>()?;
		let mut bindings = Vec::new();
		let guard = guard.map(|solver_view| {
			let view = huub.new_bool_decision();
			bindings.push((AnyView::Bool(view), solver::AnyView::Bool(solver_view)));
			view
		});
		Ok(Self {
			model,
			huub,
			first,
			created,
			bound: FxHashMap::default(),
			existing,
			bindings,
			guard,
		})
	}

	/// Check that no integer in `values` can be negative.
	fn non_negative(&self, ident: &str, values: &[View<i64>]) -> Result<(), PostError> {
		if values.iter().any(|v| v.min(&self.huub) < 0) {
			return Err(PostError::Invalid(format!(
				"`{ident}` requires its durations and resource requirements to be non-negative"
			)));
		}
		Ok(())
	}

	/// Resolve an argument that is a fixed integer.
	fn par_int(&mut self, value: Value<'_>) -> Result<i64, PostError> {
		match value.view() {
			ValueView::Int(i) => Ok(i),
			other => Err(unexpected("a fixed integer", &other)),
		}
	}

	/// Resolve an argument that is a fixed set of integers.
	fn par_set(&mut self, value: Value<'_>) -> Result<RangeList<i64>, PostError> {
		match value.view() {
			ValueView::IntSet(ranges) => Ok(ranges.iter().map(|(min, max)| min..=max).collect()),
			other => Err(unexpected("a fixed set of integers", &other)),
		}
	}

	/// Post constraint `con` of the application's model.
	///
	/// Returns whether the constraint only holds when the guard does, which is
	/// trivially so when there is no guard.
	pub(crate) fn post(&mut self, con: ConstraintIdx) -> Result<bool, PostError> {
		let model = self.model;
		let ident = model.constraint_ident(con);
		let len = model.constraint_argument_len(con);
		let arg = |i: usize| model.constraint_argument(con, i);

		let (base, reified) = if let Some(base) = ident.strip_suffix("_reif") {
			(base, Some(true))
		} else if let Some(base) = ident.strip_suffix("_imp") {
			(base, Some(false))
		} else {
			(ident, None)
		};
		let arity = len - usize::from(reified.is_some() && len > 0);
		let expect = |expected: usize| {
			if arity == expected && (reified.is_none() || len > 0) {
				Ok(())
			} else {
				Err(PostError::Invalid(format!(
					"`{ident}` expects {} argument(s), found {len}",
					expected + usize::from(reified.is_some())
				)))
			}
		};
		let reification = match reified {
			None => Reification::None,
			Some(_) if len == 0 => Reification::None,
			Some(true) => Reification::Full(self.bool(arg(len - 1))?),
			Some(false) => Reification::Half(self.bool(arg(len - 1))?),
		};
		// Only a linear constraint, a formula, or set membership can be
		// (half-)reified.
		let plain = || {
			if reified.is_some() {
				Err(PostError::Invalid(format!(
					"`{ident}` is not a constraint this library declares"
				)))
			} else {
				Ok(())
			}
		};
		let unguarded = self.guard.is_none();

		match base {
			"bool_array_and" => {
				plain()?;
				expect(2)?;
				let xs = self.bool_atoms(arg(0))?;
				let r = self.bool(arg(1))?;
				self.proposition(Proposition::And(xs), Reification::Full(r))
			}
			"bool_array_element" => {
				plain()?;
				expect(4)?;
				let offset = self.par_int(arg(1))?;
				let index = self.int(arg(2))?.bounding_sub(&mut self.huub, offset)?;
				let result = self.bool(arg(3))?;
				let xs = self.list(arg(0), Self::bool)?;
				if xs.is_empty() {
					return self.fail();
				}
				self.huub.element(xs).index(index).result(result).post()?;
				Ok(unguarded)
			}
			"bool_array_xor" => {
				expect(1)?;
				let xs = self.list(arg(0), Self::bool)?;
				// Two literals that differ are one literal and its negation: a
				// view rather than a constraint. This is how negation reaches
				// the solver. A guard or a reification makes it
				// conditional, and then it is a formula again.
				if let (&[a, b], Reification::None, true) = (xs.as_slice(), reification, unguarded)
				{
					a.unify(&mut self.huub, !b)?;
					return Ok(true);
				}
				let xs = xs.into_iter().map(Proposition::Atom).collect();
				self.proposition(Proposition::Xor(xs), reification)
			}
			"bool_clause" => {
				expect(2)?;
				let mut literals = self.bool_atoms(arg(0))?;
				literals.extend(self.list(arg(1), |poster, v| {
					poster.bool(v).map(|b| Proposition::Atom(!b))
				})?);
				self.proposition(Proposition::Or(literals), reification)
			}
			"bool_lin_eq" | "bool_lin_le" | "bool_lin_ne" => {
				expect(3)?;
				let coeffs = self.list(arg(0), Self::par_int)?;
				let xs = self.list(arg(1), |poster, v| poster.bool(v).map(View::<i64>::from))?;
				let mut sum = self.weighted_sum(ident, &coeffs, xs)?;
				let (comparator, rhs) = match base {
					"bool_lin_le" => (Comparator::LessEqual, self.par_int(arg(2))?),
					_ => {
						sum -= self.int(arg(2))?;
						let comparator = if base == "bool_lin_eq" {
							Comparator::Equal
						} else {
							Comparator::NotEqual
						};
						(comparator, 0)
					}
				};
				self.linear(sum, comparator, rhs, reification)
			}
			"bool_to_int" => {
				plain()?;
				expect(2)?;
				let a = self.bool(arg(0))?;
				let b = self.int(arg(1))?;
				b.unify(&mut self.huub, a)?;
				Ok(unguarded)
			}
			"int_abs" => {
				plain()?;
				expect(2)?;
				let a = self.int(arg(0))?;
				let b = self.int(arg(1))?;
				self.huub.abs(a).result(b).post()?;
				Ok(unguarded)
			}
			"int_all_different" => {
				plain()?;
				expect(1)?;
				let xs = self.list(arg(0), Self::int)?;
				self.huub.unique(xs).post()?;
				Ok(unguarded)
			}
			"int_array_element" => {
				plain()?;
				expect(4)?;
				let offset = self.par_int(arg(1))?;
				let index = self.int(arg(2))?.bounding_sub(&mut self.huub, offset)?;
				let result = self.int(arg(3))?;
				let xs = self.list(arg(0), Self::int)?;
				if xs.is_empty() {
					return self.fail();
				}
				self.huub.element(xs).index(index).result(result).post()?;
				Ok(unguarded)
			}
			"int_array_maximum" | "int_array_minimum" => {
				plain()?;
				expect(2)?;
				let xs = self.list(arg(0), Self::int)?;
				let result = self.int(arg(1))?;
				if xs.is_empty() {
					return Err(PostError::Invalid(format!(
						"`{ident}` is undefined for an empty list"
					)));
				}
				if base == "int_array_maximum" {
					self.huub.maximum(xs).result(result).post()?;
				} else {
					self.huub.minimum(xs).result(result).post()?;
				}
				Ok(unguarded)
			}
			"int_circuit" | "int_subcircuit" => {
				plain()?;
				expect(2)?;
				let xs = self.list(arg(0), Self::int)?;
				let offset = self.par_int(arg(1))?;
				self.huub
					.circuit(xs)
					.offset(offset)
					.subcircuit(base == "int_subcircuit")
					.post()?;
				Ok(unguarded)
			}
			"int_cumulative" => {
				plain()?;
				expect(4)?;
				let starts = self.list(arg(0), Self::int)?;
				let durations = self.list(arg(1), Self::int)?;
				let usages = self.list(arg(2), Self::int)?;
				let capacity = self.int(arg(3))?;
				if starts.len() != durations.len() || starts.len() != usages.len() {
					return Err(PostError::Invalid(format!(
						"`{ident}` requires lists of equal length"
					)));
				}
				self.non_negative(ident, &durations)?;
				self.non_negative(ident, &usages)?;
				self.huub
					.cumulative()
					.start_times(starts)
					.durations(durations)
					.usages(usages)
					.capacity(capacity)
					.post()?;
				Ok(unguarded)
			}
			"int_disjunctive_strict" => {
				plain()?;
				expect(2)?;
				let starts = self.list(arg(0), Self::int)?;
				let durations = self.list(arg(1), Self::par_int)?;
				if starts.len() != durations.len() {
					return Err(PostError::Invalid(format!(
						"`{ident}` requires lists of equal length"
					)));
				}
				if durations.iter().any(|&d| d < 0) {
					return Err(PostError::Invalid(format!(
						"`{ident}` requires its durations to be non-negative"
					)));
				}
				self.huub
					.disjunctive()
					.start_times(starts)
					.durations(durations)
					.post()?;
				Ok(unguarded)
			}
			"int_div" | "int_pow" | "int_times" => {
				plain()?;
				expect(3)?;
				let a = self.int(arg(0))?;
				let b = self.int(arg(1))?;
				let c = self.int(arg(2))?;
				match base {
					"int_div" => self.huub.div(a, b).result(c).post()?,
					"int_pow" => self.huub.pow(a, b).result(c).post()?,
					_ => self.huub.mul(a, b).result(c).post()?,
				}
				Ok(unguarded)
			}
			"int_in" => {
				expect(2)?;
				let x = self.int(arg(0))?;
				let values = self.par_set(arg(1))?;
				// Membership is posted as its reification, conditioned like any
				// formula: the reification of a new decision always holds.
				let member = self.huub.contains(values).member(x).define();
				self.proposition(Proposition::Atom(member), reification)
			}
			"int_lin_eq" | "int_lin_le" | "int_lin_ne" => {
				expect(3)?;
				let coeffs = self.list(arg(0), Self::par_int)?;
				let xs = self.list(arg(1), Self::int)?;
				let rhs = self.par_int(arg(2))?;
				let sum = self.weighted_sum(ident, &coeffs, xs)?;
				let comparator = match base {
					"int_lin_eq" => Comparator::Equal,
					"int_lin_le" => Comparator::LessEqual,
					_ => Comparator::NotEqual,
				};
				self.linear(sum, comparator, rhs, reification)
			}
			"int_no_overlap" | "int_no_overlap_nonstrict" => {
				plain()?;
				expect(4)?;
				let x = self.list(arg(0), Self::int)?;
				let dx = self.list(arg(1), Self::int)?;
				let y = self.list(arg(2), Self::int)?;
				let dy = self.list(arg(3), Self::int)?;
				if x.len() != dx.len() || x.len() != y.len() || x.len() != dy.len() {
					return Err(PostError::Invalid(format!(
						"`{ident}` requires lists of equal length"
					)));
				}
				let origins = x.into_iter().zip(y).map(|(x, y)| vec![x, y]).collect();
				let sizes = dx
					.into_iter()
					.zip(dy)
					.map(|(dx, dy)| vec![dx, dy])
					.collect();
				self.huub
					.no_overlap()
					.origins(origins)
					.sizes(sizes)
					.strict(base == "int_no_overlap")
					.post()?;
				Ok(unguarded)
			}
			"int_no_overlap_nd" | "int_no_overlap_nd_nonstrict" => {
				plain()?;
				expect(3)?;
				let dimensions = self.par_int(arg(0))?;
				let positions = self.list(arg(1), Self::int)?;
				let sizes = self.list(arg(2), Self::int)?;
				let dimensions = usize::try_from(dimensions)
					.ok()
					.filter(|&d| {
						d > 0 && positions.len() == sizes.len() && positions.len() % d == 0
					})
					.ok_or_else(|| {
						PostError::Invalid(format!(
							"`{ident}` requires a positive number of dimensions that divides the length of both lists"
						))
					})?;
				let rows = |list: Vec<View<i64>>| {
					list.chunks_exact(dimensions).map(<[_]>::to_vec).collect()
				};
				self.huub
					.no_overlap()
					.origins(rows(positions))
					.sizes(rows(sizes))
					.strict(base == "int_no_overlap_nd")
					.post()?;
				Ok(unguarded)
			}
			"int_seq_precede_chain" => {
				plain()?;
				expect(1)?;
				let xs = self.list(arg(0), Self::int)?;
				self.huub.value_precede(xs).post()?;
				Ok(unguarded)
			}
			"int_table" => {
				plain()?;
				expect(2)?;
				let xs = self.list(arg(0), Self::int)?;
				let tuples = self.list(arg(1), Self::par_int)?;
				if xs.is_empty() {
					return Ok(true);
				}
				if tuples.len() % xs.len() != 0 {
					return Err(PostError::Invalid(format!(
						"`{ident}` requires a table whose length is a multiple of the number of decisions"
					)));
				}
				if tuples.is_empty() {
					return self.fail();
				}
				let rows: Vec<_> = tuples.chunks_exact(xs.len()).map(<[_]>::to_vec).collect();
				self.huub.table(xs).values(rows).post()?;
				Ok(unguarded)
			}
			"int_value_precede" | "int_value_precede_chain" => {
				plain()?;
				let (values, xs) = if base == "int_value_precede" {
					expect(3)?;
					let s = self.par_int(arg(0))?;
					let t = self.par_int(arg(1))?;
					(vec![s, t], self.list(arg(2), Self::int)?)
				} else {
					expect(2)?;
					(
						self.list(arg(0), Self::par_int)?,
						self.list(arg(1), Self::int)?,
					)
				};
				self.huub.value_precede(xs).values(values).post()?;
				Ok(unguarded)
			}
			_ => Err(PostError::Invalid(format!(
				"`{ident}` is not a constraint this library declares"
			))),
		}
	}

	/// Post a formula, (half-)reified as asked.
	fn proposition(
		&mut self,
		formula: Proposition<View<bool>>,
		reification: Reification,
	) -> Result<bool, PostError> {
		let guard = self.guard;
		let huub = &mut self.huub;
		match (reification, guard) {
			(Reification::None, None) => huub.proposition(formula).post()?,
			(Reification::None, Some(b)) | (Reification::Half(b), None) => {
				huub.proposition(formula).implied_by(b).post()?;
			}
			(Reification::Half(r), Some(guard)) => {
				let both = huub
					.proposition(Proposition::And(vec![r.into(), guard.into()]))
					.reify();
				huub.proposition(formula).implied_by(both).post()?;
			}
			(Reification::Full(r), None) => huub.proposition(formula).reified_by(r).post()?,
			(Reification::Full(r), Some(guard)) => huub
				.proposition(Proposition::Equiv(vec![r.into(), formula]))
				.implied_by(guard)
				.post()?,
		}
		Ok(true)
	}

	/// Sum each of `terms` multiplied by its coefficient.
	fn weighted_sum(
		&mut self,
		ident: &str,
		coeffs: &[i64],
		terms: Vec<View<i64>>,
	) -> Result<IntLinearExp, PostError> {
		if coeffs.len() != terms.len() {
			return Err(PostError::Invalid(format!(
				"`{ident}` requires as many coefficients as terms"
			)));
		}
		let mut sum = IntLinearExp::from(0);
		for (&coeff, term) in coeffs.iter().zip(terms) {
			if coeff != 0 {
				sum += term.bounding_mul(&mut self.huub, coeff)?;
			}
		}
		Ok(sum)
	}
}
