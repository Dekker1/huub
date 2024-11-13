use delegate::delegate;
use pindakaas::solver::propagation::PropagatingSolver;

use crate::{
	actions::{
		decision::DecisionActions, initialization::InitializationActions,
		inspection::InspectionActions, trailing::TrailingActions,
	},
	solver::{
		engine::{
			activation_list::IntPropCond, int_var::IntVarRef, trail::TrailedInt, Engine, PropRef,
		},
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, IntVal, IntView, LitMeaning, Solver,
};

/// Reference to the construct that we are intilizing
pub(crate) enum InitRef {
	// a brancher
	Brancher,
	// a specific propagator
	Propagator(PropRef),
}

pub(crate) struct InitializationContext<'a, Oracle: 'a> {
	pub(crate) init_ref: InitRef,
	pub(crate) slv: &'a mut Solver<Oracle>,
}

impl<'a, Oracle: PropagatingSolver<Engine>> InitializationActions
	for InitializationContext<'a, Oracle>
{
	fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		clause: I,
	) -> Result<(), crate::ReformulationError> {
		self.slv.add_clause(clause)
	}

	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		self.slv.engine_mut().state.trail.track_int(init)
	}

	fn enqueue_on_bool_change(&mut self, var: BoolView) {
		match var.0 {
			BoolViewInner::Lit(lit) => {
				self.slv.engine_mut().state.trail.grow_to_boolvar(lit.var());
				self.slv.oracle.add_observed_var(lit.var());
				if let InitRef::Propagator(prop) = self.init_ref {
					self.slv
						.engine_mut()
						.state
						.bool_activation
						.entry(lit.var())
						.or_default()
						.add(prop);
				}
			}
			BoolViewInner::Const(_) => {}
		}
	}

	fn enqueue_on_int_change(&mut self, var: IntView, condition: IntPropCond) {
		let mut subscribe_intref = |var: IntVarRef, prop, cond| {
			self.slv.engine_mut().state.int_activation[var].add(prop, cond);
		};
		match (&self.init_ref, var.0) {
			(InitRef::Propagator(prop), IntViewInner::VarRef(var)) => {
				subscribe_intref(var, *prop, condition);
			}
			(InitRef::Propagator(prop), IntViewInner::Linear { transformer, var }) => {
				let event = if transformer.positive_scale() {
					condition
				} else {
					match condition {
						IntPropCond::LowerBound => IntPropCond::UpperBound,
						IntPropCond::UpperBound => IntPropCond::LowerBound,
						_ => condition,
					}
				};
				subscribe_intref(var, *prop, event);
			}
			(_, IntViewInner::Const(_)) => {} // ignore
			(_, IntViewInner::Bool { lit, .. }) => {
				self.enqueue_on_bool_change(BoolView(BoolViewInner::Lit(lit)));
			}
			(InitRef::Brancher, _) => {} // ignore: branchers don't receive notifications, and contained literals are already observed.
		}
	}

	fn enqueue_when_n_fixed(&mut self, mut n: usize, bool_vars: &[BoolView], int_vars: &[IntView]) {
		let InitRef::Propagator(prop) = self.init_ref else {
			panic!("enqueue_when_n_fixed can only be called for propagators")
		};
		assert!(
			n <= bool_vars.len() + int_vars.len(),
			"waiting on more fixed events than there are variables"
		);
		assert!(
			!self
				.slv
				.engine_mut()
				.state
				.fixed_daemons
				.contains_key(&prop),
			"propagator is already waiting on fixed events"
		);

		// Filter constants and extract variable references
		let mut lits = Vec::new();
		let mut ints = Vec::new();
		for bv in bool_vars {
			match bv.0 {
				BoolViewInner::Lit(lit) => lits.push(lit),
				BoolViewInner::Const(_) => n -= 1,
			}
		}
		for iv in int_vars {
			match iv.0 {
				IntViewInner::Bool { lit, .. } => lits.push(lit),
				IntViewInner::Const(_) => n -= 1,
				IntViewInner::Linear { var, .. } | IntViewInner::VarRef(var) => ints.push(var),
			}
		}

		if n <= 0 {
			todo!("immediately enqueue the propagator")
		}

		for lit in lits {
			self.slv.engine_mut().state.trail.grow_to_boolvar(lit.var());
			self.slv.oracle.add_observed_var(lit.var());
			self.slv
				.engine_mut()
				.state
				.bool_activation
				.entry(lit.var())
				.or_default()
				.add_fixed_daemon(prop);
		}
		for var in ints {
			self.slv.engine_mut().state.int_activation[var].add_fixed_daemon(prop)
		}

		let count = self.slv.engine_mut().state.trail.track_int(n as i64);
		let _ = self
			.slv
			.engine_mut()
			.state
			.fixed_daemons
			.insert(prop, count);
	}
}

impl<'a, Oracle: PropagatingSolver<Engine>> TrailingActions for InitializationContext<'a, Oracle> {
	delegate! {
		to self.slv.engine().state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
		}
		to self.slv.engine_mut().state {
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}

impl<'a, Oracle: PropagatingSolver<Engine>> InspectionActions
	for InitializationContext<'a, Oracle>
{
	delegate! {
		to self.slv.engine().state {
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}

impl<'a, Oracle: PropagatingSolver<Engine>> DecisionActions for InitializationContext<'a, Oracle> {
	delegate! {
		to self.slv {
			fn get_intref_lit(&mut self, var: IntVarRef, meaning: LitMeaning) -> BoolView;
			fn get_num_conflicts(&self) -> u64;
		}
	}
}
