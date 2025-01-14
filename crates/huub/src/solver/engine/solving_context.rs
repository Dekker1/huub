use delegate::delegate;
use index_vec::IndexVec;
use pindakaas::{solver::SolvingActions, Lit as RawLit};
use tracing::trace;

use crate::{
	actions::{
		decision::DecisionActions, explanation::ExplanationActions, inspection::InspectionActions,
		propagation::PropagationActions, trailing::TrailingActions,
	},
	propagator::{
		conflict::Conflict,
		reason::{LazyReason, ReasonBuilder},
	},
	solver::{
		engine::{
			int_var::{IntVarRef, LazyLitDef},
			trace_new_lit,
			trail::TrailedInt,
			PropRef, State,
		},
		poster::BoxedPropagator,
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, Clause, IntVal, IntView, LitMeaning,
};

pub(crate) struct SolvingContext<'a> {
	/// Actions to create new variables in the oracle
	pub(crate) slv: &'a mut dyn SolvingActions,
	/// Engine state object
	pub(crate) state: &'a mut State,
	/// Current propagator being executed
	pub(crate) current_prop: PropRef,
}

enum ChangeType {
	Redundant,
	New,
	Conflicting,
}

impl<'a> SolvingContext<'a> {
	pub(crate) fn new(slv: &'a mut dyn SolvingActions, state: &'a mut State) -> Self {
		Self {
			slv,
			state,
			current_prop: PropRef::new(u32::MAX as usize),
		}
	}

	pub(crate) fn run_propagators(&mut self, propagators: &mut IndexVec<PropRef, BoxedPropagator>) {
		while let Some(p) = self.state.propagator_queue.pop() {
			debug_assert!(self.state.conflict.is_none());
			self.state.enqueued[p] = false;
			self.current_prop = p;
			let prop = propagators[p].as_mut();
			let res = prop.propagate(self);
			self.state.statistics.propagations += 1;
			self.current_prop = PropRef::new(u32::MAX as usize);
			if let Err(Conflict { subject, reason }) = res {
				let mut clause: Clause = reason.to_clause(propagators, self.state);
				if let Some(subject) = subject {
					clause.push(subject);
				}
				trace!(clause = ?clause.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "conflict detected");
				debug_assert!(!clause.is_empty());
				debug_assert!(self.state.conflict.is_none());
				self.state.conflict = Some(clause);
			}
			if self.state.conflict.is_some() || !self.state.propagation_queue.is_empty() {
				return;
			}
		}
	}

	#[inline]
	fn check_change(&self, var: IntVarRef, change: &LitMeaning) -> ChangeType {
		let (lb, ub) = self.state.int_vars[var].get_bounds(self);
		match change {
			LitMeaning::Eq(i) if lb == *i && ub == *i => ChangeType::Redundant,
			LitMeaning::Eq(i) if *i < lb || *i > ub => ChangeType::Conflicting,
			LitMeaning::NotEq(i) if *i < lb || *i > ub => ChangeType::Redundant,
			LitMeaning::Eq(_) | LitMeaning::NotEq(_) => {
				let lit = self.state.int_vars[var].get_bool_lit(change.clone());
				let val = lit.and_then(|lit| self.get_bool_val(lit));
				match val {
					Some(true) => ChangeType::Redundant,
					Some(false) => ChangeType::Conflicting,
					None => ChangeType::New,
				}
			}
			LitMeaning::GreaterEq(i) if *i <= lb => ChangeType::Redundant,
			LitMeaning::GreaterEq(i) if *i > ub => ChangeType::Conflicting,
			LitMeaning::Less(i) if *i > ub => ChangeType::Redundant,
			LitMeaning::Less(i) if *i <= lb => ChangeType::Conflicting,
			_ => ChangeType::New,
		}
	}

	#[inline]
	fn propagate_int(
		&mut self,
		iv: IntVarRef,
		lit_req: LitMeaning,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		match self.check_change(iv, &lit_req) {
			ChangeType::Redundant => Ok(()),
			ChangeType::Conflicting => {
				let bv = self.get_intref_lit(iv, lit_req.clone());
				let lit = match bv.0 {
					BoolViewInner::Lit(l) => Some(l),
					BoolViewInner::Const(b) => {
						debug_assert!(!b);
						None
					}
				};
				Err(Conflict::new(self, lit, reason))
			}
			ChangeType::New => {
				let bv = self.get_intref_lit(iv, lit_req.clone());
				self.set_bool_val(bv, true, reason)
			}
		}
	}

	#[inline]
	fn propagate_bool_lin(
		&mut self,
		lit: RawLit,
		lit_req: LitMeaning,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		match lit_req {
			LitMeaning::Eq(0) | LitMeaning::Less(1) | LitMeaning::NotEq(1) => {
				self.set_bool_val(BoolView(BoolViewInner::Lit(lit)), false, reason)
			}
			LitMeaning::Eq(1) | LitMeaning::GreaterEq(1) | LitMeaning::NotEq(0) => {
				self.set_bool_val(BoolView(BoolViewInner::Lit(lit)), true, reason)
			}
			LitMeaning::Eq(_) => Err(Conflict::new(self, None, reason)),
			LitMeaning::GreaterEq(i) if i > 1 => Err(Conflict::new(self, None, reason)),
			LitMeaning::Less(i) if i <= 0 => Err(Conflict::new(self, None, reason)),
			LitMeaning::NotEq(_) | LitMeaning::GreaterEq(_) | LitMeaning::Less(_) => Ok(()),
		}
	}
}

impl DecisionActions for SolvingContext<'_> {
	fn get_intref_lit(&mut self, iv: IntVarRef, meaning: LitMeaning) -> BoolView {
		let var = &mut self.state.int_vars[iv];
		let new_var = |def: LazyLitDef| {
			// Create new variable
			let v = self.slv.new_var();
			trace_new_lit!(iv, def, v);
			self.slv.add_observed_var(v);
			self.state
				.bool_to_int
				.insert_lazy(v, iv, def.meaning.clone());
			// Add clauses to define the new variable
			for cl in def.meaning.defining_clauses(
				v.into(),
				def.prev.map(Into::into),
				def.next.map(Into::into),
			) {
				self.state.clauses.push_back(cl);
			}
			v
		};
		var.bool_lit(meaning, new_var)
	}
}

impl ExplanationActions for SolvingContext<'_> {
	delegate! {
		to self.state {
			fn try_int_lit(&self, var: IntView, meaning: LitMeaning) -> Option<BoolView>;
			fn get_int_lit_relaxed(&mut self, var: IntView, meaning: LitMeaning) -> (BoolView, LitMeaning);
			fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;
			fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
		}
	}

	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		let val = self.get_int_val(var)?;
		Some(self.get_int_lit(var, LitMeaning::Eq(val)))
	}
}

impl InspectionActions for SolvingContext<'_> {
	delegate! {
		to self.state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}

impl PropagationActions for SolvingContext<'_> {
	fn set_bool_val(
		&mut self,
		bv: BoolView,
		val: bool,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		match bv.0 {
			BoolViewInner::Lit(lit) => match self.state.trail.get_sat_value(lit) {
				Some(b) if b == val => Ok(()),
				Some(_) => Err(Conflict::new(
					self,
					Some(if val { lit } else { !lit }),
					reason,
				)),
				None => {
					let propagated_lit = if val { lit } else { !lit };
					let reason = reason.build_reason(self);
					trace!(lit = i32::from(propagated_lit), reason = ?reason, "propagate bool");
					self.state.register_reason(propagated_lit, reason);
					self.state.propagation_queue.push(propagated_lit);
					let prev = self.state.trail.assign_sat(propagated_lit);
					debug_assert!(prev.is_none());
					Ok(())
				}
			},
			BoolViewInner::Const(b) => {
				if b != val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}

	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::GreaterEq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			lit_req = transformer.rev_transform_lit(lit_req).unwrap();
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i < val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}
	fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::Less(val + 1);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			lit_req = transformer.rev_transform_lit(lit_req).unwrap();
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i > val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}
	fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::Eq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			match transformer.rev_transform_lit(lit_req) {
				Ok(lit) => lit_req = lit,
				Err(v) => {
					debug_assert!(!v);
					return Err(Conflict::new(self, None, reason));
				}
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i != val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}
	fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict> {
		let mut lit_req = LitMeaning::NotEq(val);
		if let IntViewInner::Linear { transformer, .. } | IntViewInner::Bool { transformer, .. } =
			var.0
		{
			match transformer.rev_transform_lit(lit_req) {
				Ok(lit) => lit_req = lit,
				Err(v) => {
					debug_assert!(v);
					return Ok(());
				}
			}
		}

		match var.0 {
			IntViewInner::VarRef(iv) | IntViewInner::Linear { var: iv, .. } => {
				self.propagate_int(iv, lit_req, reason)
			}
			IntViewInner::Bool { lit, .. } => self.propagate_bool_lin(lit, lit_req, reason),
			IntViewInner::Const(i) => {
				if i == val {
					Err(Conflict::new(self, None, reason))
				} else {
					Ok(())
				}
			}
		}
	}

	fn deferred_reason(&self, data: u64) -> LazyReason {
		LazyReason(self.current_prop, data)
	}
}

impl TrailingActions for SolvingContext<'_> {
	delegate! {
		to self.state {
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}
