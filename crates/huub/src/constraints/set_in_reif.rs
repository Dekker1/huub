//! Structures and algorithms for the `set_in_reif` constraint, which
//! constraints that an integer decision variable is assigned to a member of a
//! given set if-and-only-if a given Boolean decision variable is assigned to
//! `true`.

use crate::{
	actions::{ConstraintInitActions, ReformulationActions, SimplificationActions},
	constraints::{Constraint, SimplificationStatus},
	model::{bool::BoolView, int::IntExpr},
	BoolExpr, IntSetVal, ReformulationError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of the `set_in_reif` constraint within a model.
///
/// This constraint enforces that the given Boolean variable takes the value
/// `true` if-and-only-if an integer variable is in a given set.
pub struct SetInReif {
	/// The integer decision variable monitored.
	pub(crate) var: IntExpr,
	/// The set of considered values for the integer decision variable.
	pub(crate) set: IntSetVal,
	/// The Boolean variable that indicates if the integer decision variable is in
	/// the set.
	pub(crate) reif: BoolView,
}

impl Constraint for SetInReif {
	fn initialize(&self, actions: &mut impl ConstraintInitActions) {
		actions.simplify_on_change_bool(self.reif);
	}

	fn simplify(
		&mut self,
		actions: &mut impl SimplificationActions,
	) -> Result<SimplificationStatus, ReformulationError> {
		match actions.get_bool_val(self.reif) {
			Some(true) => {
				actions.set_int_in_set(self.var, &self.set)?;
				Ok(SimplificationStatus::Subsumed)
			}
			Some(false) => {
				actions.set_int_not_in_set(self.var, &self.set)?;
				Ok(SimplificationStatus::Subsumed)
			}
			None => Ok(SimplificationStatus::Fixpoint),
		}
	}

	fn to_solver(&self, slv: &mut impl ReformulationActions) -> Result<(), ReformulationError> {
		if self.set.iter().len() == 1 {
			let lb = *self.set.lower_bound().unwrap();
			let ub = *self.set.upper_bound().unwrap();
			BoolExpr::Equiv(vec![
				BoolExpr::And(vec![self.var.geq(lb).into(), self.var.leq(ub).into()]),
				self.reif.into(),
			])
			.to_solver(slv)
		} else {
			let eq_lits = self
				.set
				.iter()
				.flatten()
				.map(|v| self.var.eq(v).into())
				.collect();
			BoolExpr::Equiv(vec![self.reif.into(), BoolExpr::Or(eq_lits)]).to_solver(slv)
		}
	}
}
