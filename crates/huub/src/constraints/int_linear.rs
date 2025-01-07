//! Structures and algorithms  for the integer linear constraint, including
//! `int_lin_eq`, `int_lin_le`, `int_lin_ne` and their reification. These
//! constraint enforce a condition on the sum of (linear transformations of)
//! integer decision variables.

use itertools::Itertools;
use pindakaas::Lit as RawLit;

use crate::{
	actions::{PropagatorInitActions, ReformulationActions, SimplificationActions},
	constraints::{
		Conflict, Constraint, ExplanationActions, PropagationActions, Propagator, ReasonBuilder,
		SimplificationStatus,
	},
	helpers::opt_field::OptField,
	model::{bool::BoolView as ModelBoolView, int::IntExpr},
	solver::{
		activation_list::IntPropCond,
		queue::PriorityLevel,
		value::IntVal,
		view::{BoolView, BoolViewInner, IntView, IntViewInner},
	},
	Conjunction, ReformulationError,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Possible operators that can be used for in a linear constraint.
pub(crate) enum LinOperator {
	/// Sum is equal to the constant
	Equal,
	/// Sum is less than or equal to the constant
	LessEq,
	/// Sum is not equal to the constant
	NotEqual,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Representation of an integer linear constraint within a model.
///
/// This constraint enforces that a sum of (linear transformations of) integer
/// decision variables is less than, equal, or not equal to a constant value, or
/// the implication or reification or whether this is so.
pub struct IntLinear {
	/// The integer linear terms that are being summed.
	pub(crate) terms: Vec<IntExpr>,
	/// The operator that is used to compare the sum to the right-hand side.
	pub(crate) operator: LinOperator,
	/// The constant right-hand side value.
	pub(crate) rhs: IntVal,
	/// Boolean decision varaible that (half-)reifies the constraint, if any.
	pub(crate) reif: Option<Reification>,
}

/// Type alias for the non-reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqBounds = IntLinearLessEqBoundsImpl<0>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `int_lin_le` or `int_lin_le_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not refied, or `1` if it is. Other
/// values are invalid.
pub struct IntLinearLessEqBoundsImpl<const R: usize> {
	/// Variables that are being summed
	terms: Vec<IntView>,
	/// Maximum value of the sum can take
	max: IntVal,
	/// Reified variable, if any
	reification: OptField<R, RawLit>,
}

/// Type alias for the reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqImpBounds = IntLinearLessEqBoundsImpl<1>;

/// Type alias for the reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqImpValue = IntLinearNotEqValueImpl<1>;

/// Type alias for the non-reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqValue = IntLinearNotEqValueImpl<0>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `int_lin_ne` or `int_lin_ne_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not refied, or `1` if it is. Other
/// values are invalid.
pub struct IntLinearNotEqValueImpl<const R: usize> {
	/// Variables in the sumation
	terms: Vec<IntView>,
	/// The value the sumation should not equal
	violation: IntVal,
	/// Reified variable, if any
	reification: OptField<R, RawLit>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Reification possibilities for a linear constraint.
pub(crate) enum Reification {
	/// The constraint is half-reified by the given [`ModelBoolView`].
	ImpliedBy(ModelBoolView),
	/// The constraint is reified by the given [`ModelBoolView`].
	ReifiedBy(ModelBoolView),
}

impl IntLinear {
	/// Change the integer linear constraint to be implied by the given Boolean
	/// decision variable.
	///
	/// The integer linear constraint must hold when the given Boolean decision
	/// variable is `true`. If the constraint does not hold, then the Boolean
	/// decision variable must be `false`.
	pub fn implied_by(self, b: ModelBoolView) -> Self {
		assert!(
			self.reif.is_none(),
			"IntLinear is already implied or reified."
		);
		Self {
			reif: Some(Reification::ImpliedBy(b)),
			..self
		}
	}

	/// Change the integer linear constraint to be reified by the given Boolean
	/// decision variable.
	///
	/// The integer linear constraint must hold if-and-only-if the given Boolean
	/// decision variable is `true`.
	pub fn reified_by(self, b: ModelBoolView) -> Self {
		assert!(
			self.reif.is_none(),
			"IntLinear is already implied or reified."
		);
		Self {
			reif: Some(Reification::ReifiedBy(b)),
			..self
		}
	}

	/// Internal method to negate the linear constraint.
	fn negate(self) -> Self {
		match self.operator {
			LinOperator::Equal => Self {
				operator: LinOperator::NotEqual,
				..self
			},
			LinOperator::LessEq => Self {
				terms: self.terms.into_iter().map(|v| -v).collect(),
				rhs: -self.rhs,
				..self
			},
			LinOperator::NotEqual => Self {
				operator: LinOperator::Equal,
				..self
			},
		}
	}
}

impl Constraint for IntLinear {
	fn simplify(
		&mut self,
		actions: &mut impl SimplificationActions,
	) -> Result<SimplificationStatus, ReformulationError> {
		// If the reification of the constriant is known, simplify to non-reified version
		if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
			match actions.get_bool_val(r) {
				Some(true) => {
					let mut lin = self.clone();
					lin.reif = None;
					actions.add_constraint(lin);
					return Ok(SimplificationStatus::Subsumed);
				}
				Some(false) => {
					if matches!(self.reif.unwrap(), Reification::ReifiedBy(_)) {
						let mut lin = self.clone().negate();
						lin.reif = None;
						actions.add_constraint(lin);
					}
					return Ok(SimplificationStatus::Subsumed);
				}
				None => {}
			}
		}

		// Collect variable bounds and create their sums
		let lb = self
			.terms
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.collect_vec();
		let ub = self
			.terms
			.iter()
			.map(|v| actions.get_int_upper_bound(*v))
			.collect_vec();

		let lb_sum = self.rhs - lb.iter().sum::<IntVal>();
		let ub_sum = self.rhs - ub.iter().sum::<IntVal>();

		// Detection for not-equal constraints. Mark as subsumed, unsatisfiable, or
		// stop.
		if self.operator == LinOperator::NotEqual {
			if self.rhs < lb_sum || self.rhs > ub_sum {
				if let Some(Reification::ReifiedBy(r)) = self.reif {
					actions.set_bool(r)?;
				}
				return Ok(SimplificationStatus::Subsumed);
			} else if lb_sum == ub_sum && lb_sum == self.rhs {
				if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
					actions.set_bool(!r)?;
					return Ok(SimplificationStatus::Subsumed);
				}
				return Err(ReformulationError::TrivialUnsatisfiable);
			}
			return Ok(SimplificationStatus::Fixpoint);
		}
		debug_assert_ne!(self.operator, LinOperator::NotEqual);

		// Check whether LessEq constraint are already subsumed
		if self.operator == LinOperator::LessEq && ub_sum < self.rhs {
			if let Some(Reification::ReifiedBy(r)) = self.reif {
				actions.set_bool(r)?;
			}
			return Ok(SimplificationStatus::Subsumed);
		}

		// Propagate the upper bounds of the variables
		for (i, &v) in self.terms.iter().enumerate() {
			let new_ub = lb_sum + lb[i];
			if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
				if lb[i] > new_ub {
					actions.set_bool(!r)?;
					return Ok(SimplificationStatus::Subsumed);
				}
			} else {
				actions.set_int_upper_bound(v, new_ub)?;
			}
		}

		// For equality constriants, propagate the lower bounds of the variables
		if self.operator == LinOperator::Equal {
			for (i, &v) in self.terms.iter().enumerate() {
				let new_lb = ub_sum + ub[i];
				if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
					if ub[i] < new_lb {
						actions.set_bool(!r)?;
						return Ok(SimplificationStatus::Subsumed);
					}
				} else {
					actions.set_int_lower_bound(v, new_lb)?;
				}
			}
		}
		Ok(SimplificationStatus::Fixpoint)
	}

	fn to_solver(&self, slv: &mut impl ReformulationActions) -> Result<(), ReformulationError> {
		use Reification::*;

		let terms = self
			.terms
			.iter()
			.map(|&v| slv.get_solver_int(v))
			.collect_vec();
		let r = self.reif.as_ref().map(|&r| {
			slv.get_solver_bool(match r {
				ImpliedBy(r) | ReifiedBy(r) => r,
			})
		});
		let full_reif = matches!(self.reif, Some(ReifiedBy(_)));

		match (self.operator, r) {
			(LinOperator::Equal, None) => {
				// coeffs * vars >= c <=> -coeffs * vars <= -c
				IntLinearLessEqBounds::new_in(slv, terms.iter().map(|&v| -v), -self.rhs);
				// coeffs * vars <= c
				IntLinearLessEqBounds::new_in(slv, terms.clone(), self.rhs);
			}
			(LinOperator::Equal, Some(r)) => {
				if full_reif {
					IntLinearNotEqImpValue::new_in(slv, terms.clone(), self.rhs, !r);
				}
				IntLinearLessEqImpBounds::new_in(slv, terms.iter().map(|&v| -v), -self.rhs, r);
				IntLinearLessEqImpBounds::new_in(slv, terms, self.rhs, r);
			}
			(LinOperator::LessEq, None) => {
				IntLinearLessEqBounds::new_in(slv, terms, self.rhs);
			}
			(LinOperator::LessEq, Some(r)) => {
				if full_reif {
					IntLinearLessEqImpBounds::new_in(
						slv,
						terms.iter().map(|&v| -v),
						-(self.rhs + 1),
						!r,
					);
				}
				IntLinearLessEqImpBounds::new_in(slv, terms, self.rhs, r);
			}
			(LinOperator::NotEqual, None) => {
				IntLinearNotEqValue::new_in(slv, terms, self.rhs);
			}
			(LinOperator::NotEqual, Some(r)) => {
				if full_reif {
					IntLinearLessEqImpBounds::new_in(slv, terms.clone(), self.rhs, !r);
					IntLinearLessEqImpBounds::new_in(slv, terms.iter().map(|&v| -v), -self.rhs, !r);
				}
				IntLinearNotEqImpValue::new_in(slv, terms, self.rhs, r);
			}
		}
		Ok(())
	}
}

impl IntLinearLessEqBounds {
	/// Create a new [`IntLinearLessEqBounds`] propagator and post it in the
	/// solver.
	pub fn new_in(
		solver: &mut impl PropagatorInitActions,
		vars: impl IntoIterator<Item = IntView>,
		mut max: IntVal,
	) {
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let IntViewInner::Const(c) = v.0 {
					max -= c;
					false
				} else {
					true
				}
			})
			.collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				max,
				reification: Default::default(),
			}),
			PriorityLevel::Low,
		);
		solver.enqueue_now(prop);
		for &v in vars.iter() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::UpperBound);
		}
	}
}

impl<const R: usize, P, E> Propagator<P, E> for IntLinearLessEqBoundsImpl<R>
where
	P: PropagationActions,
	E: ExplanationActions,
{
	fn explain(&mut self, actions: &mut E, _: Option<RawLit>, data: u64) -> Conjunction {
		let i = data as usize;
		let mut var_lits: Vec<RawLit> = self
			.terms
			.iter()
			.enumerate()
			.filter_map(|(j, v)| {
				if j == i {
					return None;
				}
				if let BoolView(BoolViewInner::Lit(lit)) = actions.get_int_lower_bound_lit(*v) {
					Some(lit)
				} else {
					None
				}
			})
			.collect();
		if let Some(r) = self.reification.get() {
			var_lits.push(*r);
		}
		var_lits
	}
	// propagation rule: x[i] <= rhs - sum_{j != i} x[j].lower_bound
	#[tracing::instrument(name = "int_lin_le", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		// If the reified variable is false, skip propagation
		if let Some(&r) = self.reification.get() {
			if !actions.get_bool_val(r.into()).unwrap_or(true) {
				return Ok(());
			}
		}

		// get the difference between the right-hand-side value and the sum of variable lower bounds
		let sum = self
			.terms
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.fold(self.max, |sum, val| sum - val);

		// propagate the reified variable if the sum of lower bounds is greater than the right-hand-side value
		if let Some(&r) = self.reification.get() {
			if sum < 0 {
				actions.set_bool((!r).into(), |a: &mut P| {
					self.terms
						.iter()
						.map(|v| a.get_int_lower_bound_lit(*v))
						.collect_vec()
				})?;
			}
			// skip the remaining propagation if the reified variable is not assigned to true
			if !actions.get_bool_val(r.into()).unwrap_or(false) {
				return Ok(());
			}
		}

		// propagate the upper bound of the variables
		for (j, &v) in self.terms.iter().enumerate() {
			let reason = actions.deferred_reason(j as u64);
			let ub = sum + actions.get_int_lower_bound(v);
			actions.set_int_upper_bound(v, ub, reason)?;
		}
		Ok(())
	}
}

impl IntLinearLessEqImpBounds {
	/// Create a new [`IntLinearLessEqImpBounds`] propagator and post it in the
	/// solver.
	pub fn new_in(
		solver: &mut impl PropagatorInitActions,
		vars: impl IntoIterator<Item = IntView>,
		mut max: IntVal,
		reification: BoolView,
	) {
		let reification = match reification.0 {
			BoolViewInner::Lit(r) => r,
			BoolViewInner::Const(true) => return IntLinearLessEqBounds::new_in(solver, vars, max),
			BoolViewInner::Const(false) => return,
		};
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let IntViewInner::Const(c) = v.0 {
					max -= c;
					false
				} else {
					true
				}
			})
			.collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				max,
				reification: OptField::new(reification),
			}),
			PriorityLevel::Low,
		);
		solver.enqueue_now(prop);
		for &v in vars.iter() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::UpperBound);
		}
		solver.enqueue_on_bool_change(prop, reification.into());
	}
}

impl IntLinearNotEqImpValue {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn new_in(
		solver: &mut impl PropagatorInitActions,
		vars: impl IntoIterator<Item = IntView>,
		mut violation: IntVal,
		reification: BoolView,
	) {
		let reification = match reification.0 {
			BoolViewInner::Lit(r) => r,
			BoolViewInner::Const(true) => {
				return IntLinearNotEqValue::new_in(solver, vars, violation)
			}
			BoolViewInner::Const(false) => return,
		};

		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let IntViewInner::Const(c) = v.0 {
					violation -= c;
					false
				} else {
					true
				}
			})
			.collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				violation,
				reification: OptField::new(reification),
			}),
			PriorityLevel::Low,
		);

		for &v in vars.iter() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Fixed);
		}
		solver.enqueue_on_bool_change(prop, reification.into());
	}
}

impl IntLinearNotEqValue {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	pub fn new_in(
		solver: &mut impl PropagatorInitActions,
		vars: impl IntoIterator<Item = IntView>,
		mut violation: IntVal,
	) {
		let vars: Vec<IntView> = vars
			.into_iter()
			.filter(|v| {
				if let IntViewInner::Const(c) = v.0 {
					violation -= c;
					false
				} else {
					true
				}
			})
			.collect();

		let prop = solver.add_propagator(
			Box::new(Self {
				terms: vars.clone(),
				violation,
				reification: Default::default(),
			}),
			PriorityLevel::Low,
		);

		for &v in vars.iter() {
			solver.enqueue_on_int_change(prop, v, IntPropCond::Fixed);
		}
	}
}

impl<const R: usize> IntLinearNotEqValueImpl<R> {
	/// Helper function to construct the reason for propagation given the index of
	/// the variable in the list of variables to sum or the length of the list, if
	/// explaining the reification.
	fn reason<A: ExplanationActions>(&self, data: usize) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let mut conj: Vec<_> = self
				.terms
				.iter()
				.enumerate()
				.filter_map(|(i, v)| {
					if data != i {
						Some(actions.get_int_val_lit(*v).unwrap())
					} else {
						None
					}
				})
				.collect();
			if let Some(&r) = self.reification.get() {
				if data != self.terms.len() {
					conj.push(r.into());
				}
			}
			conj
		}
	}
}

impl<const R: usize, P, E> Propagator<P, E> for IntLinearNotEqValueImpl<R>
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_lin_ne", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (r, r_fixed) = if let Some(&r) = self.reification.get() {
			let r_bv = r.into();
			match actions.get_bool_val(r_bv) {
				Some(false) => return Ok(()),
				Some(true) => (r_bv, true),
				None => (r_bv, false),
			}
		} else {
			(true.into(), true)
		};
		let mut sum = 0;
		let mut unfixed = None;
		for (i, v) in self.terms.iter().enumerate() {
			if let Some(val) = actions.get_int_val(*v) {
				sum += val;
			} else if unfixed.is_some() {
				return Ok(());
			} else {
				unfixed = Some((i, v));
			}
		}
		if let Some((i, v)) = unfixed {
			if !r_fixed {
				return Ok(());
			}
			let val = self.violation - sum;
			actions.set_int_not_eq(*v, val, self.reason(i))
		} else if sum == self.violation {
			actions.set_bool(!r, self.reason(self.terms.len()))
		} else {
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_linear::{IntLinearLessEqBounds, IntLinearNotEqValue},
		solver::int_var::{EncodingType, IntVar},
		InitConfig, Model, NonZeroIntVal, Solver,
	};

	#[test]
	#[traced_test]
	fn test_linear_ge_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntLinearLessEqBounds::new_in(
			&mut slv,
			vec![a * NonZeroIntVal::new(-2).unwrap(), -b, -c],
			-6,
		);

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			1, 2, 2
			2, 1, 1
			2, 1, 2
			2, 2, 1
			2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_linear_ge_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += (a * 2 + b + c).geq(10);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_linear_le_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntLinearLessEqBounds::new_in(&mut slv, vec![a * NonZeroIntVal::new(2).unwrap(), b, c], 6);

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
			1, 1, 1
			1, 1, 2
			1, 2, 1
			1, 2, 2
			2, 1, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_linear_le_unsat() {
		let mut prb = Model::default();
		let a = prb.new_int_var((1..=4).into());
		let b = prb.new_int_var((1..=4).into());
		let c = prb.new_int_var((1..=4).into());

		prb += (a * 2 + b + c).leq(3);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_linear_ne_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		IntLinearNotEqValue::new_in(&mut slv, vec![a * NonZeroIntVal::new(2).unwrap(), b, c], 6);

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
		1, 1, 1
		1, 1, 2
		1, 2, 1
		2, 1, 2
		2, 2, 1
		2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_ge_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += (a * 2 + b + c).geq(7).implied_by(r);
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
		false, 1, 1, 1
		false, 1, 1, 2
		false, 1, 2, 1
		false, 1, 2, 2
		false, 2, 1, 1
		false, 2, 1, 2
		false, 2, 2, 1
		false, 2, 2, 2
		true, 2, 1, 2
		true, 2, 2, 1
		true, 2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_le_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += (a * 2 + b + c).leq(5).implied_by(r);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
		false, 1, 1, 1
		false, 1, 1, 2
		false, 1, 2, 1
		false, 1, 2, 2
		false, 2, 1, 1
		false, 2, 1, 2
		false, 2, 2, 1
		false, 2, 2, 2
		true, 1, 1, 1
		true, 1, 1, 2
		true, 1, 2, 1"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_ne_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += (a * 2 + b + c).ne(6).implied_by(r);

		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
		false, 1, 1, 1
		false, 1, 1, 2
		false, 1, 2, 1
		false, 1, 2, 2
		false, 2, 1, 1
		false, 2, 1, 2
		false, 2, 2, 1
		false, 2, 2, 2
		true, 1, 1, 1
		true, 1, 1, 2
		true, 1, 2, 1
		true, 2, 1, 2
		true, 2, 2, 1
		true, 2, 2, 2"#]],
		);
	}
}
