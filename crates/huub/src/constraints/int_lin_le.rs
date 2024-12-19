//! Propagator for the `int_lin_le` constraint, and its reification. This
//! constraint enforce that the sum of the products of the variables is less or
//! equal to a given value.

use itertools::Itertools;
use pindakaas::Lit as RawLit;

use crate::{
	actions::PropagatorInitActions,
	constraints::{Conflict, ExplanationActions, PropagationActions, Propagator},
	helpers::opt_field::OptField,
	solver::{
		activation_list::IntPropCond,
		queue::PriorityLevel,
		value::IntVal,
		view::{BoolViewInner, IntView, IntViewInner},
	},
	BoolView, Conjunction,
};

/// Type alias for the non-reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub(crate) type IntLinearLessEqBounds = IntLinearLessEqBoundsImpl<0>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `int_lin_le` or `int_lin_le_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not refied, or `1` if it is. Other
/// values are invalid.
pub struct IntLinearLessEqBoundsImpl<const R: usize> {
	/// Variables that are being summed
	vars: Vec<IntView>,
	/// Maximum value of the sum can take
	max: IntVal,
	/// Reified variable, if any
	reification: OptField<R, RawLit>,
}

/// Type alias for the reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub(crate) type IntLinearLessEqImpBounds = IntLinearLessEqBoundsImpl<1>;

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
				vars: vars.clone(),
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
			.vars
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
			.vars
			.iter()
			.map(|v| actions.get_int_lower_bound(*v))
			.fold(self.max, |sum, val| sum - val);

		// propagate the reified variable if the sum of lower bounds is greater than the right-hand-side value
		if let Some(&r) = self.reification.get() {
			if sum < 0 {
				actions.set_bool((!r).into(), |a: &mut P| {
					self.vars
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
		for (j, &v) in self.vars.iter().enumerate() {
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
				vars: vars.clone(),
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

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_lin_le::IntLinearLessEqBounds,
		solver::int_var::{EncodingType, IntVar},
		Constraint, InitConfig, Model, NonZeroIntVal, Solver,
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

		prb += Constraint::IntLinLessEq(vec![a * -2, -b, -c], -10);
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

		prb += Constraint::IntLinLessEq(vec![a * 2, b, c], 3);
		prb.assert_unsatisfiable();
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_ge_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += Constraint::IntLinLessEqImp(
			vec![
				a.clone() * NonZeroIntVal::new(-2).unwrap(),
				-b.clone(),
				-c.clone(),
			],
			-7,
			r.clone().into(),
		);
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

		prb += Constraint::IntLinLessEqImp(
			vec![
				a.clone() * NonZeroIntVal::new(2).unwrap(),
				b.clone(),
				c.clone(),
			],
			5,
			r.clone().into(),
		);
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
}
