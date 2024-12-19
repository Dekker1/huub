//! Propagators for the `int_abs` constraint, which enforces that one variable
//! is takes absolute value of another.

use std::iter::once;

use crate::{
	actions::{ExplanationActions, PropagatorInitActions},
	constraints::{Conflict, PropagationActions, Propagator},
	solver::{activation_list::IntPropCond, queue::PriorityLevel},
	IntView, LitMeaning,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Bounds propagator for one integer variable being the absolute value of another
pub struct IntAbsBounds {
	/// The integer variable whose absolute value is being taken
	origin: IntView,
	/// The integer variable representing the absolute value
	abs: IntView,
}

impl IntAbsBounds {
	/// Create a new [`IntAbsBounds`] propagator and post it in the solver.
	pub fn new_in(solver: &mut impl PropagatorInitActions, origin: IntView, abs: IntView) {
		let prop = solver.add_propagator(Box::new(Self { origin, abs }), PriorityLevel::Highest);
		// Subscribe to both bounds of the origin variable
		solver.enqueue_on_int_change(prop, origin, IntPropCond::Bounds);
		// Subscribe only to the upper bound of the absolute value variable
		solver.enqueue_on_int_change(prop, abs, IntPropCond::UpperBound);
	}
}

impl<P, E> Propagator<P, E> for IntAbsBounds
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_abs", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (lb, ub) = actions.get_int_bounds(self.origin);

		// If we know that the origin is negative, then just negate the bounds
		if ub < 0 {
			actions.set_int_upper_bound(self.abs, -lb, |a: &mut P| {
				vec![
					a.get_int_lower_bound_lit(self.origin),
					a.get_int_lit(self.origin, LitMeaning::Less(0)),
				]
			})?;
			actions.set_int_lower_bound(self.abs, -ub, |a: &mut P| {
				once(a.get_int_upper_bound_lit(self.origin))
			})?;
		} else if lb >= 0 {
			// If we know that the origin is positive, then the bounds are the same
			actions.set_int_lower_bound(self.abs, lb, |a: &mut P| {
				once(a.get_int_lower_bound_lit(self.origin))
			})?;
			actions.set_int_upper_bound(self.abs, ub, |a: &mut P| {
				vec![
					a.get_int_upper_bound_lit(self.origin),
					a.get_int_lit(self.origin, LitMeaning::GreaterEq(0)),
				]
			})?;
		} else {
			// If the origin can be either positive or negative, then the bounds are
			// the maximum of the absolute values
			let abs_max = ub.max(-lb);
			actions.set_int_upper_bound(self.abs, abs_max, |a: &mut P| {
				vec![
					a.get_int_lit(self.origin, LitMeaning::GreaterEq(-abs_max)),
					a.get_int_lit(self.origin, LitMeaning::Less(abs_max + 1)),
				]
			})?;
		}

		// If the upper bound of the absolute value variable have changed, we
		// propagate bounds of the origin variable
		let ub = actions.get_int_upper_bound(self.abs);
		let ub_lit = actions.get_int_upper_bound_lit(self.abs);
		actions.set_int_lower_bound(self.origin, -ub, ub_lit)?;
		actions.set_int_upper_bound(self.origin, ub, ub_lit)?;

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		constraints::int_abs::IntAbsBounds,
		solver::int_var::{EncodingType, IntVar},
		Solver,
	};

	#[test]
	#[traced_test]
	fn test_int_abs_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			(-3..=3).into(),
			EncodingType::Eager,
			EncodingType::Lazy,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([-3..=3]),
			EncodingType::Eager,
			EncodingType::Lazy,
		);

		IntAbsBounds::new_in(&mut slv, a, b);

		slv.expect_solutions(
			&[a, b],
			expect![[r#"
    -3, 3
    -2, 2
    -1, 1
    0, 0
    1, 1
    2, 2
    3, 3"#]],
		);
	}
}
