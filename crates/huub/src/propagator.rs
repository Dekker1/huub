//! Module containing the definitions for propagators and their implementations.

pub(crate) mod all_different_int;
pub(crate) mod array_int_minimum;
pub(crate) mod array_var_int_element;
pub(crate) mod conflict;
pub(crate) mod disjunctive_strict;
pub(crate) mod int_abs;
pub(crate) mod int_div;
pub(crate) mod int_lin_le;
pub(crate) mod int_lin_ne;
pub(crate) mod int_pow;
pub(crate) mod int_times;
pub(crate) mod reason;

use std::fmt::Debug;

use pindakaas::Lit as RawLit;

use crate::{
	actions::{ExplanationActions, PropagationActions},
	propagator::conflict::Conflict,
	solver::{
		engine::{solving_context::SolvingContext, State},
		poster::BoxedPropagator,
	},
	Conjunction,
};

/// A trait for a propagator that is called during the search process to filter
/// the domains of decision variables, and detect inconsistencies.
///
/// Implementations of the propagator trait must be able to explain changes to
/// domains of decision variables as a conjunction of literals that imply the
/// change. If these explanations are too expensive to compute during
/// propagation, then the propagator can delay giving the explanation using
/// [`PropagationActions::deferred_reason`]. If the explanation is needed, then
/// the propagation engine will revert the state of the solver and call
/// [`Propagator::explain`] to receive the explanation.
pub(crate) trait Propagator<P: PropagationActions, E: ExplanationActions>:
	Debug + DynPropClone
{
	/// The propagate method is called during the search process to allow the
	/// propagator to enforce
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let _ = actions;
		Ok(())
	}

	/// Explain a lazy reason that was emitted.
	///
	/// This method is called by the engine when a conflict is found involving a
	/// lazy explaination emitted by the propagator. The propagator must now
	/// produce the conjunction of literals that led to a literal being
	/// propagated.
	///
	/// The method is called with the data that was passed to the
	/// [`PropagationActions::deferred_reason`] method, and the literal that was
	/// propagated. If the `lit` argument is `None`, then the reason was used to
	/// explain `false`.
	///
	/// The state of the solver is reverted to the state before the propagation of
	/// the `lit` to be explained.
	fn explain(&mut self, actions: &mut E, lit: Option<RawLit>, data: u64) -> Conjunction {
		let _ = actions;
		let _ = lit;
		let _ = data;
		// Method will only be called if `propagate` used a lazy reason.
		panic!("propagator did not provide an explain implementation")
	}
}

/// A trait to allow the cloning of boxed propagators.
///
/// This trait allows us to implement [`Clone`] for [`BoxedPropagator`].
pub(crate) trait DynPropClone {
	/// Clone the object and store it as a boxed trait object.
	fn clone_dyn_prop(&self) -> BoxedPropagator;
}

impl<P: for<'a> Propagator<SolvingContext<'a>, State> + Clone + 'static> DynPropClone for P {
	fn clone_dyn_prop(&self) -> BoxedPropagator {
		Box::new(self.clone())
	}
}

impl Clone for BoxedPropagator {
	fn clone(&self) -> BoxedPropagator {
		self.clone_dyn_prop()
	}
}
