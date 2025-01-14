use crate::{
	actions::initialization::InitializationActions,
	brancher::Brancher,
	propagator::Propagator,
	solver::engine::{queue::PriorityLevel, solving_context::SolvingContext, trail::Trail, State},
};

pub(crate) type BoxedPropagator = Box<dyn for<'a> Propagator<SolvingContext<'a>, State, Trail>>;

/// The trait used called to registering a propagator with the solver.
pub(crate) trait Poster {
	/// Register the propagator with the solver.
	///
	/// This method is expected to return the propagator to be registered and a
	/// boolean indicating whether the propagator should be placed in the
	/// propagation queue.
	///
	/// The post method is given access to the solver's initialization actions,
	/// which includes the ability to subscribe to variable events, creating
	/// trailed data structures, and inspecting the current state of varaibles.
	fn post<I: InitializationActions>(self, actions: &mut I)
		-> (BoxedPropagator, QueuePreferences);
}

pub(crate) struct QueuePreferences {
	/// Whether to immediately add the propagator to the queue when the propagator is posted
	pub(crate) enqueue_on_post: bool,
	/// Priority level in the queue used for the propagator
	pub(crate) priority: PriorityLevel,
}

/// The trait used to register a brancher with the solver.
pub(crate) trait BrancherPoster {
	/// Register the brancher with the solver.
	///
	/// This method is expected to return the brancher to be registered.
	///
	/// The post method is given access to the solver's initialization actions,
	/// which includes the ability to subscribe to variable events, creating
	/// trailed data structures, and inspecting the current state of varaibles.
	fn post<I: InitializationActions>(self, actions: &mut I) -> Brancher;
}
