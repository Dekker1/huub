//! Module containing data structures for the activation of propagators based on
//! changes to decision variables.

use std::{
	mem,
	ops::{Add, AddAssign},
};

use crate::{
	IntVal,
	actions::{IntEvent, IntPropCond},
	model::{self, ConRef},
	solver::engine::{self, PropRef},
};

/// Possible actions to be triggered by the activation list.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ActivationAction<A, P> {
	/// When activated, advise the propagator with the given [`PropRef`] of the
	/// event that triggered the activation. If the advisor method returns
	/// `true`, then enqueue the propagator if it is not already in the queue.
	Advise(A),
	/// When activated, simply add the propagator with the given [`PropRef`] to
	/// the propagator queue if it is not already in the queue.
	Enqueue(P),
}

/// Object used to efficiently store an [`ActivationAction`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ActivationActionS(u32);

/// A data structure that stores a list of propagators to be enqueued based on
/// different propagation conditions.
///
/// The list is sorted in the following order of propagation condition:
/// Fixed, LowerBound, UpperBound, Bound, Domain.
///
/// Unless the condition is LowerBound, enqueueing can start from the index
/// of the most specific condition and enqueue all propagators until the end
/// of the list. If the condition is LowerBound, enqueueing can start from the
/// index of the LowerBound condition, enqueue all propagators until the
/// beginning of the UpperBound condition, and then continue from the beginning
/// of the Bound condition to the end of the list.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ActivationList {
	/// The list of propagators that are to be enqueued based on different
	/// propagation conditions.
	activations: Vec<ActivationActionS>,
	/// The index for the first propagator to be activated when an event
	/// triggers [`IntPropCond::LowerBound`].
	lower_bound_idx: u32,
	/// The index for the first propagator to be activated when an event
	/// triggers [`IntPropCond::UpperBound`].
	upper_bound_idx: u32,
	/// The first index for the propagators to be activated when an event
	/// triggers [`IntPropCond::Bounds`].
	bounds_idx: u32,
	/// The index for the first propagator to be activated when an event
	/// triggers [`IntPropCond::Domain`].
	domain_idx: u32,
}

/// A change to the domain of an integer decision variable, carrying enough
/// information to describe it to any subscriber.
///
/// The values are in the value space of the decision variable itself, not of
/// any view a subscriber may have registered with.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct IntChange {
	/// The event describing the change as a whole.
	pub(crate) event: IntEvent,
	/// The bounds of the decision variable immediately before the change.
	pub(crate) previous: (IntVal, IntVal),
	/// The value the change removed from the domain, when it removed exactly
	/// one.
	pub(crate) removed: Option<IntVal>,
}

impl From<ActivationActionS> for ActivationAction<engine::AdvRef, PropRef> {
	fn from(value: ActivationActionS) -> Self {
		if (value.0 & 0b1) == 1 {
			Self::Advise(engine::AdvRef::from_raw(value.0 >> 1))
		} else {
			Self::Enqueue(PropRef::from_raw(value.0 >> 1))
		}
	}
}

impl From<ActivationActionS> for ActivationAction<model::AdvRef, ConRef> {
	fn from(value: ActivationActionS) -> Self {
		if (value.0 & 0b1) == 1 {
			Self::Advise(model::AdvRef::from_raw(value.0 >> 1))
		} else {
			Self::Enqueue(ConRef::from_raw(value.0 >> 1))
		}
	}
}

impl From<ActivationAction<engine::AdvRef, PropRef>> for ActivationActionS {
	fn from(value: ActivationAction<engine::AdvRef, PropRef>) -> Self {
		Self(match value {
			ActivationAction::Advise(advisor) => (advisor.raw() << 1) | 0b1,
			ActivationAction::Enqueue(prop) => prop.raw() << 1,
		})
	}
}

impl From<ActivationAction<model::AdvRef, ConRef>> for ActivationActionS {
	fn from(value: ActivationAction<model::AdvRef, ConRef>) -> Self {
		Self(match value {
			ActivationAction::Advise(advisor) => (advisor.raw() << 1) | 0b1,
			ActivationAction::Enqueue(prop) => prop.raw() << 1,
		})
	}
}

impl ActivationList {
	/// Add a propagator to the list of propagators to be enqueued based on the
	/// given condition.
	pub(crate) fn add<A, P>(&mut self, action: ActivationAction<A, P>, condition: IntPropCond)
	where
		ActivationAction<A, P>: Into<ActivationActionS>,
	{
		assert!(
			self.activations.len() < u32::MAX as usize,
			"Unable to add more than u32::MAX propagators to the activation list of a single variable."
		);
		let mut action = action.into();
		let mut cond_swap = |idx: u32| {
			let idx = idx as usize;
			if idx < self.activations.len() {
				mem::swap(&mut action, &mut self.activations[idx]);
			}
		};
		match condition {
			IntPropCond::Fixed => {
				cond_swap(self.lower_bound_idx);
				if self.lower_bound_idx < self.upper_bound_idx {
					cond_swap(self.upper_bound_idx);
				}
				if self.upper_bound_idx < self.bounds_idx {
					cond_swap(self.bounds_idx);
				}
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.lower_bound_idx += 1;
				self.upper_bound_idx += 1;
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(action);
			}
			IntPropCond::LowerBound => {
				cond_swap(self.upper_bound_idx);
				if self.upper_bound_idx < self.bounds_idx {
					cond_swap(self.bounds_idx);
				}
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.upper_bound_idx += 1;
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(action);
			}
			IntPropCond::UpperBound => {
				cond_swap(self.bounds_idx);
				if self.bounds_idx < self.domain_idx {
					cond_swap(self.domain_idx);
				}
				self.bounds_idx += 1;
				self.domain_idx += 1;
				self.activations.push(action);
			}
			IntPropCond::Bounds => {
				cond_swap(self.domain_idx);
				self.domain_idx += 1;
				self.activations.push(action);
			}
			IntPropCond::Domain => self.activations.push(action),
		};
	}

	/// The propagation condition that the subscription at the given index was
	/// registered with.
	fn condition_at(&self, i: u32) -> IntPropCond {
		if i < self.lower_bound_idx {
			IntPropCond::Fixed
		} else if i < self.upper_bound_idx {
			IntPropCond::LowerBound
		} else if i < self.bounds_idx {
			IntPropCond::UpperBound
		} else if i < self.domain_idx {
			IntPropCond::Bounds
		} else {
			IntPropCond::Domain
		}
	}

	/// Extend the activation list with another activation list, consuming it.
	pub(crate) fn extend(&mut self, other: Self) {
		for (i, act) in other.activations.iter().enumerate() {
			let act: ActivationAction<engine::AdvRef, PropRef> = (*act).into();
			self.add(act, other.condition_at(i as u32));
		}
	}

	/// Iterate over the activation actions triggered by the given event and
	/// execute the provided function for each of them, together with the
	/// [`IntPropCond`] that the subscription was registered with.
	///
	/// The condition is what allows a caller to describe the change in the
	/// terms the subscriber asked about: a subscription on
	/// [`IntPropCond::LowerBound`] wants to hear about the minimum even when
	/// the change that triggered it fixed the variable outright.
	///
	/// This method does not enqueue or advise by itself; it simply delegates
	/// handling to the provided function `f`.
	pub(crate) fn for_each_activated_by<A, P, F>(&self, event: IntEvent, mut f: F)
	where
		ActivationAction<A, P>: From<ActivationActionS>,
		F: FnMut(ActivationAction<A, P>, IntPropCond),
	{
		let mut run = |from: u32, to: u32, condition: IntPropCond| {
			for &act in &self.activations[from as usize..to as usize] {
				f(act.into(), condition);
			}
		};
		let len = self.activations.len() as u32;
		if event == IntEvent::Fixed {
			run(0, self.lower_bound_idx, IntPropCond::Fixed);
		}
		if matches!(
			event,
			IntEvent::Fixed | IntEvent::Bounds | IntEvent::LowerBound
		) {
			run(
				self.lower_bound_idx,
				self.upper_bound_idx,
				IntPropCond::LowerBound,
			);
		}
		if matches!(
			event,
			IntEvent::Fixed | IntEvent::Bounds | IntEvent::UpperBound
		) {
			run(
				self.upper_bound_idx,
				self.bounds_idx,
				IntPropCond::UpperBound,
			);
		}
		if event != IntEvent::Domain {
			run(self.bounds_idx, self.domain_idx, IntPropCond::Bounds);
		}
		run(self.domain_idx, len, IntPropCond::Domain);
	}

	/// Return the number of subscriptions to the decision variable.
	pub(crate) fn subscription_count(&self) -> u32 {
		self.activations.len() as u32
	}
}

impl IntChange {
	/// Describe this change to a subscriber that registered with `condition`:
	/// the event to report, and the value that the change replaced.
	///
	/// A subscriber that asked about a single bound is always told about that
	/// bound, even when the change fixed the variable outright. Only a
	/// subscriber that asked to hear about fixing (or about both bounds at
	/// once) receives [`IntEvent::Fixed`] or [`IntEvent::Bounds`], and those
	/// cannot attribute the change to a single value.
	///
	/// `condition` is the condition the subscription is stored under, which is
	/// already expressed for the decision variable rather than the subscriber's
	/// view. Set `negated` for a subscriber whose view reverses the two bounds,
	/// so that the reported event is the one it expects. The value is left in
	/// the decision variable's value space for the subscriber to translate.
	pub(crate) fn advice(
		&self,
		condition: IntPropCond,
		negated: bool,
	) -> (IntEvent, Option<IntVal>) {
		let (event, previous) = match condition {
			IntPropCond::Fixed => (IntEvent::Fixed, None),
			IntPropCond::LowerBound => (IntEvent::LowerBound, Some(self.previous.0)),
			IntPropCond::UpperBound => (IntEvent::UpperBound, Some(self.previous.1)),
			IntPropCond::Bounds | IntPropCond::Domain => match self.event {
				IntEvent::LowerBound => (IntEvent::LowerBound, Some(self.previous.0)),
				IntEvent::UpperBound => (IntEvent::UpperBound, Some(self.previous.1)),
				IntEvent::Domain => (IntEvent::Domain, self.removed),
				IntEvent::Fixed | IntEvent::Bounds => (self.event, None),
			},
		};
		let event = match event {
			IntEvent::LowerBound if negated => IntEvent::UpperBound,
			IntEvent::UpperBound if negated => IntEvent::LowerBound,
			e => e,
		};
		(event, previous)
	}

	/// A change that cannot be attributed to a single value, such as one that
	/// coalesces several separate changes.
	pub(crate) fn unattributed(event: IntEvent, previous: (IntVal, IntVal)) -> Self {
		Self {
			event,
			previous,
			removed: None,
		}
	}
}

impl Add<IntEvent> for IntEvent {
	type Output = IntEvent;

	fn add(self, rhs: IntEvent) -> Self::Output {
		use IntEvent::*;
		match (self, rhs) {
			(Fixed, _) | (_, Fixed) => Fixed,
			(Bounds, _) | (_, Bounds) => Bounds,
			(LowerBound, UpperBound) | (UpperBound, LowerBound) => Bounds,
			(LowerBound, _) | (_, LowerBound) => LowerBound,
			(UpperBound, _) | (_, UpperBound) => UpperBound,
			(Domain, Domain) => Domain,
		}
	}
}

impl AddAssign<IntEvent> for IntEvent {
	fn add_assign(&mut self, rhs: IntEvent) {
		*self = *self + rhs;
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use rustc_hash::FxHashSet;

	use crate::{
		actions::{IntEvent, IntPropCond},
		solver::{
			activation_list::{ActivationAction, ActivationList},
			engine::PropRef,
		},
	};

	#[test]
	fn test_activation_list() {
		let props = [
			(PropRef::new(0), IntPropCond::Fixed),
			(PropRef::new(1), IntPropCond::LowerBound),
			(PropRef::new(2), IntPropCond::UpperBound),
			(PropRef::new(3), IntPropCond::Bounds),
			(PropRef::new(4), IntPropCond::Domain),
		];

		for list in props.iter().permutations(5) {
			let mut activation_list = ActivationList::default();
			for (prop, cond) in list.iter() {
				activation_list.add(ActivationAction::Enqueue(*prop), *cond);
			}
			let mut fixed = FxHashSet::default();
			activation_list.for_each_activated_by(
				IntEvent::Fixed,
				|a: ActivationAction<_, _>, _| {
					fixed.insert(a);
				},
			);
			assert_eq!(
				fixed,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::new(0)),
					ActivationAction::Enqueue(PropRef::new(1)),
					ActivationAction::Enqueue(PropRef::new(2)),
					ActivationAction::Enqueue(PropRef::new(3)),
					ActivationAction::Enqueue(PropRef::new(4))
				])
			);
			let mut bounds = FxHashSet::default();
			activation_list.for_each_activated_by(
				IntEvent::Bounds,
				|a: ActivationAction<_, _>, _| {
					bounds.insert(a);
				},
			);
			assert_eq!(
				bounds,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::new(1)),
					ActivationAction::Enqueue(PropRef::new(2)),
					ActivationAction::Enqueue(PropRef::new(3)),
					ActivationAction::Enqueue(PropRef::new(4))
				])
			);
			let mut lower_bound = FxHashSet::default();
			activation_list.for_each_activated_by(
				IntEvent::LowerBound,
				|a: ActivationAction<_, _>, _| {
					lower_bound.insert(a);
				},
			);
			assert_eq!(
				lower_bound,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::new(1)),
					ActivationAction::Enqueue(PropRef::new(3)),
					ActivationAction::Enqueue(PropRef::new(4))
				])
			);
			let mut upper_bound = FxHashSet::default();
			activation_list.for_each_activated_by(
				IntEvent::UpperBound,
				|a: ActivationAction<_, _>, _| {
					upper_bound.insert(a);
				},
			);
			assert_eq!(
				upper_bound,
				FxHashSet::from_iter([
					ActivationAction::Enqueue(PropRef::new(2)),
					ActivationAction::Enqueue(PropRef::new(3)),
					ActivationAction::Enqueue(PropRef::new(4))
				])
			);
			let mut domain = FxHashSet::default();
			activation_list.for_each_activated_by(
				IntEvent::Domain,
				|a: ActivationAction<_, _>, _| {
					domain.insert(a);
				},
			);
			assert_eq!(
				domain,
				FxHashSet::from_iter([ActivationAction::Enqueue(PropRef::new(4))])
			);
		}
	}
}
