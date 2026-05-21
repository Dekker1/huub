//! This module defines [`NegatedView`], a lightweight view wrapper that
//! represents the negation of an underlying integer view.
//!
//! Conceptually, if the underlying view behaves as an integer decision
//! variable `x`, then `NegatedView<T>` behaves as `-x`.

use std::{ops::Neg, slice};

use crate::{
	IntSet, IntVal,
	actions::{
		IntDecisionActions, IntExplanationActions, IntInitActions, IntInspectionActions,
		IntPropCond, IntPropagationActions, IntSimplificationActions, PropagationActions,
		ReasoningContext,
	},
	constraints::ReasonBuilder,
	solver::{
		IntLitMeaning,
		solution::{Solution, Valuation},
	},
};

/// A view wrapper that represents the negation of an underlying integer view.
///
/// This is `#[repr(transparent)]` over `T`, which enables safely
/// reinterpreting `&T` as `&NegatedView<T>` (and similarly for slices) via the
/// provided helper functions.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NegatedView<T>(T);

impl<T> NegatedView<T> {
	/// Reinterpret a mutable reference as a mutable reference to
	/// [`NegatedView`].
	///
	/// This is safe because [`NegatedView`] is `#[repr(transparent)]` over `T`.
	///
	/// Callers must uphold Rust's usual aliasing rules for `&mut`.
	pub fn from_mut(x: &mut T) -> &mut Self {
		let ptr: *mut T = x;
		// SAFETY: `Self` is `#[repr(transparent)]` over `T`.
		unsafe { &mut *ptr.cast::<Self>() }
	}

	/// Reinterpret a shared reference as a shared reference to [`NegatedView`].
	///
	/// This is safe because [`NegatedView`] is `#[repr(transparent)]` over `T`.
	pub fn from_ref(x: &T) -> &Self {
		let ptr: *const T = x;
		// SAFETY: `Self` is `#[repr(transparent)]` over `T`.
		unsafe { &*ptr.cast::<Self>() }
	}

	/// Returns the underlying view.
	pub fn into_inner(self) -> T {
		self.0
	}

	/// Returns a new set that contains the element-wise negation of `values`.
	///
	/// This maps each range `[a..=b]` to `[-b..=-a]`, and reverses the order of
	/// ranges so that the resulting set remains sorted.
	fn negate_intset(values: &IntSet) -> IntSet {
		IntSet::from_sorted_ranges(values.iter().rev().map(|r| (-*r.end())..=(-*r.start())))
	}

	/// Reinterpret a slice of `T` as a slice of [`NegatedView<T>`].
	///
	/// This is safe because [`NegatedView`] is `#[repr(transparent)]` over `T`.
	pub fn slice(xs: &[T]) -> &[Self] {
		// SAFETY: `Self` is `#[repr(transparent)]` over `T`.
		unsafe { slice::from_raw_parts(xs.as_ptr().cast::<Self>(), xs.len()) }
	}

	/// Reinterpret a mutable slice of `T` as a mutable slice of
	/// [`NegatedView<T>`].
	///
	/// This is safe because [`NegatedView`] is `#[repr(transparent)]` over `T`.
	///
	/// Callers must uphold Rust's usual aliasing rules for `&mut`.
	pub fn slice_mut(xs: &mut [T]) -> &mut [Self] {
		// SAFETY: `Self` is `#[repr(transparent)]` over `T`.
		unsafe { slice::from_raw_parts_mut(xs.as_mut_ptr().cast::<Self>(), xs.len()) }
	}

	/// Transforms an [`IntPropCond`] from the condition on `-x` to the
	/// equivalent condition on `x`.
	///
	/// In particular, changes to the lower bound of `-x` correspond to changes
	/// to the upper bound of `x`, and vice versa.
	fn transform_cond(cond: IntPropCond) -> IntPropCond {
		match cond {
			IntPropCond::LowerBound => IntPropCond::UpperBound,
			IntPropCond::UpperBound => IntPropCond::LowerBound,
			cond => cond,
		}
	}

	/// Transforms an [`IntLitMeaning`] from the meaning on `-x` to the meaning
	/// on `x`.
	///
	/// This matches the transformation that would be applied by a `LinearView`
	/// with `scale = -1` and `offset = 0`.
	fn transform_meaning(meaning: IntLitMeaning) -> IntLitMeaning {
		match meaning {
			IntLitMeaning::Eq(v) => IntLitMeaning::Eq(-v),
			IntLitMeaning::NotEq(v) => IntLitMeaning::NotEq(-v),
			IntLitMeaning::GreaterEq(v) => IntLitMeaning::Less(-v + 1),
			IntLitMeaning::Less(v) => IntLitMeaning::GreaterEq(-v + 1),
		}
	}
}

impl<T> From<T> for NegatedView<T> {
	fn from(value: T) -> Self {
		Self(value)
	}
}

impl<Ctx, T> IntDecisionActions<Ctx> for NegatedView<T>
where
	Ctx: ReasoningContext + ?Sized,
	T: IntDecisionActions<Ctx>,
{
	fn lit(&self, ctx: &mut Ctx, meaning: IntLitMeaning) -> Ctx::Atom {
		self.0.lit(ctx, Self::transform_meaning(meaning))
	}
}

impl<Ctx, T> IntExplanationActions<Ctx> for NegatedView<T>
where
	Ctx: ReasoningContext + ?Sized,
	T: IntExplanationActions<Ctx>,
{
	fn lit_relaxed(&self, ctx: &Ctx, meaning: IntLitMeaning) -> (Ctx::Atom, IntLitMeaning) {
		let (atom, meaning) = self.0.lit_relaxed(ctx, Self::transform_meaning(meaning));
		(atom, Self::transform_meaning(meaning))
	}
}

impl<Ctx, T> IntInitActions<Ctx> for NegatedView<T>
where
	Ctx: ReasoningContext + ?Sized,
	T: IntInitActions<Ctx>,
{
	fn advise_when(&self, ctx: &mut Ctx, condition: IntPropCond, data: u64) {
		self.0
			.advise_when(ctx, Self::transform_cond(condition), data);
	}

	fn enqueue_when(&self, ctx: &mut Ctx, condition: IntPropCond) {
		self.0.enqueue_when(ctx, Self::transform_cond(condition));
	}
}

impl<Ctx, T> IntInspectionActions<Ctx> for NegatedView<T>
where
	Ctx: ReasoningContext + ?Sized,
	T: IntInspectionActions<Ctx>,
{
	fn bounds(&self, ctx: &Ctx) -> (IntVal, IntVal) {
		let (lb, ub) = self.0.bounds(ctx);
		(-ub, -lb)
	}

	fn domain(&self, ctx: &Ctx) -> IntSet {
		Self::negate_intset(&self.0.domain(ctx))
	}

	fn in_domain(&self, ctx: &Ctx, val: IntVal) -> bool {
		self.0.in_domain(ctx, -val)
	}

	fn lit_meaning(&self, ctx: &Ctx, lit: Ctx::Atom) -> Option<IntLitMeaning> {
		Some(Self::transform_meaning(self.0.lit_meaning(ctx, lit)?))
	}

	fn max(&self, ctx: &Ctx) -> IntVal {
		-self.0.min(ctx)
	}

	fn max_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		self.0.min_lit(ctx)
	}

	fn min(&self, ctx: &Ctx) -> IntVal {
		-self.0.max(ctx)
	}

	fn min_lit(&self, ctx: &Ctx) -> Ctx::Atom {
		self.0.max_lit(ctx)
	}

	fn try_lit(&self, ctx: &Ctx, meaning: IntLitMeaning) -> Option<Ctx::Atom> {
		self.0.try_lit(ctx, Self::transform_meaning(meaning))
	}

	fn val(&self, ctx: &Ctx) -> Option<IntVal> {
		self.0.val(ctx).map(|v| -v)
	}
}

impl<Ctx, T> IntPropagationActions<Ctx> for NegatedView<T>
where
	Ctx: PropagationActions + ?Sized,
	T: IntPropagationActions<Ctx>,
{
	fn fix(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.0.fix(ctx, -val, reason)
	}

	fn remove_val(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.0.remove_val(ctx, -val, reason)
	}

	fn tighten_max(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.0.tighten_min(ctx, -val, reason)
	}

	fn tighten_min(
		&self,
		ctx: &mut Ctx,
		val: IntVal,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.0.tighten_max(ctx, -val, reason)
	}
}

impl<Ctx, T> IntSimplificationActions<Ctx> for NegatedView<T>
where
	Ctx: PropagationActions + ?Sized,
	T: IntSimplificationActions<Ctx>,
{
	fn exclude(
		&self,
		ctx: &mut Ctx,
		values: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.0.exclude(ctx, &Self::negate_intset(values), reason)
	}

	fn restrict_domain(
		&self,
		ctx: &mut Ctx,
		domain: &IntSet,
		reason: impl ReasonBuilder<Ctx>,
	) -> Result<(), Ctx::Conflict> {
		self.0
			.restrict_domain(ctx, &Self::negate_intset(domain), reason)
	}

	fn unify(&self, ctx: &mut Ctx, other: impl Into<Self>) -> Result<(), Ctx::Conflict> {
		self.0.unify(ctx, other.into().0)
	}
}

impl<T> Neg for NegatedView<T> {
	type Output = T;

	fn neg(self) -> Self::Output {
		self.into_inner()
	}
}

impl<T> Valuation for NegatedView<T>
where
	T: Valuation<Val = IntVal>,
{
	type Val = IntVal;

	fn val(&self, sol: Solution<'_>) -> IntVal {
		-self.0.val(sol)
	}
}

#[cfg(test)]
mod tests {
	use std::mem::{align_of, size_of};

	use crate::{IntSet, IntVal, actions::IntInspectionActions, model::Model, views::NegatedView};

	#[test]
	fn bounds_and_domain_are_negated() {
		let mut model = Model::default();
		let x = model.new_int_decision(IntSet::from_iter([1..=1, 3..=4, 10..=12]));
		let nx = NegatedView::from(x);

		assert_eq!(x.bounds(&model), (1, 12));
		assert_eq!(nx.bounds(&model), (-12, -1));

		let expected = IntSet::from_iter([-12..=-10, -4..=-3, -1..=-1]);
		assert_eq!(nx.domain(&model), expected);
	}

	#[test]
	fn in_domain_and_val_are_negated() {
		let mut model = Model::default();
		let x = model.new_int_decision(5..=5);
		let nx = NegatedView::from(x);

		assert!(nx.in_domain(&model, -5));
		assert!(!nx.in_domain(&model, 5));
		assert_eq!(nx.val(&model), Some(-5));
	}

	#[test]
	fn layout_and_slice_casts_are_sound() {
		let mut model = Model::default();
		let x = model.new_int_decision(0..=1);

		assert_eq!(
			size_of::<crate::model::View<IntVal>>(),
			size_of::<NegatedView<crate::model::View<IntVal>>>()
		);
		assert_eq!(
			align_of::<crate::model::View<IntVal>>(),
			align_of::<NegatedView<crate::model::View<IntVal>>>()
		);

		let xs = [x, x];
		let ys = NegatedView::slice(&xs);
		assert_eq!(xs.as_ptr().cast::<u8>(), ys.as_ptr().cast::<u8>());
		assert_eq!(xs.len(), ys.len());
	}
}
