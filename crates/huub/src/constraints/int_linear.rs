//! Structures and algorithms  for the integer linear constraint, including
//! `int_lin_eq`, `int_lin_le`, `int_lin_ne` and their reification. These
//! constraint enforce a condition on the sum of (linear transformations of)
//! integer decision variables.

use std::{any::TypeId, num::NonZero};

use itertools::{Either, Itertools};
use pindakaas::{
	Lit as RawLit, Unsatisfiable,
	bool_linear::{BoolLinAggregator, BoolLinExp, BoolLinVariant, BoolLinear},
};

use crate::{
	IntVal,
	actions::{
		BoolAnalyzeActions, BoolInitActions, BoolInspectionActions, BoolPropagationActions,
		BoolSimplificationActions, DeferReasonActions, InitActions, IntAnalyzeActions,
		IntDecisionActions, IntEvent, IntInitActions, IntInspectionActions, IntPropCond,
		IntPropagationActions, IntSimplificationActions, PostingActions, PropagationActions,
		PropagationContext, ReasonActions, ReasoningContext, ReasoningEngine,
		SimplificationActions, Trailed, TrailingActions,
	},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, IntModelActions, IntSolverActions,
		NO_REASON, Propagator, SimplificationStatus, reason_ty,
	},
	helpers::{
		overflow::{OverflowImpossible, OverflowMode, OverflowPossible},
		true_type::True,
	},
	lower::{LoweringContext, LoweringError},
	model::{self, expressions::bool_formula::BoolFormula},
	solver::{
		self, BoolView, Decision, IntLitMeaning, Polarity, queue::PriorityLevel,
		view::integer::IntView,
	},
	views::LinearBoolView,
};

/// A type with twice the bit width of [`IntVal`], allowing for large
/// intermediate value computation.
type DoubleIntVal = i128;

/// Representation of an integer equality constraint that cannot be unified.
///
/// This constraint enforces that two integer decisions take the same value.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct IntEq {
	/// The two integer decisions that must be equal.
	pub(crate) vars: [model::View<IntVal>; 2],
}

/// Representation of an integer linear constraint within a model.
///
/// This constraint enforces that a sum of (linear transformations of) integer
/// decision variables is less than, equal, or not equal to a constant value, or
/// the implication or reification or whether this is so.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntLinear<OF: OverflowMode> {
	/// The integer linear terms that are being summed.
	pub(crate) terms: Vec<model::View<IntVal>>,
	/// The operator that is used to compare the sum to the right-hand side.
	pub(crate) comparator: LinComparator,
	/// The constant right-hand side value.
	pub(crate) rhs: OF::Accumulator,
	/// Boolean decision variable that (half-)reifies the constraint, if any.
	pub(crate) reif: Option<Reification>,
	/// Strategy used to decide when the bounds consistent propagators for this
	/// constraint are scheduled.
	pub(crate) scheduling: LinearScheduling,
}

/// Type alias for the non-reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqBounds<OV, IV> = IntLinearLessEqBoundsImpl<OV, IV, True>;

/// Bounds consistent propagator for the `int_lin_le` or `int_lin_le_imp`
/// constraint.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntLinearLessEqBoundsImpl<OV: OverflowMode, IV, BV> {
	/// Variables that are being summed
	terms: Vec<IV>,
	/// Maximum value of the sum can take
	max: OV::Accumulator,
	/// Reified variable, if any
	reification: BV,
}

/// Type alias for the reified version of the [`IntLinearLessEqBoundsImpl`]
/// propagator.
pub type IntLinearLessEqImpBounds<OV, IV, BV> = IntLinearLessEqBoundsImpl<OV, IV, BV>;

/// Type alias for the half-reified version of the [`IntLinearLessEqSlackImpl`]
/// propagator.
pub type IntLinearLessEqImpSlack<OV, IV, BV, const TRACK_MAX: bool> =
	IntLinearLessEqSlackImpl<OV, IV, BV, TRACK_MAX>;

/// Type alias for the non-reified version of the [`IntLinearLessEqSlackImpl`]
/// propagator.
pub type IntLinearLessEqSlack<OV, IV, const TRACK_MAX: bool> =
	IntLinearLessEqSlackImpl<OV, IV, True, TRACK_MAX>;

/// Bounds consistent propagator for the `int_lin_le` or `int_lin_le_imp`
/// constraint that maintains the slack of the constraint incrementally, so
/// that it is only scheduled when it can actually prune something.
///
/// The slack `max - Σ min(term)` is the amount by which any single term may
/// still grow, so propagation is possible exactly when some term can grow
/// further than the slack allows, and the constraint is violated when the
/// slack is negative. The advisor keeps the slack up to date from the value
/// each bound change replaced, and compares it against `max_span`, which
/// bounds how far any term can still grow.
///
/// The slack is only ever an over-estimate: an advisor is not told about a
/// change until the SAT solver reports the corresponding literal back, so a
/// change that a propagator has already enacted may not be accounted for yet.
/// That is safe because every enacted change is eventually reported, and the
/// advisor decides again on each one, so the last advice for a batch of
/// changes is taken with all of them applied.
///
/// See Harvey and Schimpf, "Bounds consistency techniques for long linear
/// constraints" (2002) for the slack formulation, and Schulte and Stuckey,
/// "Efficient constraint propagation engines" (TOPLAS 2008) for the advisor
/// design.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntLinearLessEqSlackImpl<OV: OverflowMode, IV, BV, const TRACK_MAX: bool> {
	/// The propagator whose scheduling is being made incremental.
	inner: IntLinearLessEqBoundsImpl<OV, IV, BV>,
	/// The slack of the constraint, `max - Σ min(term)`, saturated into the
	/// [`IntVal`] range.
	slack: Trailed<IntVal>,
	/// An upper bound on the largest `max(term) - min(term)` over the terms,
	/// refreshed whenever the propagator runs. [`IntVal::MAX`] marks a span
	/// that did not fit, and is therefore unknown.
	max_span: Trailed<IntVal>,
	/// `max - Σ max(term)`, saturated into the [`IntVal`] range. The constraint
	/// is entailed while this is non-negative. Only maintained when
	/// `TRACK_MAX`.
	max_slack: Trailed<IntVal>,
}

/// Type alias for the reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqImpValue<OF, IV, BV> = IntLinearNotEqValueImpl<OF, IV, BV>;

/// Type alias for the non-reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub type IntLinearNotEqValue<OF, IV> = IntLinearNotEqValueImpl<OF, IV, True>;

/// Value consistent propagator for the `int_lin_ne` or `int_lin_ne_imp`
/// constraint.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IntLinearNotEqValueImpl<OF: OverflowMode, IV, BV> {
	/// Decision variables in the summation
	terms: Vec<IV>,
	/// Number of decision variables that have been not yet been fixed to a
	/// single value
	num_free: Trailed<usize>,
	/// The value the summation should not equal
	violation: OF::Accumulator,
	/// Reified variable, if any
	reification: BV,
}

/// Possible operators that can be used for in a linear constraint.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum LinComparator {
	/// Sum is equal to the constant
	Equal,
	/// Sum is less than or equal to the constant
	LessEq,
	/// Sum is not equal to the constant
	NotEqual,
}

/// Strategy used to decide when the bounds consistent propagator for a linear
/// constraint is scheduled during the search.
///
/// The strategies differ only in how often the propagator runs, never in what
/// it infers when it does.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum LinearScheduling {
	/// Schedule the propagator whenever the minimum of any of its terms
	/// changes.
	#[default]
	Eager,
	/// Track the slack of the constraint, and schedule the propagator only when
	/// the slack is small enough for one of its terms to be pruned.
	Slack,
	/// As [`LinearScheduling::Slack`], but additionally track the maxima of the
	/// terms, so that the propagator is no longer scheduled once the constraint
	/// is entailed. This filters more, at the cost of watching both bounds of
	/// every term instead of one.
	SlackEntailment,
}

/// Reification possibilities for a linear constraint.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Reification {
	/// The constraint is half-reified by the given [`BoolDecision`].
	ImpliedBy(model::View<bool>),
	/// The constraint is reified by the given [`BoolDecision`].
	ReifiedBy(model::View<bool>),
}

/// Post the bounds consistent propagator for `terms <= rhs` selected by
/// `scheduling`, half-reified by `r` when one is given.
fn post_less_eq(
	slv: &mut LoweringContext<'_>,
	terms: Vec<solver::View<IntVal>>,
	rhs: impl Into<DoubleIntVal>,
	r: Option<solver::View<bool>>,
	scheduling: LinearScheduling,
) {
	let rhs = rhs.into();
	match (scheduling, r) {
		(LinearScheduling::Eager, None) => IntLinearLessEqBounds::post(slv, terms, rhs),
		(LinearScheduling::Slack, None) => {
			IntLinearLessEqSlack::<_, _, false>::post(slv, terms, rhs);
		}
		(LinearScheduling::SlackEntailment, None) => {
			IntLinearLessEqSlack::<_, _, true>::post(slv, terms, rhs);
		}
		(LinearScheduling::Eager, Some(r)) => {
			IntLinearLessEqImpBounds::<_, _, Decision<bool>>::post(slv, terms, rhs, r);
		}
		(LinearScheduling::Slack, Some(r)) => {
			IntLinearLessEqImpSlack::<_, _, Decision<bool>, false>::post(slv, terms, rhs, r);
		}
		(LinearScheduling::SlackEntailment, Some(r)) => {
			IntLinearLessEqImpSlack::<_, _, Decision<bool>, true>::post(slv, terms, rhs, r);
		}
	}
}

/// Clamp an accumulated value into the [`IntVal`] range, so that it can be
/// stored in a [`Trailed`] value.
///
/// Clamping is only correct because both quantities that are stored this way
/// are slacks: clamping at [`IntVal::MAX`] under-estimates the slack, which
/// only leads to a propagator being scheduled when it has nothing to do, and
/// clamping at [`IntVal::MIN`] leaves a negative slack negative.
fn saturate(val: DoubleIntVal) -> IntVal {
	val.clamp(IntVal::MIN.into(), IntVal::MAX.into()) as IntVal
}

impl<E> Constraint<E> for IntEq
where
	E: ReasoningEngine,
	for<'a> E::PropagationContext<'a>: SimplificationActions<Target = E>,
	model::View<IntVal>: IntModelActions<E>,
	model::View<bool>: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;
		// Note that one variable might be fixed and not the other one. Gaps in domains
		// or linear view might require multiple rounds of propagation to reach a
		// fixpoint.
		if self.vars.iter().all(|v| v.val(ctx).is_some()) {
			Ok(SimplificationStatus::Subsumed)
		} else {
			Ok(SimplificationStatus::NoFixpoint)
		}
	}

	fn to_solver(&self, actions: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let lin = IntLinear::<OverflowPossible> {
			terms: vec![self.vars[0], -self.vars[1]],
			comparator: LinComparator::Equal,
			rhs: 0,
			reif: None,
			scheduling: LinearScheduling::default(),
		};
		<_ as Constraint<E>>::to_solver(&lin, actions)
	}
}

impl<E> Propagator<E> for IntEq
where
	E: ReasoningEngine,
	model::View<IntVal>: IntSolverActions<E>,
{
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Highest);

		for iv in self.vars {
			iv.enqueue_when(ctx, IntPropCond::Bounds);
		}
	}

	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		// Channel bounds of self.vars[0] to self.vars[1]
		self.vars[0].tighten_min(ctx, self.vars[1].min(ctx), |ctx, reason| {
			reason.push(self.vars[1].min_lit(ctx));
		})?;
		self.vars[0].tighten_max(ctx, self.vars[1].max(ctx), |ctx, reason| {
			reason.push(self.vars[1].max_lit(ctx));
		})?;

		// Channel bounds of self.vars[1] to self.vars[0]
		self.vars[1].tighten_min(ctx, self.vars[0].min(ctx), |ctx, reason| {
			reason.push(self.vars[0].min_lit(ctx));
		})?;
		self.vars[1].tighten_max(ctx, self.vars[0].max(ctx), |ctx, reason| {
			reason.push(self.vars[0].max_lit(ctx));
		})?;
		Ok(())
	}
}

impl<OF: OverflowMode> IntLinear<OF> {
	/// Internal method to negate the linear constraint.
	fn negate<Ctx>(self, ctx: &mut Ctx) -> Result<Self, Ctx::Conflict>
	where
		Ctx: PropagationContext + ?Sized,
		model::View<IntVal>: IntPropagationActions<Ctx>,
	{
		Ok(match self.comparator {
			LinComparator::Equal => Self {
				comparator: LinComparator::NotEqual,
				..self
			},
			LinComparator::LessEq => Self {
				terms: self
					.terms
					.into_iter()
					.map(|v| v.bounding_neg(ctx))
					.try_collect()?,
				rhs: -self.rhs - 1.into(),
				..self
			},
			LinComparator::NotEqual => Self {
				comparator: LinComparator::Equal,
				..self
			},
		})
	}

	/// Try to convert the integer linear constraint into a [`BoolLinear`]
	/// constraint, where the given terms are the [`IntView`] representations of
	/// the [`IntDecision`] terms in `self`.
	///
	/// This only succeeds if the linear constraint is not implied, all terms
	/// are [`BoolLinView`]s, and the comparator is not
	/// [`LinOperator::NotEqual`].
	fn try_bool_lin(&self, terms: &[solver::View<IntVal>]) -> Option<BoolLinear> {
		if self.reif.is_some() || self.comparator == LinComparator::NotEqual {
			return None;
		}

		let mut offset = OF::Accumulator::from(0);
		let terms: Vec<(RawLit, IntVal)> = terms
			.iter()
			.map(|&v| {
				if let IntView::Bool(lin) = v.0 {
					offset += lin.offset.into();
					Ok((lin.var.0, lin.scale.into()))
				} else {
					Err(())
				}
			})
			.collect::<Result<_, ()>>()
			.ok()?;
		let rhs = (self.rhs - offset).try_into().ok()?;

		let bool_lin = BoolLinExp::from_terms(&terms);
		let bool_lin = BoolLinear::new(
			bool_lin,
			match self.comparator {
				LinComparator::Equal => pindakaas::bool_linear::Comparator::Equal,
				LinComparator::LessEq => pindakaas::bool_linear::Comparator::LessEq,
				LinComparator::NotEqual => unreachable!(),
			},
			rhs,
		);
		Some(bool_lin)
	}
}

impl IntLinear<OverflowPossible> {
	/// Returns whether the given terms that are summed in integer linear
	/// expressions can overflow.
	///
	/// Note that the order of the terms matters. If the terms are reordered,
	/// then the result of this method may change.
	pub(crate) fn can_overflow<Ctx, IV>(ctx: &Ctx, terms: &[IV]) -> bool
	where
		Ctx: ReasoningContext + ?Sized,
		IV: IntInspectionActions<Ctx>,
	{
		let mut acc_min: IntVal = 0;
		let mut acc_max: IntVal = 0;
		for iv in terms {
			let (lb, ub) = iv.bounds(ctx);
			if let Some(min) = acc_min.checked_sub(lb) {
				acc_min = min;
			} else {
				return true;
			}
			if let Some(max) = acc_max.checked_add(ub) {
				acc_max = max;
			} else {
				return true;
			}
		}
		false
	}
}

impl<E, OF> Constraint<E> for IntLinear<OF>
where
	E: ReasoningEngine,
	for<'a> E::PropagationContext<'a>: SimplificationActions<Target = E>,
	model::View<IntVal>: IntModelActions<E>,
	model::View<bool>: BoolModelActions<E>,
	OF: OverflowMode,
{
	fn analyze(&self, ctx: &mut E::InitializationContext<'_>) {
		match self.reif {
			// A half-reified constraint is vacuously satisfied when the
			// implication literal is false.
			Some(Reification::ImpliedBy(r)) => r.polarity(ctx, Polarity::Negative),
			// For an `int_lin_le` constraint (sum <= rhs), making each term
			// smaller makes the constraint easier to satisfy.
			None if self.comparator == LinComparator::LessEq => {
				for t in &self.terms {
					t.polarity(ctx, Polarity::Negative);
				}
			}
			_ => {}
		}
	}

	fn simplify(
		&mut self,
		ctx: &mut E::PropagationContext<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		// If the reification of the constraint is known, simplify to non-reified
		// version
		if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
			match r.val(ctx) {
				Some(true) => {
					let mut lin = self.clone();
					lin.reif = None;
					ctx.post_constraint(lin);
					return Ok(SimplificationStatus::Subsumed);
				}
				Some(false) => {
					if matches!(self.reif.unwrap(), Reification::ReifiedBy(_)) {
						let mut lin = self.clone().negate(ctx)?;
						lin.reif = None;
						ctx.post_constraint(lin);
					}
					return Ok(SimplificationStatus::Subsumed);
				}
				None => {}
			}
		}

		// Filter known values from the terms
		let (vals, terms): (Vec<_>, _) =
			self.terms.iter().partition_map(|&var| match var.val(ctx) {
				Some(val) => Either::Left(val),
				None => Either::Right(var),
			});
		self.terms = terms;
		self.rhs -= vals.into_iter().map(OF::Accumulator::from).sum();

		// Perform single-term domain changes and any possible unification
		match *self.terms.as_slice() {
			[var] if self.reif.is_none() => {
				match (self.comparator, self.rhs.try_into()) {
					(LinComparator::Equal, Ok(rhs)) => var.fix(ctx, rhs, NO_REASON)?,
					(LinComparator::Equal, Err(_)) => {
						return Err(ctx.declare_conflict(NO_REASON));
					}
					(LinComparator::LessEq, Ok(rhs)) => {
						var.tighten_max(ctx, rhs, NO_REASON)?;
					}
					(LinComparator::LessEq, Err(_)) if self.rhs < IntVal::MIN.into() => {
						return Err(ctx.declare_conflict(NO_REASON));
					}
					(LinComparator::LessEq, Err(_)) => {
						debug_assert!(self.rhs > IntVal::MAX.into());
					}
					(LinComparator::NotEqual, Ok(rhs)) => {
						var.remove_val(ctx, rhs, NO_REASON)?;
					}
					(LinComparator::NotEqual, Err(_)) => {}
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			[var] => {
				let lit = match (self.comparator, self.rhs.try_into()) {
					(LinComparator::Equal, Ok(rhs)) => var.eq(rhs),
					(LinComparator::Equal, Err(_)) => false.into(),
					(LinComparator::LessEq, Ok(rhs)) => var.leq(rhs),
					(LinComparator::LessEq, Err(_)) if self.rhs < IntVal::MIN.into() => {
						false.into()
					}
					(LinComparator::LessEq, Err(_)) => {
						debug_assert!(self.rhs > IntVal::MAX.into());
						true.into()
					}
					(LinComparator::NotEqual, Ok(rhs)) => var.ne(rhs),
					(LinComparator::NotEqual, Err(_)) => false.into(),
				};
				match self.reif.unwrap() {
					Reification::ImpliedBy(r) => ctx.post_constraint(BoolFormula::Implies(
						Box::new(BoolFormula::Atom(r)),
						Box::new(BoolFormula::Atom(lit)),
					)),
					Reification::ReifiedBy(r) => r.unify(ctx, lit)?,
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			[a, b] if self.comparator == LinComparator::Equal && self.reif.is_none() => {
				match self.rhs.try_into() {
					Ok(rhs) => {
						let b = b.bounding_neg(ctx)?.bounding_add(ctx, rhs)?;
						a.unify(ctx, b)?;
					}
					Err(_) => {
						// TODO: might be incorrect
						return Err(ctx.declare_conflict(NO_REASON));
					}
				}
				return Ok(SimplificationStatus::Subsumed);
			}
			_ => {}
		}

		// Collect variable bounds and create their sums
		let lb = self.terms.iter().map(|v| v.min(ctx)).collect_vec();
		let ub = self.terms.iter().map(|v| v.max(ctx)).collect_vec();

		let lb_sum: OF::Accumulator = lb.iter().copied().map(OF::Accumulator::from).sum();
		let ub_sum: OF::Accumulator = ub.iter().copied().map(OF::Accumulator::from).sum();

		// Check if the constraint is already known to be true or false
		let known_result = match self.comparator {
			LinComparator::Equal if lb_sum > self.rhs || ub_sum < self.rhs => Some(false),
			LinComparator::Equal if lb_sum == ub_sum => {
				debug_assert_eq!(lb_sum, self.rhs);
				Some(true)
			}
			LinComparator::LessEq if ub_sum <= self.rhs => Some(true),
			LinComparator::LessEq if lb_sum > self.rhs => Some(false),
			LinComparator::NotEqual if lb_sum > self.rhs || ub_sum < self.rhs => Some(true),
			LinComparator::NotEqual if lb_sum == ub_sum => {
				debug_assert_eq!(lb_sum, self.rhs);
				Some(false)
			}
			_ => None,
		};
		let fail_reason = reason_ty::<E::PropagationContext<'_>, _>(|ctx, reason| {
			reason.extend(self.terms.iter().map(|v| match self.comparator {
				LinComparator::Equal if lb_sum > self.rhs => v.min_lit(ctx),
				LinComparator::Equal if ub_sum < self.rhs => v.max_lit(ctx),
				LinComparator::LessEq => v.min_lit(ctx),
				LinComparator::NotEqual => v.val_lit(ctx).unwrap(),
				_ => unreachable!(),
			}));
		});

		if let Some(satisfied) = known_result {
			return match self.reif {
				Some(Reification::ImpliedBy(r)) => {
					if !satisfied {
						r.fix(ctx, false, fail_reason)?;
					}
					Ok(SimplificationStatus::Subsumed)
				}
				Some(Reification::ReifiedBy(r)) if satisfied => {
					r.require(ctx, |ctx, reason| {
						reason.extend(self.terms.iter().flat_map(|v| match self.comparator {
							LinComparator::NotEqual if lb_sum > self.rhs => {
								vec![v.min_lit(ctx)]
							}
							LinComparator::NotEqual if ub_sum < self.rhs => {
								vec![v.max_lit(ctx)]
							}
							LinComparator::LessEq => vec![v.max_lit(ctx)],
							LinComparator::NotEqual => {
								vec![v.min_lit(ctx), v.max_lit(ctx)]
							}
							_ => unreachable!(),
						}));
					})?;
					Ok(SimplificationStatus::Subsumed)
				}
				Some(Reification::ReifiedBy(r)) => {
					debug_assert!(!satisfied);
					r.fix(ctx, false, fail_reason)?;
					Ok(SimplificationStatus::Subsumed)
				}
				None if !satisfied => Err(ctx.declare_conflict(fail_reason)),
				None => Ok(SimplificationStatus::Subsumed),
			};
		} else if self.comparator == LinComparator::NotEqual {
			// No further bounds propagation possible
			return Ok(SimplificationStatus::NoFixpoint);
		}

		// The difference between the right-hand-side value and the sum of the lower
		// bounds. The current lower bound plus this difference is an upper bound
		// for each variable.
		let lb_diff = self.rhs - lb_sum;
		// Propagate the upper bounds of the variables
		for (i, v) in self.terms.iter().enumerate() {
			let lb_i = lb[i].into();
			let new_ub = lb_diff + lb_i;
			let reason = reason_ty::<E::PropagationContext<'_>, _>(|ctx, reason| {
				reason.extend(
					self.terms
						.iter()
						.enumerate()
						.filter(|&(j, _)| j != i)
						.map(|(_, w)| w.min_lit(ctx)),
				);
			});
			if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
				if lb_i > new_ub {
					r.fix(ctx, false, reason)?;
					return Ok(SimplificationStatus::Subsumed);
				}
			} else {
				match new_ub.try_into() {
					Ok(new_ub) => v.tighten_max(ctx, new_ub, reason)?,
					Err(_) if new_ub < IntVal::MIN.into() => {
						return Err(ctx.declare_conflict(NO_REASON));
					}
					Err(_) => {
						debug_assert!(new_ub > IntVal::MAX.into());
					}
				}
			}
		}

		// For equality constraints, propagate the lower bounds of the variables
		if self.comparator == LinComparator::Equal {
			if lb_sum == ub_sum {
				assert_eq!(lb_sum, self.rhs);
				return Ok(SimplificationStatus::Subsumed);
			}

			// The amount the sum of the upper bounds exceeds the right-hand-side
			// value (negated). Used to propagate lower bounds of each variable.
			let ub_diff = self.rhs - ub_sum;
			for (i, v) in self.terms.iter().enumerate() {
				let ub_i = ub[i].into();
				let new_lb = ub_diff + ub_i;
				let reason = reason_ty::<E::PropagationContext<'_>, _>(|ctx, reason| {
					reason.extend(
						self.terms
							.iter()
							.enumerate()
							.filter(|&(j, _)| j != i)
							.map(|(_, &w)| w.max_lit(ctx)),
					);
				});
				if let Some(Reification::ReifiedBy(r) | Reification::ImpliedBy(r)) = self.reif {
					if ub_i < new_lb {
						r.fix(ctx, false, reason)?;
						return Ok(SimplificationStatus::Subsumed);
					}
				} else {
					match new_lb.try_into() {
						Ok(new_lb) => v.tighten_min(ctx, new_lb, reason)?,
						Err(_) if new_lb > IntVal::MAX.into() => {
							return Err(ctx.declare_conflict(NO_REASON));
						}
						Err(_) => {
							debug_assert!(new_lb < IntVal::MAX.into());
						}
					}
				}

				// We create a negated view in [`Self::to_solver`], ensure that it is correctly
				// bounded.
				let _ = v.bounding_neg(ctx)?;
			}
		}
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, slv: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		use Reification::*;

		// Linear constraints should otherwise have been simplified.
		debug_assert!(
			self.terms.len() > 1,
			"`IntLinear` must have at least two terms"
		);

		let terms = self.terms.iter().map(|&v| slv.solver_view(v)).collect_vec();
		let r = self.reif.as_ref().map(|&r| {
			slv.solver_view(match r {
				ImpliedBy(r) | ReifiedBy(r) => r,
			})
		});
		let full_reif = matches!(self.reif, Some(ReifiedBy(_)));

		// Detect Pseudo-Boolean constraints, and simplify them if possible.
		let (terms, operator, rhs) = if let Some(bool_lin) = self.try_bool_lin(&terms) {
			let map_cmp = |cmp| match cmp {
				pindakaas::bool_linear::Comparator::Equal => LinComparator::Equal,
				pindakaas::bool_linear::Comparator::LessEq => LinComparator::LessEq,
				pindakaas::bool_linear::Comparator::GreaterEq => unreachable!(),
			};

			let (op, lin) = match BoolLinAggregator::default().aggregate(slv, &bool_lin) {
				Err(Unsatisfiable) => return Err(slv.error.take().unwrap()),
				Ok(BoolLinVariant::Cardinality(card)) => (map_cmp(card.comparator()), card.into()),
				Ok(BoolLinVariant::CardinalityOne(card))
					if card.comparator() == pindakaas::bool_linear::Comparator::Equal =>
				{
					slv.add_clause(card.iter_lits().map(Decision))?;
					(LinComparator::LessEq, card.into())
				}
				Ok(BoolLinVariant::CardinalityOne(card)) => (LinComparator::LessEq, card.into()),
				Ok(BoolLinVariant::Linear(lin)) => (map_cmp(lin.comparator()), lin),
				Ok(BoolLinVariant::Trivial) => return Ok(()),
			};
			(
				lin.iter_terms()
					.map(|(lit, coeff)| {
						LinearBoolView::new(NonZero::new(coeff).unwrap(), 0, Decision(lit)).into()
					})
					.collect_vec(),
				op,
				lin.rhs().into(),
			)
		} else {
			(terms, self.comparator, self.rhs)
		};

		let negate_terms = |terms: &[solver::View<IntVal>]| terms.iter().map(|&v| -v).collect_vec();

		let sched = self.scheduling;
		match (operator, r) {
			(LinComparator::Equal, None) => {
				// coeffs * vars >= c <=> -coeffs * vars <= -c
				post_less_eq(slv, negate_terms(&terms), -rhs, None, sched);
				// coeffs * vars <= c
				post_less_eq(slv, terms, rhs, None, sched);
			}
			(LinComparator::Equal, Some(r)) => {
				if full_reif {
					IntLinearNotEqImpValue::<_, _, Decision<bool>>::post(
						slv,
						terms.clone(),
						rhs,
						!r,
					);
				}
				post_less_eq(slv, negate_terms(&terms), -rhs, Some(r), sched);
				post_less_eq(slv, terms, rhs, Some(r), sched);
			}
			(LinComparator::LessEq, None) => {
				post_less_eq(slv, terms, rhs, None, sched);
			}
			(LinComparator::LessEq, Some(r)) => {
				if full_reif {
					post_less_eq(
						slv,
						negate_terms(&terms),
						-(rhs + 1.into()),
						Some(!r),
						sched,
					);
				}
				post_less_eq(slv, terms, rhs, Some(r), sched);
			}
			(LinComparator::NotEqual, None) => {
				IntLinearNotEqValue::post(slv, terms, rhs);
			}
			(LinComparator::NotEqual, Some(r)) => {
				if full_reif {
					post_less_eq(slv, terms.clone(), rhs, Some(!r), sched);
					post_less_eq(slv, negate_terms(&terms), -rhs, Some(!r), sched);
				}
				IntLinearNotEqImpValue::<_, _, Decision<bool>>::post(slv, terms, rhs, r);
			}
		}
		Ok(())
	}
}

impl<E, OF> Propagator<E> for IntLinear<OF>
where
	E: ReasoningEngine,
	model::View<IntVal>: IntSolverActions<E>,
	model::View<bool>: BoolSolverActions<E>,
	OF: OverflowMode,
{
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		for &iv in &self.terms {
			iv.enqueue_when(ctx, IntPropCond::Bounds);
		}
		if let Some(Reification::ImpliedBy(r) | Reification::ReifiedBy(r)) = self.reif {
			r.enqueue_when_fixed(ctx);
		}
	}

	fn propagate(&mut self, _: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		unreachable!()
	}
}

impl IntLinearLessEqBounds<OverflowPossible, solver::View<IntVal>> {
	/// Create a new [`IntLinearLessEqBounds`] propagator and post it in the
	/// solver.
	///
	/// # Panics
	///
	/// Panics if no terms are given. An empty linear constraint is a constant
	/// comparison rather than a propagation problem, so the caller must
	/// evaluate it directly instead of posting a propagator.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		max: impl Into<DoubleIntVal>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let prop = Self::build(solver, vars, max, True);
		solver.add_propagator(Box::new(prop));
	}
}

impl<OF, IV, BV> IntLinearLessEqBoundsImpl<OF, IV, BV>
where
	OF: OverflowMode,
{
	/// Enforce `x[i] <= max - sum_{j != i} x[j].min` on every term, given the
	/// sum of the minima of all terms.
	///
	/// Returns the largest `x[i].max - x[i].min` left over the terms, saturated
	/// into the [`IntVal`] range, which bounds how much any single term can
	/// still grow. Terms are re-read after they are tightened, so a maximum
	/// that a hole in the domain pushed below the requested bound is reported
	/// as the smaller span it really is.
	fn propagate_terms<E>(
		&self,
		ctx: &mut E::PropagationContext<'_>,
		lb_sum: OF::Accumulator,
	) -> Result<IntVal, E::Conflict>
	where
		E: ReasoningEngine,
		IV: IntSolverActions<E>,
		E::Atom: BoolSolverActions<E>,
	{
		let slack = self.max - lb_sum;
		let mut max_span: DoubleIntVal = 0;
		for (j, v) in self.terms.iter().enumerate() {
			let (min, mut max) = v.bounds(ctx);
			// A term that cannot grow beyond the slack has nothing to prune.
			if DoubleIntVal::from(max) - DoubleIntVal::from(min) > slack.into() {
				let ub = slack + min.into();
				match ub.try_into() {
					Ok(ub) => v.tighten_max(ctx, ub, |_, rsn| rsn.defer(j as u64))?,
					Err(_) if ub < IntVal::MIN.into() => v
						.lit(ctx, IntLitMeaning::Less(IntVal::MIN))
						.require(ctx, |_, rsn| rsn.defer(j as u64))?,
					Err(_) => {
						debug_assert!(ub > max.into());
					}
				}
				max = v.max(ctx);
			}
			max_span = max_span.max(DoubleIntVal::from(max) - DoubleIntVal::from(min));
		}
		Ok(saturate(max_span))
	}
}

impl<BV> IntLinearLessEqBoundsImpl<OverflowPossible, solver::View<IntVal>, BV> {
	/// Collect the terms that are not yet fixed, folding the value of every
	/// fixed term into the right-hand side.
	///
	/// # Panics
	///
	/// Panics if no unfixed terms are left. An empty linear constraint is a
	/// constant comparison rather than a propagation problem, so the caller
	/// must evaluate it directly instead of posting a propagator.
	fn build<E>(
		solver: &E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		max: impl Into<DoubleIntVal>,
		reification: BV,
	) -> Self
	where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let mut max = max.into();
		let terms = vars
			.into_iter()
			.filter(|v| {
				if let Some(c) = v.val(solver) {
					max -= DoubleIntVal::from(c);
					false
				} else {
					true
				}
			})
			.collect_vec();
		assert!(
			!terms.is_empty(),
			"a linear propagator must be given at least one term"
		);
		Self {
			terms,
			max,
			reification,
		}
	}
}

impl<OF, BV, E, IV> Propagator<E> for IntLinearLessEqBoundsImpl<OF, IV, BV>
where
	OF: OverflowMode,
	E: ReasoningEngine,
	BV: BoolSolverActions<E>,
	IV: IntSolverActions<E>,
	E::Atom: BoolSolverActions<E>,
{
	#[tracing::instrument(
		name = "int_linear_less_eq_bounds",
		target = "solver",
		level = "trace",
		skip(self, ctx, reason)
	)]
	fn explain(
		&mut self,
		ctx: &mut E::ExplanationContext<'_>,
		_: E::Atom,
		data: u64,
		reason: &mut E::ReasonSink<'_>,
	) {
		let i = data as usize;
		let const_true: bool = TypeId::of::<BV>() == TypeId::of::<True>();
		debug_assert!(i <= self.terms.len());
		debug_assert!(!const_true || i < self.terms.len());

		reason.reserve(self.terms.len() - const_true as usize);
		for (j, t) in self.terms.iter().enumerate() {
			if j != i {
				reason.push(t.min_lit(ctx));
			}
		}
		if !const_true && i < self.terms.len() {
			reason.push(self.reification.clone().into());
		}
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		for v in self.terms.iter() {
			v.enqueue_when(ctx, IntPropCond::LowerBound);
		}
		self.reification.enqueue_when_fixed(ctx);
	}

	// propagation rule: x[i] <= rhs - sum_{j != i} x[j].min
	#[tracing::instrument(
		name = "int_linear_less_eq_bounds",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		// If the reified variable is false, skip propagation
		let r_val = self.reification.val(ctx);
		if r_val == Some(false) {
			return Ok(());
		}

		// Compute the sum of the lower bounds of all terms
		let lb_sum = self
			.terms
			.iter()
			.map(|v| OF::Accumulator::from(v.min(ctx)))
			.sum();

		if TypeId::of::<BV>() != TypeId::of::<True>() {
			// Propagate the reified variable if the sum of lower bounds is greater than the
			// right-hand-side value
			if lb_sum > self.max {
				self.reification.fix(ctx, false, |ctx, reason| {
					reason.extend(self.terms.iter().map(|v| v.min_lit(ctx)));
				})?;
			}
		}

		// skip the remaining propagation if the reified variable is not assigned to
		// true
		if r_val != Some(true) {
			return Ok(());
		}

		let _ = self.propagate_terms(ctx, lb_sum)?;
		Ok(())
	}
}

impl IntLinearLessEqImpBounds<OverflowPossible, solver::View<IntVal>, Decision<bool>> {
	/// Create a new [`IntLinearLessEqImpBounds`] propagator and post it in the
	/// solver.
	///
	/// # Panics
	///
	/// Panics if no terms are given. An empty linear constraint is a constant
	/// comparison rather than a propagation problem, so the caller must
	/// evaluate it directly instead of posting a propagator.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		max: impl Into<DoubleIntVal>,
		reification: solver::View<bool>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let max = max.into();
		let reification = match reification.0 {
			BoolView::Lit(r) => r,
			BoolView::Const(true) => {
				return IntLinearLessEqBounds::post(solver, vars, max);
			}
			BoolView::Const(false) => return,
		};
		let prop = Self::build(solver, vars, max, reification);
		solver.add_propagator(Box::new(prop));
	}
}

impl<const TRACK_MAX: bool>
	IntLinearLessEqImpSlack<OverflowPossible, solver::View<IntVal>, Decision<bool>, TRACK_MAX>
{
	/// Create a new [`IntLinearLessEqImpSlack`] propagator and post it in the
	/// solver.
	///
	/// # Panics
	///
	/// Panics if no terms are given. An empty linear constraint is a constant
	/// comparison rather than a propagation problem, so the caller must
	/// evaluate it directly instead of posting a propagator.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		max: impl Into<DoubleIntVal>,
		reification: solver::View<bool>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let max = max.into();
		let reification = match reification.0 {
			BoolView::Lit(r) => r,
			BoolView::Const(true) => {
				return IntLinearLessEqSlack::<_, _, TRACK_MAX>::post(solver, vars, max);
			}
			BoolView::Const(false) => return,
		};
		let inner = IntLinearLessEqImpBounds::build(solver, vars, max, reification);
		let prop = Self::new(solver, inner);
		solver.add_propagator(Box::new(prop));
	}
}

impl<const TRACK_MAX: bool>
	IntLinearLessEqSlack<OverflowPossible, solver::View<IntVal>, TRACK_MAX>
{
	/// Create a new [`IntLinearLessEqSlack`] propagator and post it in the
	/// solver.
	///
	/// # Panics
	///
	/// Panics if no terms are given. An empty linear constraint is a constant
	/// comparison rather than a propagation problem, so the caller must
	/// evaluate it directly instead of posting a propagator.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		max: impl Into<DoubleIntVal>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let inner = IntLinearLessEqBounds::build(solver, vars, max, True);
		let prop = Self::new(solver, inner);
		solver.add_propagator(Box::new(prop));
	}
}

impl<OF, IV, BV, const TRACK_MAX: bool> IntLinearLessEqSlackImpl<OF, IV, BV, TRACK_MAX>
where
	OF: OverflowMode,
{
	/// Create the propagator around `inner`, allocating and seeding its trailed
	/// state from the current bounds of the terms.
	fn new<E>(solver: &mut E, inner: IntLinearLessEqBoundsImpl<OF, IV, BV>) -> Self
	where
		E: PostingActions + ?Sized,
		IV: IntInspectionActions<E>,
	{
		let sum = |bound: fn(&IV, &E) -> IntVal, solver: &E| -> DoubleIntVal {
			inner
				.terms
				.iter()
				.map(|v| DoubleIntVal::from(bound(v, solver)))
				.sum()
		};
		let lb_sum = sum(IV::min, solver);
		let ub_sum = TRACK_MAX.then(|| sum(IV::max, solver));
		let slack = solver.new_trailed(saturate(inner.max.into() - lb_sum));
		let max_slack = solver.new_trailed(match ub_sum {
			Some(ub_sum) => saturate(inner.max.into() - ub_sum),
			None => IntVal::MIN,
		});
		// No propagation has happened yet, so the largest span is not yet known.
		let max_span = solver.new_trailed(IntVal::MAX);
		Self {
			inner,
			slack,
			max_span,
			max_slack,
		}
	}

	/// Recompute the incrementally maintained slacks from scratch, given the
	/// sum of the minima of all terms.
	///
	/// The maintained slacks are approximations that this restores to their
	/// exact values, and both ways in which they drift are safe:
	///
	/// - They can be *too large*, because an advisor is not told about a change
	///   until the SAT solver reports the corresponding literal back, so a
	///   change a propagator has already enacted may not be accounted for yet.
	///   Every enacted change is eventually reported and the advisor decides
	///   again on each one, so the last advice for a batch of changes is taken
	///   with all of them applied.
	/// - They can be *too small*, because a term whose domain is nearly the
	///   full [`IntVal`] range, or a change that could not be attributed to a
	///   single value, saturates the slack towards [`IntVal::MIN`]. That only
	///   schedules the propagator when it has nothing to do, and this recompute
	///   then restores the exact value.
	fn resync<E>(&self, ctx: &mut E::PropagationContext<'_>, lb_sum: OF::Accumulator)
	where
		E: ReasoningEngine,
		IV: IntSolverActions<E>,
	{
		let _ = ctx.set_trailed(self.slack, saturate(self.inner.max.into() - lb_sum.into()));

		if TRACK_MAX {
			let ub_sum: DoubleIntVal = self
				.inner
				.terms
				.iter()
				.map(|v| DoubleIntVal::from(v.max(ctx)))
				.sum();
			let _ = ctx.set_trailed(self.max_slack, saturate(self.inner.max.into() - ub_sum));
		}
	}

	/// Apply a term's bound change to a trailed `max - Σ bound` value, keeping
	/// it saturated within the [`IntVal`] range.
	fn shift<Ctx: TrailingActions>(
		ctx: &mut Ctx,
		slack: Trailed<IntVal>,
		previous: IntVal,
		current: IntVal,
	) {
		let shifted = DoubleIntVal::from(ctx.trailed(slack))
			- (DoubleIntVal::from(current) - DoubleIntVal::from(previous));
		let _ = ctx.set_trailed(slack, saturate(shifted));
	}

	/// Whether the current slack allows any term to still be pruned, and the
	/// propagator therefore has to run.
	fn should_enqueue<Ctx: TrailingActions>(&self, ctx: &Ctx) -> bool {
		// Once the sum of the maxima fits under the right-hand side the
		// constraint can no longer be violated, so nothing can be pruned.
		if TRACK_MAX && ctx.trailed(self.max_slack) >= 0 {
			return false;
		}
		let max_span = ctx.trailed(self.max_span);
		max_span == IntVal::MAX || ctx.trailed(self.slack) < max_span
	}
}

impl<OF, BV, E, IV, const TRACK_MAX: bool> Propagator<E>
	for IntLinearLessEqSlackImpl<OF, IV, BV, TRACK_MAX>
where
	OF: OverflowMode,
	E: ReasoningEngine,
	BV: BoolSolverActions<E>,
	IV: IntSolverActions<E>,
	E::Atom: BoolSolverActions<E>,
{
	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		data: u64,
		event: IntEvent,
		previous: Option<IntVal>,
	) -> bool {
		let Some(previous) = previous else {
			// A term backed by a Boolean is advised through its literal, which is
			// only ever reported as becoming fixed and carries no value to
			// attribute the change to. The maintained slack can then only be
			// brought up to date by running the propagator.
			debug_assert_eq!(event, IntEvent::Fixed);
			// Saturate the slack so that it stays an under-estimate until the
			// propagator runs and recomputes it.
			let _ = ctx.set_trailed(self.slack, IntVal::MIN);
			return true;
		};
		let term = self.inner.terms[data as usize].clone();
		let previous = term.transform_decision_val(previous);
		match event {
			IntEvent::LowerBound => Self::shift(ctx, self.slack, previous, term.min(ctx)),
			IntEvent::UpperBound => {
				debug_assert!(TRACK_MAX);
				Self::shift(ctx, self.max_slack, previous, term.max(ctx));
			}
			e => unreachable!("advised of {e:?} by a bound subscription"),
		}
		self.should_enqueue(ctx)
	}

	fn explain(
		&mut self,
		ctx: &mut E::ExplanationContext<'_>,
		lit: E::Atom,
		data: u64,
		reason: &mut E::ReasonSink<'_>,
	) {
		self.inner.explain(ctx, lit, data, reason);
	}

	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::Low);
		// Run once, so that the largest span of the terms becomes known and the
		// advisor can start suppressing work.
		ctx.enqueue_now(true);
		for (i, v) in self.inner.terms.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::LowerBound, i as u64);
			if TRACK_MAX {
				// A second subscription, rather than `IntPropCond::Bounds`, so that
				// each bound is advised of separately and can be attributed.
				v.advise_when(ctx, IntPropCond::UpperBound, i as u64);
			}
		}
		self.inner.reification.enqueue_when_fixed(ctx);
	}

	#[tracing::instrument(
		name = "int_linear_less_eq_slack",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		// The maintained slack is brought up to date even when the constraint is
		// switched off, so that it never has to be reasoned about as stale.
		let lb_sum: OF::Accumulator = self
			.inner
			.terms
			.iter()
			.map(|v| OF::Accumulator::from(v.min(ctx)))
			.sum();
		self.resync(ctx, lb_sum);

		let r_val = self.inner.reification.val(ctx);
		if r_val == Some(false) {
			return Ok(());
		}

		if TypeId::of::<BV>() != TypeId::of::<True>() && lb_sum > self.inner.max {
			let inner = &self.inner;
			inner.reification.fix(ctx, false, |ctx, reason| {
				reason.extend(inner.terms.iter().map(|v| v.min_lit(ctx)));
			})?;
		}
		if r_val != Some(true) {
			return Ok(());
		}

		let max_span = self.inner.propagate_terms(ctx, lb_sum)?;
		let _ = ctx.set_trailed(self.max_span, max_span);
		Ok(())
	}
}

impl IntLinearNotEqImpValue<OverflowPossible, solver::View<IntVal>, Decision<bool>> {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	///
	/// # Panics
	///
	/// Panics if no terms are given. An empty linear constraint is a constant
	/// comparison rather than a propagation problem, so the caller must
	/// evaluate it directly instead of posting a propagator.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		violation: impl Into<DoubleIntVal>,
		reification: solver::View<bool>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
		solver::View<bool>: BoolInspectionActions<E>,
	{
		let mut violation = violation.into();
		let reification = match reification.val(solver) {
			None => {
				let BoolView::Lit(r) = reification.0 else {
					unreachable!()
				};
				r
			}
			Some(true) => {
				return IntLinearNotEqValue::<OverflowPossible, _>::post(solver, vars, violation);
			}
			Some(false) => return,
		};

		let vars: Vec<_> = vars
			.into_iter()
			.filter(|&v| {
				if let Some(c) = v.val(solver) {
					violation -= DoubleIntVal::from(c);
					false
				} else {
					true
				}
			})
			.collect();
		assert!(
			!vars.is_empty(),
			"`IntLinearNotEqImpValue::post` must be given at least one term"
		);

		let num_free = solver.new_trailed(vars.len() + 1);

		if IntLinear::can_overflow(solver, &vars) || IntVal::try_from(violation).is_err() {
			solver.add_propagator(Box::new(IntLinearNotEqImpValue::<OverflowPossible, _, _> {
				terms: vars.clone(),
				violation,
				num_free,
				reification,
			}));
		} else {
			solver.add_propagator(Box::new(
				IntLinearNotEqImpValue::<OverflowImpossible, _, _> {
					terms: vars.clone(),
					violation: violation as IntVal,
					num_free,
					reification,
				},
			));
		}
	}
}

impl IntLinearNotEqValue<OverflowPossible, solver::View<IntVal>> {
	/// Create a new [`IntLinearNotEqImpValue`] propagator and post it in the
	/// solver.
	///
	/// # Panics
	///
	/// Panics if no terms are given. An empty linear constraint is a constant
	/// comparison rather than a propagation problem, so the caller must
	/// evaluate it directly instead of posting a propagator.
	pub fn post<E>(
		solver: &mut E,
		vars: impl IntoIterator<Item = solver::View<IntVal>>,
		violation: impl Into<DoubleIntVal>,
	) where
		E: PostingActions + ?Sized,
		solver::View<IntVal>: IntInspectionActions<E>,
	{
		let mut violation = violation.into();
		let vars: Vec<_> = vars
			.into_iter()
			.filter(|&v| {
				if let Some(c) = v.val(solver) {
					violation -= DoubleIntVal::from(c);
					false
				} else {
					true
				}
			})
			.collect();
		assert!(
			!vars.is_empty(),
			"`IntLinearNotEqValue::post` must be given at least one term"
		);

		let num_free = solver.new_trailed(vars.len());

		if IntLinear::can_overflow(solver, &vars) || IntVal::try_from(violation).is_err() {
			solver.add_propagator(Box::new(IntLinearNotEqValue::<OverflowPossible, _> {
				terms: vars.clone(),
				violation,
				num_free,
				reification: True,
			}));
		} else {
			solver.add_propagator(Box::new(IntLinearNotEqValue::<OverflowImpossible, _> {
				terms: vars.clone(),
				violation: violation as IntVal,
				num_free,
				reification: True,
			}));
		}
	}
}

impl<OF, IV, BV> IntLinearNotEqValueImpl<OF, IV, BV>
where
	OF: OverflowMode,
{
	/// Increment the number of decision variables that are fixed, returning
	/// whether the propagator should now be enqueued.
	fn decrement_num_free<Ctx>(&self, ctx: &mut Ctx) -> bool
	where
		Ctx: TrailingActions,
	{
		let num_free = ctx.trailed(self.num_free);
		debug_assert!(num_free >= 1);
		let num_free = num_free - 1;
		ctx.set_trailed(self.num_free, num_free);
		num_free <= 1
	}

	/// Helper function to construct the reason for propagation given the index
	/// of the variable in the list of variables to sum or the length of the
	/// list, if explaining the reification.
	fn reason<Ctx>(&self, data: usize) -> impl FnOnce(&mut Ctx, &mut Ctx::ReasonSink<'_>) + '_
	where
		Ctx: PropagationContext + ?Sized,
		IV: IntDecisionActions<Ctx>,
		BV: Clone + Into<Ctx::Atom> + 'static,
	{
		move |ctx, reason| {
			reason.extend(self.terms.iter().enumerate().filter_map(|(i, v)| {
				if data != i {
					Some(v.val_lit(ctx).unwrap())
				} else {
					None
				}
			}));
			if TypeId::of::<BV>() != TypeId::of::<True>() && data != self.terms.len() {
				reason.push(self.reification.clone().into());
			}
		}
	}
}

impl<OF, BV, IV, E> Propagator<E> for IntLinearNotEqValueImpl<OF, IV, BV>
where
	OF: OverflowMode,
	E: ReasoningEngine,
	E::Atom: BoolSolverActions<E> + From<bool>,
	IV: IntSolverActions<E>,
	BV: BoolSolverActions<E>,
{
	fn advise_of_bool_change(&mut self, ctx: &mut E::NotificationContext<'_>, _data: u64) -> bool {
		debug_assert_ne!(TypeId::of::<BV>(), TypeId::of::<True>());
		debug_assert_eq!(_data, self.terms.len() as u64);
		debug_assert!(self.reification.val(ctx).is_some());

		self.decrement_num_free(ctx)
	}

	fn advise_of_int_change(
		&mut self,
		ctx: &mut E::NotificationContext<'_>,
		_data: u64,
		_event: IntEvent,
		_: Option<IntVal>,
	) -> bool {
		debug_assert!(self.terms[_data as usize].val(ctx).is_some());
		debug_assert_eq!(_event, IntEvent::Fixed);
		self.decrement_num_free(ctx)
	}
	fn initialize(&mut self, ctx: &mut E::InitializationContext<'_>) {
		ctx.set_priority(PriorityLevel::High);
		for (i, v) in self.terms.iter().enumerate() {
			v.advise_when(ctx, IntPropCond::Fixed, i as u64);
		}
		self.reification
			.advise_when_fixed(ctx, self.terms.len() as u64);
	}

	#[tracing::instrument(
		name = "int_linear_not_eq_value",
		target = "solver",
		level = "trace",
		skip(self, ctx)
	)]
	fn propagate(&mut self, ctx: &mut E::PropagationContext<'_>) -> Result<(), E::Conflict> {
		let r_fixed = match self.reification.val(ctx) {
			Some(false) => return Ok(()),
			Some(true) => true,
			None => false,
		};

		let mut sum = OF::Accumulator::from(0);
		let mut unfixed = None;
		for (i, v) in self.terms.iter().enumerate() {
			if let Some(val) = v.val(ctx) {
				sum += val.into();
			} else if unfixed.is_some() {
				debug_assert!(false, "propagator shouldn't have been scheduled");
				return Ok(());
			} else {
				unfixed = Some((i, v));
			}
		}
		if let Some((i, v)) = unfixed {
			if !r_fixed {
				debug_assert!(false, "propagator shouldn't have been scheduled");
				return Ok(());
			}
			let val = self.violation - sum;
			if let Ok(val) = val.try_into() {
				v.remove_val(ctx, val, self.reason(i))?;
			}
			Ok(())
		} else if sum == self.violation {
			self.reification
				.fix(ctx, false, self.reason(self.terms.len()))
		} else {
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZero;

	use expect_test::expect;
	use tracing_test::traced_test;

	use crate::{
		IntSet, IntVal,
		actions::IntInspectionActions,
		constraints::int_linear::{
			DoubleIntVal, IntLinearLessEqBounds, IntLinearLessEqSlack, IntLinearNotEqValue,
			LinearScheduling,
		},
		model::{Model, view::View},
		solver::{IntLitMeaning, LiteralStrategy, Solver},
	};

	#[test]
	fn double_int_val() {
		assert_eq!(size_of::<DoubleIntVal>(), 2 * size_of::<IntVal>());
	}

	/// The scheduling strategy must not change what the propagator infers, only
	/// how often it runs, so every strategy has to admit the same solutions.
	#[test]
	#[traced_test]
	fn scheduling_preserves_solutions() {
		for scheduling in [
			LinearScheduling::Eager,
			LinearScheduling::Slack,
			LinearScheduling::SlackEntailment,
		] {
			let mut prb = Model::default();
			let r = prb.new_bool_decision();
			let a = prb.new_int_decision(1..=4);
			let b = prb.new_int_decision(1..=4);
			// A two-valued domain is backed by a Boolean, whose advisor arrives
			// through the literal path without a value to attribute the change to.
			let c = prb.new_int_decision(1..=2);

			// A `le`, a `ge` (negated terms) and a half-reified `le`, so that both
			// the plain and the reified propagator are covered in both directions.
			prb.linear(a * 2 + b + c)
				.le(9)
				.scheduling(scheduling)
				.post()
				.unwrap();
			prb.linear(a + b * 3 - c)
				.ge(2)
				.scheduling(scheduling)
				.post()
				.unwrap();
			prb.linear(a + b + c)
				.le(6)
				.implied_by(r)
				.scheduling(scheduling)
				.post()
				.unwrap();

			prb.expect_solutions(
				&[r.into(), a, b, c],
				expect![[r#"
    0, 1, 1, 1
    0, 1, 1, 2
    0, 1, 2, 1
    0, 1, 2, 2
    0, 1, 3, 1
    0, 1, 3, 2
    0, 1, 4, 1
    0, 1, 4, 2
    0, 2, 1, 1
    0, 2, 1, 2
    0, 2, 2, 1
    0, 2, 2, 2
    0, 2, 3, 1
    0, 2, 3, 2
    0, 2, 4, 1
    0, 3, 1, 1
    0, 3, 1, 2
    0, 3, 2, 1
    1, 1, 1, 1
    1, 1, 1, 2
    1, 1, 2, 1
    1, 1, 2, 2
    1, 1, 3, 1
    1, 1, 3, 2
    1, 1, 4, 1
    1, 2, 1, 1
    1, 2, 1, 2
    1, 2, 2, 1
    1, 2, 2, 2
    1, 2, 3, 1
    1, 3, 1, 1
    1, 3, 1, 2
    1, 3, 2, 1"#]],
			);
		}
	}

	/// Once the sum of the maxima fits under the right-hand side the constraint
	/// is entailed, and a propagator that tracks the maxima must stop
	/// scheduling itself.
	#[test]
	#[traced_test]
	fn slack_entailment_stops_scheduling() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(0..=10)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(0..=10)
			.order_literals(LiteralStrategy::Eager)
			.view();
		IntLinearLessEqSlack::<_, _, true>::post(&mut slv, vec![a, b], 12);
		let _ = slv.propagate_next().unwrap();

		// Dropping both maxima to 5 makes the sum of the maxima 10 <= 12, so the
		// constraint can no longer be violated.
		slv.assign_int_lit(a, IntLitMeaning::Less(6));
		slv.assign_int_lit(b, IntLitMeaning::Less(6));
		assert!(!slv.propagator_enqueued(0));

		// Without the entailment test the remaining slack of 7 would be below the
		// largest span of 5, and the propagator would be scheduled for nothing.
		slv.assign_int_lit(a, IntLitMeaning::GreaterEq(5));
		assert!(!slv.propagator_enqueued(0));
	}

	/// The slack propagator must prune exactly as much as the eager one, also
	/// when a hole in a domain makes a bound land below the value that was
	/// requested.
	#[test]
	#[traced_test]
	fn slack_prunes_across_domain_gaps() {
		for slack in [false, true] {
			let mut slv = Solver::default();
			// `a` has a hole: tightening its maximum to anything below 10 collapses
			// it to 0, well below the requested bound.
			let a = slv
				.new_int_decision(IntSet::from_iter([0..=0, 10..=10]))
				.order_literals(LiteralStrategy::Eager)
				.direct_literals(LiteralStrategy::Eager)
				.view();
			let b = slv
				.new_int_decision(0..=10)
				.order_literals(LiteralStrategy::Eager)
				.view();
			if slack {
				IntLinearLessEqSlack::<_, _, true>::post(&mut slv, vec![a, b], 8);
			} else {
				IntLinearLessEqBounds::post(&mut slv, vec![a, b], 8);
			}
			let propagated = slv.propagate_next().unwrap();

			// `a <= 8` snaps to `a <= 0`, and `b <= 8` is exact.
			assert_eq!(a.bounds(&slv), (0, 0), "slack: {slack}");
			assert_eq!(b.bounds(&slv), (0, 8), "slack: {slack}");
			assert_eq!(propagated.len(), 2, "slack: {slack}");
		}
	}

	/// A change that leaves enough slack for every term must not schedule the
	/// propagator, while one that does not must schedule it.
	#[test]
	#[traced_test]
	fn slack_skips_scheduling_when_idle() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(0..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(0..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();
		IntLinearLessEqSlack::<_, _, false>::post(&mut slv, vec![a, b], 100);
		// Run once so that the largest span is known.
		let _ = slv.propagate_next().unwrap();
		assert!(!slv.propagator_enqueued(0));

		// Plenty of slack is left, so raising a minimum cannot prune anything.
		slv.assign_int_lit(a, IntLitMeaning::GreaterEq(1));
		assert!(!slv.propagator_enqueued(0));

		// Once the slack drops below the largest span, the propagator has to run.
		let mut slv2 = Solver::default();
		let x = slv2
			.new_int_decision(0..=10)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let y = slv2
			.new_int_decision(0..=10)
			.order_literals(LiteralStrategy::Eager)
			.view();
		IntLinearLessEqSlack::<_, _, false>::post(&mut slv2, vec![x, y], 12);
		let _ = slv2.propagate_next().unwrap();
		assert!(!slv2.propagator_enqueued(0));
		slv2.assign_int_lit(x, IntLitMeaning::GreaterEq(6));
		assert!(slv2.propagator_enqueued(0));
	}

	#[test]
	fn test_constraint_rewriting() {
		// Regression test for GitHub issue 233, where a `int_lin_le_reif` known to be
		// false was rewritten incorrectly. It allowed `a` to be 2.
		let mut prb = Model::default();
		let a = prb.new_int_decision(1..=2);
		let r: View<bool> = false.into();

		prb.linear(-a).le(-2).reified_by(r).post().unwrap();

		prb.expect_solutions(&[a], expect![[r#"1"#]]);
	}

	#[test]
	#[traced_test]
	fn test_linear_ge_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();

		IntLinearLessEqBounds::post(&mut slv, vec![a * NonZero::new(-2).unwrap(), -b, -c], -6);

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
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		assert!(prb.linear(a * 2 + b + c).ge(10).post().is_err());
	}

	#[test]
	#[traced_test]
	fn test_linear_le_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.view();

		IntLinearLessEqBounds::post(&mut slv, vec![a * NonZero::new(2).unwrap(), b, c], 6);

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
		let a = prb.new_int_decision(1..=4);
		let b = prb.new_int_decision(1..=4);
		let c = prb.new_int_decision(1..=4);

		assert!(prb.linear(a * 2 + b + c).le(3).post().is_err());
	}

	#[test]
	#[traced_test]
	fn test_linear_ne_sat() {
		let mut slv = Solver::default();
		let a = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let b = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();
		let c = slv
			.new_int_decision(1..=2)
			.order_literals(LiteralStrategy::Eager)
			.direct_literals(LiteralStrategy::Eager)
			.view();

		IntLinearNotEqValue::post(&mut slv, vec![a * NonZero::new(2).unwrap(), b, c], 6);

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
		let r = prb.new_bool_decision();
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		prb.linear(a * 2 + b + c)
			.ge(7)
			.implied_by(r)
			.post()
			.unwrap();

		let (mut slv, map): (Solver, _) = prb.lower().to_solver().unwrap();
		let a = map.get_any(&mut slv, a.into());
		let b = map.get_any(&mut slv, b.into());
		let c = map.get_any(&mut slv, c.into());
		let r = map.get_any(&mut slv, r.into());
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
		let r = prb.new_bool_decision();
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		prb.linear(a * 2 + b + c)
			.le(5)
			.implied_by(r)
			.post()
			.unwrap();

		let (mut slv, map): (Solver, _) = prb.lower().to_solver().unwrap();
		let a = map.get_any(&mut slv, a.into());
		let b = map.get_any(&mut slv, b.into());
		let c = map.get_any(&mut slv, c.into());
		let r = map.get_any(&mut slv, r.into());
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
		let r = prb.new_bool_decision();
		let a = prb.new_int_decision(1..=2);
		let b = prb.new_int_decision(1..=2);
		let c = prb.new_int_decision(1..=2);

		prb.linear(a * 2 + b + c)
			.ne(6)
			.implied_by(r)
			.post()
			.unwrap();

		let (mut slv, map): (Solver, _) = prb.lower().to_solver().unwrap();
		let a = map.get_any(&mut slv, a.into());
		let b = map.get_any(&mut slv, b.into());
		let c = map.get_any(&mut slv, c.into());
		let r = map.get_any(&mut slv, r.into());
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
