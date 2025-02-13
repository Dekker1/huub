use std::collections::{HashMap, HashSet};

use pindakaas::{solver::propagation::PropagatingSolver, Lit as RawLit, Var as RawVar};
use rangelist::{IntervalIterator, RangeList};
use tracing::debug;

use crate::{
	actions::{
		BrancherInitActions, DecisionActions, InspectionActions, PropagationActions,
		TrailingActions,
	},
	constraints::Conflict,
	helpers::trailed_list::TrailedList,
	solver::{
		engine::Engine, solving_context::SolvingContext, BoolView, BoolViewInner, IntView, SetView,
		Solver,
	},
	Clause, Conjunction, IntLitMeaning, IntVal, SetViewInner,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct SetVar {
	/// The [`IntView`] that represents the cardinality of the optional part of
	/// the set.
	pub(crate) optional_card: Option<IntView>,
	/// A list of the elements (from [`Self::optional_elements`]) in the set that
	/// have been currently chosen.
	pub(crate) chosen: TrailedList<IntVal>,
	/// Elements that are already known to be part of the set.
	pub(crate) mandatory_elements: RangeList<IntVal>,
	/// Elements that could potentially be part of the set.
	pub(crate) optional_elements: RangeList<IntVal>,
	/// A map containing the mapping from element value to the representative
	/// Boolean variable, if it has been created.
	pub(crate) vars: HashMap<IntVal, RawVar>,
}

impl SetVar {
	/// Construct a clause explaining why the cardinality of the set has been
	/// exceeded.
	fn cardinality_exceeded_clause(&self, actions: &mut impl DecisionActions) -> Clause {
		// TODO: Could probably be unified with propagate_cardinality.
		let card_lit = match actions
			.get_int_lit(
				self.optional_card.unwrap(),
				IntLitMeaning::GreaterEq(self.chosen.len(actions) as IntVal),
			)
			.0
		{
			BoolViewInner::Lit(card_lit) => Some(card_lit),
			BoolViewInner::Const(false) => None,
			BoolViewInner::Const(true) => unreachable!(),
		};
		self.chosen
			.iter(actions)
			.map(|elem| !self.vars[elem])
			.chain(card_lit)
			.collect()
	}

	/// Get the [`BoolView`] that represents whether a given element is in the set
	/// if it has been created, or create it if it doesn't exist.
	///
	/// Note that the `new_var` closure is called with the conjunction, then this
	/// should be the reason used to enforce that the new variable is `false`.
	pub(crate) fn elem_lit<A: InspectionActions>(
		&mut self,
		elem: IntVal,
		actions: &A,
		mut new_var: impl FnMut(Option<Conjunction>) -> RawVar,
	) -> BoolView {
		// Check whether a literal already exists for this element.
		if let Some(bv) = self.get_elem_lit(elem) {
			return bv;
		}

		// Check whether the new element exceeds the cardinality of the set, and
		// create a reason if required.
		let mut reason = None;
		if let Some(card) = self.optional_card {
			let cur_card = self.chosen.len(actions);
			if cur_card as IntVal >= actions.get_int_upper_bound(card) {
				reason = Some(
					self.chosen
						.iter(actions)
						.map(|elem| self.vars[elem].into())
						.collect(),
				);
			}
		}

		// Record new variable and return it as a literal.
		let var = new_var(reason);
		let res = self.vars.insert(elem, var);
		debug_assert_eq!(res, None);
		BoolView(BoolViewInner::Lit(var.into()))
	}

	/// Get the [`BoolView`] that represents whether a given element is in the set
	/// if it has been created, otherwise `None`.
	pub(crate) fn get_elem_lit(&self, elem: IntVal) -> Option<BoolView> {
		// Check whether a literal already exists for this element.
		if let Some(&var) = self.vars.get(&elem) {
			return Some(BoolView(BoolViewInner::Lit(var.into())));
		}
		// Check whether the element is known to be in the set.
		if self.mandatory_elements.contains(&elem) {
			return Some(true.into());
		}
		// Check whether the element is known to not be in the set.
		if !self.optional_elements.contains(&elem) {
			return Some(false.into());
		}
		// Otherwise, no literal exists.
		None
	}

	/// Introduce new literals to allow the set variable to match the given
	/// cardinality, if possible.
	///
	/// If the cardinality higher than the amount of included elements, this
	/// function will return a list of the introduced literals for elements that
	/// are now assumed true. Otherwise, it will return a clause that explains why
	/// the cardinality is too low.
	pub(crate) fn match_card(
		&mut self,
		set_var: SetVarRef,
		ctx: &mut SolvingContext<'_>,
	) -> Result<Vec<RawLit>, Clause> {
		if let Some(card) = self.optional_card {
			let cur_card = self.chosen.len(ctx);
			let card_val = ctx.get_int_val(card).unwrap();

			let elem_required = card_val - cur_card as IntVal;
			let elem_remaining = self.optional_elements.card() - self.vars.len();
			debug!(elem_required, elem_remaining, chosen = ?self.chosen.as_slice(ctx), "match_card");

			return match (elem_required, elem_required <= elem_remaining as IntVal) {
				// The cardinality is already reached: no need to introduce new
				// elements.
				(0, _) => Ok(Vec::new()),
				// We already exceeded the cardinality: give a clause that given the
				// chosen elements, the cardinality must be greater or equal to the
				// number of chosen elements.
				(c, _) if c < 0 => Err(self.cardinality_exceeded_clause(ctx)),
				// There are not enough elements to reach the cardinality: give a clause
				// that given the number of unchosen elements, the cardinality must be
				// less or equal to the number of chosen elements.
				(_, false) => {
					debug!(lit_req = ?IntLitMeaning::Less(cur_card as IntVal + 1), "request");
					let card_lit = match ctx
						.get_int_lit(card, IntLitMeaning::Less(cur_card as IntVal + 1))
						.0
					{
						BoolViewInner::Lit(card_lit) => Some(card_lit),
						BoolViewInner::Const(false) => None,
						BoolViewInner::Const(true) => unreachable!(),
					};
					let chosen_set: HashSet<IntVal> = self.chosen.iter(ctx).copied().collect();
					Err(self
						.optional_elements
						.iter()
						.flatten()
						.filter(|elem| !chosen_set.contains(elem))
						.filter_map(|elem| self.vars.get(&elem).map(|&var| var.into()))
						.chain(card_lit)
						.collect())
				}
				// We can introduce new elements to reach the cardinality.
				(_, true) => {
					let mut lits = Vec::new();
					for elem in self.optional_elements.iter().flatten() {
						if !self.vars.contains_key(&elem) {
							let var = ctx.slv.new_var();
							// Mapping from element to variable and vice versa.
							ctx.state.trail.grow_to_boolvar(var);
							let x = self.vars.insert(elem, var);
							debug_assert_eq!(x, None);
							ctx.state.bool_to_int.insert_set_var(var, set_var, elem);
							// Add the element to the chosen set
							self.chosen.push(ctx, elem);
							// Return variable as literal.
							lits.push(var.into());

							if lits.len() as IntVal == elem_required {
								break;
							}
						}
					}
					debug_assert_eq!(self.chosen.len(ctx), card_val as usize);
					Ok(lits)
				}
			};
		}
		Ok(Vec::new())
	}

	pub(crate) fn new_in<Oracle: PropagatingSolver<Engine>>(
		slv: &mut Solver<Oracle>,
		mandatory_elements: RangeList<IntVal>,
		optional_elements: RangeList<IntVal>,
		card: Option<IntView>,
	) -> SetView {
		let chosen = TrailedList::new(slv);
		let optional_card = card.map(|c| c - mandatory_elements.card() as IntVal);
		if let Some(card) = optional_card {
			slv.ensure_decidable(card.into());
		}
		SetView(SetViewInner::Lazy(slv.engine_mut().state.set_vars.push(
			SetVar {
				optional_card,
				chosen,
				mandatory_elements,
				optional_elements,
				vars: HashMap::new(),
			},
		)))
	}

	/// Method to update the set variable storage about the inclusion of an
	/// element by the oracle solver. The method will return whether to schedule
	/// the variable for cardinality propagation.
	pub(crate) fn notify_include_element<A: TrailingActions>(
		&mut self,
		actions: &mut A,
		elem: IntVal,
	) -> bool {
		debug_assert!(self.optional_elements.contains(&elem));
		debug_assert!(!self.chosen.as_slice(actions).contains(&elem));

		// Record the element as chosen.
		self.chosen.push(actions, elem);

		self.optional_card.is_some()
	}

	/// Propagate the cardinality integer decision variable based on the number of
	/// chosen elements.
	pub(crate) fn propagate_cardinality<A: PropagationActions>(
		&self,
		actions: &mut A,
	) -> Result<(), Conflict> {
		let Some(card) = self.optional_card else {
			unreachable!();
		};
		let cur_card = self.chosen.len(actions);
		// Check whether the cardinality is exceeded.
		actions.set_int_lower_bound(card, cur_card as IntVal, |actions: &mut A| {
			self.chosen
				.iter(actions)
				.map(|elem| BoolView(BoolViewInner::Lit(self.vars[elem].into())))
		})
	}
}

index_vec::define_index_type! {
	/// Identifies an set of integers decision variable in a [`Solver`]
	pub struct SetVarRef = u32;
}
