//! Tests of the library: every declared constraint against its definition in
//! the registry, and the reuse of the solver across the runs of a layered
//! model.

use std::{collections::BTreeSet, rc::Rc};

use fznso::{
	LayeredModel, Model, OwnedValue, RangeList, Solution, Solver, SolverType, Status, Type,
	TypeBase, Value, ValueExt, ValueView, dont_interrupt, ignore_messages,
};

use crate::{HuubSolution, HuubSolver, declarations::CONSTRAINTS};

/// A Boolean decision.
const B: Domain = Domain::Bool;

/// A constraint to test against its definition.
struct Case {
	/// The identifier of the constraint.
	ident: String,
	/// The domain of each decision of the test model.
	domains: Vec<Domain>,
	/// The arguments of the constraint, given the decisions.
	args: Rc<dyn Fn(&[OwnedValue]) -> Vec<OwnedValue>>,
	/// Whether an assignment to the decisions satisfies the definition.
	check: Rc<dyn Fn(&[i64]) -> bool>,
}

/// The domain of a decision in a test model.
#[derive(Clone, Copy, Debug)]
enum Domain {
	/// A Boolean decision, taken as 0 or 1.
	Bool,
	/// An integer decision from the first value to the second.
	Int(i64, i64),
}

/// A layer that becomes permanent is committed to, rather than assumed.
#[test]
fn a_layer_made_permanent_is_committed() {
	let mut model = LayeredModel::default();
	let x = int_decision(&mut model, 0, 5);
	model.set_objective(Some("int_maximize"), x.clone(), Vec::new());
	model.push_layer();
	let _ = model.add_constraint(
		"int_lin_le",
		vec![ints(&[1]), list(&[x]), OwnedValue::Int(3)],
		None,
		Vec::new(),
	);
	let mut solver = HuubSolver::new();
	assert!(matches!(
		best(&mut solver, &model),
		(Status::Complete, Some(3))
	));
	assert!(solver.live.as_ref().unwrap().layers[1].activation.is_some());

	model.mark_permanent();
	model.set_unchanged(2);
	assert!(matches!(
		best(&mut solver, &model),
		(Status::Complete, Some(3))
	));
	assert!(solver.live.as_ref().unwrap().layers[1].activation.is_none());
	assert_eq!(solver.builds, 1);
}

/// Retracting a layer whose constraints its activation literal conditions
/// keeps the solver.
#[test]
fn a_retracted_layer_keeps_the_solver() {
	let mut model = LayeredModel::default();
	let x = int_decision(&mut model, 0, 5);
	model.set_objective(Some("int_maximize"), x.clone(), Vec::new());
	let mut solver = HuubSolver::new();
	assert!(matches!(
		best(&mut solver, &model),
		(Status::Complete, Some(5))
	));

	model.set_unchanged(1);
	model.push_layer();
	let _ = model.add_constraint(
		"int_lin_le",
		vec![ints(&[1]), list(&[x]), OwnedValue::Int(3)],
		None,
		Vec::new(),
	);
	assert!(matches!(
		best(&mut solver, &model),
		(Status::Complete, Some(3))
	));

	model.set_unchanged(2);
	model.pop_layer();
	assert!(matches!(
		best(&mut solver, &model),
		(Status::Complete, Some(5))
	));
	assert_eq!(solver.builds, 1);
}

/// With `all_solutions`, the solutions that tie with the optimum follow it.
#[test]
fn all_solutions_report_the_ties() {
	let (mut model, decisions) = model_of(&[i(0, 2), i(0, 2)]);
	model.set_objective(Some("int_maximize"), decisions[0].clone(), Vec::new());
	let mut solver = HuubSolver::new();
	solver
		.option_set("all_solutions", Value::from_bool(true))
		.unwrap();
	let (status, found) = solutions(&mut solver, &model);
	assert!(matches!(status, Status::Complete));
	let found: BTreeSet<_> = found.into_iter().collect();
	assert_eq!(found, BTreeSet::from([vec![2, 0], vec![2, 1], vec![2, 2]]));
}

/// An unsatisfiable model completes without a solution.
#[test]
fn an_unsatisfiable_model_completes() {
	let (mut model, decisions) = model_of(&[i(0, 2)]);
	let _ = model.add_constraint(
		"int_lin_le",
		vec![ints(&[1]), list(&decisions), OwnedValue::Int(-1)],
		None,
		Vec::new(),
	);
	let mut solver = HuubSolver::new();
	let (status, found) = solutions(&mut solver, &model);
	assert!(matches!(status, Status::Complete));
	assert!(found.is_empty());
}

/// Every assignment of values to decisions with the given domains.
fn assignments(domains: &[Domain]) -> Vec<Vec<i64>> {
	domains.iter().fold(vec![Vec::new()], |partial, domain| {
		let (min, max) = match *domain {
			Domain::Bool => (0, 1),
			Domain::Int(min, max) => (min, max),
		};
		partial
			.into_iter()
			.flat_map(|p| {
				(min..=max).map(move |v| {
					let mut next = p.clone();
					next.push(v);
					next
				})
			})
			.collect()
	})
}

/// Run `model`, returning the last value of the objective that was reported.
fn best(solver: &mut HuubSolver, model: &LayeredModel) -> (Status, Option<i64>) {
	let mut objective = None;
	let status = solver.run(
		model,
		&mut |sol: &HuubSolution| objective = Some(sol.statistic("int_objective").get_int()),
		ignore_messages(),
		dont_interrupt(),
	);
	(status, objective)
}

/// A test case for a constraint.
fn case(
	ident: &str,
	domains: &[Domain],
	args: impl Fn(&[OwnedValue]) -> Vec<OwnedValue> + 'static,
	check: impl Fn(&[i64]) -> bool + 'static,
) -> Case {
	Case {
		ident: ident.to_owned(),
		domains: domains.to_vec(),
		args: Rc::new(args),
		check: Rc::new(check),
	}
}

/// A test case for every constraint the library declares.
fn cases() -> Vec<Case> {
	let int = OwnedValue::Int;
	let mut cases = Vec::new();

	cases.extend(reifiable(
		"int_lin_eq",
		&[i(-2, 2), i(-2, 2)],
		move |d| vec![ints(&[2, -1]), list(d), int(1)],
		|s| 2 * s[0] - s[1] == 1,
	));
	cases.extend(reifiable(
		"int_lin_le",
		&[i(-2, 2), i(-2, 2)],
		move |d| vec![ints(&[2, -1]), list(d), int(1)],
		|s| 2 * s[0] - s[1] <= 1,
	));
	cases.extend(reifiable(
		"int_lin_ne",
		&[i(-2, 2), i(-2, 2)],
		move |d| vec![ints(&[2, -1]), list(d), int(1)],
		|s| 2 * s[0] - s[1] != 1,
	));
	cases.extend(reifiable(
		"bool_lin_le",
		&[B, B, B],
		move |d| vec![ints(&[2, 3, -1]), list(d), int(2)],
		|s| 2 * s[0] + 3 * s[1] - s[2] <= 2,
	));
	cases.extend(reifiable(
		"bool_lin_ne",
		&[B, B, i(0, 3)],
		|d| vec![ints(&[1, 2]), list(&d[..2]), d[2].clone()],
		|s| s[0] + 2 * s[1] != s[2],
	));
	cases.push(case(
		"bool_lin_eq",
		&[B, B, B, i(0, 4)],
		|d| vec![ints(&[1, 2, 1]), list(&d[..3]), d[3].clone()],
		|s| s[0] + 2 * s[1] + s[2] == s[3],
	));
	cases.extend(reifiable(
		"bool_clause",
		&[B, B, B],
		|d| vec![list(&d[..2]), list(&d[2..])],
		|s| s[0] == 1 || s[1] == 1 || s[2] == 0,
	));
	cases.extend(reifiable(
		"bool_array_xor",
		&[B, B, B],
		|d| vec![list(d)],
		|s| (s[0] + s[1] + s[2]) % 2 == 1,
	));
	// Two literals are posted as a view, one the negation of the other.
	cases.extend(reifiable(
		"bool_array_xor",
		&[B, B],
		|d| vec![list(d)],
		|s| s[0] != s[1],
	));
	cases.push(case(
		"bool_array_and",
		&[B, B, B],
		|d| vec![list(&d[..2]), d[2].clone()],
		|s| (s[0] == 1 && s[1] == 1) == (s[2] == 1),
	));
	cases.push(case(
		"bool_to_int",
		&[B, i(-1, 2)],
		<[OwnedValue]>::to_vec,
		|s| s[0] == s[1],
	));
	cases.push(case(
		"int_abs",
		&[i(-3, 3), i(-1, 3)],
		<[OwnedValue]>::to_vec,
		|s| s[1] == s[0].abs(),
	));
	cases.push(case(
		"int_times",
		&[i(-2, 2), i(-2, 2), i(-4, 4)],
		<[OwnedValue]>::to_vec,
		|s| s[2] == s[0] * s[1],
	));
	cases.push(case(
		"int_div",
		&[i(-3, 3), i(-2, 2), i(-3, 3)],
		<[OwnedValue]>::to_vec,
		|s| s[1] != 0 && s[2] == s[0] / s[1],
	));
	cases.push(case(
		"int_pow",
		&[i(-2, 2), i(-1, 2), i(-4, 4)],
		<[OwnedValue]>::to_vec,
		// MiniZinc's integer power: a negative exponent truncates like division,
		// and only a zero base makes it undefined. The registry's note calls
		// every base other than 1 and -1 undefined, which MiniZinc does not do.
		|s| match (s[0], s[1]) {
			(0, e) if e < 0 => false,
			(1, e) if e < 0 => s[2] == 1,
			(-1, e) if e < 0 => s[2] == if e % 2 == 0 { 1 } else { -1 },
			(_, e) if e < 0 => s[2] == 0,
			(b, e) => s[2] == b.pow(u32::try_from(e).unwrap()),
		},
	));
	cases.push(case(
		"int_array_element",
		&[i(0, 2), i(1, 4), i(0, 5)],
		move |d| {
			vec![
				list(&[int(5), d[0].clone()]),
				int(2),
				d[1].clone(),
				d[2].clone(),
			]
		},
		|s| match s[1] {
			2 => s[2] == 5,
			3 => s[2] == s[0],
			_ => false,
		},
	));
	cases.push(case(
		"bool_array_element",
		&[B, i(-1, 2), B],
		move |d| {
			vec![
				list(&[OwnedValue::Bool(true), d[0].clone()]),
				int(0),
				d[1].clone(),
				d[2].clone(),
			]
		},
		|s| match s[1] {
			0 => s[2] == 1,
			1 => s[2] == s[0],
			_ => false,
		},
	));
	cases.push(case(
		"int_array_maximum",
		&[i(-1, 1), i(-1, 1), i(-2, 2)],
		move |d| vec![list(&[d[0].clone(), d[1].clone(), int(0)]), d[2].clone()],
		|s| s[2] == s[0].max(s[1]).max(0),
	));
	cases.push(case(
		"int_array_minimum",
		&[i(-1, 1), i(-1, 1), i(-2, 2)],
		move |d| vec![list(&[d[0].clone(), d[1].clone(), int(0)]), d[2].clone()],
		|s| s[2] == s[0].min(s[1]).min(0),
	));
	cases.extend(reifiable(
		"int_in",
		&[i(0, 5)],
		|d| {
			vec![
				d[0].clone(),
				OwnedValue::IntSet([1..=2, 4..=4].into_iter().collect()),
			]
		},
		|s| matches!(s[0], 1 | 2 | 4),
	));
	cases.push(case(
		"int_all_different",
		&[i(1, 3); 3],
		|d| vec![list(d)],
		|s| s[0] != s[1] && s[0] != s[2] && s[1] != s[2],
	));
	cases.push(case(
		"int_table",
		&[i(0, 2), i(0, 2)],
		|d| vec![list(d), ints(&[0, 1, 1, 2, 2, 2])],
		|s| matches!((s[0], s[1]), (0, 1) | (1, 2) | (2, 2)),
	));
	cases.push(case(
		"int_circuit",
		&[i(0, 2); 3],
		move |d| vec![list(d), int(0)],
		|s| circuit(s, 0),
	));
	cases.push(case(
		"int_subcircuit",
		&[i(1, 3); 3],
		move |d| vec![list(d), int(1)],
		|s| subcircuit(s, 1),
	));
	cases.push(case(
		"int_cumulative",
		&[i(0, 2), i(0, 2), i(0, 1), i(1, 2)],
		move |d| {
			vec![
				list(&d[..2]),
				list(&[int(2), d[2].clone()]),
				ints(&[1, 1]),
				d[3].clone(),
			]
		},
		|s| cumulative(&[s[0], s[1]], &[2, s[2]], &[1, 1], s[3]),
	));
	cases.push(case(
		"int_disjunctive_strict",
		&[i(0, 3), i(0, 3)],
		|d| vec![list(d), ints(&[2, 0])],
		|s| s[0] + 2 <= s[1] || s[1] <= s[0],
	));
	// Two rectangles: (x0, y0) sized 2 by 1, and (x1, y1) sized 1 by dy1.
	let rectangles = [i(0, 2), i(0, 2), i(0, 1), i(0, 1), i(0, 1)];
	let separate =
		|s: &[i64]| s[0] + 2 <= s[1] || s[1] < s[0] || s[2] < s[3] || s[3] + s[4] <= s[2];
	for (ident, strict) in [
		("int_no_overlap", true),
		("int_no_overlap_nonstrict", false),
	] {
		cases.push(case(
			ident,
			&rectangles,
			move |d| {
				vec![
					list(&d[..2]),
					ints(&[2, 1]),
					list(&d[2..4]),
					list(&[int(1), d[4].clone()]),
				]
			},
			move |s| separate(s) || (!strict && s[4] == 0),
		));
	}
	for (ident, strict) in [
		("int_no_overlap_nd", true),
		("int_no_overlap_nd_nonstrict", false),
	] {
		cases.push(case(
			ident,
			&rectangles,
			move |d| {
				vec![
					int(2),
					list(&[d[0].clone(), d[2].clone(), d[1].clone(), d[3].clone()]),
					list(&[int(2), int(1), int(1), d[4].clone()]),
				]
			},
			move |s| separate(s) || (!strict && s[4] == 0),
		));
	}
	cases.push(case(
		"int_seq_precede_chain",
		&[i(0, 3); 3],
		|d| vec![list(d)],
		|s| {
			let mut max = 0;
			s.iter().all(|&x| {
				let ok = x <= max + 1;
				max = max.max(x);
				ok
			})
		},
	));
	cases.push(case(
		"int_value_precede_chain",
		&[i(0, 3); 3],
		|d| vec![ints(&[3, 1, 2]), list(d)],
		|s| value_precede_chain(&[3, 1, 2], s),
	));
	cases.push(case(
		"int_value_precede",
		&[i(0, 2); 3],
		move |d| vec![int(2), int(0), list(d)],
		|s| value_precede_chain(&[2, 0], s),
	));
	cases
}

/// Whether the successors `s`, numbered from `offset`, form one circuit.
fn circuit(s: &[i64], offset: i64) -> bool {
	let mut seen = vec![false; s.len()];
	let mut node = 0;
	for _ in 0..s.len() {
		if seen[node] {
			return false;
		}
		seen[node] = true;
		node = usize::try_from(s[node] - offset).unwrap();
	}
	node == 0
}

/// Every declared constraint accepts exactly the assignments its registry
/// definition does: posted in the permanent base layer, and posted in a layer
/// of its own that is conditioned on an activation literal.
#[test]
fn constraints_match_their_definitions() {
	let cases = cases();
	let mut failures = Vec::new();
	for declared in CONSTRAINTS {
		// SAFETY: every identifier is declared from a string literal.
		let ident = unsafe { declared.ident.as_str() }.unwrap();
		match cases.iter().find(|c| c.ident == ident) {
			Some(c) => {
				let (_, decisions) = model_of(&c.domains);
				assert_eq!(
					(c.args)(&decisions).len(),
					declared.arg_len,
					"the test of `{ident}` passes the wrong number of arguments"
				);
			}
			None => failures.push(format!("`{ident}` is declared, but not tested")),
		}
	}

	for c in &cases {
		let expected: BTreeSet<Vec<i64>> = assignments(&c.domains)
			.into_iter()
			.filter(|s| (c.check)(s))
			.collect();
		for layered in [false, true] {
			let (mut model, decisions) = model_of(&c.domains);
			if layered {
				model.push_layer();
			}
			let _ = model.add_constraint(c.ident.clone(), (c.args)(&decisions), None, Vec::new());
			let mut solver = HuubSolver::new();
			solver
				.option_set("all_solutions", Value::from_bool(true))
				.unwrap();
			let (status, found) = solutions(&mut solver, &model);
			let found_len = found.len();
			let found: BTreeSet<Vec<i64>> = found.into_iter().collect();
			let place = if layered { "in a layer" } else { "in the base" };
			if !matches!(status, Status::Complete) || found_len != found.len() {
				failures.push(format!(
					"`{}` {place}: status {status:?}, {found_len} solutions reported for {} distinct",
					c.ident,
					found.len()
				));
			}
			if found != expected {
				failures.push(format!(
					"`{}` {place}: missing {:?}, not allowed {:?}",
					c.ident,
					expected.difference(&found).collect::<Vec<_>>(),
					found.difference(&expected).collect::<Vec<_>>()
				));
			}
			if layered {
				// With the layer retracted, every assignment is a solution.
				model.set_unchanged(2);
				model.pop_layer();
				let (_, found) = solutions(&mut solver, &model);
				if found.len() != assignments(&c.domains).len() {
					failures.push(format!(
						"`{}` retracted: {} solutions reported",
						c.ident,
						found.len()
					));
				}
			}
		}
	}
	assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Whether no more than `capacity` is used at any time by the tasks.
fn cumulative(starts: &[i64], durations: &[i64], usages: &[i64], capacity: i64) -> bool {
	(0..=8).all(|t| {
		let used: i64 = (0..starts.len())
			.filter(|&k| starts[k] <= t && t < starts[k] + durations[k])
			.map(|k| usages[k])
			.sum();
		used <= capacity
	})
}

/// A domain from `min` to `max`.
const fn i(min: i64, max: i64) -> Domain {
	Domain::Int(min, max)
}

/// Add an integer decision from `min` to `max` to the top layer.
fn int_decision(model: &mut LayeredModel, min: i64, max: i64) -> OwnedValue {
	OwnedValue::Decision(model.add_decision(
		Type::new(TypeBase::FznsoTypeBaseInt).decision(true),
		OwnedValue::IntSet(RangeList::from(min..=max)),
		None,
		false,
		true,
		Vec::new(),
	))
}

/// With `intermediate`, each improving solution is reported, in order.
#[test]
fn intermediate_solutions_improve() {
	let mut model = LayeredModel::default();
	let x = int_decision(&mut model, 0, 3);
	model.set_objective(Some("int_maximize"), x, Vec::new());
	let mut solver = HuubSolver::new();
	solver
		.option_set("intermediate", Value::from_bool(true))
		.unwrap();
	let mut objectives = Vec::new();
	let status = solver.run(
		&model,
		&mut |sol: &HuubSolution| objectives.push(sol.statistic("int_objective").get_int()),
		ignore_messages(),
		dont_interrupt(),
	);
	assert!(matches!(status, Status::Complete));
	assert!(objectives.windows(2).all(|w| w[0] < w[1]), "{objectives:?}");
	assert_eq!(objectives.last(), Some(&3));
}

/// A list of integers.
fn ints(values: &[i64]) -> OwnedValue {
	OwnedValue::List(values.iter().copied().map(OwnedValue::Int).collect())
}

/// A list of values.
fn list(values: &[OwnedValue]) -> OwnedValue {
	OwnedValue::List(values.to_vec())
}

/// A model with a decision of each domain in its permanent base layer.
fn model_of(domains: &[Domain]) -> (LayeredModel, Vec<OwnedValue>) {
	let mut model = LayeredModel::default();
	let decisions = domains
		.iter()
		.map(|domain| match *domain {
			Domain::Bool => OwnedValue::Decision(model.add_decision(
				Type::new(TypeBase::FznsoTypeBaseBool).decision(true),
				OwnedValue::Absent,
				None,
				false,
				true,
				Vec::new(),
			)),
			Domain::Int(min, max) => int_decision(&mut model, min, max),
		})
		.collect();
	(model, decisions)
}

/// Options reject values outside their meaning.
#[test]
fn options_are_checked() {
	let mut solver = HuubSolver::new();
	assert!(solver.option_set("time_limit", (&0_i64).into()).is_err());
	assert!(solver.option_set("time_limit", (&10_i64).into()).is_ok());
	assert_eq!(solver.option_get("time_limit").get_int(), 10);
	assert!(solver.option_set("time_limit", Value::absent()).is_ok());
	assert!(solver.option_set("intermediate", (&1_i64).into()).is_err());
	assert!(solver.option_set("threads", (&2_i64).into()).is_err());
}

/// The base case, and its reified and half-reified forms.
fn reifiable(
	ident: &str,
	domains: &[Domain],
	args: impl Fn(&[OwnedValue]) -> Vec<OwnedValue> + 'static,
	check: impl Fn(&[i64]) -> bool + 'static,
) -> [Case; 3] {
	let base = case(ident, domains, args, check);
	let n = domains.len();
	let mut reified_domains = domains.to_vec();
	reified_domains.push(B);
	let with_reification = |suffix: &str, holds: fn(bool, bool) -> bool| {
		let (args, check) = (Rc::clone(&base.args), Rc::clone(&base.check));
		Case {
			ident: format!("{ident}{suffix}"),
			domains: reified_domains.clone(),
			args: Rc::new(move |d: &[OwnedValue]| {
				let mut a = args(&d[..n]);
				a.push(d[n].clone());
				a
			}),
			check: Rc::new(move |s: &[i64]| holds(check(&s[..n]), s[n] == 1)),
		}
	};
	let reif = with_reification("_reif", |c, r| c == r);
	let imp = with_reification("_imp", |c, r| c || !r);
	[base, reif, imp]
}

/// Retracting a layer with a constraint that its activation literal cannot
/// condition rebuilds the solver.
#[test]
fn retracting_an_unconditioned_constraint_rebuilds() {
	let mut model = LayeredModel::default();
	let x = int_decision(&mut model, 0, 5);
	model.set_objective(Some("int_maximize"), x.clone(), Vec::new());
	let mut solver = HuubSolver::new();
	let _ = best(&mut solver, &model);

	model.set_unchanged(1);
	model.push_layer();
	let _ = model.add_constraint("int_table", vec![list(&[x]), ints(&[2])], None, Vec::new());
	assert!(matches!(
		best(&mut solver, &model),
		(Status::Complete, Some(2))
	));

	model.set_unchanged(2);
	model.pop_layer();
	assert!(matches!(
		best(&mut solver, &model),
		(Status::Complete, Some(5))
	));
	assert_eq!(solver.builds, 2);
}

/// Run `model`, returning every solution reported, with each Boolean as 0 or 1.
fn solutions(solver: &mut HuubSolver, model: &LayeredModel) -> (Status, Vec<Vec<i64>>) {
	let len = model.decision_len();
	let mut found = Vec::new();
	let status = solver.run(
		model,
		&mut |sol: &HuubSolution| {
			found.push(
				(0..len)
					.map(|i| match sol.value(i).view() {
						ValueView::Int(v) => v,
						ValueView::Bool(b) => i64::from(b),
						other => panic!("decision {i} has value {other:?}"),
					})
					.collect(),
			);
		},
		ignore_messages(),
		dont_interrupt(),
	);
	(status, found)
}

/// Whether the successors `s`, numbered from `offset`, form one circuit over
/// the nodes that are not their own successor.
fn subcircuit(s: &[i64], offset: i64) -> bool {
	let distinct = (0..s.len()).all(|a| (a + 1..s.len()).all(|b| s[a] != s[b]));
	let successor = |node: usize| usize::try_from(s[node] - offset).unwrap();
	let visited: Vec<usize> = (0..s.len()).filter(|&k| successor(k) != k).collect();
	let Some(&start) = visited.first() else {
		return distinct;
	};
	let mut node = start;
	for step in 1..=visited.len() {
		node = successor(node);
		if node == start {
			return distinct && step == visited.len();
		}
	}
	false
}

/// Whether each of `values` only occurs in `s` after the value before it.
fn value_precede_chain(values: &[i64], s: &[i64]) -> bool {
	values
		.windows(2)
		.all(|pair| (0..s.len()).all(|j| s[j] != pair[1] || s[..j].contains(&pair[0])))
}
