//! What the library declares: the constraints it posts natively, the types of
//! decision it can hold, and the objectives, options, and statistics it
//! understands.
//!
//! The declared constraints are the entire negotiation with an application,
//! which adapts its model to them. A constraint is therefore only declared when
//! Huub has a propagator or an encoding for it, and every name is spelled as in
//! the registry, with an argument narrowed from a decision to a fixed value
//! only where Huub cannot take a decision.

/// Declare a constraint with the given argument types.
macro_rules! constraint {
	($ident:literal, [$($arg:expr),* $(,)?]) => {
		ConstraintType {
			ident: Str::new($ident),
			arg_len: [$($arg),*].len(),
			arg_types: {
				const ARGS: &[Type] = &[$($arg),*];
				ARGS.as_ptr()
			},
			lifetime: PhantomData,
		}
	};
}

/// Declare a statistic, and where it can be read.
macro_rules! statistic {
	($ident:literal, $ty:expr, solution: $solution:literal, solver: $solver:literal) => {
		Statistic {
			ident: Str::new($ident),
			ty: $ty,
			solution: $solution,
			solver: $solver,
			lifetime: PhantomData,
		}
	};
}

use std::marker::PhantomData;

use fznso::{
	ConstraintList, ConstraintType, Objective, ObjectiveList, OptionDef, OptionList, Statistic,
	StatisticList, Str, Type, TypeBase, TypeList, Value,
};

/// A list of fixed integers.
const AI: Type = I.list(true);
/// A list of Boolean decisions.
const AVB: Type = VB.list(true);
/// A list of integer decisions.
const AVI: Type = VI.list(true);

/// A fixed Boolean.
const B: Type = Type::new(TypeBase::FznsoTypeBaseBool);

/// The list of [`CONSTRAINTS`], as the entry point returns it.
pub(crate) const CONSTRAINT_LIST: ConstraintList<'static> = ConstraintList {
	len: CONSTRAINTS.len(),
	constraints: CONSTRAINTS.as_ptr(),
	lifetime: PhantomData,
};

/// The constraints the library posts.
///
/// Not declared, because Huub only has a decomposition for them, which belongs
/// in the application's library rather than here: `int_regular` (encoded as
/// tables) and `int_mod`. Not declared, because Huub has no propagator that
/// takes a decision literal: the half-reified form of anything other than a
/// linear constraint, a clause, a parity constraint, and `int_in`, and the
/// reified form of any global constraint. `int_disjunctive` is not declared,
/// because Huub only separates zero-duration tasks strictly.
pub(crate) const CONSTRAINTS: &[ConstraintType<'static>] = &[
	constraint!("bool_array_and", [AVB, VB]),
	constraint!("bool_array_element", [AVB, I, VI, VB]),
	constraint!("bool_array_xor", [AVB]),
	constraint!("bool_array_xor_imp", [AVB, VB]),
	constraint!("bool_array_xor_reif", [AVB, VB]),
	constraint!("bool_clause", [AVB, AVB]),
	constraint!("bool_clause_imp", [AVB, AVB, VB]),
	constraint!("bool_clause_reif", [AVB, AVB, VB]),
	constraint!("bool_lin_eq", [AI, AVB, VI]),
	constraint!("bool_lin_le", [AI, AVB, I]),
	constraint!("bool_lin_le_imp", [AI, AVB, I, VB]),
	constraint!("bool_lin_le_reif", [AI, AVB, I, VB]),
	constraint!("bool_lin_ne", [AI, AVB, VI]),
	constraint!("bool_lin_ne_imp", [AI, AVB, VI, VB]),
	constraint!("bool_lin_ne_reif", [AI, AVB, VI, VB]),
	constraint!("bool_to_int", [VB, VI]),
	constraint!("int_abs", [VI, VI]),
	constraint!("int_all_different", [AVI]),
	constraint!("int_array_element", [AVI, I, VI, VI]),
	constraint!("int_array_maximum", [AVI, VI]),
	constraint!("int_array_minimum", [AVI, VI]),
	constraint!("int_circuit", [AVI, I]),
	constraint!("int_cumulative", [AVI, AVI, AVI, VI]),
	constraint!("int_disjunctive_strict", [AVI, AI]),
	constraint!("int_div", [VI, VI, VI]),
	constraint!("int_in", [VI, SI]),
	constraint!("int_in_imp", [VI, SI, VB]),
	constraint!("int_in_reif", [VI, SI, VB]),
	constraint!("int_lin_eq", [AI, AVI, I]),
	constraint!("int_lin_eq_imp", [AI, AVI, I, VB]),
	constraint!("int_lin_eq_reif", [AI, AVI, I, VB]),
	constraint!("int_lin_le", [AI, AVI, I]),
	constraint!("int_lin_le_imp", [AI, AVI, I, VB]),
	constraint!("int_lin_le_reif", [AI, AVI, I, VB]),
	constraint!("int_lin_ne", [AI, AVI, I]),
	constraint!("int_lin_ne_imp", [AI, AVI, I, VB]),
	constraint!("int_lin_ne_reif", [AI, AVI, I, VB]),
	constraint!("int_no_overlap", [AVI, AVI, AVI, AVI]),
	constraint!("int_no_overlap_nd", [I, AVI, AVI]),
	constraint!("int_no_overlap_nd_nonstrict", [I, AVI, AVI]),
	constraint!("int_no_overlap_nonstrict", [AVI, AVI, AVI, AVI]),
	constraint!("int_pow", [VI, VI, VI]),
	constraint!("int_seq_precede_chain", [AVI]),
	constraint!("int_subcircuit", [AVI, I]),
	constraint!("int_table", [AVI, AI]),
	constraint!("int_times", [VI, VI, VI]),
	constraint!("int_value_precede", [I, I, AVI]),
	constraint!("int_value_precede_chain", [AI, AVI]),
];

/// The list of [`DECISIONS`], as the entry point returns it.
pub(crate) const DECISION_LIST: TypeList<'static> = TypeList {
	len: DECISIONS.len(),
	types: DECISIONS.as_ptr(),
	lifetime: PhantomData,
};

/// The types of decision the library can hold.
const DECISIONS: &[Type] = &[VB, VI];
/// A fixed float.
const F: Type = Type::new(TypeBase::FznsoTypeBaseFloat);
/// A fixed integer.
const I: Type = Type::new(TypeBase::FznsoTypeBaseInt);

/// The list of [`OBJECTIVES`], as the entry point returns it.
pub(crate) const OBJECTIVE_LIST: ObjectiveList<'static> = ObjectiveList {
	len: OBJECTIVES.len(),
	objectives: OBJECTIVES.as_ptr(),
	lifetime: PhantomData,
};

/// The objectives the library can optimise.
const OBJECTIVES: &[Objective<'static>] = &[
	Objective {
		ident: Str::new("int_maximize"),
		arg_type: VI,
		lifetime: PhantomData,
	},
	Objective {
		ident: Str::new("int_minimize"),
		arg_type: VI,
		lifetime: PhantomData,
	},
];

/// The list of [`OPTIONS`], as the entry point returns it.
pub(crate) const OPTION_LIST: OptionList<'static> = OptionList {
	len: OPTIONS.len(),
	options: OPTIONS.as_ptr(),
	lifetime: PhantomData,
};

/// The options the library accepts.
///
/// Huub searches on a single thread, and has no random choices to seed, so
/// neither `threads` nor `random_seed` is declared.
const OPTIONS: &[OptionDef<'static>] = &[
	OptionDef {
		ident: Str::new("all_solutions"),
		arg_ty: B,
		arg_def: Value::from_bool(false),
		lifetime: PhantomData,
	},
	OptionDef {
		ident: Str::new("fixed_search"),
		arg_ty: B,
		arg_def: Value::from_bool(false),
		lifetime: PhantomData,
	},
	OptionDef {
		ident: Str::new("intermediate"),
		arg_ty: B,
		arg_def: Value::from_bool(false),
		lifetime: PhantomData,
	},
	OptionDef {
		ident: Str::new("time_limit"),
		arg_ty: I.opt(true),
		arg_def: Value::absent(),
		lifetime: PhantomData,
	},
];
/// A fixed set of integers.
const SI: Type = I.set(true);

/// The list of [`STATISTICS`], as the entry point returns it.
pub(crate) const STATISTIC_LIST: StatisticList<'static> = StatisticList {
	len: STATISTICS.len(),
	stats: STATISTICS.as_ptr(),
	lifetime: PhantomData,
};

/// The statistics the library reports.
///
/// The `huub_` statistics are the counters Huub keeps that the registry has no
/// name for.
const STATISTICS: &[Statistic<'static>] = &[
	statistic!("bool_decisions", I, solution: false, solver: true),
	statistic!("failures", I, solution: false, solver: true),
	statistic!("huub_eager_literals", I, solution: false, solver: true),
	statistic!("huub_lazy_literals", I, solution: false, solver: true),
	statistic!("huub_sat_search_directives", I, solution: false, solver: true),
	statistic!("huub_user_search_directives", I, solution: false, solver: true),
	statistic!("init_time", F, solution: false, solver: true),
	statistic!("int_decisions", I, solution: false, solver: true),
	statistic!("int_objective", I, solution: true, solver: false),
	statistic!("peak_depth", I, solution: false, solver: true),
	statistic!("propagations", I, solution: false, solver: true),
	statistic!("propagators", I, solution: false, solver: true),
	statistic!("restarts", I, solution: false, solver: true),
	statistic!("solutions", I, solution: true, solver: true),
	statistic!("solve_time", F, solution: false, solver: true),
];
/// A Boolean decision.
const VB: Type = B.decision(true);
/// An integer decision.
const VI: Type = I.decision(true);
