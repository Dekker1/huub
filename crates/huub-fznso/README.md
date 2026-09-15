# huub-fznso

Huub, the lazy clause generation solver, as an FZnSO solver library.

The crate builds `libhuub`, which exports the FZnSO entry points under the name
`huub`. It is written against the Rust bindings in `rust/fznso` of the FZnSO
repository, and depends on them by path from outside their workspace.

```sh
cargo build -p huub-fznso --profile fznso   # target/fznso/libhuub.dylib
cargo test -p huub-fznso
```

The `fznso` profile is the release profile with `panic = "unwind"`: a panic in
the solver is reported to the application as an error, which only works when
it can unwind to the entry point. Huub's release profile aborts instead.

## How a model is posted

The application's model is read through the interface and posted straight into
Huub; nothing of it is kept beyond the solver.

One Huub solver is kept from run to run. The layers the application marks
permanent are posted into one Huub model, simplified together, and lowered into
a new solver. Every other layer is posted into a model of its own and lowered
into the existing solver with `Lowerer::extend_solver`: a decision of an earlier
layer is bound to the solver view that already stands for it.

A layer that can be retracted is conditioned on an *activation* literal, which
the run assumes. Retracting the layer adds its negation as a clause, so the
solver keeps everything it learned, and a clause learned from the layer is
simply satisfied. A layer that becomes permanent has its activation literal
fixed instead.

Only a linear constraint, a clause, a parity constraint, and set membership can
be conditioned: Huub has no global propagator that takes a literal. A global
constraint in a retractable layer is posted unconditionally, and retracting that
layer rebuilds the solver from the model. So does enumerating solutions, whose
nogoods are permanent.

## What is declared

Decision types `var bool` and `var int`; objectives `int_minimize` and
`int_maximize`; options `all_solutions`, `fixed_search`, `intermediate`, and
`time_limit`.

Constraints, by their registry names:

- `int_lin_eq`, `int_lin_le`, `int_lin_ne`, `bool_lin_le`, `bool_lin_ne`,
  `bool_clause`, and `bool_array_xor`, with their `_reif` and `_imp` forms;
- `int_in` with `_reif` and `_imp`;
- `bool_lin_eq`, `bool_array_and`, `bool_to_int`, `int_abs`, `int_times`,
  `int_div`, `int_pow`, `int_array_element`, `bool_array_element`,
  `int_array_maximum`, and `int_array_minimum`;
- `int_all_different`, `int_table`, `int_circuit`, `int_subcircuit`,
  `int_cumulative`, `int_disjunctive_strict` (with fixed durations),
  `int_no_overlap`, `int_no_overlap_nonstrict`, `int_no_overlap_nd`,
  `int_no_overlap_nd_nonstrict`, `int_seq_precede_chain`,
  `int_value_precede_chain`, and `int_value_precede`.

Not declared: `int_regular` and `int_mod`, which Huub only decomposes;
`int_array_element_nd` and `bool_array_element_nd`, which promise every number
of dimensions; `int_disjunctive`, because Huub only separates zero-duration
tasks strictly; and the reified form of any global constraint. Huub has no float
or set decisions.

## MiniZinc library

`mznlib/` holds the decompositions MiniZinc's FZnSO library cannot provide,
because the registry backs them with a FlatZinc builtin and gives them no body:

- `fzn_int_mod.mzn`: the remainder of truncating division, as Huub's own library
  states it;
- `fzn_int_array_element_nd.mzn` and `fzn_bool_array_element_nd.mzn`: the
  row-major index as one linear sum, onto the one-dimensional element. Each
  index is also kept inside its own dimension, which the flat index alone does
  not do: Gecode's version of this file accepts an index past the end of one
  dimension that the next one makes up for.

Every identifier in them is a registry name Huub declares, so none is rewritten
back onto the predicate that uses it.

`cargo run -p fznso-conform -- check target/fznso/libhuub.dylib` passes: all 48
constraints are registry names whose argument types narrow the registry's, and
the four statistics the registry does not name are prefixed `huub_`.

Every declared constraint is tested against its registry definition by
enumerating every solution of a small model and comparing it with a brute-force
enumeration, both in the permanent base layer and in a retractable layer, which
is then retracted.

## What this backend found

In Huub, fixed on this branch:

- **A search left its solution assigned.** After `solve`, the engine stayed at
  the decision level of the last solution, so anything posted afterwards read the
  solution as facts of the problem. A propagator's `post` removes the terms it
  sees as fixed, so a constraint posted after a run could be weakened.
  `Solver::at_root` now returns a wrapper that rewinds the trail to the root,
  restorably, as an explanation does, and redoes it when dropped. Posting after
  a search goes through it, as `Lowerer::extend_solver` does; the search
  itself is untouched.
- **`value_precede(..).values(v)` removed `v[0]` from the first decision**, not
  just the values after it, so `[3, 0, 0]` was rejected for the chain `[3, 1,
  2]`. Huub's own FlatZinc frontend reaches this through
  `huub_value_precede_chain_int`.
- **Edge finding in the strict disjunctive did not terminate** with a
  zero-duration task: a gray task is found by its gray duration, so one without
  could never be removed from the tree.

In Huub, not fixed: with edge finding disabled, the strict disjunctive's
overload checking accepts a zero-duration task inside another task. The
default, and this backend, enable edge finding.

In Huub, not fixed: a linear constraint over decisions whose domain reaches
`i64::MIN` overflows in `views/linear_view.rs`, which the release build wraps
silently. An unbounded `var int` gets that domain, so `regression/bug282` and
`regression/bug318_orig` come back unsatisfiable. Huub's own frontend avoids
it there by turning the equality into a view. `regression/bug222` panics on an
overflowing division inside propagation, where a panic cannot unwind through
CaDiCaL's frames, so it aborts despite the `fznso` profile.

In the interface:

- MiniZinc handed a constraint to the solver as `fzn_<ident>` at run time, not
  only when writing FlatZinc. Fixed in `FznsoModel::constraint_ident`, which now
  strips the prefix; this backend no longer does.
- The registry's note on `int_pow` called a negative exponent undefined for any
  base other than 1 and -1. MiniZinc and Huub truncate: `2^-1 = 0`, and only
  `0^-1` is undefined. The registry now says so.
- Negation reaches the solver as a two-element `bool_array_xor`. Unguarded and
  unreified, it is posted as a view, one literal the negation of the other.

## Where it stands

Measured on MiniZinc's `tests/spec/unit` (1095 models) with the scripts in the
FZnSO repository, against Huub's own MiniZinc integration built from this
branch (`cargo xtask stage`, passed as `EXTRA_SOLVER_PATH`/`REF`):

- **Compilation:** 27 models only the FZnSO path fails to compile. 26 use
  floats, which Huub's frontend compiles but cannot solve; the other is
  `compilation/aggregation.mzn`, which redefines a builtin on purpose.
- **Constraints:** 41 models decompose further, 722 are equal, 68 need fewer,
  264 skipped; 17131 constraints against 16863, a net of +268. The bulk is
  negation, which reaches the solver as a two-element `bool_array_xor` because
  the registry has no `bool_not` (36 of them in
  `regression/cardinality_atmost_partition`), and `regular`, which Huub's own
  library hands to `huub_regular`. Half-reification does reach the solver: a
  model of seven half-reified constraints compiles to 15 constraints, among
  them `int_lin_le_imp`, `int_lin_ne_imp`, `int_lin_eq_imp`, and `int_in_imp`,
  against 16 natively.
- **Solutions:** against native Huub, 728 identical, 100 equivalent, 4
  differing (`general/test_same`, floats on both sides; the three
  full-domain models above). Against Gecode through FZnSO, 640 identical, 206
  equivalent, 22 differing: the same four, `on_restart`, blackbox and float
  models, and `general/test_set_lt_3`, where this backend gives the answer the
  test expects.
- **Semantics:** `scripts/check-semantics.sh`, 211 passed, 13 differing: 6 use
  floats, 4 are an integer overflow in the reference, and 3 are ties
  (`lex_lesseq`, `ite var 2br`, `value_precede_chain`) with the same objective.
