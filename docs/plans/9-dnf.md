# Plan 9 — The DNF converter: Lean model, proofs and differential test

## Goal

`cedar` branch 9 converts a boolean expression into cubes by linearising the evaluation
decision tree, claiming the result is exact under Cedar's three-valued semantics, that at most
one cube is ever true, that the cubes' order is irrelevant, and that a never-true cube may be
dropped whenever every may-error node on it lies on another cube. This branch turns each claim
into a machine-checked theorem over a Lean model of the converter, and ties the Rust converter
to that model with a differential fuzz target.

## Design

### The model (`Cedar/DNF.lean`)

Module-style, importing only `Cedar.Spec` — the Rust module is independent of the evaluator
too. Definitions mirror `src/dnf` case for case: `Outcome` (`tt | ff | err`) and `interp`
(the three-valued structural semantics over an atom valuation; a valuation is a function, so
purity holds by construction; Lean expressions carry no data, so the Rust "erased key" is the
expression itself); `Literal`, `Leaf`, `Path` with `flipped` and `extended` (append with dedup:
same polarity drops, opposite polarity truncates to a contradiction leaf); `paths` (the same DFS
order as Rust: `not` flips, `and`/`or` graft, `ite` grafts both branches over the test's paths,
anything else is an atom yielding its positive-true and negative-false paths); `Node`,
`Path.nodes` and `prune` with the same covered-set fold; `Cube.toExpr`/`toExpr` (right-nested
chains, `&& false`, `true`/`false` for the empty cases); `dnf e canError`. No cube budget and
no stack check — resource limits, not semantics.

### The theorems (`Cedar/Thm/DNF/{Interp,Extend,Invariant,Master,Pruning,Equivalence}.lean`)

- A valuation-free **pairwise-conflict invariant**: any two distinct real-leaf paths contradict
  on some atom — which yields `dnf_cubes_exclusive` (at most one cube of the DNF is true, in
  any valuation) and, per valuation, the uniqueness the erring-node argument needs.
- The **master invariant** of `paths e`, per valuation, as a trichotomy: on a `tt` input exactly
  one true-leaf path passes and the rest are `ff`; on `ff` every path is `ff`; on `err` no path
  is `tt` and there is an erring node `n` such that every path through `n` errs and every other
  is `ff`.
- **Pruning**: `prune` preserves the disjunction's outcome given only that `canError` is sound
  (an atom answered `false` never errs): a true-leaf path through `n` is always kept, and
  otherwise the first never-true path through `n` finds it uncovered or covered by an earlier
  kept cube that also contains `n`.
- `interp_dnf` — under every three-valued valuation on which the `canError` answers are
  correct, the DNF interprets exactly like the input.
- `evaluate_dnf` / `evaluate_dnfOfExpr` — under the concrete evaluator, the DNF and the input
  produce the same boolean value or both error, for every request and entity store on which the
  `canError` answers are correct (`dnfOfExpr` unconditionally); soundness *and* completeness up
  to the error kind. `interp` agrees with `evaluate` unconditionally (Cedar's `.as Bool`
  coercions collapse ok-non-boolean and error to the same abstract outcome), and the
  boolean-atoms hypothesis — every atom evaluates to a boolean or errors, true for anything
  that validates — appears only when reading the outcome equality back as "same value or both
  error": literal dedup turns `a || a` into `a`, and for `a : Long` the original type-errors
  while the DNF returns the long.
- One modeling assumption: `canError` is a pure function of the atom where Rust's is `FnMut`
  — the theorems cover answerers that depend only on the atom expression, which every intended
  caller satisfies.

### The differential test (`dnf-lean-drt`)

Schema-free (the conversion is syntactic): a generated boolean expression is converted on both
sides under both `can_error` extremes — every atom can error (`Dnf::of_expr`, which keeps exactly
the never-true cubes with an uncovered node) and none can (which drops every never-true cube) —
and the rendered DNFs must be structurally identical after canonicalizing record-field order
(prost encodes map fields in hash order). `DnfCheckRequest {expr, expected, can_error_all}`,
`runCheckDnf` in `CedarFFI/Main.lean`, `run_dnf_check` in `cedar-lean-ffi`, the harness in
`cedar-drt/fuzz/src/dnf.rs`. Fixed cases cover dedup, contradiction truncation, `if` grafting,
never-true-cube coverage (`(a && false) || (e && false)` separates the two extremes) and
record/set atoms; a seeded smoke test runs under `cargo test`.

## Files

- `cedar-lean/Cedar/DNF.lean`, `Cedar/Thm/DNF.lean`, `Cedar/Thm/DNF/{Interp,Extend,Invariant,Master,Pruning,Equivalence}.lean`,
  `Cedar.lean`, `Cedar/Thm.lean`, `CedarFFI/Main.lean`, `CedarProto/DnfCheckRequest.lean`, `CedarProto.lean`.
- `cedar-lean-ffi/protobuf_schema/Messages.proto`, `src/lean_ffi.rs`, `src/lean_ffi/dnf.rs`, `src/messages.rs`.
- `cedar-drt/fuzz/src/dnf.rs`, `fuzz_targets/dnf-lean-drt.rs`, `Cargo.toml`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`, the Lean test suites,
`build_lean_lib.sh`; `cargo test` in `cedar-drt/fuzz`; a live `cargo fuzz run -s none dnf-lean-drt`.

## History

Merged from the private plans "Lean proofs of the DNF conversion" and "DRT for the DNF
converter vs its Lean model". The proof architecture shifted mid-way (a valuation-free conflict
invariant first; the unpruned equivalence as a corollary of the master invariant; six files
instead of four) with the theorem statements unchanged.
