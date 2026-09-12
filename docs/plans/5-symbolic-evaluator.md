# Plan 5 — The symbolic evaluator: differential tests, Lean model and soundness proofs

## Goal

`cedar` branch 5 adds a symbolic evaluator that annotates a boolean expression with the exact
outcomes (`True`, `False`, `Error`) it can produce under assumptions, folding what is
determined. This branch makes that claim checkable: three Rust-versus-Rust differential fuzz
targets, a Lean model of the evaluator over an abstract unsat oracle, machine-checked soundness
theorems for the model, and a replay target that runs a recorded Rust evaluation — every solver
query with its answer — through the model and fails at the first divergence.

## Design

### Differential tests (`cedar-drt/fuzz/src/symeval.rs`)

- `symcc-evaluator-concrete-drt`: a schema, a *complete* entity store, a request and a boolean
  expression from the type-directed generators; the whole store and request are assumed, so the
  result must fold to exactly the concrete outcome (`{o}` for the concrete `o`), and the result
  must be solver-equivalent to the input (`check_equivalent`). Only strongly well-formed inputs
  (every referenced entity present, the hierarchy acyclic and transitive) — the Lean envelope.
- `symcc-evaluator-open-drt`: the same oracle without the existence filter — the request, the
  expression or the entity data may reference entities that are not in the store: the concrete
  outcome must be in the symbolic set, and the folded result must evaluate like the input up
  to the error kind, checked concretely.
- `symcc-evaluator-tpe-drt`: TPE on partial data; for every policy TPE produces a residual for,
  the symbolic outcome set is a subset of the residual's `possible_bool_outcomes`, and both the
  residual and the symbolic result are solver-equivalent to the policy condition on every
  completion of the data (unless the residual contains an error node, which SymCC cannot
  express). Linked template policies are skipped (SymCC does not compile slots).
- A shared solver process per target; timeouts as skips; seeded smoke tests run under
  `cargo test` so CI covers the plumbing.

### The Lean model (`Cedar/SymCCOpt/SymEval.lean`)

`Cedar.SymCC.Opt.SymEval` mirrors the Rust evaluator case for case, using the Opt per-node
compilers so that node terms are bit-identical to Rust's: `buildTree` (children built eagerly,
atoms carrying their existence checks, facts for the true and the false case, and the `keep`
flag of a guard), `atomOutcomes` (the three questions, then `addMissing` for the existence
questions), `evalNode` with the same trail gating and result combination, `symEvalWithBase`
(assumptions shipped as a base assert list) and `symEvaluate` (assumption expressions compiled
and the hierarchy enforced by the model itself), and `checkEquivalent`. The oracle is
`unsat? : Asserts → m Bool` and the evaluator is monad-parametric: `Id` for the theorems, a
state monad over the recorded queries for the replay, `SolverM` for the cvc5 unit tests
(`SymTest/SymEval.lean`).

### The theorems (`Cedar/Thm/SymCC/Evaluator/{Outcomes,Tree,Soundness}.lean`)

For an oracle whose `unsat? = true` answers are correct (`UnsatSound`) and an interpretation
that reads `exists[E]` as true everywhere (`ExistsTrue I`):

- `evalNode_sound` / `symEvalWithBase_sound` — (S1) the concrete outcome is in every visited
  node's outcome set relative to its trail, and (S2) the folded expression evaluates like the
  input up to the error kind, for every well-formed interpretation satisfying the base;
- `symEvaluate_sound` — the same for the entry point that compiles the assumptions and
  enforces the hierarchy itself, over every strongly well-formed input on which the assumptions
  hold;
- `checkEquivalent_sound` — a `true` verdict really is (S2).

The statements keep their closed-store hypotheses: the existence questions only add outcomes,
and the facts hold under any interpretation reading `exists[E]` as true. The open-store
guarantee is tested by the open DRT, not proved (SymCC's bisimulation excludes
`entityDoesNotExist`); completeness is not proved; the proved entry point enforces the
hierarchy over expression footprints while Rust enforces over all atoms' footprints (a
superset). `SENode` is a nested inductive, so the proofs go by induction on a size bound with
per-constructor characterizations at `m := Id`.

### The replay target (`symcc-evaluator-lean-drt`)

Rust records the base asserts, every query (full assert list + answer), the folded result, its
root outcome set and the `check_equivalent` verdict (`EvaluationTrace`); the proto
`SymEvalReplayRequest` carries it through `runSymEvalReplay` in `CedarFFI/Main.lean`, where the
replay oracle checks each popped query's asserts match the model's (the mismatch index is the
signal), then compares the folded expression and outcomes and re-runs `checkEquivalent`. Record
fields of the replayed expression are canonicalized on the Lean side first, since prost encodes
map fields in hash order.

## Files

- `cedar-drt/fuzz/src/symeval.rs`, `fuzz_targets/symcc-evaluator-{concrete,open,tpe,lean}-drt.rs`,
  `cedar-drt/fuzz/Cargo.toml`, `cedar-drt/README.md`.
- `cedar-lean/Cedar/SymCCOpt/SymEval.lean`, `Cedar/Thm/SymCC/Evaluator{,/Outcomes,/Tree,/Soundness}.lean`,
  `SymTest/SymEval.lean`, `CedarFFI/Main.lean`, `CedarProto/SymEvalReplayRequest.lean`.
- `cedar-lean-ffi/protobuf_schema/Messages.proto`, `src/lean_ffi/symeval.rs`, `src/messages.rs`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`, `lake exe CedarSymTests`
with cvc5; `cargo test` in `cedar-drt/fuzz` (fixed cases and seeded smoke tests of all four
targets); live fuzzing with `-len_control=0 -max_len=4096`, since the generator-based inputs
need hundreds of bytes.

## History

Merged from the private plans "the symbolic evaluator" (its DRT part), "formally verify the
symbolic evaluator in Lean" and "entity existence" (its model, open-store DRT and phantom-value
revisions), plus the kept-guard model change. The Rust side is `cedar` branch 5.
