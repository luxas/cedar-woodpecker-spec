# Follow-ups for branch 5 — symbolic-evaluator (differential tests, Lean model, proofs)

## PR description

Backs the symbolic evaluator of `cedar` branch 5 with evidence: three fuzz targets compare it
against the concrete evaluator (closed and open stores) and against TPE; a Lean model of the
evaluator is proved sound — the concrete outcome is always in the reported set, and the folded
expression evaluates like the input — for any solver whose "unsatisfiable" answers are correct;
and a replay target feeds every recorded Rust solver query through the model, so the Rust
evaluator is checked against the proved model query by query.

```sh
cd cedar-drt/fuzz
cargo test symeval                                   # fixed cases + seeded smoke tests
cargo fuzz run -s none symcc-evaluator-lean-drt -- -len_control=0 -max_len=4096
```

```lean
theorem symEvaluate_sound … (hu : UnsatSound unsat? εnv) (hI : ExistsTrue I) … :
  outcomeOf (evaluate x request entities) ∈ r.outcomes ∧
  (evaluate r.toExpr request entities).toOption = (evaluate x request entities).toOption
```

## What this branch contains

- `cedar-drt/fuzz/src/symeval.rs` and the targets `symcc-evaluator-{concrete,open,tpe,lean}-drt`.
- `Cedar/SymCCOpt/SymEval.lean` (the model: existence questions, phantom values, kept guards
  included), `Cedar/Thm/SymCC/Evaluator/{Outcomes,Tree,Soundness}.lean`, `SymTest/SymEval.lean`,
  the replay FFI entry (`runSymEvalReplay`, `SymEvalReplayRequest`).

## Review findings

- Every theorem carries `ExistsTrue I` and keeps the closed-store statement; the open-store
  guarantee that `symcc-evaluator-open-drt` tests is *not* proved. The theorem names do not say
  so; a docstring per theorem would prevent over-reading.
- Completeness (C) is not proved; the proved entry point enforces the hierarchy over expression
  footprints while Rust enforces over all atoms' footprints (a superset).
- `Soundness.lean` is ~2.2k lines in one file with a large `facts_mem` structural recursion
  (nested inductive `SENode`); splitting per constructor family would help review.
- `lake build` reports Lean linter warnings in `Tree.lean` and `Soundness.lean` (unused `simp`
  arguments, a `<;>` where `;` suffices); CI does not fail on them.
- `symeval.rs`'s module doc says the Lean model is not involved — stale since the replay was
  added; the source text is kept.
- `cedar-drt/README.md` has rows for the concrete, TPE and Lean targets but none for the open
  target.
- The replay canonicalizes record fields on the Lean side because prost encodes `HashMap` map
  fields in random order; a deterministic encoder in `cedar-lean-ffi` would remove the need.

## Divergences from the private source

- `symeval.rs:24`: the pointer to the private plan file now names `docs/plans/5-symbolic-evaluator.md`.
- Lean docstrings cite the kept-guard rule as "plan 5" instead of the private plan number.

## Suggested follow-ups

- The open-store theorem; completeness; the deterministic proto encoder; the README row.
