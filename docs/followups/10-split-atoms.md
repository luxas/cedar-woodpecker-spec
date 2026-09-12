# Follow-ups for branch 10 — split-atoms (Lean model, proofs, DRT)

## PR description

Proves the atom splitter of `cedar` branch 10 exact: `evaluate (splitAtoms e) = evaluate e` for
every expression, request and entity store — no hypotheses, error identity included — plus the
cleanliness of its output and the `iferror` table the allow/deny combination will rely on; and
a fuzz target that runs the Rust splitter and the model on the same generated expressions and
compares the results.

```lean
theorem evaluate_splitAtoms (e : Expr) (request : Request) (entities : Entities) :
  evaluate (splitAtoms e) request entities = evaluate e request entities
```

```sh
(cd cedar-drt/fuzz && cargo fuzz run -s none split-atoms-lean-drt)
```

## What this branch contains

- `Cedar/DNF/Split.lean`, `Cedar/Thm/DNF/{SplitEquiv,HoistSpec,SplitSound,IfError}.lean`, the
  `split-atoms-lean-drt` target (`runCheckSplit`, `SplitCheckRequest`).

## Review findings

- `IfError.lean` is filed under `Thm/DNF` although it is a property of the spec's `iferror`
  (branch 4); it lives here because it reasons with the split equivalence algebra.
- `SplitSound.lean` (~900 lines) and `SplitEquiv.lean` (~770) carry the guard proofs and the
  context/dedupe machinery in one place; a file per rule family would ease review.
- `lake build` reports Lean linter warnings in the new files (unused `simp` arguments); CI does
  not fail on them.
- The model has no budget and no stack check; the DRT skips `TooLarge`/`RecursionLimit` as
  benign, so the budget arithmetic is tested only by `tests/dnf.rs` on the Rust side.

## Divergences from the private source

- `cedar-drt/fuzz/src/dnf.rs`: the split harness's invariant-breach arm matches on
  `DnfError::Unsupported` alone until branch 12 adds the typing variants; the comment cites the
  reverted opaque-equality experiment by description.

## Suggested follow-ups

- Move the `iferror` table next to the spec; split the proof files.
