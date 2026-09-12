# Follow-ups for branch 11 — rewrite-like (Lean proofs, DRT)

## PR description

Proves the like rewrite of `cedar` branch 11 sound and complete: a structural characterization
of Cedar's memoized `wildcardMatch`, `evaluate_rewriteLike` (the rewrite preserves evaluation
where the operand is a string or errors), `rewriteLike_complete` and `rewriteLike_matches_two`
(every remaining `like` is matched by at least two strings); and a fuzz target comparing the
Rust rewrite with the model.

```lean
theorem wildcardMatch_eq_matchB (s : String) (p : Pattern) :
  wildcardMatch s p = matchB s.toList p
```

## What this branch contains

- `Cedar/DNF/Like.lean`, `Cedar/Thm/DNF/{Wildcard,Like}.lean`, the `like-lean-drt` target.

## Review findings

- `Wildcard.lean` must `import all Cedar.Spec.Wildcard` to see the private memoization helpers;
  a public structural characterization in `Cedar/Spec/Wildcard.lean` itself would be cleaner.
- The soundness hypothesis is again not connected to `typeOf`.

## Divergences from the private source

- None.

## Suggested follow-ups

- A public `wildcardMatch` characterization in the spec.
