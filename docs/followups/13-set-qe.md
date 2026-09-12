# Follow-ups for branch 13 — set-qe

## PR description

Proves, cell by cell, what two conjoined Cedar set atoms that share an existentially quantified
set or element are equivalent to over the remaining variables — the 81-cell matrix policy
synthesis (branch 16) uses to eliminate an intermediate request's sets — with explicit domain
hypotheses where a cell needs them, and inexpressibility proofs (plus tight over-approximations)
for the three cells no Cedar atom combination can state.

```lean
/-- ∃X. A.containsAll(X) && X.containsAll(B)  ⟺  A.containsAll(B) -/
theorem qe_sub_sup {A B : Set α} (hA : A.WellFormed) (hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = true ∧ B.subset X = true) ↔ B.subset A = true
```

## What this branch contains

- `Cedar/Thm/DNF/SetQE.lean` (the matrix, `Unbounded`/`TwoElems`, the `_over` lemmas, the
  inexpressibility results), its entry in `Cedar/Thm/DNF.lean`.

## Review findings

- The matrix is on values, not on `Spec.evaluate`; the bridge waits for the pass that fixes
  what the quantified variable is. Until then the theorems document `cedar-woodpecker`'s
  `sets.rs`, whose golden tests were cross-checked by hand.
- 1.4k lines of near-identical cell proofs; a tactic or a finite-abstraction enumeration would
  shrink the file and make adding a cell mechanical.
- Inexpressibility is proved against a fixed atom vector; a richer atom set (a new Cedar
  operation) would need the proofs redone — say so in the module doc.

## Divergences from the private source

- The module doc cites this branch's plan number instead of the private one.

## Suggested follow-ups

- The `evaluate` bridge; proof automation for the cells.
