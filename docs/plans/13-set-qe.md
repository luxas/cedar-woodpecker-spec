# Plan 13 — The set quantifier-elimination matrix

## Goal

Policy synthesis (branch 16) takes a conjunction of two set atoms that share a variable —
a set, or the element of a `contains` — existentially quantifies that variable away, and
replaces the pair by one Cedar set operation over the remaining variables:
`(∃a. A.contains(a) && B.contains(a)) ⟺ A.containsAny(B)`;
`(∃X. C.containsAll(X) && X.containsAll(A)) ⟺ C.containsAll(A)`. This branch fixes the
complete case matrix — every pair of the five set operations (`isEmpty`, `==`, `contains`,
`containsAll`, `containsAny`), each possibly negated, with either operand quantified — and, per
cell, a Lean proof that a rewrite is exact, or a proof that no boolean combination of Cedar
atoms over the remaining variables expresses it together with the tightest implied
over-approximation. It is a theory deliverable at the level of set *values*; the bridge to
`Spec.evaluate` belongs to the pass that fixes how the quantified variable arises.

## The matrix

Validated Cedar fixes the types, so the quantified variable is a set `X` in `X.isEmpty()`,
`X == A`, `X.contains(e)`, `A.containsAll(X)` (`X ⊆ A`), `X.containsAll(A)` (`A ⊆ X`),
`X.containsAny(A)`, or an element `x` in `A.contains(x)`. Up to `&&`-symmetry that is 12 set
literals (78 unordered pairs) plus 3 element pairs: **81 cells**, each a theorem
`qe_<left>_<right>` on well-formed `Cedar.Data.Set` values (evaluated sets are well formed).

Some cells depend on how big the element type is; the hypotheses are stated explicitly and
hand-rolled: `Nonempty α`, `TwoElems α` (two distinct elements; `Bool` has them, a one-member
enum type does not), `Unbounded α` (every finite set misses some element: strings and entity
types, not `Bool`/`Long`/the extension types). For such a cell the `⇒` direction — the
`_over` lemma — holds unconditionally; exactness needs the hypothesis.

Shapes of the results: the `X == A` row is substitution and the `X.isEmpty()` row is constant
or `A.isEmpty()`; the exact single-operation cells include `A.containsAll(X) && X.containsAll(B)
⇒ A.containsAll(B)`, `A.containsAll(X) && X.containsAny(B) ⇒ A.containsAny(B)`,
`X.contains(e) && A.containsAll(X) ⇒ A.contains(e)`, `A.contains(x) && B.contains(x) ⇒
A.containsAny(B)`, `A.contains(x) && !B.contains(x) ⇒ !B.containsAll(A)`,
`X.contains(e) && !X.contains(f) ⇒ e != f`, and many cells are `!A.isEmpty()`. Three cells are
**not expressible** by any boolean combination of the Cedar atoms over the free variables,
proved by a distinguishing pair (two instances with the same atom vector and different targets):
`!X.containsAll(A) && X.containsAny(B)` (over-approximation `!A.isEmpty() && !B.isEmpty()`) and
`X.contains(e) && !X.containsAll(A)` / `!X.contains(e) && X.containsAny(A)` (exact with a
literal, `![e].containsAll(A)`; literal-free over-approximation `!A.isEmpty()`). The
over-approximations are tight in the atom language.

## Design

One file, `Cedar/Thm/DNF/SetQE.lean`, whose module doc carries the full table as the source of
truth next to the proofs. Cedar atoms are the model's `Bool` functions exactly as
`Spec.apply₁/apply₂` use them (`isEmpty`, `==` via `DecidableEq`, `contains`, `subset`,
`intersects`), stated with `= true` so each cell reads as the Cedar rewrite; a characterization
layer turns each atom into membership first. Inexpressibility is stated against the atom vector
of the free variables.

## Files

- `cedar-lean/Cedar/Thm/DNF/SetQE.lean` (new), `Cedar/Thm/DNF.lean`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`. The golden tests of the
policy-synthesis crate (branch 16) were cross-checked against this table cell by cell.

## History

Merged from the private plan "the set quantifier-elimination matrix"; no Rust pass exists yet.
