# Follow-ups for branch 15 — combine-allow-deny (Lean model, proofs, DRT)

## PR description

Proves the allow/deny combination of `cedar` branch 15 decision-preserving
(`combineAllowDeny_decision`, `allowCubes_decision`) for every policy set whose forbids'
conjuncts are boolean-or-error — everything that validates — and adds `combine-lean-drt`, which
compares whole policy sets (ids, effects, scopes, conditions) between Rust and the model.

```lean
theorem combineAllowDeny_decision (ps : Policies) (request : Request) (entities : Entities)
    (hb : ∀ F ∈ ps, F.effect = .forbid → ∀ d ∈ conjuncts F.toExpr, Boolish (evaluate d request entities)) :
  (isAuthorized request entities (combineAllowDeny ps)).decision = (isAuthorized request entities ps).decision
```

## What this branch contains

- `Cedar/DNF/Combine.lean`, `Cedar/Thm/DNF/Combine.lean`, the `combine-lean-drt` target
  (`runCheckCombine`, `CombineCheckRequest`); with it every cedar-spec DNF file (aggregator,
  FFI, proto, fuzz harness, manifest) reaches its source shape.

## Review findings

- The theorem is decision-only, as for the policy split.
- The DRT's skip on a cube-budget error also skips the budget-free combination check.

## Divergences from the private source

- None in content; `cedar-lean-ffi/src/lean_ffi/dnf.rs` stays rustfmt-formatted.

## Suggested follow-ups

- None beyond the Rust side's.
