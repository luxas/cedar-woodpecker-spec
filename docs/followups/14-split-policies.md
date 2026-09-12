# Follow-ups for branch 14 — split-policies (Lean model, proofs, DRT)

## PR description

Proves the policy split of `cedar` branch 14 decision-preserving: `splitPolicySet_decision`
states that replacing every policy of a set by its cube policies leaves `isAuthorized`'s
decision unchanged on every request and entity store (under the typing hypothesis the
normalization needs); and `split-policies-lean-drt` compares the Rust split's cube conditions
with the model's.

```lean
theorem splitPolicySet_decision (ps : Policies) (request : Request) (entities : Entities)
    (ht : ∀ p ∈ ps, TypedPolicy p request entities) :
  (isAuthorized request entities (splitPolicySet ps)).decision
    = (isAuthorized request entities ps).decision
```

## What this branch contains

- `Cedar/DNF/SplitPolicy.lean`, `Cedar/Thm/DNF/{SplitCond,SplitPolicyThm}.lean`, the
  `split-policies-lean-drt` target (`runCheckSplitPolicy`, `SplitPolicyCheckRequest`).

## Review findings

- The theorem is decision-only; `Response`'s determining/erroring policies are unclaimed.
- The DRT compares cube conditions in order; scope/effect/id copying is covered only by the
  Rust tests.

## Divergences from the private source

- None.

## Suggested follow-ups

- A diagnostics-aware theorem.
