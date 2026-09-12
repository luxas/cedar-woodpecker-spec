# Plan 14 — The policy splitter: Lean model, the decision theorem, differential test

## Goal

`cedar` branch 14 replaces every policy of a set by one policy per true-cube of its condition
and claims the authorization decision is preserved. This branch proves it: a policy is
satisfied exactly when one of its split policies is (and never more than one), and since the
decision depends only on which policies are satisfied, replacing every policy by its split
preserves the decision on every input — the goal theorem of the DNF development.

## Design

- **Model** (`Cedar/DNF/SplitPolicy.lean`): `splitCondExprs c = (prune (paths (normalize c))
  (fun _ => false)).map Cube.toExpr` — the Rust pipeline with `can_error ≡ false`, which keeps
  exactly the true-leaf paths in DFS order; `splitPolicy p` = one `Spec.Policy` per cube, id
  `{id}.cube{i}`, same effect and scopes, the cube as the sole `when` condition (`List.mapIdx`);
  `splitPolicySet = flatMap splitPolicy`. No budgets.
- **The cube-satisfaction lemma** (`Cedar/Thm/DNF/SplitCond.lean`): `cond_satisfied_iff` —
  `evaluate c = .ok true ⟺ ∃ cond ∈ splitCondExprs c, evaluate cond = .ok true` — and
  `cond_satisfied_unique`, both under `TypedPolicy`'s condition hypothesis for the normalized
  condition (branch 12's `Typed`), through `evaluate_normalize`, the master invariant and
  `dnf_cubes_exclusive`; everything lands on `outcome = .tt`, which `outcome_tt_inv` turns into
  `.ok true` with no side conditions.
- **The policy theorems** (`Cedar/Thm/DNF/SplitPolicyThm.lean`): `evaluate_and_ok_true` (the
  scope-threading primitive), `splitPolicy_spec`/`splitPolicy_complete` (effect, the three
  scopes, the condition being a cube), `policy_satisfied_iff`, `policy_satisfied_unique`,
  `satisfiedPolicies_split_isEmpty` per effect (via `Set.isEmpty_make` and
  `List.filterMap_eq_nil_iff`), and `splitPolicySet_decision`:
  `(isAuthorized req es (splitPolicySet ps)).decision = (isAuthorized req es ps).decision`,
  since the decision is a function of the two `isEmpty` flags alone. The `determiningPolicies`
  and `erroringPolicies` fields are not claimed equal (ids differ; erroring cubes differ).
- **The differential test** (`split-policies-lean-drt`): `SplitPolicyCheckRequest {expr,
  repeated expected}`, `runCheckSplitPolicy` (canonicalize, compare the model's
  `splitCondExprs` with the split policies' cube conditions elementwise); the harness builds
  `permit(principal, action, resource) when { c }` on a generated schema, validated, and
  extracts each split policy's condition; budget errors are benign skips. Fixed cases: the
  `a || b` example, `(if a then 1 else 2) == 1`, a multi-field record, `true` (one empty cube),
  `false` (no policies); a seeded smoke test. Scope/effect/id copying is covered by the
  solver-checked Rust tests.

## Files

- `cedar-lean/Cedar/DNF/SplitPolicy.lean`, `Cedar/Thm/DNF/{SplitCond,SplitPolicyThm}.lean`,
  `Cedar/Thm/DNF.lean`, `Cedar.lean`, `CedarFFI/Main.lean`, `CedarProto/SplitPolicyCheckRequest.lean`,
  `CedarProto.lean`; `cedar-lean-ffi` (proto, `lean_ffi.rs`, `lean_ffi/dnf.rs`, `messages.rs`);
  `cedar-drt/fuzz/src/dnf.rs`, `fuzz_targets/split-policies-lean-drt.rs`, `Cargo.toml`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`, the Lean test suites;
`cargo test` in `cedar-drt/fuzz`; a live `cargo fuzz run -s none split-policies-lean-drt`.

## History

Merged from the private plan "Lean verification of split_policy" and its revisions, with the
later change that the model normalizes the condition and the decision theorems carry
`TypedPolicy`.
