# Plan 15 — The allow/deny combination: Lean model, decision theorem, differential test

## Goal

`cedar` branch 15 rewrites a policy set into permits only, each permit conjoined with a
witness that every forbid is not `true`, and claims the decision is preserved. This branch
proves it and compares whole policy sets — ids, effects, scopes and conditions — between the
Rust combiner and the model.

## Design

- **Model** (`Cedar/DNF/Combine.lean`): `denyWitness` (nested right; `.call .ifError [d,
  boolLit false]`), `combineAllowDeny` (permits get `condition ++ forbids.map (⟨.when,
  denyWitness (conjuncts F.toExpr)⟩)`, forbids sorted by id with `List.mergeSort`),
  `allowCubes = splitPolicySet ∘ combineAllowDeny`.
- **Theorems** (`Cedar/Thm/DNF/Combine.lean`): `outcome_andChain_conjuncts`,
  `outcome_denyWitness` (`tt` iff the chain is not `tt`, never `err`, for boolean-or-error
  conjuncts), `denyWitness_ok_true_iff`, `combinePermit_satisfied_iff` (a combined permit is
  satisfied iff the permit is and no forbid is), `satisfiedPolicies_nonempty_iff`,
  `combineAllowDeny_decision` — under `∀ F ∈ ps, F.effect = .forbid → ∀ d ∈ conjuncts
  F.toExpr, Boolish (evaluate d)` — and `allowCubes_decision` composed with
  `splitPolicySet_decision` (branch 14).
- **The differential test** (`combine-lean-drt`): `CombineCheckRequest {policies,
  expected_combined, expected_cubes}` — three whole policy sets; `runCheckCombine` decodes them,
  sorts by id, and compares each policy's id, effect, three scopes and its condition list
  rendered as one canonicalized expression (a private `NormPolicy` structure with derived
  `DecidableEq`, since the nested-tuple instance does not synthesize). The generator makes 1–3
  policies with unconstrained scopes, generated conditions and arbitrary effects; fixed cases
  cover every scope kind, forbid id order and a template-linked forbid.

## Files

- `cedar-lean/Cedar/DNF/Combine.lean`, `Cedar/Thm/DNF/Combine.lean`, `Cedar/Thm/DNF.lean`,
  `Cedar.lean`, `CedarFFI/Main.lean`, `CedarProto/CombineCheckRequest.lean`, `CedarProto.lean`;
  `cedar-lean-ffi` (proto, `lean_ffi.rs`, `lean_ffi/dnf.rs`, `messages.rs`);
  `cedar-drt/fuzz/src/dnf.rs`, `fuzz_targets/combine-lean-drt.rs`, `Cargo.toml`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`, the Lean test suites;
`cargo test` in `cedar-drt/fuzz`; a live `cargo fuzz run -s none combine-lean-drt`.

## History

Merged from the Lean half of the private plan "combine allow and deny policies" and its
revisions; the two structural-shape fixes on the Rust side were found by this target.
