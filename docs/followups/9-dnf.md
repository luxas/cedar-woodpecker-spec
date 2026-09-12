# Follow-ups for branch 9 — dnf (Lean model, proofs, DRT)

## PR description

Proves the DNF converter of `cedar` branch 9 correct: a Lean model of the converter, theorems
that its output interprets exactly like the input under every three-valued valuation and
evaluates like it under Cedar's concrete evaluator (same boolean value or both error), that at
most one cube is ever true, and that pruning never-true cubes is sound; plus a fuzz target that
converts the same generated expressions on both sides and compares the results structurally.

```lean
theorem evaluate_dnfOfExpr (e : Expr) (request : Request) (entities : Entities) :
  (∃ b, evaluate (dnfOfExpr e) request entities = .ok (.prim (.bool b)) ∧
        evaluate e request entities = .ok (.prim (.bool b))) ∨
  (∃ err, evaluate (dnfOfExpr e) request entities = .error err) ∧ (∃ err, evaluate e request entities = .error err)
```

```sh
(cd cedar-drt/fuzz && cargo fuzz run -s none dnf-lean-drt)
```

## What this branch contains

- `Cedar/DNF.lean`, `Cedar/Thm/DNF/{Interp,Extend,Invariant,Master,Pruning,Equivalence}.lean`,
  the `dnf-lean-drt` target with its FFI entry (`runCheckDnf`, `DnfCheckRequest`).

## Review findings

- `evaluate_dnf` needs the boolean-atoms hypothesis; validated Cedar satisfies it, but the
  theorem is not connected to the typechecker — a bridge lemma from `typeOf` would close it.
- `Cedar/Thm/DNF.lean` is the aggregator whose doc comment summarizes every DNF theorem and
  grows with each branch; keeping only the theorem index there would avoid duplicating the plans.
- The DRT checks structural equality of rendered chains after record-field canonicalization on
  the Lean side; a deterministic proto encoder would remove the need.

## Divergences from the private source

- `cedar-drt/fuzz/src/dnf.rs`: the invariant-breach `panic!` arm matches on
  `DnfError::Unsupported` alone (the typing variants exist from branch 12); the module doc is the
  original one-target wording until branch 15.
- `cedar-lean-ffi/src/lean_ffi/dnf.rs` is rustfmt-formatted (the source fails `cargo fmt --check`).

## Suggested follow-ups

- The `typeOf` → boolean-atoms bridge.
