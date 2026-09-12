# Follow-ups for branch 12 — eliminate-aggregates (Lean model, proofs, DRT)

## PR description

Proves the literal elimination of `cedar` branch 12 exact under typing: `evaluate_eliminate`
and `evaluate_normalize` state that on every request and entity store on which the expression
is `Typed`, eliminating the literals (and the whole split → eliminate → split pipeline)
evaluates exactly like the original; and `elim-lean-drt` runs the Rust pipeline and the model on
generated well-typed expressions.

```lean
theorem evaluate_normalize (e : Expr) (request : Request) (entities : Entities)
    (ht : Typed (splitAtoms e) request entities) :
  evaluate (normalize e) request entities = evaluate e request entities
```

```sh
(cd cedar-drt/fuzz && cargo fuzz run -s none elim-lean-drt)
```

## What this branch contains

- `Cedar/DNF/Elim.lean`, `Cedar/Thm/DNF/{ElimChains,ElimRules,EvalOrder,ElimSound}.lean`, the
  splitter model's shared-guard changes, the `elim-lean-drt` target (`runCheckElim`).

## Review findings

- `Typed` is a semantic predicate over every node, dead code included; the bridge from the
  validator's `typeOf` is not proved (documented gap) — the natural next theorem for the whole
  DNF development.
- `ElimRules.lean` (~720 lines) and `ElimSound.lean` (~700) prove each rule twice (value and
  evaluation level); a shared lemma schema would halve them.
- The DRT skips ill-typed generated expressions as benign without measuring the skip rate.
- Lean linter warnings as in the earlier proof branches.

## Divergences from the private source

- None in content.

## Suggested follow-ups

- The `typeOf` → `Typed` bridge; skip-rate reporting in the DRT.
