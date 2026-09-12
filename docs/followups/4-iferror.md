# Follow-ups for branch 4 — iferror (Lean)

## PR description

Gives `iferror(e, d)` — `e`'s value, or `d`'s when `e` errors, introduced in `cedar` branch 4 —
its formal definition: a lazy arm in the Lean evaluator, the typechecker rule, both symbolic
compilers (`ite (isNone e) d e`) and the TPE arm, with every soundness theorem the new arm
touches re-established, and the DRT generators emitting the function so that every
Rust-versus-Lean differential target covers it.

```lean
-- Cedar.Spec.evaluate, the new arm
| .call .ifError [x₁, x₂] => match evaluate x₁ request entities with
  | .ok (.prim (.bool b)) => .ok (.prim (.bool b))
  | .ok _                 => .error .typeError
  | .error _              => (evaluate x₂ request entities >>= Value.asBool).map …
```

```sh
(cd cedar-drt/fuzz && cargo test iferror)   # the table rows, Rust vs Lean
```

## What this branch contains

- `ExtFun.ifError`, the evaluator arm, `typeOfCall`, both `compileCall`s, the TPE arm, the
  23 repaired proof files, the protobuf decoders and the FFI `ExtFun` mirror, the generators'
  extension-function table, and `cedar-drt/fuzz/src/iferror.rs` (fixed-case rows).

## Review findings

- The strict `call` body is reachable only when both arguments evaluated without error; the
  comment says so, a theorem would pin it.
- `cedar-drt/fuzz/src/iferror.rs` is a unit test in the fuzz crate and therefore the only part
  of this DRT that CI runs; the type-directed targets cover the rest only when run.
- The operator's own table theorems live with the DNF splitter (branch 10) because they use its
  outcome algebra; moving that algebra next to the spec would let them sit with the extension.

## Divergences from the private source

- None in content.

## Suggested follow-ups

- The invariant theorem; move the outcome algebra to `Thm/Spec`.
