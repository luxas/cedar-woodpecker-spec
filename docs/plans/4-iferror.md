# Plan 4 — `iferror` in the Lean specification, proofs and differential tests

## Goal

Branch 4 of `cedar` adds the boolean extension function `iferror(e, d)` — `e`'s value, or
`d`'s when `e` errors — which the DNF pipeline needs to move deny terms into allow policies
soundly. This branch gives it a formal definition and re-establishes every theorem that the
new evaluator arm touches, so that the Rust implementation is covered by the existing
Rust-versus-Lean differential tests.

## Semantics

| `e` evaluates to | result |
| --- | --- |
| `true` / `false` | that value; `d` is **not** evaluated |
| a non-boolean value | a type error |
| an error | `d`, coerced to a boolean: its value, or its own error |

## Design

- **Spec**: `ExtFun.ifError`; a lazy arm in `Cedar.Spec.evaluate` for `.call .ifError [x₁, x₂]`
  placed before the generic `.call` arm (the table above), and a strict `call` body
  `.ifError, [bool b, bool _] => .ok b` reached only when both arguments evaluated (mirroring
  Rust's extension body). The strict arm sits last so the auto-numbered cases of existing
  `split` proofs stay stable.
- **Typechecker**: `typeOfCall` gives `.ifError, [.bool _, .bool _] => .bool .anyBool`.
- **Symbolic compilers** (`Cedar.SymCC.Compiler`, `Cedar.SymCCOpt.Compiler`): both terms typed
  `.option .bool`, result `ite (isNone t₁) t₂ t₁`; the optimizing compiler unions footprints.
- **TPE** (`Cedar.TPE.Evaluator`, `Cedar.TPE.Residual`): the same table on residuals; an
  erroring first argument with a partial fallback stays `iferror(<error>, d')` so that type
  preservation holds.
- **Proofs repaired**: adding a lazy arm before the generic `.call` makes Lean keep an
  unconditional equation for the new shape and a *conditional* one for the generic arm, so
  every proof that unfolds `evaluate` on an abstract call gains a case — 23 files under
  `Thm/{SymCC,TPE,Validation,WellTyped}`, each one more case in an existing per-`ExtFun`
  scheme (`Spec.evaluate_call_ne` / `evaluate_call_arity` expose the strict equation; the
  `compile` case is the `ite`-of-options argument the `compileIf` proofs already make).
- **Protobuf decoders** (`CedarProto/Expr.lean`, `CedarProto/Residual.lean`) and the FFI
  `ExtFun` mirror (`cedar-lean-ffi/src/datatypes/tpe.rs`) know the function, so the Lean-TPE
  authorization targets compare residuals that keep an `iferror` call instead of failing.
- **Generators**: `iferror` joins the type-directed generators' extension-function table
  (`cedar-policy-generators/src/abac.rs`), so every existing Rust-vs-Lean target that draws on it
  — evaluation, validation, the symbolic-evaluator replay, the DNF pipeline, the Lean-TPE
  authorization targets — exercises it without a new target.

The operator's own table theorems (`outcome_ifError`, `outcome_ifError_false_ne_err`,
`ifError_false_ok_true_iff`) reason with the atom splitter's outcome algebra and are part of
branch 10 (`Cedar/Thm/DNF/IfError.lean`).

## Files

- `cedar-lean/Cedar/Spec/{ExtFun,Evaluator}.lean`, `Cedar/Validation/Typechecker.lean`,
  `Cedar/SymCC/Compiler.lean`, `Cedar/SymCCOpt/Compiler.lean`, `Cedar/TPE/{Evaluator,Residual}.lean`,
  the repaired proof files under `Cedar/Thm/`, `CedarProto/{Expr,Residual}.lean`.
- `cedar-lean-ffi/src/datatypes/tpe.rs`, `cedar-policy-generators/src/abac.rs`,
  `cedar-drt/fuzz/src/iferror.rs` (fixed-case Rust-vs-Lean evaluation rows).

## Verification

`lake build Cedar SymCC` with no `sorry` and standard axioms only; `lake lint`; the Lean unit
and SymCC test suites; `cargo test` in `cedar-drt/fuzz` (the fixed-case rows: the table,
laziness, wrong arity, nesting), and short runs of the type-directed targets.

## History

Merged from the private plan "iferror — coalescing error → bool"; the Rust half is `cedar`
branch 4. The residual shape for a partial fallback and the number of proof files affected
were found while proving, not planned.
