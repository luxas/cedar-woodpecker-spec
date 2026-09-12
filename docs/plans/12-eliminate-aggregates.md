# Plan 12 — The literal elimination: Lean model, proofs under typing, differential test

## Goal

`cedar` branch 12's `eliminate_aggregates` rewrites record and set literals out of atoms and
`normalize_atoms` runs split → eliminate → split. Unlike the earlier passes its exactness needs
a *typing* hypothesis (an `in` over a set type-checks every element; `containsAll` on a non-set
type-errors where a chain of `contains` calls does not). This branch models the pass, states
that hypothesis precisely, proves the pass exact under it, and ties the Rust pipeline to the
model.

## Design

- **Model** (`Cedar/DNF/Elim.lean`): `elim`/`elimList`/`elimRecord` (mutual, structural),
  returning `(changed, guards, rewritten)` per node; the rules as in the Rust pass, with
  `elimEq` (record and set-literal equalities), `elimContainsAll`/`elimContains` (the mutual
  block cycles through them; termination lexicographic over the operands' sizes), `orChain`;
  `elimStructure ctx` carrying the splitter's context; `dropRepeated`/`evalList` for the guards
  the term evaluates first; `eliminate e = elimStructure [] e` and
  `normalize e = splitAtoms (eliminate (splitAtoms e))`; the postcondition `elimFree`.
- **The typing hypothesis** (`Typed e req es`): a *semantic* predicate over every node —
  set-typed `containsAll`/`containsAny` operands, entity-typed `in` operands, present `.a`
  keys, equal record key sets, and at every `==`, `contains`, `containsAll` and `containsAny`
  the value-level `EqTyped` on the values that meet in an equality (two sets are well formed and
  element-wise `EqTyped`, two records field by field, a set never meets a non-set). It is what
  the validator's soundness gives every *reachable* node of a validated expression on a
  schema-conformant input; on dead code it asks more than validation does. The bridge from
  `typeOf` is not proved — a documented gap, not a soundness one.
- **The proofs** (`Cedar/Thm/DNF/{ElimChains,ElimRules,EvalOrder,ElimSound}.lean`): per-rule
  semantic lemmas on `Map`/`Set` (`Map.make_find?_eq_list_find?` makes `.a` the first field;
  `Set.subset_iff_eq` for set equality on well-formed sets); the invariant `elim e = (c, gs, e')
  → evaluate e = underGuards gs (evaluate e') ∧ (Transparent gs → ∃ v, evaluate e' = .ok v)` by
  mutual induction — the second conjunct lets a later sibling's guards move out past an earlier
  child's bind; `underGuards_evalList_prefix` (a prefix of the term's own evaluation order is
  redundant in front of it, because an erring guard there is the term's first error), which
  justifies dropping those guards; `evaluate_eliminate` and `evaluate_normalize` under `Typed`;
  `eliminate_elimFree` / `normalize_elimFree`.
- **Splitter model changes** for the shared guards: `addGuards` decomposing aggregates (and
  `==`), `learnTrue`/`learnFalse` over the evaluated closure, `splitStructure` extending the
  context in `if`-then, `&&`-right, `||`-right and `if`-else.
- **The differential test** (`elim-lean-drt`): a schema, a request (for its environment) and a
  generated boolean expression; the Rust side typechecks it (an ill-typed one is a benign skip)
  and runs `normalize_atoms`; the model runs `normalize`; the results must agree structurally.
  `runCheckElim` reuses `SplitCheckRequest`. Fixed cases per rule including the empty-literal
  cases, nested records, `<set>.contains(<record>)` kept, records inside `iferror`, set equality
  with a literal side; a seeded smoke test.

## Files

- `cedar-lean/Cedar/DNF/Elim.lean`, `Cedar/DNF/Split.lean`, `Cedar/Thm/DNF/{ElimChains,ElimRules,EvalOrder,ElimSound,SplitEquiv,SplitSound}.lean`,
  `Cedar/Thm/DNF.lean`, `Cedar.lean`, `CedarFFI/Main.lean`.
- `cedar-lean-ffi/src/lean_ffi.rs`, `src/lean_ffi/dnf.rs`; `cedar-drt/fuzz/src/dnf.rs`,
  `fuzz_targets/elim-lean-drt.rs`, `Cargo.toml`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`, the Lean test suites;
`cargo test` in `cedar-drt/fuzz`; a live `cargo fuzz run -s none elim-lean-drt`.

## History

Merged from the Lean parts of the private plan "eliminate record and set literals in atoms" and
its revisions (the value-level `EqTyped` came with set equality; the evaluated closure and
`dropRepeated` with the guard-context work).
