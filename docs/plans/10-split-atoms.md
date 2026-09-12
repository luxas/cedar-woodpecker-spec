# Plan 10 — The atom splitter: Lean model, exactness proof and differential test

## Goal

`cedar` branch 10's `split_atoms` hoists `&&`/`||`/`!`/`if` nodes out of atoms and claims to
preserve evaluation exactly — the same value or the same error — thanks to `g == g` guards for
the hoisted node's left siblings. This branch models the splitter in Lean, proves that claim as
an equality of `Result Value`s with no hypotheses, proves the output clean, states the
`iferror` table the later combination rests on, and ties the Rust splitter to the model with a
differential target.

## Design

### The model (`Cedar/DNF/Split.lean`)

Mirrors `split.rs` case for case: `isOffender`; `foldEq` (bottom-up `lit == lit` folding);
`hoistStep`/`hoist`/`hoistList` (the first offending node strictly inside an expression, in the
same child order as Rust's `expr_util::children` — record children key-sorted on both sides —
returning the condition and the two substituted copies, with the guards collected from the
siblings evaluated before it); `neverErrs` (a literal, a variable, or a set/record literal of
such — no guard needed); `newGuards ctx gs` (dedupe against the context and left to right);
`splitStructure ctx`/`splitAtom ctx` (mutual), an atom hoisting `if G then (if c then A[x] else
A[y]) else false` until nothing is found, then `foldEq`; `splitAtoms e = splitStructure [] e`.
`iferror` calls are opaque: `hoist` returns `none` for `.call .ifError _`, and `cleanAtoms`
treats the call as a leaf. No budget and no stack check; termination is well-founded on the
substituted atoms' size (`hoist_size`).

### The theorems (`Cedar/Thm/DNF/{SplitEquiv,HoistSpec,SplitSound}.lean`)

- `foldEq_sound`: exact — `apply₂ .eq` on two literal values is `.ok` of their equality.
- `hoist_spec`: if `hoist e = some (cond, t, f, guards)` then, when the guards evaluate,
  `cond = tt` gives `evaluate e = evaluate t`, `ff` gives `evaluate f`, and an erring `cond`
  errs `e` — by strictness of every atom-interior node and purity.
- `evaluate_splitAtoms : evaluate (splitAtoms e) req es = evaluate e req es` — for every
  expression, request and entity store, with **no hypotheses**: the guards reproduce the left
  siblings' errors in the original order (`underGuards_newGuards`: a context whose guards
  evaluate without error), so the equality is of `Result Value`s, error identity included.
- `splitAtoms_clean`: no atom of the output contains `&&`/`||`/`!`/`if` outside an opaque
  `iferror` call (`offFree`/`cleanAtoms`).
- `evaluate_dnf_splitAtoms`: the pipeline corollary — the DNF of the split expression
  evaluates like the original under branch 9's hypotheses for the split expression.
- `Cedar/Thm/DNF/IfError.lean`: the three-valued `iferror` table (`outcome_ifError`),
  `outcome_ifError_false_ne_err` (`iferror(e, false)` never errs for boolean-or-error `e`) and
  `ifError_false_ok_true_iff` / `not_ifError_false_ok_true_iff` — the shape branch 15 moves
  deny terms with. They use the split equivalence algebra, which is why they live here.

### The differential test (`split-atoms-lean-drt`)

`SplitCheckRequest {expr, expected}`, `runCheckSplit` (input canonicalized, the model's output
canonical by construction), `run_split_check`; the harness runs `split_atoms(expr,
DEFAULT_MAX_SPLIT_NODES)` (budget and recursion errors are benign skips) and compares
structurally. Fixed cases: the worked example, `if`s under `==`, booleans inside sets and
records, `lit == lit` folds across types, already-clean inputs, guards, guard dedupe against the
context, never-erring siblings, two identical erring siblings, an offender inside an opaque
`iferror` call; a seeded smoke test.

## Files

- `cedar-lean/Cedar/DNF/Split.lean`, `Cedar/Thm/DNF/{SplitEquiv,HoistSpec,SplitSound,IfError}.lean`,
  `Cedar/Thm/DNF.lean`, `Cedar.lean`, `CedarFFI/Main.lean`, `CedarProto/SplitCheckRequest.lean`.
- `cedar-lean-ffi` (proto, `lean_ffi.rs`, `lean_ffi/dnf.rs`, `messages.rs`), `cedar-drt/fuzz/src/dnf.rs`,
  `fuzz_targets/split-atoms-lean-drt.rs`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`, the Lean test suites;
`cargo test` in `cedar-drt/fuzz`; a live `cargo fuzz run -s none split-atoms-lean-drt`.

## History

Merged from the private plans "Lean verification of split_atoms" (an equivalence up to the
error kind at the time) and "exact error behaviour for split_atoms" (the guards; the theorem
became a plain equality and `EquivRes` disappeared), plus the model changes for the
aggregate-guard decomposition and learned guards.
