# Plan 11 — The like rewrite: Lean model, proofs and differential test

## Goal

`cedar` branch 11 rewrites `x like "exact"` (no wildcard) to `x == "exact"`. Cedar's matcher
`wildcardMatch` is a memoized dynamic program in `StateM`, so even this small rewrite needs a
real proof: a structural characterization of the matcher, soundness of the rewrite where the
operand is a string, and completeness (every `like` left has a wildcard, and such a pattern is
matched by at least two strings). Plus the differential target.

## Design

- **Model** (`Cedar/DNF/Like.lean`): `hasStar`, `patternString`, `rewriteLike` (mirrors
  `rewrite_like` over every constructor), `likesHaveWildcards`.
- **The matcher's specification** (`Cedar/Thm/DNF/Wildcard.lean`): a structural matcher
  `matchB : List Char → Pattern → Bool` and `wildcardMatchIdx_spec` — the memoized program
  computes it, by the function's own induction principle with the cache invariant "every cached
  `(i, j)` holds the specified answer"; `wildcardMatch_eq_matchB`; `matchB_noStar` (a star-free
  pattern matches exactly its characters); `star_matches_two` (a pattern with a star is matched
  by two strings of different lengths). The program's helpers are private to
  `Cedar.Spec.Wildcard`, so this file is a `module` with `import all` that exports only
  statements over `wildcardMatch`.
- **The theorems** (`Cedar/Thm/DNF/Like.lean`): `evaluate_rewriteLike` (sound, under "the
  operand of every wildcard-free `like` evaluates to a string or errors"), `rewriteLike_complete`
  and `rewriteLike_matches_two`.
- **The differential test** (`like-lean-drt`): `LikeCheckRequest {expr, expected}`,
  `runCheckLike` (both canonicalized), `run_like_check`; the harness reuses the DNF generator
  (the type-directed generators emit `like`); fixed cases including an escaped star; the smoke
  test counts only inputs the rewrite changes.

## Files

- `cedar-lean/Cedar/DNF/Like.lean`, `Cedar/Thm/DNF/{Wildcard,Like}.lean`, `Cedar/Thm/DNF.lean`,
  `Cedar.lean`, `CedarFFI/Main.lean`, `CedarProto/LikeCheckRequest.lean`, `CedarProto.lean`;
  `cedar-lean-ffi` (proto, `lean_ffi.rs`, `lean_ffi/dnf.rs`, `messages.rs`);
  `cedar-drt/fuzz/src/dnf.rs`, `fuzz_targets/like-lean-drt.rs`, `Cargo.toml`.

## Verification

`lake build Cedar SymCC` (no `sorry`, standard axioms), `lake lint`, the Lean test suites;
`cargo test like` in `cedar-drt/fuzz`; a live `cargo fuzz run -s none like-lean-drt`.

## History

Merged from the Lean half of the private plan "like without wildcards is ==" and its revision.
