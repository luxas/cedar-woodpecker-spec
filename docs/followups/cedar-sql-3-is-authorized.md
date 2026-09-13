# Follow-ups for branch cedar-sql-3 — is-authorized (review)

## PR description

The first differential test of `cedar-sql`: `sql-is-authorized-drt` authorizes generated type-directed
inputs through `cedar-sql` on Postgres and through `cedar-policy`, requiring the same decision, determining
policies and erroring policies (`docs/plans/cedar-sql-3-is-authorized.md`). Five minutes of fuzzing found
no disagreement.

## Review findings (fixed in branches cedar-sql-4 and cedar-sql-5)

- Loader errors other than NUL-containing strings, and `Request`/`Tpe` errors after validation passed,
  were skipped as benign or outside the envelope; they are bugs and now panic.
- With `enable_extensions: false`, the typed generators still chose extension-function arms and aborted the
  whole input on the empty function table; they now fall back to a literal.
- `like` was off and the hierarchy table always closed, so the `like` translation and the recursive
  ancestors CTE were not fuzzed; `like` is on since cedar-sql-4 and the mode is drawn from the input since
  cedar-sql-5.

## Suggested follow-ups

- Run the corpus (`cedar-sql-6`) and the partial-request target for longer than the five-minute smoke runs.
