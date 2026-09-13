# Follow-ups for branch cedar-sql-6 — corpus

## PR description

The `cedar-integration-tests` corpus through `cedar-sql` (`docs/plans/cedar-sql-6-corpus.md`): every request
inside the compiler's envelope must give the expected decision, determining policies and erroring policies;
the rest is tallied by reason.

## Results of the full corpus (2026-09-13)

`CEDAR_SQL_FULL_CORPUS=1`, 7497 tests in 458 s: 4304 tests checked with 34413 requests and no disagreement.
Outside the envelope: 1599 tests whose policies do not validate strictly, 580 tests with extension types in
the schema, 864 requests with extension values in the policies, 7251 requests with a string holding a NUL
character (Postgres `text` cannot store one), and 16 requests with `hasTag` on an action type, which
`cedar-sql` branch 6 now compiles as `false` (the validator's type for it). The 24 handwritten tests all
check (78 requests).

## Suggested follow-ups

- Extension types (Plan 7) would bring the 580 tests and 864 requests into the envelope.
- NUL characters could be encoded in storage (with the same encoding applied to literals) if the corpus
  matters more than the fidelity of stored strings.
