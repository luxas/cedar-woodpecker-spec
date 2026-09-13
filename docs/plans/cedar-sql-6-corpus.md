# Plan cedar-sql-6 — corpus: the integration tests through cedar-sql

## Goal

The `cedar-integration-tests` corpus — the handwritten tests and the generated corpus — through `cedar-sql`:
every request of every test inside the compiler's envelope must give the expected decision, determining
policies and erroring policies, and what falls outside the envelope is counted and named rather than failed.

## Design

- `cedar-drt/tests/sql_integration_tests.rs` (feature `integration-testing`): for each test file
  (`get_integration_tests`, `get_corpus_tests`), the policies, schema and entities are parsed with
  `cedar_testing::integration_testing`; a test whose policies do not validate strictly is outside the
  envelope (the README makes strict validation a precondition; most of the generated corpus comes from the
  untyped `abac` target), as is a schema `cedar-sql` cannot store (extension types); each request is
  authorized through `SqlTestImpl` and compared with the JSON's expected result; a request the compiler
  cannot handle (extension values in policies) or that holds a string with a NUL character is skipped by
  name. Everything skipped is tallied and printed, so the envelope is visible per run.
- The corpus runs a deterministic sixteenth by default (file names starting with `0`), all of it with
  `CEDAR_SQL_FULL_CORPUS=1`; the DRT workflow clones the corpus and runs the tests.
- Hardening the plan foresaw needed no code: linked templates are static policies to the corpus, dangling
  references load without foreign keys, over-long and unicode names are shortened, and open entity types
  did not occur in the checked slice.

## Files

`cedar-drt/tests/sql_integration_tests.rs`, `cedar-drt/README.md`,
`.github/workflows/build_and_test_drt_reusable.yml`, `docs/plans/cedar-sql-6-corpus.md`.

## Verification

With the corpus at `cedar/cedar-integration-tests` (unpacked) and `CEDAR_SQL_PG_URL` set:
`cd cedar-drt && cargo test --features integration-testing --test sql_integration_tests -- --nocapture
--test-threads=1`. First run: all 24 handwritten tests checked (78 requests, no skips); the `0` slice of the
corpus, 470 tests: 263 checked with 2104 requests and no disagreement, 104 tests not validating strictly, 38
with extension types, 48 requests with extension values, 472 requests with NUL strings. The full corpus is
reported in the follow-ups.

## History

New; the sixth `cedar-sql-spec` branch.
