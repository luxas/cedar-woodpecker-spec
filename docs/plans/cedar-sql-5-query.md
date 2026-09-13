# Plan cedar-sql-5 — query: partial requests against every candidate

## Goal

`cedar-sql` branch 5 answers a request with an unknown principal and/or resource with one row per candidate.
This branch tests it: every returned row must agree with `cedar-policy`'s authorizer on the concrete request
it stands for, the rows must be exactly the candidates, and the allowed set must agree with the permission
queries `PolicySet::query_resource`/`query_principal`. It also applies the review of branch 3 to the
generators and the target.

## Design

- **The target** (`sql-query-drt`, `cedar-drt/fuzz/src/sql.rs`): `SqlQueryFuzzTargetInput` is the ABAC input
  plus, per request, which variables are unknown (`Unknowns::{Principal, Resource, Both}`). `compare_query`
  drops the chosen ids (`SqlTestImpl::query`), builds the candidate set from the entities of the unknown
  types, authorizes every candidate (pair) concretely through `cedar-policy`, and requires the row map to
  equal it; with one unknown variable it also compares the allowed set with the permission query when that
  query accepts the request. `SqlTestImpl::query` is `with_loaded` around `SqlAuthorizer::query`.
- **Review of branch 3**: `classify` panics on loader errors other than NUL strings and on `Request`/`Tpe`
  errors (both are bugs once validation passed); the generators fall back to a literal instead of an
  extension-function call when `enable_extensions` is off, so typed generation no longer aborts inputs at
  those arms; the input draws `hierarchy_closed`, so the recursive ancestors CTE is fuzzed too; `like` is on
  since branch 4.
- The fixed cases run the README's example with the resource, the principal and both unknown, in both
  hierarchy modes; the seeded smoke test wants 25 checked inputs with no benign skip.

## Files

`cedar-policy-generators/src/expr.rs`, `cedar-drt/src/sql_impl.rs`, `cedar-drt/fuzz/src/sql.rs`,
`cedar-drt/fuzz/fuzz_targets/sql-query-drt.rs`, `cedar-drt/fuzz/Cargo.toml`, `cedar-drt/README.md`,
`docs/plans/cedar-sql-5-query.md`.

## Verification

`cd cedar-drt/fuzz && cargo test sql::` with `CEDAR_SQL_PG_URL` set (both smoke tests: 25 checked, no benign
skip); `cargo fuzz run -s none sql-query-drt -- -len_control=0 -max_len=4096` for five minutes.

## History

New; paired with `cedar-sql` branch 5.
