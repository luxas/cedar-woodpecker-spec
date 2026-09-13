# Plan cedar-sql-1 — init: the cedar-sql roadmap, its dependency from cedar-drt, Postgres in CI

## Goal

`cedar-sql` (a sibling checkout, `luxas/cedar-sql`) compiles Cedar evaluation into SQL: the Cedar schema becomes
DDL, and after typed partial evaluation the residual policies become one query whose CTEs fetch the entity data,
so the database computes each policy's three-valued outcome and the decision; an unknown `principal` and/or
`resource` yields one row per candidate. Its end state is passing the DRT targets of this repository and the
`cedar-integration-tests` corpus, with `cedar-policy`'s concrete `Authorizer` as the oracle (Rust versus Lean is
covered by the existing `abac*` and `tpe-*` targets; a Lean model of the compilation is deferred). This branch
records the roadmap, makes `cedar-drt` depend on the crate, and gives DRT CI a Postgres.

## Design

### The series

One `cedar-sql` branch `N-slug` and one branch `cedar-sql-N-slug` here per phase, each with a plan document:

1. **init** — this branch; `cedar-sql` branch 1 adds the crate skeleton, `SharedPostgres` (feature `testing`:
   `CEDAR_SQL_PG_URL` or an embedded Postgres 18 once per process, inputs isolated by `BEGIN … ROLLBACK`) and CI.
2. **schema** — Idea 1: `SQLIdentifier`, `DatabaseConfiguration`/`TableConfiguration`/`ColumnConfiguration`/
   `SQLType`, the `@sql_*` annotations read from the schema fragment, DDL, the entity loader with the canonical
   JSONB encoding of sets and records (deduplicated and sorted arrays, wrapped records and entity references, so
   that JSONB equality is Cedar equality), ancestor rows and tag rows.
3. **is-authorized** — Idea 2 for a concrete request: `cedar_policy_core::tpe::is_authorized` with the action
   entities as the only known entities, a query plan (one CTE per unknown variable or dereferenced entity literal,
   `LEFT JOIN`s per attribute path, a recursive ancestors CTE per `in` root), the three-valued encoding (`NULL`
   is an error: `CASE` forms for `&&`/`||`/`if`, arithmetic guarded in `numeric` since a `bigint` overflow would
   abort the statement, `has` guarded by the parent's value so an errored parent errors and a missing entity is
   `false`), the decision and the `reason`/`errors` sets rebuilt as `cedar-policy` does. Target
   `sql-is-authorized-drt`: `FuzzTargetInput<true>` with `enable_extensions: false` (a new `ABACSettings` flag)
   and `enable_like: false`, validation gates, `run_auth_test` through a `SqlTestImpl` implementing
   `CedarTestImplementation` (`PolicyIds` error comparison); `Error::Unsupported` maps to a benign skip so the
   target lands before every operator is compiled; fixed cases and a seeded smoke test under `cargo test`.
4. **values** — sets, records, `like`, tags, non-root dereferences, memoization; `enable_like: true`; the smoke
   test asserts zero benign skips on non-extension inputs.
5. **query** — unknown `principal`/`resource` as `CROSS JOIN`s; target `sql-query-drt` compares every returned row
   with the concrete `Authorizer` over all entities of the unknown type(s), and the `Allow` subset with
   `PolicySet::query_resource`/`query_principal`.
6. **corpus** — `cedar-drt/tests/sql_integration_tests.rs` runs the `cedar-integration-tests` corpus through
   `perform_integration_test` with `SqlTestImpl`; templates, open entity types, dangling references.
7. **extensions** — `ipaddr`/`decimal`/`datetime`/`duration`; the corpus and all `sql-*` targets green.
8. **sqlite** — SQLite and Turso dialect parity. 9. **benchmarks**, and the seam for a later Lean model.

### This branch

- `cedar-drt/Cargo.toml` and `cedar-drt/fuzz/Cargo.toml` depend on `cedar-sql` by path (`../cedar-sql`,
  `../../cedar-sql`, feature `testing`), next to the existing `../cedar` patches; the crate's own `[patch]` of
  `cedar-policy` to `../cedar` coincides with this repository's, so one copy of `cedar-policy` is built.
- `.github/workflows/build_and_test_drt_reusable.yml` checks out `luxas/cedar-sql` next to `cedar`, runs a
  `postgres:18` service and sets `CEDAR_SQL_PG_URL` for the `cedar-drt/fuzz` tests.

## Files

`docs/plans/cedar-sql-1-init.md`, `cedar-drt/Cargo.toml`, `cedar-drt/fuzz/Cargo.toml`,
`.github/workflows/build_and_test_drt_reusable.yml`.

## Verification

`cd cedar-drt && cargo build`; `cd cedar-drt/fuzz && cargo build && cargo test` (unchanged targets);
`cd ../cedar-sql && cargo test --all-features` with `CEDAR_SQL_PG_URL` set.

## History

New; planned on 2026-09-13 from the `cedar-sql` README with the user's decisions: Postgres first, no Lean model
yet, canonical JSONB for sets and records.
