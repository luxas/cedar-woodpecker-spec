# Plan cedar-sql-3 — is-authorized: the first differential test of cedar-sql

## Goal

`cedar-sql` branch 3 authorizes a concrete request by partially evaluating the policies with the request and
the action entities known and compiling the residuals into one query over the tables its branch 2 generates.
This branch tests that claim differentially: generated schemas, entities, a policy and requests are
authorized through `cedar-sql` (entities loaded into Postgres) and through `cedar-policy`'s authorizer, and
the decision, the determining policies and the erroring policies must agree.

## Design

- **The generator flag** (`cedar-policy-generators`): `ABACSettings::enable_extensions` (default `true`, so
  every existing target is unchanged) drops the four extension types from generated attribute types
  (`schema.rs`), from generated types (`types.rs`) and from comparison operand types (`expr.rs`), and empties
  the extension-function table (`abac.rs`), since `cedar-sql` does not store extension values yet.
- **The test implementation** (`cedar-drt/src/sql_impl.rs`): `SqlTestImpl` implements
  `CedarTestImplementation` over one schema and one connection to `cedar_sql::testing::SharedPostgres`
  (`CEDAR_SQL_PG_URL`, or an embedded server): `is_authorized` creates the tables (no foreign keys, since
  Cedar data may reference entities that do not exist; the hierarchy table holds the closure), loads the
  entities, runs the compiled query and rolls back, all under a 30 s statement timeout; validation and
  evaluation delegate to `RustEngine`; errors compare by policy id. Plan 6 runs the integration corpus
  through it.
- **The target** (`cedar-drt/fuzz/src/sql.rs`, `sql-is-authorized-drt`): `SqlFuzzTargetInput` is the shape of
  `abac::FuzzTargetInput` under `SETTINGS` (type-directed, depth and width 3, `enable_extensions: false`,
  `enable_like: false`); a generated template is linked to a static policy (partial evaluation takes static
  policies). `compare` requires the policies to validate strictly and each request to validate (the compiler
  relies on typing), then authorizes through both and asserts equality of `(decision, reason set, error set)`
  with the policies and entities in the message. Skips reuse `symeval::{Verdict, Skip}`: `Unsupported` and
  loader limits are `Benign` (the constructs later branches compile), validation gaps `NotWellTyped`/
  `OutsideEnvelope`, a cancelled statement `Timeout`; any other database error panics. `tally` summarizes
  verdicts; the seeded smoke test wants 25 checked inputs and prints the skip counts, the fixed cases are the
  README's example over existing, confidential, dangling and missing entities, and a set operation as a
  benign skip.

## Files

`cedar-policy-generators/src/{settings,schema,types,expr,abac}.rs`, `cedar-drt/src/{lib,sql_impl}.rs`,
`cedar-drt/fuzz/src/{lib,sql}.rs`, `cedar-drt/fuzz/fuzz_targets/sql-is-authorized-drt.rs`,
`cedar-drt/fuzz/Cargo.toml`, `cedar-drt/README.md`, `docs/plans/cedar-sql-3-is-authorized.md`.

## Verification

`cd cedar-policy-generators && cargo test`; `cd cedar-drt/fuzz && cargo test sql::` with `CEDAR_SQL_PG_URL`
set (the fixed cases and the seeded smoke test, which reported 25 checked, 8 benign and 7 not-well-typed
skips on the first run); `cargo fuzz run -s none sql-is-authorized-drt -- -len_control=0 -max_len=4096`
(the generator-based inputs need hundreds of bytes); building needs `protoc` on the path (or `PROTOC`).

## History

New; the third `cedar-sql-spec` branch of the series, paired with `cedar-sql` branch 3.
