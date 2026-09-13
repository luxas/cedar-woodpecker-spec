# Plan cedar-sql-4 — values: the target covers every generated construct

## Goal

`cedar-sql` branch 4 compiles sets, records, computed entities and `in` over sets, and shares
sub-expressions. This branch turns `like` back on for the target and asserts that nothing the generators
produce (without extension types) is skipped as unsupported any more.

## Design

- `SETTINGS` in `cedar-drt/fuzz/src/sql.rs` drops `enable_like: false`.
- `SqlTestImpl::new` maps the schema with `DatabaseConfiguration::from_schema_shortening_names`, since
  generated entity type names may exceed the 63-byte identifier limit and carry no `@sql_table`.
- `compare` panics on loader errors except strings containing a NUL character (a documented Postgres
  limitation), which stay benign skips; `tally` reports each skip with its message.
- The smoke test asserts that no benign skip other than the NUL case remains; the fixed benign case is an
  extension-typed attribute.

## Files

`cedar-drt/src/sql_impl.rs`, `cedar-drt/fuzz/src/sql.rs`, `docs/plans/cedar-sql-4-values.md`.

## Verification

`cd cedar-drt/fuzz && cargo test sql::` with `CEDAR_SQL_PG_URL` set (the first run: 25 checked, 1 NUL
skip, 5 not well typed); `cargo fuzz run -s none sql-is-authorized-drt -- -len_control=0 -max_len=4096`
for five minutes without a disagreement.

## History

New; paired with `cedar-sql` branch 4.
