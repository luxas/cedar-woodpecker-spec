# Follow-ups for branch cedar-sql-4 — values (review)

## PR description

`sql-is-authorized-drt` with `like` on, generated names shortened, and no benign skip left
(`docs/plans/cedar-sql-4-values.md`); five minutes of fuzzing with the branch 4 compiler found no disagreement.

## Review findings (fixed in branch cedar-sql-6)

- The input-level verdict hid per-request benign skips: an input with one checked request counted as checked
  whatever the other requests skipped. `Outcome` now carries every request's result.
- Loader errors were classified benign on the substring `NUL`, which generated data can contain; the crate's
  `Error::Nul` is matched instead.

## Suggested follow-ups

- Longer fuzz runs than the five-minute smoke runs, once CI has a Postgres.
