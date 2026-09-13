# Follow-ups for branch cedar-sql-5 — query (review)

## PR description

`sql-query-drt`: partial requests against brute-force concrete authorization of every candidate and the
permission queries (`docs/plans/cedar-sql-5-query.md`), plus the branch 3 review fixes for the generators and
the target. Five minutes of fuzzing found no disagreement.

## Review findings (fixed in branch cedar-sql-6)

- The permission-query cross-check collapsed every failure (an invalid request environment, or entity
  validation failing on dangling references) into silence, so it could be vacuous unnoticed; it is now noted
  per request and the fixed cases assert no note.
- The per-request accounting of `Outcome` applies here too.

## Suggested follow-ups

- The candidates of an enum entity type are the table's rows, as for `PolicySet::query_resource`; the
  differential test cannot see a difference, so this is a documented choice, not a tested one.
