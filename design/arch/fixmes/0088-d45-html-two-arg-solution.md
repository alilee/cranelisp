---
number: 0088
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1653
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0088 — d45 html two-arg solution-cell does not crash

## Issue

2 tests, solution-cell takes two grid params (2 cell-at calls), wraps via td + wrap-tag.

## Test name

`d45_html_two_arg_solution_no_crash`

## Test purpose

Add: wrap-tag + td + solution-cell takes TWO grid params. Mirrors html.cl's signature closely: `solution-cell original solved idx`, and `solution-page solved original` (two grid args, used g g).

## Source location

`tests/sprint59_defects456_repro.rs:1653`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0087, 0089–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
