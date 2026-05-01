---
number: 0089
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1695
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0089 — d45 html min v1 nine-cell flat does not crash

## Issue

1 test, 9-cell grid, flat str-concat (no wrap-tag/td), but retained: two-grid-param solution-cell, 2 cell-at calls, match in tail of let.

## Test name

`d45_html_min_v1_no_crash`

## Test purpose

Strip to: 1 test, solution-cell takes two-grid params, no td/wrap-tag (flat str-concat). Smaller grid size (9 cells). No 9x9 outer loop.

## Source location

`tests/sprint59_defects456_repro.rs:1695`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0088, 0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
