---
number: 0082
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1167
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0082 — d45 real html.cl with trimmed grid.cl does not crash

## Issue

real html.cl + trimmed grid.cl. If this crashes, the defect is isolated from grid.cl's 20 test-* defns + bitmask helpers — we've pinned the crash to html.cl + {Grid, Cell, Given, Solved, Candidates, cell-at, cell-value} alone.

## Test name

`d45_real_html_with_trimmed_grid_no_crash`

## Test purpose

Reads the real exemplar html.cl from disk and pairs it with a trimmed grid.cl fixture (only the symbols html.cl imports). Driven through /run-tests.

## Source location

`tests/sprint59_defects456_repro.rs:1167`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0081, 0083–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
