---
number: 0090
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1726
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0090 — d45 html min v2 single-cell does not crash

## Issue

1 test, single-cell Grid, no loop, one solution-cell call. If crashes, the iteration loop is not needed — just calling a cross-module let+2xcell-at+match helper crashes.

## Test name

`d45_html_min_v2_no_crash`

## Test purpose

Even smaller than v1: 1-cell grid, 1 call to solution-cell (no row-helper loop). Tests whether the iteration matters, or just one call pattern.

## Source location

`tests/sprint59_defects456_repro.rs:1726`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0089. Smallest html-min-v2 reduction in this cluster.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
