---
number: 0074
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:491
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0074 — d6 Grid wrapper COW does not segv

## Issue

Grid ADT wrapper adds one level of boxing (and a match to unpack). If this fails but d6_vec_cow_adt passes, the defect is at the Grid level — likely the match (Grid cs) arm dropping the old Vec while a new Grid wraps the same Vec; or the Grid's inner Vec RC isn't inc'd when cells-of returns it.

## Test name

`d6_grid_wrapper_cow_does_not_segv`

## Test purpose

Grid wraps Vec of Cells; `set-cell` unwraps, updates, rewraps — matches the exemplar's `set-cell` shape and Grid ADT handling. Recursive update loop exercises the wrapper RC handling.

## Source location

`tests/sprint59_defects456_repro.rs:491`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Defect 6 reductions). Sibling entries: 0065–0073, 0075–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
