---
number: 0073
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:445
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0073 — d6 Vec COW with ADT cells does not segv

## Issue

If d6_vec_cow_int passes but this fails, the defect is in COW + ADT cells. Likely the old cell at the replaced index isn't getting RC-dec'd on vec-set, causing a leak (explains +2479 alloc/dealloc delta). If this ALSO passes, the defect needs the Grid ADT wrapper and/or recursive match nesting to surface.

## Test name

`d6_vec_cow_adt_loop_does_not_segv`

## Test purpose

Vec of ADT + COW updates (no Grid wrapper, no match outside main). Cell sum type {Given Int | Solved Int | Candidates Int} pushed/replaced via vec-set in a recursive update loop.

## Source location

`tests/sprint59_defects456_repro.rs:445`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Defect 6 reductions). Sibling entries: 0065–0072, 0074–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
