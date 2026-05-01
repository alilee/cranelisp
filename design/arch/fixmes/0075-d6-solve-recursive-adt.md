---
number: 0075
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:542
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0075 — d6 solve recursive ADT does not segv

## Issue

Recursive Grid-building with 30 levels of match nesting on SolveResult. If passes, increase depth or add peers-list (Vec of Int) handling. If fails, the defect is in the match-over-ADT return-value dropping interaction with deep recursion. The +2479 alloc/dealloc delta in /backend's original trace is about this order of magnitude for a 30-depth recursion.

## Test name

`d6_solve_recursive_adt_does_not_segv`

## Test purpose

Recursive solver-shaped function that builds/discards Grids at depth. No propagate (which would be huge) — just the branching search shape with `Success`/`Unsolvable` ADT match in tail position.

## Source location

`tests/sprint59_defects456_repro.rs:542`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Defect 6 reductions). Sibling entries: 0065–0074, 0076–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
