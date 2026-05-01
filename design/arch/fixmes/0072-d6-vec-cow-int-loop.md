---
number: 0072
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:409
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0072 — d6 Vec COW Int loop does not segv

## Issue

If this test PASSES (no segv), plain Vec COW with Int elements is not the defect. Next axis: move to Vec of ADT elements (Candidates mask | Given v | Solved v). If this FAILS, the defect is in the vec-set COW primitive's RC logic for non-uniquely-owned elements.

## Test name

`d6_vec_cow_int_loop_does_not_segv`

## Test purpose

Minimal Vec COW stress — push a 100-element Vec, then repeatedly `vec-set` an index in a recursive helper. No ADTs, no match, no strings. Just Int Vec.

## Source location

`tests/sprint59_defects456_repro.rs:409`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Defect 6 reductions on Vec/Grid COW). Sibling entries: 0065–0071, 0073–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
