---
number: 0064
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_reduction.rs:651
status: open
migrated_from_inline: true
split_from_cluster: 0023
---

# 0064 — S60 Round 2 variant: duplicate regression guard (Grid Vec Int)

## Issue

S60 Round 2 variant. This is literally identical source to `s60_drop_glue_minimal_14_loc` — committed as a duplicate regression guard so that a well-intentioned "simplify" edit of the minimal test can't silently delete coverage. If one crashes, both do.

## Test name

`s60_drop_glue_grid_vec_int_no_crash`

## Test purpose

Duplicate-guard variant of the 14-LOC minimal drop-glue repro: Grid wrapping a Vec of Ints, two `cell-at` calls on the same argument inside `walk`. Committed as a sibling so a refactor cannot silently remove regression coverage.

## Source location

`tests/sprint60_reduction.rs:651`

## Cluster context

This entry was split from cluster 0023 (S60 Round 2 drop-glue / auto-curry minimal repro). Sibling entry: 0063 (the minimal 14 LOC repro with identical source).

## Proposed resolution

`/backend` audits `emit_consuming_caller_rc` and closure-env RC accounting for captures of ADT-wrapped Vec. Both reduction tests must pass without crashing after the fix.
