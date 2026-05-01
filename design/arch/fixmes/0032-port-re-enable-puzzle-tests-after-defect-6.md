---
number: 0032
target: /port
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/wave6_demo_repros.rs:441, exemplar/solver.cl
status: open
migrated_from_inline: true
---

# 0032 — Re-enable `test-easy-puzzle` / `test-hard-puzzle` / `test-unsolvable` after Defect 6

## Issue

Once Defect 6 is fixed (FIXME 0031), re-enable `test-easy-puzzle`, `test-hard-puzzle`, and `test-unsolvable` in `exemplar/solver.cl` (currently body-disabled to avoid the segfault).

## Source location

`tests/wave6_demo_repros.rs:441` (FIXME, paired with FIXME 0031 above it).

## Context

The puzzle tests are the headline acceptance criteria for the exemplar solver. They are currently body-disabled rather than `#[ignore]`'d so the durable record stays visible. Re-enabling is `/port`'s task once `/backend` lands the FIXME 0031 fix.

## Proposed resolution

`/port` un-body-disables the three test functions in `exemplar/solver.cl` after Defect 6 is fixed; confirms the regression repro now passes.
