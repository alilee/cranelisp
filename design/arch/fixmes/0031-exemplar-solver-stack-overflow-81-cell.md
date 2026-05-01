---
number: 0031
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/wave6_demo_repros.rs:437, exemplar/solver.cl
status: open
migrated_from_inline: true
---

# 0031 — Sudoku solve/propagate stack overflow on 81-cell puzzles (Defect 6)

## Issue

solve/propagate stack-overflow on 81-cell puzzles. Likely propagate/solve recursion depth or stack frame size issue. Investigate Grid/Vec copy-on-write semantics in deep recursion. Sister: FIXME 0032 — once Defect 6 is fixed, `/port` re-enables `test-easy-puzzle`, `test-hard-puzzle`, `test-unsolvable` in `exemplar/solver.cl` (currently body-disabled to avoid this segfault).

Spec anchor: implicit (exemplar validation, not language conformance).

## Source location

`tests/wave6_demo_repros.rs:437` (FIXME at `exemplar_solver_does_not_stack_overflow_on_small_puzzle`).

## Context

Pre-existing per `exemplar/CLAUDE.md` "Known Issues". Sprint 19 stack-overflow on full 81-cell puzzles. Carries S62 baseline ledger (5× Defect 6 family entries per `sprints/SPRINT.md §"Carries from S62"`).

## Proposed resolution

`/backend` lands the codegen / Grid-Vec COW fix that prevents the stack overflow on 81-cell input; FIXME 0032 (port re-enabling) becomes actionable.
