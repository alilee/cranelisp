---
number: 0027
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/wave6_demo_repros.rs:158, src/session_v4.rs::compile_dep_inline
status: open
migrated_from_inline: true
---

# 0027 — `compile_dep_inline` must publish dep_sexps before scheduler register

## Issue

Fix in `src/session_v4.rs::compile_dep_inline` by publishing `dep_sexps` to `shared.module_sexps` BEFORE `scheduler.register_module` so any persistent worker that wakes between the two operations finds the sexps it needs. (Spec anchor: implicit — REPL/`--run` divergence is a defect per `repl/spec.md §"Self-documenting REPL"` and root `CLAUDE.md` "Defects" criterion.)

## Source location

`tests/wave6_demo_repros.rs:158` (FIXME at the regression repro).

## Context

The race shape: between publishing dep_sexps and registering the module, a persistent worker may wake and look up a module whose sexps haven't been published yet — leading to spurious failures. Sprint 58 Wave 6 `/repl` demo surfaced this as Defect 1; the test is the durable record.

## Proposed resolution

`/int` reorders publish-then-register in `compile_dep_inline` (and audits the 5 sister sites identified in `design/review/sprint58-wave6-review.md`). Test must pass post-fix.
