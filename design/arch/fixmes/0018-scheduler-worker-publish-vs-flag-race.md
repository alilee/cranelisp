---
number: 0018
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint23.rs:2194, design/int/heisenbug-race-closure.md §3b
status: open
migrated_from_inline: true
---

# 0018 — Scheduler/worker publish-vs-flag race (Sprint 61 Wave 3 step 3e)

## Issue

Sprint 61 Wave 3 step 3e is the scheduler/worker fix that makes `cache_repl_loads_heisenbug_parallel_stress` stably green. Until 3e lands this test is expected to fail at >=50% rate (see reduction notes in `design/int/heisenbug-race-closure.md §3b`). Do NOT `#[ignore]` per `memory/feedback_failing_not_ignored.md` — the failing test IS the regression guard and 3b evidence anchor.

## Source location

`tests/sprint23.rs:2194` (FIXME at `cache_repl_loads_heisenbug_parallel_stress`).

## Context

Reduced-shape repro authored under Sprint 61 Wave 3 step 3a (reduction-only agent). Shape: N concurrent OS threads, each driving K sequential (session 1 → delete cache → session 2) pairs against its own project. Reduction lives in `tests/sprint23.rs`; design analysis in `design/int/heisenbug-race-closure.md`.

## Proposed resolution

`/int` lands step 3e (scheduler/worker fix). Test then required to be 20/20 green per the success bar in `design/int/heisenbug-race-closure.md §3d''`.
