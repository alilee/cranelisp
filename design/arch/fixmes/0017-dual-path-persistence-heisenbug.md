---
number: 0017
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint23.rs:2119, design/int/dual-path-persistence-collapse.md §7 step 7 + §8
status: open
migrated_from_inline: true
---

# 0017 — Dual-path persistence heisenbug (50/50 stress test)

## Issue

Sprint 59 Workstream A — the dual-path persistence collapse design explicitly names the ~1755/1754 heisenbug observed at Sprint 58 close (Sprint 58 §Findings) as the structural symptom of two orchestrators working on the same module simultaneously. Per the design doc migration plan step 7, under the collapsed path this loop MUST be 50/50 green (heisenbug source eliminated). Before the collapse lands, this test is expected to flake; after the collapse lands, it MUST be rock solid.

## Source location

`tests/sprint23.rs:2119` (FIXME at the dual-path heisenbug stress repro).

## Context

The repro stresses N concurrent OS threads, each driving K sequential (session 1 → delete cache → session 2) pairs against its own project. Heisenbug surface comes from the dual-orchestrator structure documented in `design/int/dual-path-persistence-collapse.md §8`.

## Proposed resolution

`/int` lands the collapse (Workstream A) per the design doc; the test then must reach 50/50 green. Until the collapse lands, the test is expected to flake — kept failing per `memory/feedback_failing_not_ignored.md`.
