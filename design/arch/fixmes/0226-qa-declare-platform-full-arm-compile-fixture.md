---
number: 0226
target: /qa
filed_by: /qa
filed_at: 2026-05-27
sprint_filed: 71
refers_to: design/arch/facades/cranelisp-platform-audit-s69.md §4 C3, tests/plan/sprint71-platform.md §3 (T17–T21 partial coverage)
status: deferred
deferred_to: 72
deferred_at: 2026-05-28
deferred_rationale: |
  Sprint 71 Wave 1 gate disposition. **Partially mitigated this
  sprint** by T17–T21 (the new `schema:` arm gets compile-fixture
  coverage via Wave 2 `/dev platform` work in
  `crates/cranelisp-platform/tests/`). The unfinished portion — a
  single fixture exercising all arms (`name:`, `version:`, `host:`,
  `functions:`, `schema:`) at once — defers to the conformance-triad-
  enhancement sprint (target 72) alongside the rest of the C1–C5
  follow-ups.
---

# `declare_platform!` full-arm compile-fixture coverage gap (audit C3 follow-up)

## Issue

The S69 audit recommended a compile-fixture test invoking `declare_platform!` with the facade-documented shape, so any future arm-reshape (adding/removing/renaming a key, delimiter change) fails at PR gate. Sprint 71's tests T17–T21 cover this for the NEW `schema:` arm only. The existing arms (`name:`, `version:`, `host:`, `functions:`) still rely on the doc-comment example at `lib.rs:716–740` (or its post-retirement folded location) as the only compilation witness.

## Proposed resolution

Author a single compile-fixture test at `crates/cranelisp-platform/tests/macro_full_arm_compile.rs` that invokes `declare_platform!` with the facade-documented (post-retirement, in the rustdoc) shape — exercising every required arm + the new `schema:` arm in one invocation. The test's role: fail at PR time if any arm is silently reshaped.

## Operational implication / Context

The audit called this "the more durable fix" over a structural macro-rules parser. Sprint 71 partially mitigated (the new arm) but did not finish the job. One-sprint sized, low-risk.
