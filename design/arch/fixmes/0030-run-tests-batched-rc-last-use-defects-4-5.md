---
number: 0030
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/wave6_demo_repros.rs:329, repl/spec.md §16.3, src/session_v4.rs::run_test_by_name
status: open
migrated_from_inline: true
---

# 0030 — Run-tests batched: RC / last-use across consecutive `run_test_by_name`

## Issue

Likely an RC / last-use issue surfacing across consecutive `run_test_by_name` invocations. Investigate `run_test_by_name` in `src/session_v4.rs` and the IO trampoline RC paths in `cranelisp-runtime`. Defect could be `/backend` (codegen-incomplete path for `html` exemplar module + RC/last-use across consecutive `run_test_by_name`) or `/int`.

Spec anchor: `repl/spec.md §16.3` (run-tests builtins).

## Source location

`tests/wave6_demo_repros.rs:329` (FIXME at `run_tests_batched_invocation_no_crash`).

## Context

Sprint 58 Wave 6 `/repl` demo surfaced as Defects 4+5: batched `run-tests` invocation crashes (where individual ones succeed). The crash signature points to RC accounting at the boundary between consecutive `run_test_by_name` calls.

## Proposed resolution

`/backend` audits the RC discipline for IO trampoline returns from `run_test_by_name`; `/int` confirms the orchestration site does not double-release. Test must pass without crashing.
