---
number: 0116
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/scheduler.rs
status: open
---

# Harvest tests/legacy/scheduler.rs into src/ (scheduler) unit tests

## Issue

The Sprint 64 test-port quarantined this file because its assertions
test Rust-internal state with no e2e equivalent: every test directly
constructs `cranelisp::scheduler::CompileScheduler` and inspects its
public-but-internal API (priority queue, waiter/unblock state, failure
cascade). Per the two-tier strategy
(`memory/project_test_strategy.md`), these belong as
`#[cfg(test)]` unit tests inside the owning crate (the binary `src/`
today; the scheduler crate post-FIXME-0109 split).

The scheduler's observable behaviour is covered indirectly by every
other e2e test in the new suite (every multi-module program runs
through it).

## Proposed resolution

- Read each of the 18 tests in `tests/legacy/scheduler.rs`.
- Translate into `#[cfg(test)]` modules inside
  `src/scheduler.rs` (or its successor module post-FIXME-0109)
  adjacent to the code under test.
- Use cranelisp-frontend's `parse` + `build_program` for AST input
  per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — do NOT
  hand-construct AST.
- When complete, delete `tests/legacy/scheduler.rs` and remove its
  row from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until
it lands, the assertions are inert (the file is not compiled). The
FIXME blocks no other work — but the longer it sits, the further
the post-FIXME-0109 internal surface drifts from the quarantined
shape and the more rewrite the harvest requires.
