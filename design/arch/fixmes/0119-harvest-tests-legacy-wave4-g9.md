---
number: 0119
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/wave4_g9.rs
status: open
---

# Harvest tests/legacy/wave4_g9.rs into src/ (persistent-worker) unit tests

## Issue

The Sprint 64 test-port quarantined this file because its assertions
test Rust-internal state with no e2e equivalent: Layer-3 integration
observations of persistent priority workers (Sprint 57 Wave 4 / G9)
through the `CompilerSession` Rust API — worker-pool lifecycle,
priority-queue scheduling, observability counters. Per the two-tier
strategy (`memory/project_test_strategy.md`), these belong as
`#[cfg(test)]` unit tests inside the owning crate (the binary `src/`
today; the worker-pool module post-FIXME-0109 split).

## Proposed resolution

- Read each of the 4 tests in `tests/legacy/wave4_g9.rs`.
- Translate into `#[cfg(test)]` modules inside
  `src/worker.rs` (or its successor module post-FIXME-0109) adjacent
  to the persistent-worker code under test.
- Use cranelisp-frontend's `parse` + `build_program` for AST input
  per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — do NOT
  hand-construct AST.
- When complete, delete `tests/legacy/wave4_g9.rs` and remove its
  row from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until
it lands, the assertions are inert (the file is not compiled). The
FIXME blocks no other work — but the longer it sits, the further
the post-FIXME-0109 internal surface drifts from the quarantined
shape and the more rewrite the harvest requires.
