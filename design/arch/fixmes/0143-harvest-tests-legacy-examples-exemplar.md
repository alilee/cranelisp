---
number: 0143
target: /port
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
refers_to: tests/legacy/examples.rs, tests/legacy/examples_run.rs, tests/legacy/exemplar.rs, tests/legacy/exemplar_solver_correctness.rs, tests/examples.rs (NEW), tests/exemplar.rs (NEW), tests/regression.rs (NEW)
status: open
---

# Harvest tests/legacy/examples + exemplar files into /port-owned coverage

## Issue

Sprint 64 Wave 6 batch 1 quarantined four source files exercising
`examples/` and `exemplar/` subprocess execution. The new e2e
carry-forwards (tests/examples.rs umbrella + tests/exemplar.rs
batch-mode shapes + 1 regression entry) preserve the load-bearing
coverage; the legacy files retain finer-grained variant tests
that may be worth folding back as `/port` crate tests.

## Proposed resolution

`/port` reviews the quarantined files for any test-shape worth
preserving as `#[cfg(test)]` unit tests inside the exemplar/ or
examples/ project, OR for fold-back into the new
tests/examples.rs / tests/exemplar.rs e2e tests. Anything not
worth preserving is deleted with the legacy file when the
harvest is complete.

## Operational implication / Context

The legacy files have integration-tier dependencies on
exemplar/grid.cl + exemplar/solver.cl that the new e2e tests do
NOT (per `feedback_repro_handoff.md` — repros stand alone).
Harvest should preserve self-containment.
