---
number: 0118
target: /backend
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/wave3_g8.rs
status: open
---

# Harvest tests/legacy/wave3_g8.rs into cranelisp-backend unit tests

## Issue

The Sprint 64 test-port quarantined this file because its assertions
test Rust-internal state with no e2e equivalent: Layer-3 integration
observations of platform-registry removal (Sprint 57 Wave 3 / G8) —
`platform_fn_ptr` and `scheduling_class` directly on
`ModuleEntry::Def`, exercised through `ReplSession` / `CompilerSession`
Rust API. Per the two-tier strategy
(`memory/project_test_strategy.md`), these belong as
`#[cfg(test)]` unit tests inside the owning crate.

## Proposed resolution

- Read each of the 9 tests in `tests/legacy/wave3_g8.rs`.
- Translate into `#[cfg(test)]` modules inside
  `crates/cranelisp-backend/src/` adjacent to the platform-fn-pointer
  write path.
- Use cranelisp-frontend's `parse` + `build_program` for AST input
  per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — do NOT
  hand-construct AST.
- When complete, delete `tests/legacy/wave3_g8.rs` and remove its
  row from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until
it lands, the assertions are inert (the file is not compiled). The
FIXME blocks no other work — but the longer it sits, the further
the internal surface drifts from the quarantined shape and the more
rewrite the harvest requires.
