---
number: 0117
target: /typecheck
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/wave2_g6.rs
status: open
---

# Harvest tests/legacy/wave2_g6.rs into cranelisp-typecheck (and -backend) unit tests

## Issue

The Sprint 64 test-port quarantined this file because its assertions
test Rust-internal state with no e2e equivalent: Layer-3 integration
observations of `Code { ptr }` writes onto `ModuleEntry::Def` via the
`CodeFinalizer` trait (Sprint 57 Wave 2 / G6) — exercised through
`ReplSession` / `CompilerSession` Rust API. Per the two-tier strategy
(`memory/project_test_strategy.md`), these belong as
`#[cfg(test)]` unit tests inside the owning crates.

Primary owner: `/typecheck` (the `ModuleEntry::Def` shape and
SymbolTable contract). Secondary participant: `/backend` (the
`CodeFinalizer` write path). The 9 tests should split between the
two crates by which layer the assertion observes.

## Proposed resolution

- Read each of the 9 tests in `tests/legacy/wave2_g6.rs`.
- Translate the SymbolTable / ModuleEntry shape assertions into
  `#[cfg(test)]` modules inside `crates/cranelisp-typecheck/src/`.
- Translate the `CodeFinalizer` write-path assertions into
  `#[cfg(test)]` modules inside `crates/cranelisp-backend/src/`.
- Use cranelisp-frontend's `parse` + `build_program` for AST input
  per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — do NOT
  hand-construct AST.
- When complete, delete `tests/legacy/wave2_g6.rs` and remove its
  row from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until
it lands, the assertions are inert (the file is not compiled). The
FIXME blocks no other work — but the longer it sits, the further
the internal surface drifts from the quarantined shape and the more
rewrite the harvest requires.
