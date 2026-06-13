---
number: 0119
target: /qa
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/wave4_g9.rs
status: open
harvested_by: /dev int (S81 W-E)
---

## S81 W-E harvest (/dev int) — DONE; remaining action is /qa deletion

The 4 persistent-worker assertions are ported into
`src/session_v4.rs` `#[cfg(test)] mod persistent_worker_tests` as the
`harvest_*` cluster:
- `harvest_concurrent_register_many_modules_codegen_populated` (10-module
  concurrent register + per-defn `code.is_some()` codegen-population check)
- `harvest_per_worker_jit_isolation_across_sessions` (two live sessions +
  two-thread concurrency guard)
- `harvest_thread_scope_absent_outside_cfg_test` (the §11 close-gate grep)

The legacy file's park/wake, shutdown-under-load, concurrent-register, and
reload-during-compile scenarios were ALREADY covered by the pre-existing
`persistent_worker_tests` cluster (`persistent_worker_park_and_wake`,
`shutdown_under_load_no_panic`, `concurrent_register_module_two_modules_complete`,
`reload_during_compile_race_completes`) — not re-ported.

**Remaining action (/qa):** delete `tests/legacy/wave4_g9.rs` and remove its
row from `tests/legacy/README.md`. Git history preserves provenance.

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
