---
number: 0116
target: /qa
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/scheduler.rs
status: open
harvested_by: /dev int (S81 W-E)
---

## S81 W-E harvest (/dev int) — DONE; remaining action is /qa deletion

The scheduler lifecycle assertions are ported into
`src/scheduler.rs` `#[cfg(test)] mod tests` as the `harvest_*` test cluster
(15 tests), translated against the CURRENT scheduler API. Three legacy tests
(`block_for_macro_codegen_adds_priority_entry`, `priority_codegen_complete_unblocks`,
`priority_queue_deduplicates_symbols`) were intentionally NOT ported — they
probed the `block_for_macro_codegen` + `BlockingJitCodegen` priority-codegen
subsystem that has been DELETED (the locked macro model has no empty-slot
pre-compile case). The coverage they held is dead with the subsystem.

**Remaining action (/qa):** delete `tests/legacy/scheduler.rs` and remove its
row from `tests/legacy/README.md`. Git history preserves provenance.

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
