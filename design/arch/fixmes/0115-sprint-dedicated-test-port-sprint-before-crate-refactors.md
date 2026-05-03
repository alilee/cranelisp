---
number: 0115
target: /sprint
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/plan/PLAN.md §"Migration policy", tests/plan/helpers.md §"Implementation phasing", design/arch/fixmes/0109-dev-int-decomposition-session-v4-worker-lib.md
status: open
---

# Sequence a dedicated test-port sprint before any crate-refactor sprint

## Issue

User decision (Sprint 64): the migration from current integration-tier tests (using `compile_and_run*`, `repl_session*`, inline `const &str` trait preludes) to the new e2e harness (`Cranelisp` builder per `tests/plan/helpers.md`) will be a **dedicated sprint**, not opportunistic rewrite-on-touch.

The sprint sequence:

1. **Build phase** — implement `tests/helpers/e2e.rs` (`Cranelisp` builder, `CrOutput`, regex helper library, toml/CLI configuration). Depends on FIXMEs 0110/0111/0112 landing in `/int`.
2. **Port phase** — port every test in `tests/` to the e2e harness; add or update each test's row in `tests/plan/PLAN.md` so coverage documentation builds in lockstep with the migration.
3. **Remove phase** — delete `tests/helpers/mod.rs::ReplSession` and the integration-tier scaffolding; delete or rewrite holdouts with explicit rationale.

Once Phases 1–3 complete, **then** crate-refactor sprints (FIXME 0109 — int decomposition splitting `session_v4.rs` and `worker.rs`; any other refactors that change internal session shapes) may begin. The lock-in: a refactor that shuffles `session_v4`/`worker` internals before tests are decoupled from those internals breaks the suite for many sprints, slowing every other concurrent skill.

## Proposed resolution

`/sprint` schedules:

1. **Sprint N+1** (or whichever is next available): the test-port sprint. Three phases as above.
2. **Sprint N+2 onward**: crate-refactor sprints (FIXME 0109 first; other refactors as scoped).

`/sprint` confirms with user before sequencing. Estimate: the test-port sprint is likely 1–2 sprints (depends on `tests/` size — currently `tests/e2e.rs` alone is ~2,700 LOC; total `tests/` likely 10k+ LOC of test bodies).

The FIXMEs that must land BEFORE the test-port sprint can begin Phase 1 (`/int` work):
- FIXME 0111 (trace channel separation) — required for `assert_stderr_traces_only` and the regex helper library's `compiler::trace_line()` discrimination.
- FIXME 0112 (REPL ready sentinel) — required for stdin scripting reliability.
- FIXME 0110 (Cranelisp.toml + CLI knobs for worker count, cache disable) — required for deterministic-ordering tests.

Sequencing options for `/sprint`:
- (a) Bundle FIXMEs 0110/0111/0112 into the test-port sprint's Phase 0.
- (b) Land them in the prior sprint as preparatory `/int` work.
- (c) A small `/int`-only sprint dedicated to the three FIXMEs, immediately preceding the test-port sprint.

`/qa`'s soft preference: (b) or (c). The test-port sprint is large enough on its own; pre-landing the binary surface gives the port phase a stable target.

## Operational implication / Context

The methodology change here is significant: the project's test-migration approach was previously framed as opportunistic (per recently-updated `tests/plan/PLAN.md`); this FIXME captures the user's revision to dedicated-sprint sequencing.

Once the test-port sprint completes, the test suite is fully e2e-tier or unit-tier (per `memory/project_test_strategy.md`), and crate refactors can proceed without the "if I touch X, will it break a test that mocks Y?" friction.

Sprint order matters more than sprint contents here: the lock-in is about NOT scheduling a crate-refactor sprint before the test-port sprint completes. `/sprint` enforces.
