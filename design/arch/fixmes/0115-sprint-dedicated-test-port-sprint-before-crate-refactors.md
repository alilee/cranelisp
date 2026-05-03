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

1. **Sprint 64**: the test-port sprint. Three phases as above (Build / Port / Remove). All-`/qa`, no `/int` Phase 0.
2. **Sprint 65 onward**: crate-refactor sprints (FIXME 0109 first; other refactors as scoped).

### Phase 0 collapse (Sprint 64 scoping conversation, 2026-05-03)

The original framing required `/int` to land FIXMEs 0110 (toml/CLI knobs), 0111 (trace channel separation), 0112 (REPL ready sentinel) before Phase 1 could begin. **All three retired** during scope review (this sprint):

- **0111** retired — traces are debugging aids without spec basis. Trace-shaped assertions belong in `/dev` unit tests inside the owning crate, not in `/qa` e2e tests. Stderr discipline reduces to "no trace flag set → stderr empty / spec-error-only", which needs no channel tagging.
- **0112** retired — pipe-all-stdin then parse-stdout-after-exit covers every realistic e2e need. The "send-then-wait-then-send" request/response pattern was speculative; no concrete test case requires it. Prompt-splitting via `compiler::repl_prompt()` regex separates form outputs in piped runs.
- **0110** retired — fresh per-test `TempDir` (already harness discipline) means cache-hit testing is test orchestration (run binary twice in same tmpdir), not a binary knob. Worker-count knob was justified by scheduler-trace tests, which by 0111 belong in `/dev`. `[repl] show_times = false` was justified by byte-stable `assert_stdout_eq`; regex-based parsing absorbs prompt timing decoration without needing the knob.

Net: Sprint 64 is pure `/qa`. The harness builds against existing binary surface. Genuine `/int` blockers discovered during port (e.g., binary writes cache outside CWD breaking tmpdir isolation, if observed) file as new targeted FIXMEs.

## Operational implication / Context

The methodology change here is significant: the project's test-migration approach was previously framed as opportunistic (per recently-updated `tests/plan/PLAN.md`); this FIXME captures the user's revision to dedicated-sprint sequencing.

Once the test-port sprint completes, the test suite is fully e2e-tier or unit-tier (per `memory/project_test_strategy.md`), and crate refactors can proceed without the "if I touch X, will it break a test that mocks Y?" friction.

Sprint order matters more than sprint contents here: the lock-in is about NOT scheduling a crate-refactor sprint before the test-port sprint completes. `/sprint` enforces.
