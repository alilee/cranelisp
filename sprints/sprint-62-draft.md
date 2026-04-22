# Sprint 62: Concurrency Audit + `loom` + Structured Interleaving Tests

**Status**: DRAFT (authored by /sprint at Sprint 61 close 2026-04-22, pending user approval to open as `sprints/SPRINT.md`)

**Ring**: 4 (Effects — stabilisation continuation)

**Goal**: Replace Sprint 61's stress-run verification with sound race-closure proof methodology. Audit every shared-state access site in `crates/cranelisp-typecheck/` + `src/scheduler.rs` + `src/worker.rs` + `src/session_v4.rs`. Adopt `loom` (Rust's permutation model checker) for critical shared-state operations. Author structured interleaving tests that deterministically force race windows rather than hoping stress triggers them. Precondition for Sprint 63+: the 7 ledgered carries from S61 honestly resolve (not carry) — either fixed by the audit work, or dispositioned as architectural limitations with explicit rationale.

## Scope

Sprint 61 closed with three scheduler race mechanisms closed (H4/H5/H6) but with:
- One H6 residue (`heisenbug_race_reduced_concurrent_import_pairs` at 5-10% under 6-thread contention).
- One harness ceiling concern (`io_trace_off_path_subprocess_completes_within_generous_ceiling`).
- Five escaped exemplar-gap carries (4× `d6_exemplar_*` + `wave6_demo_repros::exemplar_solver_*`) — pre-existing 81-cell solver stack overflow.
- A methodology gap: stress-run verification is low-statistical-power and fails to prove races closed.

S62 addresses the first two via audit + loom + structured tests. The escaped exemplar carries are /port + /backend ownership; may fold into S62 or a separate slice depending on root cause overlap with audit findings.

### Three workstreams

1. **Audit** — enumerate every shared-state access site. For each: operation, lock held, atomicity class (atomic / under-lock / relaxed / racy), invariant required, current implementation status. Output: `design/int/concurrency-audit.md` with a full table. Targets:
   - `crates/cranelisp-typecheck/` — `self.modules`, `symbol_tables`, `impl_registry`, any other DashMap/Mutex state.
   - `src/scheduler.rs` — all `SchedulerState` fields, pool transitions, condvar patterns.
   - `src/worker.rs` — `handle_import`, `register_dep`, priority-worker claim loop.
   - `src/session_v4.rs` — `register_dep_for_eval`, `wait_module_inmem_complete_blocking`, `SharedState` access.

2. **`loom` adoption** — introduce `loom` for the race-critical shared-state operations. Write tests: each test encodes "thread A does X, thread B does Y, assert invariant I". Loom enumerates interleavings up to a bounded depth. Candidates for first targets:
   - `ensure_module_exists` — the Slice 3 H6 fix site. Loom should prove the atomic-entry pattern has no residual race.
   - `register_dep` publish-before-register discipline (Slice 3 H5 site).
   - `try_unblock_locked` + `eval_in_flight` flag coordination.

3. **Structured interleaving tests** — for race windows loom can't cover (e.g., where the interleaving depth exceeds practical loom bounds, or where tests involve subprocess spawning), author tests that use `std::sync::Barrier` + atomic phase-markers to force specific interleavings. Replaces the Wave 3 stress-style tests where appropriate.

### Out of Scope (deferred with rationale)

- **FQTypeName migration** — displaced from S62 by the methodology pivot. Slides to S63+. No concurrency dimension; can land any time after audit.
- **Escaped exemplar-gap carries** (5× `d6_exemplar_*` + `wave6_demo_repros::exemplar_solver_*`) — pre-existing 81-cell stack overflow. May fold into S62 if audit uncovers a related root cause; otherwise separate slice or S63+.
- **Performance baseline** — Ring 4 AC `Performance within 2x of prototype` still unmeasured.
- **Stdlib prelude monolith remediation** — S63+.
- **Phase H / Tier 2 release backend** — post-Ring-4.

### Precondition gates

- Sprint 61 committed (all five waves: `b140ec5`, `35062ca`, `776a6cf`, `e20a7fa`, `dbe4bac`).
- Sprint 61 archived to `sprints/archive/sprint-61.md` and ROADMAP updated.
- User approval to open S62.

## Slices (draft)

Slice 0 — Audit
Slice 1 — `loom` integration + first-target tests
Slice 2 — Structured interleaving tests for non-loom-coverable sites
Slice 3 — H6 residue follow-through (apply audit findings + loom verification)
Slice 4 — Harness-robustness cleanup + remaining S61 I-1 deferrals
Slice 5 — Showcase + methodology documentation + close

(Detailed per-slice scope + wave structure authored at S62 Phase 1.)

## Notes

- Three S61 /review Importants fold into S62 scope: Wave 1 I-1 (reset_panic_hook_installed_for_tests Mutex<()>), Wave 2 I-1 (test helper consolidation continuation), Wave 3 I-1 (counter_non_zero hedge replaced by loom).
- The audit itself may uncover new races. Per S61's "every new finding gets a failing test" discipline — each such finding gets a regression guard, either fixed in S62 or ledgered honestly with a concrete plan.
- S61's evidence-gated cycle discipline (reduction → evidence → hypothesis → /arch → fix → evidence) is proven. S62 applies the same pattern where races still fire; loom + audit replace stress as the proof method where they fire no longer.

## Skill plans

TBD at Phase 2 (/arch review) + Phase 3 (skill planning).
