# Sprint 54: Clean & Green

**Status**: DRAFT
**Ring**: 4 (Effects — full spec scope)
**Goal**: Zero test failures — triage and fix all 58 failures to establish a clean baseline for Ring 4 gate review.

## Scope

Sprint 53 fixed the workspace build (backend API conformance, broken call site repairs) and unmasked 29 additional failures. Sprint 53 also silently fixed 7 tests (default methods, parse-int, constructor-as-value, batch scoping) via backend API changes. The true failure inventory is 58 tests across 8 categories:

| Category | Count | Owner | Root Cause Hypothesis |
|----------|-------|-------|-----------------------|
| Trace | 22 | /backend or /int | Trace codegen broken after session restructure — likely one root cause |
| Cache SIGSEGV/FAIL | 12 | /backend | Memory corruption in .o loading / JIT relocation path |
| File watching E2E | 11 | /int | E2E test subprocess environment (prelude/primitives availability, watcher timing) |
| Link | 5 | /backend | Likely related to cache — same .o loading path |
| Multi-sig batch | 3 | /typecheck | `Defn::params()` panics on `DefnMulti` in batch codegen |
| Checked division | 3 | /backend or /int | Checked div codegen or panic handler wiring |
| Persistence | 1 | /int | Import restart — module resolution in temp dir |
| run-tests | 1 | /int | `run-tests` special form not wired in v4 pipeline |

### Failure Detail

**Trace (22 tests)**:
- `ring4_trace::trace_*` (19 tests) — trace codegen, field access, composability
- `sketch_port::sketch_trace_literal_returns_trace_call` — trace return type
- `sketch_port::sketch_trace_nanos_is_positive` — trace timing field
- `v4_repl_eval::v4_repl_trace_as_expression` — trace in REPL context

**Cache (12 tests)**:
- SIGSEGV (8): `cache_multi_module_hit_cross_module_call`, `cache_multi_module_multiple_imports`, `cache_multi_module_two_deps`, `cache_multi_module_unchanged_dep_stays_cached`, `cache_multi_module_with_prelude`, `cache_repl_incremental_monomorphisation`, `cache_quick_build_links_cached_objects`, `cache_repl_restart_cache_hit`
- FAIL (1): `cache_multi_module_transitive_imports` — unresolved GOT symbol
- sprint23 (2): `cache_repl_loads_on_startup`, `cache_repl_produces_object_files`
- v4_pipeline (1): `v4_cache_hit_dependency`

**File Watching (11 tests)**:
- `watch_automatic_recompilation`, `watch_detects_source_change`, `watch_cascade_invalidation`, `watch_invalidates_cache_on_change`, `watch_notification_format`, `watch_notification_deferred_during_input`, `watch_type_incompatibility_on_reload`, `watch_notification_truncation`, `watch_error_display_format`, `watch_error_recovery_last_known_good`, `watch_retry_on_next_change`

**Link (5 tests)**:
- `link_hello_world_produces_executable`, `link_main_returns_int_exit_code`, `link_reuses_cached_object_files`, `link_multi_module_project`, `link_default_output_is_entry_stem`

**Multi-sig (3 tests)**:
- `sketch_multi_sig_different_arities`, `sketch_multi_sig_type_based_dispatch`, `sketch_repl_multi_sig_different_arities`

**Checked Division (3 tests)**:
- `ring0::checked_division_by_zero_panics`, `ring0::checked_div_min_neg1_panics`, `sketch_port::sketch_checked_division_by_zero_panics`

**Persistence (1 test)**: `persist_import_survives_restart`

**run-tests (1 test)**: `sketch_run_tests_pass_fn_called`

### /int Burden Assessment

/int owns 13 tests directly (11 watch + 1 persistence + 1 run-tests). Trace (22) and checked-div (3) need triage to determine if they're /backend (codegen) or /int (pipeline wiring). Cache (12) and link (5) are /backend.

This is feasible because: (a) watch failures are likely one or two root causes in E2E test infrastructure, (b) trace failures are likely one root cause in trace codegen after session restructure, (c) cache SIGSEGVs are the main risk but are all in one subsystem.

### FIXME Debt

All 5 source code FIXMEs from the prior Sprint 54 draft were resolved in Sprint 53. No `FIXME()` markers remain in `src/`, `crates/`, or `tests/`.

Design doc FIXMEs remain (in `design/int/`, `design/backend/`) but these are future-work notes, not blocking debt.

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| (none in source) | — | All 5 S53 FIXMEs resolved | resolved |

### Prior-Ring Coverage Gaps

~25 spec requirements from completed rings (R0-R3) still carry `[R{N} S{M}]` tags. These are traceability gaps, not missing features. Noted but not blocking Sprint 54 — priority is 0 failures.

### Out of Scope

- Ring 4 gate review (Sprint 55 — after clean baseline)
- Prior-ring spec traceability updates (Sprint 55)
- Performance benchmarking
- Phase H (Tier 2 backend)

## Architecture Review

{To be filled by /arch during Wave 2}

## Skill Plans

### /backend
**Task**: Fix 3 failure categories + triage trace:
- (A) Cache SIGSEGV (12 tests): investigate .o loading / JIT relocation / GOT init path for memory corruption. 8 SIGSEGVs suggest use-after-free or bad relocation in cached module loading.
- (B) Link (5 tests): likely shares root cause with cache — both use .o loading path. Investigate after cache fix.
- (C) Trace codegen (shared with /int): if trace failures are codegen-level (Cranelift IR generation for trace special form), /backend owns. If pipeline wiring, /int owns. Triage determines.
- (D) Checked division (3 tests): if codegen-level panic handler emission, /backend owns.
**Design doc**: n/a (bug fixes — triage notes in Wave 1)
**Approach**: {to be filled by /backend during Wave 1 triage}
**Design refs**: `crates/cranelisp-backend/src/cache/`, `src/session_v4.rs` (nice worker .o path), `design/backend/compile-to-module.md`
**Acceptance**: All cache (12), link (5), and owned trace/checked-div tests pass. 0 SIGSEGVs.

### /typecheck
**Task**: Fix multi-sig batch path (3 tests):
- `Defn::params()` panics on `DefnMulti` in batch codegen path. REPL path was fixed in S52 (`check_repl_multi_sig`). Batch path needs same treatment.
**Design doc**: n/a (regression fix)
**Approach**: {to be filled by /typecheck during Wave 1 triage}
**Design refs**: `crates/cranelisp-typecheck/src/`, `spec/05-definitions.md` §5.1.2
**Acceptance**: All 3 multi-sig tests pass.

### /int
**Task**: Fix 3 failure categories + triage shared issues:
- (A) File watching E2E (11 tests): investigate subprocess test environment — CRANELISP_LIB env, prelude/primitives availability in child process, watcher timing.
- (B) Persistence (1 test): `persist_import_survives_restart` — module resolution in temp dir after session restart.
- (C) run-tests (1 test): `run-tests` special form needs v4 pipeline wiring.
- (D) Trace triage (shared): if trace failures are pipeline wiring (trace not routed through compile_unit), /int owns.
- (E) Checked-div triage (shared): if checked-div failures are panic handler wiring in v4, /int owns.
**Design doc**: n/a (bug fixes)
**Approach**: {to be filled by /int during Wave 1 triage}
**Design refs**: `src/session_v4.rs`, `src/worker.rs`, `repl/spec.md` §14 §15
**Acceptance**: All watch (11), persistence (1), run-tests (1), and owned trace/checked-div tests pass.

### /arch
**Task**: Architecture review of sprint scope and triage findings.
**Acceptance**: Architecture review complete. No architectural concerns with proposed fixes.

### /qa
**Task**: (A) Validate all fixes against spec — confirm each test exercises the correct spec requirement. (B) Update spec annotations for newly-passing tests (including the 7 silently fixed by S53). (C) Run full suite to confirm 0 failures.
**Design doc**: n/a
**Approach**: Spec-first validation. Each passing test gets a `// spec:` trace and the corresponding spec gets `[Tested ...]`.
**Design refs**: `spec/*.md`, `repl/spec.md`, all test files
**Acceptance**: 0 failures, 0 ignored. Spec annotations current for all fixed tests.

### /review
**Task**: Code review of all bug fixes. Two review passes: one after Wave 3 implementation, one after Wave 4 fix cycle.
**Acceptance**: 0 Blockers, all Important findings addressed.

### /frontend
**Task**: No primary assignment. Validate after fixes.

### /repl
**Task**: (A) Create sprint demo `repl/demos/ring4l.demo`. (B) Verify all prior demos play cleanly.
**Design doc**: n/a
**Approach**: Demo showcases the fixes visible to users: trace working, multi-sig dispatch, cached modules, linked executables.
**Design refs**: `repl/demos/CLAUDE.md`
**Acceptance**: Demo plays cleanly. All prior demos pass.

### /port
**Task**: Validate exemplar compiles and runs after fixes.
**Acceptance**: Exemplar batch mode runs. Exemplar tests pass.

### /examples
**Task**: Verify all examples compile and run.
**Acceptance**: All `examples/*.cl` run successfully.

### /stdlib
**Task**: Validate stdlib compiles after fixes.
**Acceptance**: All stdlib modules compile.

### /spec
**Task**: Update spec annotations for newly-passing tests. Address any spec gaps discovered during triage.
**Acceptance**: Annotations current for fixed tests.

### /docs, /platform
**Task**: No primary assignment. Validate after fixes.

## Waves

### Wave 1: Triage (no code changes)

Root cause investigation for each failure category. This is the design-equivalent for a bug-fix sprint — understanding the root cause IS the design work. Each skill investigates their failures and documents findings.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Architecture review of sprint scope | pending | |
| /backend | Triage cache SIGSEGVs — reproduce, identify corruption source | pending | 12 tests |
| /backend | Triage link failures — relate to cache or independent | pending | 5 tests |
| /backend | Triage trace — codegen-level or pipeline-level? | pending | shared ownership |
| /backend | Triage checked-div — codegen or panic handler wiring? | pending | shared ownership |
| /typecheck | Triage multi-sig batch — confirm `Defn::params()` on `DefnMulti` | pending | 3 tests |
| /int | Triage watch — subprocess env or watcher architecture? | pending | 11 tests |
| /int | Triage persistence — temp dir module resolution | pending | 1 test |
| /int | Triage run-tests — v4 pipeline gap | pending | 1 test |

### Wave 2: Arch Review

/arch reviews triage findings and proposed approaches for all categories.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review triage findings, confirm approaches are architecturally sound | pending | |

### Wave 3: Implementation (parallel by skill)

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | Fix cache SIGSEGV root cause | pending | 12 tests |
| /backend | Fix link failures | pending | 5 tests |
| /backend | Fix trace codegen (if /backend-owned) | pending | up to 22 tests |
| /backend | Fix checked-div (if /backend-owned) | pending | up to 3 tests |
| /typecheck | Fix multi-sig batch path | pending | 3 tests |
| /int | Fix file watching E2E | pending | 11 tests |
| /int | Fix persistence import restart | pending | 1 test |
| /int | Wire run-tests in v4 pipeline | pending | 1 test |
| /int | Fix trace pipeline wiring (if /int-owned) | pending | shared |
| /int | Fix checked-div panic handler (if /int-owned) | pending | shared |

### Wave 4: Build/Test/Review (iterative)

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Run full suite, validate 0 failures | pending | |
| /qa | Update spec annotations for all fixed tests | pending | |
| /review | Review all code changes from Wave 3 | pending | |
| /backend | Address /review findings (B + I) | pending | |
| /typecheck | Address /review findings (B + I) | pending | |
| /int | Address /review findings (B + I) | pending | |

### Wave 5: Showcase

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Create `repl/demos/ring4l.demo` | pending | |
| /repl | Verify all prior demos play cleanly | pending | |
| /port | Validate exemplar compiles and runs | pending | |
| /examples | Verify all examples compile and run | pending | |
| /stdlib | Validate stdlib compiles | pending | |

## Notes

{Runtime log: blockers encountered, scope changes, decisions made}

## Outcome

{Filled in when sprint closes}

### Delivered
- {completed tasks and artifacts}

### Deferred
- {tasks moved to next sprint with rationale}

### Findings
- {unexpected issues, skill feedback, architectural observations}
