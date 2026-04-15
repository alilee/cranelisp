# Sprint 54: Clean & Green

**Status**: ACTIVE
**Ring**: 4 (Effects — full spec scope)
**Goal**: Zero test failures — triage and fix all 58 failures to establish a clean baseline for Ring 4 gate review.

## Scope

Sprint 53 fixed the workspace build (backend API conformance, broken call site repairs) and unmasked 29 additional failures. Sprint 53 also silently fixed 7 tests (default methods, parse-int, constructor-as-value, batch scoping) via backend API changes. The true failure inventory is 58 tests across 8 categories:

| Category | Count | Owner | Confirmed Root Cause |
|----------|-------|-------|---------------------|
| Trace | 22 | /backend | Conflicting intrinsic signature: `cranelisp_trace_restore_got` declared with return in jit.rs, void in trace_codegen.rs |
| Cache SIGSEGV/FAIL | 12 | /backend + /int | Cross-module GOT crash with nice_workers=1; transitive deps: GOT data symbols not registered |
| File watching E2E | 11 | /int | `notify` v7 uses kqueue on macOS (not FSEvents); kqueue directory watches miss file modifications |
| Link | 5 | /backend | Object files export module-qualified `hello/main` but startup stub expects unqualified `main` |
| Multi-sig batch | 3 | /int | `pre_register_got_slots_in_tc` and `compile_regular_defns` in worker.rs don't skip DefnMulti |
| Checked division | 3 | /int | `compile_and_execute_expr` in pipeline.rs doesn't check `take_runtime_error()` after JIT call |
| Persistence | 1 | /int | `compile_dep_inline` takes `repl_check_state` but doesn't restore on error path |
| run-tests | 1 | /backend + /int | `run-test`/`discover-tests` extern primitives declared but no runtime function implemented |

### Triage Ownership Summary

- **/backend**: 39 tests (trace 22, cache 12, link 5) + run-tests runtime implementation
- **/int**: 19 tests (watch 11, multi-sig 3, checked-div 3, persistence 1, run-tests wiring 1)
- **/typecheck**: 0 tests (multi-sig is in worker.rs, not typecheck)

### FIXME Debt

All source code FIXMEs resolved. No blocking debt.

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| (none in source) | — | All S53 FIXMEs resolved | resolved |

### Prior-Ring Coverage Gaps

~25 spec requirements from completed rings (R0-R3) still carry `[R{N} S{M}]` tags. Noted but not blocking Sprint 54.

### Out of Scope

- Ring 4 gate review (Sprint 55 — after clean baseline)
- Prior-ring spec traceability updates (Sprint 55)
- Performance benchmarking
- Phase H (Tier 2 backend)

## Architecture Review

**Reviewer**: /arch
**Verdict**: APPROVED

**Technical coherence**: PASS. 8 failure categories cleanly partitioned. Shared-ownership items resolved via triage before implementation. Wave structure sound.

**No interim architecture**: PASS. All tasks are fixes to existing subsystems. No new abstractions proposed.

**Design references**: Adequate. Each skill plan cites correct source locations. Design doc "n/a" is correct for bug fixes — triage findings serve as design artifacts.

**Interface gaps**: None. Bug fixes don't require boundary type changes.

**Risk assessment**:
| Category | Risk | Rationale |
|----------|------|-----------|
| Trace (22) | **Low** | Single root cause in jit.rs intrinsic declaration |
| Cache SIGSEGV (12) | **High** | Could be race condition or fundamental .o loading issue |
| File watching (11) | **Medium** | Platform-specific watcher backend; fix is clear but fiddly |
| Link (5) | **Low** | Clear cause: module-qualified name vs unqualified expectation |
| Multi-sig (3) | **Low** | Add `is_multi_sig()` guard in 2 places |
| Checked div (3) | **Low** | Add `take_runtime_error()` check |
| Persistence (1) | **Low** | Restore state before `?` operator |
| run-tests (1) | **Medium** | Missing runtime function implementation |

**Conditional**: If cache SIGSEGVs require architectural changes to .o loading path, descope cache+link (17 tests) to Sprint 55.

## Skill Plans

### /backend
**Task**: Fix 3 confirmed failure categories (39 tests) + run-tests runtime:
- (A) **Trace (22 tests)**: Add `cranelisp_trace_restore_got` to void-return exception list in `declare_intrinsics_generic` (jit.rs:617), alongside `runtime/vec_drop`.
- (B) **Cache SIGSEGV (12 tests)**: Investigate whether setting `nice_workers: 0` eliminates SIGSEGVs (isolates race vs logic bug). For transitive imports: ensure `load_cached_module_object` registers GOT data symbols for ALL modules including transitive deps.
- (C) **Link (5 tests)**: Fix module-qualified `main` export. Either always export `main` without prefix, or have `generate_startup_object` use qualified name.
- (D) **run-tests runtime**: Implement `run-test` and `discover-tests` functions in cranelisp-runtime and register in JIT builder symbol table.
**Design doc**: n/a (bug fixes — triage findings above serve as design)
**Design refs**: `crates/cranelisp-backend/src/jit.rs:617`, `crates/cranelisp-backend/src/compiler/trace_codegen.rs:71`, `crates/cranelisp-backend/src/lib.rs:88`, `crates/cranelisp-backend/src/exe.rs:50`, `src/worker.rs:2619-2681`
**Acceptance**: All trace (22), cache (12), link (5) tests pass. 0 SIGSEGVs. run-test/discover-tests symbols resolvable.

### /int
**Task**: Fix 5 confirmed failure categories (19 tests):
- (A) **Watch (11 tests)**: Replace `RecommendedWatcher` with `notify::FsEventWatcher` on macOS via `#[cfg(target_os = "macos")]` in `src/watch.rs:36-42`.
- (B) **Multi-sig (3 tests)**: Add `if defn.is_multi_sig() { continue; }` in `pre_register_got_slots_in_tc` (worker.rs:2475) and `compile_regular_defns` (worker.rs:2555).
- (C) **Checked-div (3 tests)**: Add `take_runtime_error()` check after JIT call in `compile_and_execute_expr` (pipeline.rs:129) and trace variant (~line 180).
- (D) **Persistence (1 test)**: Move `repl_check_state` restore before `?` in `compile_dep_inline` (session_v4.rs:1771).
- (E) **run-tests wiring (1 test)**: Wire v4 pipeline to use the runtime functions once /backend implements them.
**Design doc**: n/a (bug fixes)
**Design refs**: `src/watch.rs`, `src/worker.rs`, `src/pipeline.rs`, `src/session_v4.rs`
**Acceptance**: All watch (11), multi-sig (3), checked-div (3), persistence (1), run-tests (1) tests pass.

### /typecheck
**Task**: No tasks — multi-sig triage confirmed the bug is in worker.rs (/int territory), not in typecheck.

### /arch
**Task**: Architecture review of sprint scope and triage findings.
**Acceptance**: COMPLETE — reviewed and approved.

### /qa
**Task**: (A) Validate all fixes against spec. (B) Update spec annotations for newly-passing tests. (C) Run full suite to confirm 0 failures.
**Design doc**: n/a
**Design refs**: `spec/*.md`, `repl/spec.md`, all test files
**Acceptance**: 0 failures, 0 ignored. Spec annotations current.

### /review
**Task**: Code review of all bug fixes. Two review passes: one after Wave 3, one after Wave 4 fix cycle.
**Acceptance**: 0 Blockers, all Important findings addressed.

### /frontend
**Task**: No primary assignment.

### /repl
**Task**: (A) Create sprint demo `repl/demos/ring4l.demo`. (B) Verify all prior demos play cleanly.
**Design refs**: `repl/demos/CLAUDE.md`
**Acceptance**: Demo plays cleanly. All prior demos pass.

### /port
**Task**: Validate exemplar compiles and runs after fixes.
**Acceptance**: Exemplar batch mode runs.

### /examples
**Task**: Verify all examples compile and run.
**Acceptance**: All `examples/*.cl` run successfully.

### /stdlib
**Task**: Validate stdlib compiles after fixes.
**Acceptance**: All stdlib modules compile.

### /spec
**Task**: Update spec annotations for newly-passing tests.
**Acceptance**: Annotations current.

### /docs, /platform
**Task**: No primary assignment.

## Waves

### Wave 1: Triage (no code changes) — COMPLETE

Root cause investigation for each failure category. All 8 categories triaged with confirmed root causes and ownership.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Architecture review of sprint scope | **done** | APPROVED with cache descope conditional |
| /backend | Triage cache SIGSEGVs | **done** | Race condition or GOT symbol registration; HIGH risk |
| /backend | Triage link failures | **done** | Module-qualified name mismatch; LOW risk |
| /backend | Triage trace | **done** | Intrinsic signature conflict in jit.rs; /backend-owned |
| /backend | Triage checked-div | **done** | Missing take_runtime_error() check; /int-owned |
| /typecheck | Triage multi-sig batch | **done** | worker.rs issue, not typecheck; /int-owned |
| /int | Triage watch | **done** | kqueue vs FSEvents on macOS |
| /int | Triage persistence | **done** | repl_check_state not restored on error |
| /int | Triage run-tests | **done** | Missing runtime function implementation |

### Wave 2: Arch Review of Triage Findings — COMPLETE

/arch reviewed sprint scope and approved. Triage findings embedded in skill plans above.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review triage findings, confirm approaches | **done** | APPROVED; cache descope conditional |

### Wave 3: Design docs (sequential — each builds on prior decisions)

Five design docs for the remaining 32 tests. Sequenced so decisions cascade correctly.

| # | Skill | Design Doc | Scope | Status | Notes |
|---|-------|-----------|-------|--------|-------|
| 3a | /int + /backend | Codegen convergence | Delete `codegen_module_symbols`, route JIT through `compile_to_module` | pending | Fixes multi-sig (3 tests). Principle 11. Must land before link design. |
| 3b | /backend + /arch | `"user"` special-casing removal + link startup | Audit all `"user"` special-casing, GOT-indirect startup stub | pending | Fixes link (5 tests). Depends on 3a (single codegen path). |
| 3c | /int | Cache / nice_worker interaction | Investigate SIGSEGV root cause, document fix, restructure test helpers | pending | 12 tests. Depends on 3a (codegen convergence may affect nice worker path). |
| 3d | /int + /qa | Watch test design + watcher status | Outcome-based tests, assess watcher implementation | pending | 11 tests. Independent but benefits from test helper patterns in 3c. |
| 3e | /arch + /frontend + /backend | run-tests / discover-tests special forms | Separate testing from tracing, spec the codegen | pending | 1 test. Independent. Design doc revision. |

### Wave 4: Arch review of design docs

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review all 5 design docs for coherence | pending | |

### Wave 5: Implementation (Tier 1 fixes + design doc implementations)

Tier 1 fixes (26 tests) picked up here alongside Tier 2/3 implementations approved by /arch.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | Fix trace intrinsic signature (jit.rs) | pending | 22 tests |
| /int | Fix checked-div: add runtime error check + rewrite tests | pending | 3 tests |
| /int | Fix persistence: module resolution path ordering | pending | 1 test |
| /int + /backend | Implement codegen convergence per design 3a | pending | 3 tests |
| /backend | Implement link fix per design 3b | pending | 5 tests |
| /int | Implement cache fix per design 3c | pending | 12 tests (if scope allows) |
| /int + /qa | Implement watch per design 3d | pending | 11 tests (if scope allows) |
| | run-tests per design 3e | pending | 1 test (likely deferred to S55) |

### Wave 6: Build/Test/Review (iterative)

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Run full suite, validate fixes | pending | |
| /qa | Update spec annotations | pending | |
| /review | Review all code changes | pending | |

### Wave 7: Showcase

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Create sprint demo | pending | |
| /repl | Verify all prior demos | pending | |
| /port | Validate exemplar | pending | |

## Notes

**Wave 1 triage review — confirmed actions:**

1. **Trace (22 tests)**: Add `has_return: bool` field to `IntrinsicSymbol` struct (jit.rs:69). Set correctly for each intrinsic in `intrinsic_symbols()`. Use in `declare_intrinsics_generic` instead of hardcoded `runtime/vec_drop` name check. Also fix `cranelisp_trace_enter` param_count from 3 to 4 (must match runtime signature). Owner: /backend.

2. **Cache SIGSEGV (12 tests)**: Pipeline bug — `CompilerSession` with `nice_workers >= 1` SIGSEGVs on multi-module projects during fresh compile (before any cache loading). Test helper restructuring needed: collapse `compile_cached` → `batch_run_file_cached` → `ReplSession` into a thin helper that calls `CompilerSession` APIs directly. Fix the underlying pipeline bug in `src/session_v4.rs` or `src/worker.rs`. Owner: /int (pipeline), /qa (test helpers).

   **Target test shape** (cache tests should read like this):
   ```rust
   let dir = project_from_sources(&[("main.cl", "..."), ("util.cl", "...")]);

   // Fresh compile works
   let r1 = run_entry(&dir, "main");
   assert_eq!(r1, 42);

   // Cache artifacts written
   assert_cache_exists(&dir, "util");

   // Cache-hit compile produces same result
   let r2 = run_entry(&dir, "main");
   assert_eq!(r2, 42);
   ```
   Where `run_entry` is one thin function: `CompilerSession::new(settings)` → `register_module()` → `trampoline()` with production-like settings (including `nice_workers: 1`). No `ReplSession` wrapper, no "batch" vs "cached" naming.

3. **Watch E2E (11 tests)**: These tests were never implemented — Sprint 52 confirms file watching E2E was never completed. They've been failing since creation. Additionally, the test design is wrong: tests check for `[updated: mymod.cl]` notification strings on stdout (REPL chrome), not for the actual effect of file watching (recompilation). Correct tests should verify the *outcome* — that changed code produces different results:
   ```rust
   let dir = project_from_sources(&[("main.cl", "..."), ("helper.cl", "(defn val [] 42)")]);
   let r1 = run_entry(&dir, "main");
   assert_eq!(r1, 42);

   // Modify source
   write(dir.join("helper.cl"), "(defn val [] 99)");

   // Re-run picks up change
   let r2 = run_entry(&dir, "main");
   assert_eq!(r2, 99);
   ```
   These need rewriting, not just fixing. Owner: /qa (test design), /int (watcher implementation if needed).

6. **Checked division (3 tests)**: Two problems. (a) Solution: `compile_and_execute_expr` (pipeline.rs:129) doesn't check `take_runtime_error()` after JIT execution — `runtime_panic` stores the error in a thread-local and returns 0, but nobody reads it. Fix: add `take_runtime_error()` check after JIT call, return `Err` if set. (b) Test design: tests use `catch_unwind` expecting a Rust panic, but `runtime_panic` doesn't Rust-panic. Tests should assert `session.eval()` returns `Err` with the expected error message, not rely on `catch_unwind`. Owner: /int (pipeline.rs fix), /qa (rewrite tests).

7. **Persistence (1 test)**: `persist_import_survives_restart` fails at session 1 — `(import [helper [helper-val]])` produces no output at all. REPL shows `0+0ms` (no prelude compilation time) then no results. Other tests using the same `run_repl_in_with_test_prelude` helper pass (e.g., `persist_defn_survives_restart`). The difference: the failing test imports a module from the temp dir while `CRANELISP_LIB` is set to `tests/fixtures/`. Module resolution may not search the working directory when `CRANELISP_LIB` is set. This is a solution bug in module resolution path ordering, not a test design issue. Owner: /int (module resolution in session_v4.rs).

8. **run-tests (1 test)**: `can't resolve symbol run-test` — JIT linker can't find the function. Per spec (appendix-a §A.4, repl/spec.md §16), `discover-tests` and `run-test` are **special forms** returning IO values — not extern runtime functions. `(discover-tests [module])` → `:(IO (SList Sexp))` scans symbol tables for `test-*` functions. `(run-test name)` → `:(IO TestResult)` calls a function by name via GOT. `TestResult` ADT (`TestPass`/`TestFail`) is spec'd. Trace and test are independent, composable features (§16: "use `(trace (test-fn))` separately"). The `PrimitiveKind::Extern` declarations in builtins.rs are wrong — these need `Expr` variants and codegen, like `trace`. The design doc (`design/backend/auto-curry-and-run-tests.md` §R1) conflates testing with tracing and needs revision. Fix: (a) change builtins.rs from Extern to proper special form registration, (b) add `Expr::DiscoverTests`/`Expr::RunTest` variants, (c) implement codegen — `discover-tests` builds SList from symbol tables at compile time, `run-test` emits GOT-indirect call + TestResult construction. Owner: /frontend (AST), /backend (codegen), /int (wiring). Feature implementation — defer from Sprint 54.

5. **Multi-sig batch (3 tests)**: `codegen_module_symbols` in worker.rs is a parallel JIT codegen path that duplicates `compile_to_module` in lib.rs. It misses multi-sig handling (panics on `defn.params()` for DefnMulti). The fix is NOT to add guards to worker.rs — it's to **delete `codegen_module_symbols` and route the JIT path through `compile_to_module`**, which is already generic over `M: Module` and handles multi-sig correctly. This is an Principle 11 (single pipeline) and Principle 7 (single source of truth) violation. Owner: /int (delete worker.rs codegen path), /backend (ensure `compile_to_module` covers JIT needs).

4. **Link (5 tests)**: Startup stub imports bare `_main` but .o exports `hello/main` (module-qualified). Root cause is deeper: `compile_to_module` (lib.rs:88) special-cases `"user"` and `"main"` module names to skip JIT prefixing. This leaks CLI naming conventions into the backend — the backend shouldn't know or care what the module is called. The correct model: `generate_startup_object` calls `main` through the entry module's GOT (like any cross-module call), not via a bare symbol import. Fix: (a) remove `"user"`/`"main"` special-casing from `compile_to_module`, (b) rewrite startup stub to use GOT-indirect call to entry module's `main`, (c) grep for other `"user"` special-casing outside `parse_args` and eliminate. Owner: /backend (exe.rs, lib.rs), /arch (review the "user" special-casing audit).

**Wave 1 findings (triage):**
- Multi-sig ownership shifted: /typecheck → /int (bug is in worker.rs, not typecheck crate)
- Checked-div ownership shifted: /backend → /int (bug is in pipeline.rs, not codegen)
- Trace confirmed as single root cause — intrinsic signature mismatch, not pipeline issue
- Cache SIGSEGVs may need descoping if architectural — /arch conditional approved
- Watch failure is platform-specific (macOS kqueue), not watcher architecture
- run-tests needs both /backend (implement runtime fns) and /int (wire into pipeline)

## Outcome

{Filled in when sprint closes}

### Delivered
- {completed tasks and artifacts}

### Deferred
- {tasks moved to next sprint with rationale}

### Findings
- {unexpected issues, skill feedback, architectural observations}
