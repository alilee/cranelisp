# Sprint 21: Ring 4F — Testing Infrastructure & Auto-Currying

**Status**: COMPLETE
**Ring**: 4 (Effects) — sixth increment
**Goal**: Implement `(run-tests init pass-fn fail-fn)` special form, auto-currying, coverage metrics tooling, and conduct crate-vs-sketch architecture audit with code quality review.

## Scope

Sprint 20 delivered trace end-to-end and cleared all 3x-deferred debt. This sprint closes the testing infrastructure loop (trace → run-tests → stdlib testing helpers → exemplar test suite), fills the auto-currying gap (4 ignored tests since Sprint 17), adds code coverage metrics tooling, and audits the reimplementation crates against the sketch.

### Features

| # | Feature | Owner(s) | Description |
|---|---------|----------|-------------|
| A1 | Auto-currying: typecheck detection | /typecheck | Detect partial application in `infer_apply`. Emit `ResolvedCall::AutoCurry`. Spec §4.6.3. |
| A2 | Auto-currying: codegen | /backend | `compile_auto_curry` — closure wrapper capturing applied args. In `compiler/apply.rs`. |
| A3 | Auto-currying: REPL integration | /int | Wire through REPL eval; curried closures display correctly. |
| R1 | `(run-tests init pass-fn fail-fn)` codegen | /backend | Discover `test-*` fns, GOT-swap tracing per test, fold via pass/fail fns. In `compiler/trace_codegen.rs`. |
| R2 | `/run-tests` slash command | /int | REPL handler for run-tests. Discover `.test` modules, invoke codegen, display results. |
| R3 | `cranelisp_trace_first_child_nanos` | /platform | Runtime extern: extract nanos from first child trace frame (per-test timing). |
| S1 | Testing stdlib helpers | /stdlib | `run-tests-pass-default`, `run-tests-fail-default`, `run-tests-report` in `stdlib/testing.cl`. |
| S2 | `str-eq` prelude export | /stdlib | Add missing `str-eq` to prelude exports. |
| P1 | Exemplar test suite | /port | `.test` submodules for exemplar using testing assertions. Validate with `/run-tests`. |
| Q1 | Coverage metrics tooling | /qa | Set up `cargo-llvm-cov`. Layer-by-layer reports (unit/integration/E2E). Document in `tests/CLAUDE.md`. |
| Q2 | Sprint test coverage | /qa | Un-ignore 4 auto-curry tests. Port ~9 run-tests tests. Write negative tests. |
| Q3 | Spec traceability update | /qa | Update §4.6.3 annotations from IGNORED to Tested. |
| X1 | Crate-vs-sketch audit + code quality review | /arch + /review | For each reimplementation crate: (a) compare against sketch counterpart — features missing/divergent, rationale for divergences, gaps in hard-won design knowledge; (b) code quality review — structure, naming, error handling, function decomposition, test coverage, technical debt. Output: `design/arch/sketch-audit.md` + `design/review/crate-quality.md`. |

### Audit Remediation (added post-Wave 0)

| # | Feature | Owner(s) | Description |
|---|---------|----------|-------------|
| B1 | Fix `CompiledExpr::execute()` unsafe | /backend | Blocker: safe fn wraps `unsafe { transmute }`. Mark as `unsafe fn`, update all call sites. |
| B2 | Fix `str_as_str` in frontend tests | /frontend | Unlock workspace-wide coverage — remove unstable feature gate from one test line in `ast_builder.rs`. |
| B3 | repl.rs refactoring | /int | Split `src/repl.rs` (3283 lines) into modules: session, commands, display, eval. Sketch had 5 REPL files. |
| B4 | Coverage gap investigation | /qa | Analyze unit + integration coverage gaps. Identify uncovered code paths. Prioritize and write missing tests or file FIXMEs for coverage-blocking code structure issues. |

### Out of Scope

- HKT (3 ignored tests) — Ring 5+
- Lazy sequences (1 ignored test) — Ring 5+
- Module caching (Sprint 22)
- Multi-sig + auto-currying + constrained poly interaction (known gap, defer)

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `repl/spec.md:839` | /repl | Terminal styling | Carry — cosmetic |
| `spec/10-io.md:52` | /spec | resource_token for Par | Carry — Par not in scope |
| `.claude/commands/platform.md:73` | /platform | stderr write | Carry — evaluate later |

## Architecture Review

**Status: Wave 0 complete.** Sketch audit and code quality review delivered.

### Sketch Audit Summary (`design/arch/sketch-audit.md`)
- Reimplementation has strong structural improvements over sketch (7-crate DAG, string newtypes, CompileContext, scope stack, decomposed codegen)
- Missing subsystems are all future-sprint scope (cache, scheduling, Par, exe, hot-reload)
- Risk: `repl.rs` (3283 lines) and `lib.rs` (2317 lines) need decomposition
- Auto-curry codegen is a stub — ready for A2 implementation

### Code Quality Summary (`design/review/crate-quality.md`)
- 3 Good (types, frontend, runtime), 4 Needs Attention (typecheck, backend, platform, src/)
- **1 Blocker**: `CompiledExpr::execute()` is safe fn wrapping unsafe transmute
- **6 Important**: repl.rs size, unwrap calls, functions >100 lines, no platform tests, unused dep

### Coverage Baseline
- **72.97%** combined line coverage (root crate only — workspace blocked by `str_as_str` in frontend tests)
- `repl.rs` accounts for 69% of uncovered lines
- Documented in `tests/CLAUDE.md`

## Skill Plans

### /arch
**Task**: (X1) Crate-vs-sketch architecture audit. For each reimplementation crate (`cranelisp-types`, `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-runtime`, `cranelisp-platform`) and `src/` (integration binary): compare against corresponding sketch code. Document: (a) features present in sketch but missing in reimplementation, (b) divergences from sketch approach, (c) whether divergences are justified or represent gaps. Also review auto-curry and run-tests designs.
**Output**: `design/arch/sketch-audit.md` — one section per crate with findings table.
**Acceptance**: Audit complete. Each crate has findings. Auto-curry + run-tests designs approved.

### /review
**Task**: (X1) Code quality review of each reimplementation crate. Assess: structure, naming, error handling, function decomposition (flag >100 lines), unsafe code, test coverage adequacy, technical debt. Rate each crate (Good / Needs Attention / Needs Rework). Also review auto-curry and run-tests code with sketch comparison checks.
**Output**: `design/review/crate-quality.md` — one section per crate with quality summary and actionable findings.
**Acceptance**: Every crate reviewed. Findings classified B/I/S. 0 Blockers, 0 Important unresolved for sprint code.

### /typecheck
**Task**: (A1) Auto-curry detection. When `infer_apply` finds fewer args than params, record in overload resolution and emit `ResolvedCall::AutoCurry`. Study sketch `src/typechecker/overloads.rs`.
**Design doc**: Required — with sketch comparison section.
**Design refs**: `spec/04-expressions.md` §4.6.3, `sketch/src/typechecker/overloads.rs`
**Acceptance**: 4 auto-curry tests pass.

### /backend
**Task**: (A2) `compile_auto_curry` in `compiler/apply.rs` — replace existing stub error. (R1) `compile_run_tests` in `compiler/trace_codegen.rs`. Study sketch `src/codegen/trace.rs:452-700` and `src/codegen/apply.rs`.
**Design doc**: Required — with sketch comparison sections for both features.
**Design refs**: `spec/04-expressions.md` §4.6.3, `sketch/src/codegen/apply.rs`, `sketch/src/codegen/trace.rs`
**Acceptance**: (A2) `(let [f (add 1)] (f 2))` → 3. (R1) run-tests discovers and executes test functions.

### /platform
**Task**: (R3) `cranelisp_trace_first_child_nanos` extern fn in `cranelisp-runtime/src/trace.rs`.
**Acceptance**: Callable from JIT, returns correct nanos.

### /int
**Task**: (A3) Auto-curried closure display in REPL. (R2) `/run-tests` slash command handler.
**Acceptance**: (A3) Curried values show as closures. (R2) `/run-tests` works at REPL with pass/fail output.

### /qa
**Task**: (Q1) Install `cargo-llvm-cov`, configure workspace coverage, generate layer-by-layer reports, document in `tests/CLAUDE.md`. (Q2) Un-ignore 4 auto-curry tests, port ~9 run-tests tests, write auto-curry negative tests. (Q3) Update spec §4.6.3 annotations.
**Acceptance**: (Q1) `cargo llvm-cov --workspace --html` produces report; `tests/CLAUDE.md` has Coverage section. (Q2) ~15 new/un-ignored tests pass. (Q3) Spec annotations updated.

#### Coverage Tooling Detail (Q1)

**Setup**: `cargo install cargo-llvm-cov` + `rustup component add llvm-tools-preview`

**Layer commands**:
| Layer | Command |
|-------|---------|
| Unit (crate internals) | `cargo llvm-cov --lib --workspace --html --output-dir coverage/unit` |
| Integration (ring tests) | `cargo llvm-cov --test ring0 --test ring1 --test ring2 ... --html --output-dir coverage/integration` |
| API (REPL tests) | `cargo llvm-cov --test repl_experience --test repl_negative --html --output-dir coverage/api` |
| E2E (binary subprocess) | `cargo llvm-cov --test e2e --test examples --test exemplar --html --output-dir coverage/e2e` |
| Combined | `cargo llvm-cov --workspace --html --output-dir coverage/all` |

**Known limitations to document**:
- Measures Rust compiler code coverage, not JIT-emitted code paths
- E2E tests invoke subprocess — subprocess profiling requires `LLVM_PROFILE_FILE` env var propagation
- Serial RC tests may need `--test-threads=1` coordination
- `coverage/` directory should be gitignored

### /stdlib
**Task**: (S1) `stdlib/testing.cl` — `run-tests-pass-default`, `run-tests-fail-default`, `run-tests-report`. Import `Trace` from primitives. (S2) `str-eq` prelude export.
**Acceptance**: Testing helpers importable and work with run-tests fold pattern.

### /port
**Task**: (P1) Write `.test` submodules for exemplar (at least `grid.test`, `form.test`).
**Acceptance**: `/run-tests` discovers and runs exemplar tests.

### /repl
**Task**: Create `repl/demos/ring4f.demo` — auto-currying + `/run-tests`.
**Acceptance**: Demo plays cleanly. All prior demos verified.

### /examples
**Task**: Verify all examples. Optional: `examples/curry.cl` for partial application.
**Acceptance**: All examples pass.

### /docs
**Task**: Validate auto-curry and run-tests in user docs.
**Acceptance**: Docs reflect working features.

### /spec, /frontend
**Task**: No changes expected. Respond to any FIXMEs filed.

## Waves

### Wave 0: Audit + Design + Coverage Setup
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | X1: Crate-vs-sketch architecture audit → `design/arch/sketch-audit.md` | done | 416 lines, 7 areas audited |
| /review | X1: Crate code quality review → `design/review/crate-quality.md` | done | 1B, 6I findings |
| /typecheck | Study sketch auto-curry; write design notes with sketch comparison | done | `design/typecheck/auto-curry.md` |
| /backend | Study sketch compile_auto_curry + compile_run_tests; write design notes | done | `design/backend/auto-curry-and-run-tests.md` |
| /arch | Review auto-curry + run-tests designs | done | APPROVED — add total_count to AutoCurry enum |
| /qa | Q1: Install cargo-llvm-cov, establish baseline coverage | done | 72.97% baseline |

**Gate**: Audit documents complete. /arch approves designs. Baseline coverage numbers recorded.

### Wave 1: Auto-Currying
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | A1: Auto-curry detection in inference + resolve_overloads | done | Fixed callee_ty lookup bug |
| /backend | A2: compile_auto_curry closure wrapper | done | RC-correct: inc captures, drop glue |
| /int | A3: REPL integration for curried values | done | Tests updated for auto-curry behavior |
| /qa | Q2 partial: Un-ignore 4 auto-curry tests, write negative tests | pending | 4 tests ready to un-ignore |
| /review | Review auto-curry code (sketch comparison) | pending | |

**Gate**: 4 auto-curry tests pass + negatives pass.

### Wave 2: Run-Tests
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /platform | R3: cranelisp_trace_first_child_nanos extern | done | Already implemented |
| /backend | R1: compile_run_tests codegen | done | ~350 lines, 8 helper methods |
| /int | R2: /run-tests slash command handler | done | Direct invocation, /run-tests + /rt shortcut |
| /stdlib | S1: testing helpers. S2: str-eq export | done | testing/runner.cl created. str-eq export reverted (not in primitives module) |
| /qa | Q2 partial: Port ~9 run-tests tests | pending | |
| /review | Review run-tests code (sketch comparison) | pending | |

**Gate**: `/run-tests` works at REPL with test discovery and pass/fail output.

### Wave 3: Showcase + Coverage Report
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /port | P1: Exemplar .test submodules | deferred | Needs frontend parser for (run-tests ...) form |
| /repl | ring4f.demo | done | 25-line demo: auto-curry + /run-tests |
| /examples | Verify all examples; optional curry example | done | 24 pass + new 25-curry.cl |
| /docs | Validate docs | done | Demo docs updated |
| /qa | Q1 completion: Document coverage in tests/CLAUDE.md. Q3: Spec traceability | done | 86.72% baseline documented, §4.6.3 [Tested+Neg] |
| /review | Sprint 21 code review | done | PASS with 5I, 8S. design/review/sprint-21-review.md |

## Notes

- **B1 done**: `CompiledExpr::execute()` + `TracedCompiledExpr::execute()` marked `unsafe fn`. Call sites updated with SAFETY comments.
- **B2 done**: Fixed `str_as_str` in frontend test (line 2035: `name.as_str()` → `&**name`). Workspace coverage unlocked: **86.72%** (up from 72.97% root-only).
- **Workspace coverage baseline**: 86.72% line coverage, 86.00% function coverage. Key gaps: repl.rs (56%), backend builtins.rs (52%), operators.rs (5%), platform crates (0%).
- **Scope expanded post-Wave 0**: Added B1-B4 (audit remediation) per user request — blocker fix, str_as_str, repl.rs refactoring, coverage gap investigation.
- **A1+A2 done**: Auto-curry typecheck + codegen implemented. Fixed bug: `apply_subst_callee` used scope stack lookup (missed module-registered defns); fixed by passing already-inferred `callee_ty` to `try_auto_curry`. 3 negative tests updated to expect auto-curry success. 4 ignored auto-curry tests now pass when run with `--ignored`. Net +3 tests.
- **B4 done**: Coverage gap investigation → `tests/plan/coverage-gaps.md`. 86.72% baseline, ~128 tests could reach ~90.7%.
- **R1+R2+R3 done**: run-tests codegen (350 lines, 8 helpers), /run-tests REPL handler (direct invocation, /rt shortcut), runtime extern already existed.
- **S1 done**: `stdlib/testing/runner.cl` — check macro, run-tests-pass-default/fail-default/report. S2 reverted (str-eq not in primitives module).
- **Q2+Q3 done**: 6 E2E tests for /run-tests (passing), 6 integration tests for run-tests special form (#[ignore] — needs frontend parser support). Spec §4.6.3 updated to [Tested+Neg].
- **B3 done**: repl.rs split into 5 files under `src/repl/`: mod.rs (2104), commands.rs (1004), trace.rs (224), run_tests.rs (167), io_format.rs (50). All tests pass.
- **Test count**: 1609 passing, 11 ignored (4 HKT/lazy + 6 run-tests form + 1 other), 0 failures.
- **Constrained auto-curry bug FIXED**: `(+ n)` inside constrained poly fns failed at codegen — `AutoCurry` stored abstract name `"+"` but mono compilation needed concrete `"add-i64"`. Fix: added `trait_resolution: Option<Box<ResolvedCall>>` to `AutoCurry`, deferred trait resolution in `resolve_auto_curry()`, and `recheck_body_for_mono()` now captures auto-curry resolutions. Cross-skill fix spanning types/typecheck/backend — justified as tightly coupled defect during build/test/review cycle. FIXME(/qa) filed for test coverage, FIXME(/spec) filed for documentation.
- **ring4f.demo**: `map` not in prelude scope — demo needs adjustment. Constrained auto-curry now works.

## Outcome

### Delivered
- **A1-A3**: Auto-currying end-to-end — typecheck detection (`try_auto_curry` on unification failure), codegen (RC-correct wrapper with drop glue), REPL integration. 6 tests (4 un-ignored + 2 negatives).
- **Constrained auto-curry**: Fixed interaction between auto-curry, trait dispatch, and monomorphisation. `(+ n)`, `(defn make-adder [n] (+ n))` → `(make-adder 10)` → closure → `42`. Added `trait_resolution` field to `ResolvedCall::AutoCurry`.
- **R1-R3**: `compile_run_tests` codegen (350 lines, 8 helpers, unrolled loop with GOT-swap), `/run-tests` REPL handler (direct invocation, `/rt` shortcut, pass/fail reporting), `cranelisp_trace_first_child_nanos` (already existed).
- **S1**: `stdlib/testing/runner.cl` — `check` macro, `run-tests-pass-default`, `run-tests-fail-default`, `run-tests-report`.
- **Q1**: `cargo-llvm-cov` installed, workspace coverage baseline **86.72%**, layer-by-layer commands documented in `tests/CLAUDE.md`.
- **Q2**: 6 auto-curry tests + 6 E2E run-tests tests + 6 ignored run-tests form tests. Spec §4.6.3 updated to `[Tested+Neg]`.
- **X1**: Crate-vs-sketch architecture audit (`design/arch/sketch-audit.md`). Code quality review (`design/review/crate-quality.md`) — 3 Good, 4 Needs Attention, 1B/6I.
- **B1**: `CompiledExpr::execute()` → `unsafe fn` (Blocker fix).
- **B2**: `str_as_str` fix unlocked workspace-wide coverage (86.72% vs 72.97% root-only).
- **B3**: `src/repl.rs` (3283 lines) → `src/repl/` module directory (5 files: mod.rs, commands.rs, trace.rs, run_tests.rs, io_format.rs).
- **B4**: Coverage gap analysis (`tests/plan/coverage-gaps.md`) — ~128 tests to reach ~90.7%.
- **Sprint code review**: PASS with 5I, 8S (`design/review/sprint-21-review.md`).
- **Showcase**: `repl/demos/ring4f.demo` (auto-curry + /run-tests with pass/fail), `examples/25-curry.cl`.
- **1609 tests passing** (up from 1241), **11 ignored** (4 HKT/lazy + 6 run-tests form + 1 doctest), **0 failures**.

### Deferred
- **P1** (exemplar .test submodules) — needs frontend parser for `(run-tests ...)` form expression syntax. `/run-tests` slash command works; the `Expr::RunTests` AST path needs frontend wiring.
- **S2** (`str-eq` prelude export) — reverted; `str-eq` is an operator implementation, not registered in primitives module. Use `(= s1 s2)` via Eq trait instead.
- **Review findings I1-I5** — non-Var auto-curry edge case (I2), run-tests drop glue gaps (I4/B1), `emit_single_test_iteration` param count (I1). See `design/review/sprint-21-review.md`.
- **FIXME(/qa)**: Constrained auto-curry test coverage (trait method curry, constrained fn curry).
- **FIXME(/spec)**: §4.6.3 needs constrained polymorphism interaction documented.

### Findings
- **Constrained auto-curry is a cross-cutting concern**: The fix required changes in types (new field on `AutoCurry`), typecheck (deferred resolution, mono recheck), and backend (wrapper dispatch). This is inherent — the feature spans inference, monomorphisation, and codegen.
- **Scope stack vs module lookup**: `apply_subst_callee` using scope stack lookup missed module-registered defns. Fixed by passing the already-inferred `callee_ty`. This pattern (env lookup ≠ module lookup) is a recurring source of bugs in the typecheck crate.
- **Coverage tooling reveals structural gaps**: `repl.rs` (56%) accounts for 69% of missed lines. The refactoring into 5 modules improves maintainability but coverage requires direct unit tests of command handlers (structured for testability but not yet tested in-process).
- **Sketch as oracle**: The sketch correctly handles constrained auto-curry. The reimplementation's initial implementation missed this because the design doc deferred the constrained interaction, and tests only covered concrete types. Sketch consultation caught the gap.
- **`str_as_str` blocked workspace coverage**: A single unstable feature use in one test line blocked coverage measurement for all 6 sub-crates. Infrastructure issues like this should be caught in CI.
