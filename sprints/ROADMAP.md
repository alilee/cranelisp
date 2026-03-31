# Cranelisp Delivery Roadmap

Delivery progress for the Cranelisp reimplementation. For technical scope per ring, see `design/arch/roadmap.md`. For quality gates, see `tests/plan/strategy.md`.

## Phases

| Phase | Description | Status |
|-------|-------------|--------|
| A | Extract: spec completion, architecture contracts, QA plan | COMPLETE |
| B | Scaffold: crate structure, interfaces, CLAUDE.md files, experience specs | COMPLETE |
| C | Ring 0 — Core: expressions, types, functions, let, if, match | COMPLETE |
| D | Ring 1 — Heap: strings, ADTs, closures, reference counting | COMPLETE |
| E | Ring 2 — Abstraction: traits, modules, constrained polymorphism | COMPLETE |
| F | Ring 3 — Meta: macros, derive, standard library | COMPLETE |
| G | Ring 4 — Effects: IO, platforms, parallelism, REPL, caching | — |
| H | Release Compiler: Tier 2 backend | — |

## Sprints

| Sprint | Scope | Status | Report |
|--------|-------|--------|--------|
| 0 | Foundation survey and planning — every skill validates and plans | COMPLETE | `sprints/archive/sprint-0.md` |
| 1 | Ring 0 — Core implementation | COMPLETE | `sprints/archive/sprint-1.md` |
| 2 | Ring 1 — Heap types, closures, RC (779 tests, gate PASS) | COMPLETE | `sprints/archive/sprint-2.md` |
| 3 | Vec (Ring 1 completion) + demo relocation — 487 tests, Ring 1 COMPLETE | COMPLETE | `sprints/archive/sprint-3.md` |
| 4 | Ring 2A — Traits & operator dispatch: 622 tests, 0 failures, gate PASS | COMPLETE | `sprints/archive/sprint-4.md` |
| 5 | Ring 2A completion — constrained poly, default methods, user traits, `!=`: 1177 tests, 0 failures, gate PASS | COMPLETE | `sprints/archive/sprint-5.md` |
| 6 | Ring 2B — module infrastructure, tech debt, RC scope-dec, traceability: 691 tests, 0 failures | COMPLETE | `sprints/archive/sprint-6.md` |
| 7 | Ring 2B completion — cross-module wiring, REPL qualified display, REPL chrome: 748 tests, 0 failures | COMPLETE | `sprints/archive/sprint-7.md` |
| 8 | QA catchup — test coverage for Rings 0-2B, traceability audit: 798 tests, 5 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-8.md` |
| 9 | Ring 2 gate + Ring 3 prep — RC fixes, Decision 17, macro architecture, function decomposition, float display: 807 tests, 0 failures, 0 ignored, 0 clippy, Ring 2 PASS | COMPLETE | `sprints/archive/sprint-9.md` |
| 10 | Ring 3 macro infrastructure (Phases 1-4) — synthetic macros module, marshal, quasiquote, defmacro, CraneliftExpander: 1446 tests, 0 failures, 0 clippy | COMPLETE | `sprints/archive/sprint-10.md` |
| 11 | Ring 3 pipeline integration (Phases 5-7) — CraneliftExpander wiring, D17 elimination, prelude loading mechanism, REPL macro commands, lib/→stdlib/ rename, stdlib governance: 1551 tests, 20 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-11.md` |
| 12 | Foundation fix — prelude loading (3 pipeline bugs), stdlib prelude (traits+macros+Option), CRANELISP_LIB env var, import-driven discovery, demo infrastructure, 8 demos (incl. 4x4 Sudoku solver), 18 examples, /docs survey: 959 tests, 20 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-12.md` |
| 13 | Catchup — 4 defect fixes (quasiquote, ADT RC, closure traits, trait introspection), 8 ignored tests fixed, 10 stubs deleted, multi-dot imports, deep qualified refs, bare macro introspection, defmacro special form, 13 FIXMEs resolved, 0 clippy: 985 tests, 0 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-13.md` |
| 14 | Ring 3 Complete — stdlib module tree (27 modules), exemplar pure core (4 modules, 4x4 Sudoku solver), string primitives (13), derive macro, REPL spec rewrite (universal output format, /list//imports//exports), 6 pipeline bugs fixed, gate review PASS: 1660 tests, 0 ignored, 0 failures. **Ring 3 COMPLETE.** | COMPLETE | `sprints/archive/sprint-14.md` |
| 15 | REPL Output Conformance — universal output format, /list//imports//exports rewrites, /exports new command, `__macro_*` private visibility fix, 50 new tests, spec traceability update: 1710 tests, 0 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-15.md` |
| 16 | Prior-Ring Debt + Ring 4A IO Foundation — IO ADT, trampoline, platform DLLs, `(print "hello")` end-to-end, platform governance, 2 review cycles (4B+10I resolved), spec-first QA process: 1833 tests, 9 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-16.md` |
| 17 | Ring 4B IO Sequencing — export mechanism, prelude remediation, do/bind! macros, lambda RC fix, showcase infrastructure: 1188 tests, 8 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-17.md` |
| 18 | Ring 4C REPL Hardening — prelude ADT display, type annotations, lambda+defn RC leak fix, runtime error spec §12.7, slash command tests, IO docs: 1269 tests, 21 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-18.md` |
| 19 | Ring 4D Developer Tools & Exemplar — 6 slash commands (/source /sexp /ast /clif /disasm /mod), REPL panic boundary (thread-local error flag), spec §8.11 lib dir clarification, exemplar batch mode fix, 2 demos, sprint showcase process: 1218 tests, 8 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-19.md` |
| 20 | Ring 4E Trace & Debt Clearance — trace special form (spec §4.12, codegen, runtime, stdlib), display format extraction (§12.9), borrowed-var RC fix, IO display fix, /mod conformance, exemplar IO, docs validation, Ring 3 traceability, Principle 10 (module-scoped special forms), sketch consultation: 1241 tests, 8 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-20.md` |
| 21 | Ring 4F Testing Infrastructure & Auto-Currying — auto-curry (typecheck+codegen+constrained poly fix), /run-tests REPL handler, run-tests codegen, stdlib testing helpers, cargo-llvm-cov coverage tooling (86.72% baseline), crate-vs-sketch audit, code quality review, repl.rs refactoring (5 modules), unsafe blocker fix, coverage gap analysis: 1609 tests, 11 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-21.md` |
| 22 | Module Caching & Spec Advancement — end-to-end module caching (.o generation + Linker loading + cascade invalidation + --no-cache), CompilationSession pipeline convergence, generic FnCompiler\<M: Module\>, non-Var auto-curry rejection, run-tests parser, trait method GOT fix, terminal styling spec, consolidated intrinsic symbols, flaky trace test fix, caching design addendum §13: 1312 tests, 9 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-22.md` |
| 23 | Executable, Hot-Reload & REPL Lifecycle — standalone executable (`--link`), file watching (eager recompile, cascade, error blocking), shell escape (`;#!`), session persistence (`user.cl` source regeneration + cache), REPL cache integration (trait/impl restore, macro recompile, TypeId fix), batch `main` requirement, demo trampoline, local file import, 5 FIXMEs resolved, 3 specs rewritten: 1411 tests, 4 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-23.md` |
| 23a | UAT Findings — primitive name scoping §8.9.1 (3 compiler bugs), duplicate param rejection, REPL trait constraint eagerness, cross-eval mono GOT, multi-module JIT name collisions, constrained type display §3.5.1, test infrastructure redesign (prelude/preamble fixtures, single-pipeline helpers), QA process overhaul (failing tests > #[ignore]): 1211 tests, 4 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-23a.md` |
| 24 | HKT, Lazy Sequences & Terminal Styling — higher-kinded types (TyConApp unification, HKT traits/impls, method resolution), lazy sequences (Seq ADT, 4 producers, 9 consumers), S-expression pretty-printer (syntax highlighting, Lisp indentation), checked division (§12.7.3), batch→GOT bridge (stdlib fn-as-value fix), comment preservation (Sexp::Comment), --no-color flag, 2 examples, ring4i demo, 6 review findings fixed: 1441 tests, 0 ignored, 0 failures | COMPLETE | `sprints/archive/sprint-24.md` |
| 25 | Lenient Eval, Auto IO Scheduling & First-Class Operators — lenient evaluation (IVar runtime, sparkability analysis, barrier-force codegen, rayon thread pool), auto IO scheduling (bind-chain independence analysis, Expr::ParBind, trampoline Par handler with resource token serialization), trait methods as first-class values (§7.6 — operator closure wrapping), pretty-printer bold for constructors, demo player interactive controls, 61 clippy warnings fixed, 6 FIXMEs resolved (2 were 2x deferred), 2B+4I review findings fixed: 1475 tests (1474 passed, 1 failed), 0 ignored, 0 clippy | COMPLETE | `sprints/archive/sprint-25.md` |
| 26 | Pipeline Convergence — unified `TypeChecker::check()`, deleted ReplInput/ReplCheckResult, merged Defn/DefnMulti, CompileContext, compile_unit(), 47 v1-vs-v2 comparison tests, multi-sig typecheck+codegen (not end-to-end), 3 architectural principles (11-13), v1 docs archived: 1528 passed, 11 failed (sketch_port — triaged), 0 ignored, 0 clippy | COMPLETE | `sprints/archive/sprint-26.md` |
| 27 | Pipeline Switchover Design — §8 rewritten (two-caller model, recursive compile_unit, PipelineDepth), §15 added (5 remaining v1 paths). Design-only. | COMPLETE | `sprints/archive/sprint-27.md` |
| 28 | Pipeline Switchover Implementation — compile_unit() owns all 7 stages, --run + --link + test helper through compile_unit(), CodegenTarget enum, CacheWriter background .o, ~650 lines deleted. REPL deferred. | COMPLETE | `sprints/archive/sprint-28.md` |
| 29 | Pipeline v3 Step 1 — Decouple codegen from compile_unit: compile_unit() returns after stage 5, new codegen_and_execute() for stages 6-7, CompileUnitResult/CodegenResult split, 13 call sites updated, 2 dead transitional functions deleted, /review I1 fixed: 1533 tests, 11 pre-existing sketch_port failures, 0 ignored, 0 warnings | COMPLETE | `sprints/archive/sprint-29.md` |
| 30 | Pipeline v3 Step 2 — CodegenItem queues: CodegenItem struct, inmem_queue/object_queue on CompilationSession, flush_inmem_queue()/flush_object_queue(), all v2 call sites converted (run_batch_v2, compile_for_link_v2, load_prelude_for_link, compile_and_run), Step 1.5 dead code cleanup dropped (functions not dead), /review 0B 3I 4S (I1+S2 fixed): 1533 passed, 11 pre-existing sketch_port failures, 0 ignored, 9 pre-existing clippy warnings | COMPLETE | `sprints/archive/sprint-30.md` |
| 31 | Pipeline v3 Steps 3+4 — CompileMode removal + platform prescan absorption: deleted CompileMode enum (125 refs/16 files), session.interactive + got_slots.is_some() replace, compile_program use_got:bool API, PlatformSpec type, platform_specs on ModuleStructure, extract_module_declarations recognizes (platform ...), compile_unit stage 2d loads DLLs, project_root on CompilationSession, prescan loops deleted, 4 frontend tests added, /review 0B 4I 5S (I1+I2 fixed): 1533 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-31.md` |
| 32 | Pipeline v3 Step 5 — Prelude auto-loading: load_dependencies extended to import+export union via &ModuleStructure, auto-prelude trigger in compile_unit stage 2b (4-guard condition), ~135 lines deleted (run_batch_v2 prelude block + load_prelude_for_link function), /review 0B 3I 3S (I1+I2 fixed): 1533 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-32.md` |
| 33 | Pipeline v3 Step 6 — Collapse orchestration into main: run_batch_v2 inlined into run_file_inner(), compile_for_link_v2 inlined into link_file_inner(), both deleted from pipeline_v2.rs (~205 lines), LinkCompileResult deleted, pipeline_v2.rs now just compile_unit + stage helpers, /review 0B 3I 3S (I2+I3+S2 fixed): 1533 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-33.md` |
| 34 | Pipeline v3 Step 7 — Decompose CompilationSession: InMemWorkerState (4 fields), ObjectWorkerState (5 fields), V1State (5 fields) extracted from 24-field CompilationSession, pipeline core (10 fields) retained, boundary verified (compile_unit_inner/load_dependencies don't touch worker state), option (a) convention-based separation, /review 0B 1I 3S (I1 compile_checked_program signature deferred): 1533 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-34.md` |
| 35 | Pipeline v3 Step 8 — ModuleDependencyGraph: imports/dependents/file_to_module on CompilationSession, edges registered incrementally in compile_unit (3 sites), REPL file_to_module/module_dependencies migrated, find_transitive_dependents simplified (reverse map), build_file_to_module_map + build_module_dependency_map deleted, /review 2B fixed 1I 2S: 1533 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-35.md` |
| 36 | Pipeline v3 Step 9 — REPL migration to compile_unit: eval routes through compile_unit + codegen_and_execute, ~815 lines of v1 REPL pipeline deleted (eval_sexp, eval_flattened_forms, eval_defmacro, eval_import, eval_platform, compile_and_execute, execute_*, TracedCompiledExpr), eval_annotation_expr + reload_single_module refactored to v3, all 8 architectural invariants verified, /review 0B 0I 6S: 1533 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-36.md` |
| 37 | Pipeline v3 Step 10 — File watcher cascade: transitive_dependents on ModuleDependencyGraph, clear_module_state/recompile_module/recompile_module_and_dependents on CompilationSession, reload_changed_modules simplified to delegation, reload_single_module/find_transitive_dependents/clear_module_state deleted from REPL, /review 0B 0I 3S (behavioral equivalence verified): 1533 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-37.md` |
| 38 | Pipeline v3 Step 14 — Delete v1 dead code: compile_module_graph/compile_module_graph_cached rewritten to compile_unit (53 test sites), 5 REPL v1 callers migrated, 1,293 lines deleted from pipeline.rs (4,055→2,762), V1State + 17 functions + 3 structs deleted, single-pipeline invariant fully established, 4 cache-hit tests ignored (v2 cache-hit loading not yet implemented): 1643 passed, 23 pre-existing failures, 4 ignored | COMPLETE | `sprints/archive/sprint-38.md` |
| 39 | Pipeline v3 Step 11 foundation — codegen decoupled from CompilationSession: codegen_and_execute + 6 helpers refactored to free functions taking worker state params, CodegenPacket Send-safe, send_codegen/flush_codegen API, CodegenMode enum (Sync/Async), single async worker thread as proof of concept. Full N-core pools deferred to Sprint 40: 1643 passed, 23 pre-existing failures, 4 ignored | COMPLETE | `sprints/archive/sprint-39.md` |
| 40a | Pipeline v3 — Parallel compile_unit and N-Core Codegen: CANCELLED. Partial waves 1-3 (check &self, compile_unit &self, CodegenQueue). Build broken. | CANCELLED | `sprints/archive/sprint-40a.md` |
| 40 | Pipeline v4 Steps 0+1 — Build recovery, v4 CompilerSession skeleton (`--v4` flag), per-form typecheck API (`check_form`/`FormCheckResult`/`ModuleCheckAccumulator`), 28 new tests, design doc: 1733 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-40.md` |
| 41 | Pipeline v4 Steps 2+3 — CompileScheduler (module lifecycle, priority ladder, waiter/unblock, 17 API methods), form-by-form worker loop (two-pass typecheck, post-typecheck codegen sweep), `--v4 --run` for primitive-only programs, Sprint 40 I-1/I-2/I-3 debt resolved, /review 0B 3I 5S (all I fixed): 1574 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-41.md` |
| 42 | Pipeline v4 Step 4 — Macro expansion blocking: per-sexp Pass 2 with inline macro compilation, Decision 21 (TC-sourced call graph, `callees: Vec<FQSymbol>` on ModuleEntry), C2 filter relaxation, begin-splicing, spec clarification (macro availability vs compilation), 10 new macro parity tests, /review 0B 4I 6S (all I fixed): 1684 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-42.md` |
| 43 | Pipeline v4 Steps 5+6 — Lazy dependency discovery + MacroExpander removal: WorkerContext, FormKind/classify_form, handle_import/export/mod/platform, prelude injection (uniform lazy path), cycle detection (blocked_on walk), C2 filter deleted, MacroExpander trait + CraneliftExpander + NoOpExpander deleted, frontend API cleaned (24 functions), MacroEnv standalone, 11 new v4 parity tests, /review 0B 2I 5S (all fixed): 31 v4 pipeline tests, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-43.md` |
| 44 | Pipeline v4 Step 7 — REPL eval via scheduler: serial per-form processing, ModuleStrategy::Additive on process_module_forms, eval_v4/run_repl_v4, bare-symbol introspection, no interceptions (annotations/trace/macros handled by language machinery), ~250 lines dead code deleted, scheduler leak fix, 8 E2E REPL tests + 7 unit tests, /review 0B 3I 4S (all I fixed): 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-44.md` |
| 45 | Pipeline v4 Steps 8+9 — PlatformRegistry (FQSymbol keys, unified fn_ptr+scheduling_class, bind_chain_analysis migration) + Error Cascade (reset_module/reset_all_failed_modules, cascade embeds original error, impl From, REPL recovery) + cross-module macro dep fix (compile_dep_symbol_inline uses dep module path/table/CheckResult) + 2 FIXMEs resolved, /review 0B 2I 4S (R1-R4 fixed, R5 deferred), 21 new tests, FIXME(/spec) on §9.2.5: 11 pre-existing sketch_port failures, 1 ignored | COMPLETE | `sprints/archive/sprint-45.md` |
| 46 | Pipeline v4 Step 10 — Nice workers for object codegen: Mutex<SchedulerState> + 3 condvars, scheduler &mut→&self migration, Arc<SharedState>, nice_worker_loop with .o + .meta.json compilation (ObjectCodegenInput stash, build_object_compile_input, compile_module_to_object, write_cached_metadata), object_working double-claim prevention, thread_util.rs extraction, self-promote pattern (AtomicBool), run_with_nice_workers scoped threads, cache in all modes, stash-before-notify race fix, §9.2.5 FIXME restored without codegen concern, /review 2B+6I+5S (all B+I fixed), 6 new scheduler tests: 1570 passed, 11 pre-existing sketch_port failures, 0 ignored | COMPLETE | `sprints/archive/sprint-46.md` |

## Forward Plan

### Pipeline v3 migration — COMPLETE (Sprints 29-38)

Steps 1-10 + 14 delivered. Single-pipeline invariant established. ~2,100 lines of v1 code deleted. Steps 11-13 (concurrency) deferred indefinitely. Step 15 (new main.rs) retired — substantially delivered by Step 6. See `design/arch/pipeline-v3-roadmap.md` §Post-Migration for full assessment.

### Pipeline v4 migration — IN PROGRESS (Sprint 40+)

Scheduler-driven concurrent compilation. See `design/arch/pipeline-v4-roadmap.md` for the 15-step migration plan.

| Sprint | Theme | Scope | Skills |
|--------|-------|-------|--------|
| 40 | v4 Steps 0+1 — skeleton + per-form typecheck | Build recovery, CompilerSession wrapper, --v4 flag, check_form API | `/int`, `/typecheck`, `/qa` |
| 41 | v4 Steps 2+3 — scheduler + worker loop | CompileScheduler, form-by-form worker loop, --v4 --run for primitives | `/int`, `/typecheck`, `/arch`, `/qa`, `/review` |
| 42 | v4 Step 4 — macro expansion blocking | Per-sexp expansion, inline compile-and-continue, Decision 21 call graph, C2 filter | `/int`, `/typecheck`, `/arch`, `/qa`, `/review`, `/spec` |
| 43 | v4 Steps 5+6 — lazy deps + expander cleanup | Lazy dependency discovery, MacroExpander trait removal, C2 filter deleted | `/int`, `/frontend`, `/arch`, `/qa`, `/review` |
| 44 | v4 Step 7 — REPL eval via scheduler | Serial per-form eval, additive strategy, bare-symbol introspection, no interceptions | `/int`, `/qa`, `/review` |
| 45 | v4 Steps 8+9 — platform registry + error cascade | PlatformRegistry, error cascade, reset_module, cross-module macro dep fix | `/int`, `/qa`, `/review`, `/arch` |
| 46 | v4 Step 10 — nice workers for object codegen | Scheduler Mutex+condvars, nice_worker_loop, .o compilation, scoped threads | `/int`, `/arch`, `/qa`, `/review` |
| 47+ | v4 Steps 11-15 — concurrency + cleanup | Multi-thread priority workers, DashMap, cache-hit loading, watcher, legacy delete | All skills |

### Ring 4 acceptance criteria gap analysis

Ring 4 acceptance criteria from `design/arch/roadmap.md` vs current state:

| Criterion | Status | Sprint |
|-----------|--------|--------|
| `(print "hello")` produces IO effect | DONE (S16) | |
| `(do ...)` chains IO effects | DONE (S17) | |
| Lenient evaluation parallelises independent bindings | DONE (S25) | |
| Platform DLLs load and function | DONE (S16) | |
| Module caching: second compilation hits cache | **GAP** — writes cache, does not load from cache | 39 |
| Standalone executable generation (`--link`) | DONE (S23) | |
| REPL: all slash commands work | DONE (S19-21) | |
| Hot-reload: file changes auto-reload in REPL | DONE (S23, migrated S37) | |
| `(trace (fib 5))` execution tracing | DONE (S20) | |
| `(run-tests ...)` test runner | DONE (S21) | |
| All ~470 portable integration tests from prototype pass | **GAP** — 23 pre-existing sketch_port failures, needs triage | 41+ |
| All E2E transcript tests pass | Partial — 1643 passing, 23 failures | 41+ |
| Performance within 2x of prototype | **NOT MEASURED** — needs benchmarking after cache-hit | 41+ |
| REPL experience test suite passes | Partial — core experience works, coverage gaps in edge cases | 41+ |
| Exemplar project compiles, runs, passes tests | **GAP** — exemplar exists but not fully validated | 41+ |
| `cargo clippy` clean across all crates | DONE (maintained since S9) | |

### Phase G (Ring 4) remaining work after Sprint 40

The pipeline rebuild is done. The remaining Ring 4 work is feature completion and validation:
1. Cache-hit loading (Sprint 39) closes the biggest functional gap
2. REPL cleanup (Sprint 40) closes the last structural debt
3. Sketch-port test triage (23 failures) — determine which are real gaps vs sketch-specific behaviors
4. Performance benchmarking — establish baseline, compare to sketch
5. Exemplar validation — full end-to-end run of the Sudoku solver exemplar
6. REPL experience edge cases — coverage gaps in spec conformance
7. Ring 4 gate review — formal review before advancing to Phase H
