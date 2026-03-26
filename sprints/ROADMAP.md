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

## Forward Plan

| Sprint | Theme | Key Features | Skills | Dependencies |
|--------|-------|-------------|--------|--------------|
| ~~22~~ | ~~Module Caching~~ | ~~Done~~ | | |
| ~~23~~ | ~~Executable, Hot-Reload & REPL Lifecycle~~ | ~~Done~~ | | |
| ~~24~~ | ~~HKT, Lazy Sequences & Terminal Styling~~ | ~~Done~~ | | |
| ~~25~~ | ~~Lenient Eval, Auto IO Scheduling & First-Class Operators~~ | ~~Done~~ | | |
