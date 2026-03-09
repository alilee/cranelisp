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
