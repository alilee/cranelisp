# Cranelisp Delivery Roadmap

Delivery progress for the Cranelisp reimplementation. For technical scope per ring, see `design/arch/roadmap.md`. For quality gates, see `tests/plan/strategy.md`.

## Phases

| Phase | Description | Status |
|-------|-------------|--------|
| A | Extract: spec completion, architecture contracts, QA plan | COMPLETE |
| B | Scaffold: crate structure, interfaces, CLAUDE.md files, experience specs | COMPLETE |
| C | Ring 0 — Core: expressions, types, functions, let, if, match | COMPLETE |
| D | Ring 1 — Heap: strings, ADTs, closures, reference counting | COMPLETE |
| E | Ring 2 — Abstraction: traits, modules, constrained polymorphism | Next |
| F | Ring 3 — Meta: macros, derive, standard library | — |
| G | Ring 4 — Effects: IO, platforms, parallelism, REPL, caching | — |
| H | Release Compiler: Tier 2 backend | — |

## Sprints

| Sprint | Scope | Status | Report |
|--------|-------|--------|--------|
| 0 | Foundation survey and planning — every skill validates and plans | COMPLETE | `sprints/archive/sprint-0.md` |
| 1 | Ring 0 — Core implementation | COMPLETE | `sprints/archive/sprint-1.md` |
| 2 | Ring 1 — Heap types, closures, RC (779 tests, gate PASS) | COMPLETE | `sprints/archive/sprint-2.md` |
| 3 | Vec (Ring 1 completion) + demo relocation — 487 tests, Ring 1 COMPLETE | COMPLETE | `sprints/archive/sprint-3.md` |
| 4 | Ring 2 — Abstraction (modules, traits, constrained poly, dispatch) | — | — |
