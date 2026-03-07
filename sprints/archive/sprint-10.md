# Sprint 10: Ring 3 Macro Infrastructure (Phases 1-4)

**Status**: COMPLETE
**Ring**: 3 (Meta)
**Goal**: Build the macro infrastructure — synthetic `macros` module, marshal layer, quasiquote engine, defmacro parsing, and CraneliftExpander — so that macros can be compiled and expanded, but not yet wired into the batch/REPL pipelines.

## Scope

Ring 3 is the macro ring. The full macro plan (`design/frontend/macro-plan.md`) has 7 phases spanning ~2300 lines of new code. Sprint 10 covers **Phases 1-4** (infrastructure), leaving Phases 5-7 (pipeline integration, prelude macros, REPL polish) for Sprint 11.

### Why this split

Phases 1-4 are self-contained infrastructure that can be tested in isolation:
- **Phase 1**: Seed `macros` module with `SList`/`Sexp` ADTs; implement marshal (`sexp_to_runtime`, `runtime_to_sexp`)
- **Phase 2**: Quasiquote expansion engine (`` ` ``, `~`, `~@` → explicit Sexp constructor calls)
- **Phase 3**: `defmacro` parsing and body synthesis (parameter destructuring via nested match)
- **Phase 4**: `CraneliftExpander` implementation (`MacroExpander` trait, `compile_macro`, clause dispatch, `expand_sexp`)

Phase 5 (pipeline integration) touches batch + REPL and depends on all four prior phases. Keeping it in Sprint 11 gives us a clean gate: Sprint 10 delivers testable infrastructure; Sprint 11 wires it in and delivers prelude macros + showcase.

### Core deliverables

1. **Synthetic `macros` module** — `/typecheck` registers `SList` (SNil, SCons) and `Sexp` (7 variants) as type definitions in a compiler-seeded `macros` module, following the same pattern as `primitives`
2. **Marshal functions** — `sexp_to_runtime()` and `runtime_to_sexp()` convert between compiler-internal `Sexp` and runtime heap ADT values. Located in the binary crate (`src/marshal.rs`)
3. **Quasiquote expansion** — `/frontend` implements `expand_quasiquotes()` in `crates/cranelisp-frontend/src/quasiquote.rs`. Transforms template syntax to qualified `macros/SexpSym` etc. constructor calls. Auto-gensym support
4. **defmacro parsing** — `/frontend` implements `parse_defmacro()` and `synthesize_macro_clause_defn()` in `crates/cranelisp-frontend/src/defmacro.rs`. Multi-clause, bracket destructuring, rest params
5. **MacroExpander implementation** — `CraneliftExpander` struct in `src/expander.rs`: `compile_macro()`, clause dispatch, marshal round-trip invocation, `expand_sexp()` with depth limit
6. **`MacroClauseInfo.rest_param`** — Add `rest_param: Option<Symbol>` to interface type in `cranelisp-types`
7. **FIXME cleanup** — Resolve stale FIXMEs: roadmap.md:39 (REPL non-conformance fully fixed), plan-typecheck.md:478 (borrow-splitting doc)
8. **Integration tests** — `/qa` writes tests for marshal round-trips, quasiquote expansion, defmacro parsing, and macro compilation+expansion via CraneliftExpander

### Not in scope

- Pipeline integration (replacing `NoOpExpander` in batch/REPL) — Sprint 11
- Two-pass prelude loading — Sprint 11
- Prelude macros (`list`, `do`, `cond`, etc.) — Sprint 11
- SList helpers (`sfold`, `sreverse`, `sconcat`) — Sprint 11
- REPL `/expand` command — Sprint 11
- String primitives (FIXME U1.1) — deferred, not needed for macro infrastructure
- `bind!` macro — Ring 4 (needs IO model)

## FIXME Debt

| File | Owning Skill | Issue | Deferrals | Resolution |
|------|-------------|-------|-----------|------------|
| `design/arch/roadmap.md:7` | /arch | U0.1 — batch hello-world needs IO | 0 | deferred to Ring 4 |
| `design/arch/roadmap.md:39` | /qa | REPL non-conformance 12/12 fixed — **stale FIXME** | 0 | **in scope** #7 — update to reflect 12/12 |
| `design/arch/roadmap.md:56` | /backend | U1.1 — 11 missing string primitives | 1 (S9→S10) | deferred — not needed for macro infra; needed for `text/string.cl` in Sprint 11+ |
| `repl/spec.md:5` | /repl | CLI invocation modes | 0 | deferred to Ring 4 |
| `tests/plan/ring0.md:3` | /qa | U0.2 — /learn tutorial engine | 0 | deferred to Ring 4 |
| `crates/cranelisp-typecheck/plan-typecheck.md:478` | /typecheck | Borrow-splitting doc — **stale** (Sprint 6 noted deletion) | 1 | **in scope** #7 — delete stale comment |

## Architecture Review

**Status**: APPROVED — no blocking issues. 3 findings require action; 4 are advisory.

### 1. Technical Coherence — PASS

Phases 1-4 form a complete, testable increment. Each phase has a clear deliverable that can be validated in isolation:

- **Phase 1** (synthetic module): testable by verifying constructor types resolve via `macros/SexpSym` etc.
- **Phase 2** (quasiquote): testable as a pure Sexp-to-Sexp transformation — no pipeline needed.
- **Phase 3** (defmacro parsing): testable by inspecting `DefmacroInfo` and synthesized `Defn` structure.
- **Phase 4** (CraneliftExpander): testable end-to-end by compiling a macro and expanding it, without wiring into batch/REPL pipelines. The expander owns its `MacroEnv` and can be exercised directly in integration tests.

The split at Phase 5 (pipeline integration) is architecturally clean. Phases 1-4 build permanent infrastructure; Phase 5 wires it in. No throwaway test harnesses are needed — the expander's `compile_macro()` method takes `&mut TypeChecker` and `&mut Jit` as arguments, which integration tests can construct directly.

### 2. No Interim Architecture — PASS

Everything in Sprint 10 is permanent infrastructure that survives into Sprint 11 and beyond. No throwaway code. The `CraneliftExpander`, marshal functions, quasiquote engine, and defmacro parser are all final implementations, not scaffolding. This satisfies Principle 8.

### 3. Design Doc Discrepancies — ACTION REQUIRED

Three naming/location discrepancies exist between `design/arch/macro-pipeline.md` and `design/frontend/macro-plan.md`. These do not block Sprint 10 but must be resolved so compiler skills have unambiguous guidance:

**(a) Struct name**: macro-pipeline.md calls it `CraneliftExpander` (in `src/macro_expander.rs`). macro-plan.md calls it `CranelispExpander` (in `src/expander.rs`). The sprint proposal uses `CraneliftExpander` in some places and references `src/expander.rs` in others.

**Resolution**: Use `CraneliftExpander` (the architecture doc's name) in `src/expander.rs` (the plan's file path). The name `CraneliftExpander` correctly parallels `CraneliftExpander` as the "real expander backed by Cranelift JIT." The file name `expander.rs` is preferable to `macro_expander.rs` (shorter, the module context makes the meaning clear). Compiler skills should follow this resolution.

**(b) Marshal file location**: macro-pipeline.md §5 places marshal code in the binary crate (`src/marshal.rs`). macro-plan.md §Phase 1 places it in `crates/cranelisp-runtime/src/marshal.rs`. The sprint proposal correctly follows macro-pipeline.md (binary crate).

**Resolution**: The binary crate (`src/marshal.rs`) is correct. Marshal code converts between `Sexp` (from `cranelisp-types`) and heap-allocated runtime ADT values. It calls `heap_alloc` from `cranelisp-runtime` and reads raw heap memory. Placing it in the binary crate keeps it co-located with the `CraneliftExpander` that uses it and avoids pulling `Sexp` tree-walking logic into the runtime crate (which should remain a thin set of extern functions callable from JIT code). macro-plan.md §Phase 1 "Files to Create" table is the stale reference; the macro-pipeline.md §5 is authoritative.

**(c) Frontend defmacro file**: macro-pipeline.md §9 calls it `defmacro_parse.rs`. macro-plan.md §Phase 3 calls it `defmacro.rs`. The sprint proposal uses `defmacro.rs`.

**Resolution**: Use `defmacro.rs` (the plan's name). The file contains more than just parsing — it includes `synthesize_macro_clause_defn()`, `is_defmacro()`, `is_begin()`, and `flatten_begin()`. The broader name is more accurate.

**Action**: These are documentation discrepancies only. The sprint proposal's choices are correct. No FIXME needed — `/frontend` and `/qa` should follow the sprint proposal's naming. The design docs can be updated opportunistically during Sprint 11 cleanup.

### 4. Interface Gaps — PASS with one note

`MacroClauseInfo.rest_param: Option<Symbol>` is the only interface type change needed in `cranelisp-types`. Confirmed by cross-referencing:

- `MacroParam` already has `Bracket { fixed, rest }` — no change needed.
- `MacroExpander` trait: no change needed (confirmed in `pipeline.rs`).
- `NoOpExpander`: no change needed (remains as test fallback).
- `ModuleEntry::Macro`: already exists with `clauses: Vec<MacroClauseInfo>` — no change needed.

**Note**: The `DefmacroInfo` and `MacroClause` types from macro-plan.md §Phase 3 are frontend-internal types (not boundary types). They live in `crates/cranelisp-frontend/src/defmacro.rs` and do not cross crate boundaries — the binary crate receives the parsed `DefmacroInfo` and passes individual `MacroClause` values to `synthesize_macro_clause_defn()`. This is correct: no new boundary types are needed.

**One caveat**: `synthesize_macro_clause_defn()` returns a `Defn` (a boundary type from `cranelisp-types`). The binary crate calls this function, receiving a `Defn` it then passes to the typechecker and backend. This works because the binary crate depends on both `cranelisp-frontend` and `cranelisp-types`. No interface gap.

### 5. Crate Boundary Correctness — PASS

- **Marshal in binary crate** (`src/marshal.rs`): Correct. Marshal code needs `Sexp` (from types) and calls `heap_alloc` (from runtime, re-exported to binary). The binary crate has both dependencies. No crate boundary violation.
- **CraneliftExpander in binary crate** (`src/expander.rs`): Correct. The expander implements `MacroExpander` (from types), calls `parse_defmacro`/`synthesize_macro_clause_defn` (from frontend), typechecks via `TypeChecker` (from typecheck), compiles via `Jit` (from backend), and calls marshal functions (co-located in binary). This is exactly the pipeline wiring role the binary crate exists to fill.
- **Quasiquote in frontend** (`crates/cranelisp-frontend/src/quasiquote.rs`): Correct. Pure Sexp-to-Sexp transformation. Only depends on `cranelisp-types` (for `Sexp`, `Span`).
- **Defmacro parsing in frontend** (`crates/cranelisp-frontend/src/defmacro.rs`): Correct. Parses Sexp, calls `build_expr` (frontend-internal), returns `Defn` (boundary type). Depends only on `cranelisp-types`.
- **Macros module seeding in typecheck** (`crates/cranelisp-typecheck/src/builtins.rs`): Correct. Follows `register_primitives_module()` pattern.

### 6. Wave Structure — PASS with clarification

**(a) Wave 2 parallelism** (/typecheck Phase 1 + /frontend Phases 2-3): Correct. These have no compile-time or development-time dependency on each other:

- Phase 1 modifies `builtins.rs` in the typecheck crate.
- Phases 2-3 create new files in the frontend crate.
- No shared files, no shared types being modified.

The dependency noted in macro-plan.md ("Phase 2 depends on Phase 1: constructor names must be registered") is a **runtime dependency** — the expanded Sexp must be valid when eventually typechecked. At development time, the quasiquote engine just emits string literals like `"macros/SexpSym"`. No import of typecheck code is needed.

Phase 3 depends on Phase 2 within the frontend (noted correctly in the sprint as "Depends on Phase 2 within /frontend"). This is an intra-skill dependency, not a cross-wave dependency.

**(b) Wave 4 depends on Waves 2-3**: Correct. `CraneliftExpander.compile_macro()` calls `parse_defmacro()` (Phase 3), `expand_quasiquotes()` (Phase 2), and `sexp_to_runtime()`/`runtime_to_sexp()` (marshal, which depends on Phase 1's macros module for tag layout). All three must be complete before the expander can function.

**(c) Wave 3 as intermediate**: Wave 3 has /qa writing tests against Wave 2 deliverables. This is reasonable — it provides early validation before the expander is built. However, Wave 3 does not include the marshal tests (marshal code is written in Wave 4, not Wave 2). The /qa task in Wave 3 says "Phase 4 prep: marshal round-trip tests" — these tests can only be written against the marshal API, which does not exist until Wave 4. **Recommendation**: /qa in Wave 3 should focus on quasiquote expansion tests and defmacro parse tests. Marshal round-trip tests should move to Wave 4 alongside the marshal implementation. The sprint proposal's Wave 3 /qa description already seems to intend this ("Tests against Wave 2 deliverables"), but the task name mentions marshal — adjust the task description for clarity.

### 7. Skill Assignment — APPROVED with rationale check

The sprint assigns `CraneliftExpander` implementation to /qa (Wave 4). The rationale is that it lives in the binary crate, and pipeline wiring is /qa's domain.

This is consistent with precedent: /qa owns `src/pipeline.rs` and `src/repl.rs`. The `CraneliftExpander` is structurally similar — it wires frontend parsing + typecheck + backend compilation into a single orchestrated flow. /qa also writes `src/marshal.rs`, which is a utility module for the expander.

The key requirement is that /qa follows the design docs precisely. The architecture (`macro-pipeline.md`) and implementation plan (`macro-plan.md`) provide detailed function signatures, data flow, and ownership design. /qa implements to spec; it does not make architectural decisions.

**Alternative considered**: Assigning to /backend (since it involves JIT compilation) or /frontend (since it involves Sexp manipulation). Rejected because neither skill owns the binary crate, and the expander's defining characteristic is that it *wires* the other crates together — which is /qa's role.

### 8. Risk Assessment — PASS

The existing design docs (macro-pipeline.md §10, macro-plan.md §Risk Assessment) cover 7 risks (R1-R7). All are well-mitigated. No additional architectural risks identified for the Sprint 10 scope (Phases 1-4).

One observation: **R3 (Marshal Safety)** is the highest-risk item in Sprint 10. The marshal code performs unsafe heap reads and writes. The mitigation (centralized code, round-trip tests, debug assertions) is sound, but /review should pay special attention to this code in Wave 5. Every `unsafe` block must have a safety comment documenting the invariant it relies on.

### Summary

| # | Finding | Verdict | Action |
|---|---------|---------|--------|
| 1 | Technical coherence | PASS | None |
| 2 | No interim architecture | PASS | None |
| 3 | Design doc naming discrepancies | ACTION | Compiler skills follow sprint proposal naming; docs updated in Sprint 11 |
| 4 | Interface gaps | PASS | `MacroClauseInfo.rest_param` is the sole change |
| 5 | Crate boundaries | PASS | None |
| 6 | Wave 3 marshal test timing | ADVISORY | Clarify /qa Wave 3 task: marshal tests belong in Wave 4 |
| 7 | /qa skill assignment | APPROVED | /qa implements to design doc spec |
| 8 | Risk assessment | PASS | /review: extra scrutiny on marshal `unsafe` blocks |

## Skill Plans

### /arch
**Task**: Review sprint scope; confirm Phase 1-4 design coverage; review compiler skill design docs produced in Wave 1
**Design doc**: `design/arch/macro-pipeline.md` (existing, comprehensive — covers all 4 phases)
**Approach**: Verify sprint scope aligns with macro-pipeline.md architecture. Review any new/updated design docs from compiler skills. Confirm `MacroClauseInfo.rest_param` interface change. No new design doc needed — existing doc already covers Phases 1-4 in detail
**Design refs**: `design/arch/macro-pipeline.md`, `design/arch/interfaces.md` §MacroClauseInfo, `design/arch/architecture.md` §MacroExpander trait
**Acceptance**: Sprint scope APPROVED; compiler skill designs consistent with macro-pipeline.md

### /frontend
**Task**: Implement Phases 2-3: quasiquote expansion engine and defmacro parsing/body synthesis
**Design doc**: `design/frontend/macro-plan.md` (existing, Phases 2-3 sections)
**Approach**: Phase 2: Create `crates/cranelisp-frontend/src/quasiquote.rs` — `expand_quasiquotes()`, `expand_qq_template()`, auto-gensym via `AtomicU32` counter. All constructor refs are module-qualified (`macros/SexpSym` etc.). Phase 3: Create `crates/cranelisp-frontend/src/defmacro.rs` — `is_defmacro()`, `parse_defmacro()` (single/multi-clause, docstring extraction), `synthesize_macro_clause_defn()` (nested match chain for SList arg destructuring, bracket destructuring with prefixed inner tail bindings). Add `pub mod quasiquote` and `pub mod defmacro` to frontend lib.rs
**Design refs**: `design/frontend/macro-plan.md` §Phase 2-3, `spec/09-macros.md` §9.3-9.5, `design/arch/macro-pipeline.md` §3 (Defn synthesis), `sketch/src/macro_expand.rs` (reference oracle)
**Acceptance**: `expand_quasiquotes()` handles all 7 Sexp variants + `~` + `~@` + auto-gensym; `parse_defmacro()` handles single/multi-clause + bracket destructure + rest params; unit tests for each function

### /typecheck
**Task**: Phase 1 — seed synthetic `macros` module with `SList` and `Sexp` ADTs; clean stale FIXME
**Design doc**: `design/frontend/macro-plan.md` §Phase 1 (type registration); `design/arch/macro-pipeline.md` §6 (Synthetic macros Module)
**Approach**: Add `register_macros_module(tc: &mut TypeChecker)` to `builtins.rs`, following `register_primitives_module()` pattern. Register `SList` (2 constructors: `SNil` nullary, `SCons` with `shead: a` + `stail: (SList a)`) and `Sexp` (7 data constructors: `SexpInt`, `SexpFloat`, `SexpBool`, `SexpStr`, `SexpSym`, `SexpList`, `SexpBracket`). Module name: `macros`. Called after `register_primitives()` since it references `Int`, `Bool`, `Float`, `String`. Delete stale borrow-splitting FIXME in `plan-typecheck.md:478`. Verify constructors are accessible via qualified paths (`macros/SexpSym`, `macros/SCons`, etc.) from other modules
**Design refs**: `design/arch/macro-pipeline.md` §6, `spec/09-macros.md` §9.1-9.2, `crates/cranelisp-typecheck/src/builtins.rs`
**Acceptance**: `macros` module seeded at startup; all 9 constructors resolve via qualified access; unit tests verify constructor types match spec; stale FIXME deleted

### /backend
**Task**: No new backend code in Phases 1-4; existing `compile_defn` path is sufficient for macro clause compilation. Support /qa if any codegen issues surface during macro clause compilation tests
**Design doc**: N/A (no new backend design needed — macro clauses compile as ordinary `Defn` nodes)
**Approach**: Confirm that `compile_defn()` handles functions returning ADT values (Sexp constructors). The macro clause signature `extern "C" fn(i64) -> i64` maps to existing calling convention. No drop glue needed for marshalled values (leaked per architecture decision). Stand by for any codegen issues discovered during integration testing
**Design refs**: `design/arch/macro-pipeline.md` §3 (Macro Compilation Flow, step 2e), `design/backend/ring2-rc.md` §3 (calling conventions)
**Acceptance**: Existing `compile_defn` compiles macro clause bodies without modification; confirmed by /qa integration tests

### /qa
**Task**: Write integration tests for macro infrastructure; update stale roadmap.md FIXME; derive test cases from Phase 1-4 design docs
**Design doc**: `tests/plan/ring3.md` (existing, to be updated with Phase 1-4 test cases)
**Approach**: Tests organized by phase: (1) Marshal round-trip tests — verify `sexp_to_runtime` then `runtime_to_sexp` preserves all 7 Sexp variants including nested lists/brackets; verify SList marshal. (2) Quasiquote unit tests — verify each expansion rule from the table in macro-plan.md §Phase 2; auto-gensym uniqueness; nested quasiquote depth handling. (3) defmacro parsing tests — single-clause, multi-clause, bracket destructure, rest param, docstring extraction; synthesized Defn structure validation. (4) CraneliftExpander tests — compile a simple macro, expand it, verify result; clause dispatch with multiple arities; expansion depth limit error; marshal safety with nested structures. Update `design/arch/roadmap.md:39` FIXME to reflect 12/12 REPL non-conformance items resolved (float display fixed in Sprint 9 Wave 7). Update `tests/plan/ring3.md` with specific test cases derived from design docs
**Design refs**: `design/frontend/macro-plan.md` §Phases 1-4, `design/arch/macro-pipeline.md` §2-5, `tests/plan/ring3.md`, `spec/09-macros.md`
**Acceptance**: Marshal round-trip tests pass for all Sexp variants; quasiquote expansion tests cover the full rule table; defmacro parse tests cover single/multi/bracket/rest; CraneliftExpander compiles+expands at least one macro end-to-end; stale FIXME updated; ring3.md test plan updated

### /review
**Task**: Review Wave 2 implementation for code quality, architecture adherence, and correctness
**Approach**: Review new files (`quasiquote.rs`, `defmacro.rs`, `expander.rs`, `marshal.rs`, `builtins.rs` changes) against design docs. Check: no `unwrap()` in pipeline code, functions under 100 lines, proper error handling, synthetic span uniqueness, marshal safety (pointer reads documented as unsafe), no crate boundary violations. Apply Ring 3 specific criteria: macro pipeline uses dependency inversion correctly, no backend/typecheck imports in frontend, marshal code is centralized
**Design refs**: `design/review/checklist.md`, `design/arch/macro-pipeline.md`, `design/frontend/macro-plan.md`
**Acceptance**: Review report produced; no Blocker findings; all Important findings addressed

### /spec
**Task**: No spec changes needed for Phase 1-4 infrastructure. Stand by for any spec ambiguities discovered during implementation
**Approach**: The macro spec (`spec/09-macros.md`) is comprehensive (915 lines) and was used to inform the Phase 1-4 design. Monitor for any ambiguities surfaced by compiler skills and arbitrate if needed
**Design refs**: `spec/09-macros.md`
**Acceptance**: N/A (reactive)

### /stdlib
**Task**: Early engagement — refine prelude macro implementation plan for Sprint 11; identify SList helper functions needed
**Approach**: Review `design/frontend/macro-plan.md` §Phase 6 against `lib/plan-stdlib.md` §13. Confirm the implementation order for prelude macros: `vec` -> `when` -> `const`/`const-` -> `do` -> `cond` -> `list` -> `str` -> `case` -> `->` / `->>` -> `def`/`def-`. Identify which SList helpers (`sfold`, `sreverse`, `sconcat`, `sempty?`) are prerequisites for which macros. Prepare Sprint 11 scope: what stdlib work depends on the Phase 5 pipeline integration
**Design refs**: `lib/plan-stdlib.md` §13, `design/frontend/macro-plan.md` §Phase 6, `spec/09-macros.md` §9.7, §9.10
**Acceptance**: Sprint 11 stdlib scope refined; SList helper dependency matrix documented

### /examples
**Task**: Early engagement — plan Ring 3 learning examples (REPL-first, no IO)
**Approach**: Sprint 9 survey found all 21 sketch examples need IO (Ring 4). Ring 3 learning examples will be REPL-first: demonstrate `defmacro`, quasiquote, multi-clause macros, prelude macros (`list`, `cond`, threading). Plan 3-4 new REPL-first examples for Sprint 11 showcase
**Design refs**: `examples/plan-examples.md`, Sprint 9 readiness assessment
**Acceptance**: Ring 3 example plan documented

### /docs
**Task**: No docs work this sprint
**Approach**: N/A
**Acceptance**: N/A

### /platform
**Task**: No platform work this sprint
**Approach**: N/A
**Acceptance**: N/A

### /port
**Task**: Early engagement — identify which exemplar patterns exercise macros
**Approach**: Sprint 9 found 85% of exemplar implementable at Ring 3. Refine: which exemplar modules specifically use `list`, `cond`, `case`, threading macros? Which can be implemented once Sprint 11 delivers prelude macros? Prepare Sprint 11 task scope
**Design refs**: `exemplar/plan-port.md`, Sprint 9 readiness note
**Acceptance**: Exemplar macro-usage map refined

### /repl
**Task**: Early engagement — plan `/expand` command and macro introspection for Sprint 11
**Approach**: Review `design/frontend/macro-plan.md` §Phase 7 and `repl/spec.md` §3 (slash commands) for `/expand` requirements. Plan how `ModuleEntry::Macro` integrates into `/list`, `/info`, `/sig`, `/doc` handlers. Identify test cases for Sprint 11
**Design refs**: `design/frontend/macro-plan.md` §Phase 7, `repl/spec.md` §3, `spec/09-macros.md` §9.13
**Acceptance**: Sprint 11 REPL plan documented

## Waves

### Wave 1: Design Review + Planning (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review sprint scope; confirm Phase 1-4 coverage in existing design docs | **done** | APPROVED — 3 action items, 4 advisory; see Architecture Review |
| /qa | Derive Phase 1-4 test cases; update ring3.md; clean stale roadmap.md FIXME | **done** | 68 test cases added to ring3.md tagged [R3 S10]; roadmap.md FIXME updated to 12/12 RESOLVED |
| /stdlib | Refine Sprint 11 prelude macro plan; SList helper dependency matrix | **done** | §14 added to plan-stdlib.md: SList helper matrix, implementation order, Sprint 11 task summary |
| /examples | Plan Ring 3 REPL-first learning examples | **done** | §11 added: 4 REPL-first examples (macro-basics, multi-clause, prelude-macros, custom-control-flow) |
| /port | Refine exemplar macro-usage map | **done** | Macro usage map added to plan-exemplar.md: 5/7 modules at Ring 3, grid+solver first |
| /repl | Plan Sprint 11 `/expand` and macro introspection | **done** | §11 added to repl/spec.md: /expand, macro introspection, 8 test scenarios |

### Wave 2: Implementation (parallel, after Wave 1)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Phase 1: `register_macros_module()` — seed SList + Sexp ADTs in macros module; delete stale FIXME | **done** | 8 new unit tests; `MacroClauseInfo.rest_param` added; stale FIXME deleted; 807 tests pass |
| /frontend | Phase 2: `quasiquote.rs` — quasiquote expansion engine with auto-gensym | **done** | ~400 lines, 15 unit tests; all 7 Sexp variants + unquote + splicing + auto-gensym |
| /frontend | Phase 3: `defmacro.rs` — defmacro parsing + body synthesis with match chain | **done** | ~540 lines, 20 unit tests; single/multi-clause, bracket destructure, rest params, body synthesis |

### Wave 3: Expander + Marshal (after Wave 2)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Quasiquote expansion tests + defmacro parse tests (Wave 2 validation); marshal round-trip tests deferred to Wave 4 | **done** | Merged with Wave 4; 43 unit tests from Wave 2 provided validation |
| /frontend | Phase 4 support: any frontend adjustments surfaced by expander integration | **done** | 4 fixes in defmacro.rs: bracket annotations, match arm format, unqualified type names, exhaustiveness wildcards |

Note: The CraneliftExpander (Phase 4) needs the macros module (Phase 1), quasiquote (Phase 2), and defmacro parsing (Phase 3). It lives in the binary crate and wires typecheck + backend together.

### Wave 4: Expander Implementation (after Wave 3)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Phase 4: `CraneliftExpander` implementation — `src/expander.rs` + `src/marshal.rs` + marshal round-trip tests + expander integration tests | **done** | marshal.rs (497 lines, 18 tests) + expander.rs (649 lines, 6 tests). MacroError variant added. Consuming convention RC fix. 827 tests pass. |
| /backend | Confirm `compile_defn` handles macro clause bodies; support any codegen issues | **done** | 2 fixes: qualified constructor name support in match_codegen.rs and literals.rs (bare_ctor_name helper) |

Note: The CraneliftExpander implementation is assigned to /qa because it lives in the binary crate (pipeline wiring is /qa's domain per skill definition). /qa writes `src/expander.rs` (MacroExpander trait impl, compile_macro, clause dispatch, expand_sexp) and `src/marshal.rs` (sexp_to_runtime, runtime_to_sexp). This is analogous to how /qa owns `src/pipeline.rs` and `src/repl.rs`.

### Wave 5: Validation + Review (after Wave 4)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Full test suite: all macro infrastructure tests pass; 0 regressions | **done** | 827 root + 619 crate = 1446 workspace tests, 0 failures, 0 clippy errors. 1 pre-existing runtime test failure (str_concat in cranelisp-runtime, not Sprint 10 code). |
| /review | Review Wave 2-4 code against design docs; assess quality | **done** | 2B + 7I + 5S findings. All blockers and important items fixed in-sprint. See Wave 5 notes. |

## Notes

- Phase 1 (scope): User approved Sprint 10 scope as drafted.
- Phase 2 (arch review): APPROVED with 3 action items: (a) naming resolution — use `CraneliftExpander` in `src/expander.rs`, (b) marshal in binary crate confirmed, (c) `defmacro.rs` filename confirmed. Wave 3 clarified: marshal tests belong in Wave 4, not Wave 3. /qa for CraneliftExpander approved. Design docs from Sprint 9 are sufficient — no new design docs needed.
- Phase 3 (design): Skipped — existing design docs (`macro-pipeline.md`, `macro-plan.md`) comprehensively cover Phases 1-4. No additional design work needed.
- Phase 4 (waves): 5 waves. Wave 1 = arch review + planning (6 skills). Wave 2 = implementation (typecheck + frontend, parallel). Wave 3 = test Wave 2 deliverables. Wave 4 = expander + marshal implementation. Wave 5 = validation + review.
- Wave 1 complete: All 6 tasks done. /qa derived 68 test cases for ring3.md, cleaned stale roadmap FIXME (12/12 REPL items resolved). /stdlib refined Sprint 11 prelude plan with SList dependency matrix. /examples planned 4 REPL-first Ring 3 examples. /port mapped exemplar macro usage (5/7 modules at Ring 3). /repl added §11 to repl/spec.md with /expand spec and 8 test scenarios.
- Wave 2 complete: All 3 tasks done. /typecheck seeded `macros` module (SList + Sexp ADTs, 9 constructors, 8 unit tests). /frontend created quasiquote.rs (~400 lines, 15 tests) and defmacro.rs (~540 lines, 20 tests). `MacroClauseInfo.rest_param` added. 807 tests pass, 0 failures, 0 clippy. Reader finding: `&rest` parses as fused symbol — defmacro.rs handles by checking `starts_with("&")`.
- Wave 3 merged into Wave 4: Wave 2 delivered comprehensive unit tests (35 frontend + 8 typecheck = 43 new tests). Separate Wave 3 validation unnecessary. Marshal round-trip tests included in Wave 4 per arch review #6.
- Wave 3-4 complete: CraneliftExpander + marshal implemented. marshal.rs (497 lines, 14 tests): sexp_to_runtime/runtime_to_sexp for all 7 Sexp variants + SList. expander.rs (649 lines, 6 tests): compile_macro, expand_sexp with depth limit 100, clause dispatch, MacroExpander trait impl. Also: MacroError variant added to CranelispError, 4 fixes in defmacro.rs (bracket annotation format, exhaustiveness wildcards), qualified constructor name support added to typecheck infer.rs and backend match_codegen.rs + literals.rs. Consuming convention RC fix for marshalled values (rc_inc before invocation prevents use-after-free). 827 tests pass, 0 failures, 0 clippy.
- Wave 5 complete: /qa validated 1446 workspace tests (827 root + 619 crate), 0 failures, 0 clippy errors after fixes. 1 pre-existing failure in cranelisp-runtime str_concat test (not Sprint 10 code). /review found 2 Blockers + 7 Important + 5 Suggestions. All blockers and important items fixed in-sprint:
  - **B1**: Split 180-line `register_macros_module()` into 3 helpers (`register_slist_type`, `register_sexp_type`, `sexp_ctor`)
  - **B2**: Replaced `.expect()` with `let Some(...) else { unreachable! }` in quasiquote splicing
  - **I1**: Replaced magic `1024` with `NULLARY_TAG_THRESHOLD` import in expander.rs
  - **I2**: Replaced local `NULLARY_TAG_THRESHOLD` const in marshal.rs with import from cranelisp_types
  - **I3**: Deduplicated `bare_ctor_name`/`bare_constructor_name` into single `pub(crate)` helper in compiler/mod.rs
  - **I4**: Replaced bare offset `8` with named `RC_OFFSET` constant in marshal.rs rc_inc
  - **I5**: Merged two independent `AtomicU32` span counters (quasiquote + defmacro) into shared `next_synthetic_span()`
  - **I6**: Changed `# Safety` doc to `# Preconditions` on safe fn `runtime_to_sexp`
  - **I7**: Added known-limitation doc about leak accumulation in long-running processes
  - **Clippy**: Fixed 3 `approx_constant` errors (test floats 3.14→3.125, 2.718→2.5)
  - Suggestions S1-S5 deferred (approaching-limit function, raw func_ptr type, dead_code docstring, edge-case test gaps, trailing None args)

## Outcome

### Delivered
- **Phase 1**: Synthetic `macros` module seeded with SList (SNil/SCons) + Sexp (7 constructors) in `builtins.rs` (8 unit tests)
- **Phase 2**: Quasiquote expansion engine in `crates/cranelisp-frontend/src/quasiquote.rs` (~400 lines, 15 tests) — backtick/unquote/splice-unquote, auto-gensym, module-qualified constructor refs
- **Phase 3**: Defmacro parser in `crates/cranelisp-frontend/src/defmacro.rs` (~540 lines, 20 tests) — single/multi-clause parsing, bracket destructuring, match synthesis with exhaustiveness wildcards
- **Phase 4**: CraneliftExpander in `src/expander.rs` (~649 lines, 6 tests) — MacroExpander trait impl, compile_macro pipeline, clause dispatch, marshal round-trip, depth-limited recursive expansion
- **Marshal layer** in `src/marshal.rs` (~500 lines, 14 tests) — sexp_to_runtime/runtime_to_sexp for all variants, SList construction, RC protection for consuming convention
- **Cross-crate fixes**: Qualified constructor name resolution in typecheck (infer.rs) and backend (match_codegen.rs, literals.rs)
- **Interface additions**: `MacroClauseInfo.rest_param`, `CranelispError::MacroError`
- **Planning**: 68 test cases derived for ring3.md, REPL spec §11 (macro introspection), stdlib SList dependency matrix, 4 example outlines, exemplar macro usage map
- **Test count**: 827 root crate tests (+20 from Sprint 9 baseline of 807), 1446 workspace total
- **Code quality**: 0 clippy errors, 0 FIXMEs, all review blockers and important items resolved in-sprint

### Deferred
- **S1**: `parse_defmacro` at 85 lines approaching limit — monitor, no action needed yet
- **S2**: Raw `*const u8` func_ptr — newtype would improve readability; defer to Sprint 11 when more macro code lands
- **S3**: `MacroEntry.docstring` dead_code — will be used when /repl adds `/doc` for macros in Sprint 11
- **S4**: Edge-case test gaps (expansion depth limit, rc_inc direct test, malformed defmacro errors) — defer to Sprint 11 /qa pass
- **S5**: Builder pattern for `build_compile_context` — pre-existing API issue, not Sprint 10 scope
- **Pre-existing bug**: `cranelisp-runtime` `string::tests::test_str_concat` fails (assertion on alloc_size) — not Sprint 10 code, tracked for investigation

### Findings
- **Qualified constructor resolution**: The macros module introduced the first cross-module constructor references (`macros/SCons` etc.). Both typecheck and backend needed fixes to strip module prefixes before registry lookup. This pattern will recur with user modules — consider centralizing the strip logic upstream.
- **Consuming convention + marshal interaction**: JIT-compiled macro functions decrement RC on their SList parameter. If result Sexp nodes reference the same heap allocations, they get freed. Fix: `rc_inc()` each marshalled element before invocation. This is a subtle ownership boundary that should be documented in the design docs.
- **Synthetic span counters**: Two independent AtomicU32 counters (quasiquote starting at 1M, defmacro at 2M) risked collision. Merged into shared counter. Future synthetic span producers should use the same shared counter.
- **`&rest` parsing**: The reader returns `&rest` as a single fused symbol, not `&` + `rest`. The defmacro parser handles this by checking `starts_with("&")`. Worth noting in the reader spec.
