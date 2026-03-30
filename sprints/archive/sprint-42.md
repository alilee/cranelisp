# Sprint 42: Pipeline v4 Step 4 — Macro Expansion Blocking

**Status**: COMPLETE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: Programs with macros (including `defmacro` definitions and macro calls) compile through the v4 scheduler path, with macro dependencies resolved via the priority codegen queue.

## Context

Sprint 41 delivered Steps 2+3: the `CompileScheduler` and form-by-form worker loop. The v4 path (`--v4 --run`) handles programs using only primitives and special forms — no macros, no imports, no operators. The C2 filter rejects any program containing `defmacro` or operator symbols.

This sprint delivers **Step 4** from `design/arch/pipeline-v4-roadmap.md`:

When `process_module_forms` encounters a macro call whose function pointer is not yet compiled, the worker blocks via the scheduler's priority codegen queue. The same thread (single-threaded) picks up the codegen work, compiles the macro's dependencies, unblocks the module, and resumes typechecking from the blocked form.

After this sprint, programs with user-defined macros compile through `--v4 --run`. The prelude is still not loaded (that requires multi-module dependency discovery in Step 5), so only programs that define their own macros inline qualify. Operators still require prelude traits and remain rejected.

**All skills MUST read:**
- `design/arch/pipeline-v4-roadmap.md` — Step 4 specification (lines 114-126)
- `design/arch/concurrent-pipeline.md` — scheduler blocking/unblocking semantics, §5.2 form processing flow
- `design/arch/pipeline-v4.md` — target architecture, §3.2 per-form processing
- `src/worker.rs` — current worker loop and `process_module_forms`
- `src/scheduler.rs` — `block_for_macro_codegen`, `notify_priority_codegen_complete`

## Scope

### A. Restructure `process_module_forms` for Per-Sexp Expansion

This is the largest change in the sprint. The current function does `build_program` (all sexps at once with `NoOpExpander`) then two-pass typecheck. Step 4 requires per-sexp expansion interleaved with Pass 2, per `pipeline-v4.md` §3.2 and `concurrent-pipeline.md` §5.2.

New structure:
1. **Pass 1 (Register)**: Iterate all sexps. For each: build AST via `build_top_level`, call `tc.check_form(Register)`. When a `defmacro` is encountered, typecheck its body and register clause info + AST in the module table. **No codegen** — deferred until first use (`concurrent-pipeline.md` §5.2 step 5).
2. **Pass 2 (CheckBody)**: Iterate sexps in source order. For each:
   a. **Expand**: If the sexp is a macro call, check if the macro's function pointer exists. If not, typecheck the macro body (if not already done), walk its call graph, compile dependencies inline via `compile_and_register_defn`, then expand the macro. All state stays on the stack — no suspension, no scheduler blocking.
   b. **Build AST** from the (possibly expanded) sexp via `build_top_level` with `NoOpExpander`.
   c. **Typecheck** the form via `tc.check_form(CheckBody)`.
   d. **Notify** scheduler via `notify_symbol_typechecked`.

Expansion happens per-sexp before AST building, keeping blocking logic in the worker (not the frontend crate). Extract reusable free functions from `src/expander.rs` (`invoke_clause`, marshal/unmarshal, `clause_matches`, `find_matching_clause`, `rewrite_spans`) so the v4 worker can call them without going through the `MacroExpander` trait.

### B. BlockingJitCodegen Handler

The stub in `priority_worker_loop` at line 380 must be implemented:
1. Look up the symbol's typechecked defn from the tc module table.
2. JIT-compile it via `compile_and_register_defn`.
3. Register the code pointer in the GOT.
4. Call `scheduler.notify_priority_codegen_complete()`.

### C. Inline Compile-and-Continue (Single-Threaded)

Single-threaded inline compilation. When Pass 2 encounters a macro call needing codegen, the same thread compiles deps inline via `compile_and_register_defn` and continues. All state stays on the stack — no `ResumeTypecheck` variant, no `SuspendedState`, no worker-local HashMap. The scheduler is notified of completions but does not drive the blocking. Multi-threaded suspension/resumption is a Step 11 concern.

### D. C2 Filter Relaxation

Remove the `defmacro` rejection from `sexp_qualifies` in `session_v4.rs:70`. Programs with macros (but no imports, no operators) now qualify for the v4 path.

### E. Macro Expansion Integration

Wire real macro expansion into the per-sexp Pass 2 flow:
- When a `defmacro` is encountered in Pass 1, register it in the module table (`ModuleEntry::Macro` with clause info + AST). No codegen.
- When a macro call is encountered in Pass 2 and the function pointer is already compiled (or after inline compilation of deps): marshal args, invoke the function pointer, unmarshal the result sexp, recursively expand to fixed point, then continue with the expanded sexp.
- Reuse existing marshal/unmarshal/invoke machinery extracted from `src/expander.rs` (see Scope A).

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `spec/05-definitions.md:565` | /spec | "compiled immediately" is implementation guidance; requirement is availability from next form | filed this sprint |
| `spec/09-macros.md:263` | /spec | same — "compiled and registered immediately" should be "registered when encountered" | filed this sprint |
| (arch review B-1) | /typecheck | TC doesn't store AST — no way to walk call graph post-typecheck | **Resolved**: Decision 21 — call graph edges accumulated during Pass 2, stored in `ModuleEntry.callees` |
| (arch review B-2) | /int | Macro body must be typechecked before call graph walk | **Resolved**: `defmacro` typechecked in Pass 2 before any call; `callees` already populated when macro call triggers blocking |

## Architecture Review

**Reviewer**: /arch
**Verdict**: PASS (with recommendations, all incorporated below)

### Coherence
The five scope sections (A-E) connect logically and form a complete testable increment. Acceptance criterion is clear: programs with inline `defmacro` + macro calls produce identical results on `--v4 --run` vs old path.

### No Interim Architecture
Pass. All infrastructure survives into the target architecture:
- `BlockingJitCodegen` handler is the permanent priority codegen mechanism (Steps 4-15).
- Inline compile-and-continue is the simplest correct approach for single-threaded Step 4. Step 11 will introduce real suspension/resumption when multi-threading requires it.
- Per-sexp expansion replaces `NoOpExpander` permanently.
- Macro codegen is demand-driven (on first call), matching `pipeline-v4.md` §3.2 step 5. No eager compilation that would need unwinding later.

### Interface Gaps
No new cross-crate types needed. Inline compile-and-continue requires no new scheduler variants or state types.

### Design Recommendations (incorporated)
1. **Restructure `process_module_forms`** — the largest change. Scope A rewritten to describe the per-sexp expansion flow explicitly (was underspecified in original draft).
2. **Lazy macro codegen** — `defmacro` registered on encounter, codegen deferred until first call. Matches target architecture.
3. **Extract free functions from `src/expander.rs`** — expansion logic reusable without `MacroExpander` trait dependency.
4. **Inline compile-and-continue** — simplest correct approach for single-threaded Step 4. No `SuspendedState`, no `ResumeTypecheck`. Step 11 adds real suspension/resumption for multi-threading.
5. **`/typecheck` note**: verify `check_form(CheckBody)` works for macro clause defns when called outside normal Pass 2 flow.
6. **`/int` additional reference**: study `src/session.rs::compile_and_register_macro` and `src/expander.rs::compile_single_clause` for the existing macro compilation pipeline.

### Decision 21: TC-sourced call graph

The call graph is populated by the typechecker during Pass 2 and stored in the symbol table — no separate data structure or post-hoc collection pass.

- `ModuleEntry::Def` and `ModuleEntry::Macro` gain `callees: Vec<FQSymbol>` — the set of fully-qualified symbols that the definition's body calls.
- `FormCheckResult.call_graph_edges` changes from `Vec<FQSymbol>` to `Vec<(Symbol, FQSymbol)>` — each edge pairs the local call-site symbol with the resolved callee.
- Edges are accumulated during `check_form(CheckBody)` and written to `ModuleEntry` during `finalize_check_result()`.
- Cross-module queries use the existing `SymbolTable` lookup path: `tc.symbol_table(module).get(name).callees`.
- **Rationale**: The scheduler needs pre-codegen visibility into dependencies (Principle 4: scheduler decides compilation order). Storing edges in the TC symbol table avoids creating an interim data structure that would need unwinding later (Principle 8: no interim architecture). The TC already resolves all names during Pass 2, so it has the information — no second pass needed.

### Wave 2 Design Review Findings

**Reviewer**: /arch
**Scope**: Wave 1 design docs + call graph approach

#### Blockers (2) — both resolved

| ID | Finding | Resolution |
|----|---------|------------|
| B-1 | TC doesn't store AST — worker needs call graph to discover macro deps, but no AST walk is available post-typecheck | Resolved by Decision 21: call graph edges are accumulated during Pass 2 typecheck, stored in `ModuleEntry.callees`. No AST walk needed. |
| B-2 | Macro body must be typechecked before call graph walk — if `defmacro` body is deferred, callees are unknown when a macro call triggers blocking | Resolved: `defmacro` is typechecked in Pass 2 before any call. When a macro call is encountered, the macro's `ModuleEntry` already has `callees` populated. |

#### Important (4) — to be addressed in design doc revision

| ID | Finding |
|----|---------|
| I-1 | ~~`SuspendedState` must capture the `MacroExpander` state~~ — **N/A: `SuspendedState` removed.** Inline compile-and-continue keeps all state on the stack. No suspension/resumption in Step 4. |
| I-2 | Recursive macro expansion (macro A expands to a call to macro B) needs a depth limit or cycle check to prevent infinite expansion loops. |
| I-3 | `block_for_macro_codegen` dependency list should be transitively closed — walk `callees` recursively, not just direct deps of the macro. |
| I-4 | Error reporting path for macro expansion failures during v4 per-sexp flow needs design (currently `MacroExpander` trait returns `Result`, but worker loop uses a different error propagation model). |

#### Suggestions (3)

- S-1: Consider a `FormExpansionResult` enum (`Expanded(Sexp)` / `NeedsBlock(Vec<FQSymbol>)` / `NotAMacro`) to make the per-sexp expansion control flow explicit.
- S-2: Add a debug log when a module blocks for macro codegen, including the blocked form index and the dependency list — essential for debugging the scheduler.
- S-3: Extract the transitive callee walk as a utility on `SymbolTable` so both the worker and future incremental recompilation can reuse it.

## Skill Plans

### /int
**Task**: Restructure `process_module_forms` for per-sexp expansion, implement BlockingJitCodegen handler, inline compile-and-continue for macro deps, C2 filter relaxation, macro expansion integration.
**Design doc**: `design/int/step4-macro-blocking.md` (to be written)
**Approach**: {to be filled by /int}
**Design refs**: `design/arch/pipeline-v4-roadmap.md` Step 4, `design/arch/concurrent-pipeline.md` §5.2 + §6, `design/arch/pipeline-v4.md` §3.2, `src/expander.rs`, `src/session.rs::compile_and_register_macro`. **Call graph source (Decision 21)**: worker reads callees from `ModuleEntry` via `tc.symbol_table(module).get(name).callees` — no separate call graph structure or method resolution walk. Transitive deps compiled inline by walking `callees` recursively through the symbol table and calling `compile_and_register_defn` for each uncompiled dep. No suspension/resumption — all state stays on the stack.
**Acceptance**: `--v4 --run` compiles programs with inline `defmacro` + macro calls. Results match old path.

### /typecheck
**Task**: Populate `call_graph_edges` during Pass 2 typecheck; write callees to `ModuleEntry` during `finalize_check_result()` (Decision 21). Ensure `check_form(CheckBody)` works for macro clause defns outside normal Pass 2 flow (i.e., when typechecking a macro body on demand before its first call). No separate `collect_call_graph` method needed — edges are accumulated as a side effect of name resolution during Pass 2.
**Design doc**: `design/typecheck/step4-macro-deps.md` (to be written if needed)
**Approach**: {to be filled by /typecheck}
**Design refs**: `design/arch/pipeline-v4-roadmap.md` Step 4, `crates/cranelisp-typecheck/src/program.rs`, Decision 21 (TC-sourced call graph)
**Acceptance**: `check_form` handles `defmacro` forms in both Register and CheckBody passes. `FormCheckResult.call_graph_edges` contains `Vec<(Symbol, FQSymbol)>` edges. `ModuleEntry::Def` and `ModuleEntry::Macro` have `callees` populated after `finalize_check_result()`.

### /arch
**Task**: Review sprint scope for technical coherence, confirm no interim architecture, review design docs.
**Design doc**: n/a (reviewer role)
**Approach**: Phase 2 review — COMPLETE (see Architecture Review section above)
**Design refs**: `design/arch/pipeline-v4.md`, `design/arch/concurrent-pipeline.md`
**Acceptance**: Architecture review section filled, design docs approved.

### /qa
**Task**: Write integration tests for macro programs through the v4 path. Test macro definition, macro call expansion, macro dependency blocking/unblocking, resumption correctness.
**Design doc**: n/a
**Approach**: Spec-first test design from `spec/09-macros.md` and Step 4 requirements.
**Design refs**: `spec/09-macros.md`, `design/arch/pipeline-v4-roadmap.md` Step 4
**Acceptance**: Tests cover: (1) simple defmacro + call, (2) macro calling a helper function defined before it, (3) macro calling another macro, (4) multiple macros in one module, (5) macro with multi-clause dispatch, (6) results match old path for all cases.

### /review
**Task**: Review implementation for correctness, adherence to design doc, and structural quality.
**Design doc**: n/a
**Approach**: Standard review during implementation wave.
**Design refs**: `design/review/checklist.md`, `src/CLAUDE.md`
**Acceptance**: 0 Blockers, all Important findings resolved.

### /frontend
**Task**: No implementation work this sprint. Advisory for macro expansion API extraction.
**Approach**: Standby.
**Acceptance**: n/a

### /backend
**Task**: No implementation work this sprint. `compile_and_register_defn` is reused as-is.
**Approach**: Standby.
**Acceptance**: n/a

### /stdlib
**Task**: No implementation work (prelude not loaded in v4 path until Step 5).
**Approach**: Standby.
**Acceptance**: n/a

### /examples
**Task**: No changes this sprint (examples use prelude macros, which require Step 5).
**Approach**: Standby.
**Acceptance**: n/a

### /repl
**Task**: No changes (REPL remains on old path until Step 7).
**Approach**: Standby.
**Acceptance**: n/a

### /port
**Task**: No changes (exemplar uses prelude, requires Step 5+).
**Approach**: Standby.
**Acceptance**: n/a

### /docs
**Task**: No changes this sprint.
**Approach**: Standby.
**Acceptance**: n/a

### /platform
**Task**: No changes this sprint.
**Approach**: Standby.
**Acceptance**: n/a

### /spec
**Task**: Resolve 2 FIXMEs filed this sprint (macro "compiled immediately" → "registered when encountered").
**Approach**: Update normative text in §5.13.2 and §9.3.4 to separate the requirement (availability from next form) from implementation guidance (when codegen occurs).
**Acceptance**: FIXMEs removed, normative text updated.

## Waves

### Wave 1: Design
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Write `design/int/step4-macro-blocking.md` | done | Per-sexp expansion flow, inline compile-and-continue, expander extraction |
| /typecheck | Assess call-graph dep extraction, write `design/typecheck/step4-macro-deps.md` | done | Decision 21: populate call_graph_edges, write callees to ModuleEntry |
| /spec | Resolve 2 FIXMEs on macro ordering language | done | §5.13.2 and §9.3.4 updated |

### Wave 2: Design Review + Iteration
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review design docs | done | 2B + 4I + 3S; Blockers resolved by Decision 21 |
| /arch | Decision 21: TC-sourced call graph | done | `callees: Vec<FQSymbol>` on ModuleEntry, populated during typecheck |
| /qa | Derive test cases from design docs | done | 13 test cases planned |
| /arch | Re-review revised design docs | done | APPROVED, 3 new suggestions |

### Wave 3: Implementation + Test + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Implement Step 4 | done | per-sexp Pass 2, inline macro compilation, C2 filter, begin-splicing |
| /typecheck | Populate call_graph_edges, write callees to ModuleEntry | done | Decision 21 implementation |
| /qa | Write 10 integration tests | done | All passing with v4-vs-old parity |
| /review | Review new code | done | 0B, 4I, 6S |

### Wave 4: Build/Test/Review Cycle
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Fix I-1 (transitive walk), I-2 (check_form), I-3 (scheduler notifications) | done | |
| /typecheck | Fix I-4 (callees accessor), S-3 (dedup helper) | done | |
| /qa | Full suite verification | done | 1684 passed, 11 pre-existing sketch_port, 0 ignored |

## Notes

**Design decisions (from /arch review):**

1. **No suspension/resumption in Step 4**: Inline compile-and-continue. When Pass 2 hits a macro needing codegen, the same thread compiles deps inline via `compile_and_register_defn` and continues — all state stays on the stack. No `ResumeTypecheck`, no `SuspendedState`, no worker-local HashMap. Step 11 will introduce real suspension/resumption when multi-threading requires it.

2. **Macro codegen ordering**: Demand-driven. `defmacro` encountered → register in module table (typecheck body, store clause info + AST, populate `callees` in `ModuleEntry` per Decision 21). No codegen. When a macro *call* is encountered later in Pass 2 and function pointer doesn't exist → read `callees` from `ModuleEntry` via `tc.symbol_table(module).get(name).callees`, walk transitively, `block_for_macro_codegen` with uncompiled deps. Matches `pipeline-v4.md` §3.2 step 5.

3. **Macro expansion point**: Per-sexp, before `build_top_level`, in the worker. Pass `NoOpExpander` to `build_top_level` after expanding the sexp. Extract marshal/unmarshal/invoke from `src/expander.rs` as free functions. Keeps blocking logic in the worker, not the frontend.

4. **No state across blocks**: Inline compile-and-continue keeps all state on the call stack. No `SuspendedState` needed. Blocking (in the suspension/resumption sense) only becomes relevant at Step 11 with multi-threading.

5. **Macro forward references within bodies**: A macro body can only call functions defined before it (spec §9.2.5). Pass 1 registers all signatures. When typechecking the macro body on demand, all referenced functions have signatures available from Pass 1 — their bodies may not be typechecked yet, but macro body typecheck only needs type signatures.

## Outcome

### Delivered

- **Per-sexp Pass 2 with macro expansion** (`src/worker.rs`): `process_module_forms` restructured from bulk `build_program` + `NoOpExpander` to per-sexp expansion interleaved with typechecking. Macros expanded inline, begin-spliced forms registered and checked.
- **Inline compile-and-continue** for macro deps: when a macro call needs codegen, transitive deps walked via `ModuleEntry.callees`, uncompiled deps compiled inline, macro function compiled, expansion proceeds. No suspension/resumption.
- **Decision 21: TC-sourced call graph** (`cranelisp-typecheck`, `cranelisp-types`): `callees: Vec<FQSymbol>` on `ModuleEntry::Def` and `ModuleEntry::Macro`. Populated during `merge_form_result` from `FormCheckResult.call_graph_edges`. `ModuleEntry::callees()` accessor. `write_callees_to_module_entries` helper.
- **C2 filter relaxation** (`src/session_v4.rs`): `defmacro` no longer rejected — macro programs qualify for v4 path.
- **Expander extraction** (`src/expander.rs`): key functions made `pub(crate)` for v4 worker reuse.
- **Spec clarification** (`spec/05-definitions.md`, `spec/09-macros.md`): normative text updated — macro availability from next form, implementation MAY defer codegen.
- **10 new macro parity tests** (`tests/v4_pipeline.rs`): simple, quasiquote, helper fn, macro chain, interleaved, multi-clause, define-before-use error, transitive deps, type error, begin-splicing. All verify v4-vs-old parity.
- **Architecture docs updated**: Decision 21 recorded in `design/arch/CLAUDE.md`, `pipeline-v4.md`, `concurrent-pipeline.md`, `interfaces.md`, `pipeline-v4-roadmap.md`.
- **Design docs**: `design/int/step4-macro-blocking.md`, `design/typecheck/step4-macro-deps.md`.

### Test Results

1684 passed, 11 pre-existing sketch_port failures, 0 ignored, 0 new failures.

### Deferred

- **S-2**: Debug logging at expansion/blocking points — not added. Low priority.
- **S-4**: `sexp_contains_macro_call` may over-match bare symbols in non-call position — cosmetic, no incorrect behavior.
- **S-5**: Test naming inconsistency (`test_v4_` vs `v4_macro_`) — cosmetic.
- **S-6**: Fresh JIT per macro clause (design doc says "shared JIT") — functionally correct, design doc needs update.
- **Missing test coverage**: expansion depth limit, defmacro-in-results.

### Findings

- **Decision 21 (TC-sourced call graph)** is a significant architectural decision affecting the whole pipeline. `callees: Vec<FQSymbol>` on `ModuleEntry` serves macro dep scheduling, incremental recomp, mutual recursion detection, and non-tail-call warnings. Single source of truth from typechecking.
- **Inline compile-and-continue** is dramatically simpler than the suspension/resumption mechanism originally designed. The roadmap's Step 4 description already implied this approach. Multi-threaded suspension is correctly deferred to Step 11.
- **Spec clarification** separates the requirement (macro available from next form) from implementation guidance (when codegen occurs). Implementations MAY defer compilation until first use.
- **`merge_form_result` eagerly writes callees** to `ModuleEntry`, making them available immediately during Pass 2 — no need to wait for `finalize_check_result`. This was key to avoiding the S-1 timing issue.
- **Begin-splicing** required re-registering expanded forms in Pass 1 before checking bodies in Pass 2. This was discovered during testing and fixed.
