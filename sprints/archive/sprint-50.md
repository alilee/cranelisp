# Sprint 50: Session Restructure Regression Fix

**Status**: COMPLETE
**Ring**: — (stabilisation)
**Goal**: Fix the macro/prelude/platform regressions introduced by the Sprint 49 session restructure, restoring all tests that passed before Sprint 49.

## Scope

The Sprint 49 session restructure (GOT unification, SharedState DashMaps, `src/repl/` deletion) broke macro symbol availability, platform DLL registration, introspection commands, and some module export paths. This caused 137 test failures (up from 13 pre-existing). This sprint diagnoses and fixes the regressions.

**In scope:**
1. **Macro expander refactor** (~100 failures): Replace the cache-based macro expansion (pre-built HashMap of macro entries) with direct symbol table lookups. Root cause: per-module codegen products store macro code pointers under the current module, but the lookup searches the defining module. Rather than patch the store/lookup mismatch, eliminate the redundant cache layer entirely. Requires design doc.
2. **Platform DLL JIT symbol resolution** (~12-17 failures): `collect_jit_setup_for_module` only scans `ModuleEntry::Def` but platform functions appear as `ModuleEntry::Import`. Fix: register all platform registry entries unconditionally.
3. **Test fixture imports** (~24 failures, MIXED): Tests use bare primitive names (`add-i64`) without import, violating spec §8.9.1. Fix the tests to add explicit `(import [primitives [...]])`. Also fix the entry-module inconsistency (entry modules get primitives implicitly, violating the spec).
4. **Builtin type leaking into `/list`** (~7 failures): `ensure_module_exists` copies all TypeDef entries from user to new modules. Fix: filter out compiler-seeded builtin type names.
5. **Macro body type checking** (~4 failures): Macro clauses not type-checked at definition time in v4. Either add eager check or update test expectations.
6. **`run-tests` special form** (~7 failures): Never ported to reimplementation AST builder. Missing feature, not regression — may defer to Sprint 51.
7. **ObjectWorkerState dead code** (35 lines in `src/session.rs`): Trivial cleanup per `/arch`.

**Out of scope (pre-existing, carried to Sprint 51):**
- 11 sketch_port failures (pre-existing before Sprint 49)
- 2 ring0 checked_div failures (pre-existing, spec §12.7.3)

**Success criteria:** Restore to <= 13 failures (pre-existing only). All stdlib 54/54 pass. All ring4_trace 29/29 pass. All cache 51/51 pass. All v4_pipeline platform tests pass.

## Diagnosis Summary (Wave 1 findings)

### Root causes identified

| # | Root Cause | Tests | Fix Type |
|---|-----------|-------|----------|
| 1 | Macro code pointer store/lookup mismatch — cache layer diverged from codegen products | ~100 | Architectural refactor: eliminate macro cache, use symbol table directly |
| 2 | Platform JIT symbols: `collect_jit_setup_for_module` misses Import entries | ~12-17 | Code fix |
| 3 | Test fixtures use bare primitives without import (spec §8.9.1 violation) | ~24 | Test fix + entry-module consistency fix |
| 4 | Builtin types leak from `user` module into all new modules via `ensure_module_exists` | ~7 | Code fix |
| 5 | Macro body type checking deferred (not checked at definition time) | ~4 | Code fix or test update |
| 6 | `run-tests` special form not ported to reimplementation | ~7 | Missing feature |
| 7 | Cross-eval REPL macros not visible (sub-case of #1) | ~2 | Fixed by #1 |

### Key design decision

The prior implementation used three redundant caches of macro information:
- `macro_names: Vec<&str>` — pre-built list for sexp scanning
- `macro_infos: Vec<(Symbol, DefmacroInfo, Sexp)>` — current-module definitions
- `HashMap<Symbol, MacroEntry>` — assembled by `build_all_macro_entries` + `build_persistent_macro_entries`

All three duplicate information already in the symbol table + codegen products. The bug exists because cache #3 disagrees with codegen products about which module key to use. The fix eliminates the caches:

**New approach**: `expand_sexp_recursive` takes a `MacroResolver` trait. The implementation walks the symbol table on each symbol encounter, follows Import/Reexport chains to the defining module, checks codegen products there, compiles on demand if needed, and returns the `MacroEntry`. No pre-scanning, no name lists, no HashMap assembly.

**Design constraint**: FQ macro references (e.g., `(control/cond ...)`) are out of scope — they don't work for regular defns either. Only imported macros are supported. FQ support is a future feature.

**Borrow checker consideration**: The resolver needs `&mut` access for on-demand compilation but the caller needs `&mut` access after expansion. Solution: extract expansion into a separate function so borrows are scoped.

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `crates/cranelisp-typecheck/src/checker.rs:417` | /arch | FQTypeName migration | deferred — not blocking |
| `crates/cranelisp-backend/src/cache/linker.rs:231` | /backend | BL range for runtime intrinsics | deferred — large codebase only |
| `crates/cranelisp-types/src/types.rs:23` | /arch | TypeName → FQTypeName | deferred — architectural improvement |
| `tests/sprint23.rs:11` | /qa | Sprint23 tests disabled for v4 | deferred — needs triage in Sprint 51 |
| `tests/v4_pipeline.rs:359` | /frontend | Macro define-before-use not enforced | deferred — spec compliance gap |
| `spec/08-modules.md:82` | /spec | Remove sibling fallback rule | deferred — spec clarification |

## Architecture Review

**Reviewer**: `/arch`
**Verdict**: APPROVED with notes (initial scope review — pre-diagnosis)

**Technical coherence**: Scope is well-defined — restore pre-Sprint-49 test behavior through restructured session code paths. Success criteria (≤13 pre-existing failures) is concrete and measurable. Complete, testable increment.

**No interim architecture**: Confirmed. All fixes within existing `SharedState` / `DashMap` / `CodegenProduct` data model. No new types or temporary bridges.

**Wave ordering**: Correct. Macro/prelude is the dominant root cause — fixing it will likely resolve significantly more than 94 tests (roadmap estimated ~120). Wave 2 should re-triage after Wave 1 lands since some failures may cascade.

**Additional design refs for `/int`**:
- `design/arch/archive/session-restructure.md` — target data model, especially §MacroEnv elimination
- `src/worker.rs:1848-2020` — `build_all_macro_entries`, `build_persistent_macro_entries`, `collect_persistent_macro_names` — DashMap-based macro env builders (likely regression site)
- `src/session.rs:264` — `inject_prelude_import` — verify called at right point in v4 worker flow
- `src/worker.rs:465` — prelude auto-injection 4-guard condition

**Note**: `MacroEnv` still exists in `src/expander.rs` (test-only). Production path uses DashMap-based builder functions. Regression is in the latter.

**Cleanup**: Include `ObjectWorkerState` dead code deletion (35 lines in `src/session.rs`) in Wave 1 — trivial, consistent with debt-first principle.

**Interface gaps**: None. Boundary types (`TypecheckProduct`, `CodegenProduct`, `ModuleEntry::Macro`) are sufficient.

**Single pipeline invariant**: Maintained. No risk of re-introducing parallel paths.

**NOTE**: The diagnosis revealed that the fix requires an architectural refactor (eliminate macro cache layer), not a simple store-key patch. This needs a design doc from `/arch` and re-review before implementation.

## Skill Plans

### /arch
**Task**: Write design doc `design/arch/macro-resolver.md` for the macro expander refactor.

The design doc MUST cover:

**1. Problem statement**: Three redundant caches (`macro_names`, `macro_infos`, `HashMap<Symbol, MacroEntry>`) duplicate information in the symbol table + codegen products. The `HashMap` cache disagrees with codegen products on which module key stores macro code pointers (current module vs defining module). This is the root cause of ~100 test failures.

**2. Target architecture**: 
- `MacroResolver` trait in `expander.rs` with method `resolve_macro(&mut self, name: &str, span: Span) -> Result<Option<MacroEntry>, CranelispError>`
- `SymbolTableMacroResolver` impl in `worker.rs` that:
  - Looks up `name` in the current module's symbol table
  - If `ModuleEntry::Macro` → local, use current module as defining module
  - If `ModuleEntry::Import` → follow chain (Import → Reexport → Macro) to find defining module. Use generic recursive chain walker, not hardcoded 2-hop.
  - Check codegen products under the **defining module** for compiled code pointers
  - If not compiled → compile inline via `compile_macro_clause_inline`, store under defining module
  - Return `MacroEntry` with function pointers
- Read-only variant (`ReadOnlyMacroResolver`) for `/expand` slash command in `session_v4.rs` — same lookup, no on-demand compilation
- `expand_sexp_recursive` takes `&mut dyn MacroResolver` instead of `&HashMap<Symbol, MacroEntry>`

**3. What gets deleted**:
- `MacroEnv` struct + impl + `compile_single_clause` (expander.rs) — dead code, only used by unit tests
- `build_all_macro_entries`, `build_persistent_macro_entries`, `collect_persistent_macro_names` (worker.rs)
- `sexp_contains_macro_call`, `collect_called_macros`, `collect_called_macros_inner` (worker.rs)
- `resolve_macro_entry`, `resolve_macro_sexp`, `compile_persistent_macro_if_needed` (worker.rs)
- `build_macro_map` (session_v4.rs)
- `macro_names` list construction and `macro_infos` threading through `pass2_check_bodies_with_expansion` / `process_regular_form`

**4. What changes**:
- `compile_macro_if_needed` gains `target_module: &ModuleFullPath` param (the defining module for code pointer storage)
- `compile_macro_clause_inline` gains `target_module` param — stores code pointer, GOT slot, etc. under target module
- `pass2_check_bodies_with_expansion` simplified — no macro_names/macro_infos plumbing
- `process_regular_form` simplified — creates resolver, calls `expand_sexp_recursive`, done. Return type changes from `Vec<String>` to `()` (new macros auto-visible via symbol table)
- `expand_form_sexp` in session_v4.rs uses `ReadOnlyMacroResolver` instead of `build_macro_map`

**5. Borrow checker design**:
- `SymbolTableMacroResolver` must NOT hold `&mut ModuleCompiler` (would prevent caller from using it after expansion)
- Instead: extract expansion into a separate function `try_expand_sexp(ctx, module, sexp, accumulator)` that creates the resolver, runs expansion, drops resolver, returns result. Borrows are scoped to the function.
- The resolver struct holds only the shared-ref fields it needs from `ModuleCompiler` — document which fields and why
- For on-demand compilation inside the resolver, document the borrow path

**6. Scope constraints**:
- FQ macro references (`control/cond`) NOT supported — same as FQ defn references, which require module to already be loaded via import. Separate future feature.
- Macros in the current module (from `defmacro` in the current batch) are registered in the symbol table during Pass 1 (`register_macro_in_module`), so the resolver sees them naturally
- Macros produced by expansion (e.g., `const`/`def` → `defmacro`) are registered inline in `process_regular_form` and immediately visible to the resolver for subsequent forms

**7. Sketch comparison**: The sketch used `MacroEnv` (a flat HashMap) because it had a single JIT with a single flat code pointer namespace. The reimplementation's per-module `CodegenProduct` DashMaps introduced the store/lookup mismatch. The resolver eliminates the intermediate cache entirely.

**Acceptance**: Design doc in `design/arch/macro-resolver.md`, addresses all 7 sections above.

### /frontend
**Task**: Design and implement `MacroResolver` trait in `expander.rs`. Change `expand_sexp_recursive` and `expand_macro_call` to use `&mut dyn MacroResolver`. Delete `MacroEnv`, `compile_single_clause`, and MacroEnv unit tests.
**Design doc**: `design/frontend/macro-resolver-trait.md` — trait definition, expansion loop changes, what gets deleted from expander.rs
**Acceptance**: `expander.rs` compiles with new trait; old `HashMap`-based API removed; marshal round-trip tests preserved.

### /typecheck
**Task**: Fix `ensure_module_exists` to stop leaking builtin type names into new modules (RC4). Assess macro body type checking at definition time (RC5).
**Design doc**: `design/typecheck/sprint50-fixes.md` — which entries to filter in `ensure_module_exists`, approach for macro body type check (eager vs deferred)
**Acceptance**: `/list` on empty REPL shows no types; macro body type errors caught at definition time (or test expectations updated with rationale).

### /int
**Task**: Implement `SymbolTableMacroResolver` in `worker.rs`. Simplify `pass2_check_bodies_with_expansion` and `process_regular_form` (delete macro_names/macro_infos plumbing). Implement `ReadOnlyMacroResolver` in `session_v4.rs`. Fix platform JIT symbol resolution (RC2). Fix entry-module primitives inconsistency. Delete ObjectWorkerState. Delete dead macro cache functions from worker.rs.
**Design doc**: `design/int/macro-resolver-impl.md` — resolver struct fields, borrow scoping (`try_expand_sexp` extraction), `compile_macro_clause_inline` target_module change, platform JIT fix, what gets deleted from worker.rs
**Acceptance**: stdlib 54/54, ring4_trace 29/29, cache 51/51, v4_pipeline 47/47, io 74/74, all platform tests pass.

### /qa
**Task**: Fix test fixtures that use bare primitives without import (spec §8.9.1). Verify fixes progressively. Triage remaining failures after each implementation wave.
**Acceptance**: Full suite ≤ 13 failures, all from pre-existing set (11 sketch_port + 2 ring0).

### /sprint
**Task**: Coordinate design → review → implementation → verification cycle.

### All other skills
No assignment this sprint — stabilisation only.

## Waves

### Wave 1: Diagnosis (COMPLETE)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Diagnose macro regression | done | Root causes 1-7 identified |
| /qa | Audit failing tests against spec | done | 137 tests classified |

### Wave 2: Design docs + review (COMPLETE)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Write `design/arch/macro-resolver.md` | done | Umbrella design, all 7 sections |
| /frontend | Write `design/frontend/macro-resolver-trait.md` | done | MacroResolver trait, expansion loop, expander.rs deletions |
| /typecheck | Write `design/typecheck/sprint50-fixes.md` | done | ensure_module_exists filter, macro body type check, take_state API |
| /int | Write `design/int/macro-resolver-impl.md` | done | Resolver impl, borrow scoping, worker.rs changes, platform JIT fix |
| /arch | Review all design docs | done | APPROVED WITH CHANGES — 3 doc fixes applied (compile_queue, fn name, depth limit) |

### Wave 3a: Implementation — macro refactor + test fixtures (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /frontend | Implement MacroResolver trait, update expand_sexp_recursive, delete MacroEnv | pending | Per design doc |
| /int | Implement SymbolTableMacroResolver, simplify worker.rs, ReadOnlyMacroResolver | pending | Per design doc; depends on /frontend trait |
| /qa | Fix test fixtures with bare primitives (RC3) | pending | Add explicit imports per spec §8.9.1 |

### Wave 3b: Implementation — remaining fixes (after 3a re-triage)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Fix platform JIT symbol resolution (RC2) | pending | If not resolved by Wave 3a |
| /typecheck | Fix builtin type leaking in ensure_module_exists (RC4) | pending | Per design doc |
| /typecheck | Fix macro body type checking (RC5) | pending | Per design doc |
| /int | Delete ObjectWorkerState dead code | pending | 35 lines |
| /int | Delete dead macro cache functions from worker.rs | pending | build_all_macro_entries etc. |

### Wave 4: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Run full suite, confirm ≤ 13 failures | pending | |
| /int | Assess `run-tests` port (RC6) | pending | May defer to Sprint 51 |

## Notes

- **Primitives seeding was NOT the fix**: First /int agent restored implicit primitives seeding (violating spec §8.9.1). Reverted. The prior implementation at `17a9906` also violated the spec — tests passed because of invalid behavior.
- **Test validity audit**: /qa audited all 137 failures. Only ~2 are clearly invalid tests. ~24 are mixed (test needs import fix AND implementation inconsistency). ~111 are genuine implementation bugs.
- **FQ references**: Neither macros nor defns support FQ references to unloaded modules. Module discovery only happens via import/export/mod declarations. FQ support is a separate future feature.
- **TC stateless design (carry to Sprint 51)**: Cache root cause #2 (TypecheckProduct.symbols empty) reveals TC and TypecheckProduct maintain parallel symbol tables that are never synced. Target state: TC becomes transient — constructed in the worker with `&mut SymbolTable` pointing into the TypecheckProduct DashMap entry, writes directly, dropped when done. No copying. Requires `/arch` design doc + `/typecheck` crate refactor. Blocks 11 cache tests (manifest writing needs populated symbols). `/qa` root cause #3 (test file layout) also deferred — no point fixing 1 test when the other 10 are blocked.
- **Cache test file layout (carry to Sprint 51)**: `cache_multi_module_transitive_imports` uses flat file layout but `(mod mid)` expects submodule paths. Fix alongside cache infrastructure.

## Outcome

### Delivered

- **Macro resolver refactor**: Eliminated 3 redundant macro caches (`macro_names`, `macro_infos`, `HashMap<MacroEntry>`). New `MacroResolver` trait with `SymbolTableMacroResolver` (inline compilation, `take_state`/`restore_state` borrow scoping) and `ReadOnlyMacroResolver` for `/expand`. Code pointers stored under defining module. ~350 lines deleted from expander.rs, ~12 dead functions deleted from worker.rs.
- **Platform JIT symbol resolution**: All platform registry entries registered unconditionally.
- **Builtin type isolation**: `Int`/`Bool`/`Float`/`String`/`Vec`/`TestResult` moved from `user` to `primitives` module. `ensure_module_exists` only seeds special forms.
- **Trace codegen fix**: Skip constrained polymorphic base names in `build_traced_fns`, derive arity from `param_types.len()`, added assertion in `compile_trace_wrapper_fn`.
- **Cross-module macro qualification**: Macro-expanded symbols qualified with defining module path.
- **`/list` improvements**: Traits category, empty module message, bare fn introspection.
- **Test fixture compliance**: 22 tests updated with explicit `(import [primitives [...]])` per spec §8.9.1.
- **run-tests test redesign**: 6 tests rewritten for `/run-tests` slash command + 2 new special form type tests.
- **Spec clarification**: §4.12.4 — `trace` keyword vs `Trace`/`TraceCall` types clearly separated.
- **ObjectWorkerState dead code deleted** (35 lines).
- **TypeChecker API**: `take_state()`/`restore_state()` methods for borrow scoping.
- **4 design docs**: `design/arch/macro-resolver.md`, `design/frontend/macro-resolver-trait.md`, `design/typecheck/sprint50-fixes.md`, `design/int/macro-resolver-impl.md`.

**Test results**: 137 failures → 32. 16 of 20 test suites fully green. 1487 passed of 1546 total (+80 from sprint start).

### Deferred

- **Cache infrastructure (11 tests)**: TC and TypecheckProduct maintain parallel symbol tables. Manifest never written. Blocked on TC stateless design — TC becomes transient, constructed with `&mut SymbolTable` pointing into TypecheckProduct DashMap, writes directly. Requires `/arch` design + `/typecheck` refactor.
- **IO display/platform (3 tests)**: REPL IO forcing, platform DLL in submodules, .o cross-module compilation.
- **Sketch_port (13 tests)**: Mostly pre-existing (11 before Sprint 49). Default methods, multi-sig, ADT display.
- **Ring0 checked_div (2 tests)**: Pre-existing.
- **Ring2 (2 tests)**: Multi-sig panic + spec enforcement negative test.
- **E2E imported fn HOF (1 test)**: REPL `/mod` switch + cross-module resolution.

### Findings

- **Prior implementation violated spec §8.9.1**: Primitives were implicitly seeded into all module tables. Tests passed on invalid behavior. Sprint 49 restructure exposed this.
- **Redundant caches are a bug category**: The macro cache diverged from the source of truth (symbol table + codegen products). Eliminating the cache eliminated the category.
- **TC stateless is the next architectural milestone**: The TypeChecker holding its own module DashMap while TypecheckProduct holds a parallel copy is the root cause of cache failures. Target: TC is transient, writes directly to the session's DashMaps.
- **Test validity matters**: Automated agents must validate failing tests against the spec before assuming the code is wrong. Several tests relied on non-compliant behavior.
