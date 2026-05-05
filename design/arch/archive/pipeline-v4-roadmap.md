# Pipeline v4 Roadmap

Status of the scheduler-driven architecture described in `pipeline-v4.md` and `concurrent-pipeline.md`.

## Current State (verified 2026-04-16)

The v4 scheduler-driven pipeline is the only pipeline. `CompilerSession` in `session_v4.rs` is the unified session type. `main.rs` uses one code path for Run/Link/REPL.

**Build status**: Does not compile at HEAD. Commit `3dadf5e` introduced a placeholder `GOT_TABLE` type on `SymbolTable` as part of the §9 data model design. Reverting that one field restores compilation. **1546 pass, 200 fail** out of 1604 tests (at HEAD~1).

**Failure breakdown** (at HEAD~1, last compiling commit):

| Category | Failures | Root Cause |
|----------|----------|------------|
| sprint23 (watch) | 38 | `notify` kqueue backend misses file modifications on macOS |
| ring4_trace | 38 | Trace intrinsic signature conflict (`cranelisp_trace_restore_got`) |
| sketch_port | 14 | Needs triage — mix of real gaps and sketch-specific |
| ring0 | 4 | checked_div missing runtime error check; 2 related |
| v4_repl_eval | 2 | Trace-as-expression |
| v4_pipeline | 2 | Cache-hit dependency loading |
| cache | 2 | Cross-module GOT / nice worker interaction |

### What's Implemented

The pipeline orchestration layer is complete. What remains is the **data model convergence** — collapsing intermediate types into the symbol table so that `compile_to_module` is self-sufficient.

| Capability | Status |
|------------|--------|
| One `CompilerSession`, one `run()`, all modes | Done |
| `CompileScheduler` with module lifecycle, priority ladder, blocking/unblocking | Done |
| Per-form typecheck via `tc.check_form()` + `FormCheckResult` | Done |
| Form-by-form worker loop (`process_module_forms`) | Done |
| Macro expansion blocking via scheduler priority codegen queue | Done |
| Lazy dependency discovery during form processing | Done |
| Expansion as free function in `src/expander.rs` | Done |
| REPL eval with TC snapshot/restore, Additive strategy | Done |
| Error cascade via `notify_module_failed` + `cascade_failure_locked` | Done |
| DashMap-backed symbol tables and codegen products | Done |
| Cache-hit loading via `try_cache_hit_load()` | Done |
| GOT with atomic slot-based table (`GotTable`) | Done |
| Nice workers as persistent threads (`.o` production) | Done |
| `--link` mode (`link_by_name` + exe infrastructure) | Done |
| Introspection (source, sexp, expanded, ast, clif_ir, disasm) | Done |
| File watcher (`src/watch.rs`, init/sync/poll_and_reload) | Done |
| Old pipeline deleted (~12k+ lines removed) | Done |

<!-- Super-import rewrite: arbitrated Sprint 57 Wave 0 — Option A (frontend capture-time).
     See `design/arch/super-import-arbitration.md`. Implementation owned by `/frontend`
     in `crates/cranelisp-frontend/src/module_extract.rs`. -->

### What's NOT Implemented (v4 target gaps)

The audit compares actual code against `pipeline-v4.md` §9. Nine structural gaps remain, all related to the data model convergence. See `design/arch/sequence-diagram/` for visual comparison.

| # | Gap | Severity | What exists now | What v4 §9 specifies |
|---|-----|----------|-----------------|---------------------|
| G1 | `ModuleEntry::Def` lacks `ast` field | HIGH | Bodies in transient `CodegenInput.program: Vec<TopLevel>` | `ast: Option<DefnVariant>` on entry |
| G2 | `CheckResult` still a boundary type | HIGH | Passed from typecheck to codegen via `CodegenInput` | Eliminated — TC writes to symbol table |
| G3 | Resolved calls / expr types in side maps | HIGH | `HashMap<Span, ResolvedCall>`, `HashMap<Span, Type>` on `CheckResult` | Directly on AST nodes |
| G4 | `compile_to_module` takes program + CheckResult | HIGH | `(path, program, check, symbol_tables, module)` | `(path, names, symbol_tables, module)` |
| G5 | Two codegen entry points | HIGH | `codegen_module_symbols` (JIT) + `compile_to_module` (object) | `compile_to_module` only (§9.3) |
| G6 | Compiled code in separate `CodegenProduct` | MEDIUM | `DashMap<ModuleFullPath, CodegenProduct>` with `DashMap<Symbol, Code>` | `code: Option<C>` on `ModuleEntry::Def` |
| G7 | GOT table on `TypecheckProduct` | MEDIUM | `TypecheckProduct { got, file_path, source_text }` | `got: GotTable` on `SymbolTable` |
| G8 | Separate `PlatformRegistry` | MEDIUM | `HashMap<FQSymbol, PlatformFunction>` | Platform fn ptrs on `ModuleEntry::Def` entries |
| G9 | Scoped priority workers | LOW | Thread scope per `register_module_with_source()` | Session-persistent workers |
| ~~G10~~ | ~~Persistent eval JIT~~ | — | Fresh `JIT` per REPL expression | **Correct target — no work.** See Decision 31: eval compiles on a fresh `JITModule` wrapped in our `Jit` newtype whose custom `Drop` calls `unsafe free_memory()` after the result is consumed. The previously-stated target (persistent eval JIT reused across evals) has been retracted: it assumed `Arc<Jit>` drop would reclaim pages, but Cranelift 0.116 `Memory::drop` leaks on purpose. Per-eval fresh JIT + explicit reclaim is the canonical shape. |
| G11 | Reload via scoped threads | LOW | `reload_module` spawns scoped worker threads | Re-register through scheduler for persistent workers |
| G12 | `SymbolTable<C, L>` generics inactive | MEDIUM | Concrete `SymbolTable` + raw `*const u8` on `ModuleEntry::Def.code` + `SharedState.kept_jits` retention pool | `SymbolTable<C: CodeStore, L: LinkerStore>` parameterised per §9.1; `Arc<Jit>` directly on `ModuleEntry::Def.code`; per-redefinition reclaim. See Decision 31 Scenario 2 + Decision 25 rescheduling note. |

Gaps G9 and G11 are consequences of G9 (no persistent priority workers). Once workers are persistent, reload naturally routes through them. G10 is no longer a gap — see Decision 31. G12 is the new gap that emerged when Decision 31 retired G10: activating the `SymbolTable<C, L>` generics is what lets `Arc<Jit>` live on the entry (Scenario 2 of Decision 31's table) rather than in the session retention pool. Phase 5 Step 5c closes it.

## Completed Steps

| Step | Description | Sprint |
|------|-------------|--------|
| 0 | North-star main.rs — one `run()`, all modes | 49 |
| 1 | Per-form typecheck API (`tc.check_form()`, `FormCheckResult`) | 40 |
| 2 | CompileScheduler (lifecycle, priority ladder, condvar blocking) | 41 |
| 3 | Form-by-form worker loop (`process_module_forms()`) | 41 |
| 4 | Macro expansion blocking (`block_for_macro_codegen()`) | 42 |
| 5 | Lazy dependency discovery (imports trigger recursive loading) | 43 |
| 6 | Remove MacroExpander trait (expansion is free fn in `expander.rs`) | 43 |
| 7 | REPL eval via scheduler (Additive strategy, TC snapshot/restore) | 44 |
| 8 | Platform registry (`PlatformRegistry`, DLL loading) | 45 |
| 9 | Error cascade (`notify_module_failed`, `cascade_failure_locked`) | 45 |
| 10 | Nice workers as persistent threads (`.o` production) | 46 |
| 11 | Persistent priority workers — **deferred**, scoped workers correct | — |
| 12 | DashMap (TC module tables, codegen products) | 47 |
| 13 | Cache-hit loading (`try_cache_hit_load()`, symbol table restore) | 48 |
| 14 | File watcher (`src/watch.rs`, init/sync/poll_and_reload) | REPL rework |
| 15 | Link mode, dead code cleanup, v4 test infrastructure | 49+ |

## Remaining Work

### Phase 0: Stabilise (fix what's broken)

Get to green on the existing test suite before any data model work. Every convergence step below must land on a green baseline and leave it green.

| Task | Tests | Owner | Notes |
|------|-------|-------|-------|
| **P0.1** Revert `GOT_TABLE` placeholder | 0 | /int | Restore compilation. One-line fix. |
| **P0.2** Fix trace intrinsic signature | 38 | /backend | `cranelisp_trace_restore_got` void-return exception in `declare_intrinsics_generic` |
| **P0.3** Fix file watcher tests | 38 | /int | Replace `RecommendedWatcher` with `FsEventWatcher` on macOS |
| **P0.4** Triage sketch_port failures | 14 | /qa | Classify: real gap vs sketch-specific. Fix or delete. |
| **P0.5** Fix checked-div | 4 | /int | Add `take_runtime_error()` check in `compile_and_execute_expr` |
| **P0.6** Fix remaining (v4_pipeline, v4_repl_eval, cache) | 6 | /int + /backend | Cache GOT symbol registration, trace-as-expression |

**Exit criterion**: 0 test failures. This is the baseline for convergence work.

### Phase 1: AST on symbol table (G1 + G2 + G3)

The foundational change. Once AST bodies, types, and resolved calls live on `ModuleEntry`, every downstream step becomes possible.

#### Step 1a: Add `ast` to `ModuleEntry::Def` (G1)

Add an `ast: Option<Defn>` field to `ModuleEntry::Def`. Typecheck stores the typechecked defn body on the entry after `check_form(CheckBody)`. Initially duplicated — both the entry and the existing `CodegenInput.program` carry the body. No consumers change yet.

**Touches**: `cranelisp-types/src/module.rs` (add field), `src/worker.rs` (write to entry after typecheck).

**Verification**: All tests still pass. The new field is write-only in this step.

#### Step 1b: Move resolved calls and expr types onto AST nodes (G3)

Add `resolved_call: Option<ResolvedCall>` to `Expr::Apply` and `inferred_type: Option<Type>` to every `Expr` variant (or a wrapping struct). Typecheck populates these during inference instead of (or in addition to) the `HashMap<Span, _>` side maps.

**Touches**: `cranelisp-types/src/ast.rs` (add fields), `cranelisp-typecheck/src/checker.rs` (write to AST nodes).

**Verification**: Both old (side map) and new (AST node) paths populated. Tests pass. Add assertions that they agree.

#### Step 1c: Backend reads from AST nodes (G3 completion)

`compile_to_module` and `FnCompiler` read resolved calls and expr types from AST nodes instead of `CheckResult` side maps. Side maps become optional / deprecated.

**Touches**: `cranelisp-backend/src/compiler/*.rs` (read from AST nodes), `cranelisp-backend/src/lib.rs` (stop requiring side maps).

**Verification**: All tests pass reading from AST nodes. Side maps can be removed.

#### Step 1d: Eliminate `CheckResult` as boundary type (G2)

`compile_to_module` no longer takes `CheckResult`. It reads everything from `ModuleEntry::Def.ast` (body + resolved calls + types) and `ModuleEntry::Def.scheme` (type signature). The `CheckResult` struct is either deleted or reduced to a typecheck-internal type (warnings + display info only).

**Touches**: `cranelisp-backend/src/lib.rs` (new signature), `src/worker.rs` (stop building CodegenInput), `src/session_v4.rs` (stop stashing CheckResult).

**Verification**: All tests pass. `CodegenInput` type deleted.

### Phase 2: Single codegen entry point (G4 + G5)

With AST on symbol table entries, `compile_to_module` can take symbol names instead of a program.

#### Step 2a: `compile_to_module` takes `names: &[Symbol]`  (G4)

Change the signature to `(path, names, symbol_tables, module)`. Implementation reads `ModuleEntry::Def.ast` for each name. Multi-sig, constrained, default-method entries are all just names in the symbol table — no special expansion logic in the caller.

**Touches**: `cranelisp-backend/src/lib.rs` (new signature + implementation), all callers.

**Verification**: Both JIT and object callers updated. All tests pass.

#### Step 2b: Delete `codegen_module_symbols` (G5)

Route JIT codegen through `compile_to_module` with per-function `JITModule` instances. The batch sweep function and its helpers (`compile_regular_defns`, `compile_and_register_defn_shared`, etc.) are deleted. Priority workers call `compile_to_module` directly.

**Touches**: `src/worker.rs` (delete function, update priority worker), `src/pipeline.rs` (may be substantially reduced or deleted).

**Verification**: All tests pass. Only one codegen path exists.

### Phase 3: Consolidate per-module state (G6 + G7)

Collapse the intermediate DashMaps into the symbol table.

#### Step 3a: Move GOT table onto `SymbolTable` (G7)

Add `got: GotTable` field to `SymbolTable`. GOT created at module registration time. `TypecheckProduct` reduced to file metadata only, or deleted.

**Touches**: `cranelisp-types/src/module.rs`, `cranelisp-backend/src/got.rs`, `src/session_v4.rs` (delete `TypecheckProduct` or reduce it).

**Verification**: All tests pass. GOT access goes through symbol table.

#### Step 3b: Move compiled code onto `ModuleEntry::Def` (G6)

Add `code: Option<Code>` to `ModuleEntry::Def` (initially not generic — `Code` is a concrete type from the integration layer). `CodegenProduct` DashMap eliminated. `Introspection` remains separate (display-only data, not needed for compilation).

This requires `SymbolTable` to be in a `DashMap` that allows concurrent read/write since codegen workers write `code` while typecheck workers read `scheme`. Already the case — `DashMap<ModuleFullPath, SymbolTable>` with per-module granularity.

**Touches**: `cranelisp-types/src/module.rs` (add field), `src/worker.rs` (write code to entry), `src/session_v4.rs` (delete `CodegenProduct`).

**Verification**: All tests pass. Code pointers read from symbol table.

**Note on generics**: `pipeline-v4.md` §9.1 specifies `SymbolTable<C: CodeStore, L: LinkerStore>` generics so that typecheck and backend crates can work with `SymbolTable<()>` (no code dependency). This is an API cleanliness concern, not a prerequisite. The initial implementation can use `#[serde(skip)]` on the `code` field and defer generics until the coupling becomes a problem. The priority is eliminating the separate DashMap, not achieving generic purity.

### Phase 4: Platform and worker convergence (G8 + G9)

#### Step 4a: Platform functions on symbol table entries (G8)

Move platform function pointers onto `ModuleEntry::Def` entries with `PrimitiveKind::PlatformEffect`. The IO trampoline resolves platform functions by symbol table lookup. Delete `PlatformRegistry`.

**Touches**: `src/platform_registry.rs` (delete), `src/worker.rs` (platform form handling), IO trampoline code.

**Verification**: All platform / IO tests pass. No separate registry.

#### Step 4b: Persistent priority workers (G9, G11)

Priority workers become session-persistent (spawned in `CompilerSession::new`, parked on condvar). `register_module` enqueues work; workers pick it up. `eval` submits dependencies to the scheduler; `reload_module` re-registers via scheduler. Scoped thread spawning eliminated.

Eval's trailing-expression compile (the `__expr` synthetic defn) continues to use a fresh `JITModule` created inline by the eval path — NOT a worker-owned JIT. Per Decision 31, the `Jit` wrapper has a custom `Drop` that calls `unsafe JITModule::free_memory()`, reclaiming the `__expr` batch's pages once eval consumes the result and returns. The dependency compiles submitted to `BlockingJitCodegen` run on worker-owned per-batch JITs under the same reclaim primitive. There is no "persistent eval JIT" — that framing was retracted (see the G10 row in the table above).

**Touches**: `src/session_v4.rs` (worker lifecycle, eval path, reload path), `src/worker.rs` (thread function signature), `crates/cranelisp-backend/src/jit.rs` (custom `Drop` on `Jit` — depends on Decision 31; /backend implementation).

**Verification**: All tests pass. No `thread::scope` for workers outside of tests.

### Phase 5: Structural declarations and cache (cleanup)

#### Step 5a: Structural declarations on `SymbolTable`

Add `imports`, `exports`, `platforms`, `submodules` fields to `SymbolTable` for `.cl` regeneration (§6.4). Delete `ModuleStructure` from `SharedState`.

**Touches**: `cranelisp-types/src/module.rs`, `src/session_v4.rs`, `src/save.rs`.

#### Step 5b: Cache serialization via symbol table

`.meta.json` serializes the enriched `SymbolTable` (types, GOT slots, AST bodies, structural declarations). Cache restore reconstructs the full compilation state without re-typechecking. `CodegenInput` stashing no longer needed.

**Touches**: `src/worker.rs` (cache write), `crates/cranelisp-backend/src/cache/`.

#### Step 5c: Activate `SymbolTable<C, L>` generics (G12) — completes Decision 31 Scenario 2

Parameterise `SymbolTable` with `C: CodeStore` and `L: LinkerStore` trait bounds per `pipeline-v4.md §9.1`. Move `Arc<Jit>` onto `ModuleEntry::Def.code` directly (as the concrete `C` chosen by the integration layer), replacing the current raw-pointer-plus-`SharedState.kept_jits` retention pool. `SharedState.kept_jits` dissolves for Jit retention — if the `LinkerStore` policy genuinely differs (e.g., object-cache-hit rehydration retains linker-resolved pages at a different granularity), `kept_linkers` may persist in a narrower form; otherwise it dissolves too.

**Rationale.** Decision 31 requires `Arc<Jit>` on the entry so that reclaim fires when the last entry referencing a given batch's JIT drops (Scenario 2: defn redefinition). The generics are the DAG-compatible path to that placement — without them, placing `Arc<Jit>` on `ModuleEntry::Def.code` in `cranelisp-types` would require `cranelisp-types → cranelisp-backend` (inverted dependency, forbidden by Principle 3). The generics keep `cranelisp-types` ignorant of the concrete `Jit` type; the integration layer chooses `C = Arc<Jit>` (or a tiny wrapper) at instantiation. Decision 25's "API cleanliness only" deferral rationale was written before Decision 31 emerged and is no longer operative — see the Decision 25 update for the re-scoping.

**Cost.** ~182 call sites mechanically touch the `SymbolTable` type; most are type-annotation-level changes (adding `<C, L>` or `<_, _>` to a path). No behavioural churn inside the changed sites — the work is largely search-and-replace plus bound plumbing.

**Touches**: `crates/cranelisp-types/src/module.rs` (introduce `CodeStore` + `LinkerStore` traits; re-parameterise `SymbolTable` and `ModuleEntry::Def`); all call sites across `src/`, `crates/cranelisp-typecheck/`, `crates/cranelisp-backend/`, `crates/cranelisp-frontend/`; `src/session_v4.rs` (dissolve `kept_jits`; choose the concrete `C` / `L` types for the session's instantiation).

**Verification**: all tests pass; REPL redefinition with `/mem` shows per-redefinition memory reclaim (Scenario 2 fires on the redefinition, not only at session teardown); the session-wide `kept_jits` pool for Jit entries is gone or empty after redefinitions.

**Ordering.** Step 5c lands alongside 5a and 5b in Phase 5. It is independent of 5a (structural declarations) and 5b (cache serialization) — a generics activation touches type annotations everywhere but not the fields 5a and 5b add — so the three can be scheduled in any order once their shared baseline (Phases 1–4) is green. See Decision 25's updated rejected-alternatives discussion and Decision 31's Scenario 2 scheduling footnote for the cross-references.

## Deferred (not blocking convergence)

| Item | Reason |
|------|--------|
| `FQTypeName` migration | 182 call sites. Display works via `type_modules` lookup. |
| BL range fix (linker.rs) | Only manifests on very large codebases. |

## Dependency Graph

```
Phase 0: Stabilise (green baseline)
    │
    ▼
Phase 1: AST on symbol table ──────────────────────┐
    1a: ast field on ModuleEntry                    │
    1b: resolved calls / types on AST nodes         │
    1c: backend reads from AST nodes                │
    1d: eliminate CheckResult boundary              │
    │                                               │
    ▼                                               │
Phase 2: Single codegen entry point                 │
    2a: compile_to_module(names, symbol_tables)      │
    2b: delete codegen_module_symbols               │
    │                                               │
    ├───────────────┬───────────────────────────────┘
    ▼               ▼
Phase 3:        Phase 4:
GOT + code      Platform + workers
on SymbolTable  on SymbolTable
    3a: GOT         4a: platform fns
    3b: code        4b: persistent workers
    │               │
    └───────┬───────┘
            ▼
        Phase 5:
        Structural decls + cache + generics
            5a: imports/exports
            5b: cache via SymbolTable
            5c: SymbolTable<C, L> generics (G12 — Decision 31 Scenario 2)
```

Phases 3 and 4 are independent and can be done in parallel or either order. Phase 5 depends on both. Within Phase 5, 5a / 5b / 5c are independent and may be scheduled in any order.

## Visual Reference

See `design/arch/sequence-diagram/` for Mermaid sequence diagrams comparing:
- `3dadf5e/` — current implementation (commit 3dadf5e)
- `v4-target.*` — pipeline-v4.md target with colour-highlighted differences
