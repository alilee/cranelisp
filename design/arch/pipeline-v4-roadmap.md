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

<!-- FIXME(/int) Sprint 56 Wave 3 /port verification: exemplar/solver.cl fails to
     compile with: "module 'super' not found (imported by 'grid.test')".
     The frontend module_extract captures `(import [super [*]])` as a module
     path named literally "super" (see crates/cranelisp-frontend/src/module_extract.rs
     test_import_super). The v4 scheduler/module loader never rewrites this to
     the parent path. The sketch resolved this in sketch/src/module.rs:1429-1434
     (strip last dotted component: `math.test` super → `math`). Spec requirement
     is spec/08-modules.md §8.3.6 lines 183-195 (MUST rewrite; MUST error if
     parent doesn't exist). This blocks all exemplar modules (grid, solver,
     html, form each use `(mod test (import [super [*]])...)`). Proposed
     resolution: add `resolve_super_imports` pass in src/scheduler.rs or
     src/worker.rs when a module's import_specs are first consumed, rewriting
     `super` → parent path (via `ModuleFullPath::rsplit_once('.')`) and
     erroring on root modules. -->

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
| G10 | Fresh JIT per REPL expression | LOW | `Jit::new_with_symbols()` in `compile_and_execute_expr` | Persistent eval JIT across session |
| G11 | Reload via scoped threads | LOW | `reload_module` spawns scoped worker threads | Re-register through scheduler for persistent workers |

Gaps G9–G11 are all consequences of G9 (no persistent priority workers). Once workers are persistent, reload and eval naturally route through them.

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

#### Step 4b: Persistent priority workers (G9, G10, G11)

Priority workers become session-persistent (spawned in `CompilerSession::new`, parked on condvar). `register_module` enqueues work; workers pick it up. `eval` submits to the scheduler; `reload_module` re-registers via scheduler. Scoped thread spawning eliminated.

This also enables the persistent eval JIT (G10) — the eval path submits dependencies as `BlockingJitCodegen` entries, blocks until notified, then compiles the expression on a session-persistent JIT instance.

**Touches**: `src/session_v4.rs` (worker lifecycle, eval path, reload path), `src/worker.rs` (thread function signature).

**Verification**: All tests pass. No `thread::scope` for workers outside of tests.

### Phase 5: Structural declarations and cache (cleanup)

#### Step 5a: Structural declarations on `SymbolTable`

Add `imports`, `exports`, `platforms`, `submodules` fields to `SymbolTable` for `.cl` regeneration (§6.4). Delete `ModuleStructure` from `SharedState`.

**Touches**: `cranelisp-types/src/module.rs`, `src/session_v4.rs`, `src/save.rs`.

#### Step 5b: Cache serialization via symbol table

`.meta.json` serializes the enriched `SymbolTable` (types, GOT slots, AST bodies, structural declarations). Cache restore reconstructs the full compilation state without re-typechecking. `CodegenInput` stashing no longer needed.

**Touches**: `src/worker.rs` (cache write), `crates/cranelisp-backend/src/cache/`.

## Deferred (not blocking convergence)

| Item | Reason |
|------|--------|
| `SymbolTable<C, L>` generics | API cleanliness. `#[serde(skip)]` on code field is sufficient for now. |
| `FQTypeName` migration | 182 call sites. Display works via `type_modules` lookup. |
| BL range fix (linker.rs) | Only manifests on very large codebases. |
| `Linker` on `SymbolTable` | Depends on generics. Cache-hit `.o` loading works without it. |

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
        Structural decls + cache
            5a: imports/exports
            5b: cache via SymbolTable
```

Phases 3 and 4 are independent and can be done in parallel or either order. Phase 5 depends on both.

## Visual Reference

See `design/arch/sequence-diagram/` for Mermaid sequence diagrams comparing:
- `3dadf5e/` — current implementation (commit 3dadf5e)
- `v4-target.*` — pipeline-v4.md target with colour-highlighted differences
