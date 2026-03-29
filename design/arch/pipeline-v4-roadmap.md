# Pipeline v4 Migration Roadmap

How to get from the current state to the scheduler-driven architecture described in `pipeline-v4.md` and `concurrent-pipeline.md`. Each step produces a working compiler — no step leaves things broken.

## Current State

- `compile_unit` (method on `CompilationSession` in `pipeline.rs`) is the single entry point for all compilation: stages 1-5 (parse through typecheck), with codegen enqueued to `CodegenQueue`.
- `CompilationSession` (in `session.rs`) owns: `tc: Mutex<TypeChecker>`, `expander: CraneliftExpander`, `module_deps: Mutex<ModuleDependencyGraph>`, `platform_symbols: RwLock<Vec<(String, *const u8)>>`, `inmem_worker: Mutex<InMemWorkerState>`, `object_worker: Mutex<ObjectWorkerState>`, sync/async codegen queues, `watcher_paused` gate.
- `CompilerSessionV3` exists as the pipeline-v3 target session but is not yet the primary session.
- `CodegenItem` enum (`FromSource` / `FromCache`) + `CodegenPacket` + `CodegenQueue` provide producer-consumer codegen with sync/async modes.
- `CompileUnitResult` is the boundary between stages 1-5 and stages 6-7 (whole-module granularity).
- `tc.check()` typechecks an entire program (`Vec<TopLevel>`) in one call. No per-form typecheck API exists.
- Dependency resolution happens upfront in `compile_unit` stage 2c via recursive `compile_unit` calls with a `compile_stack` for cycle detection.
- Macro expansion uses `CraneliftExpander` (trait object implementing `MacroExpander`) which compiles macros inline during stage 3.
- Cache-hit loading restores type info and enqueues `CodegenItem::FromCache` for Linker loading — functional as of Sprint 40a.
- `CodegenMode::Async` spawns inmem/object worker pools; `CodegenMode::Sync` drains on the calling thread.
- REPL uses `compile_unit` + `codegen_and_execute` for eval. TC snapshot/restore wraps the compile path.

### v3 Migration Status

Steps 1-10 and 14 of `pipeline-v3-roadmap.md` are complete. Steps 11-13 (concurrent codegen worker overlap, coarse RwLock on tc.modules, parallel file I/O) were partially delivered in Sprint 40a:
- `CodegenQueue` and `CodegenMode::Async` infrastructure exists.
- Worker thread spawning and join are implemented.
- `CodegenPacket` carries pre-cloned data for `Send` across threads.
- Actual async codegen is gated behind `new_async()` constructor — tests and REPL still use sync mode.

### What v4 Changes

The v3 pipeline is caller-driven: callers call `compile_unit`, wait for it to return, then flush codegen queues. The v4 pipeline is scheduler-driven: callers register modules, workers pull work from a priority ladder. The key transitions:

1. **Per-form typecheck** replaces whole-program `tc.check()`.
2. **`CompileScheduler`** replaces caller-driven `compile_unit` + flush pattern.
3. **Lazy dependency discovery** replaces upfront recursive `compile_unit` at stage 2c.
4. **Priority codegen queue** replaces inline macro compilation in `CraneliftExpander`.
5. **Workers own JIT state** — no `InMemWorkerState`/`ObjectWorkerState` on session.
6. **Concurrent TypeChecker maps** (DashMap) replace `Mutex<TypeChecker>`.
7. **REPL eval with persistent JIT** replaces `codegen_and_execute` for temporary closures.

## Step 0: North-Star `main.rs`

**Goal**: Create the target `main.rs` from `pipeline-v4.md` §2.2 with all methods stubbed. This is the skeleton that every subsequent step progressively fills in.

**Changes**:
- Create `src/main_v4.rs` (or a `v4_main()` function gated behind a feature flag / CLI flag like `--v4`) with the full structure from `pipeline-v4.md` §2.2.
- All v4 methods are stubbed:
  - `CompilerSession::new(settings, project_root)` → creates a new v4 session wrapping the old `CompilationSession` for delegation.
  - `s.spawn_priority_workers(n)` → `todo!()`
  - `s.spawn_nice_workers(n)` → `todo!()`
  - `s.register_module(&name)` → delegates to existing `compile_unit` + `codegen_and_execute` (the old path).
  - `s.scheduler.wait_inmem_complete()` → `Ok(())` (no-op — old path did it synchronously).
  - `s.scheduler.wait_object_complete()` → `Ok(())` (no-op).
  - `s.trampoline(&name)` → delegates to existing trampoline.
  - `s.link(&name)` → delegates to existing link.
  - `s.process_commands(&src)` → delegates to existing REPL command dispatch.
  - `s.eval(&src)` → delegates to existing `compile_unit` + `codegen_and_execute`.
  - `s.shutdown()` → no-op.
- The old `main()` remains the default. The v4 main is reachable via flag for testing.
- The v4 main works end-to-end by delegating everything to the old path. It is a thin wrapper.

**Main.rs progress**: Full skeleton exists. Every method delegates to the old path. `--v4` flag runs it.

**Verification**: `--v4 --run`, `--v4 --link`, and `--v4` (REPL) produce identical results to the old main. All existing tests unaffected.

## Step 1: Per-Form Typecheck API

**Goal**: TypeChecker gains a `check_form()` method that typechecks one form and returns per-form results, accumulating into the module's state.

**Changes**:
- Add `tc.check_form(module: &ModuleFullPath, form: &TopLevel) -> Result<FormCheckResult, CranelispError>` to `cranelisp-typecheck`. `FormCheckResult` contains: method resolutions, expr_types, constraints, and warnings for this form's symbols.
- `FormCheckResult` accumulates into the module's typecheck state via `tc.merge_form_result(module, form_result)`.
- Rewrite `tc.check()` to iterate forms and call `check_form()` internally — existing callers are unchanged.
- The multi-pass structure (register all signatures, then check all bodies) must still work. `check_form` for a `defn` registers the signature; a second pass calls `check_form` for the body. This means `check()` calls `check_form` in two passes, matching the current multi-pass design.

**Main.rs progress**: No change — `register_module` still delegates to old path which calls `tc.check()`.

**Verification**: `cargo test` passes. `check()` returns identical results. `check_form` is callable independently (add unit tests in `cranelisp-typecheck`).

## Step 2: Introduce `CompileScheduler` (Single-Threaded)

**Goal**: A `CompileScheduler` struct exists with the module lifecycle and priority ladder from `concurrent-pipeline.md`, but runs on a single thread.

**Changes**:
- Define `CompileScheduler`, `SchedulerState`, `ModulePool`, `ModuleState`, `PriorityEntry`, `PriorityStatus`, `PriorityWork`, `WaitKind`, `Waiter` in a new `src/scheduler.rs`.
- Implement the full scheduler interface from `concurrent-pipeline.md` §6: `register_module`, `register_module_cached`, `take_priority_work`, `block_for_typecheck`, `block_for_macro_codegen`, `notify_symbol_typechecked`, `notify_typecheck_done`, `notify_module_failed`, `notify_priority_codegen_complete`, `notify_inmem_codegen_complete`, `notify_inmem_codegen_batch_complete`, `notify_object_codegen_complete`, `take_object_codegen`, `wait_inmem_complete`, `wait_object_complete`, `shutdown`.
- Single-threaded fallback: `take_priority_work` and `take_object_codegen` return immediately (no condvar wait) since there is only one caller.
- Add the scheduler as a field on the v4 `CompilerSession`.
- Unit tests for the scheduler in isolation: register modules, move through lifecycle, verify waiter/unblock logic, verify priority queue ordering, verify cascade failure.

**Main.rs progress**: `CompilerSession::new` creates a scheduler. `spawn_priority_workers` / `spawn_nice_workers` remain `todo!()`. The scheduler exists but is not yet driving compilation.

**Verification**: `cargo test` passes. Scheduler unit tests cover the lifecycle from `concurrent-pipeline.md` §2. The v4 main still delegates to old path.

## Step 3: Form-by-Form Worker Loop

**Goal**: A `priority_worker_loop()` function processes modules form-by-form using `check_form()`, calling scheduler notifications. Single-threaded, running on the calling thread.

**Changes**:
- New function `process_module_forms(session, module, sexps, strategy) -> Result<(), CranelispError>` that:
  1. For each sexp in source order: expand (using existing expander path), build AST, call `tc.check_form()`.
  2. After each form: call `scheduler.notify_symbol_typechecked()`.
  3. If a form is `defmacro`: register the macro in the module table. Do NOT compile it yet.
  4. After all forms: call `scheduler.notify_typecheck_done()`.
- On error: call `scheduler.notify_module_failed()`.
- New function `priority_worker_loop(session)` that calls `scheduler.take_priority_work()` and dispatches:
  - `Typecheck(module)` → `process_module_forms`.
  - `BlockingJitCodegen(module, symbol)` → existing `compile_and_register_defn` (reused from old path).
  - `JitCodegen(module, symbol)` → same codegen as `BlockingJitCodegen`.
- Wire into `register_module`: instead of delegating to `compile_unit`, parse source, register with scheduler, run `priority_worker_loop` until `wait_inmem_complete` returns.

**Main.rs progress**: `register_module` now uses the scheduler + worker loop instead of `compile_unit`. `spawn_priority_workers` becomes a no-op (worker loop runs inline on calling thread). `wait_inmem_complete` and `wait_object_complete` work against the scheduler state. The old `compile_unit` delegation is removed for `register_module`.

**Verification**: Simple programs (no macros, no multi-module dependencies) compile via the v4 main. Results match old path. Old `compile_and_run` test helper unchanged (still uses `CompilationSession`).

## Step 4: Macro Expansion Blocking

**Goal**: When a macro call needs compiled functions, the worker blocks via the scheduler's priority codegen queue instead of compiling inline.

**Changes**:
- When `process_module_forms` encounters a macro call whose function pointer is not yet compiled: typecheck the macro body, walk the call graph, call `scheduler.block_for_macro_codegen(module, needed_symbols)`. Return — the module enters `TypecheckBlocked`.
- The worker loop's `BlockingJitCodegen` handler: reads the symbol's typechecked AST, JIT-compiles it, registers the code pointer in the GOT, calls `scheduler.notify_priority_codegen_complete()`.
- When unblocked, the worker resumes `process_module_forms` from the blocked form. Store resumption point (form index) in `ModuleState`.
- Single-threaded: the worker loop alternates between typecheck and priority codegen — typechecking blocks, the same thread picks up codegen, completes it, unblocks the module, resumes typechecking.

**Main.rs progress**: Programs with macros (including prelude macros) now compile through the v4 path. The REPL `eval` still delegates to old path.

**Verification**: Programs with macros compile correctly via `--v4 --run`. Results match old path.

## Step 5: Lazy Dependency Discovery

**Goal**: Dependencies are discovered during form processing (at import/mod/qualified-ref time), not upfront.

**Changes**:
- When `process_module_forms` encounters an unresolved import: resolve the module path, check cache. On cache hit: restore type info, call `scheduler.register_module_cached()`. On cache miss: parse source, call `scheduler.register_module()`.
- If the needed symbol is not yet available: call `scheduler.block_for_typecheck()`. Return — the module enters `TypecheckBlocked`.
- Prelude injection: when a non-prelude module starts processing, inject `(import [prelude [*]])` as the first form. Triggers prelude discovery via the same lazy path.
- `compile_stack` (cycle detection) replaced by scheduler — circular imports produce a cycle of `TypecheckBlocked` modules which the scheduler detects and fails.

**Main.rs progress**: `register_module` no longer needs to read source or parse — the worker does it. `register_module` just registers the module path with the scheduler; workers resolve the file, read source, parse, and process. Multi-module programs and prelude loading work through the v4 path.

**Verification**: Multi-module programs compile via `--v4 --run`. Circular import detection works. Prelude loads lazily.

## Step 6: Remove MacroExpander Trait

**Goal**: Delete `CraneliftExpander` and `MacroExpander` trait. Macro expansion becomes a free function.

**Changes**:
- Extract macro expansion logic (marshal sexp args, call function pointer, unmarshal result) into a free function `expand_macro(clause: &MacroClauseInfo, args: &[Sexp]) -> Result<Sexp, CranelispError>`.
- `process_module_forms` calls this free function instead of `session.expander.expand()`.
- Delete `CraneliftExpander` struct, `MacroExpander` trait, `expander` field from both session structs.
- The `build_program` function in `cranelisp-frontend` that takes `&dyn MacroExpander` is updated to not require it (macros are looked up from tc module tables, expansion is a free function call).

**Main.rs progress**: No visible change to main — the expander was internal. `CompilerSession` struct shrinks.

**Verification**: `cargo test` passes. All macro tests pass. The `MacroExpander` trait is gone.

## Step 7: REPL Eval with Persistent JIT

**Goal**: REPL `eval` uses the scheduler for definitions and a persistent eval JIT for temporary closures.

**Changes**:
- `session.eval(&src)` submits input to the current REPL module with `Additive` strategy. Definitions go through `process_module_forms` via the scheduler.
- Trailing expression becomes a temporary closure — typechecked in the module's scope, not registered in GOT.
- Eval walks the closure's call graph. Un-codegenned dependencies submitted as `BlockingJitCodegen`. Eval blocks until notified.
- Eval JIT-compiles the closure using a persistent `Jit` instance (retained across evals, private to eval path).
- Calls the closure, returns the result as `Result<Option<Sexp>, CranelispError>`.
- TC snapshot/restore wraps the compile path.
- `process_commands` remains thin (slash commands + blank detection).
- After successful eval with definitions, regenerate and save the REPL module source.

**Main.rs progress**: `eval(&src)` is now the real v4 implementation, not a delegation to old path. The REPL branch of the main match is fully functional. `process_commands` delegates are removed.

**Verification**: All REPL demo files play cleanly. Slash commands work. Error recovery works. `/mod` namespace switching works.

## Step 8: Platform Registry

**Goal**: Platform function pointers and scheduling classes move to `session.platform: Mutex<HashMap<FQSymbol, PlatformFunction>>`.

**Changes**:
- Define `PlatformFunction { fn_ptr: *const u8, scheduling_class: SchedulingClass }`.
- Platform loading: register type signatures in tc module tables, register fn pointers + scheduling classes in `session.platform`.
- Codegen reads platform function pointers from `session.platform`.
- Delete `platform_symbols` and `scheduling_registry` from both session structs.

**Main.rs progress**: No visible change to main. Internal session field cleanup.

**Verification**: Programs with `(platform ...)` forms compile and execute correctly. IO trampoline works.

## Step 9: Failed State and Error Cascade

**Goal**: Module failures cascade through the dependency graph via the scheduler.

**Changes**:
- `notify_module_failed`: move module to `Failed`, store error, walk waiter map. Cascade transitively.
- `wait_inmem_complete` and `wait_object_complete` return `Err` with the first error if any module is `Failed`.
- REPL: on `Failed` eval, TC snapshot/restore rolls back. Failed state cleared.
- Batch: on `Failed`, print error chain and exit.

**Main.rs progress**: The `?` on `wait_inmem_complete()` and `wait_object_complete()` in Run/Link modes now handles real errors. The REPL match arm's `Err(e) => print_error(e)` handles real errors. Error display is functional.

**Verification**: Type error in a dependency cascades. REPL recovers from failed evals. Batch mode exits with clear errors.

## Step 10: Nice Workers for Object Codegen

**Goal**: Nice workers compile modules to `.o` files at low OS priority.

**Changes**:
- Implement `nice_worker_loop(session)`: calls `scheduler.take_object_codegen()`, compiles to `.o` + `.meta.json`, calls `scheduler.notify_object_codegen_complete()`.
- `session.spawn_nice_workers(n)` spawns N threads at nice priority.
- `wait_object_complete` promotes nice workers to normal then blocks.
- Cache-hit modules have `object_done = true` — nice workers skip them.

**Main.rs progress**: `spawn_nice_workers(n)` is no longer `todo!()` — it spawns real threads. `wait_object_complete` blocks on real work. `--run` produces cache files in background. `--link` waits for `.o` files.

**Verification**: Cache files appear after `--run`. `--link` produces a linked binary. Cache valid on next run.

## Step 11: Multi-Threaded Priority Workers

**Goal**: Multiple priority worker threads run in parallel.

**Changes**:
- `session.spawn_priority_workers(n)` spawns N threads running `priority_worker_loop`.
- `take_priority_work` parks on condvar when no work. Woken by registration, unblocking, typecheck completion.
- Workers own thread-local JIT instances.
- GOT writes use atomic stores to pre-assigned slots.

**Main.rs progress**: `spawn_priority_workers(n)` is no longer `todo!()` — it spawns real threads. The calling thread no longer runs the worker loop inline; it just waits. Multi-module programs typecheck in parallel.

**Verification**: `cargo test` passes. Multi-module programs compile with parallelism. No data races.

## Step 12: Concurrent TypeChecker Maps (DashMap)

**Goal**: TypeChecker module tables use concurrent maps for safe multi-worker access.

**Changes**:
- Replace `Mutex<TypeChecker>` with concurrent module tables (`DashMap<ModuleFullPath, CompiledModule>`).
- Per-shard locking: one worker writing its module doesn't block another reading a different module.
- `tc.check_form()` takes `&self`. Internal mutation via DashMap per-shard locks.
- Add `dashmap` dependency to `cranelisp-typecheck`.

**Main.rs progress**: No visible change. Internal data structure upgrade for safe parallelism.

**Verification**: `cargo test` passes. Thread sanitizer clean (`RUSTFLAGS="-Z sanitizer=thread"`).

## Step 13: Cache-Hit Loading via `register_module_cached`

**Goal**: Cache-hit modules enter the scheduler at `TypecheckDone` with type info restored. In-memory code loads on demand via Linker.

**Changes**:
- During lazy dependency discovery (Step 5): when cache valid, restore type info into tc, call `scheduler.register_module_cached(module, symbols)`.
- Cached module enters `TypecheckDone` with `object_done = true`, `inmem_done = false`.
- Inmem codegen worker claiming a cached symbol: load `.o` via Linker (all symbols at once), call `scheduler.notify_inmem_codegen_batch_complete()`.
- Priority codegen for macro deps in cached modules: same Linker fast path.

**Main.rs progress**: No visible change. Second runs are faster (cache hits skip typecheck).

**Verification**: Second run faster. Macro expansion from cached prelude works. Cache invalidation triggers recompile.

## Step 14: File Watcher Integration

**Goal**: File watcher re-registers changed modules via the scheduler.

**Changes**:
- File watcher thread watches `project_root` for `.cl` changes.
- On change: re-register module with `Replace` strategy.
- Unchanged dependencies already in `TypecheckDone`/`Complete`.
- Type-change limitation: changing exported symbol's type is an error.
- GOT stability: pause priority worker JIT writes during REPL eval.

**Main.rs progress**: No visible change to main structure. File watcher is spawned internally by the session during REPL mode.

**Verification**: Edit file while REPL running → updated definitions. Type-change error reported.

## Step 15: Delete Legacy Code

**Goal**: Remove all v3/old pipeline code that is no longer reachable.

**Changes**:
- Delete `CompilationSession` struct and all its methods.
- Delete `compile_unit`, `compile_unit_inner`, `compile_unit_with_stack`.
- Delete `CompileUnitResult`, `CodegenResult`, `CodegenItem`, `CodegenPacket`.
- Delete `CodegenQueue`, `CodegenMode`, `JitOrLinker`.
- Delete `InMemWorkerState`, `ObjectWorkerState`, `CacheState` from session.
- Delete `ModuleDependencyGraph`.
- Delete `compile_and_run` test helper — replace with v4 equivalent.
- Merge remaining `pipeline.rs` utilities into appropriate modules or delete.

**Main.rs progress**: The `--v4` flag/gate is removed. The v4 main IS the main. Old `main()` code deleted.

**Verification**: `cargo test` passes. `cargo clippy` clean. Significant line count reduction. Only one session struct, one main, one compilation path.

## Ordering and Dependencies

```
Step 0: North-star main.rs (skeleton with delegations)
  │
  ▼
Step 1: Per-form typecheck API
  │
  ▼
Step 2: Introduce CompileScheduler (single-threaded)
  │
  ▼
Step 3: Form-by-form worker loop ── register_module fills in
  │
  ▼
Step 4: Macro expansion blocking ── macros work through v4 path
  │
  ▼
Step 5: Lazy dependency discovery ── multi-module works
  │
  ▼
Step 6: Remove MacroExpander trait
  │
  ├─► Step 8: Platform registry (independent of 7)
  │
  ▼
Step 7: REPL eval with persistent JIT ── eval fills in  ◄── highest risk
  │
  ├─► Step 9: Failed state and error cascade ── error paths fill in
  │
  ▼
Step 10: Nice workers ── spawn_nice_workers fills in
  │
  ▼
Step 11: Multi-threaded priority workers ── spawn_priority_workers fills in
  │
  ▼
Step 12: Concurrent TypeChecker maps (DashMap)
  │
  ├─► Step 13: Cache-hit loading (needs 12)
  │
  ├─► Step 14: File watcher integration (needs 7 + 9)
  │
  ▼
Step 15: Delete legacy code ── v4 main becomes the only main
```

### Main.rs Progression Summary

| Step | What fills in | What still delegates to old path |
|------|--------------|----------------------------------|
| 0 | Full skeleton | Everything delegates |
| 3 | `register_module` (single-module, no macros) | REPL eval, macros, multi-module |
| 4 | Macro programs work | REPL eval, multi-module |
| 5 | Multi-module + prelude work | REPL eval |
| 7 | `eval` for REPL | Nothing — all paths are v4 |
| 9 | Error handling (`?` on waits, `Err` in REPL) | — |
| 10 | `spawn_nice_workers` | `spawn_priority_workers` (still inline) |
| 11 | `spawn_priority_workers` | — |
| 15 | Remove `--v4` gate, delete old main | — |

## Risk Assessment

**Step 7 (REPL eval with persistent JIT) is the highest-risk step.** The REPL has accumulated interception points (defmacro, import, platform, bare symbol introspection, trace, annotation expressions) that currently flow through `compile_unit`. Moving to a scheduler-driven model where definitions go through workers but temporary closures are compiled on the eval path requires careful separation of concerns. The persistent eval JIT is a new concept not present in v3.

**Mitigation**: Step 7 can be decomposed incrementally:
1. First: definitions-only REPL (no trailing expressions) via scheduler.
2. Then: trailing expressions via persistent eval JIT, starting with simple expressions.
3. Then: macro usage in REPL input.
4. Finally: trace, annotation, and introspection edge cases.

**Step 1 (per-form typecheck) is the highest-effort step.** The current `tc.check()` is a monolithic multi-pass function. Decomposing it into `check_form()` while preserving the multi-pass invariant (register all signatures, then check all bodies) requires understanding the exact dependencies between passes. However, this is mechanical refactoring with compiler-enforced correctness — the types constrain the valid decompositions.

**Step 12 (DashMap) is the most architecturally invasive.** Changing the TypeChecker's internal data structures from `HashMap` behind `Mutex` to `DashMap` touches every method that reads or writes module tables. However, `DashMap`'s API is close to `HashMap`'s, so most changes are mechanical. The risk is subtle concurrency bugs from incorrect assumptions about atomicity across multiple map operations.
