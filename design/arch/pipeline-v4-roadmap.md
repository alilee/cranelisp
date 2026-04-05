# Pipeline v4 Migration Roadmap

How to get from the current state to the scheduler-driven architecture described in `pipeline-v4.md` and `concurrent-pipeline.md`. Each step produces a working compiler — no step leaves things broken.

## Current State (Sprint 49)

The v4 pipeline is the only pipeline. `CompilerSession` in `session_v4.rs` is the unified session type. `main.rs` uses one code path for Run/Link/REPL. There is no `--v4` flag.

**What works:**
- One `CompilerSession`, one `run()`, all modes
- `CompileScheduler` with full module lifecycle, priority ladder, blocking/unblocking
- Per-form typecheck via `tc.check_form()`
- Form-by-form worker loop in `process_module_forms()`
- Macro expansion blocking via scheduler priority codegen queue
- Lazy dependency discovery during form processing
- MacroExpander trait removed — expansion is a free function in `expander.rs`
- REPL eval with TC snapshot/restore and scheduler-driven definitions
- Platform registry (`PlatformRegistry` with `HashMap<FQSymbol, PlatformFunction>`)
- Error cascade via `notify_module_failed` + `cascade_failure_locked`
- DashMap for `SharedCodegenState.def_codegen`; TC modules behind DashMap
- Cache-hit loading via `try_cache_hit_load()` in worker.rs
- GOT with atomic slot-based table (`GotTable` with `AtomicPtr`)
- Scoped priority workers spawned per `register_module_with_source()` call
- Old pipeline code deleted (~7k lines removed in sprint 49)
- `--v4` CLI flag removed
- `ReplSession` moved to `tests/helpers/mod.rs` (test-only adapter)
- stdlib tests: 54/54 pass
- ring0: 106/108 (2 pre-existing `checked_div` failures)

**What doesn't work:**
- Nice workers are never spawned — `.o` files are never produced
- `wait_object_complete()` hangs in production (`main.rs` Run/Link/REPL exit)
- `link_by_name()` is stubbed — `--link` mode returns error
- `v4_pipeline.rs` tests pass `--v4` flag that no longer exists
- File watcher only wired to dead `src/repl/mod.rs`
- ~4,700 lines of dead legacy code remains

## Completed Steps

### Step 0: North-Star main.rs — DONE

`main.rs` has the full v4 structure. All methods are real implementations, not stubs. No delegation to old pipeline.

### Step 1: Per-Form Typecheck API — DONE

`tc.check_form()` exists in `cranelisp-typecheck`. `FormCheckResult` accumulates into `ModuleCheckAccumulator`. Two-pass structure preserved (register signatures, then check bodies).

### Step 2: CompileScheduler — DONE

Full scheduler in `src/scheduler.rs` with module lifecycle, priority ladder, condvar-based blocking, waiter map, cascade failure. Comprehensive unit tests.

### Step 3: Form-by-Form Worker Loop — DONE

`process_module_forms()` in `src/worker.rs` processes modules form-by-form. `priority_worker_loop()` dispatches from scheduler. `register_module_with_source()` spawns scoped priority workers.

### Step 4: Macro Expansion Blocking — DONE

Workers block via `block_for_macro_codegen()`. Priority codegen compiles macro dependencies. Resume from blocked form index.

### Step 5: Lazy Dependency Discovery — DONE

Dependencies discovered during form processing. `inject_prelude_if_needed()` triggers prelude loading. Cache hits restore type info and enter `TypecheckDone`.

### Step 6: Remove MacroExpander Trait — DONE

`CraneliftExpander` and `MacroExpander` trait deleted. Expansion is a free function in `src/expander.rs`. `build_program` no longer requires `&dyn MacroExpander`.

### Step 7: REPL Eval — DONE

`eval()` on `CompilerSession` uses `process_module_forms(Additive)` for definitions. TC snapshot/restore on error. Inline codegen via `codegen_and_execute()`.

### Step 8: Platform Registry — DONE

`PlatformRegistry` in `src/platform_registry.rs` with `HashMap<FQSymbol, PlatformFunction>`. Platform loading registers type signatures in TC and function pointers in registry.

### Step 9: Error Cascade — DONE

`notify_module_failed()` cascades through dependency graph via `cascade_failure_locked()`. `wait_inmem_complete()` and `wait_object_complete()` return `Err` on failed modules. REPL does TC snapshot/restore.

### Step 12: DashMap — DONE (partial)

`SharedCodegenState.def_codegen` uses `DashMap<Symbol, DefCodegen>`. TC module tables use `DashMap<ModuleFullPath, SymbolTable>`. TC access still serialized via `tc_mutex` for typecheck coherence. Full concurrent access (one writer per module, many readers without mutex) is a future optimization.

### Step 13: Cache-Hit Loading — DONE

`try_cache_hit_load()` in worker.rs checks cache validity, restores symbol table to TC, registers with scheduler at `TypecheckDone`, pre-registers GOT slots.

## Remaining Steps

### Step 10: Spawn Nice Workers as Persistent Threads

**Status:** Infrastructure exists, never wired to production.

**Problem:** `spawn_nice_workers()` at session_v4.rs:1679 and `nice_worker_loop()` at 1708 are functional but never called from `CompilerSession::new()` or anywhere in production. `wait_object_complete()` blocks forever because no workers set `object_done`.

**Changes:**
1. In `CompilerSession::new()`, if `settings.nice_workers > 0`, spawn persistent background threads via `std::thread::spawn` running `nice_worker_loop(&shared)`. `SharedState` is already `Arc`-wrapped.
2. Store `Vec<JoinHandle<()>>` on `CompilerSession`.
3. In `shutdown()`, after signaling the scheduler, join the nice worker handles.
4. Guard `wait_object_complete()`: when `nice_workers == 0`, return `Ok(())` immediately (test safety net).

**Unblocks:** Run mode caching (`.o` files produced in background), Link mode (`.o` files needed), REPL clean exit.

**Verification:** `cargo run -- --run examples/hello.cl` prints result and exits (not hang). `tests/VERIFICATION.md` Phase 4 cache tests.

### Step 11: Persistent Priority Workers

**Status:** Scoped (per `register_module` call), not session-persistent.

**Problem:** Priority workers are spawned per-call via `std::thread::scope()` in `register_module_with_source()` (session_v4.rs:559). They join when the scope exits. v4 spec says session-lifetime persistent workers.

**Impact:** Functionally correct for both batch and REPL. Suboptimal for REPL (fresh workers per eval). Not blocking any tests or functionality.

**Changes:**
1. Move priority worker spawning to `CompilerSession::new()` as persistent `std::thread::spawn` threads.
2. `register_module` becomes a pure enqueue (parse + register with scheduler). Workers wake on condvar.
3. Store `JoinHandle`s on session, join in `shutdown()`.
4. REPL `eval()` submits work and waits on scheduler, no longer spawns workers inline.

**Deferred:** This is a design improvement, not a functional fix. Current scoped workers are correct. Can be done after test verification is complete.

### Step 14: Wire File Watcher to CompilerSession

**Status:** File watcher code exists in `src/repl/watch.rs`, only connected to dead `ReplSession`.

**Changes:**
1. Move `watch.rs` out of `src/repl/` (which is dead code) into `src/watch.rs` or similar.
2. Instantiate `FileWatcher` in the REPL loop in `main.rs`.
3. Before each REPL prompt, poll the watcher.
4. For changed files, look up module via `file_to_module`, re-register with scheduler.

**Deferred:** No tests exercise this path. Interactive-only feature.

### Step 15: Link Mode + Test Fixes + Dead Code Cleanup

**15a. Implement `link_by_name` (depends on Step 10):**
- session_v4.rs:1319 currently returns "not yet implemented"
- Implement: `wait_object_complete()`, collect `.o` paths from `shared.compiled_o_paths`, call `exe::validate_main()` + `exe::generate_startup_object()` + system linker
- Reference: `src/exe.rs` has existing linker infrastructure

**15b. Fix v4_pipeline test infrastructure:**
- `tests/v4_pipeline.rs` passes `--v4` flag that no longer exists
- Change `["--v4", "--run", ...]` to `["--run", ...]`
- Simplify comparison tests (only one pipeline now)

**15c. Delete dead legacy code (~4,700 lines):**
- `src/repl/mod.rs` (3,203 lines) — old `ReplSession`, not used
- Dead functions in `src/session.rs` — `CompilationSession`, `ObjectWorkerState`
- Dead functions in `src/pipeline.rs` — `compile_unit` family, `ModuleGraph`
- `src/repl/commands.rs`, `src/repl/io_format.rs`, etc. — entire `src/repl/` directory

**Order:** 15a (functional), 15b (test fix), 15c (cleanup — do last, after tests pass).

## Execution Order

```
Step 10: Spawn nice workers          ── unblocks production binary + link mode
  │
  ├─► Step 15a: link_by_name         ── unblocks --link mode
  │
  ├─► Step 15b: v4_pipeline tests    ── unblocks 47 test file
  │
  ▼
Run test verification (tests/VERIFICATION.md)
  │
  ▼
Step 15c: Dead code cleanup          ── after tests pass
  │
  ▼
Step 11: Persistent priority workers ── design improvement (deferred)
  │
  ▼
Step 14: File watcher wiring         ── interactive feature (deferred)
```

## Verification

See `tests/VERIFICATION.md` for the systematic post-refactor test verification procedure.

**Production smoke tests (after Step 10):**
- `cargo run -- --run examples/hello.cl` — prints result, exits cleanly
- `cargo run` — REPL starts, accepts input, Ctrl-D exits cleanly (no hang)

**After Step 15a:**
- `cargo run -- --link examples/hello.cl` — produces linked binary
