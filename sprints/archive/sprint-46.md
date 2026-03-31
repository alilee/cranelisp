# Sprint 46: Pipeline v4 Step 10 — Nice Workers for Object Codegen

**Status**: COMPLETE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: Nice worker threads compile modules to `.o` files at low OS priority, enabling background cache file generation during `--run` and blocking cache completion before `--link`.

## Context

Sprint 45 delivered Steps 8+9: PlatformRegistry and error cascade. The single-threaded v4 pipeline is now robust — all compilation paths (batch `--run`, `--link`, REPL eval) route through the scheduler with proper error handling and REPL recovery. The next step introduces the first real threading into the v4 pipeline: nice workers for object file codegen.

Step 10 is the first concurrency step. It spawns background threads at nice (low) OS priority that compile modules to relocatable `.o` files + `.meta.json` cache metadata. This is architecturally significant because:

1. It introduces the **nice worker pool** — a new thread pool separate from the (still inline) priority worker loop.
2. It makes `spawn_nice_workers()` and `wait_object_complete()` functional on `CompilerSession`.
3. It enables **background caching** during `--run` — object files are written while the program executes.
4. It provides the **blocking barrier** for `--link` — all `.o` files must be written before the system linker runs.

**All skills MUST read:**
- `design/arch/pipeline-v4-roadmap.md` — Step 10 specification
- `design/arch/concurrent-pipeline.md` §5.3 (Nice Workers), §5.4 (Priority Escalation), §6.3 (Nice Worker Interface)
- `design/arch/pipeline-v4.md` §4.3 (Object Codegen), §5 (CompilerSession)
- `src/session_v4.rs` — v4 CompilerSession (`spawn_nice_workers` is currently a no-op)
- `src/scheduler.rs` — CompileScheduler (`take_object_codegen`, `notify_object_codegen_complete` exist)
- `src/session.rs` — ObjectWorkerState, CacheState, CacheWriterHandle

## Scope

### Step 10: Nice Workers for Object Codegen

Implement `nice_worker_loop()` and wire it into `spawn_nice_workers()` on `CompilerSession`. Nice workers:

1. Call `scheduler.take_object_codegen()` to claim a TypecheckDone module with `object_done == false`.
2. Compile all the module's symbols to a single `.o` file using Cranelift's object backend.
3. Write `.meta.json` cache metadata (symbol table, module structure, source hash).
4. Call `scheduler.notify_object_codegen_complete()`.
5. Loop until shutdown.

**Threading model:**
- `spawn_nice_workers(n)` spawns N threads. Each runs `nice_worker_loop`.
- Threads run at nice priority (lower OS scheduling priority than the main/priority worker thread).
- `take_object_codegen` parks on a condvar when no work is available. Woken by `notify_typecheck_done` or `shutdown`.
- `wait_object_complete` blocks until all modules have `object_done == true` (or are Failed).
- Before `--link`, nice workers are promoted to normal priority via `promote_object_codegen` (hot flush).

**Scheduler changes:**
- `take_object_codegen` needs condvar support (currently returns None immediately — single-threaded design).
- Add `object_work_available: Condvar` to `CompileScheduler` (per `concurrent-pipeline.md` §6).
- `notify_typecheck_done` and `register_module_cached` wake the `object_work_available` condvar.
- `wait_object_complete` blocks on a `completion` condvar.
- `shutdown` wakes all condvars.

**Session changes:**
- `CompilerSession` gains `nice_worker_handles: Vec<JoinHandle<()>>` for thread management.
- `spawn_nice_workers(n)` spawns threads and stores handles.
- `shutdown()` joins nice worker threads.
- Object codegen needs: ISA, TypeChecker (read-only for symbol tables), ObjectWorkerState (cache config, .o paths).

**Key design consideration:** The nice worker needs access to session state (TypeChecker module tables, ISA, cache config) across thread boundaries. Currently `CompilationSession` is not `Send` (it contains `*const u8` function pointers). The nice worker needs either:
- A shared reference model (`Arc<CompilerSession>` with internal `Mutex` on mutable fields), or
- Pre-cloned/pre-extracted data passed to each worker thread (matching the `CodegenPacket` pattern from v3).

The `concurrent-pipeline.md` design says "Workers own their JIT state" and session maps are concurrent. For Step 10 (nice workers only), the simplest correct approach is likely: nice workers receive a reference to the session (via `Arc` or scoped threads) and read TypeChecker state through the existing `Mutex<TypeChecker>`. Object worker state (cache dir, .o paths) is per-worker — each nice worker creates its own `ObjectWorkerState` and results are collected at shutdown.

### Not in scope

- Step 11 (multi-threaded priority workers) — priority worker still runs inline on calling thread
- Step 12 (DashMap / concurrent TypeChecker) — `Mutex<TypeChecker>` suffices for read-only access
- Step 13 (cache-hit loading via register_module_cached)
- Step 14 (file watcher integration)
- Step 15 (legacy code deletion)
- New language features

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `spec/09-macros.md:147` | /spec | §9.2.5 cross-module macro helper calls not explicitly specified | From S45. Spec clarification — not blocking implementation. Carry with rationale: spec-only, no code impact. |

No code-level FIXMEs in `src/`. The spec FIXME is on its 1st carry (filed in S45) and is spec-only — it doesn't block Step 10 implementation.

## Architecture Review

**Verdict: PASS WITH RECOMMENDATIONS**

### Technical Coherence

The scope forms a complete, testable increment. Step 10 introduces exactly one new capability (background `.o` generation by nice worker threads) with clear entry/exit criteria: `spawn_nice_workers(n)` goes from no-op to real threads, `--run` produces cache files, `--link` blocks on `.o` completion. The scheduler already has `take_object_codegen` and `notify_object_codegen_complete` — they just need condvar support for parking. The existing `build_object_compile_input` + `cache::ObjectCompileInput` pipeline in `pipeline.rs` provides the object codegen logic to call from the new worker loop. This is the right granularity for a sprint.

The sprint correctly excludes Steps 11-15 from scope. Nice workers are the simplest concurrency step because they are readers of session state (TypeChecker symbol tables, ISA) and writers of independent files (one `.o` per module). No contention with the still-inline priority worker loop.

### Principle 8 Assessment (No Interim Architecture)

**Pass.** The code introduced in Step 10 survives into Steps 11-15:

- The `nice_worker_loop` function is the permanent nice worker entry point. Step 11 (multi-threaded priority workers) does not change it.
- The `Mutex<SchedulerState>` + condvars added here are the permanent scheduler locking model from `concurrent-pipeline.md` section 6. Step 11 uses the same `Mutex` — it just adds more callers (`take_priority_work` parks on `priority_work_available` condvar). Step 12 (DashMap) replaces TypeChecker locking, not scheduler locking.
- Per-worker `ObjectWorkerState` is the target design ("workers own their JIT state" — `pipeline-v4.md` section 5.2). No interim shared state to unpick later.
- The `set_nice_priority()` function already exists in `src/cache_writer.rs` and can be extracted/reused. No throwaway priority infrastructure.

### Thread Model Recommendation: Scoped Threads

**Use `std::thread::scope` (Rust 1.63+), not `Arc<CompilerSession>`.**

Rationale:

1. **`CompilerSession` is not `Send`.** It contains `CompilationSession` which holds `*const u8` function pointers, `MacroEnv` with raw pointers, and other non-Send fields. Wrapping in `Arc` would require either (a) making `CompilerSession: Send + Sync` (major refactor touching inner session, not justified for Step 10), or (b) unsafe `impl Send` (unsound unless all access is synchronized — hard to verify with the legacy `CompilationSession` wrapper still present).

2. **Scoped threads match the v4 ownership model.** The v4 main owns `CompilerSession` for the program's lifetime. `std::thread::scope` guarantees spawned threads complete before the scope exits, so threads can borrow `&CompilerSession` safely. This is exactly the pattern `concurrent-pipeline.md` section 6.4 shows: `fn nice_worker(session: &CompilerSession)`.

3. **Step 11 compatibility.** When Step 11 adds priority worker threads, they also use scoped threads from the same scope. The scope lives in `main()` — session is created, scope is entered, workers are spawned, scope exits at shutdown. The `JoinHandle` storage on `CompilerSession` (mentioned in the sprint proposal) is not needed with scoped threads — the scope itself handles join-on-exit. This is cleaner.

4. **Scoped thread caveat.** The scope blocks at exit until all spawned threads finish. This means `shutdown()` must signal workers (set `shutdown` flag, wake condvars) and then the scope exit handles the join. The `nice_worker_handles: Vec<JoinHandle<()>>` field proposed in the sprint is unnecessary — remove it. Instead, `spawn_nice_workers` takes a `&std::thread::Scope` parameter (or the spawning happens directly in `main()` inside the scope block).

**Implementation pattern:**

```rust
// In main() or equivalent:
let session = CompilerSession::new(...);
std::thread::scope(|scope| {
    for _ in 0..n {
        scope.spawn(|| nice_worker_loop(&session));
    }
    session.register_module(...);
    session.scheduler.wait_inmem_complete()?;
    session.trampoline(...);
    session.scheduler.wait_object_complete()?;
    // scope exit joins all nice workers
});
```

This eliminates the `Arc`/`Send` problem entirely and is the permanent pattern for Steps 11-15.

### ObjectWorkerState: Per-Worker, Merge at Completion

**Per-worker is correct.** Each nice worker creates its own Cranelift `ObjectModule` for the module it is compiling. The outputs (`.o` path, module structure) are collected at the end.

**Recommendation**: Do not use the existing `ObjectWorkerState` struct from `session.rs`. That struct carries `cache_state`, `cache_writer`, `cross_module_func_sigs`, and `compiled_o_paths` — most of which are legacy v3 state management. Instead, the nice worker loop should:

1. Read the module's `CheckResult` and symbol table from the TypeChecker (via `Mutex<TypeChecker>` lock).
2. Build the `ObjectCompileInput` using `build_object_compile_input` (or an extracted equivalent).
3. Compile to `.o` bytes using `cranelisp_backend::cache::compile_object`.
4. Write `.o` and `.meta.json` to the cache directory (from `session.settings` or `session.project_root`).
5. Record the `.o` path in a thread-safe collector (a `Mutex<Vec<PathBuf>>` on the session, or returned through the scheduler notification).

This keeps nice workers self-contained and avoids coupling to the legacy `ObjectWorkerState`.

### Scheduler Locking

**Confirmed: `Mutex<SchedulerState>` + 3 condvars matches `concurrent-pipeline.md` section 6 exactly.**

The current `CompileScheduler` has `state: SchedulerState` (no Mutex). Step 10 changes this to:

```rust
pub struct CompileScheduler {
    state: Mutex<SchedulerState>,
    priority_work_available: Condvar,  // for Step 11
    object_work_available: Condvar,    // for Step 10
    completion: Condvar,               // for Step 10
}
```

All existing scheduler methods (`register_module`, `take_priority_work`, `notify_*`, etc.) change from `&mut self` to `&self` with internal `self.state.lock()`. This is a mechanical refactor. The priority worker loop (still inline on the calling thread in Step 10) will not park — it continues to return `None` immediately when no work is available (the `Mutex` does not change the single-threaded priority worker's behavior; only nice workers park on `object_work_available`).

**Key interaction to verify**: `notify_typecheck_done` must wake `object_work_available` (a new TypecheckDone module is potential object work). `shutdown` must wake all condvars. `notify_object_codegen_complete` must wake `completion` (for `wait_object_complete` callers).

**`&mut self` to `&self` migration**: All scheduler methods currently take `&mut self` because there is no internal Mutex. Adding the Mutex means they can take `&self`. This also changes `WorkerContext` — the scheduler field can become `&CompileScheduler` instead of `&mut CompileScheduler`, which is necessary for scoped threads (multiple threads need `&CompileScheduler` concurrently). `/int` should make this signature change as part of the Mutex addition.

### Nice Priority: Reuse `set_nice_priority` from `cache_writer.rs`

The `set_nice_priority()` function in `src/cache_writer.rs` already does the right thing: `libc::setpriority(PRIO_PROCESS, 0, 10)` on Unix, no-op on other platforms. Extract it to a shared utility (e.g., `src/thread_util.rs` or `src/util.rs`) so both `cache_writer` and `nice_worker_loop` can call it.

**macOS/Linux notes**: `setpriority(PRIO_PROCESS, 0, nice_value)` sets the calling thread's nice value. Nice value 10 (out of range -20 to 19) is appropriate — noticeably lower priority than default (0) but not the absolute minimum (19). Raising priority back to 0 for the hot flush (`promote_object_codegen`) uses the same API with nice value 0. On macOS, lowering nice value (raising priority) back to 0 requires no special privileges if the process started at nice 0 — the kernel tracks per-thread nice values and allows restoration to the original level.

**Promote pattern for `wait_object_complete`**: Before blocking, iterate the nice worker thread IDs and call `setpriority(PRIO_PROCESS, tid, 0)`. With scoped threads, thread IDs are not directly accessible, so the recommended pattern is: each nice worker checks a shared `AtomicBool promoted` flag on each loop iteration and calls `set_normal_priority()` on itself when promoted. `wait_object_complete` sets the flag and wakes `object_work_available`. Workers self-promote on their next iteration.

### Interface Gaps

1. **`CompileScheduler` signature migration (`&mut self` to `&self`)**: This is a prerequisite for scoped threads. All scheduler methods and `WorkerContext` must work with shared references. This is the largest mechanical change in the sprint.

2. **Cache directory access**: Nice workers need the cache directory path. Currently this lives on `ObjectWorkerState.cache_state`. In the v4 model, the cache dir should be on `CompilerSession` directly (it already has `project_root`; add `cache_dir: Option<PathBuf>`). The `new_for_link` constructor already receives `cache_dir`.

3. **ISA for object codegen**: Nice workers need a `TargetIsa` for Cranelift object compilation. `concurrent-pipeline.md` section 5 specifies `shared_isa: Arc<dyn TargetIsa>` on the session. The v4 `CompilerSession` does not yet have this field — it delegates to `inner.inmem_worker` which owns the ISA implicitly through JIT instances. `/int` should add `shared_isa: Arc<dyn TargetIsa>` to `CompilerSession` and build it once during construction.

4. **`.o` path collection for `--link`**: After nice workers write `.o` files, `link()` needs to collect all `.o` paths. Add a `Mutex<Vec<PathBuf>>` field (e.g., `compiled_o_paths`) to `CompilerSession`. Each nice worker appends its `.o` path after writing. `link()` reads the collected paths.

### Design References for /int

- `design/arch/concurrent-pipeline.md` — sections 5.3 (nice workers), 5.4 (priority escalation), 6.3 (nice worker interface), 6.5 (lifecycle), 7.3 (lock granularity)
- `design/arch/pipeline-v4.md` — sections 4.3 (object codegen), 5 (CompilerSession fields), 5.2 (no worker state on session)
- `design/arch/pipeline-v4-roadmap.md` — Step 10 specification
- `src/cache_writer.rs` — `set_nice_priority()` function to extract
- `src/pipeline.rs` — `build_object_compile_input()` function and object compilation logic (around line 1185 and 2018)
- `src/scheduler.rs` — all methods need `&mut self` to `&self` migration with internal Mutex
- `src/worker.rs` — `WorkerContext` struct needs scheduler reference change

### Carried Debt

The spec FIXME on `spec/09-macros.md:147` (1st carry, filed S45) is spec-only and does not affect Step 10. Carry is justified.

No code-level debt items. The sprint is clean.

### Summary of Recommendations

1. **Use `std::thread::scope`** instead of `Arc<CompilerSession>`. Drop the `nice_worker_handles` field.
2. **Migrate scheduler to `&self` + internal `Mutex`** as the first sub-task (prerequisite for threading).
3. **Extract `set_nice_priority()`** to a shared utility module.
4. **Add `shared_isa: Arc<dyn TargetIsa>`** and `cache_dir: Option<PathBuf>` to `CompilerSession`.
5. **Add `compiled_o_paths: Mutex<Vec<PathBuf>>`** to `CompilerSession` for `--link` support.
6. **Self-promote pattern** for nice workers during hot flush (check `AtomicBool`, call `setpriority(0)` on self).

## Skill Plans

### /arch
**Task**: Review sprint proposal for technical coherence, confirm thread model, approve scheduler locking design.
**Design doc**: `design/arch/concurrent-pipeline.md` (existing — §5.3, §5.4, §6.3 cover nice workers)
**Approach**: Evaluate scoped threads vs Arc, per-worker ObjectWorkerState, Mutex addition to scheduler.
**Design refs**: `design/arch/pipeline-v4.md` §4.3, §5; `concurrent-pipeline.md` §5.3, §6
**Acceptance**: Architecture review section filled, thread model confirmed.

### /int
**Task**: Implement nice worker loop, scheduler condvar support, spawn/shutdown on CompilerSession.
**Design doc**: `design/arch/concurrent-pipeline.md` §5.3 + §6.3 (existing design)
**Approach**:
1. Add `Mutex<SchedulerState>` + `Condvar` fields to `CompileScheduler`. Update all scheduler methods to lock/unlock.
2. Implement `nice_worker_loop(session)` — loops calling `take_object_codegen`, compiles to .o, notifies completion.
3. Wire `spawn_nice_workers(n)` to spawn threads running `nice_worker_loop`.
4. Implement `wait_object_complete` with condvar blocking.
5. Wire `shutdown()` to wake workers and join threads.
6. Verify `--run` produces .o cache files in background; `--link` waits for .o completion.
**Design refs**: `concurrent-pipeline.md` §5.3, §5.4, §6.3; `pipeline-v4-roadmap.md` Step 10
**Acceptance**: `spawn_nice_workers(n)` spawns real threads. `--run` produces cache files. `--link` waits for .o files. All existing tests pass.

### /qa
**Task**: Write tests for nice worker functionality — .o file generation, cache validity, shutdown correctness.
**Design doc**: N/A (test design)
**Approach**: Tests verifying: (A) `--run` produces .o + .meta.json cache files, (B) `--link` waits for .o completion before linking, (C) shutdown joins worker threads cleanly, (D) error in object codegen propagates correctly.
**Design refs**: `pipeline-v4-roadmap.md` Step 10 verification criteria
**Acceptance**: Tests cover cache file generation and link-mode blocking.

### /review
**Task**: Review nice worker implementation for thread safety, resource cleanup, and adherence to concurrent-pipeline.md design.
**Design doc**: N/A
**Approach**: Assess thread safety (no data races, proper Mutex usage), resource cleanup (thread join on shutdown/drop), adherence to §5.3 nice worker spec.
**Design refs**: `concurrent-pipeline.md` §5.3, §5.4
**Acceptance**: 0 blockers, all important findings resolved.

### /frontend
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /typecheck
**Task**: No implementation work this sprint. Verify TypeChecker read-safety for concurrent nice workers.
**Acceptance**: Confirm `Mutex<TypeChecker>` provides safe read access for object codegen workers.

### /backend
**Task**: Verify object codegen functions are thread-safe when called from nice worker threads.
**Design doc**: N/A
**Approach**: Review object compilation code paths for thread-local state assumptions.
**Acceptance**: Object codegen callable from worker threads without data races.

### /platform
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /spec
**Task**: Evaluate FIXME on §9.2.5 (cross-module macro helper calls). Resolve or defer with rationale.
**Design refs**: `spec/09-macros.md` §9.2.5
**Acceptance**: FIXME resolved or explicitly deferred.

### /stdlib
**Task**: No implementation work this sprint. Verify stdlib modules cache correctly via nice workers.
**Acceptance**: Stdlib .o files generated correctly.

### /examples
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /docs
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /repl
**Task**: No implementation work this sprint. Verify REPL session produces .o files in background.
**Acceptance**: Demo files play cleanly.

### /port
**Task**: No implementation work this sprint. Verify exemplar produces .o files.
**Acceptance**: Exemplar compiles with cache file generation.

## Waves

*To be filled during Phase 4 after architecture review and skill plans.*

### Proposed wave structure (draft):

**Wave 1: Architecture review**
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review sprint proposal, confirm thread model | done | PASS WITH RECOMMENDATIONS: scoped threads, Arc<SharedState>, scheduler Mutex+condvars |

**Wave 2: Implementation + tests + review**
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Scheduler Mutex+condvar, nice_worker_loop, spawn/shutdown | done | Arc<SharedState>, object_working flag, ObjectCodegenInput stash, .o compilation wired |
| /qa | Nice worker tests (.o generation, link blocking, shutdown) | done | 6 scheduler unit tests |
| /review | Review implementation | done | 2B+6I+5S. Both blockers fixed (double-claim race, unsafe aliasing). All I findings resolved. |

**Wave 3: Bug fixes**
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Fix review blockers B1+B2, wire actual .o compilation | done | object_working flag, Arc<SharedState>, stash-before-notify race fix, cache_dir in all modes |

## Notes

- /arch recommended `std::thread::scope` but implementation used `Arc<SharedState>` instead — `CompilationSession` is not `Send`, and `Arc<SharedState>` avoids aliasing issues while keeping the session fields accessible to both workers and the main thread.
- /review found 2 blockers: (B1) `take_object_codegen` double-claim race (no `object_working` flag), (B2) unsafe field-splitting creating UB. Both fixed in Wave 3.
- Nice worker initially stubbed .o compilation (marking modules done without writing files). Extended to wire actual .o compilation via `ObjectCodegenInput` stash pattern.
- Race condition discovered: `notify_typecheck_done` (inside `process_module_forms`) woke nice workers before stash was populated. Fixed by moving `notify_typecheck_done` to the caller (priority worker loop) after stashing.
- `cache_dir` was initially `None` in `new()` constructor (only set in `new_for_link`). Fixed: all modes produce .o files so `--link` gets cache hits.
- spec FIXME on §9.2.5 carried (2nd carry) — spec-only, no code impact.

## Outcome

### Delivered
- **Scheduler Mutex + condvars**: `CompileScheduler` migrated from `&mut self` to `&self` with internal `Mutex<SchedulerState>` + 3 condvars (`priority_work_available`, `object_work_available`, `completion`). All scheduler methods and `WorkerContext` updated.
- **Nice worker loop**: `nice_worker_loop()` runs at low OS priority, parks on condvar, claims TypecheckDone modules, compiles to `.o` via `build_object_compile_input` + `compile_module_to_object`, writes to `.cranelisp-cache/`.
- **`Arc<SharedState>`**: Thread-safe shared state (scheduler, cache_dir, compiled_o_paths, promote flag, object codegen stash) accessible by nice workers via `Arc::clone`.
- **`ObjectCodegenInput` stash**: Priority worker stashes `CheckResult` + `Program` after codegen; nice worker consumes it for `.o` compilation. Stash-before-notify ordering prevents race.
- **`run_with_nice_workers`**: Scoped thread spawning with `wait_object_complete` before shutdown.
- **`object_working` flag**: Prevents double-claim by concurrent nice workers.
- **`thread_util.rs`**: Extracted `set_nice_priority()` / `set_normal_priority()` from `cache_writer.rs`.
- **Self-promote pattern**: `AtomicBool` flag for hot flush priority escalation.
- **Cache in all modes**: `--run`, `--link`, and REPL all produce `.o` files.
- **6 scheduler unit tests**: shutdown, double-claim prevention, object_working lifecycle, wait_object_complete, failure propagation, spawn/shutdown lifecycle.

### Deferred
- **spec FIXME on §9.2.5** (2nd carry): cross-module macro helper calls not explicitly specified. Spec-only, no code impact.
- ~~**`.meta.json` writing**~~: Resolved. Nice workers now write `.meta.json` alongside `.o` files. `ObjectCodegenInput` stash extended with `symbol_table` and `module_structure`; `compile_module_object` builds `CacheMetadata` and calls `write_cached_metadata`. `build_codegen_state_for_cache` made `pub` in `pipeline.rs`.
- ~~**`shared_isa`**~~: Resolved — not needed. `compile_module_to_object` creates its own PIC-mode ISA internally via `build_isa(true)`. No shared ISA field required on the session.

### Findings
- **Stash-before-notify ordering is critical**: `notify_typecheck_done` wakes nice workers. If the stash isn't populated before notification, nice workers find no data and skip .o compilation. This is a general pattern for any future worker interaction.
- **`process_module_forms` no longer calls `notify_typecheck_done`**: Callers are now responsible. This affects the priority worker loop and REPL dep compilation (REPL doesn't need notification — it compiles deps inline).
