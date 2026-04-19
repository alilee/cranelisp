# Persistent Priority Workers — G9/G10/G11 Design

**Sprint**: 57 (Phase 4 Step 4b of `design/arch/pipeline-v4-roadmap.md`).
**Owner**: `/int`.
**Status**: Design (Wave 1 prerequisite for Wave 4 implementation).

This document covers the Phase 4 G9/G11 migration: priority workers become session-persistent (spawned in `CompilerSession::new`, parked on condvar, joined in `Drop`). `thread::scope` disappears from worker lifecycle code (tests may retain it). `register_module`, `eval`, and `reload_module` all enqueue work on the scheduler. Scheduler-driven reload (G11) falls out of G9. G10 (previously "persistent eval JIT") has been retracted — see Decision 31 and `pipeline-v4-roadmap.md` G10 row; the target is per-batch JIT with custom-`Drop` reclaim, and the retraction eliminates the "rotate worker JIT" lifecycle question entirely.

## 1. References

- `design/arch/pipeline-v4.md` §2.2 (spawn via `s.spawn_priority_workers`), §5.1 (CompilerSession fields), §6.2 (REPL compilation — fresh-JIT-per-eval with custom-`Drop` reclaim), §9.4 (per-batch JIT + Cranelift 0.116 leak-on-drop evidence).
- `design/arch/pipeline-v4-roadmap.md` Phase 4 Step 4b (G9/G11; G10 retracted).
- `design/arch/CLAUDE.md` Decision 31 (canonical JIT-lifetime story: per-batch, `Arc<Jit>`, custom `Drop → unsafe free_memory()`).
- `design/arch/concurrent-pipeline.md` §5.1 (priority worker ladder), §6 (`CompileScheduler` interface), §11 (invariants).
- `design/arch/CLAUDE.md` Principle 11 (single pipeline, mode parameters), Decision 23 (uniform codegen).
- `design/int/phase2-codegen-convergence.md` §9.1 (module-level exclusivity via scheduler).
- `sprints/SPRINT.md` §Architecture Review condition 4 (descope triggers for G9).
- Existing nice worker implementation (`src/session_v4.rs:665–693`) — reference pattern for persistent workers.
- `sketch/` — **no sketch antecedent for this subsystem**: the sketch was single-threaded (no scheduler, no workers). §3 below covers this.

## 2. Current state

### 2.1 Scoped priority workers

Priority workers today are spawned inside a `thread::scope` *per call* to:

- `register_module_with_source` (`src/session_v4.rs:1059–1136`, scope at line 1114)
- `reload_module` (`src/session_v4.rs:1013–1024`, scope at line 1013)

Within the scope, N workers (`settings.priority_workers`) are spawned as scoped threads that each run `priority_worker_thread` (`src/worker.rs:2873`). Each worker parks on `scheduler.take_priority_work_blocking()` (condvar-based) when no work is available, and processes work items until the scheduler signals shutdown *or* the scheduler reports no more pending work.

When the scope exits, all workers join. The next call spawns a fresh cohort.

Key state passed into the scoped worker:
- `&Mutex<PlatformRegistry>` (swapped into and out of `CompilerSession.platform_registry` around the scope — see `src/session_v4.rs:993–1026, 1088–1128`).
- `&DashMap<ModuleFullPath, TypecheckProduct>`, `&DashMap<ModuleFullPath, CodegenProduct>`, introspection, scheduler, module sexps, suspend states, dirs, project root, `&SharedState`.

The `PriorityWorkerRefs` struct carries all of this via borrowed references (the scope guarantees they outlive the workers).

### 2.2 Scoped nice workers — **already persistent**

Nice workers were migrated to persistent spawn in Sprint 46 (see `src/session_v4.rs:665–693`). They:
- Spawn in `CompilerSession::new` via plain `std::thread::spawn` (not `spawn_scoped`).
- Hold `Arc<SharedState>` (the only way to share owned state across non-scoped threads).
- Park on `scheduler.take_object_codegen()` (condvar).
- Join in `CompilerSession::shutdown()` (via the stored `nice_worker_handles: Vec<JoinHandle<()>>`).
- There is a defensive `scheduler.shutdown()` call in `impl Drop for CompilerSession` (`src/session_v4.rs:3266–3274`) to wake workers on drop-without-shutdown (test teardown, panics).

Nice workers are the **proven template** for G9. The priority-worker migration follows the same pattern.

### 2.3 Eval JIT — fresh per expression

Today's REPL eval path in `codegen_and_execute` (`src/session_v4.rs:1450–1598`):
- Calls `inline_jit_codegen_for_module` to compile any new defns introduced by this eval. This creates a *fresh* `Jit::new_with_symbols` inside the worker's scope.
- If the program contains a trailing expression, calls `pipeline::compile_and_execute_expr` (`src/pipeline.rs:55`), which creates **another** fresh `Jit` to compile and call the expression's `__expr` synthetic defn.

Two JIT instances per eval, both short-lived and discarded. This is gap G10 per the roadmap.

### 2.4 Reload — scoped-worker re-spawn

`CompilerSession.reload_module` (`src/session_v4.rs:964–1038`):
- Clears the module's `typecheck_products`, `codegen_programs`, `codegen_products` entries.
- Re-parses the source, inserts into `module_sexps`.
- Calls `scheduler.register_module(...)` for re-typecheck.
- Spawns a cohort of scoped priority workers via `thread::scope` (line 1013).
- Workers process the re-registration like any other work.
- Scope exits; workers join; function returns.

G11 is the generalisation: reload enqueues work on the scheduler without spawning workers — the session-persistent workers already parked on condvar wake up and take the work.

## 3. Sketch comparison

**No sketch antecedent.** The sketch compiler is single-threaded end-to-end:
- `sketch/src/batch.rs` runs the pipeline sequentially (parse → typecheck → codegen → execute).
- `sketch/src/repl.rs` runs the REPL synchronously; each eval is parse → typecheck → JIT → call, inline.
- `sketch/src/cache_writer.rs` has an mpsc-channel + background thread for cache writes (ROADMAP context: "deferred per-module cache writes") — but that is a write-only queue drain, not a compilation worker.

The v4 pipeline's scheduler/worker model is a **net-new subsystem** introduced in Sprints 41–46 with no prototype equivalent. The normative design references for this subsystem are:
- `design/arch/pipeline-v4.md` §§4–7 (codegen, REPL, Run, Link modes).
- `design/arch/concurrent-pipeline.md` §§2–8 (module lifecycle, priority queue, workers, scheduler interface, cache-hit).

Per project CLAUDE.md "Sketch Oracle" rule, the sketch comparison for this subsystem records: **no sketch solution to consult; v4 design is the authority**. Divergence is total by necessity, not by choice.

The sketch's `cache_writer.rs` background-thread pattern is a narrow ancestor: it proves a persistent background thread + mpsc channel + atomic-shutdown-flag approach is viable in the prototype's codebase. G9 adopts the same essential pattern but scaled to N workers with condvar park/wake (more efficient than channel polling for idle time) — see §4.

## 4. Target state

### 4.1 Spawn at session init

`CompilerSession::new` spawns N priority worker threads at session creation, same pattern as nice workers today:

```rust
let mut priority_worker_handles = Vec::with_capacity(priority_workers);
for i in 0..priority_workers {
    let worker_shared = Arc::clone(&shared);
    let handle = std::thread::Builder::new()
        .name(format!("priority-worker-{}", i))
        .spawn(move || {
            priority_worker_loop(&worker_shared);
        })
        .expect("failed to spawn priority worker thread");
    priority_worker_handles.push(handle);
}
```

`priority_worker_loop` takes `&SharedState` (not `PriorityWorkerRefs`) — the refs struct's borrowed-reference design is incompatible with owned-`Arc` threading. §5 covers the refactor of `PriorityWorkerRefs` → `SharedState` access.

### 4.2 Park on condvar, wake on work

Priority workers park on the scheduler's `priority_work_available` condvar (already exists per `concurrent-pipeline.md` §6). The existing `take_priority_work_blocking` method already parks on this condvar; `priority_worker_loop` simply calls it in a loop exactly like today's `priority_worker_thread`:

```rust
fn priority_worker_loop(shared: &SharedState) {
    loop {
        let work = shared.scheduler.take_priority_work_blocking();
        match work {
            Some(PriorityWork::Typecheck(module)) => { handle_typecheck_work(shared, &module); }
            Some(PriorityWork::BlockingJitCodegen(module, symbol))
            | Some(PriorityWork::JitCodegen(module, symbol)) => { handle_codegen_work(shared, &module, &symbol); }
            None => return, // shutdown
        }
    }
}
```

**Behavioural invariant**: `take_priority_work_blocking` returns `None` only on shutdown. This is already the case (see `src/scheduler.rs`). Workers run for the session lifetime; they do NOT exit when "no more pending work" is true — they park until either more work arrives or shutdown.

This is the fundamental shift from today: today's scoped workers are expected to finish and join when the scope ends; tomorrow's persistent workers are expected to park indefinitely and only exit on shutdown.

### 4.3 `register_module` enqueues, does not spawn

```rust
pub fn register_module_with_source(
    &mut self,
    module_name: &str,
    source: &str,
    _entry_module_path: &Path,
) -> Result<Vec<Warning>, CranelispError> {
    let module = ModuleFullPath::from(module_name);
    let sexps = cranelisp_frontend::parse(source)?;

    // Record source hash (unchanged).
    /* … */

    // Insert sexps into the shared module_sexps map.
    {
        let mut map = self.shared.module_sexps.lock().unwrap_or_else(|e| e.into_inner());
        map.insert(module.clone(), sexps);
    }

    // Enqueue the module for typecheck. The persistent workers parked
    // on the priority-work condvar wake up and claim it.
    self.shared.scheduler.register_module(module.clone(), false);

    // Wait for inmem codegen to complete (the workers do the work).
    self.shared.scheduler.wait_inmem_complete()?;

    Ok(Vec::new())
}
```

No `thread::scope`, no per-call worker spawn, no `PlatformRegistry` Mutex swap. `module_sexps` + `suspend_states` move from Mutex-local-to-the-scope to fields on `SharedState` (they already need to be — workers need to read them). See §5.

### 4.4 `eval` submits, blocks on completion

The REPL eval path becomes:

```rust
pub fn eval(&mut self, src: &str) -> Result<Option<EvalResult>, CranelispError> {
    // Parse + snapshot TC state (unchanged).
    /* … */

    // Enqueue the REPL module for additive typecheck.
    self.shared.scheduler.register_module_additive(&self.current_module);

    // Inject the sexps into module_sexps.
    self.insert_eval_sexps(/* … */);

    // Wait for typecheck + inmem codegen for this module.
    self.shared.scheduler.wait_module_complete(&self.current_module)?;

    // Read __expr pointer from the symbol table (post-G6 — see §13.6 of
    // phase2-codegen-convergence.md). Call it via a fresh per-eval JIT
    // wrapped in the custom-Drop Jit newtype (Decision 31).
    let ptr = /* … */;
    let result = call_repl_expr(ptr)?;

    // On success, persist the module (§6.4 of pipeline-v4.md).
    /* … */
    Ok(Some(result))
}
```

The `call_repl_expr` step uses a **fresh per-eval JIT** — see §4.5 (canonical per-batch framing; G10 retracted). The `compile_and_execute_expr` helper in `src/pipeline.rs:55` is retained in spirit but updated to wrap its `JITModule` in the custom-`Drop` `Jit` newtype (per Decision 31): it creates a fresh JIT, compiles `__expr` on it, calls `get_finalized_function`, invokes the closure, consumes the result, and lets the `Jit` wrapper drop — its custom `Drop` calls `unsafe JITModule::free_memory()` to reclaim the `__expr` pages. The eval path does NOT submit `__expr` as a worker work item; only its *dependencies* flow through `BlockingJitCodegen` and run on worker-owned per-batch JITs.

### 4.5 Per-batch JIT (G10 retracted; see Decision 31)

Per `pipeline-v4.md` §9.4 and `design/arch/CLAUDE.md` Decision 31, the JIT-lifetime story is one `JITModule` per compile batch, not per worker. With G9 persistent workers, the target shape is:

- A worker picks up a `JitCodegen` or `BlockingJitCodegen` work item, creates a **fresh** `JITModule` for that batch, calls `compile_to_module(module, names, symbol_tables, &mut jit_module)`, finalises, writes each function's code pointer into the GOT, and stores an `Arc<Jit>` on each `ModuleEntry::Def.code` entry produced. The worker's thread-local state carries no long-lived JIT between work items.
- The `Arc<Jit>` is the sharing primitive: N compiled functions produced by one `compile_to_module` call share one underlying `Jit`. When every sibling `Code` entry holding that `Arc<Jit>` is dropped (evicted / redefined), the Arc refcount reaches zero and the custom `Drop` on our `Jit` wrapper calls `unsafe JITModule::free_memory()` — this is how executable pages are reclaimed (see §9.4 of pipeline-v4.md for the Cranelift 0.116 evidence).
- The `__expr` synthetic defn for REPL eval does NOT go through a worker — it is compiled inline on the eval path using a fresh `JITModule` owned directly by the eval call, with the same custom-`Drop` reclaim primitive. The eval-side JIT drops when the eval call returns, reclaiming the `__expr` pages. See `pipeline-v4.md` §6.2.

**Why per-batch, not per-worker?** Two reasons:

1. A long-lived worker JIT coalesces batches: all `Code` entries produced by that worker over the session share one `Arc<Jit>`, so the Arc can only drop when *every* worker-produced `Code` has been evicted. For a REPL session with hundreds of redefinitions, that refcount never reaches zero until session end — pages are never reclaimed mid-session. Per-batch JIT gives batch-level granularity: an old batch's JIT drops as soon as its outputs have been replaced.
2. Cranelift's `JITModule::define_function` is single-use per `FuncId`; a reused per-worker JIT would need `hotswap_enabled` + `prepare_for_function_redefine` to re-define symbols, and that API explicitly does NOT reclaim (Cranelift's own `FIXME` at `cranelift-jit-0.116.1/src/backend.rs:583`). Per-batch is cleaner and avoids the hotswap dance entirely.

**Thread-safety**: `JITModule` is not `Sync`, but per-batch JIT means each worker's current JIT is thread-local (stack-local during `compile_to_module`). The `Arc<Jit>` stored on `ModuleEntry::Def.code` is shared read-only (only `Drop` mutates) and the underlying `Jit`'s custom `Drop` fires on the thread that releases the last reference — no `Sync` constraint is violated.

**No memory growth concern in Wave 4**: per-batch JIT gives natural reclaim. A long-running REPL session reclaims old batches as their outputs are evicted. There is no "rotation policy" to tune — Decision 31 makes rotation meaningless because there is nothing to rotate.

### 4.6 Reload via scheduler (G11 fallout)

`reload_module` after G9:

```rust
pub fn reload_module(&mut self, module_path: &ModuleFullPath) -> Result<(), CranelispError> {
    // Clear prior codegen artifacts.
    self.clear_module_codegen(module_path);  // G6 version: walk symbol_tables, set code=None

    // Re-parse, insert into module_sexps.
    let source = std::fs::read_to_string(self.module_path_to_file(module_path))?;
    let sexps = cranelisp_frontend::parse(&source)?;
    {
        let mut map = self.shared.module_sexps.lock().unwrap_or_else(|e| e.into_inner());
        map.insert(module_path.clone(), sexps);
    }

    // Re-register with the scheduler — workers pick it up.
    self.shared.scheduler.register_module(module_path.clone(), false);

    // Wait for completion.
    self.shared.scheduler.wait_inmem_complete()?;
    Ok(())
}
```

No scoped-thread spawn. The persistent workers do the work.

### 4.7 File-watcher triggered reload

The file watcher (`src/watch.rs`) calls `session.reload_module` today. After G11 the call path is unchanged — the watcher thread still calls `reload_module`, which enqueues on the scheduler, which wakes a priority worker. The only difference is that the priority workers are now persistent — the watcher thread does not briefly block on a `thread::scope` exit.

## 5. Worker count and lifecycle details

### 5.1 Worker count

Current default: `settings.priority_workers`, configured via CLI (`--priority-workers N`) or defaulting to a setting-level default. Empirically for CI determinism, tests use 1.

Recommendation for Wave 4 default: `std::thread::available_parallelism().map(|n| n.get().saturating_sub(1)).unwrap_or(1).clamp(1, 8)`.

Rationale:
- `available_parallelism() - 1` leaves one core for the main thread + OS work.
- Clamp to [1, 8] — beyond 8 workers, contention on the scheduler Mutex and symbol-table DashMap shards grows faster than parallelism gains (no empirical data yet; 8 is a conservative upper bound).
- Tests continue to pass `priority_workers: 1` via `SessionSettings` for determinism.

Bound from above is important because **nice workers also exist** (§2.2). If priority workers = nice workers = CPU count, total threads = 2 × CPU, which oversubscribes the OS scheduler. Niceness is best-effort on macOS and does not fully prevent this (memory/feedback_no_premature_perf.md applies — we accept a simple bound and measure).

### 5.2 Shutdown sequence

`CompilerSession::shutdown` (extended from today):

```rust
pub fn shutdown(&mut self) {
    // Signal scheduler shutdown — wakes all condvars.
    self.shared.scheduler.shutdown();

    // Join priority workers.
    for handle in self.priority_worker_handles.drain(..) {
        let _ = handle.join();  // ignore join errors during shutdown
    }

    // Join nice workers (existing code).
    for handle in self.nice_worker_handles.drain(..) {
        let _ = handle.join();
    }
}
```

The `impl Drop for CompilerSession` (`src/session_v4.rs:3266–3274`) already calls `scheduler.shutdown()` defensively. After G9 it should also drain `priority_worker_handles` to ensure workers join on drop-without-shutdown. Alternatively, the `Drop` impl calls `self.shutdown()` directly — symmetric to today's nice-worker behaviour.

**Shutdown-race edge case**: session dropped while a worker is mid-`compile_to_module`. The worker holds a JIT instance (thread-local, on its stack), a borrow of `SharedState`, and a DashMap read guard. When `shutdown()` is called:
1. `scheduler.shutdown()` sets a flag and wakes all condvars. Workers parked on `take_priority_work_blocking` wake, see the flag, and return `None`, exit their loop.
2. A worker mid-codegen keeps running — its `take_priority_work_blocking` call is not currently parked; it's past the park point. The worker finishes its current work item (writes `code` to the symbol-table entry, notifies the scheduler of completion), then re-enters `take_priority_work_blocking` at the loop top, sees shutdown, returns `None`, exits.
3. `shutdown` then joins each priority-worker handle. Join waits for every worker to reach the `None` return. For a worker mid-codegen, this wait is bounded by the current codegen's runtime (tens of ms typically).

Main-thread path: `shutdown()` blocks on the join. No data races — workers only ever read `SharedState` through `Arc` or condvar-protected state; they never race with `shutdown()` except on the scheduler flag (atomic).

**Panicking worker**: if a worker panics during codegen, its `JoinHandle::join()` returns `Err`. Today's nice-worker `drain(..).let _ = ...join()` silently ignores the panic. Same pattern for priority workers. A panicking worker does NOT bring down the session; the other workers continue. This matches today's scoped-worker behaviour (scoped threads catch panics at scope exit).

### 5.3 Module-sexps and suspend-states move onto SharedState

Today's `PriorityWorkerRefs` includes `&Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>` (module_sexps) and `&Mutex<HashMap<ModuleFullPath, ModuleSuspendState>>` (suspend_states) as local fields in the caller scope. Persistent workers need these as `SharedState` fields:

```rust
pub struct SharedState {
    // … existing fields …
    pub module_sexps: Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>,
    pub suspend_states: Mutex<HashMap<ModuleFullPath, ModuleSuspendState>>,
}
```

`register_module` inserts sexps into `shared.module_sexps` and returns; workers read/remove from `shared.module_sexps` as they process. `suspend_states` is worker-owned transient state, lives on SharedState for the same reason nice-worker state does.

### 5.4 `PriorityWorkerRefs` deletion

After G9, `PriorityWorkerRefs` is deleted. Workers take `&SharedState` directly:

```rust
fn priority_worker_loop(shared: &SharedState) { /* … */ }
fn handle_typecheck_work(shared: &SharedState, module: &ModuleFullPath) -> Result<(), CranelispError> { /* … */ }
```

The `ModuleCompiler` struct (worker.rs:116) survives — it is a transient per-form builder, not a cross-thread refs bundle. Its fields that reference `PriorityWorkerRefs` change to reference `SharedState` directly.

## 6. Interaction with nice workers

Nice workers and priority workers share:
- **`SharedState`** — all compilation data (symbol_tables, codegen products today / code-on-entry post-G6, platform fn ptrs post-G8).
- **`CompileScheduler`** — nice workers call `take_object_codegen`, priority workers call `take_priority_work_blocking`. Different condvars (`priority_work_available`, `object_work_available`) wake them independently.
- **Process state** — `loaded_platforms`, cache directory, compiled `.o` paths.

Nice workers and priority workers do NOT share:
- A work pool — they are two separate pools per `concurrent-pipeline.md` §5.
- Thread-local state — each worker has its own thread-local JIT, ObjectModule, etc.

Coordination is entirely mediated by the scheduler:
- A module enters TypecheckDone → priority workers (if InMemoryAndObject mode) and nice workers BOTH can start work on it. Priority workers do background JIT; nice workers produce the `.o`.
- Priority hot-flush: `promote_nice_workers` atomic bool → nice workers self-promote to normal OS priority. Priority workers are unaffected (they run at normal priority throughout).
- Shutdown: the scheduler's `shutdown()` wakes both condvars. Both worker pools drain.

Wave 4 does not change the nice-worker code; it only adds the priority-worker persistent pool alongside.

## 7. Deletion list — Sprint 57 Wave 4

| # | Item | File:line (approx) |
|---|------|--------------------|
| 1 | `std::thread::scope` block in `register_module_with_source` | `src/session_v4.rs:1114` |
| 2 | `std::thread::scope` block in `reload_module` | `src/session_v4.rs:1013` |
| 3 | `PriorityWorkerRefs` struct | `src/worker.rs:2852` |
| 4 | `priority_worker_thread(shared: &PriorityWorkerRefs, ...)` function | `src/worker.rs:2873` |
| 5 | `PlatformRegistry` Mutex swap-in/out in `register_module_with_source` and `reload_module` | `src/session_v4.rs:993–1026, 1088–1128` (already going with G8) |
| 6 | Per-call local `module_sexps: Mutex<HashMap<_>>` construction | `src/session_v4.rs:986–990, 1081–1086` |
| 7 | Per-call local `suspend_states: Mutex<HashMap<_>>` construction | same as #6 |
| 8 | `compile_and_execute_expr` in `src/pipeline.rs:55` | Retained with Decision 31 adjustment: `__expr` continues to be compiled inline on the eval path (not on a worker), but on a fresh `JITModule` wrapped in the custom-`Drop` `Jit` newtype. The body is unchanged in shape (create JIT → call `compile_to_module` for `["__expr"]` → finalise → call → return result → drop `Jit`); only the `Jit` wrapper changes, in `/backend`'s `jit.rs`. |

Additions:
- `CompilerSession.priority_worker_handles: Vec<JoinHandle<()>>` — new field, sibling of `nice_worker_handles`.
- `SharedState.module_sexps` and `SharedState.suspend_states` — moved from per-call locals.

## 8. Risks and mitigations

### 8.1 Borrow-checker failure during refactor

**Risk**: `PriorityWorkerRefs`'s borrowed-reference design is the current glue that works with `thread::scope`. Migrating to `Arc<SharedState>` touches every worker function's signature. The refactor may surface hidden per-call mutable state that doesn't compose with `Arc` (e.g., `&mut PlatformRegistry` in `ModuleCompiler`).

**Mitigation**:
- G8 is done BEFORE G9 per the sprint order. G8 deletes the `Mutex<PlatformRegistry>` swap entirely — after G8, there is no `&mut PlatformRegistry` to worry about. This is a key reason G8 is ordered before G9.
- `ModuleCompiler` is a transient per-form builder; its fields that currently reference per-call locals migrate to `SharedState` refs naturally.
- Run the refactor incrementally: first migrate `register_module_with_source` while keeping `reload_module` on scoped workers; verify tests green; then migrate `reload_module`.

### 8.2 Shutdown-race on session drop

Covered in §5.2. Summary: bounded-wait join in `shutdown()` + defensive `shutdown()` in `Drop`. No new protocol.

### 8.3 REPL starvation — eval blocks too long

**Risk**: user types `(+ 1 2)` at the REPL. Eval enqueues on the scheduler. All priority workers are busy compiling a large prelude module. User waits 500ms.

**Mitigation**: this is not a regression — the current scoped-worker path has the same latency. The priority ladder (§5.1 of `concurrent-pipeline.md`) prioritises TypecheckFirst + BlockingJitCodegen over JitCodegen, so any prelude compilation that is blocking the REPL is prioritised. Background JIT of already-unblocked symbols yields when new BlockingJitCodegen work arrives.

For interactive responsiveness, the REPL eval path could enqueue its `__expr` as a **high-priority** form — either by re-using BlockingJitCodegen (with the REPL module as the "blocked" waiter) or by adding a new priority level for REPL submissions. Not needed for Wave 4; file as future optimisation if users report REPL lag.

<!-- FIXME(/repl): measure REPL eval latency with 4 priority workers mid-compile. If >100ms for trivial (+ 1 2), add a REPL-priority work level. -->

### 8.4 Deadlock — main thread waiting on workers, worker waiting on main

**Risk**: `wait_inmem_complete()` on the main thread blocks until all modules reach inmem_done. A worker processing a form calls out to *some* main-thread-owned function that itself blocks on the scheduler. Deadlock.

**Mitigation**: the scheduler's guarantee (`concurrent-pipeline.md` §7.1) is that workers never block on anything except scheduler condvars; all compilation work happens outside the scheduler Mutex. Main-thread paths that call scheduler methods are: `register_module` (non-blocking enqueue), `wait_inmem_complete` / `wait_object_complete` (block on completion condvar — woken by workers), `shutdown` (block on join — woken by workers returning from `take_priority_work_blocking(None)`).

No main-thread function is called *by* a worker in the current design. Preserve this invariant: the file watcher runs on its own thread (not main, not worker); cache writes are done by nice workers on their own thread.

### 8.5 Joining workers in Drop during panic unwind

**Risk**: panic in main thread → `Drop` runs → `Drop::drop` calls `shutdown()` → workers may be mid-codegen → `join()` waits for current work item → slow unwind.

**Mitigation**: `join()` with a timeout? Rust's `JoinHandle::join()` has no timeout. Options:
- Accept slow panic unwind (today's scoped-worker scope-exit has the same property).
- Use `try_join` idiom — spawn a watchdog that kills the process after a deadline.
- Skip join in Drop, only signal shutdown. Workers leak, process exits and cleans up.

Recommendation: mirror today's behaviour (bounded wait via `join`). Panic unwinds in the compiler are rare and already slow. Don't over-engineer.

## 9. Test strategy

Per the sprint plan: unit tests owned by `/int` (during Wave 4 implementation), integration tests by `/qa`.

### 9.1 Unit tests (Wave 4, in `src/session_v4.rs::tests` or `src/worker.rs::tests`)

- `persistent_worker_park_and_wake`: spawn N workers, no work enqueued, assert all workers parked (no CPU spin). Enqueue one work item, assert one worker wakes and processes it, then parks again. (Instrumentation: worker sends a channel message on entry/exit of park; test counts.)
- `persistent_worker_drain_on_shutdown`: spawn N workers, enqueue M work items, call `shutdown()`. Assert all M items processed and all workers joined within bounded time (say, 1 second in tests).
- `concurrent_register_module`: spawn N workers, enqueue K modules concurrently from the test thread, assert all K modules reach Complete. No lost updates.
- `shutdown_race_mid_codegen`: enqueue one work item that sleeps briefly (synthetic), call `shutdown()` mid-sleep, assert workers join after the work completes. Bounded wait < 500ms.

### 9.2 Integration tests (Wave 4, `/qa` in `tests/`)

- `tests/v4_persistent_workers/concurrent_modules.rs`: register 10 modules simultaneously, assert all compile.
- `tests/v4_persistent_workers/reload_during_compile.rs`: start a long compile, trigger file-watcher reload on a different module, assert both complete without wedging.
- `tests/v4_persistent_workers/repl_eval_latency.rs`: REPL eval 100 trivial expressions in sequence, assert each completes in < 100ms. Regression guard against §8.3.

### 9.3 Regression

- 14-failure baseline preserved or improved.
- All `sprint23` cache/link failures either resolve (via G6 interaction) or remain legitimate Phase-5 gaps.
- No `thread::scope` references for workers outside tests — confirmed by grep.

## 10. Descope contingency

Per `sprints/SPRINT.md` §Architecture Review condition 4, Descope B is the fallback: ship G6 + G8, defer G9 to Sprint 58.

**Descope triggers** (auto-fire):
1. `/int`'s Wave 1 design authoring time exceeds 4 hours (early signal of burden overload).
2. Wave 2 G6 regresses the 14-failure baseline (G9 depends on G6 being green).
3. Wave 3 G8 regresses the 14-failure baseline (G9 depends on `PlatformRegistry` being gone to avoid the Mutex swap — §8.1).

If descoped, G9's deliverables move intact to Sprint 58. No code is written against a partial G9 design — either workers are persistent or they are not; there is no halfway. This matches the Sprint 25 quality-gate lesson: "getting things working by not doing them isn't getting things working."

**Scope-risk assessment**: G9 is the riskiest change in Sprint 57. The migration is mechanically large (every priority-worker function signature changes), the test surface is thin (concurrency bugs may not surface until stress tests land in Wave 4), and the shutdown-race logic has never been tested end-to-end. If Wave 2 + Wave 3 consume more than 60% of the sprint's `/int` bandwidth, Descope B is the right call.

Confidence: G9 fits in Sprint 57 only if Waves 2 and 3 land cleanly with no regressions. The `/int` burden is "VERY HEAVY" per the sprint plan; Descope B is prudent insurance.

## 11. Acceptance (Wave 4 gate criteria)

1. Priority workers spawned in `CompilerSession::new`; joined in `shutdown()` and `Drop`.
2. `thread::scope` references for workers appear zero times outside `#[cfg(test)]` (confirmed by grep).
3. `register_module_with_source`, `reload_module`, REPL `eval` all submit through `scheduler.register_module` / equivalent; no per-call `thread::scope` block.
4. `PriorityWorkerRefs` struct deleted; all worker functions take `&SharedState` / `Arc<SharedState>`.
5. Shutdown-race test passes (§9.1 `shutdown_race_mid_codegen`).
6. 14-failure baseline preserved or improved.
7. REPL latency regression test passes (<100ms median for trivial eval).
8. File-watcher reload during mid-compile works end-to-end.
9. `cargo clippy -p cranelisp --all-targets` clean.

## 12. Next skills

After this design doc is approved and Waves 2 + 3 land cleanly:

- `/int` — execute Wave 4 per §7 deletion list + §11 acceptance criteria.
- `/qa` — write the integration tests in §9.2; verify REPL latency regression guard.
- `/review` — enforce the `grep -n "thread::scope"` → zero-outside-tests invariant; verify shutdown-race handling matches §5.2.
- `/repl` — update the REPL demo script to exercise concurrent-module behaviour if the new shape is visible (it shouldn't be, but file a FIXME if it is).
- `/sprint` — verify Descope B triggers are not firing; gate Wave 4 start on `/arch` Wave 1 sign-off.
