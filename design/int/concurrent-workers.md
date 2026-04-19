# Multi-Threaded Priority Workers — Step 11 Design

## 1. Problem Statement

The priority worker loop (`priority_worker_loop`) currently runs inline on the calling thread inside `CompilerSession::register_module()`. This means:

1. **No parallelism.** Only one module is typechecked and codegenned at a time, even when independent modules exist in the scheduler's ready queues.
2. **`WorkerContext` holds `&mut` references.** `WorkerContext` borrows `&mut TypeChecker` and `&mut InMemWorkerState`, making it impossible to share across threads.
3. **`InMemWorkerState` conflates shared and per-worker concerns.** The GOT table (shared, already atomic) is bundled with JIT instances (per-worker, must stay alive for code pointer validity) and trace state (REPL-only, irrelevant to batch workers).
4. **`take_priority_work` returns `None` immediately** when no work is available instead of parking on a condvar. Workers cannot wait for new work to arrive.

Step 11 spawns N priority worker threads running `priority_worker_loop`, replaces `&mut` borrows with shared references, decomposes `InMemWorkerState` into shared and per-worker parts, and adds condvar parking to `take_priority_work`.

## 2. WorkerContext Refactor

### Before

```rust
pub struct WorkerContext<'a> {
    pub tc: &'a mut cranelisp_typecheck::TypeChecker,
    pub scheduler: &'a CompileScheduler,
    pub inmem_worker: &'a mut InMemWorkerState,
    pub platform_registry: &'a mut PlatformRegistry,
    pub lib_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
    pub object_codegen_stash: Option<&'a Mutex<
        HashMap<ModuleFullPath, ObjectCodegenInput>,
    >>,
}
```

Problems: `&mut TypeChecker` and `&mut InMemWorkerState` prevent sharing across threads. `&mut PlatformRegistry` is unnecessarily mutable (the registry is read-only during codegen after platform loading completes).

### After

```rust
pub struct WorkerContext<'a> {
    pub tc: &'a TypeChecker,                          // shared, &self API (Step 12)
    pub scheduler: &'a CompileScheduler,              // shared, internal Mutex
    pub shared_codegen: &'a SharedCodegenState,       // shared, concurrent internals
    pub worker_jit: WorkerJitState,                   // owned, per-worker
    pub platform_registry: &'a PlatformRegistry,      // shared, read-only
    pub lib_dirs: &'a [PathBuf],                      // shared, read-only
    pub project_root: &'a Path,                       // shared, read-only
    pub object_codegen_stash: Option<&'a Mutex<
        HashMap<ModuleFullPath, ObjectCodegenInput>,
    >>,                                               // shared, Mutex-protected
}
```

Key changes:

- `tc` becomes `&TypeChecker`. Step 12 (DashMap migration) makes `check_form` take `&self`. Until Step 12 lands, a `Mutex<TypeChecker>` wrapper is used (see migration strategy, section 10).
- `inmem_worker` is split into `shared_codegen` (shared `&`) and `worker_jit` (owned). The worker creates its own `WorkerJitState` at thread start and drains it to shared state on completion.
- `platform_registry` drops `&mut`. It is populated during platform loading (before workers start) and read-only thereafter.

### Thread Safety

`WorkerContext` is not `Send` (it holds references with a scoped lifetime `'a`). Each worker thread constructs its own `WorkerContext` from the shared references passed via `std::thread::scope`. The references' lifetimes are bounded by the scope.

## 3. SharedCodegenState Design

Replaces the shared subset of `InMemWorkerState`. Owned by `CompilerSession`, passed to workers as `&SharedCodegenState`.

```rust
/// Shared codegen state accessible by all priority workers concurrently.
///
/// All fields use concurrent data structures (atomics, DashMap, Mutex)
/// or are read-only after construction.
pub struct SharedCodegenState {
    /// The GOT table. Already uses AtomicPtr slots. Workers write to
    /// pre-assigned disjoint slots via store(Release). Read by JIT code
    /// via raw pointer loads.
    pub got_table: Arc<GotTable>,

    /// Next available GOT slot index. Atomically incremented by
    /// `ensure_slot_for`. Replaces the plain `usize` counter on
    /// ModuleCodegenState.
    pub next_got_slot: AtomicUsize,

    /// Per-definition codegen artifacts (GOT slot, code pointer, param
    /// count, defn). Concurrent read+write via DashMap. Replaces the
    /// HashMap on ModuleCodegenState.
    pub def_codegen: DashMap<Symbol, DefCodegen>,

    /// JIT instances that must stay alive (their code memory is
    /// referenced via GOT). Workers drain their per-worker JIT vecs
    /// here at module completion.
    pub kept_jits: Mutex<Vec<Jit>>,

    /// Linker instances from cache-hit loads. Must stay alive because
    /// their code_regions hold executable memory. Workers drain their
    /// per-worker linker vecs here at module completion.
    pub kept_linkers: Mutex<Vec<Linker>>,

    /// Shared ISA for creating Jit instances without re-probing CPU
    /// features. Built once at session start, cloned for each worker.
    pub shared_isa: Arc<dyn TargetIsa>,
}
```

### Concurrency model per field

| Field | Type | Read by | Written by | Ordering |
|-------|------|---------|------------|----------|
| `got_table` | `Arc<GotTable>` (AtomicPtr slots) | JIT code (raw load) | Workers (store Release) | Release/Acquire per slot |
| `next_got_slot` | `AtomicUsize` | Workers (load for check) | Workers (fetch_add for alloc) | AcqRel on fetch_add |
| `def_codegen` | `DashMap<Symbol, DefCodegen>` | Workers (slot lookup, arity lookup) | Workers (slot assign, code_ptr update) | DashMap per-shard locks |
| `kept_jits` | `Mutex<Vec<Jit>>` | Never during compilation | Workers (push after module done) | Mutex |
| `kept_linkers` | `Mutex<Vec<Linker>>` | Never during compilation | Workers (push after module done) | Mutex |
| `shared_isa` | `Arc<dyn TargetIsa>` | Workers (clone to create Jit) | Never (read-only) | Immutable |

### `ensure_slot_for` — Thread-Safe Version

The current `ModuleCodegenState::ensure_slot_for` does a read-then-maybe-write on both `def_codegen` and `next_got_slot`. The concurrent version:

```rust
impl SharedCodegenState {
    pub fn ensure_slot_for(&self, name: &Symbol) -> Result<usize, CranelispError> {
        // Fast path: already has a slot.
        if let Some(entry) = self.def_codegen.get(name) {
            if let Some(slot) = entry.got_slot {
                return Ok(slot);
            }
        }

        // Slow path: allocate a new slot atomically.
        // Use entry API with or_insert_with for atomic insert-if-absent.
        let mut entry = self.def_codegen.entry(name.clone()).or_default();
        if let Some(slot) = entry.got_slot {
            return Ok(slot); // Another thread won the race.
        }

        let slot = self.next_got_slot.fetch_add(1, Ordering::AcqRel);
        if slot >= GOT_TABLE_SIZE {
            return Err(CranelispError::CodegenError {
                message: format!("GOT table full (max {GOT_TABLE_SIZE})"),
                span: Span::SYNTHETIC,
            });
        }
        entry.got_slot = Some(slot);
        Ok(slot)
    }
}
```

The DashMap `entry()` API holds the shard lock for the duration of the `or_insert_with` + mutation, preventing two threads from allocating duplicate slots for the same symbol.

## 4. WorkerJitState Design

Per-worker state, created at thread start, drained to shared state at module completion.

```rust
/// Per-worker JIT state. Stack-local in each priority worker thread.
///
/// Not shared across threads. Each worker accumulates JIT instances
/// and linkers during codegen, then drains them to SharedCodegenState
/// when the module is complete.
pub struct WorkerJitState {
    /// JIT instances created by this worker. Drained to
    /// shared_codegen.kept_jits after each module's codegen sweep.
    pub jit_modules: Vec<Jit>,

    /// Linker instances from cache-hit loads on this worker. Drained
    /// to shared_codegen.kept_linkers after each module's codegen.
    pub cache_linkers: Vec<Linker>,
}

impl WorkerJitState {
    pub fn new() -> Self {
        WorkerJitState {
            jit_modules: Vec::new(),
            cache_linkers: Vec::new(),
        }
    }

    /// Drain accumulated JIT and Linker instances to shared state.
    /// Called after each module's codegen sweep completes.
    pub fn drain_to_shared(&mut self, shared: &SharedCodegenState) {
        if !self.jit_modules.is_empty() {
            let mut kept = shared.kept_jits.lock()
                .unwrap_or_else(|e| e.into_inner());
            kept.extend(self.jit_modules.drain(..));
        }
        if !self.cache_linkers.is_empty() {
            let mut kept = shared.kept_linkers.lock()
                .unwrap_or_else(|e| e.into_inner());
            kept.extend(self.cache_linkers.drain(..));
        }
    }
}
```

### Lifecycle

1. **Thread start**: Worker creates `WorkerJitState::new()`.
2. **Per-module codegen**: Worker accumulates JIT instances in `jit_modules` (one per `compile_and_register_defn` call).
3. **Module complete**: Worker calls `drain_to_shared()` to move JITs and Linkers to the session-level vectors.
4. **Thread exit**: `WorkerJitState` is dropped. It should be empty (all JITs drained). Debug assert on drop that vectors are empty.

### Trace State

`traced_fns` and `trace_extra_symbols` from the old `InMemWorkerState` are REPL-only features. They are not needed by batch priority workers. In the REPL path, the eval loop runs inline (not via spawned workers) and can continue to use a local trace context. These fields are omitted from `WorkerJitState`.

## 5. JIT Lifecycle Audit

> **2026-04-19 reconciliation (Decision 31).** This section previously discussed a `JITModule::finish()` API that does not exist in Cranelift 0.116. The canonical framing is now: `Arc<Jit>` on each `ModuleEntry::Def.code`, custom `Drop` on the `Jit` wrapper calls `unsafe JITModule::free_memory()`, per-batch reclaim when the Arc refcount hits zero. The `kept_jits` vector in earlier sections of this document is superseded by that mechanism. The material below is retained for historical context and is no longer the target design.

### Finding (historical)

The `Jit` struct wraps `cranelift_jit::JITModule`. The code calls `self.module.finalize_definitions()` in `Jit::finalize()` (line 451 of `jit.rs`). It does NOT call `JITModule::finish()`.

**Correction (2026-04-19)**: Cranelift 0.116 does NOT expose a `finish()` method on `JITModule`. The method this section assumed is not present in the version we depend on — grep `cranelift-jit-0.116.1/src/backend.rs` for `fn finish` returns zero matches. The two relevant methods that DO exist are:

- `finalize_definitions()` — patches relocations and makes code executable. Code pointers are valid after this call.
- `free_memory(self) -> ()` (`unsafe`) — consumes the `JITModule` and frees its executable memory. Documented at `cranelift-jit-0.116.1/src/backend.rs:219` with the contract: "none of the functions from that module are currently executing and none of the `fn` pointers are called afterwards."

And critically, `Memory::drop` leaks on purpose (`cranelift-jit-0.116.1/src/memory.rs:269-276`) — the default drop path does NOT free pages. So to actually reclaim executable memory, callers MUST explicitly invoke `unsafe JITModule::free_memory(self)` when the fn-pointer-reachability contract is upheld.

### Target mechanism (Decision 31)

- `Jit` is a thin newtype wrapping `ManuallyDrop<JITModule>` with a custom `Drop` that calls `unsafe JITModule::free_memory()`.
- Each `ModuleEntry::Def.code` holds `Arc<Jit>` — N functions produced by one `compile_to_module` call share one underlying `Jit`.
- When every `Code` entry referencing a particular `Arc<Jit>` is dropped (evicted / redefined in the REPL), the Arc refcount reaches zero, the `Jit` `Drop` fires, and `free_memory` reclaims the batch's pages.
- Safety contract upheld by: (a) every code pointer either lives on a `ModuleEntry::Def.code` (refcount > 0) or is ephemeral; (b) GOT slots are atomically swapped to new code before the old Arc can drop; (c) user-returned `fn` values are heap closures calling through the GOT, not raw code pointers.

Per-worker batch JITs under this scheme are stack-local during `compile_to_module`; the worker moves the `Arc<Jit>` onto each produced `Code` entry and returns to the priority ladder. There is no `kept_jits` vector, no `drain_to_shared` step, and no need for workers to hold long-lived JIT state.

The earlier `kept_jits`/`drain_to_shared` design (below in this document) is superseded. It was a correct workaround given a misunderstanding of Cranelift's drop semantics (assumed default drop would invalidate pointers); the real behaviour is the opposite — default drop leaks, and explicit `free_memory` is required. The Decision 31 mechanism is the canonical reclaim path.

**FIXME(/backend)**: implement the custom `Drop` on `Jit` (in `crates/cranelisp-backend/src/jit.rs`) that calls `unsafe JITModule::free_memory()`. The safety proof is the Arc-refcount-zero + symbol-table-and-GOT-discipline invariant from Decision 31. The previously-filed `FIXME(/backend)` about adding a `Jit::finish()` wrapper is re-aimed at this target.

## 6. GOT Slot Assignment

### Current State

`ModuleCodegenState` owns:
- `got_table: Option<Arc<GotTable>>` — already atomic, already shared via Arc
- `next_got_slot: usize` — plain counter, NOT thread-safe
- `def_codegen: HashMap<Symbol, DefCodegen>` — plain HashMap, NOT thread-safe

### Target State

`SharedCodegenState` owns all three (Section 3):
- `got_table: Arc<GotTable>` — unchanged, allocated eagerly at session start
- `next_got_slot: AtomicUsize` — atomic counter
- `def_codegen: DashMap<Symbol, DefCodegen>` — concurrent map

### Slot Assignment Flow

Slots are assigned during `pre_register_got_slots`, which runs per-module before codegen. Since the scheduler guarantees no two workers typecheck/codegen the same module simultaneously, slot assignment for a given module is single-writer. But two workers may concurrently assign slots for different modules. The `AtomicUsize` counter and DashMap handle this correctly.

The `ensure_slot_for` implementation (Section 3) uses DashMap's `entry()` API to atomically check-and-allocate. Two threads calling `ensure_slot_for` with the same symbol will not allocate duplicate slots — one wins the entry lock, the other finds the slot already assigned.

### GOT Writes

`GotTable.store_slot(slot, ptr)` already uses `AtomicPtr::store(Release)`. Workers writing to disjoint slots (guaranteed by slot assignment) is safe. No changes needed to the write path.

### GOT Reads During Codegen

`compile_and_register_defn` currently builds `got_slots: HashMap<Symbol, usize>` by iterating `inmem_worker.got_state.def_codegen`. With `DashMap`, this becomes:

```rust
let got_slots: HashMap<Symbol, usize> = shared_codegen.def_codegen
    .iter()
    .filter_map(|entry| entry.got_slot.map(|s| (entry.key().clone(), s)))
    .collect();
```

DashMap iteration acquires and releases shard locks incrementally. This is safe but may see a partially-consistent view if another thread is concurrently inserting entries. This is acceptable: the GOT slot map is a snapshot used for the current compilation. Missing entries (from modules being concurrently compiled) are handled by `ensure_slot_for` which allocates on demand.

## 7. `register_module` Flow Change

### Before (Inline Worker Loop)

```
register_module(module_name, source)
    ├── parse source
    ├── scheduler.register_module(module)
    ├── build WorkerContext {tc: &mut, inmem: &mut, ...}
    ├── priority_worker_loop(&mut ctx, &mut module_sexps)   // INLINE
    │     └── loop: take_priority_work → process → codegen
    ├── scheduler.wait_inmem_complete()
    └── register_module_aliases()
```

The calling thread does all the work. No concurrency.

### After (Spawned Workers)

```
register_module(module_name, source)
    ├── parse source
    ├── scheduler.register_module(module)
    ├── store parsed sexps in shared sexp map (Mutex<HashMap>)
    ├── scheduler.wake_priority_workers()   // signal condvar
    ├── scheduler.wait_inmem_complete()     // BLOCK on condvar
    └── register_module_aliases()
```

Worker threads (spawned by `spawn_priority_workers`) do the actual work:

```
priority_worker_thread()
    ├── create WorkerJitState::new()
    └── loop:
          ├── scheduler.take_priority_work()  // parks on condvar if empty
          ├── build WorkerContext from shared refs + owned worker_jit
          ├── match work:
          │     Typecheck(module) → process_module_forms(ctx, ...)
          │     BlockingJitCodegen → compile symbol
          │     JitCodegen → compile symbol
          ├── worker_jit.drain_to_shared(shared_codegen)
          └── continue
```

### Sexp Storage

Currently `module_sexps: HashMap<ModuleFullPath, Vec<Sexp>>` is a local variable in `priority_worker_loop`. With multiple workers, parsed sexps must be shared. Options:

1. **`Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>`** on `SharedState` — simple, low contention (sexps are inserted once at registration time and cloned by the worker).
2. **`DashMap<ModuleFullPath, Vec<Sexp>>`** — more concurrent, but overkill for the access pattern.

**Decision**: Use `Mutex<HashMap>`. The map is written to by the registration path (single-threaded) and read by workers (clone the sexps, release the lock). Contention is minimal.

### Suspend State

`suspend_states: HashMap<ModuleFullPath, ModuleSuspendState>` is currently local to `priority_worker_loop`. With multiple workers, a module may be resumed on a different thread than the one that started it. Suspend state must be shared.

**Decision**: Store suspend states in a `Mutex<HashMap<ModuleFullPath, ModuleSuspendState>>` on `SharedState`. Workers lock briefly to take/put suspend state at the start/end of processing a module. The `ModuleCheckAccumulator` and `expanded_program` Vec inside `ModuleSuspendState` are moved out of the map (not cloned) during processing, so the lock is not held during compilation.

## 8. Thread Spawning

### `spawn_priority_workers(n)`

Currently a no-op. Target implementation:

```rust
impl CompilerSession {
    pub fn run_with_priority_workers<T>(
        &mut self,
        n: usize,
        f: impl FnOnce(&mut Self) -> Result<T, CranelispError>,
    ) -> Result<T, CranelispError> {
        let shared_arc = Arc::clone(&self.shared);

        std::thread::scope(|scope| {
            // Spawn N priority worker threads.
            for i in 0..n {
                let shared = Arc::clone(&shared_arc);
                scope.spawn(move || {
                    priority_worker_thread(&shared, i);
                });
            }

            // Run the caller's closure (registers modules, waits).
            let result = f(self);

            // Signal shutdown — workers will exit after draining work.
            self.shared.scheduler.shutdown();

            result
        })
    }
}
```

### Interaction with `run_with_nice_workers`

Nice workers already use `std::thread::scope`. The two scopes must be nested or merged:

```rust
// Option A: Nested scopes (simpler, both pools active during the closure)
session.run_with_nice_workers(nice_count, |session| {
    session.run_with_priority_workers(priority_count, |session| {
        session.register_module(...)?;
        Ok(())
    })
})

// Option B: Single scope with both pools
session.run_with_all_workers(priority_count, nice_count, |session| {
    session.register_module(...)?;
    Ok(())
})
```

**Decision**: Option B (single scope). A single `std::thread::scope` spawns both priority and nice workers. This avoids nested scope complexity and ensures both pools share the same lifetime boundary. The closure runs on the calling thread — it registers modules (which wakes priority workers) and waits for completion.

```rust
pub fn run_with_workers<T>(
    &mut self,
    priority_count: usize,
    nice_count: usize,
    f: impl FnOnce(&mut Self) -> Result<T, CranelispError>,
) -> Result<T, CranelispError> {
    let shared_arc = Arc::clone(&self.shared);

    std::thread::scope(|scope| {
        // Spawn priority workers.
        for i in 0..priority_count {
            let shared = Arc::clone(&shared_arc);
            scope.spawn(move || {
                priority_worker_thread(&shared, i);
            });
        }

        // Spawn nice workers.
        spawn_nice_workers(scope, &shared_arc, nice_count);

        // Run the caller's work on the calling thread.
        let result = f(self);

        // Shutdown sequence.
        let _ = self.wait_object_complete();
        self.shared.scheduler.shutdown();

        result
    })
}
```

### Worker Count

Priority workers: `std::thread::available_parallelism()` minus 1 (one core reserved for the calling thread and nice workers). Minimum 1.

Nice workers: 1 (object codegen is IO-bound, not CPU-bound). Same as current.

### `take_priority_work` Condvar Parking

Currently returns `None` immediately when no work is available. Must change to park on a condvar:

```rust
pub fn take_priority_work(&self) -> Option<PriorityWork> {
    let mut state = self.lock();
    loop {
        if state.shutdown {
            return None;
        }

        // Level 1-4 ladder (unchanged logic)
        if let Some(work) = Self::try_take_work_locked(&mut state) {
            return Some(work);
        }

        // No work available — check if all modules are done.
        if Self::all_inmem_complete_locked(&state) {
            return None; // No more work will arrive.
        }

        // Park until woken by register_module, unblock, or
        // notify_typecheck_done.
        state = self.priority_work_available.wait(state)
            .unwrap_or_else(|e| e.into_inner());
    }
}
```

The condvar `priority_work_available` (already exists on `CompileScheduler`) must be notified in:
- `register_module` — new module available for typecheck
- `try_unblock_locked` — blocked module becomes ready
- `notify_typecheck_done` — module ready for JIT codegen (Level 4)
- `shutdown` — wake all parked workers to exit

## 9. `compile_and_register_defn` Refactor

### Before

```rust
pub fn compile_and_register_defn(
    inmem_worker: &mut InMemWorkerState,
    platform_symbols: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    // ...
    let mut jit = Jit::new_with_symbols(&extra_symbols)?;
    // ...
    let slot = inmem_worker.got_state.ensure_slot_for(&defn.name)?;
    // iterate inmem_worker.got_state.def_codegen for got_slots...
    // iterate inmem_worker.got_state.def_codegen for func_arities...
    let got_base = inmem_worker.got_state.got_base_ptr() as i64;
    // ...
    inmem_worker.got_state.update_slot(slot, code_ptr);
    inmem_worker.got_state.def_codegen.entry(...).or_default() = ...;
    inmem_worker.jit_modules.push(jit);
}
```

### After

```rust
pub fn compile_and_register_defn(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_symbols: &[(String, *const u8)],
    defn: &Defn,
    check: &CheckResult,
) -> Result<(), CranelispError> {
    let extra_symbols: Vec<(&str, *const u8)> = platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();
    let mut jit = Jit::new_with_isa(
        Arc::clone(&shared_codegen.shared_isa),
        &extra_symbols,
    )?;

    jit.declare_intrinsics()?;
    let func_ids = jit.declare_functions(&[defn])?;

    // Slot assignment via concurrent SharedCodegenState.
    let slot = shared_codegen.ensure_slot_for(&defn.name)?;

    // Snapshot GOT slots and func arities from DashMap.
    let got_slots: HashMap<Symbol, usize> = shared_codegen.def_codegen
        .iter()
        .filter_map(|e| e.got_slot.map(|s| (e.key().clone(), s)))
        .collect();

    let got_base = shared_codegen.got_table.base_ptr() as i64;

    let func_arities: HashMap<Symbol, usize> = shared_codegen.def_codegen
        .iter()
        .filter_map(|e| e.param_count.map(|pc| (e.key().clone(), pc)))
        .collect();

    let compile_ctx = jit.build_compile_context(
        check, &func_ids, &func_arities,
        Some(&got_slots), Some(got_base), None,
    );
    let _clif_ir = jit.compile_defn(defn, compile_ctx)?;

    let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    // Atomic write to GOT slot.
    shared_codegen.got_table.store_slot(slot, code_ptr);

    // Update def_codegen via DashMap.
    let mut entry = shared_codegen.def_codegen.entry(defn.name.clone()).or_default();
    entry.code_ptr = Some(code_ptr);
    entry.got_slot = Some(slot);
    entry.param_count = Some(defn.params().len());
    entry.defn = Some(defn.clone());
    drop(entry); // Release DashMap shard lock explicitly.

    // Keep JIT alive (code memory is still owned by JITModule).
    worker_jit.jit_modules.push(jit);

    Ok(())
}
```

### Callers

`codegen_module_symbols` changes similarly:

```rust
pub fn codegen_module_symbols(
    shared_codegen: &SharedCodegenState,
    worker_jit: &mut WorkerJitState,
    platform_registry: &PlatformRegistry,
    scheduler: &CompileScheduler,
    module: &ModuleFullPath,
    program: &[TopLevel],
    check: &CheckResult,
) -> Result<(), CranelispError> {
    // ...
    pre_register_got_slots(shared_codegen, program)?;
    // compile_and_register_defn(shared_codegen, worker_jit, ...)
    // ...
}
```

And `pre_register_got_slots`:

```rust
fn pre_register_got_slots(
    shared_codegen: &SharedCodegenState,
    program: &[TopLevel],
) -> Result<(), CranelispError> {
    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                shared_codegen.ensure_slot_for(&defn.name)?;
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    shared_codegen.ensure_slot_for(&method.name)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}
```

## 10. Migration Strategy

The refactor is mechanical but touches many call sites. The following order minimizes intermediate breakage and keeps tests green at each step.

### Wave 1: Extract SharedCodegenState (no threading change)

1. **Create `SharedCodegenState` struct** in `src/session.rs`. Initially wraps the same data as `ModuleCodegenState` but with `AtomicUsize` and `DashMap`:
   - `got_table: Arc<GotTable>` (move from `ModuleCodegenState`)
   - `next_got_slot: AtomicUsize` (replace `usize`)
   - `def_codegen: DashMap<Symbol, DefCodegen>` (replace `HashMap`)
   - `kept_jits: Mutex<Vec<Jit>>`
   - `kept_linkers: Mutex<Vec<Linker>>`
   - `shared_isa: Arc<dyn TargetIsa>`

2. **Create `WorkerJitState` struct** in `src/session.rs`.

3. **Add `shared_codegen: SharedCodegenState` to `CompilerSession`** (or `SharedState`). Initialize in constructor.

4. **Refactor `compile_and_register_defn`** to take `(&SharedCodegenState, &mut WorkerJitState)` instead of `&mut InMemWorkerState`. Update all callers in `src/worker.rs`.

5. **Refactor `codegen_module_symbols`** and `pre_register_got_slots` similarly.

6. **Update `WorkerContext`**: replace `inmem_worker: &mut InMemWorkerState` with `shared_codegen: &SharedCodegenState`. Add `worker_jit: WorkerJitState` as an owned field.

7. **Update `priority_worker_loop`**: create `WorkerJitState` at the top, drain to shared after each module.

8. **Remove `InMemWorkerState.got_state` and `InMemWorkerState.jit_modules`**. Keep `InMemWorkerState` as a shell for trace fields (REPL-only), or inline those into the REPL eval path.

9. **All tests pass** — everything still runs single-threaded inline on the calling thread. The data structures are concurrent-safe but used by one thread.

### Wave 2: Add condvar parking to `take_priority_work`

1. **Change `take_priority_work`** to loop with condvar wait when no work and not all done.

2. **Add `notify_all()` calls** on `priority_work_available` in `register_module`, `try_unblock_locked`, `notify_typecheck_done`, and `shutdown`.

3. **Tests pass** — single-threaded workers still work (they just never park because work is available before they check).

### Wave 3: Spawn priority worker threads

1. **Implement `run_with_workers`** (Section 8) combining priority and nice worker spawning.

2. **Update `register_module`**: remove the inline `priority_worker_loop` call. Instead, store sexps in the shared sexp map and wake workers.

3. **Move `module_sexps` and `suspend_states`** to `SharedState` behind `Mutex`.

4. **Change `WorkerContext.tc`** from `&mut TypeChecker` to either:
   - `&Mutex<TypeChecker>` (interim, if Step 12 DashMap is not ready), or
   - `&TypeChecker` (if Step 12 DashMap lands first — per the sprint plan, Steps 11+12 ship together).

5. **Update the batch entry point** (`main.rs` or `session_v4.rs`) to call `run_with_workers` instead of the separate `run_with_nice_workers` + inline worker loop.

6. **Thread sanitizer validation**: `RUSTFLAGS="-Z sanitizer=thread" cargo test` must be clean.

### Wave 4: Cleanup

1. **Delete `InMemWorkerState`** if all its fields have been moved or inlined.
2. **Delete `ModuleCodegenState`** — fully replaced by `SharedCodegenState`.
3. **Remove `spawn_priority_workers` no-op** — replaced by `run_with_workers`.
4. **Update `run_with_nice_workers`** to delegate to `run_with_workers(0, n, f)` or remove if unused.

### Dependencies

- **Step 12 (DashMap TypeChecker)**: Wave 3 step 4 depends on this. If Step 12 is not ready, use `Mutex<TypeChecker>` as an interim (one worker at a time serializes on the TC mutex — still correct, just no parallelism gain from multi-threading until Step 12 lands). Since the sprint combines Steps 11+12, this interim should be brief.
- **`dashmap` crate dependency**: needed in `cranelisp` binary crate (for `SharedCodegenState.def_codegen`). Add to workspace `Cargo.toml`.

## Sketch Comparison

The sketch does not have multi-threaded compilation. It uses a single-threaded pipeline with batch and REPL as separate code paths. There is nothing to compare for concurrency patterns.

The GOT mechanism (atomic slots, `ensure_slot_for`) was designed in the reimplementation specifically for concurrent workers. The sketch used direct function pointers without a GOT.
