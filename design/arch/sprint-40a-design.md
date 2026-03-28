# Sprint 40a Design: Parallel compile_unit and N-Core Codegen Dispatch

## Wave 0: North-Star main.rs

Rewrite `src/main.rs` to match `pipeline-v3.md` §2.2 **verbatim** — the exact code from the design doc, with `todo!()` bodies for anything not yet implemented. This is the structural north star. Each subsequent wave fills in a `todo!()`.

### Target main.rs (from pipeline-v3.md §2.2)

```rust
fn main() {
    let (action, entry_module_path, settings) = parse_args();

    let entry_module_name = slug(entry_module_path);
    let project_root = base_dir(entry_module_path);

    let mut s = CompilerSession::new(settings, project_root);

    let src = read_file(entry_module_path);
    let codegen = match action {
        Link => ObjectOnly,
        _ => InMemoryAndObject,
    };
    let ctx = CompileContext::new(entry_module_name, codegen);

    if let Release = action {
        return s.build_release(&ctx);
    }

    s.compile_unit(&src, &ctx, Replace);

    match action {
        Run | Repl => s.spawn_hot_inmem_codegen(),
        _ => {}
    }
    s.spawn_nice_object_codegen();

    match action {
        Repl => {
            s.spawn_file_watcher();
            loop {
                let src = read_line();
                s.pause_watcher_codegen();      // prevent GOT changes during eval
                s.hot_flush_in_mem_queue();     // drain pending watcher codegen
                if let Some(form) = match s.process_commands(&src) {
                    Nothing => None,
                    Final(form) => Some(form),
                    Compile(src) => Some(s.compile_unit(&src, &ctx, Additive)),
                } {
                    pretty_print_form(form);
                }
                s.resume_watcher_codegen();     // allow watcher codegen again
            }
            s.hot_flush_object_queue();
        }
        Run => {
            s.hot_flush_in_mem_queue();
            s.trampoline(&ctx);
            s.hot_flush_object_queue();
        }
        Link => {
            s.hot_flush_object_queue();
            s.link(&ctx);
        }
        Release => {}
    }
}
```

### Status at Wave 0 start

**Works now (real implementations exist):**
- `parse_args()`, `slug()`, `base_dir()`, `read_file()`
- `CompilationSession::new(...)` (name is `CompilationSession`, becomes `CompilerSession`)
- `CompileContext { module, codegen }` construction
- `s.compile_unit(&src, &ctx, Replace)` (currently `&mut self`, becomes `&self` in Wave 2)

**Stubs/todo at Wave 0:**
- `s.spawn_hot_inmem_codegen()` — stub exists, real pool in Wave 3
- `s.spawn_nice_object_codegen()` — stub exists, real pool in Wave 3
- `s.spawn_file_watcher()` — exists on `ReplSession`, needs to move to `CompilerSession` (Wave 4)
- `s.hot_flush_in_mem_queue()` — stub exists (synchronous drain)
- `s.hot_flush_object_queue()` — stub exists
- `s.process_commands(&src)` — exists on `ReplSession`, needs to move to `CompilerSession` (Wave 4)
- `s.trampoline(&ctx)` — `todo!()`, needs implementing (verify main, execute, IO trampoline)
- `s.link(&ctx)` — `todo!()`, link mode logic needs to become a method
- `pretty_print_form(form)` — `todo!()`, needs implementing
- `s.pause_watcher_codegen()` / `s.resume_watcher_codegen()` — `todo!()`, needed for GOT stability (Wave 3)
- `s.build_release(&ctx)` — `todo!()`, future Release mode

### REPL watcher exclusion pattern

During REPL expression evaluation (from `hot_flush_in_mem_queue` through execution to result display), watcher-triggered codegen must not write to the GOT. The REPL loop must bracket the critical section:

```rust
Repl => {
    loop {
        let src = read_line();
        s.pause_watcher_codegen();      // prevent GOT changes during eval
        s.hot_flush_in_mem_queue();     // drain pending watcher codegen
        if let Some(form) = match s.process_commands(&src) {
            Nothing => None,
            Final(form) => Some(form),
            Compile(src) => Some(s.compile_unit(&src, &ctx, Additive)),
        } {
            pretty_print_form(form);
        }
        s.resume_watcher_codegen();     // allow watcher codegen again
    }
}
```

This ensures the GOT is stable during execution — a function mid-execution always sees consistent code pointers for its callees. Watcher `compile_unit` calls (stages 1-5) can continue during this window — only codegen enqueuing is paused. This keeps typecheck latency low while protecting execution consistency.

## Problem Statement

Two items were deferred from Sprint 40:

1. **Parallel dependency typechecking** — `compile_unit` takes `&mut self` on `CompilationSession`, preventing parallel calls for independent dependencies.
2. **N-core codegen dispatch** — The coordinator thread processes CodegenPackets sequentially. Atomic GOT, shared ISA, and CodegenPacket infrastructure exist but actual multi-thread dispatch is not implemented.

## Part 1: Make compile_unit Callable with &self

### 1.1 Mutation Audit

Every mutation inside `compile_unit_inner` falls into four categories:

**A. Per-call state (must become local/parameter):**
- `compile_stack` — cycle detection → move to parameter
- `tc.state: CheckState` — transient typecheck state → `check()` creates locally

**B. Shared state needing synchronization:**
- `module_deps` → `Mutex<ModuleDependencyGraph>`
- `tc.modules` → `RwLock<HashMap<..., Arc<RwLock<SymbolTable>>>>`
- `loaded_platforms` → `Mutex`
- `platform_symbols` → `RwLock` (frequent reads, rare writes)
- `scheduling_registry` → `Mutex`
- `inmem_worker.got_state` → behind `Mutex<InMemWorkerState>`
- `object_worker.cache_state` → behind `Mutex<ObjectWorkerState>`

**C. Read-only during compile_unit:**
- `lib_dirs`, `project_root`, `interactive`, `shared_isa`, `expander`

**D. Codegen dispatch (not touched by stages 1-5):**
- `inmem_queue`, `object_queue`, `codegen_mode`

### 1.2 CheckState as Local — The Key Refactoring

`check()` creates a stack-local `CheckState` instead of using `self.state`:

```rust
pub fn check(&self, program: &[TopLevel], ctx: &CompileContext, strategy: ModuleStrategy)
    -> Result<CheckResult, CranelispError>
{
    let mut cs = CheckState::new(ctx.module.clone());
    // ... use cs throughout ...
}
```

All ~30 internal methods gain `cs: &mut CheckState` as parameter. Replace `self.state.field` with `cs.field`.

**REPL additive overloads**: Before returning from `check()`, serialize overloads/resolved_overloads into the symbol table. On next `check()` with `Additive`, reconstruct from symbol table into new `CheckState`.

**`set_current_module` elimination**: Split into `ensure_module_exists(&self)` (brief write lock on modules map) + module identity in `CheckState::current_module`.

### 1.3 tc.modules Concurrency Model

`tc.modules: RwLock<HashMap<ModuleFullPath, Arc<RwLock<SymbolTable>>>>`

Two-level locking:
- **Outer RwLock**: protects HashMap structure. Read-locked for lookups. Write-locked only for new modules (rare).
- **Inner Arc<RwLock<SymbolTable>>**: per-module data protection. `compile_unit` write-locks its target module, read-locks other modules for import resolution.

Replace `current_symbol_table()` / `current_symbol_table_mut()` with:
- `module_read_lock(path) -> RwLockReadGuard<SymbolTable>`
- `module_write_lock(path) -> RwLockWriteGuard<SymbolTable>`

### 1.4 compile_stack as Parameter

```rust
pub fn compile_unit(&self, source: &str, ctx: &CompileContext, strategy: ModuleStrategy,
    compile_stack: &mut Vec<ModuleFullPath>) -> Result<CompileUnitResult, CranelispError>
```

Top-level callers pass `&mut Vec::new()`. Recursive calls pass through. Parallel calls get clones.

### 1.5 CompilationSession Field Changes

```rust
pub struct CompilationSession {
    // --- Read-only after construction ---
    pub tc: TypeChecker,                           // Internal RwLocks
    pub expander: CraneliftExpander,               // &self for expand, RwLock internal
    pub lib_dirs: Vec<PathBuf>,
    pub project_root: PathBuf,
    pub interactive: bool,
    pub shared_isa: Option<Arc<dyn TargetIsa>>,

    // --- Shared mutable ---
    pub module_deps: Mutex<ModuleDependencyGraph>,
    pub scheduling_registry: Mutex<SchedulingRegistry>,
    pub platform_symbols: RwLock<Vec<(String, *const u8)>>,
    pub loaded_platforms: Mutex<Vec<LoadedPlatform>>,

    // --- Worker state ---
    pub inmem_worker: Mutex<InMemWorkerState>,
    pub object_worker: Mutex<ObjectWorkerState>,

    // --- Codegen dispatch ---
    pub inmem_queue: Mutex<Vec<CodegenItem>>,
    pub object_queue: Mutex<Vec<CodegenItem>>,
    pub codegen_mode: CodegenMode,

    // REMOVED: compile_stack (now parameter)
}
```

## Part 2: N-Core Codegen Dispatch

Delete the coordinator+channel pattern (`spawn_codegen_worker`, `CodegenWorkerMsg`, batch accumulation). Replace with a shared concurrent queue and a worker pool — a classic producer-consumer.

### 2.0 CodegenItem Enum

`CodegenItem` has two variants — one for freshly typechecked source, one for cached `.o` files:

```rust
enum CodegenItem {
    FromSource {
        module: ModuleFullPath,
        program: Vec<TopLevel>,
        check_result: CheckResult,
        module_structure: ModuleStructure,
        source: String,
    },
    FromCache {
        module: ModuleFullPath,
        object_path: PathBuf,
        got_slot_map: HashMap<Symbol, usize>,
    },
}
```

`FromSource` owns all data from stages 1-5. Workers JIT-compile the program and write GOT slots.

`FromCache` carries the path to a cached `.o` file and the GOT slot mapping (from `.meta.json`). Workers load the `.o` via `Linker`, write GOT slots atomically. The `Linker` instance is pushed to `jit_collector` alongside `Jit` instances — both keep backing memory alive for the session's lifetime.

This replaces the previous design where `try_cache_hit_load` inside `compile_unit` would create a `Linker` and store it in `inmem_worker.cache_linkers`. Cache-hit loading in `compile_unit` now only restores `.meta.json` into the typechecker (symbols, types, dep edges) and enqueues a `FromCache` item. The `.o` loading and JIT linking happen on the worker pool, consistent with invariant 2 ("no codegen in `compile_unit`").

### 2.1 Shared Concurrent Queue

Replace `CodegenMode::Async` (mpsc channel + coordinator thread) with a shared queue:

```rust
struct CodegenQueue {
    items: Mutex<VecDeque<CodegenItem>>,
    condvar: Condvar,
    /// Set to true when no more items will be enqueued (flush/shutdown).
    done: AtomicBool,
    /// Count of items currently being compiled by workers.
    in_flight: AtomicUsize,
    /// Signalled when in_flight drops to 0 and queue is empty.
    drain_complete: Condvar,
}
```

`Arc<CodegenQueue>` is shared between producers (`compile_unit` callers) and consumers (worker threads). `Mutex<VecDeque>` is the simplest correct choice — contention is low because producers push infrequently (once per module) and consumers hold the lock only for the duration of a pop. If profiling shows lock contention, swap to `crossbeam::deque::Injector` later.

### 2.2 Worker Pool

`spawn_hot_inmem_codegen()` spawns N worker threads (N = `available_parallelism`, capped at a reasonable maximum like 8). Each thread runs:

```rust
fn inmem_worker_loop(queue: Arc<CodegenQueue>, shared_isa: Arc<dyn TargetIsa>,
                     jit_collector: Arc<Mutex<Vec<JitOrLinker>>>) {
    loop {
        let item = {
            let mut q = queue.items.lock().unwrap();
            loop {
                if let Some(item) = q.pop_front() {
                    queue.in_flight.fetch_add(1, Ordering::SeqCst);
                    break item;
                }
                if queue.done.load(Ordering::SeqCst) {
                    return; // No more work, exit thread.
                }
                q = queue.condvar.wait(q).unwrap();
            }
        };

        // Compile or load: thread-local, no shared mutable state.
        match item {
            CodegenItem::FromSource { .. } => {
                let mut jit = Jit::new_with_isa(shared_isa.clone());
                codegen_inmem(&mut jit, &item);  // JIT compile, write GOT slots atomically.
                jit_collector.lock().unwrap().push(JitOrLinker::Jit(jit));
            }
            CodegenItem::FromCache { object_path, got_slot_map, .. } => {
                let linker = load_cached_object(&object_path, &got_slot_map);
                jit_collector.lock().unwrap().push(JitOrLinker::Linker(linker));
            }
        }

        if queue.in_flight.fetch_sub(1, Ordering::SeqCst) == 1 {
            queue.drain_complete.notify_all();
        }
    }
}
```

`spawn_nice_object_codegen()` is the same pattern but at nice (low) priority and compiling to `.o` files instead of JIT. The object queue is a separate `Arc<CodegenQueue>`.

### 2.3 `enqueue_codegen` (replaces `send_codegen`)

```rust
pub fn enqueue_codegen(&self, item: CodegenItem, behaviour: CodegenBehaviour) {
    match behaviour {
        InMemoryAndObject => {
            self.inmem_queue.push(item.clone());
            self.object_queue.push(item);
        }
        ObjectOnly => {
            self.object_queue.push(item);
        }
    }
}

impl CodegenQueue {
    fn push(&self, item: CodegenItem) {
        self.items.lock().unwrap().push_back(item);
        self.condvar.notify_one(); // Wake one parked worker.
    }
}
```

Just pushes to the queue and wakes a parked worker. No channel send, no coordinator, no message types. Non-blocking from the caller's perspective.

### 2.4 `hot_flush_in_mem_queue` as Barrier

```rust
pub fn hot_flush_in_mem_queue(&self) {
    self.inmem_queue.done.store(true, Ordering::SeqCst);
    self.inmem_queue.condvar.notify_all(); // Wake all parked workers.

    // Wait until queue is empty AND in_flight == 0.
    let q = self.inmem_queue.items.lock().unwrap();
    let _guard = self.inmem_queue.drain_complete.wait_while(q, |q| {
        !q.is_empty() || self.inmem_queue.in_flight.load(Ordering::SeqCst) > 0
    }).unwrap();

    // Reset for next batch (REPL enters compile_unit again after flush).
    self.inmem_queue.done.store(false, Ordering::SeqCst);
}
```

This is a barrier, not a dispatcher. It signals "no more items coming", wakes any sleeping workers, and blocks until the queue is fully drained. Workers are already running — flush does not assign work.

`hot_flush_object_queue` is identical but targets the object queue and promotes remaining work to full priority (the object workers' priority flag is flipped before waking them).

### 2.5 `CodegenMode::Sync` for Tests

Tests bypass the queue entirely. `enqueue_codegen` buffers items in a local `Vec<CodegenItem>`. `hot_flush_in_mem_queue` processes the buffer synchronously on the calling thread. No threads spawned, no queue, no condvar. Unchanged from current behavior:

```rust
pub enum CodegenMode {
    Sync {
        buffer: Vec<CodegenItem>,
    },
    Async {
        inmem_queue: Arc<CodegenQueue>,
        object_queue: Arc<CodegenQueue>,
        inmem_workers: Vec<JoinHandle<()>>,
        object_workers: Vec<JoinHandle<()>>,
        jit_collector: Arc<Mutex<Vec<JitOrLinker>>>,
    },
}
```

### 2.6 Jit and Linker Lifetime

Workers create thread-local `Jit` or `Linker` instances depending on the `CodegenItem` variant. After compiling/loading and writing GOT slots atomically, the instance is pushed to `jit_collector: Arc<Mutex<Vec<JitOrLinker>>>`. Both `Jit` (from `FromSource`) and `Linker` (from `FromCache`) own backing memory that holds compiled code — the collector keeps them alive for the session's lifetime. On session drop, the collector is drained.

```rust
enum JitOrLinker {
    Jit(Jit),
    Linker(Linker),
}
```

This replaces the previous `cache_linkers: Vec<Linker>` field on `InMemWorkerState`. Cache-hit linkers are no longer created inside `compile_unit` — they are created by workers, owned by the collector.

### 2.7 Interaction with Parallel `compile_unit`

When parallel `compile_unit` calls run (from `load_dependencies` for independent cache-miss modules), each thread pushes `CodegenItem`s to the same shared `inmem_queue` and `object_queue`. Workers are already draining. No coordination needed — `CodegenQueue::push` is safe for concurrent producers (`Mutex<VecDeque>` serializes pushes). The queue handles fan-in from multiple producers and fan-out to multiple consumers.

### 2.8 Deletion List

Remove from `session.rs`:
- `CodegenWorkerMsg` enum (Codegen/Flush/Shutdown variants)
- `spawn_codegen_worker` function
- `drain_on_error` function
- `mpsc` channel usage for codegen
- Batch accumulation logic
- `cache_linkers: Vec<Linker>` from `InMemWorkerState` (moved to `jit_collector` as `JitOrLinker::Linker`)

## Part 3: Wave Structure

### Wave 0: North-star main.rs

0. Rewrite `src/main.rs` to match §2.2 verbatim, with `todo!()` for unimplemented methods
0. Rename `CompilationSession` → `CompilerSession` (or alias)
0. Verify `cargo build` succeeds (stubs compile, `todo!()` bodies are dead code in test paths)

**Acceptance**: `cargo test` passes. `main.rs` matches the design doc structurally. All unimplemented paths have `todo!()`.

### Wave 1: check() becomes &self

1. Remove `state: CheckState` field from TypeChecker
2. `check()` creates local `CheckState`, passes `cs: &mut CheckState` to all internal methods
3. `set_current_module` → `ensure_module_exists` + `CheckState::current_module`
4. REPL additive: reconstruct overloads from symbol table
5. `check()` signature: `&mut self` → `&self`

**Acceptance**: `cargo test` passes. `check()` takes `&self`. REPL additive works.

### Wave 2: compile_unit becomes &self

6. `tc.modules` → `RwLock<HashMap<..., Arc<RwLock<SymbolTable>>>>`
7. `CompilationSession` fields → Mutex/RwLock per §1.5
8. `compile_stack` → parameter
9. `compile_unit` → `&self`

**Acceptance**: `cargo test` passes. `compile_unit` takes `&self`.

### Wave 3: Producer-consumer codegen

10. Implement `CodegenQueue` (§2.1)
11. Replace `CodegenMode::Async` channel pattern with shared queue + worker pool (§2.2, §2.5)
12. `send_codegen` → `enqueue_codegen` (§2.3)
13. `hot_flush_in_mem_queue` / `hot_flush_object_queue` as barriers (§2.4)
14. Delete coordinator infrastructure (§2.8)
15. Parallel fork in `load_dependencies` for independent cache-miss deps (§2.7)
16. Implement `pause_watcher_codegen()` / `resume_watcher_codegen()` for GOT stability during REPL eval

**Acceptance**: `cargo test` passes. Multi-module compilation uses parallel codegen. `--run`, `--link`, REPL all work. Watcher enqueue exclusion prevents GOT mutation during REPL evaluation.

### Wave 4: Dissolve ReplSession

17. Move `process_commands` from `ReplSession` to `CompilerSession`
18. Move file watcher from `ReplSession` to `CompilerSession`
19. Implement `trampoline(&ctx)` — verify main, execute, IO trampoline
20. Implement `link(&ctx)` — link mode logic as a method
21. Implement `pretty_print_form(form)`
22. Fill in remaining `todo!()` stubs from Wave 0
23. Delete `ReplSession` wrapper

**Acceptance**: `cargo test` passes. `ReplSession` is deleted. All modes (REPL, `--run`, `--link`) work through `CompilerSession` methods. `main.rs` has no `todo!()` stubs for implemented features.

### Wave 5: Verification + Cleanup

24. Tests for parallel compile_unit, concurrent queue producers, lock contention
25. Performance measurement: stdlib compile time before vs after
26. REPL, --run, --link verification
27. Cleanup dead code

## Risk Analysis

**Highest risk**: TypeChecker RwLock conversion (Wave 2) — pervasive access pattern changes. Mitigated by compiler catching all broken accesses.

**Medium risk**: Deadlock in nested module loading. Mitigated by brief lock holds (never across compile_unit calls) and non-blocking try_lock.

**Low risk**: Producer-consumer codegen correctness. `Mutex<VecDeque>` is trivially correct. Atomic GOT writes are already proven. `Jit` instances are thread-local during compilation and collected after.
