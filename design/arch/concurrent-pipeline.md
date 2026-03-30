# Concurrent Pipeline: Scheduler-Driven Compilation

## 1. Overview

The compiler uses a central `CompileScheduler` to coordinate parallel typechecking and codegen across modules. The scheduler tracks per-module and per-symbol state, manages two worker pools (priority and nice), and handles the interaction between macro expansion (which requires codegen) and typechecking (which normally defers codegen).

The scheduler is a coordination structure — it does not own compilation data (ASTs, CheckResults, code pointers). Workers read and write compilation data via the session's module tables. The scheduler tells workers **what** to work on and **when**.

### 1.1 Design Drivers

Four constraints shape the design:

1. **Macro expansion requires codegen.** A `defmacro` body is a compiled function. If it calls helper functions (same-module or imported), those must be codegenned and callable before the macro can be compiled. This prevents a clean "typecheck everything, then codegen everything" separation.

2. **The spec requires sequential form processing.** Within a module, forms are processed in source order (spec §9.12). A `defmacro` is compiled and registered when encountered. Macro bodies may call any function defined before the macro. This is normative — the pipeline cannot reorder forms within a module.

3. **Parallelism is inter-module.** Independent modules (no import edges between them) can be typechecked and codegenned concurrently. The dependency graph is a DAG. Parallelism within a single module's pipeline is not possible due to constraint 2.

4. **Codegen has two targets with different urgency.** In-memory codegen (JIT) produces callable code needed for execution and macro expansion. Object codegen (.o + .meta.json) produces cached artifacts for future sessions. Both may be required for a single symbol (`InMemoryAndObject`), or only the object form (`ObjectOnly` for `--link`). Macro-dependency symbols always need in-memory codegen regardless of `CodegenBehaviour` — you cannot expand macros without callable code.

### 1.2 Relationship to pipeline-v3.md

This design refines the concurrency model sketched in pipeline-v3.md §3.4.3 and §6. The key departures:

- **Per-symbol codegen granularity** instead of per-module `CodegenItem`. Macro expansion can block mid-module, requiring codegen of individual symbols before typechecking can continue.
- **Priority codegen queue** replaces the simple producer-consumer model. Symbols needed for macro expansion are expedited at foreground priority; everything else drains at background priority.
- **Module pool scheduling** replaces the fork/join model for parallel dependency typechecking. Modules move between pools as dependencies are satisfied, rather than a single parallel level per DAG layer.

## 2. Module Lifecycle

Each module is in exactly one pool at any time:

```
  register_module
         │
         ▼
  ┌────────────────┐ take_typecheck_work ┌──────────────────┐
  │ TypecheckFirst │────────────────────▶│ TypecheckWorking │
  │  (or           │                     └──┬────────────┬──┘
  │ TypecheckNext) │◀────────┐              │            │
  └────────────────┘         │   block      │            │ notify_typecheck_done
         ▲                   │              ▼            │
         │         ┌─────────┴────────┐                  │
         └─────────│ TypecheckBlocked │                  │
           unblock └──────────────────┘                  │
                         │                               │
                         │ dep failed                    │
  register_module_cached │                               │
         │               │    ┌──────────────────────────┘
         │               │    │
         ▼               │    ▼
  ┌───────────────┐  all │ codegen   ┌──────────┐
  │ TypecheckDone │──────┼─────────▶│ Complete │
  └───────────────┘      │   done   └──────────┘
         │               │
         │ error         │
         ▼               ▼
      ┌────────────────────┐
      │       Failed       │
      └────────────────────┘

  While in TypecheckDone, up to three concurrent activities:
    1. Priority codegen workers — JIT macro-dep symbols (from priority queue)
    2. Background inmem workers — JIT remaining symbols (InMemoryAndObject only)
       (for cached modules: load .o via Linker instead of JIT-compiling)
    3. Background object workers — compile all symbols to .o files
       (for cached modules: already done, skip)
```

| Pool | Meaning | Who moves modules here |
|------|---------|----------------------|
| **TypecheckFirst** | Ready for a typecheck worker; known to be delaying another module | `register_module` (if delays known), unblock path (if module still has waiters) |
| **TypecheckNext** | Ready for a typecheck worker; not known to be delaying | `register_module` (default), unblock path (if no remaining waiters) |
| **TypecheckWorking** | Assigned to a typecheck worker | `take_typecheck_work` |
| **TypecheckBlocked** | Waiting for a symbol to be typechecked or codegenned | `block_for_macro_codegen`, `block_for_typecheck` |
| **TypecheckDone** | Typecheck complete; codegen in progress (up to 3 concurrent activities) | `notify_typecheck_done` |
| **Failed** | Error during typecheck or codegen, or dependency failed | `notify_module_failed`, cascade from dependency failure |
| **Complete** | All codegen (inmem + object) done | Last codegen notification (when all expected work is finished) |

### 2.1 TypecheckFirst vs TypecheckNext

TypecheckFirst and TypecheckNext are both "ready" pools. The distinction is priority: TypecheckFirst contains modules that are known to be blocking other modules' progress. Typecheck workers drain TypecheckFirst before TypecheckNext.

A module enters TypecheckFirst when:
- It is registered with `delays_other = true` (known from the dependency graph — another module imports from it).
- It is unblocked and still has entries in its waited-for map (other modules are actively waiting on it).

A module enters TypecheckNext when:
- It is registered with `delays_other = false` (leaf module, no dependents yet known).
- It is unblocked and has no remaining waiters.

### 2.2 TypecheckDone

TypecheckDone is a single pool where up to three kinds of codegen work happen concurrently on the same module:

1. **Priority JIT codegen.** If another module's typecheck is blocked on a macro that calls a function in this module, that symbol is in the priority codegen queue. Priority workers compile it and write the code pointer to the GOT. This work is driven by the priority queue, not the module's pool — the module just needs to be in TypecheckDone (or later) for its symbols to be eligible.

2. **Background JIT codegen.** For `InMemoryAndObject` mode: all remaining symbols (not already compiled by the priority path) are JIT-compiled by background inmem workers. For `ObjectOnly` mode: no background JIT work — the only in-memory compilation was whatever the priority path demanded during typechecking.

3. **Background object codegen.** All symbols are compiled to relocatable `.o` files by background object workers. This runs at nice priority regardless of mode.

A module moves from TypecheckDone to Complete when all codegen work is finished. The module is Complete when:
- **InMemoryAndObject**: `inmem_done` AND `object_done`
- **ObjectOnly**: `object_done` (no inmem requirement — priority-path symbols are a subset, not tracked for completion)

### 2.3 Failed

A module enters Failed when:
- A **parse error** occurs during `register_module` (source couldn't be parsed).
- A **type error** occurs during form processing (worker calls `notify_module_failed`).
- A **macro expansion error** occurs (runtime error in macro function, or no matching clause).
- A **codegen error** occurs (JIT compilation failure).
- A **dependency fails** — a module in TypecheckBlocked was waiting on a symbol from a module that moved to Failed. The blocked module is cascade-failed with a dependency-failure error.

**Cascade**: when a module moves to Failed, the scheduler walks its waiter map. Any module waiting on a symbol from this module (for typecheck or codegen) is also moved to Failed with a "dependency failed" error referencing the original module's error. This cascades transitively — a chain of blocked modules all fail together.

**Error retrieval**: `wait_inmem_complete` and `wait_object_complete` return `Result`. If any module is Failed, the first error is returned. The REPL's `eval` uses this to display the error and roll back TC state. Batch mode's `main` prints the error and exits.

**Recovery (REPL only)**: after a Failed eval, the TC snapshot/restore mechanism rolls back the typechecker. The Failed module state is cleared. The user can re-submit corrected input. Failed modules from file watcher changes are re-registered when the file changes again — the next save triggers a fresh attempt.

## 3. Per-Module State

```rust
enum ModulePool {
    TypecheckFirst,
    TypecheckNext,
    TypecheckWorking,
    TypecheckBlocked,
    TypecheckDone,
    Failed,
    Complete,
}

struct ModuleState {
    pool: ModulePool,

    /// Symbols in this module that other modules are waiting on.
    /// Key: symbol name. Value: list of waiters (module + what they need).
    /// When a symbol is typechecked or codegenned and has waiters,
    /// those waiters are evaluated for unblocking.
    waiters: HashMap<Symbol, Vec<Waiter>>,

    /// Symbols currently being JIT-compiled by a worker.
    /// Prevents two workers claiming the same symbol.
    jit_reserved: HashSet<Symbol>,

    /// All in-memory codegen complete for this module.
    /// Set when a worker scans for unreserved, un-codegenned symbols
    /// and finds none. Not applicable for ObjectOnly mode.
    inmem_done: bool,

    /// The module's .o file has been written (or already existed
    /// from a cache hit). Object codegen is per-module, not
    /// per-symbol — the entire module is compiled to one .o.
    object_done: bool,

    /// Error that caused this module to fail, if any.
    /// Set when the module moves to Failed.
    error: Option<CranelispError>,
}

// The scheduler tracks coordination state only: pools, waiters,
// reservations, done flags. Symbol-level compilation state
// (which symbols are typechecked, which have code pointers) lives
// on the session's module tables (concurrent maps). Workers query
// the session for symbol state; the scheduler never duplicates it.

struct Waiter {
    module: ModuleFullPath,
    need: WaitKind,
}

enum WaitKind {
    /// Waiter's typecheck needs this symbol's type information.
    /// Satisfied when the symbol is typechecked.
    Typecheck,
    /// Waiter's macro expansion needs this symbol compiled and callable.
    /// Satisfied when the symbol's codegen is complete.
    Codegen,
}
```

## 4. Priority Codegen Queue

The priority codegen queue is an ordered list of symbols that need expedited codegen for macro expansion to proceed. It is separate from the module pools — a symbol can be in the priority queue regardless of its module's pool state.

```rust
struct PriorityEntry {
    module: ModuleFullPath,
    symbol: Symbol,
    status: PriorityStatus,

    /// Modules to unblock when this symbol and all its dependencies
    /// are callable. Typically only the macro function itself (the
    /// last entry in a chain) has entries here, but multiple modules
    /// may wait on the same symbol (§4.2).
    unblocks: Vec<ModuleFullPath>,

    /// Symbols this entry calls (forward edges). Populated from
    /// the call graph. Entries are removed as dependencies complete
    /// their codegen. When empty, this symbol is callable.
    dependencies: HashSet<(ModuleFullPath, Symbol)>,

    /// Symbols that call THIS entry (reverse edges). When this
    /// entry becomes callable (dependencies empty), it is removed
    /// from each dependent's dependencies set.
    dependents: Vec<(ModuleFullPath, Symbol)>,
}

enum PriorityStatus {
    /// Codegen has not occurred. Dependencies are also on the queue
    /// (probably ahead due to breadth-first enqueuing, but not
    /// necessarily). A worker claims this entry and compiles it
    /// unconditionally.
    Ready,
    /// A worker is compiling this symbol. Other workers skip it.
    Working,
    /// Codegen complete. Other workers skip it. The entry stays
    /// until all its dependents are also callable. When the last
    /// dependent of a chain reaches Waiting, the chain's `unblocks`
    /// modules move from TypecheckBlocked to TypecheckFirst/
    /// TypecheckNext, and all resolved Waiting entries are removed.
    Waiting,
}
```

### 4.1 Queue Ordering

New entries are pushed to the **front** of the queue. When `block_for_macro_codegen` is called, the caller walks the macro's `ModuleEntry.callees` (a `Vec<FQSymbol>` populated during typecheck — see Decision 21) breadth-first via `tc.symbol_table(module).get(name)`, pushing each uncompiled dependency to the front. This naturally produces a topo-sort: leaf dependencies end up at the front, the macro function itself ends up deepest.

Priority workers scan from the front and claim the first Ready entry. Dependencies tend to compile before their consumers. If a dependency is further back in the queue (because it was added by an earlier request), a worker eventually reaches it — the Waiting mechanism handles the resolution. Correctness does not depend on ordering.

### 4.2 Duplicate Handling

When pushing a symbol to the priority queue:
- If the symbol is already in `inmem_codegenned` for its module — skip (already done).
- If the symbol already has a PriorityEntry (any status) — skip, but add the requesting module to `unblocks` if not already present.

This handles the case where two modules block on macros that share a common dependency (e.g., both call `core.syntax/sfold`).

### 4.3 Completion and Unblocking

When a priority entry's codegen completes (Working →):

1. The symbol is marked available in `inmem_codegenned` for its module. (This does not imply the symbol's dependencies are available — it is not yet callable.)

2. If the entry still has entries in its `dependencies` list, status becomes **Waiting**. The entry stays in the queue until its dependencies are resolved by other workers.

3. If the entry has no entries in its `dependencies` list (all dependencies are callable, so this symbol is now callable too), **resolve** the entry:
   - Unblock the modules in this entry's `unblocks` (move from TypecheckBlocked to TypecheckFirst/TypecheckNext).
   - Walk the `dependents` list: remove this symbol from each dependent's `dependencies`.
   - If that removed the last dependency from a dependent AND that dependent's status is Waiting: **resolve** that dependent (recurse).
   - Remove this entry from the queue.

The recursion terminates because the call graph is acyclic — every chain has finite depth.

When `block_for_macro_codegen` pushes entries, it wires the edges: each entry's `dependents` list includes the symbols that call it, and each entry's `dependencies` list includes the symbols it calls. The last entry in the chain (the macro function itself) carries `unblocks` referencing the waiting module.

### 4.4 CodegenBehaviour Interaction

The `CodegenBehaviour` is session-wide (set by the CLI action) and determines which codegen targets all modules need:

| Behaviour | In-memory codegen | Object codegen | Typical use |
|-----------|------------------|----------------|-------------|
| `InMemoryAndObject` | All symbols | All symbols | `--run`, REPL |
| `ObjectOnly` | Macro-dep symbols only | All symbols | `--link` |

**Priority codegen is always in-memory.** The priority queue exists to produce callable code for macro expansion. The symbols it compiles are always JIT'd, regardless of `CodegenBehaviour`. In `ObjectOnly` mode, these are the *only* symbols that get in-memory codegen.

**Background in-memory codegen respects the behaviour.** For `InMemoryAndObject`, background workers JIT all remaining symbols after typecheck. For `ObjectOnly`, there is no background in-memory work — the only in-memory compilation is what the priority path demanded.

**Object codegen runs for dirty modules only.** A module loaded from a cache hit already has a valid `.o` on disk — no object codegen needed. Object codegen runs only for modules compiled from source (cache miss) or cache-hit modules that have been dirtied by additive changes (e.g., REPL definitions added to a cached module). Object codegen runs at the lowest priority and never blocks anything.

**Behaviour determines which activities run in TypecheckDone:**

- `InMemoryAndObject`: all three activities (blocking JIT, JIT codegen, object write). Complete when `inmem_done` and `object_done`.
- `ObjectOnly`: blocking JIT + object write only (no JIT codegen). Complete when `object_done`. Inmem codegen is not tracked for completion — the only in-memory compilation is what the priority path demanded for macros.

### 4.5 Cache-Hit Codegen Fast Path

All inmem codegen workers (priority and background) check `inmem_codegenned` before starting work on a symbol. If another worker has already completed it, the symbol is skipped.

For cache-hit modules (registered via `register_module_cached`), the `.o` file is already on disk. When any inmem worker needs to JIT a symbol from a cache-hit module, it loads the entire `.o` via Linker — this produces code pointers for ALL symbols in the module at once. The worker marks all loaded symbols in `inmem_codegenned` via `notify_inmem_codegen_batch_complete` (§8.3). Subsequent workers claiming other symbols from the same module find them already in `inmem_codegenned` and skip.

Object codegen workers skip cache-hit modules entirely — `object_done` is set at registration time (§8.1). If a cache-hit module is later dirtied by additive changes (REPL), `object_done` is cleared and object workers pick up the module.

## 5. Worker Pools

Two worker pools:

| Pool | Thread priority | Work selection (in priority order) |
|------|----------------|-----------------------------------|
| **Priority workers** | Normal | 1. TypecheckFirst modules  2. Priority codegen queue  3. TypecheckNext modules  4. Background JIT codegen |
| **Nice workers** | Nice | Object codegen (`.o` + `.meta.json`) |

### 5.1 Priority Workers

Priority workers select work using a priority ladder. On each iteration, they try each level in order and take the first available work:

1. **TypecheckFirst module.** Claim a module, process forms in source order (§5.2). Highest priority — these modules are blocking other modules.
2. **Priority codegen.** Claim a Ready entry from the priority codegen queue. JIT-compile the symbol, register the code pointer, call `notify_priority_codegen_complete` (§4.3).
3. **TypecheckNext module.** Same as TypecheckFirst but lower priority — these modules aren't known to be blocking anything.
4. **JIT codegen.** The scheduler takes the first `typecheck_done` module and queries the session for a typechecked symbol without a code pointer that isn't in `jit_reserved`. Reserves it and returns it to the worker. The worker JIT-compiles, registers the code pointer on the session, and calls `notify_inmem_codegen_complete(no_remaining)`. If no un-codegenned symbols remain, the scheduler sets `inmem_done`. If the completion condition is met (§2.2), the module moves to Complete.

If no work is available at any level, the worker parks on a condvar until woken.

This means when a module blocks on a macro, the same worker that was typechecking it can immediately fall through to priority codegen — compiling the very symbols needed to unblock it. No context switch between pools, no idle workers waiting for a different pool to do work.

### 5.2 Typecheck Form Processing

When a priority worker claims a typecheck module (from level 1 or 3), it processes forms in source order:

1. **Expand** the form. If it is a macro call:
   - Look up the macro in the module table.
   - If the macro's function pointer and its call-graph dependencies are all compiled: expand (call the function pointer with marshalled sexp args), continue with the expanded sexp.
   - If not: walk the macro's `ModuleEntry.callees` (a `Vec<FQSymbol>`, populated during typecheck per Decision 21) to collect transitive uncompiled deps via `tc.symbol_table(module).get(name)`, then call `block_for_macro_codegen`. The worker releases the module (moves to TypecheckBlocked) and returns to the priority ladder. When dependencies are compiled, the module unblocks and a worker resumes from this form.
2. **Build AST** from the (possibly expanded) sexp.
3. **Typecheck** the form. Register the symbol's type information.
4. Call `notify_symbol_typechecked` — this may unblock other modules.
5. If the form is a **defmacro**: register the macro in the module table (clause info + AST). No compilation — deferred until first use (step 1).
6. After all forms: call `notify_typecheck_done`.

### 5.3 Nice Workers

Nice workers handle object codegen exclusively:

1. Claim a TypecheckDone module where `object_done` is false.
2. Compile all the module's symbols to a single relocatable object (Cranelift → `.o`). Write `.meta.json`.
3. Call `notify_object_codegen_complete` which sets `object_done`.
4. If the completion condition is met (§2.2), the module moves to Complete.

Nice workers run at low OS thread priority — they must not compete with priority workers for CPU cores. Object codegen is pure background work that prepares cache artifacts for future sessions.

### 5.4 Priority Escalation (Hot Flush)

At session shutdown (or before `--link` invokes the system linker), remaining object codegen joins the critical path. Nice workers are promoted to normal priority and the session blocks until all TypecheckDone modules reach Complete. This matches the `hot_flush_object_queue` barrier from pipeline-v3.md §6.2.

## 6. `CompileScheduler` Interface

```rust
pub struct CompileScheduler {
    state: Mutex<SchedulerState>,
    /// Wakes priority workers when any priority-ladder work becomes available
    /// (module enters TypecheckFirst/TypecheckNext, priority queue item
    /// becomes Ready, or module enters TypecheckDone with JIT work).
    priority_work_available: Condvar,
    /// Wakes nice workers when a module enters TypecheckDone with object_done == false.
    object_work_available: Condvar,
    /// Wakes callers of wait_inmem_complete / wait_object_complete
    /// when a module reaches the waited-for condition (or Failed).
    completion: Condvar,
}

struct SchedulerState {
    modules: HashMap<ModuleFullPath, ModuleState>,

    // --- Priority worker ladder (§5.1) ---
    // Each level is a work list. Workers check in order.

    /// Level 1: modules known to be delaying others.
    typecheck_first: VecDeque<ModuleFullPath>,
    /// Level 2: priority codegen queue (§4).
    priority_queue: VecDeque<PriorityEntry>,
    /// Level 3: modules ready but not known to be delaying.
    typecheck_next: VecDeque<ModuleFullPath>,
    // --- Level 4 and nice worker list share the same source ---

    /// Modules in TypecheckDone. Used by both:
    /// - Priority workers (level 4): scan for un-reserved, un-codegenned
    ///   symbols to JIT. When none found, set inmem_done.
    /// - Nice workers: compile module to .o when object_done == false.
    typecheck_done: VecDeque<ModuleFullPath>,

    shutdown: bool,
}
```

### 6.1 Module Registration

```rust
impl CompileScheduler {
    /// Add a module to the scheduler.
    /// Enters First if `delays_other` is true, otherwise Next.
    /// Wakes a priority worker.
    pub fn register_module(
        &self,
        module: ModuleFullPath,
        delays_other: bool,
    );
}
```

Dependency edges are implicit in the TypeChecker's module import specs — no explicit `register_edge` needed. The file watcher derives reverse edges from the TypeChecker when it needs to cascade.
```

### 6.2 Priority Worker Interface

```rust
/// Work item returned by take_priority_work.
pub enum PriorityWork {
    /// Typecheck a module (from TypecheckFirst or TypecheckNext).
    Typecheck(ModuleFullPath),
    /// JIT-compile a symbol needed for macro expansion (from priority queue).
    /// Blocking because a module's typecheck is waiting on this.
    BlockingJitCodegen(ModuleFullPath, Symbol),
    /// JIT-compile a symbol from a TypecheckDone module.
    JitCodegen(ModuleFullPath, Symbol),
}

impl CompileScheduler {
    /// Block until work is available, then return the highest-priority
    /// item. Checks the work lists in order:
    ///   1. Pop from `typecheck_first` → Typecheck(module)
    ///   2. Scan `priority_queue` for first Ready entry → BlockingJitCodegen(module, symbol)
    ///   3. Pop from `typecheck_next` → Typecheck(module)
    ///   4. Scan first `typecheck_done` module (via session) for a
    ///      typechecked symbol without a code pointer and not in
    ///      `jit_reserved`. Reserve it → JitCodegen(module, symbol).
    ///      If no symbols found, set inmem_done on that module.
    /// If no work at any level, parks on `priority_work_available` condvar.
    /// Returns None on shutdown.
    pub fn take_priority_work(&self) -> Option<PriorityWork>;

    /// Report that a symbol in the working module has been typechecked.
    /// Checks the module's waiter map: if any module was waiting on
    /// this symbol for WaitKind::Typecheck, removes the waiter and
    /// evaluates whether to unblock the waiting module.
    pub fn notify_symbol_typechecked(
        &self,
        module: &ModuleFullPath,
        symbol: &Symbol,
    );

    /// Typechecking needs a symbol from another module that hasn't
    /// been typechecked yet. Moves the current module to TypecheckBlocked.
    /// Adds a WaitKind::Typecheck waiter on the target symbol.
    /// The worker should then call take_priority_work for new work.
    pub fn block_for_typecheck(
        &self,
        module: &ModuleFullPath,
        needed_module: &ModuleFullPath,
        needed_symbol: &Symbol,
    );

    /// Typechecking hit a macro expansion that needs codegenned symbols.
    /// Moves the current module to TypecheckBlocked.
    ///
    /// `needed` is the call graph of uncompiled symbols required for
    /// the macro expansion — the macro function and its transitive
    /// dependencies. The typecheck worker walks the call graph before
    /// calling this. Order is a hint (dependencies first via
    /// breadth-first walk), not a strict requirement.
    ///
    /// Each symbol is pushed to the front of the priority codegen
    /// queue (skipping symbols already queued or codegenned).
    /// Forward and reverse edges are wired between entries.
    /// The macro function entry carries `unblocks` for the waiting module.
    /// Wakes priority workers.
    pub fn block_for_macro_codegen(
        &self,
        module: &ModuleFullPath,
        needed: Vec<(ModuleFullPath, Symbol)>,
    );

    /// All forms in the module have been typechecked.
    /// Moves module from TypecheckWorking to TypecheckDone.
    /// Wakes priority workers (background JIT) and nice workers (object).
    pub fn notify_typecheck_done(
        &self,
        module: &ModuleFullPath,
    );

    /// A module has failed (parse, type, macro, or codegen error).
    /// Moves module to Failed. Stores the error. Cascades failure
    /// to any modules in TypecheckBlocked waiting on this module's
    /// symbols (§2.3). Wakes wait_inmem_complete / wait_object_complete
    /// callers so they can observe the failure.
    pub fn notify_module_failed(
        &self,
        module: &ModuleFullPath,
        error: CranelispError,
    );

    /// Priority codegen of a symbol is complete.
    /// Processes the entry per §4.3: adds to inmem_codegenned,
    /// resolves dependencies, cascades unblocks.
    pub fn notify_priority_codegen_complete(
        &self,
        module: &ModuleFullPath,
        symbol: &Symbol,
    );

    /// JIT codegen of a symbol is complete.
    /// Removes from jit_reserved. The worker has already registered
    /// the code pointer on the session.
    /// If no unreserved, un-codegenned symbols remain (worker reports),
    /// sets inmem_done. If inmem_done and object_done, moves module
    /// to Complete.
    pub fn notify_inmem_codegen_complete(
        &self,
        module: &ModuleFullPath,
        symbol: &Symbol,
        no_remaining: bool,
    );
}
```

### 6.3 Nice Worker Interface

```rust
impl CompileScheduler {
    /// Block until a TypecheckDone module with `object_done == false`
    /// is available. Returns the module path.
    /// Returns None on shutdown.
    pub fn take_object_codegen(&self) -> Option<ModuleFullPath>;

    /// Object codegen for a module is complete (.o written).
    /// Sets `object_done`. If the completion condition is met (§2.2),
    /// moves the module to Complete.
    pub fn notify_object_codegen_complete(
        &self,
        module: &ModuleFullPath,
    );
}
```

### 6.4 Worker Entry Points

Workers receive a reference to the session, which owns the scheduler. The scheduler is pure coordination — workers access compilation data through the session.

```rust
/// Priority worker loop. Runs on N threads at normal OS priority.
fn priority_worker(session: &CompilerSession) {
    loop {
        match session.scheduler.take_priority_work() {
            Some(Typecheck(module)) => {
                // session.tc for form processing + macro lookup
                // session.scheduler for notifications
            }
            Some(BlockingJitCodegen(module, symbol)) => {
                // session GOT, tc module tables for JIT
            }
            Some(JitCodegen(module, symbol)) => {
                // same as BlockingJitCodegen
            }
            None => break,
        }
    }
}

/// Nice worker loop. Runs on M threads at low OS priority.
fn nice_worker(session: &CompilerSession) {
    loop {
        match session.scheduler.take_object_codegen() {
            Some(module) => {
                // session for Cranelift → .o compilation
            }
            None => break,
        }
    }
}
```

### 6.5 Lifecycle

```rust
impl CompileScheduler {
    /// Create a new scheduler.
    pub fn new() -> Self;

    /// Signal all workers to shut down. Wakes all condvars.
    /// Workers will return None from their next take_* call.
    pub fn shutdown(&self);

    /// Block until all registered modules have inmem_done set.
    /// Returns Err with the first error if any module is Failed.
    /// Does not wait for object codegen.
    pub fn wait_inmem_complete(&self) -> Result<(), CranelispError>;

    /// Promote nice workers to normal priority, then block until
    /// all registered modules have object_done set.
    /// Returns Err with the first error if any module is Failed.
    pub fn wait_object_complete(&self) -> Result<(), CranelispError>;
}
```

## 7. Concurrency Properties

### 7.1 Deadlock Freedom

The system is deadlock-free because:

1. **The module dependency graph is a DAG.** Circular imports are rejected during dependency resolution (before scheduling begins). Therefore, no two modules can be mutually waiting on each other for typecheck.

2. **The call graph is acyclic for macro dependencies.** A macro can only call functions defined before it (spec §9.2.5, §9.3.4). Functions can only call functions from imported modules (DAG) or previously-defined same-module functions. No circular codegen waits.

3. **`take_*` methods use non-blocking try-claim semantics internally.** The Mutex is held only for state inspection and updates, never during compilation work. Workers release the lock before compiling.

4. **Every Blocked module waits on a symbol that will be produced by forward progress.** A typecheck waiter waits on a symbol that another worker will reach (form-by-form, no skipping). A codegen waiter waits on a priority queue entry that will be compiled once its (acyclic) deps are ready.

### 7.2 Progress Guarantee

At least one of the following is always true (until all modules are Complete):

- A priority worker is typechecking a module.
- A priority worker is compiling a priority codegen entry.
- A priority worker is JIT-compiling a background symbol.
- A nice worker is writing a `.o` file.
- A module in TypecheckFirst or TypecheckNext is available for a priority worker.

No global stall is possible because the DAG has at least one root (no incoming edges) and roots never block.

### 7.3 Lock Granularity

Two locking domains:

**Scheduler Mutex.** A single Mutex protects all scheduler coordination state (module pools, priority queue, symbol sets, done flags). Workers hold it briefly for O(1) operations during work selection and notifications. All compilation work happens outside the lock.

**Session concurrent maps.** The TypeChecker's per-module symbol tables are accessed concurrently by multiple workers: one worker writes its module's symbols while others read from it for import resolution and macro lookup. These use concurrent HashMaps (`DashMap` or equivalent) rather than a single lock:

- **TypeChecker module tables**: concurrent read (import resolution, macro lookup) + write (new symbols, new modules, macro registration). Per-shard locking means cross-module reads don't block same-module writes. Macros are stored as `ModuleEntry::Macro` in the same tables.

The scheduler prevents coarse conflicts (no two workers typecheck the same module, no JIT + typecheck overlap on the same module). The concurrent maps handle the remaining fine-grained cross-module access that the scheduler cannot partition.

## 8. Cache-Hit Loading

A cache hit means a module's `.o` and `.meta.json` files exist on disk and the source hasn't changed (hash match, plus all transitive dependency hashes match). Cache-hit modules skip typechecking — they enter the scheduler at TypecheckDone with type info already restored, and their in-memory codegen is satisfied by loading the cached `.o` via Linker rather than JIT-compiling from source.

### 8.1 Cache-Hit Registration

When a dependency is resolved and a valid cache exists:

1. **Restore type info.** Read `.meta.json`, restore the module's `SymbolTable`, type defs, trait registrations, and constructor mappings into the TypeChecker. This makes the module's symbols available for typechecking of downstream modules.

2. **Register as TypecheckDone.** Call `register_module_cached` on the scheduler. This:
   - Creates a `ModuleState` in the TypecheckDone pool.
   - Sets `object_done = true` (the `.o` already exists on disk).
   - `inmem_done` is false — code is not loaded into memory yet.
   - Fires waiter satisfaction checks for typecheck waiters — any module waiting on this module's type info is evaluated for unblocking.

3. **In-memory code loads on demand.** The cached `.o` is NOT loaded eagerly. Instead, when an inmem codegen worker (priority or background) claims a symbol from this module, it detects the cache hit and loads the `.o` via Linker rather than JIT-compiling. This is a worker-level optimization: the scheduler sees normal `notify_inmem_codegen_complete` / `notify_priority_codegen_complete` calls regardless of whether the worker JIT-compiled or loaded from cache.

```rust
impl CompileScheduler {
    /// Register a module loaded from cache.
    /// Enters TypecheckDone with type info available but in-memory
    /// code not yet loaded. Object codegen is pre-satisfied.
    /// Satisfies any pending typecheck waiters on this module's symbols.
    pub fn register_module_cached(
        &self,
        module: ModuleFullPath,
        symbols: HashSet<Symbol>,
    );
}
```

### 8.2 Cache-Hit and Macro Dependencies

When a downstream module's typecheck hits a macro that calls a function in a cached module, the priority codegen path fires as normal: the symbol is pushed to the priority queue, a priority worker claims it, and the worker loads the `.o` via Linker (fast) instead of JIT-compiling (slow). The scheduler sees a normal priority codegen completion. The downstream module unblocks.

This is the common fast path: the prelude and core stdlib are cached, their `.meta.json` is restored at startup, and when the first user module's macro needs a prelude function, the priority worker loads the prelude `.o` via Linker. Subsequent symbols from the same module reuse the already-loaded Linker (all symbols in one `.o` are loaded together).

### 8.3 Linker Granularity

A `.o` file contains all symbols for a module. When a worker loads a `.o` via Linker, it gets code pointers for ALL symbols in that module at once. The worker should mark all of them as `inmem_codegenned` in a single scheduler notification, not one by one. This means one Linker load can satisfy multiple priority queue entries and unblock multiple waiting modules simultaneously.

```rust
impl CompileScheduler {
    /// Batch-mark multiple symbols as inmem-codegenned.
    /// Used when a Linker load resolves all symbols in a cached .o at once.
    /// Evaluates unblock conditions for all affected waiters.
    pub fn notify_inmem_codegen_batch_complete(
        &self,
        module: &ModuleFullPath,
        symbols: &[Symbol],
    );
}
```

### 8.4 Cache Validity

Cache validity is checked during dependency resolution (§9), before the module enters the scheduler. The check is:

1. `.o` and `.meta.json` both exist.
2. Source hash matches the current file's hash.
3. All transitive dependency hashes match (a recompiled dependency invalidates its dependents).

If validity cannot be confirmed, the module falls back to a full recompile: it enters TypecheckFirst or TypecheckNext like any other source module. No partial cache restoration — if the cache is stale, the module is treated as if no cache exists.

Condition 3 interacts with scheduling order: a dependency that was itself recompiled (cache miss) changes its source hash, which invalidates downstream modules that depend on it. The dependency resolution phase checks validity and either registers the module via `register_module_cached` (cache hit) or `register_module` (cache miss, needs full pipeline).

## 9. Dependency Discovery

Dependencies are discovered lazily during form-by-form typechecking. There is no upfront graph walk. When a worker encounters an unresolved import, `mod` declaration, or qualified reference:

1. **Resolve** the module path to a source file via `lib_dirs`.
2. **Check cache** — if valid, restore type info via `register_module_cached` (enters TypecheckDone). If the needed symbols are immediately available, the current module continues without blocking.
3. **Cache miss** — parse the source, register via `register_module` (enters TypecheckFirst, since the current module is waiting).
4. **Dependency edge** is implicit — the module's import specs in the TypeChecker record it.
5. If the needed symbol is not yet available: **block** the current module via `block_for_typecheck`. The worker returns to the priority ladder.
6. When the needed symbol is typechecked, the original module unblocks.

Dependency edges are not explicitly stored in a separate graph. The TypeChecker's module import specs are the source of truth. The file watcher derives reverse edges from the TypeChecker when cascading recompilation.

## 10. Interaction with Existing Pipeline

### 10.1 CompilerSession Integration

The `CompileScheduler` is a field on `CompilerSession`:

```rust
pub struct CompilerSession {
    pub tc: TypeChecker,
    pub got: GotTable,
    pub scheduler: CompileScheduler,
    pub platform: Mutex<HashMap<FQSymbol, PlatformFunction>>,
    pub settings: Settings,
    pub project_root: PathBuf,
    pub shared_isa: Arc<dyn TargetIsa>,
    // ... see pipeline-v4.md §5.1 for full field list
}
```

Workers access the session for compilation data (TypeChecker for type state and macro lookup, GOT for code pointer registration) and the scheduler for coordination. Macro expansion is a free function — marshal sexp args, call the function pointer from `ModuleEntry::Macro`, unmarshal result.

### 10.2 Per-Symbol TypeCheck Results

The current typechecker produces a single `CheckResult` for a whole program. This design requires per-symbol typecheck output available incrementally — each symbol's method resolutions, expr_types, and constraints must be accessible as soon as that symbol is typechecked.

This is a required change to `cranelisp-typecheck`. The form-by-form processing loop calls `tc.check_form()` (or equivalent) and gets back the per-form contribution to the CheckResult. These accumulate into the module's full CheckResult, but individual results are available for codegen immediately.

### 10.3 Single-Threaded Fallback

For testing and simplicity, the scheduler supports a single-worker mode: one typecheck worker, one priority codegen worker (which may be the same thread), no background workers. This degenerates to the current sequential pipeline behaviour — forms processed in order, macro-dep codegen happens inline, remaining codegen happens after typecheck.

The interface is identical. Only the worker count changes.

## 11. Invariants

1. **A module is in exactly one pool at any time.**
2. **A symbol is typechecked at most once.** The typechecked_symbols set is append-only.
3. **A symbol is in-memory codegenned at most once.** Priority and background inmem paths both check `inmem_codegenned` before compiling.
4. **A module is object-codegenned at most once.** Background object workers check `object_done` before compiling. The `.o` is per-module, not per-symbol.
5. **The priority queue is ordered: leaves before dependents.** Workers compile from the front, ensuring dependencies are ready before their consumers.
6. **A Blocked module will eventually unblock.** The DAG guarantee means every waited-for symbol will be produced by a forward-progressing worker.
7. **Priority workers handle all latency-sensitive work.** Typechecking, priority codegen, and background JIT all run on the same pool at normal priority. The priority ladder ensures the most urgent work is done first.
8. **Object codegen never competes with priority work.** Nice workers run at low OS priority. They only escalate to normal at hot flush.
9. **The scheduler Mutex is never held during compilation.** Workers acquire the lock only for state transitions, never while typechecking or codegenning.
10. **Macro-dep symbols are always in-memory, regardless of `CodegenBehaviour`.** The priority codegen path produces JIT code. In `ObjectOnly` mode, these are the only symbols with in-memory code.
11. **Object codegen is per-module.** Every dirty module gets a single `.o` + `.meta.json` for caching. Cache-hit modules already have their `.o` on disk.
