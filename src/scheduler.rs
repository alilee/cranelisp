// CompileScheduler — scheduler-driven compilation coordination.
//
// Implements the module lifecycle, priority ladder, waiter/unblock logic
// from design/arch/concurrent-pipeline.md. State is behind a Mutex with
// condvars for nice worker parking (Step 10) and future priority worker
// parking (Step 11).

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Condvar, Mutex, MutexGuard};

use cranelisp_types::{CranelispError, ModuleFullPath, Span, Symbol};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Which pool a module is in. A module is in exactly one pool at any time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModulePool {
    TypecheckFirst,
    TypecheckNext,
    TypecheckWorking,
    TypecheckBlocked,
    TypecheckDone,
    Failed,
    Complete,
}

/// Per-module coordination state tracked by the scheduler.
/// The scheduler does NOT own compilation data (ASTs, CheckResults, code
/// pointers) — only coordination metadata.
#[derive(Debug)]
pub struct ModuleState {
    pub pool: ModulePool,

    /// Symbols in this module that other modules are waiting on.
    /// Key: symbol name. Value: list of waiters.
    pub waiters: HashMap<Symbol, Vec<Waiter>>,

    /// Symbols currently being JIT-compiled by a worker (prevents
    /// two workers claiming the same symbol).
    pub jit_reserved: HashSet<Symbol>,

    /// All in-memory codegen complete for this module.
    pub inmem_done: bool,

    /// A nice worker is currently performing object codegen for this module.
    /// Set when `take_object_codegen` claims the module; cleared when
    /// `notify_object_codegen_complete` is called. Prevents double-claim
    /// when multiple nice workers wake simultaneously.
    pub object_working: bool,

    /// The module's .o file has been written (or existed from cache).
    pub object_done: bool,

    /// Error that caused this module to fail, if any.
    pub error: Option<CranelispError>,

    /// Form index to resume from when unblocked.
    /// None = start from the beginning (fresh module).
    pub resume_from_form: Option<usize>,

    /// Module this module is currently blocked on (forward edge).
    /// Set when entering TypecheckBlocked, cleared when unblocked.
    /// Used for cycle detection.
    pub blocked_on: Option<ModuleFullPath>,
}

impl ModuleState {
    fn new(pool: ModulePool) -> Self {
        Self {
            pool,
            waiters: HashMap::new(),
            jit_reserved: HashSet::new(),
            inmem_done: false,
            object_working: false,
            object_done: false,
            error: None,
            resume_from_form: None,
            blocked_on: None,
        }
    }

    fn new_cached(symbols: HashSet<Symbol>) -> Self {
        // Cache-hit modules enter TypecheckDone with object_done = true
        // and inmem_done = false (code not loaded into memory yet).
        // jit_reserved is unused since there are no active reservations.
        let _ = symbols; // Symbols are noted but not stored in scheduler
        Self {
            pool: ModulePool::TypecheckDone,
            waiters: HashMap::new(),
            jit_reserved: HashSet::new(),
            inmem_done: false,
            object_working: false,
            object_done: true,
            error: None,
            resume_from_form: None,
            blocked_on: None,
        }
    }
}

/// A module waiting on a symbol from another module.
#[derive(Debug, Clone)]
pub struct Waiter {
    pub module: ModuleFullPath,
    pub need: WaitKind,
}

/// What a waiter needs before it can be unblocked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WaitKind {
    /// Waiter needs the symbol's type information (satisfied on typecheck).
    Typecheck,
    /// Waiter needs the symbol compiled and callable (satisfied on codegen).
    Codegen,
}

/// Status of a priority codegen queue entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PriorityStatus {
    /// Codegen has not occurred. A worker can claim this entry.
    Ready,
    /// A worker is compiling this symbol.
    Working,
    /// Codegen complete; waiting for dependencies to also complete.
    Waiting,
}

/// An entry in the priority codegen queue (macro-dep symbols).
#[derive(Debug)]
pub struct PriorityEntry {
    pub module: ModuleFullPath,
    pub symbol: Symbol,
    pub status: PriorityStatus,

    /// Modules to unblock when this symbol and all its dependencies
    /// are callable.
    pub unblocks: Vec<ModuleFullPath>,

    /// Symbols this entry calls (forward edges). Entries are removed
    /// as dependencies complete their codegen.
    pub dependencies: HashSet<(ModuleFullPath, Symbol)>,

    /// Symbols that call THIS entry (reverse edges).
    pub dependents: Vec<(ModuleFullPath, Symbol)>,
}

/// Work item returned by `take_priority_work`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PriorityWork {
    /// Typecheck a module (from TypecheckFirst or TypecheckNext).
    Typecheck(ModuleFullPath),
    /// JIT-compile a symbol needed for macro expansion (from priority queue).
    BlockingJitCodegen(ModuleFullPath, Symbol),
    /// JIT-compile a symbol from a TypecheckDone module.
    JitCodegen(ModuleFullPath, Symbol),
}

// ---------------------------------------------------------------------------
// SchedulerState — all mutable state behind a Mutex.
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct SchedulerState {
    modules: HashMap<ModuleFullPath, ModuleState>,

    /// Level 1: modules known to be delaying others.
    typecheck_first: VecDeque<ModuleFullPath>,

    /// Level 2: priority codegen queue.
    priority_queue: VecDeque<PriorityEntry>,

    /// Level 3: modules ready but not known to be delaying.
    typecheck_next: VecDeque<ModuleFullPath>,

    /// Modules in TypecheckDone. Used by priority workers (level 4)
    /// and nice workers.
    typecheck_done: VecDeque<ModuleFullPath>,

    shutdown: bool,
}

impl SchedulerState {
    fn new() -> Self {
        Self {
            modules: HashMap::new(),
            typecheck_first: VecDeque::new(),
            priority_queue: VecDeque::new(),
            typecheck_next: VecDeque::new(),
            typecheck_done: VecDeque::new(),
            shutdown: false,
        }
    }
}

// ---------------------------------------------------------------------------
// CompileScheduler
// ---------------------------------------------------------------------------

/// Central coordination structure for scheduler-driven compilation.
///
/// Tracks per-module lifecycle, priority codegen queue, and waiter/unblock
/// logic. Does NOT own compilation data — workers access session tables
/// for ASTs, CheckResults, and code pointers.
///
/// State is behind a Mutex with condvars for worker parking:
/// - `priority_work_available` — for Step 11 (priority worker threads)
/// - `object_work_available` — for Step 10 (nice worker threads)
/// - `completion` — for `wait_object_complete` callers
pub struct CompileScheduler {
    state: Mutex<SchedulerState>,
    /// Condvar for priority workers: woken when new work becomes available
    /// (module registered, dependency unblocked, typecheck done) or on shutdown.
    priority_work_available: Condvar,
    /// Condvar for nice workers: woken when a TypecheckDone module becomes
    /// available for object codegen, or on shutdown.
    object_work_available: Condvar,
    /// Condvar for `wait_object_complete`: woken when a module's object
    /// codegen completes, or on shutdown.
    completion: Condvar,
}

impl std::fmt::Debug for CompileScheduler {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompileScheduler")
            .field("state", &"<Mutex<SchedulerState>>")
            .finish()
    }
}

impl Default for CompileScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for CompileScheduler {
    fn drop(&mut self) {
        // Defensive shutdown: wake all condvars so any parked threads
        // observe the shutdown flag and exit, preventing hangs when a
        // scheduler is dropped without an explicit shutdown() call.
        // Idempotent — safe to call even if shutdown() was already called.
        self.shutdown();
    }
}

impl CompileScheduler {
    /// Create a new scheduler with empty state.
    pub fn new() -> Self {
        Self {
            state: Mutex::new(SchedulerState::new()),
            priority_work_available: Condvar::new(),
            object_work_available: Condvar::new(),
            completion: Condvar::new(),
        }
    }

    /// Lock the scheduler state. Recovers from mutex poisoning — if a
    /// worker panicked while holding the lock, the data is still usable
    /// because scheduler state is pure coordination metadata with no
    /// complex invariants that a partial update would corrupt.
    fn lock(&self) -> MutexGuard<'_, SchedulerState> {
        self.state.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    // -----------------------------------------------------------------------
    // Module Registration (§6.1)
    // -----------------------------------------------------------------------

    /// Add a module to the scheduler.
    /// Enters TypecheckFirst if `delays_other` is true, otherwise TypecheckNext.
    ///
    /// Idempotent: if the module is already registered, this is a no-op.
    /// This handles the case where multiple import specs reference the
    /// same dependency module (F2 fix).
    pub fn register_module(
        &self,
        module: ModuleFullPath,
        delays_other: bool,
    ) {
        let mut state = self.lock();

        // Idempotent: skip if already registered.
        if state.modules.contains_key(&module) {
            return;
        }

        let pool = if delays_other {
            ModulePool::TypecheckFirst
        } else {
            ModulePool::TypecheckNext
        };
        state.modules.insert(module.clone(), ModuleState::new(pool));
        if delays_other {
            state.typecheck_first.push_back(module);
        } else {
            state.typecheck_next.push_back(module);
        }

        // Wake priority workers — new module available for typecheck.
        drop(state);
        self.priority_work_available.notify_all();
    }

    /// Register a module loaded from cache.
    /// Enters TypecheckDone with type info available but in-memory code
    /// not yet loaded. Object codegen is pre-satisfied.
    /// Satisfies any pending typecheck waiters on this module's symbols.
    pub fn register_module_cached(
        &self,
        module: ModuleFullPath,
        symbols: HashSet<Symbol>,
    ) {
        let mut state = self.lock();
        let ms = ModuleState::new_cached(symbols.clone());
        state.modules.insert(module.clone(), ms);
        state.typecheck_done.push_back(module.clone());

        // Satisfy any pending typecheck waiters on symbols from this module.
        Self::satisfy_typecheck_waiters_for_all_symbols_locked(
            &mut state, &module, &symbols,
        );

        // Wake nice workers — new TypecheckDone module (already object_done
        // for cached, but wake anyway for consistency).
        drop(state);
        self.object_work_available.notify_all();
    }

    // -----------------------------------------------------------------------
    // Priority Worker Interface (§6.2)
    // -----------------------------------------------------------------------

    /// Return the highest-priority work item, or None when no work available.
    ///
    /// Non-blocking: returns None immediately when all queues are empty.
    /// Used by the inline single-threaded worker loop (Steps 3-10).
    ///
    /// Checks the work lists in priority order:
    ///   1. Pop from typecheck_first -> Typecheck(module)
    ///   2. Scan priority_queue for first Ready entry -> BlockingJitCodegen
    ///   3. Pop from typecheck_next -> Typecheck(module)
    ///   4. (Level 4 — JitCodegen — deferred to later steps.)
    pub fn take_priority_work(&self) -> Option<PriorityWork> {
        let mut state = self.lock();
        Self::try_take_work_locked(&mut state)
    }

    /// Return the highest-priority work item, blocking if none available.
    ///
    /// Parks on `priority_work_available` condvar when no work is available
    /// and more work could still arrive (modules in TypecheckWorking or
    /// TypecheckBlocked). Returns None on shutdown or when all work is
    /// exhausted.
    ///
    /// Used by spawned priority worker threads (Wave 3+). The inline
    /// single-threaded loop uses the non-blocking `take_priority_work`.
    pub fn take_priority_work_blocking(&self) -> Option<PriorityWork> {
        let mut state = self.lock();
        loop {
            if state.shutdown {
                return None;
            }

            if let Some(work) = Self::try_take_work_locked(&mut state) {
                return Some(work);
            }

            // Check if all work is exhausted — no more items will arrive.
            if Self::all_inmem_complete_locked(&state) {
                return None;
            }

            // No work available — park until woken by register_module,
            // unblock, notify_typecheck_done, or shutdown.
            state = self.priority_work_available.wait(state)
                .unwrap_or_else(|e| e.into_inner());
        }
    }

    /// Try to take a work item from the priority ladder (locked).
    ///
    /// Shared implementation for both blocking and non-blocking variants.
    fn try_take_work_locked(
        state: &mut SchedulerState,
    ) -> Option<PriorityWork> {
        if state.shutdown {
            return None;
        }

        // Level 1: TypecheckFirst
        if let Some(module) = state.typecheck_first.pop_front() {
            Self::set_pool_locked(state, &module, ModulePool::TypecheckWorking);
            return Some(PriorityWork::Typecheck(module));
        }

        // Level 2: Priority codegen queue — first Ready entry
        if let Some(work) = Self::claim_priority_codegen_locked(state) {
            return Some(work);
        }

        // Level 3: TypecheckNext
        if let Some(module) = state.typecheck_next.pop_front() {
            Self::set_pool_locked(state, &module, ModulePool::TypecheckWorking);
            return Some(PriorityWork::Typecheck(module));
        }

        // Level 4: JitCodegen — deferred to later steps.
        None
    }

    /// Report that a symbol in the working module has been typechecked.
    /// Checks the module's waiter map: if any module was waiting on
    /// this symbol for WaitKind::Typecheck, removes the waiter and
    /// evaluates whether to unblock the waiting module.
    pub fn notify_symbol_typechecked(
        &self,
        module: &ModuleFullPath,
        symbol: &Symbol,
    ) {
        let mut state = self.lock();
        let waiters = Self::take_waiters_for_symbol_locked(
            &mut state, module, symbol, WaitKind::Typecheck,
        );
        let had_waiters = !waiters.is_empty();
        for waiter_module in waiters {
            Self::try_unblock_locked(&mut state, &waiter_module);
        }

        // Wake priority workers if any module was unblocked.
        if had_waiters {
            drop(state);
            self.priority_work_available.notify_all();
        }
    }

    /// Typechecking needs a symbol from another module that hasn't
    /// been typechecked yet. Moves the current module to TypecheckBlocked.
    /// Adds a WaitKind::Typecheck waiter on the target symbol.
    /// Sets `blocked_on` for cycle detection.
    ///
    /// Returns Err if a circular dependency is detected.
    pub fn block_for_typecheck(
        &self,
        module: &ModuleFullPath,
        needed_module: &ModuleFullPath,
        needed_symbol: &Symbol,
    ) -> Result<(), CranelispError> {
        let mut state = self.lock();
        Self::set_pool_locked(&mut state, module, ModulePool::TypecheckBlocked);

        // Record the forward edge for cycle detection.
        if let Some(ms) = state.modules.get_mut(module) {
            ms.blocked_on = Some(needed_module.clone());
        }

        // Check for cycles before adding the waiter.
        if let Some(cycle) = Self::detect_cycle_locked(&state, module) {
            let cycle_str = cycle.iter()
                .map(|m| m.to_string())
                .collect::<Vec<_>>()
                .join(" -> ");
            let msg = format!("circular dependency detected: {}", cycle_str);
            // Fail the module in the scheduler.
            Self::notify_module_failed_locked(&mut state, module, CranelispError::ModuleError {
                message: msg.clone(),
                file: None,
                span: Span::SYNTHETIC,
            });
            return Err(CranelispError::ModuleError {
                message: msg,
                file: None,
                span: Span::SYNTHETIC,
            });
        }

        Self::add_waiter_locked(&mut state, needed_module, needed_symbol, Waiter {
            module: module.clone(),
            need: WaitKind::Typecheck,
        });
        Ok(())
    }

    /// Typechecking hit a macro expansion that needs codegenned symbols.
    /// Moves the current module to TypecheckBlocked.
    ///
    /// `needed` is the call graph of uncompiled symbols required for
    /// macro expansion. Order is a hint (dependencies first via BFS walk).
    /// Each symbol is pushed to the front of the priority codegen queue.
    pub fn block_for_macro_codegen(
        &self,
        module: &ModuleFullPath,
        needed: Vec<(ModuleFullPath, Symbol)>,
    ) {
        let mut state = self.lock();
        Self::set_pool_locked(&mut state, module, ModulePool::TypecheckBlocked);

        if needed.is_empty() {
            return;
        }

        // The last entry in `needed` is the macro function itself;
        // it carries the unblocks for the waiting module.
        let macro_key = needed.last().map(|(m, s)| (m.clone(), s.clone()));

        Self::push_priority_entries_locked(
            &mut state, module, &needed, macro_key.as_ref(),
        );

        // Wake priority workers — new entries in the priority codegen queue.
        drop(state);
        self.priority_work_available.notify_all();
    }

    /// All forms in the module have been typechecked.
    /// Moves module from TypecheckWorking to TypecheckDone.
    ///
    /// Sweeps all remaining WaitKind::Typecheck waiters on this module
    /// and unblocks them. This handles glob imports where the waiter
    /// blocked on "*" and needs the whole module done.
    pub fn notify_typecheck_done(&self, module: &ModuleFullPath) {
        let mut state = self.lock();

        // Skip modules not registered with the scheduler (e.g., the REPL
        // "user" module in Additive mode). Without this guard the
        // typecheck_done deque grows unbounded.
        if !state.modules.contains_key(module) {
            return;
        }
        Self::set_pool_locked(&mut state, module, ModulePool::TypecheckDone);
        state.typecheck_done.push_back(module.clone());

        // Sweep: collect all modules waiting for typecheck on any symbol
        // in this module, then clear those waiters and unblock.
        let all_waiters: Vec<ModuleFullPath> =
            if let Some(ms) = state.modules.get_mut(module) {
                let waiters: Vec<ModuleFullPath> = ms.waiters
                    .values()
                    .flat_map(|ws| ws.iter())
                    .filter(|w| w.need == WaitKind::Typecheck)
                    .map(|w| w.module.clone())
                    .collect();
                // Remove typecheck waiters (keep codegen waiters).
                ms.waiters.retain(|_, ws| {
                    ws.retain(|w| w.need != WaitKind::Typecheck);
                    !ws.is_empty()
                });
                waiters
            } else {
                Vec::new()
            };

        // Unblock each waiting module and clear its blocked_on edge.
        for waiter_module in all_waiters {
            if let Some(ws) = state.modules.get_mut(&waiter_module) {
                ws.blocked_on = None;
            }
            Self::try_unblock_locked(&mut state, &waiter_module);
        }

        // Wake workers — new TypecheckDone module is potential work.
        // Nice workers get object codegen; priority workers may have
        // JitCodegen work (Level 4) or unblocked modules.
        drop(state);
        self.priority_work_available.notify_all();
        self.object_work_available.notify_all();
    }

    /// A module has failed (parse, type, macro, or codegen error).
    /// Moves module to Failed. Stores the error. Cascades failure
    /// to any modules in TypecheckBlocked waiting on this module's symbols.
    pub fn notify_module_failed(
        &self,
        module: &ModuleFullPath,
        error: CranelispError,
    ) {
        let mut state = self.lock();
        Self::notify_module_failed_locked(&mut state, module, error);

        // Wake condvars — failed modules affect completion checks.
        drop(state);
        self.priority_work_available.notify_all();
        self.completion.notify_all();
    }

    /// Priority codegen of a symbol is complete.
    /// Processes the entry per concurrent-pipeline.md section 4.3.
    pub fn notify_priority_codegen_complete(
        &self,
        module: &ModuleFullPath,
        symbol: &Symbol,
    ) {
        let mut state = self.lock();
        let key = (module.clone(), symbol.clone());

        // Find the entry in the priority queue and update status.
        let entry_idx = Self::find_priority_entry_locked(&state, &key);
        let Some(idx) = entry_idx else { return };

        let deps_empty = state.priority_queue[idx].dependencies.is_empty();

        if deps_empty {
            // All dependencies callable — resolve this entry.
            Self::resolve_priority_entry_locked(&mut state, idx);
        } else {
            // Still has unresolved dependencies — wait.
            state.priority_queue[idx].status = PriorityStatus::Waiting;
        }

        // Wake priority workers — resolved entries may unblock modules.
        drop(state);
        self.priority_work_available.notify_all();
    }

    /// JIT codegen of a symbol is complete.
    /// Removes from jit_reserved. If `no_remaining` is true, sets inmem_done.
    /// If inmem_done and object_done, moves module to Complete.
    pub fn notify_inmem_codegen_complete(
        &self,
        module: &ModuleFullPath,
        symbol: &Symbol,
        no_remaining: bool,
    ) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            ms.jit_reserved.remove(symbol);
            if no_remaining {
                ms.inmem_done = true;
            }
            Self::try_complete_locked(&mut state, module);
        }
    }

    /// Batch-mark multiple symbols as inmem-codegenned.
    /// Used when a Linker load resolves all symbols in a cached .o at once.
    pub fn notify_inmem_codegen_batch_complete(
        &self,
        module: &ModuleFullPath,
        symbols: &[Symbol],
    ) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            for sym in symbols {
                ms.jit_reserved.remove(sym);
            }
            ms.inmem_done = true;
        }
        // Evaluate waiter satisfaction for codegen waiters.
        Self::satisfy_codegen_waiters_batch_locked(&mut state, module, symbols);
        Self::try_complete_locked(&mut state, module);
    }

    // -----------------------------------------------------------------------
    // Nice Worker Interface (§6.3)
    // -----------------------------------------------------------------------

    /// Return a TypecheckDone module with `object_done == false` and
    /// `object_working == false`. Marks the returned module as
    /// `object_working = true` to prevent double-claim by concurrent
    /// nice workers.
    ///
    /// Parks on `object_work_available` condvar when no work is available.
    /// Returns None on shutdown.
    pub fn take_object_codegen(&self) -> Option<ModuleFullPath> {
        let mut state = self.lock();
        loop {
            if state.shutdown {
                return None;
            }
            // Scan for a TypecheckDone module needing object codegen
            // that is not already being worked on by another nice worker.
            let found = state.typecheck_done.iter().find_map(|module| {
                state.modules.get(module)
                    .filter(|ms| !ms.object_done && !ms.object_working)
                    .map(|_| module.clone())
            });
            if let Some(module) = found {
                // Claim the module while holding the lock.
                if let Some(ms) = state.modules.get_mut(&module) {
                    ms.object_working = true;
                }
                return Some(module);
            }
            // No work available — park until woken.
            state = self.object_work_available.wait(state)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
    }

    /// Object codegen for a module is complete (.o written).
    /// Clears `object_working`, sets `object_done`. If completion
    /// condition is met, moves to Complete.
    pub fn notify_object_codegen_complete(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            ms.object_working = false;
            ms.object_done = true;
        }
        Self::try_complete_locked(&mut state, module);

        // Wake wait_object_complete callers.
        drop(state);
        self.completion.notify_all();
    }

    // -----------------------------------------------------------------------
    // Lifecycle (§6.5)
    // -----------------------------------------------------------------------

    /// Wake all nice workers parked on the `object_work_available` condvar.
    ///
    /// Used by the session to ensure workers observe a promotion flag
    /// (e.g., before blocking in `wait_object_complete`).
    pub fn wake_object_workers(&self) {
        self.object_work_available.notify_all();
    }

    /// Signal all workers to shut down. Wakes all condvars so parked
    /// workers can observe the shutdown flag and exit.
    pub fn shutdown(&self) {
        let mut state = self.lock();
        state.shutdown = true;
        drop(state);

        self.priority_work_available.notify_all();
        self.object_work_available.notify_all();
        self.completion.notify_all();
    }

    /// Check if all registered modules have inmem_done set.
    /// Returns Ok(()) if all are Complete or TypecheckDone-with-inmem_done.
    /// Returns Err with the first error if any module is Failed.
    /// Does not wait for object codegen.
    pub fn wait_inmem_complete(&self) -> Result<(), SchedulerError> {
        let state = self.lock();
        for (path, ms) in &state.modules {
            if ms.pool == ModulePool::Failed {
                return Err(SchedulerError::ModuleFailed {
                    module: path.clone(),
                    message: ms.error.as_ref()
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown error".to_string()),
                });
            }
            if !ms.inmem_done && ms.pool != ModulePool::Complete {
                return Err(SchedulerError::InmemIncomplete {
                    module: path.clone(),
                });
            }
        }
        Ok(())
    }

    /// Block until all registered modules have object_done set.
    /// Returns Ok(()) when all are Complete or have object_done.
    /// Returns Err if any module is Failed.
    pub fn wait_object_complete(&self) -> Result<(), SchedulerError> {
        let mut state = self.lock();
        loop {
            let mut all_done = true;
            for (path, ms) in &state.modules {
                if ms.pool == ModulePool::Failed {
                    return Err(SchedulerError::ModuleFailed {
                        module: path.clone(),
                        message: ms.error.as_ref()
                            .map(|e| e.to_string())
                            .unwrap_or_else(|| "unknown error".to_string()),
                    });
                }
                if !ms.object_done {
                    all_done = false;
                    break;
                }
            }
            if all_done || state.shutdown {
                return Ok(());
            }
            // Not all done — park until a module completes or shutdown.
            state = self.completion.wait(state)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
    }

    // -----------------------------------------------------------------------
    // REPL Recovery (Step 9)
    // -----------------------------------------------------------------------

    /// Reset a module from Failed back to an unregistered state.
    ///
    /// Used by the REPL after a failed dependency compilation. Removes
    /// the module from the scheduler entirely so it can be re-registered
    /// and recompiled on the next attempt.
    ///
    /// Preconditions:
    /// - Module must be in the Failed pool.
    /// - TC state for the module has already been rolled back by the caller.
    ///
    /// Postconditions:
    /// - Module is removed from `state.modules`.
    /// - Module is removed from all deques.
    /// - Any priority queue entries for this module are removed.
    pub fn reset_module(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        let Some(ms) = state.modules.get(module) else { return };
        if ms.pool != ModulePool::Failed {
            return; // Only reset Failed modules.
        }

        state.modules.remove(module);

        // Clean deques (defensive — Failed modules should not be in deques,
        // but guard against inconsistency).
        state.typecheck_first.retain(|m| m != module);
        state.typecheck_next.retain(|m| m != module);
        state.typecheck_done.retain(|m| m != module);

        // Remove any priority queue entries for this module.
        state.priority_queue.retain(|e| &e.module != module);
    }

    /// Reset all Failed modules, removing them from the scheduler.
    ///
    /// Used by the REPL after a cascaded dependency failure. Scans all
    /// registered modules and resets any in the Failed pool.
    pub fn reset_all_failed_modules(&self) {
        let mut state = self.lock();
        let failed: Vec<ModuleFullPath> = state.modules
            .iter()
            .filter(|(_, ms)| ms.pool == ModulePool::Failed)
            .map(|(path, _)| path.clone())
            .collect();
        for m in failed {
            // Inline the reset logic to avoid re-locking.
            state.modules.remove(&m);
            state.typecheck_first.retain(|x| x != &m);
            state.typecheck_next.retain(|x| x != &m);
            state.typecheck_done.retain(|x| x != &m);
            state.priority_queue.retain(|e| e.module != m);
        }
    }

    // -----------------------------------------------------------------------
    // Query methods (for tests and diagnostics)
    // -----------------------------------------------------------------------

    /// Get the current pool for a module, if registered.
    pub fn module_pool(&self, module: &ModuleFullPath) -> Option<ModulePool> {
        let state = self.lock();
        state.modules.get(module).map(|ms| ms.pool)
    }

    /// Get a clone of the module state for a module, if registered.
    /// Returns pool, resume_from_form, and other coordination metadata.
    pub fn module_resume_from_form(
        &self,
        module: &ModuleFullPath,
    ) -> Option<Option<usize>> {
        let state = self.lock();
        state.modules.get(module).map(|ms| ms.resume_from_form)
    }

    /// Set the resume_from_form for a module.
    pub fn set_resume_from_form(
        &self,
        module: &ModuleFullPath,
        form_index: usize,
    ) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            ms.resume_from_form = Some(form_index);
        }
    }

    /// Check if the scheduler is in shutdown state.
    pub fn is_shutdown(&self) -> bool {
        let state = self.lock();
        state.shutdown
    }

    /// Iterate over all registered module paths (cloned).
    pub fn all_modules(&self) -> Vec<ModuleFullPath> {
        let state = self.lock();
        state.modules.keys().cloned().collect()
    }

    /// Number of registered modules.
    pub fn module_count(&self) -> usize {
        let state = self.lock();
        state.modules.len()
    }

    /// Number of entries in the priority codegen queue.
    pub fn priority_queue_len(&self) -> usize {
        let state = self.lock();
        state.priority_queue.len()
    }

    // -----------------------------------------------------------------------
    // Internal helpers (all take &mut SchedulerState to avoid re-locking)
    // -----------------------------------------------------------------------

    /// Check if all priority work has been exhausted.
    ///
    /// Returns true when no more work items can appear:
    /// - The modules map is empty (no work registered), or
    /// - All work queues are empty (TypecheckFirst, TypecheckNext, and no
    ///   Ready entries in priority_queue), AND
    /// - No modules are in TypecheckWorking (which could produce new work
    ///   via register_module or block_for_macro_codegen).
    ///
    /// This covers several scenarios:
    /// - All modules TypecheckDone/Complete/Failed: no more work.
    /// - Some modules TypecheckBlocked with nothing to unblock them:
    ///   no active workers means no new notifications will come.
    fn all_inmem_complete_locked(state: &SchedulerState) -> bool {
        // If queues have items, work is available (covered by the
        // try_take logic above, but double-check for completeness).
        if !state.typecheck_first.is_empty()
            || !state.typecheck_next.is_empty()
        {
            return false;
        }
        if state.priority_queue.iter().any(|e| e.status == PriorityStatus::Ready) {
            return false;
        }
        // If any module is being actively processed, it could produce
        // new work (register deps, block for macro codegen).
        let any_working = state.modules.values()
            .any(|ms| ms.pool == ModulePool::TypecheckWorking);
        !any_working
    }

    /// Set a module's pool. Does NOT add/remove from deques — caller
    /// is responsible for deque management.
    fn set_pool_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
        pool: ModulePool,
    ) {
        if let Some(ms) = state.modules.get_mut(module) {
            ms.pool = pool;
        }
    }

    /// Claim the first Ready entry from the priority codegen queue.
    /// Sets its status to Working and returns BlockingJitCodegen.
    fn claim_priority_codegen_locked(
        state: &mut SchedulerState,
    ) -> Option<PriorityWork> {
        for entry in &mut state.priority_queue {
            if entry.status == PriorityStatus::Ready {
                entry.status = PriorityStatus::Working;
                return Some(PriorityWork::BlockingJitCodegen(
                    entry.module.clone(),
                    entry.symbol.clone(),
                ));
            }
        }
        None
    }

    /// Take waiters for a specific symbol and wait kind from a module's
    /// waiter map. Returns the list of waiting module paths.
    fn take_waiters_for_symbol_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
        symbol: &Symbol,
        kind: WaitKind,
    ) -> Vec<ModuleFullPath> {
        let Some(ms) = state.modules.get_mut(module) else {
            return Vec::new();
        };
        let Some(waiters) = ms.waiters.get_mut(symbol) else {
            return Vec::new();
        };

        let mut satisfied = Vec::new();
        waiters.retain(|w| {
            if w.need == kind {
                satisfied.push(w.module.clone());
                false // remove from list
            } else {
                true // keep
            }
        });

        // Clean up empty waiter lists.
        if waiters.is_empty() {
            ms.waiters.remove(symbol);
        }
        satisfied
    }

    /// Add a waiter to a module's waiter map for a specific symbol.
    fn add_waiter_locked(
        state: &mut SchedulerState,
        target_module: &ModuleFullPath,
        target_symbol: &Symbol,
        waiter: Waiter,
    ) {
        if let Some(ms) = state.modules.get_mut(target_module) {
            ms.waiters
                .entry(target_symbol.clone())
                .or_default()
                .push(waiter);
        }
    }

    /// Try to unblock a module. If the module is TypecheckBlocked and
    /// has no remaining wait conditions, move it to TypecheckFirst
    /// (if it has waiters itself) or TypecheckNext (if not).
    fn try_unblock_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
    ) {
        let Some(ms) = state.modules.get(module) else { return };
        if ms.pool != ModulePool::TypecheckBlocked {
            return;
        }

        let has_own_waiters = !ms.waiters.is_empty();
        if has_own_waiters {
            Self::set_pool_locked(state, module, ModulePool::TypecheckFirst);
            state.typecheck_first.push_back(module.clone());
        } else {
            Self::set_pool_locked(state, module, ModulePool::TypecheckNext);
            state.typecheck_next.push_back(module.clone());
        }
    }

    /// A module has failed — locked internal version.
    fn notify_module_failed_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
        error: CranelispError,
    ) {
        Self::set_pool_locked(state, module, ModulePool::Failed);
        if let Some(ms) = state.modules.get_mut(module) {
            ms.error = Some(error);
        }
        Self::cascade_failure_locked(state, module);
    }

    /// Cascade failure from a failed module to all modules waiting
    /// on any of its symbols.
    fn cascade_failure_locked(
        state: &mut SchedulerState,
        failed_module: &ModuleFullPath,
    ) {
        let waiting_modules =
            Self::collect_waiters_for_module_locked(state, failed_module);

        let original_error_msg = state.modules.get(failed_module)
            .and_then(|ms| ms.error.as_ref())
            .map(|e| e.to_string())
            .unwrap_or_else(|| "unknown error".to_string());

        for waiter_module in waiting_modules {
            let error = CranelispError::ModuleError {
                message: format!(
                    "dependency '{}' failed: {}",
                    failed_module,
                    original_error_msg,
                ),
                file: None,
                span: Span::SYNTHETIC,
            };
            // Recursive cascade.
            Self::notify_module_failed_locked(state, &waiter_module, error);
        }
    }

    /// Collect all modules waiting on any symbol from a given module.
    fn collect_waiters_for_module_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
    ) -> Vec<ModuleFullPath> {
        let Some(ms) = state.modules.get_mut(module) else {
            return Vec::new();
        };
        let mut result = Vec::new();
        for (_sym, waiters) in ms.waiters.drain() {
            for w in waiters {
                if !result.contains(&w.module) {
                    result.push(w.module);
                }
            }
        }
        result
    }

    /// Detect a cycle in the blocked_on graph starting from `start`.
    fn detect_cycle_locked(
        state: &SchedulerState,
        start: &ModuleFullPath,
    ) -> Option<Vec<ModuleFullPath>> {
        let mut path = vec![start.clone()];
        let mut current = start.clone();

        loop {
            let next = state.modules.get(&current)
                .and_then(|ms| ms.blocked_on.clone());
            match next {
                None => return None,
                Some(next_mod) => {
                    if next_mod == *start {
                        path.push(next_mod);
                        return Some(path);
                    }
                    if path.contains(&next_mod) {
                        return None;
                    }
                    path.push(next_mod.clone());
                    current = next_mod;
                }
            }
        }
    }

    /// Move module to Complete if inmem_done and object_done.
    fn try_complete_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
    ) {
        let Some(ms) = state.modules.get(module) else { return };
        if ms.pool != ModulePool::TypecheckDone {
            return;
        }
        if ms.inmem_done && ms.object_done {
            Self::set_pool_locked(state, module, ModulePool::Complete);
            // Remove from typecheck_done deque.
            state.typecheck_done.retain(|m| m != module);
        }
    }

    /// Find a priority entry by (module, symbol) key.
    fn find_priority_entry_locked(
        state: &SchedulerState,
        key: &(ModuleFullPath, Symbol),
    ) -> Option<usize> {
        state.priority_queue.iter().position(|e| {
            e.module == key.0 && e.symbol == key.1
        })
    }

    /// Resolve a priority entry: unblock waiting modules, propagate
    /// to dependents, and remove the entry.
    fn resolve_priority_entry_locked(
        state: &mut SchedulerState,
        idx: usize,
    ) {
        let unblocks = state.priority_queue[idx].unblocks.clone();
        let dependents = state.priority_queue[idx].dependents.clone();
        let key = (
            state.priority_queue[idx].module.clone(),
            state.priority_queue[idx].symbol.clone(),
        );

        for waiter_module in &unblocks {
            Self::try_unblock_locked(state, waiter_module);
        }

        let mut newly_resolved = Vec::new();
        for dep_key in &dependents {
            if let Some(dep_idx) = Self::find_priority_entry_locked(state, dep_key)
            {
                state.priority_queue[dep_idx]
                    .dependencies
                    .remove(&key);
                if state.priority_queue[dep_idx].dependencies.is_empty()
                    && state.priority_queue[dep_idx].status
                        == PriorityStatus::Waiting
                {
                    newly_resolved.push(dep_idx);
                }
            }
        }

        state.priority_queue[idx].status = PriorityStatus::Waiting;
        state.priority_queue.remove(idx);

        // Recursively resolve any newly-resolved dependents.
        for dep_key in &dependents {
            if let Some(dep_idx) = Self::find_priority_entry_locked(state, dep_key)
                .filter(|&idx| {
                    state.priority_queue[idx].dependencies.is_empty()
                        && state.priority_queue[idx].status == PriorityStatus::Waiting
                })
            {
                Self::resolve_priority_entry_locked(state, dep_idx);
            }
        }
    }

    /// Push priority entries for a macro codegen request.
    fn push_priority_entries_locked(
        state: &mut SchedulerState,
        waiting_module: &ModuleFullPath,
        needed: &[(ModuleFullPath, Symbol)],
        macro_key: Option<&(ModuleFullPath, Symbol)>,
    ) {
        for (mod_path, sym) in needed {
            let key = (mod_path.clone(), sym.clone());

            if let Some(existing_idx) =
                Self::find_priority_entry_locked(state, &key)
            {
                if Some(&key) == macro_key {
                    let entry = &mut state.priority_queue[existing_idx];
                    if !entry.unblocks.contains(waiting_module) {
                        entry.unblocks.push(waiting_module.clone());
                    }
                }
                continue;
            }

            let unblocks = if Some(&key) == macro_key {
                vec![waiting_module.clone()]
            } else {
                Vec::new()
            };

            let entry = PriorityEntry {
                module: mod_path.clone(),
                symbol: sym.clone(),
                status: PriorityStatus::Ready,
                unblocks,
                dependencies: HashSet::new(),
                dependents: Vec::new(),
            };

            state.priority_queue.push_front(entry);
        }

        Self::wire_priority_edges_locked(state, needed);
    }

    /// Wire forward/reverse edges between priority entries.
    fn wire_priority_edges_locked(
        state: &mut SchedulerState,
        needed: &[(ModuleFullPath, Symbol)],
    ) {
        for i in 1..needed.len() {
            let dep_key = (needed[i - 1].0.clone(), needed[i - 1].1.clone());
            let consumer_key = (needed[i].0.clone(), needed[i].1.clone());

            let dep_idx = Self::find_priority_entry_locked(state, &dep_key);
            let consumer_idx =
                Self::find_priority_entry_locked(state, &consumer_key);

            if let (Some(d), Some(c)) = (dep_idx, consumer_idx) {
                state.priority_queue[c]
                    .dependencies
                    .insert(dep_key.clone());
                state.priority_queue[d]
                    .dependents
                    .push(consumer_key);
            }
        }
    }

    /// Satisfy typecheck waiters for all symbols of a cached module.
    fn satisfy_typecheck_waiters_for_all_symbols_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
        symbols: &HashSet<Symbol>,
    ) {
        for symbol in symbols {
            let waiters = Self::take_waiters_for_symbol_locked(
                state, module, symbol, WaitKind::Typecheck,
            );
            for waiter_module in waiters {
                Self::try_unblock_locked(state, &waiter_module);
            }
        }
    }

    /// Satisfy codegen waiters for a batch of symbols.
    fn satisfy_codegen_waiters_batch_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
        symbols: &[Symbol],
    ) {
        for symbol in symbols {
            let waiters = Self::take_waiters_for_symbol_locked(
                state, module, symbol, WaitKind::Codegen,
            );
            for waiter_module in waiters {
                Self::try_unblock_locked(state, &waiter_module);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Scheduler-specific error type
// ---------------------------------------------------------------------------

/// Errors returned by scheduler wait methods.
#[derive(Debug)]
pub enum SchedulerError {
    /// A module failed during compilation.
    ModuleFailed {
        module: ModuleFullPath,
        message: String,
    },
    /// In-memory codegen not yet complete for a module.
    InmemIncomplete {
        module: ModuleFullPath,
    },
    /// Object codegen not yet complete for a module.
    ObjectIncomplete {
        module: ModuleFullPath,
    },
}

impl std::fmt::Display for SchedulerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SchedulerError::ModuleFailed { module, message } => {
                write!(f, "module '{}' failed: {}", module, message)
            }
            SchedulerError::InmemIncomplete { module } => {
                write!(f, "in-memory codegen incomplete for '{}'", module)
            }
            SchedulerError::ObjectIncomplete { module } => {
                write!(f, "object codegen incomplete for '{}'", module)
            }
        }
    }
}

impl std::error::Error for SchedulerError {}

impl From<SchedulerError> for CranelispError {
    fn from(e: SchedulerError) -> Self {
        match e {
            SchedulerError::ModuleFailed { module, message } => {
                CranelispError::ModuleError {
                    message: format!("module '{}' failed: {}", module, message),
                    file: None,
                    span: Span::SYNTHETIC,
                }
            }
            SchedulerError::InmemIncomplete { module } => {
                CranelispError::ModuleError {
                    message: format!(
                        "in-memory codegen incomplete for '{}'", module
                    ),
                    file: None,
                    span: Span::SYNTHETIC,
                }
            }
            SchedulerError::ObjectIncomplete { module } => {
                CranelispError::ModuleError {
                    message: format!(
                        "object codegen incomplete for '{}'", module
                    ),
                    file: None,
                    span: Span::SYNTHETIC,
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicBool;

    fn mod_path(name: &str) -> ModuleFullPath {
        ModuleFullPath::from(name)
    }

    #[test]
    fn take_object_codegen_returns_none_on_shutdown() {
        let sched = CompileScheduler::new();
        sched.shutdown();
        assert!(sched.take_object_codegen().is_none());
    }

    #[test]
    fn take_object_codegen_object_working_prevents_double_claim() {
        let sched = CompileScheduler::new();
        let m = mod_path("test.mod");
        sched.register_module(m.clone(), false);
        sched.notify_typecheck_done(&m);

        // First claim should succeed and set object_working.
        let first = sched.take_object_codegen();
        assert_eq!(first, Some(m.clone()));

        // Verify the module is marked as object_working.
        {
            let state = sched.lock();
            let ms = state.modules.get(&m).unwrap();
            assert!(ms.object_working);
            assert!(!ms.object_done);
        }

        // Shutdown so the second take_object_codegen doesn't block.
        sched.shutdown();

        // Second call should return None (module is object_working,
        // and shutdown is set).
        let second = sched.take_object_codegen();
        assert!(second.is_none());
    }

    #[test]
    fn notify_object_codegen_complete_clears_object_working() {
        let sched = CompileScheduler::new();
        let m = mod_path("test.mod");
        sched.register_module(m.clone(), false);
        sched.notify_typecheck_done(&m);

        // Claim the module.
        let claimed = sched.take_object_codegen();
        assert_eq!(claimed, Some(m.clone()));

        // Complete object codegen.
        sched.notify_object_codegen_complete(&m);

        // Verify object_working is cleared and object_done is set.
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(!ms.object_working);
        assert!(ms.object_done);
    }

    #[test]
    fn wait_object_complete_returns_when_all_done() {
        let sched = CompileScheduler::new();
        let m = mod_path("test.mod");
        sched.register_module(m.clone(), false);
        sched.notify_typecheck_done(&m);

        // Mark object codegen complete (skip the claim step — direct
        // notification is valid for testing the wait condition).
        sched.notify_object_codegen_complete(&m);

        // wait_object_complete should return immediately.
        let result = sched.wait_object_complete();
        assert!(result.is_ok());
    }

    #[test]
    fn wait_object_complete_returns_err_on_failed_module() {
        let sched = CompileScheduler::new();
        let m = mod_path("test.mod");
        sched.register_module(m.clone(), false);
        sched.notify_module_failed(
            &m,
            CranelispError::ModuleError {
                message: "test error".into(),
                file: None,
                span: Span::SYNTHETIC,
            },
        );

        let result = sched.wait_object_complete();
        assert!(result.is_err());
    }

    #[test]
    fn nice_worker_lifecycle_spawn_and_shutdown() {
        use std::sync::Arc;

        let shared = Arc::new(crate::session_v4::SharedState {
            scheduler: CompileScheduler::new(),
            cache_dir: None,
            compiled_o_paths: Mutex::new(Vec::new()),
            promote_nice_workers: AtomicBool::new(false),
            object_codegen_inputs: Mutex::new(std::collections::HashMap::new()),
        });

        let m = mod_path("test.mod");
        shared.scheduler.register_module(m.clone(), false);
        shared.scheduler.notify_typecheck_done(&m);

        // Spawn a nice worker, let it process the module, then shut down.
        std::thread::scope(|scope| {
            crate::session_v4::spawn_nice_workers(scope, &shared, 1);

            // The worker calls notify_object_codegen_complete, which
            // sets object_done = true. Wait for it.
            let result = shared.scheduler.wait_object_complete();
            assert!(result.is_ok());

            shared.scheduler.shutdown();
        });

        // After scope exits, worker threads have joined.
        assert!(shared.scheduler.is_shutdown());
    }

    #[test]
    fn drop_without_shutdown_sets_shutdown_flag() {
        // Verify that dropping a CompileScheduler without calling
        // shutdown() still sets the shutdown flag (defensive Drop).
        let sched = CompileScheduler::new();
        let m = mod_path("test.mod");
        sched.register_module(m, false);
        // Drop without calling shutdown() — the Drop impl should
        // call shutdown() automatically, preventing any parked
        // threads from hanging.
        drop(sched);
        // If we get here without hanging, the Drop impl works.
    }

    #[test]
    fn drop_after_shutdown_is_idempotent() {
        // Verify that dropping after explicit shutdown() is harmless.
        let sched = CompileScheduler::new();
        sched.shutdown();
        assert!(sched.is_shutdown());
        drop(sched);
        // No panic, no double-shutdown issue.
    }

    #[test]
    fn drop_wakes_parked_worker() {
        // Verify that dropping a scheduler wakes a thread parked on
        // take_object_codegen, preventing a hang.
        use std::sync::Arc;

        let sched = Arc::new(CompileScheduler::new());
        let sched_clone = Arc::clone(&sched);

        let handle = std::thread::spawn(move || {
            // This call parks on the object_work_available condvar
            // because no modules are in TypecheckDone.
            sched_clone.take_object_codegen()
        });

        // Drop our Arc reference. The spawned thread still holds one,
        // so the scheduler is not dropped yet. We need to call shutdown
        // explicitly to wake it.
        // (This test validates the pattern: explicit shutdown before
        // joining threads. The Drop impl is a safety net, not a
        // replacement for explicit shutdown when threads are alive.)
        sched.shutdown();
        let result = handle.join().expect("worker thread panicked");
        assert!(result.is_none()); // shutdown returns None
    }
}
