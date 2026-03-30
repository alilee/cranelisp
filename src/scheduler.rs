// CompileScheduler — scheduler-driven compilation coordination.
//
// Implements the module lifecycle, priority ladder, waiter/unblock logic
// from design/arch/concurrent-pipeline.md. Single-threaded for now
// (no condvars — take_priority_work returns immediately).

use std::collections::{HashMap, HashSet, VecDeque};

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
// SchedulerState — all mutable state behind a single logical lock.
// (No Mutex for now — single-threaded.)
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
/// Currently single-threaded: no Mutex or Condvar. When multi-threaded
/// workers arrive (Step 11), the state will be wrapped in a Mutex and
/// condvars will be added for parking.
#[derive(Debug)]
pub struct CompileScheduler {
    state: SchedulerState,
}

impl Default for CompileScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl CompileScheduler {
    /// Create a new scheduler with empty state.
    pub fn new() -> Self {
        Self {
            state: SchedulerState::new(),
        }
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
        &mut self,
        module: ModuleFullPath,
        delays_other: bool,
    ) {
        // Idempotent: skip if already registered.
        if self.state.modules.contains_key(&module) {
            return;
        }

        let pool = if delays_other {
            ModulePool::TypecheckFirst
        } else {
            ModulePool::TypecheckNext
        };
        self.state.modules.insert(module.clone(), ModuleState::new(pool));
        if delays_other {
            self.state.typecheck_first.push_back(module);
        } else {
            self.state.typecheck_next.push_back(module);
        }
    }

    /// Register a module loaded from cache.
    /// Enters TypecheckDone with type info available but in-memory code
    /// not yet loaded. Object codegen is pre-satisfied.
    /// Satisfies any pending typecheck waiters on this module's symbols.
    pub fn register_module_cached(
        &mut self,
        module: ModuleFullPath,
        symbols: HashSet<Symbol>,
    ) {
        let ms = ModuleState::new_cached(symbols.clone());
        self.state.modules.insert(module.clone(), ms);
        self.state.typecheck_done.push_back(module.clone());

        // Satisfy any pending typecheck waiters on symbols from this module.
        self.satisfy_typecheck_waiters_for_all_symbols(&module, &symbols);
    }

    // -----------------------------------------------------------------------
    // Priority Worker Interface (§6.2)
    // -----------------------------------------------------------------------

    /// Return the highest-priority work item, or None if no work available.
    ///
    /// Checks the work lists in order:
    ///   1. Pop from typecheck_first -> Typecheck(module)
    ///   2. Scan priority_queue for first Ready entry -> BlockingJitCodegen
    ///   3. Pop from typecheck_next -> Typecheck(module)
    ///   4. (Level 4 — JitCodegen — not implemented in Step 3. Returns None.)
    ///
    /// Single-threaded: returns None immediately when empty (no condvar park).
    pub fn take_priority_work(&mut self) -> Option<PriorityWork> {
        if self.state.shutdown {
            return None;
        }

        // Level 1: TypecheckFirst
        if let Some(module) = self.state.typecheck_first.pop_front() {
            self.set_pool(&module, ModulePool::TypecheckWorking);
            return Some(PriorityWork::Typecheck(module));
        }

        // Level 2: Priority codegen queue — first Ready entry
        if let Some(work) = self.claim_priority_codegen() {
            return Some(work);
        }

        // Level 3: TypecheckNext
        if let Some(module) = self.state.typecheck_next.pop_front() {
            self.set_pool(&module, ModulePool::TypecheckWorking);
            return Some(PriorityWork::Typecheck(module));
        }

        // Level 4: JitCodegen — deferred to later steps (W2).
        None
    }

    /// Report that a symbol in the working module has been typechecked.
    /// Checks the module's waiter map: if any module was waiting on
    /// this symbol for WaitKind::Typecheck, removes the waiter and
    /// evaluates whether to unblock the waiting module.
    pub fn notify_symbol_typechecked(
        &mut self,
        module: &ModuleFullPath,
        symbol: &Symbol,
    ) {
        let waiters = self.take_waiters_for_symbol(module, symbol, WaitKind::Typecheck);
        for waiter_module in waiters {
            self.try_unblock(&waiter_module);
        }
    }

    /// Typechecking needs a symbol from another module that hasn't
    /// been typechecked yet. Moves the current module to TypecheckBlocked.
    /// Adds a WaitKind::Typecheck waiter on the target symbol.
    /// Sets `blocked_on` for cycle detection.
    ///
    /// Returns Err if a circular dependency is detected.
    pub fn block_for_typecheck(
        &mut self,
        module: &ModuleFullPath,
        needed_module: &ModuleFullPath,
        needed_symbol: &Symbol,
    ) -> Result<(), CranelispError> {
        self.set_pool(module, ModulePool::TypecheckBlocked);

        // Record the forward edge for cycle detection.
        if let Some(ms) = self.state.modules.get_mut(module) {
            ms.blocked_on = Some(needed_module.clone());
        }

        // Check for cycles before adding the waiter.
        if let Some(cycle) = self.detect_cycle(module) {
            let cycle_str = cycle.iter()
                .map(|m| m.to_string())
                .collect::<Vec<_>>()
                .join(" -> ");
            let msg = format!("circular dependency detected: {}", cycle_str);
            // Fail the module in the scheduler.
            self.notify_module_failed(module, CranelispError::ModuleError {
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

        self.add_waiter(needed_module, needed_symbol, Waiter {
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
        &mut self,
        module: &ModuleFullPath,
        needed: Vec<(ModuleFullPath, Symbol)>,
    ) {
        self.set_pool(module, ModulePool::TypecheckBlocked);

        if needed.is_empty() {
            return;
        }

        // The last entry in `needed` is the macro function itself;
        // it carries the unblocks for the waiting module.
        let macro_key = needed.last().map(|(m, s)| (m.clone(), s.clone()));

        self.push_priority_entries(module, &needed, macro_key.as_ref());
    }

    /// All forms in the module have been typechecked.
    /// Moves module from TypecheckWorking to TypecheckDone.
    ///
    /// Sweeps all remaining WaitKind::Typecheck waiters on this module
    /// and unblocks them. This handles glob imports where the waiter
    /// blocked on "*" and needs the whole module done.
    pub fn notify_typecheck_done(&mut self, module: &ModuleFullPath) {
        // Skip modules not registered with the scheduler (e.g., the REPL
        // "user" module in Additive mode). Without this guard the
        // typecheck_done deque grows unbounded.
        if !self.state.modules.contains_key(module) {
            return;
        }
        self.set_pool(module, ModulePool::TypecheckDone);
        self.state.typecheck_done.push_back(module.clone());

        // Sweep: collect all modules waiting for typecheck on any symbol
        // in this module, then clear those waiters and unblock.
        let all_waiters: Vec<ModuleFullPath> = if let Some(ms) = self.state.modules.get_mut(module) {
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
            if let Some(ws) = self.state.modules.get_mut(&waiter_module) {
                ws.blocked_on = None;
            }
            self.try_unblock(&waiter_module);
        }
    }

    /// A module has failed (parse, type, macro, or codegen error).
    /// Moves module to Failed. Stores the error. Cascades failure
    /// to any modules in TypecheckBlocked waiting on this module's symbols.
    pub fn notify_module_failed(
        &mut self,
        module: &ModuleFullPath,
        error: CranelispError,
    ) {
        self.set_pool(module, ModulePool::Failed);
        if let Some(ms) = self.state.modules.get_mut(module) {
            ms.error = Some(error);
        }
        self.cascade_failure(module);
    }

    /// Priority codegen of a symbol is complete.
    /// Processes the entry per concurrent-pipeline.md section 4.3.
    pub fn notify_priority_codegen_complete(
        &mut self,
        module: &ModuleFullPath,
        symbol: &Symbol,
    ) {
        let key = (module.clone(), symbol.clone());

        // Find the entry in the priority queue and update status.
        let entry_idx = self.find_priority_entry(&key);
        let Some(idx) = entry_idx else { return };

        let deps_empty = self.state.priority_queue[idx].dependencies.is_empty();

        if deps_empty {
            // All dependencies callable — resolve this entry.
            self.resolve_priority_entry(idx);
        } else {
            // Still has unresolved dependencies — wait.
            self.state.priority_queue[idx].status = PriorityStatus::Waiting;
        }
    }

    /// JIT codegen of a symbol is complete.
    /// Removes from jit_reserved. If `no_remaining` is true, sets inmem_done.
    /// If inmem_done and object_done, moves module to Complete.
    pub fn notify_inmem_codegen_complete(
        &mut self,
        module: &ModuleFullPath,
        symbol: &Symbol,
        no_remaining: bool,
    ) {
        if let Some(ms) = self.state.modules.get_mut(module) {
            ms.jit_reserved.remove(symbol);
            if no_remaining {
                ms.inmem_done = true;
            }
            self.try_complete(module);
        }
    }

    /// Batch-mark multiple symbols as inmem-codegenned.
    /// Used when a Linker load resolves all symbols in a cached .o at once.
    pub fn notify_inmem_codegen_batch_complete(
        &mut self,
        module: &ModuleFullPath,
        symbols: &[Symbol],
    ) {
        if let Some(ms) = self.state.modules.get_mut(module) {
            for sym in symbols {
                ms.jit_reserved.remove(sym);
            }
            ms.inmem_done = true;
        }
        // Evaluate waiter satisfaction for codegen waiters.
        self.satisfy_codegen_waiters_batch(module, symbols);
        self.try_complete(module);
    }

    // -----------------------------------------------------------------------
    // Nice Worker Interface (§6.3)
    // -----------------------------------------------------------------------

    /// Return a TypecheckDone module with `object_done == false`.
    /// Returns None if no such module exists or on shutdown.
    pub fn take_object_codegen(&mut self) -> Option<ModuleFullPath> {
        if self.state.shutdown {
            return None;
        }
        for module in &self.state.typecheck_done {
            if let Some(ms) = self.state.modules.get(module) && !ms.object_done {
                return Some(module.clone());
            }
        }
        None
    }

    /// Object codegen for a module is complete (.o written).
    /// Sets `object_done`. If completion condition is met, moves to Complete.
    pub fn notify_object_codegen_complete(&mut self, module: &ModuleFullPath) {
        if let Some(ms) = self.state.modules.get_mut(module) {
            ms.object_done = true;
        }
        self.try_complete(module);
    }

    // -----------------------------------------------------------------------
    // Lifecycle (§6.5)
    // -----------------------------------------------------------------------

    /// Signal all workers to shut down. In multi-threaded mode this
    /// would wake all condvars. Single-threaded: sets the flag so
    /// take_priority_work returns None.
    pub fn shutdown(&mut self) {
        self.state.shutdown = true;
    }

    /// Check if all registered modules have inmem_done set.
    /// Returns Ok(()) if all are Complete or TypecheckDone-with-inmem_done.
    /// Returns Err with the first error if any module is Failed.
    /// Does not wait for object codegen.
    pub fn wait_inmem_complete(&self) -> Result<(), SchedulerError> {
        for (path, ms) in &self.state.modules {
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

    /// Check if all registered modules have object_done set.
    /// Returns Ok(()) if all are Complete, or Err if any Failed or incomplete.
    pub fn wait_object_complete(&self) -> Result<(), SchedulerError> {
        for (path, ms) in &self.state.modules {
            if ms.pool == ModulePool::Failed {
                return Err(SchedulerError::ModuleFailed {
                    module: path.clone(),
                    message: ms.error.as_ref()
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown error".to_string()),
                });
            }
            if !ms.object_done {
                return Err(SchedulerError::ObjectIncomplete {
                    module: path.clone(),
                });
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Query methods (for tests and diagnostics)
    // -----------------------------------------------------------------------

    /// Get the current pool for a module, if registered.
    pub fn module_pool(&self, module: &ModuleFullPath) -> Option<ModulePool> {
        self.state.modules.get(module).map(|ms| ms.pool)
    }

    /// Get the module state for a module, if registered.
    pub fn module_state(&self, module: &ModuleFullPath) -> Option<&ModuleState> {
        self.state.modules.get(module)
    }

    /// Get mutable module state for a module, if registered.
    pub fn module_state_mut(&mut self, module: &ModuleFullPath) -> Option<&mut ModuleState> {
        self.state.modules.get_mut(module)
    }

    /// Check if the scheduler is in shutdown state.
    pub fn is_shutdown(&self) -> bool {
        self.state.shutdown
    }

    /// Number of registered modules.
    pub fn module_count(&self) -> usize {
        self.state.modules.len()
    }

    /// Number of entries in the priority codegen queue.
    pub fn priority_queue_len(&self) -> usize {
        self.state.priority_queue.len()
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------

    /// Set a module's pool. Does NOT add/remove from deques — caller
    /// is responsible for deque management.
    fn set_pool(&mut self, module: &ModuleFullPath, pool: ModulePool) {
        if let Some(ms) = self.state.modules.get_mut(module) {
            ms.pool = pool;
        }
    }

    /// Claim the first Ready entry from the priority codegen queue.
    /// Sets its status to Working and returns BlockingJitCodegen.
    fn claim_priority_codegen(&mut self) -> Option<PriorityWork> {
        for entry in &mut self.state.priority_queue {
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
    fn take_waiters_for_symbol(
        &mut self,
        module: &ModuleFullPath,
        symbol: &Symbol,
        kind: WaitKind,
    ) -> Vec<ModuleFullPath> {
        let Some(ms) = self.state.modules.get_mut(module) else {
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
    fn add_waiter(
        &mut self,
        target_module: &ModuleFullPath,
        target_symbol: &Symbol,
        waiter: Waiter,
    ) {
        if let Some(ms) = self.state.modules.get_mut(target_module) {
            ms.waiters
                .entry(target_symbol.clone())
                .or_default()
                .push(waiter);
        }
    }

    /// Try to unblock a module. If the module is TypecheckBlocked and
    /// has no remaining wait conditions, move it to TypecheckFirst
    /// (if it has waiters itself) or TypecheckNext (if not).
    fn try_unblock(&mut self, module: &ModuleFullPath) {
        let Some(ms) = self.state.modules.get(module) else { return };
        if ms.pool != ModulePool::TypecheckBlocked {
            return;
        }

        // Check if this module is still listed as a waiter anywhere.
        // A module is unblocked when its specific wait is satisfied —
        // the fact that we removed the waiter entry means it is ready.
        // Move to appropriate ready pool.
        let has_own_waiters = !ms.waiters.is_empty();
        if has_own_waiters {
            self.set_pool(module, ModulePool::TypecheckFirst);
            self.state.typecheck_first.push_back(module.clone());
        } else {
            self.set_pool(module, ModulePool::TypecheckNext);
            self.state.typecheck_next.push_back(module.clone());
        }
    }

    /// Cascade failure from a failed module to all modules waiting
    /// on any of its symbols.
    fn cascade_failure(&mut self, failed_module: &ModuleFullPath) {
        // Collect all modules that are waiting on symbols from the
        // failed module, then cascade-fail them.
        let waiting_modules = self.collect_waiters_for_module(failed_module);

        for waiter_module in waiting_modules {
            let error = CranelispError::ModuleError {
                message: format!(
                    "dependency '{}' failed",
                    failed_module
                ),
                file: None,
                span: Span { start: 0, end: 0 },
            };
            // Recursive cascade.
            self.notify_module_failed(&waiter_module, error);
        }
    }

    /// Collect all modules waiting on any symbol from a given module.
    fn collect_waiters_for_module(
        &mut self,
        module: &ModuleFullPath,
    ) -> Vec<ModuleFullPath> {
        let Some(ms) = self.state.modules.get_mut(module) else {
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
    ///
    /// Walks the `blocked_on` linked list from `start`. If it revisits
    /// `start`, a cycle exists. Returns the cycle path if found.
    fn detect_cycle(&self, start: &ModuleFullPath) -> Option<Vec<ModuleFullPath>> {
        let mut path = vec![start.clone()];
        let mut current = start.clone();

        loop {
            let next = self.state.modules.get(&current)
                .and_then(|ms| ms.blocked_on.clone());
            match next {
                None => return None, // chain ends, no cycle
                Some(next_mod) => {
                    if next_mod == *start {
                        path.push(next_mod);
                        return Some(path);
                    }
                    if path.contains(&next_mod) {
                        // Cycle not including start — shouldn't happen since
                        // we only check after blocking start.
                        return None;
                    }
                    path.push(next_mod.clone());
                    current = next_mod;
                }
            }
        }
    }

    /// Move module to Complete if inmem_done and object_done.
    fn try_complete(&mut self, module: &ModuleFullPath) {
        let Some(ms) = self.state.modules.get(module) else { return };
        if ms.pool != ModulePool::TypecheckDone {
            return;
        }
        if ms.inmem_done && ms.object_done {
            self.set_pool(module, ModulePool::Complete);
            // Remove from typecheck_done deque.
            self.state.typecheck_done.retain(|m| m != module);
        }
    }

    /// Find a priority entry by (module, symbol) key.
    fn find_priority_entry(
        &self,
        key: &(ModuleFullPath, Symbol),
    ) -> Option<usize> {
        self.state.priority_queue.iter().position(|e| {
            e.module == key.0 && e.symbol == key.1
        })
    }

    /// Resolve a priority entry: unblock waiting modules, propagate
    /// to dependents, and remove the entry. Per concurrent-pipeline.md §4.3.
    fn resolve_priority_entry(&mut self, idx: usize) {
        // Extract the entry's data before mutating.
        let unblocks = self.state.priority_queue[idx].unblocks.clone();
        let dependents = self.state.priority_queue[idx].dependents.clone();
        let key = (
            self.state.priority_queue[idx].module.clone(),
            self.state.priority_queue[idx].symbol.clone(),
        );

        // Unblock the modules waiting on this macro chain.
        for waiter_module in &unblocks {
            self.try_unblock(waiter_module);
        }

        // Walk dependents: remove this symbol from each dependent's
        // dependencies set.
        let mut newly_resolved = Vec::new();
        for dep_key in &dependents {
            if let Some(dep_idx) = self.find_priority_entry(dep_key) {
                self.state.priority_queue[dep_idx]
                    .dependencies
                    .remove(&key);
                if self.state.priority_queue[dep_idx].dependencies.is_empty()
                    && self.state.priority_queue[dep_idx].status == PriorityStatus::Waiting
                {
                    newly_resolved.push(dep_idx);
                }
            }
        }

        // Remove this entry. Mark as Waiting first to indicate resolved
        // (it will be removed below).
        self.state.priority_queue[idx].status = PriorityStatus::Waiting;

        // Remove the resolved entry from the queue.
        self.state.priority_queue.remove(idx);

        // Recursively resolve any newly-resolved dependents.
        // We must re-find indices since removal shifted them.
        for dep_key in &dependents {
            if let Some(dep_idx) = self.find_priority_entry(dep_key)
                && self.state.priority_queue[dep_idx].dependencies.is_empty()
                && self.state.priority_queue[dep_idx].status == PriorityStatus::Waiting
            {
                self.resolve_priority_entry(dep_idx);
            }
        }
    }

    /// Push priority entries for a macro codegen request.
    /// Wires forward/reverse edges between entries.
    fn push_priority_entries(
        &mut self,
        waiting_module: &ModuleFullPath,
        needed: &[(ModuleFullPath, Symbol)],
        macro_key: Option<&(ModuleFullPath, Symbol)>,
    ) {
        // Build the set of new entries to push, skipping duplicates.
        for (mod_path, sym) in needed {
            let key = (mod_path.clone(), sym.clone());

            if let Some(existing_idx) = self.find_priority_entry(&key) {
                // Already queued — add unblocks if this is the macro entry.
                if Some(&key) == macro_key {
                    let entry = &mut self.state.priority_queue[existing_idx];
                    if !entry.unblocks.contains(waiting_module) {
                        entry.unblocks.push(waiting_module.clone());
                    }
                }
                continue;
            }

            // Create new entry.
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

            // Push to front (per §4.1 — new entries go to front).
            self.state.priority_queue.push_front(entry);
        }

        // Wire forward/reverse edges between entries in `needed`.
        // needed is ordered dependencies-first (BFS), so entry i may
        // depend on entries before it.
        self.wire_priority_edges(needed);
    }

    /// Wire forward/reverse edges between priority entries.
    /// For each pair (dep, consumer) where consumer calls dep,
    /// add dep to consumer's dependencies and consumer to dep's dependents.
    ///
    /// The `needed` list is ordered BFS (dependencies first). Each entry
    /// at position i may be a dependency of entries at positions > i.
    /// For simplicity, we wire edges based on adjacency: each entry
    /// depends on all entries before it that it calls. Since we don't
    /// have the actual call graph edges here, we wire a linear chain
    /// (each entry depends on all previous entries).
    fn wire_priority_edges(&mut self, needed: &[(ModuleFullPath, Symbol)]) {
        // For a correct implementation, the caller should provide
        // actual call graph edges. For now, we wire a simple chain:
        // entry[i] depends on entry[i-1] (if both are in the queue).
        for i in 1..needed.len() {
            let dep_key = (needed[i - 1].0.clone(), needed[i - 1].1.clone());
            let consumer_key = (needed[i].0.clone(), needed[i].1.clone());

            let dep_idx = self.find_priority_entry(&dep_key);
            let consumer_idx = self.find_priority_entry(&consumer_key);

            if let (Some(d), Some(c)) = (dep_idx, consumer_idx) {
                self.state.priority_queue[c]
                    .dependencies
                    .insert(dep_key.clone());
                self.state.priority_queue[d]
                    .dependents
                    .push(consumer_key);
            }
        }
    }

    /// Satisfy typecheck waiters for all symbols of a cached module.
    fn satisfy_typecheck_waiters_for_all_symbols(
        &mut self,
        module: &ModuleFullPath,
        symbols: &HashSet<Symbol>,
    ) {
        for symbol in symbols {
            let waiters = self.take_waiters_for_symbol(
                module, symbol, WaitKind::Typecheck,
            );
            for waiter_module in waiters {
                self.try_unblock(&waiter_module);
            }
        }
    }

    /// Satisfy codegen waiters for a batch of symbols.
    fn satisfy_codegen_waiters_batch(
        &mut self,
        module: &ModuleFullPath,
        symbols: &[Symbol],
    ) {
        for symbol in symbols {
            let waiters = self.take_waiters_for_symbol(
                module, symbol, WaitKind::Codegen,
            );
            for waiter_module in waiters {
                self.try_unblock(&waiter_module);
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
