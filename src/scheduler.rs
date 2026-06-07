// CompileScheduler — scheduler-driven compilation coordination.
//
// Implements the module lifecycle, priority ladder, waiter/unblock logic
// from design/arch/concurrent-pipeline.md. State is behind a Mutex with
// condvars for nice worker parking (Step 10) and future priority worker
// parking (Step 11).

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Condvar, Mutex, MutexGuard};

use cranelisp_types::{ErrorLocation, CranelispError, ModuleFullPath, Span, Symbol};

use crate::observability::{
    self, SchedulerTraceTag,
};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Map a `ModulePool` to a stable `u8` discriminant for observability
/// payloads. Kept here (rather than `#[repr(u8)]` on the enum) so the
/// enum shape stays unconstrained.
fn pool_discriminant(pool: ModulePool) -> u8 {
    match pool {
        ModulePool::TypecheckFirst => 0,
        ModulePool::TypecheckNext => 1,
        ModulePool::TypecheckWorking => 2,
        ModulePool::TypecheckBlocked => 3,
        ModulePool::TypecheckDone => 4,
        ModulePool::Failed => 5,
        ModulePool::Complete => 6,
    }
}

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

    /// A worker has claimed cache-hit inmem loading for this module but has
    /// not yet finished. Set by `take_priority_work` when it dispatches the
    /// JitCodegen work item; checked alongside `inmem_done` so other
    /// workers skip the claimed module. Cleared on completion (via
    /// `notify_inmem_codegen_batch_complete`) or failure (via
    /// `notify_module_failed`). Sprint 58 Wave 2c — splits the
    /// "claim-then-do" race that previously set `inmem_done = true` BEFORE
    /// the worker ran, causing `wait_inmem_complete` to falsely report
    /// readiness while the cache-hit `.o` was still loading.
    pub inmem_claimed: bool,

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

    /// The REPL-eval thread owns this module's post-unblock retry via
    /// `wait_module_inmem_complete_blocking`. Set immediately before the
    /// blocking wait in `register_dep_for_eval`; cleared immediately after.
    ///
    /// When set, `try_unblock_locked` MUST NOT push the module into
    /// `typecheck_first` — doing so would let a persistent priority
    /// worker pop it and race the REPL-eval thread on
    /// `register_imports` reads of `symbol_tables[dep]`.
    ///
    /// Accessed only under the scheduler state lock (no atomics, no
    /// separate mutex). See
    /// `design/int/heisenbug-race-closure.md §7.7 + §8.2` for mechanism;
    /// §3d' for the /arch condition requiring state-lock linearisation.
    pub eval_in_flight: bool,
}

impl ModuleState {
    fn new(pool: ModulePool) -> Self {
        Self {
            pool,
            waiters: HashMap::new(),
            jit_reserved: HashSet::new(),
            inmem_done: false,
            inmem_claimed: false,
            object_working: false,
            object_done: false,
            error: None,
            resume_from_form: None,
            blocked_on: None,
            eval_in_flight: false,
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
            inmem_claimed: false,
            object_working: false,
            object_done: true,
            error: None,
            resume_from_form: None,
            blocked_on: None,
            eval_in_flight: false,
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

/// Work item returned by `take_priority_work`.
///
/// (The `BlockingJitCodegen` variant + the priority-codegen queue it drove were
/// deleted in Sprint 76 W3 — see the `unblock_module` rustdoc and FIXME 0268.
/// The cross-module-FQ macro/fn work that variant was retained for is now served
/// by the synchronous dependency typecheck-and-compile in the worker loop; no
/// speculative per-symbol JIT boost is needed.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PriorityWork {
    /// Typecheck a module (from TypecheckFirst or TypecheckNext).
    Typecheck(ModuleFullPath),
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

    /// Level 3: modules ready but not known to be delaying.
    /// (Level 2 — the priority codegen queue — was deleted in S76 W3; the
    /// numbering is retained for continuity with the work-ladder comments.)
    typecheck_next: VecDeque<ModuleFullPath>,

    /// Modules in TypecheckDone. Used by priority workers (level 4)
    /// and nice workers.
    typecheck_done: VecDeque<ModuleFullPath>,

    /// Modules loaded from cache (vs. compiled from source).
    /// Tracked by the scheduler so `re_register_module` can clear
    /// the flag, preventing stale `.o` loading after a source change.
    cached_modules: HashSet<ModuleFullPath>,

    shutdown: bool,
}

impl SchedulerState {
    fn new() -> Self {
        Self {
            modules: HashMap::new(),
            typecheck_first: VecDeque::new(),
            typecheck_next: VecDeque::new(),
            typecheck_done: VecDeque::new(),
            cached_modules: HashSet::new(),
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
        observability::record_module_event(
            SchedulerTraceTag::RegisterModuleRegister,
            module.as_ref(),
        );
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
        observability::record_module_event(
            SchedulerTraceTag::RegisterModuleCached,
            module.as_ref(),
        );
        let mut state = self.lock();

        // Idempotency guard (F-1): if the module is already registered
        // (e.g., another worker registered it via register_module or a
        // concurrent cache-hit load), skip to avoid overwriting state.
        if state.modules.contains_key(&module) {
            return;
        }

        let ms = ModuleState::new_cached(symbols.clone());
        state.modules.insert(module.clone(), ms);
        state.typecheck_done.push_back(module.clone());
        state.cached_modules.insert(module.clone());

        // Satisfy any pending typecheck waiters on symbols from this module.
        Self::satisfy_typecheck_waiters_for_all_symbols_locked(
            &mut state, &module, &symbols,
        );

        // Wake nice workers — new TypecheckDone module (already object_done
        // for cached, but wake anyway for consistency).
        drop(state);
        self.object_work_available.notify_all();
    }

    /// Re-register a module after its source file has changed.
    ///
    /// Clears the module's scheduler state and re-inserts it at
    /// TypecheckFirst for priority processing. Only modules in
    /// TypecheckDone, Complete, or Failed may be re-registered.
    /// Modules currently being typechecked (TypecheckWorking) are
    /// skipped — the watcher will catch the change on the next poll.
    ///
    /// Returns true if the module was re-registered, false if skipped.
    pub fn re_register_module(&self, module: &ModuleFullPath) -> bool {
        observability::record_module_event(
            SchedulerTraceTag::ReRegisterModule,
            module.as_ref(),
        );
        let mut state = self.lock();
        let ms = match state.modules.get(module) {
            Some(ms) => ms,
            None => return false, // Unknown module.
        };

        match ms.pool {
            ModulePool::TypecheckWorking | ModulePool::TypecheckBlocked => {
                // Worker is mid-typecheck — skip. Next poll will catch it.
                return false;
            }
            ModulePool::TypecheckFirst | ModulePool::TypecheckNext => {
                // Not yet claimed — remove from its queue and re-insert.
                state.typecheck_first.retain(|m| m != module);
                state.typecheck_next.retain(|m| m != module);
            }
            ModulePool::TypecheckDone | ModulePool::Complete | ModulePool::Failed => {
                // Remove from typecheck_done deque if present.
                state.typecheck_done.retain(|m| m != module);
            }
        }

        // Clear cached-module flag so the module gets fresh JIT
        // compilation instead of stale `.o` loading (I-1).
        state.cached_modules.remove(module);

        // Reset ModuleState for re-processing. Keep waiters — other
        // modules may still be waiting on this module's symbols.
        if let Some(ms) = state.modules.get_mut(module) {
            let waiters = std::mem::take(&mut ms.waiters);
            *ms = ModuleState {
                pool: ModulePool::TypecheckFirst,
                waiters,
                jit_reserved: HashSet::new(),
                inmem_done: false,
                inmem_claimed: false,
                object_working: false,
                object_done: false,
                error: None,
                resume_from_form: None,
                blocked_on: None,
                eval_in_flight: false,
            };
        }

        // Push to typecheck_first for immediate processing.
        state.typecheck_first.push_back(module.clone());

        // Wake priority workers.
        drop(state);
        self.priority_work_available.notify_all();
        true
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
    ///   3. Pop from typecheck_next -> Typecheck(module)
    ///   4. Cache-hit JitCodegen for typecheck_done modules needing inmem load.
    ///
    /// (Level 2 — the priority codegen queue scan — was deleted in S76 W3.)
    pub fn take_priority_work(&self) -> Option<PriorityWork> {
        let mut state = self.lock();
        Self::try_take_work_locked(&mut state)
    }

    /// Return the highest-priority work item, blocking if none available.
    ///
    /// Parks on `priority_work_available` condvar when no work is available,
    /// and only returns `None` when shutdown is signalled. Persistent
    /// priority workers (Sprint 57 Wave 4 G9) call this in their main loop
    /// and stay parked for the session lifetime — new modules may be
    /// registered at any time, so "no pending work" is not a terminal
    /// condition.
    ///
    /// Prior to Wave 4, this method also exited on `all_inmem_complete` so
    /// that scoped-thread workers could finish when the scope had no more
    /// work. Persistent workers invalidate that exit path: a session may be
    /// temporarily idle, then receive a new `register_module` /
    /// `reload_module` request, which must wake the parked worker.
    ///
    /// The inline single-threaded loop (`priority_worker_loop` in worker.rs)
    /// still uses the non-blocking `take_priority_work`.
    pub fn take_priority_work_blocking(&self) -> Option<PriorityWork> {
        let mut state = self.lock();
        loop {
            if state.shutdown {
                return None;
            }

            if let Some(work) = Self::try_take_work_locked(&mut state) {
                return Some(work);
            }

            // No work available — park until woken by register_module,
            // unblock, notify_typecheck_done, or shutdown. We do NOT exit
            // on "all work complete" — see Wave 4 doc comment above.
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
            observability::record_module_event(
                SchedulerTraceTag::ModuleStateTypechecking,
                module.as_ref(),
            );
            return Some(PriorityWork::Typecheck(module));
        }

        // Level 2 (priority codegen queue) deleted in S76 W3 — see PriorityWork.

        // Level 3: TypecheckNext
        if let Some(module) = state.typecheck_next.pop_front() {
            Self::set_pool_locked(state, &module, ModulePool::TypecheckWorking);
            observability::record_module_event(
                SchedulerTraceTag::ModuleStateTypechecking,
                module.as_ref(),
            );
            return Some(PriorityWork::Typecheck(module));
        }

        // Level 4: JitCodegen for cached modules needing inmem loading.
        // Scan typecheck_done for modules with inmem_done = false AND
        // inmem_claimed = false (cache-hit modules that need Linker-based
        // code loading and have not yet been claimed by another worker).
        // Sprint 58 Wave 2c: split claim-vs-done so `wait_inmem_complete`
        // only sees `inmem_done = true` after the worker actually finishes.
        let cached_needing_inmem = state.typecheck_done.iter().find_map(|module| {
            state.modules.get(module)
                .filter(|ms| !ms.inmem_done && !ms.inmem_claimed && ms.object_done)
                .map(|_| module.clone())
        });
        if let Some(module) = cached_needing_inmem {
            // Claim guard: set inmem_claimed = true so other workers skip
            // this module while the cache-hit worker loads its `.o`. The
            // worker calls `notify_inmem_codegen_batch_complete` on success
            // (which sets `inmem_done = true`) or `notify_module_failed`
            // on error (which moves the module to `Failed`).
            if let Some(ms) = state.modules.get_mut(&module) {
                ms.inmem_claimed = true;
            }
            // Use a synthetic symbol name — the worker will batch-load the
            // entire .o file regardless of which symbol triggered the item.
            return Some(PriorityWork::JitCodegen(module, Symbol::from("__cache_load")));
        }

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
    /// Immediately re-queue a module that was just blocked on an
    /// already-satisfied dependency.
    ///
    /// Used by the FQ-auto-load path (FIXME 0268): when an FQ reference names a
    /// module that is **already loaded** (e.g. a cache hit, or a peer form
    /// already imported it), the referencing module is registered as
    /// `TypecheckBlocked` via [`block_for_typecheck`] for resume-state
    /// uniformity, but there is no future `notify_typecheck_done(dep)` sweep to
    /// re-queue it (the dep finished before the block was recorded). This drives
    /// the same `try_unblock` sweep `notify_typecheck_done` performs, clearing
    /// the `blocked_on` edge and re-queuing the waiter (or, under
    /// `eval_in_flight`, letting the REPL eval thread drive the retry).
    pub fn unblock_module(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            ms.blocked_on = None;
        }
        Self::try_unblock_locked(&mut state, module);
        drop(state);
        self.priority_work_available.notify_all();
    }

    pub fn block_for_typecheck(
        &self,
        module: &ModuleFullPath,
        needed_module: &ModuleFullPath,
        needed_symbol: &Symbol,
    ) -> Result<(), CranelispError> {
        observability::record_module_event(
            SchedulerTraceTag::ModuleStateBlocked,
            module.as_ref(),
        );
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
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
            return Err(CranelispError::ModuleError {
                message: msg,
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        }

        Self::add_waiter_locked(&mut state, needed_module, needed_symbol, Waiter {
            module: module.clone(),
            need: WaitKind::Typecheck,
        });
        Ok(())
    }

    /// All forms in the module have been typechecked.
    /// Moves module from TypecheckWorking to TypecheckDone.
    ///
    /// Sweeps all remaining WaitKind::Typecheck waiters on this module
    /// and unblocks them. This handles glob imports where the waiter
    /// blocked on "*" and needs the whole module done.
    pub fn notify_typecheck_done(&self, module: &ModuleFullPath) {
        observability::record_module_event(
            SchedulerTraceTag::ModuleStateTypechecked,
            module.as_ref(),
        );
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
        // Wake callers waiting for inmem completion.
        drop(state);
        self.completion.notify_all();
    }

    /// Batch-mark multiple symbols as inmem-codegenned.
    /// Used when a Linker load resolves all symbols in a cached .o at once.
    /// Sprint 58 Wave 2c: clears `inmem_claimed` alongside setting
    /// `inmem_done` so the claim and the completion are released atomically.
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
            ms.inmem_claimed = false;
        }
        // Evaluate waiter satisfaction for codegen waiters.
        Self::satisfy_codegen_waiters_batch_locked(&mut state, module, symbols);
        Self::try_complete_locked(&mut state, module);
        // Wake callers waiting for inmem completion.
        drop(state);
        self.completion.notify_all();
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

    /// Block until a single module reaches inmem_done (or is Complete).
    ///
    /// Used by REPL dep-discovery (Sprint 59 Workstream A): the eval
    /// thread calls this after the form handler suspended the user
    /// module in TypecheckBlocked, to wait for just the dep (not every
    /// registered module — user itself is blocked and must be resumed
    /// by the eval thread via its retry loop). Returns Ok when the
    /// target module has inmem_done. Returns Err on module failure or
    /// if the target module isn't registered.
    pub fn wait_module_inmem_complete_blocking(
        &self,
        target: &ModuleFullPath,
    ) -> Result<(), SchedulerError> {
        let mut state = self.lock();
        loop {
            let ms = state.modules.get(target).ok_or_else(|| {
                SchedulerError::InmemIncomplete { module: target.clone() }
            })?;
            if ms.pool == ModulePool::Failed {
                return Err(SchedulerError::ModuleFailed {
                    module: target.clone(),
                    message: ms.error.as_ref()
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown error".to_string()),
                });
            }
            if ms.inmem_done || ms.pool == ModulePool::Complete {
                return Ok(());
            }
            if state.shutdown {
                return Ok(());
            }
            state = self.completion.wait(state)
                .unwrap_or_else(|e| e.into_inner());
        }
    }

    /// Block until all registered modules have inmem_done set.
    ///
    /// Parks on the `completion` condvar, woken by `notify_inmem_codegen_complete`,
    /// `notify_module_failed`, and `shutdown`. Returns Ok when all modules
    /// have inmem_done or are Complete. Returns Err on module failure.
    pub fn wait_inmem_complete_blocking(&self) -> Result<(), SchedulerError> {
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
                if !ms.inmem_done && ms.pool != ModulePool::Complete {
                    all_done = false;
                    break;
                }
            }
            if all_done || state.shutdown {
                return Ok(());
            }
            state = self.completion.wait(state)
                .unwrap_or_else(|e| e.into_inner());
        }
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

    /// Check whether a module is in the Failed pool.
    pub fn is_failed(&self, module: &ModuleFullPath) -> bool {
        let state = self.lock();
        state.modules.get(module)
            .is_some_and(|ms| ms.pool == ModulePool::Failed)
    }

    /// Check whether a module's typecheck is complete — i.e., its SymbolTable
    /// is fully populated with every Def the module will ever expose.
    ///
    /// Returns true only when the scheduler has observed the module reach a
    /// terminal typecheck state (`TypecheckDone` or `Complete`) OR the module
    /// is not in the scheduler at all (never registered — e.g. compiler-seeded
    /// synthetic modules like `primitives`, `macros`).
    ///
    /// Returns false while the module is still being processed
    /// (`TypecheckNext`, `TypecheckWorking`, `TypecheckBlocked`) — in those
    /// states `symbol_tables[module]` may exist (seeded by
    /// `ensure_module_exists`) but not yet contain the module's Defs.
    ///
    /// Sprint 60 Wave 2 Round 4 fix (publish-vs-flag race, import fast path).
    /// Used by `handle_import` to distinguish "symbol_tables entry exists AND
    /// is fully populated" from "symbol_tables entry exists BUT module
    /// typecheck is still in flight". See `design/backend/defects-456-reduction.md
    /// §"Sprint 60 Wave 2 Round 4"`.
    pub fn is_typechecked(&self, module: &ModuleFullPath) -> bool {
        let state = self.lock();
        let result = match state.modules.get(module) {
            Some(ms) => (
                matches!(
                    ms.pool,
                    ModulePool::TypecheckDone | ModulePool::Complete,
                ),
                Some(ms.pool),
            ),
            // Not in scheduler — compiler-seeded synthetic module or a module
            // that was registered and then removed (Failed reset). Treat as
            // typechecked; the symbol table is the source of truth.
            None => (true, None),
        };
        // Drop the lock before recording to keep the critical section
        // tight. Instrumentation must not hold scheduler state.
        drop(state);
        let pool_tag = result.1.map(pool_discriminant).unwrap_or(u8::MAX);
        if result.0 {
            observability::record_module_event_with_state(
                SchedulerTraceTag::IsTypecheckedHit,
                module.as_ref(),
                pool_tag,
            );
        } else {
            observability::record_module_event_with_state(
                SchedulerTraceTag::IsTypecheckedMiss,
                module.as_ref(),
                pool_tag,
            );
        }
        result.0
    }

    /// Return true if `module` has been registered with the scheduler
    /// (i.e., has a `ModuleState` entry, regardless of pool). Used by
    /// `session_v4::register_dep_for_eval`'s hot-path gate to decide
    /// whether the defensive publish+register pair should be skipped
    /// (Sprint 61 Wave 3 step 3e / H4 race closure).
    ///
    /// Complementary to `is_typechecked` (which returns true only for
    /// `TypecheckDone` / `Complete`). This predicate answers the weaker
    /// question "is the scheduler aware of this module at all?"; a
    /// module that has advanced to `Failed` and been removed via
    /// `reset_module` is NOT registered, so a caller that gates on
    /// `is_registered` will correctly re-register the failed dep.
    ///
    /// The gate at `session_v4.rs::register_dep_for_eval` checks BOTH
    /// `shared.module_sexps.contains_key(dep)` AND `is_registered(dep)`
    /// before eliding the defensive pair — never on published alone
    /// (per /arch §3d interaction-risks mitigation: gating on
    /// published-alone would hang `wait_module_inmem_complete_blocking`
    /// if failure cleanup left the sexps behind).
    pub fn is_registered(&self, module: &ModuleFullPath) -> bool {
        let state = self.lock();
        state.modules.contains_key(module)
    }

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
        observability::record_module_event(
            SchedulerTraceTag::ResetModule,
            module.as_ref(),
        );
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
        observability::record_bulk_event(
            SchedulerTraceTag::ResetAllFailed,
            failed.len(),
        );
        for m in failed {
            // Inline the reset logic to avoid re-locking.
            state.modules.remove(&m);
            state.typecheck_first.retain(|x| x != &m);
            state.typecheck_next.retain(|x| x != &m);
            state.typecheck_done.retain(|x| x != &m);
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

    /// Check if a module was loaded from cache (vs. compiled from source).
    ///
    /// Used by workers to determine whether a codegen work item should
    /// use the Linker-based `.o` fast path.
    pub fn is_cached_module(&self, module: &ModuleFullPath) -> bool {
        let state = self.lock();
        state.cached_modules.contains(module)
    }

    // -----------------------------------------------------------------------
    // Sprint 67 Cluster B sub-fire 2e — cached_modules public accessors
    //
    // The SharedState's pre-S67 `cached_modules: Mutex<HashSet<...>>` was a
    // duplicate of the scheduler's internal set — every write to it was
    // paired with a `register_module_cached` call that already populated the
    // scheduler's copy. The three methods below expose the scheduler's set
    // directly so the SharedState duplicate can delete.
    // -----------------------------------------------------------------------

    /// Mark a module as cache-loaded. Used by `worker.rs` cache-hit paths
    /// that record a cached dep WITHOUT going through `register_module_cached`
    /// (which also creates a `ModuleState` entry). Idempotent — repeated
    /// inserts are no-ops.
    pub fn cached_module_insert(&self, module: ModuleFullPath) {
        let mut state = self.lock();
        state.cached_modules.insert(module);
    }

    /// `is_cached_module` alias — facade name for the lookup.
    pub fn cached_module_contains(&self, module: &ModuleFullPath) -> bool {
        self.is_cached_module(module)
    }

    /// Remove a module from the cache-loaded set. Used when a cached
    /// module's source file changes and the cached artefact is invalidated.
    /// `re_register_module` already calls this internally — exposed here
    /// for direct callers that want to invalidate without re-enqueueing.
    #[allow(dead_code)]
    pub fn cached_module_remove(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        state.cached_modules.remove(module);
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

    // -----------------------------------------------------------------------
    // Internal helpers (all take &mut SchedulerState to avoid re-locking)
    // -----------------------------------------------------------------------

    /// Check if all priority work has been exhausted.
    ///
    /// Returns true when no more work items can appear:
    /// - The modules map is empty (no work registered), or
    /// - All work queues are empty (TypecheckFirst, TypecheckNext), AND
    /// - No modules are in TypecheckWorking (which could produce new work
    ///   via register_module).
    ///
    /// This covers several scenarios:
    /// - All modules TypecheckDone/Complete/Failed: no more work.
    /// - Some modules TypecheckBlocked with nothing to unblock them:
    ///   no active workers means no new notifications will come.
    ///
    /// Retained after Sprint 57 Wave 4 G9 removed its only caller — future
    /// callers (object-codegen exhaustion, hot-flush promotion) may want
    /// the same check. Kept for documentation + possible re-use.
    #[allow(dead_code)]
    fn all_inmem_complete_locked(state: &SchedulerState) -> bool {
        // If queues have items, work is available (covered by the
        // try_take logic above, but double-check for completeness).
        if !state.typecheck_first.is_empty()
            || !state.typecheck_next.is_empty()
        {
            return false;
        }
        // If any module is being actively processed, it could produce
        // new work (register deps).
        let any_working = state.modules.values()
            .any(|ms| ms.pool == ModulePool::TypecheckWorking);
        if any_working {
            return false;
        }
        // Check for cached modules needing inmem loading (Level 4 work).
        let cached_needing_inmem = state.typecheck_done.iter().any(|module| {
            state.modules.get(module)
                .map(|ms| !ms.inmem_done && ms.object_done)
                .unwrap_or(false)
        });
        !cached_needing_inmem
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
    ///
    /// Sprint 61 Wave 3 step 3e' — H5 race closure.
    /// See `design/int/heisenbug-race-closure.md §7.7 + §8.2`. When the
    /// module has `eval_in_flight == true`, the REPL-eval thread owns
    /// the post-unblock retry via `wait_module_inmem_complete_blocking`;
    /// pushing into `typecheck_first` would let a persistent priority
    /// worker pop the caller and race the REPL-eval thread on
    /// `register_imports` reads. Suppress the push in that case; the
    /// eval thread drives the retry when the condvar wakes. The read
    /// of `eval_in_flight` happens under the scheduler state lock held
    /// by the caller (`notify_typecheck_done` → `try_unblock_locked`).
    fn try_unblock_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
    ) {
        let Some(ms) = state.modules.get(module) else { return };
        if ms.pool != ModulePool::TypecheckBlocked {
            return;
        }

        // H5 push-gate: if the REPL-eval thread has registered an
        // in-flight wait on this module, do not queue it for worker
        // pickup. The eval thread will drive the retry itself.
        let eval_in_flight = ms.eval_in_flight;

        if !eval_in_flight {
            let has_own_waiters = !ms.waiters.is_empty();
            if has_own_waiters {
                Self::set_pool_locked(state, module, ModulePool::TypecheckFirst);
                state.typecheck_first.push_back(module.clone());
            } else {
                Self::set_pool_locked(state, module, ModulePool::TypecheckNext);
                state.typecheck_next.push_back(module.clone());
            }
        }

        // Always emit the unblock trace event (even when suppressing the
        // push) so existing observability assertions continue to fire at
        // their existing sites (per /arch §3d' condition 4). The eval
        // thread's post-wake retry is the one that advances the module
        // when the push is suppressed.
        observability::record_module_event(
            SchedulerTraceTag::ModuleStateUnblocked,
            module.as_ref(),
        );
    }

    /// Test-only accessor for the `eval_in_flight` flag. Read under the
    /// scheduler state lock so reads are linearised with
    /// `set_eval_in_flight` writes. Lives here (rather than in a test
    /// module) because `session_v4.rs`'s EvalInFlightGuard panic-unwind
    /// test needs to inspect the flag across the scheduler boundary.
    ///
    /// Sprint 61 Wave 3 step 3f — unit-test support for
    /// `design/int/heisenbug-race-closure.md §3d' test 3`.
    #[cfg(test)]
    pub fn eval_in_flight_for_test(&self, module: &ModuleFullPath) -> bool {
        let state = self.lock();
        state
            .modules
            .get(module)
            .map(|ms| ms.eval_in_flight)
            .unwrap_or(false)
    }

    /// Test-only: observe a module's current pool. Used by the
    /// EvalInFlightGuard panic-unwind test to verify the gate is
    /// disarmed via the public-ish `try_unblock_locked` path.
    ///
    /// Sprint 61 Wave 3 step 3f — unit-test support for
    /// `design/int/heisenbug-race-closure.md §3d' test 3`.
    #[cfg(test)]
    pub fn module_pool_for_test(&self, module: &ModuleFullPath) -> Option<ModulePool> {
        let state = self.lock();
        state.modules.get(module).map(|ms| ms.pool)
    }

    /// Test-only: force a module into `TypecheckBlocked` for unit tests
    /// that exercise `try_unblock_locked` directly without going through
    /// the full `block_for_typecheck` machinery (cycle detection,
    /// waiter wiring, needed-module lookup). Clears the typecheck
    /// queues so the test can observe whether a subsequent call
    /// re-pushes the module.
    ///
    /// Sprint 61 Wave 3 step 3f — unit-test support for
    /// `design/int/heisenbug-race-closure.md §3d' test 3`.
    #[cfg(test)]
    pub fn force_typecheck_blocked_for_test(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        state.typecheck_first.retain(|m| m != module);
        state.typecheck_next.retain(|m| m != module);
        if let Some(ms) = state.modules.get_mut(module) {
            ms.pool = ModulePool::TypecheckBlocked;
        }
    }

    /// Test-only: invoke the `try_unblock_locked` gate from outside
    /// this module. Acquires the scheduler state lock for the call
    /// shape `notify_typecheck_done` uses internally.
    ///
    /// Sprint 61 Wave 3 step 3f — unit-test support for
    /// `design/int/heisenbug-race-closure.md §3d' test 3`.
    #[cfg(test)]
    pub fn try_unblock_for_test(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        Self::try_unblock_locked(&mut state, module);
    }

    /// Set (or clear) the `eval_in_flight` flag on a module under the
    /// scheduler state lock.
    ///
    /// Sprint 61 Wave 3 step 3e' — H5 race closure.
    /// Called by `session_v4.rs::register_dep_for_eval` via
    /// `EvalInFlightGuard`. The flag is read inside
    /// `try_unblock_locked` — both reader and writer take the same
    /// scheduler state lock per /arch §3d' condition 2, so the
    /// set/read pair is linearised by the mutex with no atomics.
    ///
    /// If the module is not registered (e.g., reset after failure),
    /// the call is a no-op; the RAII guard still runs to completion.
    /// See `design/int/heisenbug-race-closure.md §7.7 + §8.2`.
    pub fn set_eval_in_flight(&self, module: &ModuleFullPath, value: bool) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            ms.eval_in_flight = value;
        }
    }

    /// A module has failed — locked internal version.
    fn notify_module_failed_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
        error: CranelispError,
    ) {
        observability::record_module_event(
            SchedulerTraceTag::ModuleStateFailed,
            module.as_ref(),
        );
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
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
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
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                }
            }
            SchedulerError::InmemIncomplete { module } => {
                CranelispError::ModuleError {
                    message: format!(
                        "in-memory codegen incomplete for '{}'", module
                    ),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                }
            }
            SchedulerError::ObjectIncomplete { module } => {
                CranelispError::ModuleError {
                    message: format!(
                        "object codegen incomplete for '{}'", module
                    ),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
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
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
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
            project_root: std::path::PathBuf::new(),
            lib_dirs: Mutex::new(Vec::new()),
            platform_dirs: Mutex::new(Vec::new()),
            module_sexps: Mutex::new(std::collections::HashMap::new()),
            suspend_states: Mutex::new(std::collections::HashMap::new()),
            module_aliases: cranelisp_types::ModuleAliases::default(),
            // Sprint 67 Cluster B sub-fire 3: ObjectCache facade. Disabled
            // (None) for this unit test — no .o compilation runs here.
            cache: std::sync::Arc::new(crate::cache::ObjectCache::new(None, None)),
            promote_nice_workers: AtomicBool::new(false),
            // Sprint 67 Cluster B sub-fire 2e: `cached_modules` SharedState
            // duplicate deleted — scheduler set is single source of truth.
            file_to_module: Mutex::new(std::collections::HashMap::new()),
            symbol_tables: dashmap::DashMap::new(),
            next_type_id: std::sync::atomic::AtomicU32::new(0),
            // Sprint 67 Cluster B sub-fire 2d: `current_module` PIF-relocated
            // to `CompilerSession::current_repl_module`.
            repl_check_state: Mutex::new(None),
            typecheck_products: dashmap::DashMap::new(),
            // Sprint 58 Wave 3b: kept_jits / kept_linkers dissolved per
            // Decision 35.
            kept_dlls: Mutex::new(Vec::new()),
            introspection: dashmap::DashMap::new(),
            // Sprint 66 Wave 3a-γ: TestRunnerState stub for the scheduler
            // unit test. The test exercises the nice-worker lifecycle, not
            // test/trace intrinsics — a default state with empty/null
            // pointers is fine; no JIT codegen runs in this test.
            test_runner_state: Box::new(crate::session_v4::TestRunnerState::stub()),
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

    // ──────────────────────────────────────────────────────────────────────
    // Sprint 58 Wave 2c: split inmem_claimed from inmem_done so
    // wait_inmem_complete only sees inmem_done after the cache-hit worker
    // actually finishes loading the .o.
    // ──────────────────────────────────────────────────────────────────────

    // spec: design/int/symbol-table-cache.md §3.2 — claim guard does not
    // pre-set `inmem_done`; only the worker's
    // `notify_inmem_codegen_batch_complete` does.
    #[test]
    fn level4_claim_guard_sets_inmem_claimed_not_inmem_done() {
        let sched = CompileScheduler::new();
        let m = mod_path("cached.dep");
        // Cached module enters TypecheckDone with object_done=true,
        // inmem_done=false, inmem_claimed=false.
        sched.register_module_cached(m.clone(), HashSet::new());
        {
            let state = sched.lock();
            let ms = state.modules.get(&m).unwrap();
            assert!(!ms.inmem_done, "cached module starts with inmem_done=false");
            assert!(!ms.inmem_claimed, "cached module starts with inmem_claimed=false");
            assert!(ms.object_done, "cached module starts with object_done=true");
        }

        // Take level-4 work — should claim, NOT mark done.
        let work = sched.take_priority_work();
        assert!(matches!(work, Some(PriorityWork::JitCodegen(_, _))));
        {
            let state = sched.lock();
            let ms = state.modules.get(&m).unwrap();
            assert!(
                !ms.inmem_done,
                "claim guard MUST NOT pre-set inmem_done — that races against \
                 wait_inmem_complete (Sprint 58 Wave 2c regression guard)"
            );
            assert!(
                ms.inmem_claimed,
                "claim guard sets inmem_claimed so other workers skip this module"
            );
        }

        // Second take must skip this module (claimed).
        let second = sched.take_priority_work();
        assert!(
            second.is_none(),
            "second take_priority_work must skip the inmem_claimed module"
        );

        // Worker reports completion → inmem_done set, claim cleared.
        sched.notify_inmem_codegen_batch_complete(&m, &[]);
        {
            let state = sched.lock();
            let ms = state.modules.get(&m).unwrap();
            assert!(ms.inmem_done, "completion sets inmem_done");
            assert!(
                !ms.inmem_claimed,
                "completion releases the claim atomically with setting done"
            );
        }
    }

    // spec: design/int/symbol-table-cache.md §3.2 — wait_inmem_complete
    // distinguishes "claimed but not done" from "done"; cache-hit worker
    // failure must surface as an error before trampoline runs.
    #[test]
    fn wait_inmem_complete_does_not_pass_on_claimed_but_unfinished_module() {
        let sched = CompileScheduler::new();
        let m = mod_path("cached.dep");
        sched.register_module_cached(m.clone(), HashSet::new());

        // Take work — claims the module.
        let _work = sched.take_priority_work();

        // wait_inmem_complete (non-blocking) must NOT report success because
        // inmem_done is still false. It returns InmemIncomplete.
        let result = sched.wait_inmem_complete();
        assert!(
            result.is_err(),
            "wait_inmem_complete must fail while module is claimed but not done — \
             pre-fix: claim-guard set inmem_done, hiding the unfinished work"
        );
    }

    // spec: design/int/symbol-table-cache.md §3.2 — multiple cache-hit
    // modules can be loaded in parallel without the claim guard letting
    // wait_inmem_complete pass prematurely.
    #[test]
    fn level4_multiple_cached_modules_each_claim_independently() {
        let sched = CompileScheduler::new();
        let m1 = mod_path("dep.one");
        let m2 = mod_path("dep.two");
        sched.register_module_cached(m1.clone(), HashSet::new());
        sched.register_module_cached(m2.clone(), HashSet::new());

        // Two takes — each claims one module.
        let w1 = sched.take_priority_work();
        let w2 = sched.take_priority_work();
        let w3 = sched.take_priority_work();

        assert!(matches!(w1, Some(PriorityWork::JitCodegen(_, _))));
        assert!(matches!(w2, Some(PriorityWork::JitCodegen(_, _))));
        assert!(w3.is_none(), "third take must return None — both claimed");

        // Both modules must be claimed but not done.
        {
            let state = sched.lock();
            for path in [&m1, &m2] {
                let ms = state.modules.get(path).unwrap();
                assert!(ms.inmem_claimed);
                assert!(!ms.inmem_done);
            }
        }

        // Complete one. wait_inmem_complete must still fail (the other is
        // still claimed-but-not-done).
        sched.notify_inmem_codegen_batch_complete(&m1, &[]);
        assert!(
            sched.wait_inmem_complete().is_err(),
            "wait_inmem_complete must fail while ANY module is claimed-but-not-done"
        );

        // Complete the other. Now wait succeeds.
        sched.notify_inmem_codegen_batch_complete(&m2, &[]);
        assert!(
            sched.wait_inmem_complete().is_ok(),
            "wait_inmem_complete passes after every claim is resolved"
        );
    }

    // ──────────────────────────────────────────────────────────────────────
    // Sprint 61 Wave 3 step 3f — H5 race closure: flag-state invariant
    // against `try_unblock_locked`.
    //
    // Per /arch §3d' "Test authoring (step 3f) requirements" test 2 (/int
    // unit test): when `eval_in_flight == true` on a caller module,
    // `try_unblock_locked(caller)` MUST NOT push the caller into the
    // `typecheck_first` / `typecheck_next` queues. When
    // `eval_in_flight == false`, it DOES push. The REPL-eval thread owns
    // the post-unblock retry; pushing lets a persistent priority worker
    // pop and race.
    //
    // See `design/int/heisenbug-race-closure.md §3d' + §3e'` and the fix
    // site in `try_unblock_locked` at the top of this file.
    // ──────────────────────────────────────────────────────────────────────

    /// Drive a freshly-registered module into `TypecheckBlocked` via direct
    /// state manipulation. Used by the flag-state invariant tests to set up
    /// the exact pre-condition `try_unblock_locked` expects (module in
    /// `TypecheckBlocked`, no remaining wait conditions) without pulling
    /// in the full `block_for_typecheck` machinery (cycle detection,
    /// waiter wiring, etc.) that is irrelevant to the invariant.
    fn put_in_blocked(sched: &CompileScheduler, module: &ModuleFullPath) {
        let mut state = sched.lock();
        // Move from TypecheckFirst → TypecheckBlocked. Remove from the
        // first-pool deque so the test can unambiguously observe whether
        // `try_unblock_locked` re-pushes it.
        state.typecheck_first.retain(|m| m != module);
        state.typecheck_next.retain(|m| m != module);
        if let Some(ms) = state.modules.get_mut(module) {
            ms.pool = ModulePool::TypecheckBlocked;
        }
    }

    // spec: design/int/heisenbug-race-closure.md §3d' test 2 — gate active.
    #[test]
    fn try_unblock_locked_suppressed_when_eval_in_flight_true() {
        let sched = CompileScheduler::new();
        let caller = mod_path("user");
        sched.register_module(caller.clone(), false);
        put_in_blocked(&sched, &caller);

        // Arm the flag — the REPL-eval thread "owns" the retry.
        sched.set_eval_in_flight(&caller, true);

        // Sanity: queues are empty before the call.
        {
            let state = sched.lock();
            assert!(state.typecheck_first.is_empty());
            assert!(state.typecheck_next.is_empty());
            let ms = state.modules.get(&caller).unwrap();
            assert!(ms.eval_in_flight, "flag must be set before gate");
            assert_eq!(ms.pool, ModulePool::TypecheckBlocked);
        }

        // Invoke the gate under the lock (same call shape as
        // `notify_typecheck_done`'s internal sweep).
        {
            let mut state = sched.lock();
            CompileScheduler::try_unblock_locked(&mut state, &caller);
        }

        // Assert: NO push. Caller remains in TypecheckBlocked. Neither
        // queue contains it.
        let state = sched.lock();
        assert!(
            state.typecheck_first.is_empty(),
            "H5 gate MUST suppress push to typecheck_first when \
             eval_in_flight=true; found: {:?}",
            state.typecheck_first,
        );
        assert!(
            state.typecheck_next.is_empty(),
            "H5 gate MUST suppress push to typecheck_next when \
             eval_in_flight=true; found: {:?}",
            state.typecheck_next,
        );
        let ms = state.modules.get(&caller).unwrap();
        assert_eq!(
            ms.pool,
            ModulePool::TypecheckBlocked,
            "caller pool must remain TypecheckBlocked when gate suppresses push",
        );
    }

    // spec: design/int/heisenbug-race-closure.md §3d' test 2 — gate inactive.
    #[test]
    fn try_unblock_locked_pushes_when_eval_in_flight_false() {
        let sched = CompileScheduler::new();
        let caller = mod_path("user");
        sched.register_module(caller.clone(), false);
        put_in_blocked(&sched, &caller);

        // Flag NOT armed (default false). Worker-driven path should push.
        {
            let state = sched.lock();
            let ms = state.modules.get(&caller).unwrap();
            assert!(!ms.eval_in_flight, "flag must be unset for this branch");
        }

        {
            let mut state = sched.lock();
            CompileScheduler::try_unblock_locked(&mut state, &caller);
        }

        // Assert: push happened. Caller has no own-waiters so it goes to
        // `typecheck_next`, not `typecheck_first`. Either way, the pool
        // transitions OUT of `TypecheckBlocked`.
        let state = sched.lock();
        let ms = state.modules.get(&caller).unwrap();
        assert_ne!(
            ms.pool,
            ModulePool::TypecheckBlocked,
            "caller must transition out of TypecheckBlocked when \
             eval_in_flight=false",
        );
        let in_first = state.typecheck_first.iter().any(|m| m == &caller);
        let in_next = state.typecheck_next.iter().any(|m| m == &caller);
        assert!(
            in_first || in_next,
            "caller must be pushed into typecheck_first or typecheck_next \
             when eval_in_flight=false; first={:?} next={:?}",
            state.typecheck_first,
            state.typecheck_next,
        );
    }

    // spec: design/int/heisenbug-race-closure.md §3d' condition 2 — clear
    // via `set_eval_in_flight(false)` re-enables the push path on the
    // NEXT call. This pins the RAII guard's Drop semantics at the
    // scheduler-side: the flag is a proper switch, not a one-shot.
    #[test]
    fn try_unblock_locked_toggle_flag_switches_gate() {
        let sched = CompileScheduler::new();
        let caller = mod_path("user");
        sched.register_module(caller.clone(), false);
        put_in_blocked(&sched, &caller);

        // Phase A: flag set, no push.
        sched.set_eval_in_flight(&caller, true);
        {
            let mut state = sched.lock();
            CompileScheduler::try_unblock_locked(&mut state, &caller);
        }
        {
            let state = sched.lock();
            assert!(state.typecheck_first.is_empty());
            assert!(state.typecheck_next.is_empty());
        }

        // Phase B: flag cleared (RAII Drop equivalent). `try_unblock_locked`
        // precondition requires `TypecheckBlocked`; the first call did not
        // move the caller, so the precondition still holds.
        sched.set_eval_in_flight(&caller, false);
        {
            let mut state = sched.lock();
            CompileScheduler::try_unblock_locked(&mut state, &caller);
        }
        // Now the caller must have been pushed.
        let state = sched.lock();
        let in_first = state.typecheck_first.iter().any(|m| m == &caller);
        let in_next = state.typecheck_next.iter().any(|m| m == &caller);
        assert!(
            in_first || in_next,
            "after clearing eval_in_flight, second try_unblock_locked \
             must push; first={:?} next={:?}",
            state.typecheck_first,
            state.typecheck_next,
        );
    }
}
