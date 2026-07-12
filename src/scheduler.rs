// CompileScheduler — scheduler-driven compilation coordination.
//
// Implements the module lifecycle, priority ladder, waiter/unblock logic
// from design/arch/concurrent-pipeline.md. State is behind a Mutex with
// condvars for nice worker parking (Step 10) and future priority worker
// parking (Step 11).

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Condvar, Mutex, MutexGuard};

use cranelisp_types::{ErrorLocation, CranelispError, ModuleFullPath, Sexp, Span, Symbol};

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

impl ModulePool {
    /// Whether this pool is a TERMINAL typecheck state — the module's
    /// signatures are wholly published (`TypecheckDone` or `Complete`). The
    /// SINGLE definition of the terminal-typecheck predicate: the signature
    /// barrier (`signatures_ready_locked`, `is_typechecked`), the object-stale
    /// gate (`mark_object_stale`), the importable-index arm-time sweep
    /// (`terminal_typecheck_modules`), and the per-worklist branch-(a) check
    /// (`index_worker::is_terminal`) all route through here so the predicate
    /// cannot drift (Principle 7; a drifting terminal predicate reproduces the
    /// `enumeration-miss` class `resolve-home-enumeration.md` closes).
    /// **`Failed` is deliberately excluded** — a failed module's signatures are
    /// NOT published (correct for the barrier/object questions); burn-down
    /// completion handles `Failed` separately via a zero-row skip.
    pub(crate) fn is_terminal_typecheck(self) -> bool {
        matches!(self, ModulePool::TypecheckDone | ModulePool::Complete)
    }
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

    /// Object-staleness generation (S101 R18). Bumped by `mark_object_stale`
    /// every time the module's live table changes after a defining turn /
    /// transaction; snapshotted into `object_claimed_gen` when a nice worker
    /// claims the module. `notify_object_codegen_complete` sets `object_done`
    /// only when the generations still match — a mark that lands while a
    /// write is in flight is NOT lost (the completed write observed an older
    /// table, so the module stays claimable and is rewritten).
    pub object_gen: u64,

    /// The `object_gen` value at the current/most-recent nice-worker claim.
    pub object_claimed_gen: u64,

    /// Error that caused this module to fail, if any.
    pub error: Option<CranelispError>,

    /// **Memoised static import closure (S93, Task-3 per-cluster cache).** The
    /// signature-body pre-pass computes this cluster's static import closure
    /// (`dependency::static_import_closure`) at the top of EVERY
    /// `process_cluster_once` pass — including every retry-from-top a dependency
    /// gap triggers. That walk does an `fs::read_to_string` + `parse` for every
    /// transitively-imported module, so recomputing it once per attempt is
    /// O(retries × closure-size) redundant IO. This memo caches the computed
    /// `ClosureOrder` keyed by a cheap fingerprint of the cluster's *direct*
    /// import declarations (the closure's root set): a cache hit reuses the walk;
    /// a fingerprint miss (a different cluster on the same module scope — e.g. a
    /// new REPL form) recomputes. Reset to `None` by `re_register_module` (source
    /// changed → closure must be re-walked). `None` = not yet computed for the
    /// current cluster.
    pub static_closure_memo: Option<(u64, ClosureOrder)>,

    /// The cluster sexps this module typechecks from (S78 packet model). Held
    /// here so the requeue path (`try_unblock_locked`) can reconstruct the
    /// `PriorityWork::Typecheck { module, sexps }` packet after the dep this
    /// module blocked on completes — the worker re-runs the cluster from the
    /// top with no saved suspend state. `None` for cache-restored modules
    /// (registered at `TypecheckDone`, never typechecked from source).
    pub sexps: Option<std::sync::Arc<[Sexp]>>,

    /// Module this module is currently blocked on (forward edge).
    /// Set when entering TypecheckBlocked, cleared when unblocked.
    /// Used for cycle detection.
    ///
    /// **Single-writer / exclusive-claim (S93, Invariant SW).** The former
    /// `eval_owned` role-flag (S78 §3 / B1) is RETIRED. The entry module's
    /// single-orchestrator property is now structural, not a convention flag:
    /// the eval thread (REPL) drives its entry module's body WITHOUT ever moving
    /// it to `TypecheckBlocked` — on a dependency gap it records a *cycle-check*
    /// `blocked_on` edge via [`Self::register_dep_edge_for_cycle_check`] but
    /// leaves the entry in its terminal pool (never claimable from a typecheck
    /// queue), then waits on the *dependency* itself and re-runs the cluster
    /// from the top. Because the entry never enters `TypecheckBlocked`,
    /// `try_unblock_locked`'s existing `pool != TypecheckBlocked` guard already
    /// makes a stray requeue impossible — there is no second orchestrator to
    /// suppress, so no flag is needed (claimable XOR owned, by construction).
    pub blocked_on: Option<ModuleFullPath>,
}

impl ModuleState {
    fn new(pool: ModulePool, sexps: Option<std::sync::Arc<[Sexp]>>) -> Self {
        Self {
            pool,
            waiters: HashMap::new(),
            jit_reserved: HashSet::new(),
            inmem_done: false,
            inmem_claimed: false,
            object_working: false,
            object_done: false,
            object_gen: 0,
            object_claimed_gen: 0,
            error: None,
            static_closure_memo: None,
            sexps,
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
            inmem_claimed: false,
            object_working: false,
            object_done: true,
            object_gen: 0,
            object_claimed_gen: 0,
            error: None,
            static_closure_memo: None,
            sexps: None,
            blocked_on: None,
        }
    }

    /// Cache-hit constructor for a module that has NO codegen object to load
    /// (S84 Phase 4B, FIXME 0387 — a generic-only module whose sole defn is a
    /// slot-less `Polymorphic` template produces no `.o`). It enters
    /// TypecheckDone with **`inmem_done = true`** so the Level-4 `JitCodegen`
    /// scan never picks it up — there is nothing to mmap or wire (its schemes,
    /// available as mono SOURCES, are already installed into the symbol table).
    fn new_cached_no_object(symbols: HashSet<Symbol>) -> Self {
        let _ = symbols;
        Self {
            pool: ModulePool::TypecheckDone,
            waiters: HashMap::new(),
            jit_reserved: HashSet::new(),
            inmem_done: true,
            inmem_claimed: false,
            object_working: false,
            object_done: true,
            object_gen: 0,
            object_claimed_gen: 0,
            error: None,
            static_closure_memo: None,
            sexps: None,
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

/// Work item returned by `take_priority_work`.
///
/// (The `BlockingJitCodegen` variant + the priority-codegen queue it drove were
/// deleted in Sprint 76 W3 — see the `unblock_module` rustdoc and FIXME 0268.
/// The cross-module-FQ macro/fn work that variant was retained for is now served
/// by the synchronous dependency typecheck-and-compile in the worker loop; no
/// speculative per-symbol JIT boost is needed.)
#[derive(Debug, Clone)]
pub enum PriorityWork {
    /// Typecheck a module (from TypecheckFirst or TypecheckNext).
    ///
    /// S78 in-call-stack restructure: the cluster's parsed sexps ride ON the
    /// work packet (`Arc<[Sexp]>`), replacing the former cross-thread
    /// `SharedState.module_sexps` parking map. The worker reads them off the
    /// packet; on a dependency gap the worker frees back to the pool and the
    /// scheduler requeues the SAME packet (sexps included) via
    /// `try_unblock_locked` — the worker re-runs the cluster from the top
    /// against now-larger live state with no saved suspend state.
    Typecheck {
        module: ModuleFullPath,
        sexps: std::sync::Arc<[Sexp]>,
    },
    /// JIT-compile a symbol from a TypecheckDone module.
    JitCodegen(ModuleFullPath, Symbol),
}

// `PartialEq`/`Eq` were derived pre-S78 (the queue held bare `ModuleFullPath`).
// With `Arc<[Sexp]>` on the packet, structural equality would require
// `Sexp: Eq` AND a deep slice compare on every requeue — neither is wanted.
// No call site compares whole `PriorityWork` values; tests assert on `.module`
// / the variant shape. Manual `PartialEq` compares only the discriminant +
// module identity (cheap, sufficient for any "is this the same work item"
// check), deliberately ignoring the sexps payload.
impl PartialEq for PriorityWork {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                PriorityWork::Typecheck { module: a, .. },
                PriorityWork::Typecheck { module: b, .. },
            ) => a == b,
            (
                PriorityWork::JitCodegen(am, asym),
                PriorityWork::JitCodegen(bm, bsym),
            ) => am == bm && asym == bsym,
            _ => false,
        }
    }
}
impl Eq for PriorityWork {}

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
    ///
    /// S78 packet model: `sexps` are the module's parsed cluster forms, stored
    /// on the `ModuleState` so the work item the worker pops
    /// (`PriorityWork::Typecheck { module, sexps }`) and any requeue after a
    /// dependency block both carry them. Replaces the former
    /// `SharedState.module_sexps` cross-thread parking map.
    pub fn register_module(
        &self,
        module: ModuleFullPath,
        sexps: std::sync::Arc<[Sexp]>,
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
        state.modules.insert(module.clone(), ModuleState::new(pool, Some(sexps)));
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

        // Wake BOTH worker classes. Nice workers get the new TypecheckDone
        // module (already object_done for cached, but wake for consistency).
        // Priority workers MUST also be woken: a cache-restored module enters
        // with `inmem_done == false` and its in-memory `.o` load is a Level-4
        // `JitCodegen` priority work item (`try_take_work_locked`); and the
        // `satisfy_typecheck_waiters` sweep above may have requeued blocked
        // waiter modules into `typecheck_first`/`typecheck_next` via
        // `try_unblock_locked`. Both are priority work — signalling only
        // `object_work_available` leaves a priority worker parked and the
        // queued work undrained (lost wakeup → a `wait_*_inmem_complete`
        // caller parks on `completion` forever). The guarded-condvar discipline
        // requires every state mutation that enqueues priority work to signal
        // `priority_work_available` under the established lock order.
        drop(state);
        self.priority_work_available.notify_all();
        self.object_work_available.notify_all();
    }

    /// Register a cache-hit module that has NO codegen object (S84 Phase 4B,
    /// FIXME 0387). Mirrors [`Self::register_module_cached`] but installs the
    /// module with `inmem_done = true` (via [`ModuleState::new_cached_no_object`])
    /// so the Level-4 `JitCodegen` scan never tries to mmap a non-existent `.o`.
    /// A generic-only module's schemes are already installed into the symbol
    /// table by the caller (`try_cache_hit_load`); they are mono SOURCES with no
    /// callable code to load.
    pub fn register_module_cached_no_object(
        &self,
        module: ModuleFullPath,
        symbols: HashSet<Symbol>,
    ) {
        observability::record_module_event(
            SchedulerTraceTag::RegisterModuleCached,
            module.as_ref(),
        );
        let mut state = self.lock();

        // Idempotency guard (F-1): mirror register_module_cached.
        if state.modules.contains_key(&module) {
            return;
        }

        let ms = ModuleState::new_cached_no_object(symbols.clone());
        state.modules.insert(module.clone(), ms);
        state.typecheck_done.push_back(module.clone());
        state.cached_modules.insert(module.clone());

        // Satisfy pending typecheck waiters on this module's symbols.
        Self::satisfy_typecheck_waiters_for_all_symbols_locked(
            &mut state, &module, &symbols,
        );
        // The module is already inmem_done; satisfy any codegen waiters and run
        // the completion transition so a `wait_*_inmem_complete` caller wakes.
        Self::satisfy_codegen_waiters_batch_locked(&mut state, &module, &[]);
        Self::try_complete_locked(&mut state, &module);

        drop(state);
        self.priority_work_available.notify_all();
        self.object_work_available.notify_all();
        self.completion.notify_all();
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
    ///
    /// S78 packet model: `sexps` are the freshly-reparsed cluster forms,
    /// stored on the reset `ModuleState` so the worker that pops the
    /// re-registered work item (and any requeue) typechecks from the new
    /// source.
    pub fn re_register_module(
        &self,
        module: &ModuleFullPath,
        sexps: std::sync::Arc<[Sexp]>,
    ) -> bool {
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
        // modules may still be waiting on this module's symbols. The watcher
        // reload is **pool-driven but eval-synchronous** (S93, Invariant SW):
        // this DOES reset the pool to TypecheckFirst + restores `sexps` + pushes
        // the module onto `typecheck_first`, so a POOL worker re-typechecks it
        // on this reload pass with the uniform block/requeue discipline — that
        // is SAFE because the watcher reload runs synchronously on the eval
        // thread (`poll_and_reload` / `reload_module`, which blocks on
        // `wait_inmem_complete_blocking`), so the eval thread holds NO
        // concurrent claim while the pool drives the reload. No `eval_owned`
        // role-flag is preserved or needed: the entry funnels through the same
        // exclusive claim as any other pool-driven module (B1 stays closed by
        // construction, not by a per-role early-return).
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
                // S101 R18: bump the staleness generation so an in-flight
                // nice-worker write (claimed pre-reload) cannot mark the
                // reloaded module object-done with a pre-reload table.
                object_gen: ms.object_gen + 1,
                object_claimed_gen: ms.object_claimed_gen,
                error: None,
                // Source changed — the static closure must be re-walked.
                static_closure_memo: None,
                sexps: Some(sexps),
                blocked_on: None,
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

    /// Build a `PriorityWork::Typecheck` packet for a module popped off a
    /// typecheck queue: flip it to `TypecheckWorking`, emit the trace tag, and
    /// attach the module's stored cluster sexps (S78 packet model). If the
    /// module has no stored sexps (should not happen for a queued typecheck —
    /// `register_module`/`re_register_module` always store them, and requeue
    /// preserves them), an empty slice is attached so the worker surfaces an
    /// empty-cluster no-op rather than panicking.
    fn dispatch_typecheck_locked(
        state: &mut SchedulerState,
        module: ModuleFullPath,
    ) -> PriorityWork {
        Self::set_pool_locked(state, &module, ModulePool::TypecheckWorking);
        observability::record_module_event(
            SchedulerTraceTag::ModuleStateTypechecking,
            module.as_ref(),
        );
        let sexps = state
            .modules
            .get(&module)
            .and_then(|ms| ms.sexps.clone())
            .unwrap_or_else(|| std::sync::Arc::from(Vec::new()));
        PriorityWork::Typecheck { module, sexps }
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
            return Some(Self::dispatch_typecheck_locked(state, module));
        }

        // Level 2 (priority codegen queue) deleted in S76 W3 — see PriorityWork.

        // Level 3: TypecheckNext
        if let Some(module) = state.typecheck_next.pop_front() {
            return Some(Self::dispatch_typecheck_locked(state, module));
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

    // `notify_symbol_typechecked` (the per-symbol signature-readiness path) was
    // RETIRED in S93 (`signature-body-prepass.md` §6 net-neutral subtraction).
    // Every live `block_for_typecheck` registers a `"*"` whole-module waiter
    // satisfied by `notify_typecheck_done`'s sweep — the per-symbol notify
    // matched no waiter and was a no-op in the live pipeline. The module-atomic
    // signature barrier (Invariant PP) is the single signature-readiness
    // protocol; keeping a second one was a Principle 7 violation.

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
    /// the `blocked_on` edge and re-queuing the waiter.
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

        // S93 Invariant PP — lost-wakeup Blocker fix (mirror
        // `block_on_first_unready_closure_member`'s atomic check-and-act). The
        // per-import FQ-dependency discovery path (`dependency.rs` —
        // `handle_import` / `handle_export` / `drive_module_dep` /
        // `drive_submodule`) calls `register_module(dep, …, true)` (which enqueues
        // `dep` and fires `priority_work_available`) and THEN `block_dep` → here.
        // BETWEEN those two calls a priority worker can pop `dep`, typecheck it to
        // terminal, and run `notify_typecheck_done(dep)` — whose waiter-sweep finds
        // NO waiter for `module` yet. If we then UNCONDITIONALLY register `module`
        // as a waiter on the now-terminal `dep`, no future
        // `notify_typecheck_done(dep)` will ever fire again → `module` is stranded
        // in `TypecheckBlocked` forever (the intermittent 30 s hang). This is the
        // SAME class S93 closed for the body-boundary barrier; the discovery path
        // was never converted — closing it here.
        //
        // The cure: BEFORE registering the waiter, re-check (under THIS single
        // lock — no release between the check and the act) whether `needed_module`
        // has already published its signatures (gone terminal, per
        // `signatures_ready_locked` — the same predicate the body-boundary gate
        // uses). If so, do NOT register a dead waiter; instead requeue `module`
        // immediately via the existing `try_unblock_locked` path (exactly what the
        // already-loaded / cache-hit arms of `drive_module_dep` do with
        // `unblock_module`), so a worker re-drives `module` against the now-larger
        // live state and proceeds. With the scan and the act under one lock,
        // `notify_typecheck_done(needed_module)` either ran entirely before this
        // call (the check sees it terminal and requeues) or runs entirely after
        // (it sweeps the waiter this call registers below) — there is no gap.
        //
        // Only the whole-module (`"*"`) waiter — the sole production form (every
        // `dependency.rs` caller passes `"*"`) — gets the terminal-requeue: a
        // terminal `needed_module` has published ALL its symbols, so a `"*"`
        // waiter is definitively satisfiable. The specific-symbol form is
        // test-only and keeps the register-a-waiter behaviour.
        if needed_symbol.as_ref() == "*"
            && Self::signatures_ready_locked(&state, needed_module)
        {
            // Clear any stale edge, move to TypecheckBlocked so
            // `try_unblock_locked`'s `pool == TypecheckBlocked` precondition holds,
            // then immediately requeue (→ TypecheckFirst/Next). Mirrors
            // `unblock_module`, inlined under this lock.
            if let Some(ms) = state.modules.get_mut(module) {
                ms.blocked_on = None;
            }
            Self::set_pool_locked(&mut state, module, ModulePool::TypecheckBlocked);
            Self::try_unblock_locked(&mut state, module);
            drop(state);
            self.priority_work_available.notify_all();
            return Ok(());
        }

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
        // entry module in Additive mode). Without this guard the
        // typecheck_done deque grows unbounded. (Keyed on `contains_key`, not
        // the module name — the entry module's name is the CLI target, not
        // necessarily "user", per S78 §1.)
        if !state.modules.contains_key(module) {
            return;
        }
        Self::set_pool_locked(&mut state, module, ModulePool::TypecheckDone);
        // Phase-A barrier (S93): the terminal pool transition IS the signature
        // publication edge. `notify_typecheck_done` runs post-`finalize_cluster`
        // (the cluster's Defs are already installed in `symbol_tables[module]`),
        // so `pool → TypecheckDone` happens-after publication — the barrier
        // predicate (`signatures_ready_locked`) reads the pool directly, with no
        // separate bit. Waking `completion` below releases any barrier waiter.
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
        //
        // ALSO wake `completion`: the TypecheckWorking → TypecheckDone pool
        // transition is a settle event a reload caller may be parked on. The
        // worker sets `inmem_done = true` mid-codegen (before this transition),
        // so a caller can observe `inmem_done` while the pool is still
        // TypecheckWorking. `re_register_module` refuses a mid-typecheck module
        // (returns false), so `reload_module` must be able to wait for this
        // transition before re-registering — otherwise the reload is silently
        // dropped (S82 reload-during-compile race). See
        // `wait_module_typecheck_settled`.
        drop(state);
        self.priority_work_available.notify_all();
        self.object_work_available.notify_all();
        self.completion.notify_all();
    }

    /// Block until `module` is NOT in a transient typecheck state
    /// (`TypecheckWorking` / `TypecheckBlocked`) — i.e. a worker is not
    /// currently mid-pass on it. Returns when the module has settled into a
    /// queued (`TypecheckFirst`/`TypecheckNext`) or terminal
    /// (`TypecheckDone`/`Complete`/`Failed`) pool, or when the module is
    /// unknown / shutdown is signalled.
    ///
    /// S82 reload-during-compile race fix. A worker sets `inmem_done = true`
    /// partway through codegen, *before* it finishes the pass and calls
    /// `notify_typecheck_done` (which moves the module out of
    /// `TypecheckWorking`). A caller that observed `inmem_done` via
    /// `wait_inmem_complete_blocking` can therefore reach `reload_module` while
    /// the worker is still mid-pass; `re_register_module` then hits its
    /// "mid-typecheck — skip" guard and returns `false`, and the reload is
    /// silently lost. `reload_module` calls this first so the in-flight pass
    /// settles and the subsequent `re_register_module` reliably succeeds.
    pub fn wait_module_typecheck_settled(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        loop {
            if state.shutdown {
                return;
            }
            match state.modules.get(module).map(|ms| ms.pool) {
                None => return, // Unknown module — nothing to wait on.
                Some(ModulePool::TypecheckWorking) | Some(ModulePool::TypecheckBlocked) => {
                    state = self.completion.wait(state)
                        .unwrap_or_else(|e| e.into_inner());
                }
                Some(_) => return, // Settled (queued or terminal).
            }
        }
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
        // Evaluate waiter satisfaction for codegen waiters. This may requeue
        // blocked waiter modules into the typecheck queues via
        // `try_unblock_locked` (priority work), so `priority_work_available`
        // must be signalled alongside `completion` below — a requeue without a
        // priority-worker wake is a lost wakeup.
        Self::satisfy_codegen_waiters_batch_locked(&mut state, module, symbols);
        Self::try_complete_locked(&mut state, module);
        // Wake callers waiting for inmem completion, AND priority workers in
        // case the waiter sweep requeued typecheck work.
        drop(state);
        self.priority_work_available.notify_all();
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
                // Claim the module while holding the lock (snapshotting the
                // staleness generation — S101 R18 lost-update fix).
                if let Some(ms) = state.modules.get_mut(&module) {
                    ms.object_working = true;
                    ms.object_claimed_gen = ms.object_gen;
                }
                return Some(module);
            }
            // No work available — park until woken.
            state = self.object_work_available.wait(state)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
    }

    /// Non-blocking object-codegen claim (S91 — the nice-worker index
    /// interleave). Returns a claimed TypecheckDone module needing object
    /// codegen, or `None` immediately if there is none (NEVER parks). Used by
    /// the nice-worker loop to prefer object codegen, then fall to index work
    /// when no object work is pending (object codegen first, index in the slack
    /// — `design/int/agent.md §25.5` / R17). Returns `None` on shutdown.
    pub fn try_take_object_codegen(&self) -> Option<ModuleFullPath> {
        let mut state = self.lock();
        if state.shutdown {
            return None;
        }
        let found = state.typecheck_done.iter().find_map(|module| {
            state
                .modules
                .get(module)
                .filter(|ms| !ms.object_done && !ms.object_working)
                .map(|_| module.clone())
        });
        if let Some(module) = found {
            if let Some(ms) = state.modules.get_mut(&module) {
                ms.object_working = true;
                ms.object_claimed_gen = ms.object_gen;
            }
            return Some(module);
        }
        None
    }

    /// Park a nice worker until object-codegen work, index work, or shutdown may
    /// be available (S91 — the index interleave). Parks on the
    /// `object_work_available` condvar (woken by `register_module*`,
    /// `wake_object_workers`, the index-enqueue wake, and `shutdown`). Returns
    /// `false` on shutdown (the worker should exit), `true` otherwise (re-scan).
    pub fn park_nice_worker(&self) -> bool {
        let state = self.lock();
        if state.shutdown {
            return false;
        }
        // S95 window-#2 lost-wakeup fix (mirror the S93/Invariant-PP window-#1
        // discipline — re-check the predicate UNDER THIS LOCK before parking, no
        // lost signal). The nice-worker loop's non-blocking `try_take_object_codegen`
        // and this park are TWO separate lock acquisitions (the S91 index
        // interleave). A `notify_typecheck_done` that, under the state lock, pushed
        // a module to `typecheck_done` (object_done == false) AND fired
        // `object_work_available.notify_all()` in the GAP between those two
        // acquisitions delivers its notify to an empty waiter set — it is LOST,
        // and the about-to-park nice worker then `wait`s forever. The module
        // strands in `TypecheckDone` with `object_done == false`, and the eval
        // thread's `wait_object_complete` (REPL `.o` cache-persist / `--link`
        // hot flush) hangs on it (the intermittent oversubscription hang, pinned
        // via the SIGUSR1 dump: `[TypecheckDone] user object_done=false` with the
        // nice worker parked). Re-scanning here closes the window: the push+notify
        // in `notify_typecheck_done` and this scan are serialized on the state
        // lock, so EITHER this scan observes the pending work (return `true`, the
        // loop re-iterates and `try_take_object_codegen` claims it) OR the notify
        // arrives after we begin `wait` below and wakes us. There is no gap.
        if Self::has_pending_object_work_locked(&state) {
            return true;
        }
        let state = self
            .object_work_available
            .wait(state)
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        !state.shutdown
    }

    /// Whether any `TypecheckDone` module still needs object codegen — not yet
    /// done and not currently claimed by a nice worker. This is the EXACT
    /// predicate `take_object_codegen` / `try_take_object_codegen` scan for,
    /// extracted so [`Self::park_nice_worker`] can re-check it under the lock
    /// before parking (the S95 window-#2 lost-wakeup fix). Keeping it a single
    /// shared predicate prevents the park-time check from drifting from the
    /// claim-time scan (Principle 7 single-source-of-truth).
    fn has_pending_object_work_locked(state: &SchedulerState) -> bool {
        state.typecheck_done.iter().any(|module| {
            state
                .modules
                .get(module)
                .map(|ms| !ms.object_done && !ms.object_working)
                .unwrap_or(false)
        })
    }

    /// Re-enqueue a module for nice-worker object codegen after its live
    /// symbol table changed (S101 R18 fix — the deterministic final persist).
    ///
    /// Called by the session after every defining REPL turn
    /// (`regenerate_backing_file`) and by the dependent-recompilation
    /// transaction for each touched module: clears `object_done` so the
    /// `.o`/`.meta.json` pair is rewritten from the CURRENT live table, and
    /// wakes the nice workers. The `/quit` path's existing
    /// `wait_object_complete` then genuinely waits for the rewrite, making
    /// the post-quit `.meta` deterministically reflect the last defining
    /// turns (spine §5.6 pin (ii) — faithful write after every
    /// redefinition; formerly the rewrite depended on an incidental
    /// watcher-reload race and was abandoned at shutdown).
    ///
    /// No-op for modules the scheduler doesn't know or whose typecheck has
    /// not reached a terminal pool (nothing coherent to persist yet). A
    /// module already claimed by a nice worker (`object_working`) is simply
    /// marked not-done: when the in-flight write completes it becomes
    /// claimable again and is rewritten with the newer table.
    pub fn mark_object_stale(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        let Some(ms) = state.modules.get_mut(module) else {
            return;
        };
        if !ms.pool.is_terminal_typecheck() {
            return;
        }
        ms.object_gen += 1;
        ms.object_done = false;
        // A completed module left the object-claim scan's view; restore it.
        if ms.pool == ModulePool::Complete {
            ms.pool = ModulePool::TypecheckDone;
        }
        if !state.typecheck_done.contains(module) {
            state.typecheck_done.push_back(module.clone());
        }
        drop(state);
        self.object_work_available.notify_all();
    }

    /// Object codegen for a module is complete (.o written).
    /// Clears `object_working`, sets `object_done`. If completion
    /// condition is met, moves to Complete.
    pub fn notify_object_codegen_complete(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        let mut still_stale = false;
        if let Some(ms) = state.modules.get_mut(module) {
            ms.object_working = false;
            // S101 R18 lost-update fix: a `mark_object_stale` that landed
            // WHILE this write was in flight bumped `object_gen` past the
            // claim snapshot — the completed write observed an older table,
            // so the module must stay not-done (re-claimable) rather than
            // have the pending rewrite silently clobbered.
            ms.object_done = ms.object_claimed_gen == ms.object_gen;
            still_stale = !ms.object_done;
        }
        Self::try_complete_locked(&mut state, module);

        // Wake wait_object_complete callers — and, when the module went
        // stale mid-write, the nice workers (so the rewrite is picked up
        // even if every worker is parked).
        drop(state);
        self.completion.notify_all();
        if still_stale {
            self.object_work_available.notify_all();
        }
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
            Some(ms) => (ms.pool.is_terminal_typecheck(), Some(ms.pool)),
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

    /// Every registered module whose signatures are published — i.e. in a
    /// TERMINAL typecheck pool (`TypecheckDone`/`Complete`). Used by the
    /// importable-index arm-time sweep (E3, `resolve-home-enumeration.md` §4): a
    /// module already loaded/registered at REPL-startup arm has its public
    /// symbols read straight from the live table into the `/search` index (the
    /// loaded-module feed). Snapshot under the state lock; the caller reads the
    /// live tables (whose publication happens-before the terminal transition per
    /// Invariant PP).
    pub(crate) fn terminal_typecheck_modules(&self) -> Vec<ModuleFullPath> {
        let state = self.lock();
        state
            .modules
            .iter()
            .filter(|(_, ms)| ms.pool.is_terminal_typecheck())
            .map(|(m, _)| m.clone())
            .collect()
    }

    // -----------------------------------------------------------------------
    // Signature pre-pass barrier (S93, `signature-body-prepass.md` §3.1)
    // -----------------------------------------------------------------------

    /// Whether module `m`'s signatures are wholly published.
    ///
    /// `true` when the module has reached a terminal typecheck state
    /// (`TypecheckDone`/`Complete`), OR is not registered with the scheduler at
    /// all (a compiler-seeded synthetic module — `primitives`, `macros` — whose
    /// Defs the symbol table already holds). Mirrors [`Self::is_typechecked`]'s
    /// None-as-ready fallthrough.
    ///
    /// **The terminal pool transition IS the publication edge (S93 / /arch
    /// ruling).** `notify_typecheck_done` runs post-`finalize_cluster`, after the
    /// cluster's Defs are installed in `symbol_tables[m]`; the
    /// release-acquire chain on the state lock carries `pool → TypecheckDone`
    /// happens-after publication. So there is no separate `signatures_ready` bit —
    /// reading the pool directly is correct (the live-dead bit + its explicit
    /// `register_module_signatures` driver were removed, FIXME 0452 / /arch
    /// option i).
    fn signatures_ready_locked(state: &SchedulerState, m: &ModuleFullPath) -> bool {
        match state.modules.get(m) {
            Some(ms) => ms.pool.is_terminal_typecheck(),
            None => true,
        }
    }

    /// Park the caller until **every** module in `closure` has its signatures
    /// published (the Phase-A barrier gate). Returns when the barrier opens, or
    /// `Err` if any closure module failed.
    ///
    /// Workers do NOT poll — they wait inside the scheduler on the `completion`
    /// condvar (woken by `notify_typecheck_done` / `notify_module_failed` /
    /// `shutdown`). When this returns `Ok`, the state-lock release-acquire chain
    /// carries the happens-before edge from each dependency's terminal-pool
    /// transition (its publication edge — see [`Self::signatures_ready_locked`])
    /// to here, and on to the body's read of `symbol_tables[sibling]` (§3.3). No
    /// body is admitted to Phase B until this opens, so the §3.6 publish/read
    /// window cannot occur.
    pub fn await_signature_barrier(
        &self,
        closure: &ClosureOrder,
    ) -> Result<(), SchedulerError> {
        let mut state = self.lock();
        loop {
            if state.shutdown {
                return Ok(());
            }
            // Fail fast if any closure module errored — otherwise we would park
            // forever on a dep that will never become ready.
            for m in &closure.order {
                if let Some(ms) = state.modules.get(m)
                    && ms.pool == ModulePool::Failed
                {
                    return Err(SchedulerError::ModuleFailed {
                        module: m.clone(),
                        message: ms
                            .error
                            .as_ref()
                            .map(|e| e.to_string())
                            .unwrap_or_else(|| "unknown error".to_string()),
                    });
                }
            }
            let all_ready = closure
                .order
                .iter()
                .all(|m| Self::signatures_ready_locked(&state, m));
            if all_ready {
                return Ok(());
            }
            state = self
                .completion
                .wait(state)
                .unwrap_or_else(|e| e.into_inner());
        }
    }

    /// Atomic check-and-block at the body-boundary signature barrier (S93,
    /// Invariant PP — the requeue-gate predicate; BC §6 ruling B). This is the
    /// **single-lock** operation a **pool worker** uses at the body boundary, and
    /// the structural fix for the lost-wakeup Blocker (FIXME 0452 / /review).
    ///
    /// Under ONE state-lock acquisition: scan `closure.order` for the first
    /// member whose signatures are not yet published (not terminal — see
    /// [`Self::signatures_ready_locked`]). If found, atomically register `module`
    /// as a `"*"` whole-module waiter on that member (the `block_for_typecheck`
    /// requeue-kernel transition: move `module` to `TypecheckBlocked`, record the
    /// `blocked_on` edge, run the acyclicity check) and return `Ok(Some(member))`.
    /// If every member is already terminal, return `Ok(None)` (barrier open — the
    /// body proceeds). On a transitive cycle back to `module`, fail `module` and
    /// return `Err` (the standard circular-dependency error).
    ///
    /// A pool worker MUST NOT park its thread on the barrier (that would
    /// re-introduce the starvation/deadlock axis the S78 free-back-to-pool model
    /// deleted): on `Some(member)` it surfaces a `Gap` and frees back to the
    /// pool; the scheduler requeues its body work when `member` reaches
    /// `notify_typecheck_done` → `try_unblock_locked`. The eval thread — the one
    /// genuine waiter, which consumes no pool slot — uses the blocking
    /// [`Self::await_signature_barrier`] instead.
    ///
    /// **Why one lock (the lost-wakeup fix).** The former two-call shape —
    /// `first_unready_closure_member` (lock, scan, release) THEN `block_dep` →
    /// `block_for_typecheck` (re-lock, register the waiter) — had a window: if
    /// `member` reached `notify_typecheck_done` *between* the two locks, its
    /// waiter-sweep ran BEFORE `module` registered as a waiter, so `module` parked
    /// in `TypecheckBlocked` on an already-terminal member that never notifies
    /// again → a permanent lost wakeup (the exact deadlock class this gate claims
    /// to eliminate by construction). Scanning and registering under the same lock
    /// closes the window: `notify_typecheck_done(member)` either runs entirely
    /// before this call (the scan sees `member` terminal and skips it) or entirely
    /// after (it sweeps the waiter this call just registered). There is no gap.
    pub fn block_on_first_unready_closure_member(
        &self,
        module: &ModuleFullPath,
        closure: &ClosureOrder,
    ) -> Result<Option<ModuleFullPath>, CranelispError> {
        let mut state = self.lock();
        let member = closure
            .order
            .iter()
            .find(|m| !Self::signatures_ready_locked(&state, m))
            .cloned();
        let Some(member) = member else {
            return Ok(None); // barrier open — every member is terminal
        };

        observability::record_module_event(
            SchedulerTraceTag::ModuleStateBlocked,
            module.as_ref(),
        );
        // Inline the `block_for_typecheck` transition under THIS lock — the scan
        // above and this waiter registration must not have a gap.
        Self::set_pool_locked(&mut state, module, ModulePool::TypecheckBlocked);
        if let Some(ms) = state.modules.get_mut(module) {
            ms.blocked_on = Some(member.clone());
        }
        // Acyclicity check FIRST (before adding the waiter), mirroring
        // `block_for_typecheck`: a transitive cycle back to `module` fails it
        // with the standard diagnostic.
        if let Some(cycle) = Self::detect_cycle_locked(&state, module) {
            let cycle_str = cycle
                .iter()
                .map(|m| m.to_string())
                .collect::<Vec<_>>()
                .join(" -> ");
            let msg = format!("circular dependency detected: {}", cycle_str);
            Self::notify_module_failed_locked(
                &mut state,
                module,
                CranelispError::ModuleError {
                    message: msg.clone(),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                },
            );
            return Err(CranelispError::ModuleError {
                message: msg,
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        }
        Self::add_waiter_locked(
            &mut state,
            &member,
            &Symbol::from("*"),
            Waiter {
                module: module.clone(),
                need: WaitKind::Typecheck,
            },
        );
        Ok(Some(member))
    }

    // -----------------------------------------------------------------------
    // Per-cluster static-closure memo (S93 Task-3 — recover redundant IO)
    // -----------------------------------------------------------------------

    /// Read the memoised static import closure for `module` if its fingerprint
    /// matches (S93 Task-3 per-cluster cache). `Some(closure)` on a hit — the
    /// same cluster (same direct-import root set) as a prior attempt — `None` on
    /// a miss (no memo yet, the fingerprint differs, or the module is
    /// unregistered).
    ///
    /// The closure walk in `dependency::static_import_closure` does an
    /// `fs::read_to_string` + `parse` for every transitively-imported module and
    /// runs at the top of EVERY `process_cluster_once` pass — including every
    /// retry-from-top a dependency gap triggers. This memo makes that walk run
    /// ONCE per cluster instead of once per attempt.
    pub fn cached_static_closure(
        &self,
        module: &ModuleFullPath,
        fingerprint: u64,
    ) -> Option<ClosureOrder> {
        let state = self.lock();
        state
            .modules
            .get(module)
            .and_then(|ms| match &ms.static_closure_memo {
                Some((fp, closure)) if *fp == fingerprint => Some(closure.clone()),
                _ => None,
            })
    }

    /// Memoise the static import closure for `module` under `fingerprint` (S93
    /// Task-3). Subsequent attempts of the same cluster (retry-from-top after a
    /// dependency gap) reuse it instead of re-walking + re-parsing the transitive
    /// import tree. Reset by `re_register_module` (source changed → re-walk).
    /// No-op for an unregistered module.
    pub fn cache_static_closure(
        &self,
        module: &ModuleFullPath,
        fingerprint: u64,
        closure: &ClosureOrder,
    ) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            ms.static_closure_memo = Some((fingerprint, closure.clone()));
        }
    }

    /// Test accessor (S93 §6): force a registered module into `TypecheckWorking`
    /// (claimed, not yet done) without going through `take_priority_work` — so a
    /// barrier test can model an in-flight orchestrator that has NOT yet
    /// published signatures. No-op for an unregistered module.
    #[cfg(test)]
    pub fn force_typecheck_working_for_test(&self, m: &ModuleFullPath) {
        let mut state = self.lock();
        Self::set_pool_locked(&mut state, m, ModulePool::TypecheckWorking);
    }

    /// Record a `holder → dep` cycle-detection edge **without** moving `holder`
    /// to `TypecheckBlocked` (S93, Invariant SW — the structural replacement for
    /// the `eval_owned` flag).
    ///
    /// The eval thread (REPL) is the **sole** orchestrator of its entry module:
    /// it drives the entry's body itself and waits on a gapping dependency via
    /// `wait_module_inmem_complete_blocking`, then re-runs the cluster from the
    /// top. Unlike a pool worker (which moves the gapping module to
    /// `TypecheckBlocked` so the scheduler can requeue it), the eval thread must
    /// NOT let its entry become re-claimable by a pool worker — that is the B1
    /// dual-orchestration this retires. So the entry keeps its terminal pool
    /// (never enters a typecheck queue) while the eval thread drives.
    ///
    /// This call records the forward `blocked_on` edge so the **reverse**-
    /// direction cycle check still fires (if `dep`, while compiling, imports
    /// `holder` back, `block_for_typecheck(dep, holder)` will detect the cycle
    /// against this edge and fail `dep` — the eval thread's wait then surfaces a
    /// clean circular-dependency error). On a cycle it returns `Err` WITHOUT
    /// failing `holder` (the REPL entry is not a session-killer — a bad import
    /// is an eval error). The edge is cleared by the eval thread after its wait
    /// (`register_dep_for_eval`) so no stale edge lingers on the terminal entry.
    /// No-op for an unregistered module.
    pub fn register_dep_edge_for_cycle_check(
        &self,
        holder: &ModuleFullPath,
        dep: &ModuleFullPath,
    ) -> Result<(), CranelispError> {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(holder) {
            ms.blocked_on = Some(dep.clone());
        }
        if let Some(cycle) = Self::detect_cycle_locked(&state, holder) {
            // Clear the edge — `holder` is eval-owned and is NOT failed.
            if let Some(ms) = state.modules.get_mut(holder) {
                ms.blocked_on = None;
            }
            let cycle_str = cycle
                .iter()
                .map(|m| m.to_string())
                .collect::<Vec<_>>()
                .join(" -> ");
            return Err(CranelispError::ModuleError {
                message: format!("circular dependency detected: {}", cycle_str),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        }
        Ok(())
    }

    /// Clear a module's `blocked_on` cycle-check edge (S93, Invariant SW). The
    /// eval thread calls this after waiting on a dependency it recorded via
    /// [`Self::register_dep_edge_for_cycle_check`], so the terminal entry module
    /// carries no stale forward edge into the next REPL form. No-op when unset
    /// or unregistered.
    pub fn clear_dep_edge(&self, holder: &ModuleFullPath) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(holder) {
            ms.blocked_on = None;
        }
    }

    /// Drop a module's stored cluster sexps (S93, Invariant SW). Called by the
    /// REPL once the eval thread takes over the entry module: the entry sits in
    /// its terminal pool, the eval thread owns its content via its own
    /// `CheckState`, so the scheduler-held startup sexps are no longer needed —
    /// dropping them means even a stray dispatch would find an empty cluster.
    /// No-op for an unregistered module.
    pub fn release_entry_sexps(&self, module: &ModuleFullPath) {
        let mut state = self.lock();
        if let Some(ms) = state.modules.get_mut(module) {
            ms.sexps = None;
        }
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

    /// Render a full snapshot of scheduler coordination state for diagnostics
    /// (the SIGUSR1 lost-wakeup dump — `src/sched_dump.rs`). For every module:
    /// its pool, the `blocked_on` forward edge, the inmem/object flags, and the
    /// waiter list it holds (who is waiting on which of ITS symbols, and for
    /// what). Plus the three priority/done queue contents and the shutdown flag.
    ///
    /// This is the asset that pins a lost wakeup: a module stranded in
    /// `TypecheckBlocked` with a `blocked_on` edge to a module that is already
    /// terminal (`TypecheckDone`/`Complete`) — yet NOT present in that module's
    /// waiter list (the sweep already ran) and NOT in any queue — is a lost
    /// wakeup. The dump makes that triangle directly visible.
    ///
    /// Acquires the state lock — MUST be called from a normal thread (the
    /// watchdog), NEVER from inside a signal handler (the handler only flips an
    /// atomic flag; `src/sched_dump.rs §safety`).
    pub fn dump_state_to_string(&self) -> String {
        use std::fmt::Write as _;
        let state = self.lock();
        let mut s = String::with_capacity(2048);
        let _ = writeln!(
            s,
            "=== CompileScheduler state dump (shutdown={}, modules={}) ===",
            state.shutdown,
            state.modules.len(),
        );
        let _ = writeln!(
            s,
            "  queues: typecheck_first={:?} typecheck_next={:?} typecheck_done={:?}",
            state.typecheck_first.iter().map(|m| m.as_ref()).collect::<Vec<_>>(),
            state.typecheck_next.iter().map(|m| m.as_ref()).collect::<Vec<_>>(),
            state.typecheck_done.iter().map(|m| m.as_ref()).collect::<Vec<_>>(),
        );
        // Stable iteration order for deterministic dumps across runs.
        let mut paths: Vec<&ModuleFullPath> = state.modules.keys().collect();
        paths.sort_by(|a, b| a.as_ref().cmp(b.as_ref()));
        for path in paths {
            let ms = &state.modules[path];
            let cached = state.cached_modules.contains(path);
            let _ = writeln!(
                s,
                "  [{:?}] {} blocked_on={:?} inmem_done={} inmem_claimed={} \
                 object_done={} object_working={} cached={} sexps={} error={}",
                ms.pool,
                path.as_ref(),
                ms.blocked_on.as_ref().map(|m| m.as_ref()),
                ms.inmem_done,
                ms.inmem_claimed,
                ms.object_done,
                ms.object_working,
                cached,
                ms.sexps.is_some(),
                ms.error.is_some(),
            );
            for (sym, waiters) in &ms.waiters {
                for w in waiters {
                    let _ = writeln!(
                        s,
                        "        waiter-on-symbol {:?}: {} needs {:?}",
                        sym.as_ref(),
                        w.module.as_ref(),
                        w.need,
                    );
                }
            }
        }
        // Lost-wakeup heuristic: flag any TypecheckBlocked module whose
        // blocked_on target is already terminal AND does not list it as a
        // waiter. That triangle is the lost-wakeup signature.
        for path in state.modules.keys() {
            let ms = &state.modules[path];
            if ms.pool != ModulePool::TypecheckBlocked {
                continue;
            }
            let Some(dep) = &ms.blocked_on else { continue };
            let dep_terminal = Self::signatures_ready_locked(&state, dep);
            let listed_as_waiter = state
                .modules
                .get(dep)
                .map(|d| {
                    d.waiters
                        .values()
                        .flatten()
                        .any(|w| &w.module == path)
                })
                .unwrap_or(false);
            if dep_terminal && !listed_as_waiter {
                let _ = writeln!(
                    s,
                    "  !! LOST-WAKEUP SUSPECT: {} is TypecheckBlocked on {} which is \
                     terminal but does NOT list it as a waiter (sweep already ran)",
                    path.as_ref(),
                    dep.as_ref(),
                );
            }
        }
        s
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

    /// Try to unblock a module. If the module is TypecheckBlocked and has no
    /// remaining wait conditions, move it to TypecheckFirst (if it has waiters
    /// itself) or TypecheckNext (if not) and requeue it for a worker.
    ///
    /// S78: this is the requeue half of the in-call-stack dependency protocol.
    /// When the dep a module blocked on completes, `notify_typecheck_done`
    /// sweeps its waiters and calls this to re-enqueue each. The worker that
    /// pops the requeued module reads its cluster sexps off `ModuleState`
    /// (`dispatch_typecheck_locked`) and re-runs the cluster from the top
    /// against now-larger live state. The former `eval_in_flight` push-gate
    /// (Sprint 61 H5 closure) is GONE — the in-call-stack model keeps each
    /// cluster's in-progress state on its owning stack frame, so there is no
    /// shared in-progress state for a racing worker to read, and the REPL-eval
    /// thread no longer needs to suppress the worker requeue (OQ-3; validated
    /// by the H5-replay gate staying green under stress after this deletion).
    fn try_unblock_locked(
        state: &mut SchedulerState,
        module: &ModuleFullPath,
    ) {
        let Some(ms) = state.modules.get(module) else { return };
        // S93 Invariant SW: the entry module's single-orchestrator property is
        // structural, not a flag. The eval thread NEVER moves its entry to
        // `TypecheckBlocked` (it records a cycle-check edge via
        // `register_dep_edge_for_cycle_check` and drives its own retry while the
        // entry stays in its terminal pool). So this `pool != TypecheckBlocked`
        // guard already makes a stray requeue of the entry impossible — there is
        // no second orchestrator to suppress, and the retired `eval_owned`
        // early-return is gone (claimable XOR owned, by construction).
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

        observability::record_module_event(
            SchedulerTraceTag::ModuleStateUnblocked,
            module.as_ref(),
        );
    }

    // `module_pool_for_test` / `force_typecheck_blocked_for_test` /
    // `try_unblock_for_test` — deleted in S78 Step 3. Their only callers were
    // the `eval_in_flight` push-gate unit tests, which retired with the gate.

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

// ---------------------------------------------------------------------------
// Signature/body pre-pass — static dependency closure + cycle error (S93)
//
// `design/int/signature-body-prepass.md` §3.1 / §7 step 1. The barrier's
// Phase-A unit of work is the *static* import closure: the modules a cluster
// transitively imports, computed purely from Pass-0 structural import
// declarations (no inference needed to know WHICH modules the closure
// contains). A cycle in that closure has no topological order — it is the
// D0030 mutual-import disposition (§4): mutual imports are a compile-time
// cycle-error, NOT compiled.
// ---------------------------------------------------------------------------

/// A topologically ordered static import closure — leaves (deepest deps) first,
/// the root last. Computed by [`dependency_closure`] from Pass-0 import
/// declarations. The ordering guarantee: for any module `m` in `order`, every
/// module `m` imports appears *before* `m`. This is the order in which Phase-A
/// signature registration drives the closure so a dependent's body never reads
/// a not-yet-registered sibling (the §3.3 ordering guarantee).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosureOrder {
    /// Modules in dependency (topological) order: imports precede importers.
    pub order: Vec<ModuleFullPath>,
}

/// A static import cycle — the closure has no topological order, so the
/// signature pre-pass cannot register it (mutual imports are not compiled;
/// `signature-body-prepass.md` §4 ratified user ruling). Carries the modules on
/// the back-edge path for a clean cycle diagnostic at the import site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CycleError {
    /// The modules forming the cycle, in discovery order, terminated by the
    /// repeated back-edge module (e.g. `[a, b, a]` for a 2-cycle).
    pub cycle: Vec<ModuleFullPath>,
}

impl CycleError {
    /// Render the cycle as `a -> b -> a` for a diagnostic message.
    pub fn render(&self) -> String {
        self.cycle
            .iter()
            .map(|m| m.to_string())
            .collect::<Vec<_>>()
            .join(" -> ")
    }
}

/// Topologically order the static import closure rooted at `root`.
///
/// `import_decls` is the adjacency list: each entry `(m, deps)` names a module
/// `m` and the modules it directly imports (its Pass-0 import declarations).
/// Modules reachable from `root` but absent from `import_decls` are treated as
/// leaves (no outgoing edges) — e.g. already-loaded or compiler-seeded modules
/// whose decls the caller did not enumerate.
///
/// Returns [`ClosureOrder`] (leaves first, `root` last) on success, or
/// [`CycleError`] when a back-edge is found (the D0030 disposition — §4).
///
/// Pure over the edge list (no scheduler state). This is the static-graph
/// analogue of [`CompileScheduler::detect_cycle_locked`], which detects cycles
/// on the *live* `blocked_on` graph; here the graph is the *declared* import
/// graph, known before any body typechecks.
pub fn dependency_closure(
    root: &ModuleFullPath,
    import_decls: &[(ModuleFullPath, Vec<ModuleFullPath>)],
) -> Result<ClosureOrder, CycleError> {
    let adjacency: HashMap<&ModuleFullPath, &[ModuleFullPath]> = import_decls
        .iter()
        .map(|(m, deps)| (m, deps.as_slice()))
        .collect();

    // Three-colour DFS: White (unvisited) / Gray (on the current stack) /
    // Black (finished). A Gray re-visit is a back-edge → cycle. Post-order
    // emission yields a topological order with imports before importers.
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        Gray,
        Black,
    }
    let mut colour: HashMap<ModuleFullPath, Colour> = HashMap::new();
    let mut order: Vec<ModuleFullPath> = Vec::new();
    // Explicit stack of (node, parent-path-prefix-len) to recover the cycle
    // path without recursion (deep closures must not blow the call stack).
    let mut path: Vec<ModuleFullPath> = Vec::new();
    // Work stack entries: Enter(node) pushes children; Exit(node) emits.
    enum Step {
        Enter(ModuleFullPath),
        Exit(ModuleFullPath),
    }
    let mut work: Vec<Step> = vec![Step::Enter(root.clone())];

    while let Some(step) = work.pop() {
        match step {
            Step::Enter(node) => {
                match colour.get(&node) {
                    Some(Colour::Black) => continue, // already finished
                    Some(Colour::Gray) => {
                        // Back-edge — reconstruct the cycle from `path`.
                        let start = path.iter().position(|m| *m == node)
                            .unwrap_or(0);
                        let mut cycle: Vec<ModuleFullPath> =
                            path[start..].to_vec();
                        cycle.push(node);
                        return Err(CycleError { cycle });
                    }
                    None => {}
                }
                colour.insert(node.clone(), Colour::Gray);
                path.push(node.clone());
                work.push(Step::Exit(node.clone()));
                if let Some(deps) = adjacency.get(&node) {
                    for dep in deps.iter() {
                        if colour.get(dep) != Some(&Colour::Black) {
                            work.push(Step::Enter(dep.clone()));
                        }
                    }
                }
            }
            Step::Exit(node) => {
                // Only emit/pop on the first Exit for this node.
                if colour.get(&node) == Some(&Colour::Gray) {
                    colour.insert(node.clone(), Colour::Black);
                    // Pop the matching path entry (it is the last occurrence).
                    if let Some(pos) = path.iter().rposition(|m| *m == node) {
                        path.remove(pos);
                    }
                    order.push(node);
                }
            }
        }
    }

    Ok(ClosureOrder { order })
}

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
mod tests;
