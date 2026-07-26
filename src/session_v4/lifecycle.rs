// session_v4::lifecycle — the session lifecycle impl (S87 §2.1).
//
// `impl CompilerSession` — construct (`new`), accessors, module registration,
// watcher reload, link, shutdown/Drop — plus `populate_ring0_got_slots` (a
// `new`-helper). This is the residual responsibility set `src/CLAUDE.md
// §"Session/REPL module decomposition"` names for the session: one coherent
// concern (the session's own lifetime + the module-graph operations it owns)
// and the bulk of the file. The `CompilerSession`/`SharedState` struct
// definitions live in the parent (`session_v4.rs`); this is a sibling module
// carrying additional `impl CompilerSession` blocks (the same proven pattern as
// `eval.rs`/`repl.rs`). Moved verbatim from `session_v4.rs` (S87 §2.1), with
// `new` decomposed into phase-helpers (S87 §3.2).

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::{Arc, Mutex};

use cranelisp_types::{
    CranelispError, ErrorLocation, FQSymbol, ModuleEntry, ModuleFullPath, Sexp, Span, Symbol, Type,
    Warning,
};

use cranelisp_typecheck::CheckState;

use crate::code::{Code, SessionSymbolTable};
use crate::scheduler::CompileScheduler;

use super::{
    CompilerSession, FailedForm, ModuleIntroductionOutcome, SessionSettings, SharedState,
    SymbolCategory, SymbolInfo, TestRunnerState, dedup_platform_names_preserving_order,
    nice_worker_loop, resolve_priority_worker_count,
};

/// One read of the entry module's `main` entry (`read_main_entry`): the
/// callable address, the declared result type, and the code lifetime owner.
///
/// These three travel together deliberately — the result owner's release
/// target must be paired with the retention owner of the code that produced
/// the result (`design/int/result-owner.md` §3.2 step 3), and the result type
/// must come from the same read that produced the pointer (§4.3), not from a
/// second lookup that could fall back.
struct MainEntryRead {
    code_ptr: *const u8,
    result_type: Type,
    code_owner: Option<Code>,
    /// `main`'s `codegen_view` body type — the release key backend itself
    /// computed its result root from (`design/int/result-owner.md` §4.3).
    codegen_result_ty: Option<cranelisp_types::ConcreteType>,
}

/// Pillar-3 (S91): bounded grace period at shutdown for the in-flight
/// importable-symbol burn-down to drain (best-effort, never a correctness
/// gate). Keeps shutdown prompt for a large reachable set.
const SHUTDOWN_INDEX_SETTLE_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(3);

/// Poll interval while waiting on the shutdown burn-down settle.
const SHUTDOWN_INDEX_SETTLE_POLL: std::time::Duration = std::time::Duration::from_millis(5);

impl CompilerSession {
    /// Create a new compiler session (pipeline-v4.md §5).
    ///
    /// Spawns `priority_workers` persistent priority worker threads and
    /// `nice_workers` persistent nice worker threads. Workers park on the
    /// scheduler's condvars and process work for the session lifetime;
    /// `shutdown()` (called from `Drop`) joins them all. Sprint 57 Wave 4
    /// G9 per `design/int/persistent-workers.md` §4.1.
    ///
    /// The effective priority worker count is derived from
    /// `settings.priority_workers`: values of 0 are interpreted as
    /// "auto-detect" (`available_parallelism()-1`, clamped to `[1, 8]`);
    /// explicit values are clamped to `[1, 8]`. Tests pass
    /// `priority_workers: 1` for determinism.
    pub fn new(settings: SessionSettings, project_root: PathBuf, entry_module_name: &str) -> Self {
        // Lib dirs: stdlib location(s), NOT including project_root.
        // Project root is tier 2 in §8.11.2, searched separately.
        let lib_dirs = crate::session_setup::assemble_lib_dirs(&project_root);

        // Platform dirs: extra search locations from env var (§8.11.5).
        let platform_dirs = crate::session_setup::assemble_platform_dirs(&project_root);

        let object_cache = Self::build_object_cache(&settings, &project_root);

        // Priority-worker count: 0 = auto-detect, else explicit. Clamp to
        // [1, 8] per `persistent-workers.md` §5.1.
        let priority_workers = resolve_priority_worker_count(settings.priority_workers);
        let nice_workers = settings.nice_workers;

        // D1 ruling §4: capture the run-mode before `settings` is consumed
        // below; it is carried on `SharedState` as the explicit REPL-vs-batch
        // signal (introspection gating + layout-hash gate).
        let run_mode = settings.run_mode;

        let next_type_id = AtomicU32::new(0);
        // S78 §1: the ENTRY module is an ordinary module. `"user"` is only its
        // default NAME (passed by `main.rs` when no CLI target is given); it is
        // NOT a privileged identity. The session seeds the REPL cursor /
        // check-state / test-runner state off this name (below), and lazily
        // creates the entry module's symbol table by its real name so any
        // pre-first-input REPL introspection (`/list`, `/imports` on an empty
        // session) finds a table. The real entry registration (`register_module`
        // → `register_entry_module`) is name-agnostic and runs later; this seed
        // is just the create-by-real-name table the cursor points at.
        let entry_module = ModuleFullPath::from(entry_module_name);

        // Symbol-table seeding (S87 §3.2 — extracted). The strict mount order
        // (entry table → primitives `into_concrete` mount → synthetic mount →
        // Ring-0 GOT-populate) is preserved inside the helper.
        let symbol_tables = Self::seed_session_symbol_tables(&entry_module, &next_type_id);

        let shared = Self::build_shared_state(
            project_root,
            lib_dirs,
            platform_dirs,
            object_cache,
            symbol_tables,
            next_type_id,
            run_mode,
            &entry_module,
        );

        // Arm the SIGUSR1 scheduler-state dump if CRANELISP_SCHED_DUMP_ON_SIGUSR1
        // is set (permanent in-tree lost-wakeup diagnostic; no-op otherwise).
        // Registers this session's scheduler so `kill -USR1 <pid>` on a hung
        // child prints which module is stranded + on what — see src/sched_dump.rs.
        crate::sched_dump::arm_if_enabled(&shared);

        let (priority_worker_handles, nice_worker_handles) =
            Self::spawn_worker_threads(&shared, priority_workers, nice_workers);

        CompilerSession {
            shared,
            error_modules: HashSet::new(),
            failed_forms: HashMap::new(),
            watcher: None,
            worker_pool: crate::worker_pool::WorkerPool::new(
                priority_worker_handles,
                nice_worker_handles,
                nice_workers,
            ),
            // S78 §1: the REPL cursor + carry-forward CheckState start at the
            // ENTRY module (its real name), not a hardcoded "user".
            current_repl_module: entry_module.clone(),
            repl_check_state: Mutex::new(Some(CheckState::new(entry_module.clone()))),
            repl_input_active: std::sync::Arc::new(AtomicBool::new(false)),
            warnings: Vec::new(),
            pending_cascade_reports: Vec::new(),
            entry_module,
            // Agent starts unconfigured; `enable_agent` wires it in REPL mode
            // when `--agent` is set + the `agent` feature is built (S88 W3).
            #[cfg(feature = "agent")]
            agent: None,
        }
    }

    /// Enable the embedded agent for this (REPL) session (Sprint 88 Phase 5
    /// Wave 3). Threads the resolved `--agent` runtime toggle (`main.rs` S1
    /// `_agent_enabled`) into the agent state: selects + constructs the runtime
    /// provider (anthropic / ollama / stub by config — `agent.md §6.3/§6.4`),
    /// or leaves the agent dormant when no provider is reachable. The agent is
    /// REPL-only, so this is called from `main.rs`'s REPL arm only. Idempotent
    /// is not required (called once at startup).
    #[cfg(feature = "agent")]
    pub fn enable_agent(&mut self, enabled: bool, auto_accept: bool) {
        self.agent = Some(crate::agent::provider::build_agent_state_with(
            enabled,
            auto_accept,
        ));
    }

    /// Arm the Pillar-3 importable-symbol burn-down (S91, `agent.md §25.5`).
    /// REPL-only by construction (R17): `main.rs` calls this from the REPL arm
    /// ONLY. Enumerates the reachable set (lib-path ∪ project-root) onto the
    /// `IndexModule` worklist and wakes the nice workers, which drain it BEHIND
    /// object codegen (index warm-up in the slack). Idempotent. In
    /// `--run`/`--link`/`--release` this is never called, so the worklist is
    /// never enumerated and no index-driven `.meta` write ever fires
    /// (batch-mode-inert, R9).
    pub fn arm_importable_index(&self) {
        crate::session_v4::index_worker::arm_burndown(&self.shared);
    }

    /// One-shot poll for the `search index complete.` completion notice
    /// (spec §17.19.3, timing (b), S108). Returns `true` EXACTLY ONCE — when the
    /// Pillar-3 burn-down has completed AND a "indexing N modules…" not-ready
    /// note was shown this session (timing (b)). The `main.rs` REPL read loop
    /// polls this at the clean prompt boundary and, on `true`, prints the
    /// notice; the single-writer discipline (only the main/eval thread prints)
    /// and the note-shown gate keep every non-TTY golden byte-identical.
    pub fn take_search_index_completion_notice(&self) -> bool {
        self.shared.importable_indices.take_completion_notice()
    }

    /// `new` phase (S87 §3.2): build the on-disk `ObjectCache` facade.
    ///
    /// Sprint 67 Cluster B sub-fire 3: cache directory + state are folded into
    /// the `ObjectCache` facade. `Some(_)` when caching is enabled; `None`
    /// under `--no-cache`. The directory is created eagerly because the worker
    /// writes happen on the hot path.
    fn build_object_cache(
        settings: &SessionSettings,
        project_root: &Path,
    ) -> std::sync::Arc<crate::cache::ObjectCache> {
        let cache_dir_opt = if settings.no_cache {
            None
        } else {
            let dir = project_root.join(".cranelisp-cache");
            let _ = std::fs::create_dir_all(&dir);
            Some(dir)
        };
        let cache_state = cache_dir_opt
            .as_ref()
            .map(|d| crate::session_setup::CacheState::new(d.clone()));
        std::sync::Arc::new(crate::cache::ObjectCache::new(cache_dir_opt, cache_state))
    }

    /// `new` phase (S87 §3.2): construct + seed the session's per-module symbol
    /// tables.
    ///
    /// The mount ORDER is load-bearing and preserved exactly: (1) create the
    /// entry module's table by its REAL name; (2) `into_concrete`-mount the
    /// static `PRIMITIVES_TABLE`; (3) `mount_synthetic_modules`; (4)
    /// `populate_ring0_got_slots`. Fresh type vars for the polymorphic
    /// ADTs/primitive are allocated from `next_type_id`, advancing the
    /// high-water mark monotonically.
    fn seed_session_symbol_tables(
        entry_module: &ModuleFullPath,
        next_type_id: &AtomicU32,
    ) -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable> =
            dashmap::DashMap::new();

        // S78 §1: create the entry module's table by its REAL name (never a
        // hardcoded "user" literal). Special forms mount at root "" and
        // synthetic modules mount in `mount_synthetic_modules` — neither needs
        // a pre-seeded entry table; this exists only so pre-first-input REPL
        // introspection has a table for the cursor's module.
        cranelisp_types::ensure_module_exists(&symbol_tables, entry_module);

        // S68 Wave 4 (Decision 0048): Arc-clone the statically-constructed
        // `PRIMITIVES_TABLE` into the session's symbol tables at
        // `ModuleFullPath::from("primitives")`. The session's primitives
        // module then *shares* the static `Arc<GotTable>` with every other
        // session in the process. `(*PRIMITIVES_TABLE).clone()` clones the
        // `SymbolTable<Code, ()>` by value; the inner `got: Arc<GotTable>`
        // field is an Arc-clone, so the underlying GotTable is shared with
        // the static. From this point on, primitives dispatch is functionally
        // equivalent to any other module via the standard cross-module
        // GOT-indirect call path.
        //
        // `mount_synthetic_modules` (next call) short-circuits the primitives-
        // module creation (its `if !contains_key` check finds the entry).
        // Subsequent `register_primitives` / `register_ring1_primitives` /
        // etc. `get_mut` the same module and *overwrite* the Symbol entries
        // by name — the typecheck-side metadata (scheme, docstring) reflects
        // the typecheck registry's view. The shared `Arc<GotTable>` carries
        // through unchanged because `register_primitives` mutates only the
        // session-local `next_got_slot` counter, allocating fresh slots that
        // `populate_ring0_got_slots` (called below) populates from the
        // static table's slot ↔ fn-ptr mapping. The dispatch invariant is
        // preserved: every primitive call lands on a GOT slot that holds
        // the static `extern "C" fn` ptr.
        // S76 (FIXME 0242-i): `PRIMITIVES_TABLE` is now `SymbolTable<(), ()>`;
        // concretise to the session `<Code, ()>` flavour via `into_concrete`
        // at the mount. The inner `got: Arc<GotTable>` is Arc-cloned, so the
        // session's primitives module shares the static GOT (slots already
        // populated with the Ring-0 shim addresses).
        symbol_tables.insert(
            ModuleFullPath::from("primitives"),
            (*cranelisp_primitives::PRIMITIVES_TABLE)
                .as_ref()
                .clone()
                .into_concrete::<Code, ()>(),
        );

        // S76 (FIXME 0242): the synthetic-module mount — int's reconstruction
        // of the deleted `cranelisp_typecheck::register_builtins` body. Seeds
        // special forms (root ""), intrinsic type names + Vec, the `macros`
        // module (Sexp/SList + sconcat), Option, IO (+ bind), Trace, and the
        // test infrastructure into the session tables. `primitives` is already
        // mounted above; this adds to it + the root "" + creates `macros`. It
        // does NOT touch the entry module (it is an ordinary module, seeded by
        // its real name above and registered name-agnostically later — S78 §1).
        // Fresh type vars for the polymorphic ADTs/primitive are allocated
        // from `next_type_id`, advancing the high-water mark monotonically.
        crate::bootstrap::mount_synthetic_modules(&symbol_tables, next_type_id);

        // Per FIXME 0174 + Decision 43: Ring 0 primitives (`add-i64`, `not`,
        // …) are now ordinary `ModuleEntry::Def` entries with `got_slot:
        // Some(_)`. Pair each name with its Rust shim address and write the
        // pointer into the primitives module's GOT slot so the standard
        // GOT-indirect dispatch path (and the mappable-path
        // `(let [f not] (f true))`) resolves correctly. Inline substitution
        // in backend remains a separate optimisation.
        populate_ring0_got_slots(&symbol_tables);

        symbol_tables
    }

    /// `new` phase (S87 §3.2): assemble the `Arc<SharedState>` + patch the
    /// `test_runner_state.tc_modules` single-writer pointer.
    ///
    /// The single-writer-pre-spawn invariant is preserved: this builds the Arc
    /// and patches the `tc_modules` pointer (via the `set_tc_modules` setter)
    /// BEFORE `spawn_worker_threads` is called by `new` — so no concurrent
    /// reader exists when the write happens.
    #[allow(clippy::too_many_arguments)]
    fn build_shared_state(
        project_root: PathBuf,
        lib_dirs: Vec<PathBuf>,
        platform_dirs: Vec<PathBuf>,
        object_cache: std::sync::Arc<crate::cache::ObjectCache>,
        symbol_tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
        next_type_id: AtomicU32,
        run_mode: super::RunMode,
        entry_module: &ModuleFullPath,
    ) -> Arc<SharedState> {
        // Sprint 66 Wave 3a-γ: build the session-wide TestRunnerState. The
        // `tc_modules` pointer is derived from the `symbol_tables` DashMap
        // owned by the Arc<SharedState> we're about to construct. Since
        // `SharedState` is held behind `Arc` for the session lifetime and
        // never moved, the pointer is stable. The `current_module` field is
        // a `Mutex` so `/mod` may update it without rebuilding the state.
        // S78 §1: seed off the ENTRY module name, not a hardcoded "user".
        // `tc_modules` is null until patched immediately after Arc construction
        // (via the `set_tc_modules` setter — S87 §2.2).
        let test_runner_state = Box::new(TestRunnerState::new(entry_module.clone()));

        let shared = Arc::new(SharedState {
            scheduler: CompileScheduler::new(),
            project_root,
            lib_dirs: Mutex::new(lib_dirs),
            platform_dirs: Mutex::new(platform_dirs),
            cache: object_cache,
            promote_nice_workers: AtomicBool::new(false),
            file_to_module: Mutex::new(HashMap::new()),
            symbol_tables,
            next_type_id,
            module_aliases: cranelisp_types::ModuleAliases::default(),
            prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
            // FIXME 0604 §2.2: the declared-export closure map starts empty;
            // populated per session by the `install_exports` seam.
            declared_exports: crate::imports::DeclaredExports::default(),
            typecheck_products: dashmap::DashMap::new(),
            // Sprint 58 Wave 3b: kept_jits / kept_linkers dissolved per
            // Decision 35; Arc retention now lives on each Code::Jit /
            // Code::Linker on `ModuleEntry::Def.code`.
            kept_dlls: Mutex::new(Vec::new()),
            // D1b: the introspection STORE is REPL-only — `Some(empty map)`
            // under `RunMode::Repl`, `None` in `--run`/`--link` (no allocation
            // in batch). Same `run_mode` carrier that gates population (D1 §4).
            introspection: run_mode
                .populates_introspection()
                .then(dashmap::DashMap::new),
            // Pillar-3 indices start empty + unarmed; the burn-down is armed at
            // REPL startup only (R17 — REPL-only by construction). In
            // `--run`/`--link`/`--release` the worklist is never enumerated.
            importable_indices: crate::session_v4::ImportableIndices::default(),
            // S101 R3 machinery: the broken registry + the session retention
            // pool (design/int/session-transaction.md §5.1/§6.1). Both start
            // empty; populated only by dev-session redefinition transactions.
            broken: dashmap::DashMap::new(),
            retained_code: Mutex::new(Vec::new()),
            fresh_jit_drop_glues: dashmap::DashMap::new(),
            run_mode,
            test_runner_state,
        });

        // Patch the `tc_modules` pointer inside `test_runner_state` to point
        // at `shared.symbol_tables`. Safe: `shared` is `Arc<SharedState>`,
        // never moved; the `symbol_tables` field has a stable address for
        // the session lifetime. The `Box<TestRunnerState>` itself sits inside
        // the `SharedState` struct, so a `&mut` through `Arc` would alias
        // shared state — instead we cast through a raw pointer to flip the
        // single `*const` field. This write happens exactly once, before any
        // worker thread is spawned (so before any reader observes the field).
        // SAFETY: single-writer, pre-spawn; no concurrent reader exists yet
        // (`spawn_worker_threads` runs strictly after this returns). The unsafe
        // raw-pointer write is encapsulated inside
        // `TestRunnerState::set_tc_modules` (S87 §2.2) — the field stays private
        // to `test_runner.rs`.
        unsafe {
            shared
                .test_runner_state
                .set_tc_modules(&shared.symbol_tables as *const _);
        }

        shared
    }

    /// `new` phase (S87 §3.2): spawn the persistent priority + nice worker
    /// threads.
    ///
    /// MUST run AFTER `build_shared_state` (so the `tc_modules` single-writer
    /// patch has completed before any worker observes the field — the
    /// single-writer-pre-spawn invariant). Returns the join handles for the
    /// `WorkerPool`.
    #[allow(clippy::type_complexity)]
    fn spawn_worker_threads(
        shared: &Arc<SharedState>,
        priority_workers: usize,
        nice_workers: usize,
    ) -> (
        Vec<std::thread::JoinHandle<()>>,
        Vec<std::thread::JoinHandle<()>>,
    ) {
        // Spawn persistent priority worker threads (Sprint 57 Wave 4 G9).
        // Workers park on `scheduler.priority_work_available` and process
        // modules until shutdown. Joined in `shutdown()` / `Drop`.
        let mut priority_worker_handles = Vec::with_capacity(priority_workers);
        for i in 0..priority_workers {
            let worker_shared = Arc::clone(shared);
            let handle = std::thread::Builder::new()
                .name(format!("priority-worker-{}", i))
                .spawn(move || {
                    crate::worker::priority_worker_loop_shared(&worker_shared);
                })
                .expect("failed to spawn priority worker thread");
            priority_worker_handles.push(handle);
        }

        // Spawn persistent nice worker threads for object codegen (.o files).
        // Workers park on scheduler condvar and wake when modules reach
        // TypecheckDone. They run for the session lifetime and are joined
        // in shutdown().
        let mut nice_worker_handles = Vec::with_capacity(nice_workers);
        for i in 0..nice_workers {
            let worker_shared = Arc::clone(shared);
            let handle = std::thread::Builder::new()
                .name(format!("nice-worker-{}", i))
                .spawn(move || {
                    nice_worker_loop(&worker_shared);
                })
                .expect("failed to spawn nice worker thread");
            nice_worker_handles.push(handle);
        }

        (priority_worker_handles, nice_worker_handles)
    }

    /// Convenience accessor: project root.
    pub fn project_root(&self) -> &Path {
        &self.shared.project_root
    }

    /// Convenience accessor: lib search directories (snapshot clone).
    pub fn lib_dirs(&self) -> Vec<PathBuf> {
        self.shared
            .lib_dirs
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Convenience accessor: platform DLL search directories (snapshot clone).
    pub fn platform_dirs(&self) -> Vec<PathBuf> {
        self.shared
            .platform_dirs
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Update the lib directory set. Sprint 57 Wave 4 G9: tests and the
    /// CLI call this after `new()` to override defaults; workers take a
    /// fresh clone for each file-resolution call, so the change is
    /// observed by subsequent typechecks.
    pub fn set_lib_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self
            .shared
            .lib_dirs
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Update the platform search directory set. Same semantics as
    /// `set_lib_dirs`.
    pub fn set_platform_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self
            .shared
            .platform_dirs
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Append a single platform search directory to the current set.
    /// Convenience wrapper around `set_platform_dirs` for tests/CLI.
    pub fn push_platform_dir(&mut self, dir: PathBuf) {
        let mut guard = self
            .shared
            .platform_dirs
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        guard.push(dir);
    }

    // -- Convenience accessors for shared TC state --

    // `tc_env` deleted (W-Absorb): all former callers switched to the
    // types-crate `ensure_module_exists` free fn; no remaining use for a
    // session-built `TypeCheckEnv`.

    /// Get the current module path (REPL carry-forward).
    ///
    /// Sprint 67 Cluster B sub-fire 2d: reads the CompilerSession-owned
    /// `current_repl_module` field (PIF-relocated from
    /// `SharedState.current_module` per facade L222 — REPL is single-threaded
    /// against this state).
    pub(crate) fn current_module_path(&self) -> ModuleFullPath {
        self.current_repl_module.clone()
    }

    /// Reset every Failed module in the scheduler AND drop the stale live symbol
    /// table of each one that NEVER reached terminal typecheck (I1, 0571.2 +
    /// 0571.3). A module that fails to load leaves live bindings behind:
    /// `(import [primitives [Int]])` writes the `Int` import into the LIVE table
    /// *before* the body-check failure, so the failed module's table is NON-empty
    /// even though it never finished loading. If the reset leaves that table in
    /// place, a later FQ reference reads the module as "loaded" (the table exists
    /// and the scheduler has forgotten it) and reports a false "module X has no
    /// member Y" on autoload RETRY (§8.5.4 edge 4/5). Dropping the table makes the
    /// retry re-drive from scratch — `ensure_module_exists` re-seeds it.
    ///
    /// **Discriminate by MODULE HISTORY, not call-site (0571.3 fix (a)).** The
    /// Failed set at an autoload-failure moment can include a **cascade victim** —
    /// a previously-terminal (was-good) module that `cascade_failure_locked`
    /// marked Failed only because it awaited the broken dep. Purging ITS table
    /// would destroy valid definitions — the exact state-destruction the earlier
    /// call-site scoping was meant to prevent. So purge only a module that was
    /// **never terminal** (`!was_ever_terminal`): a fresh dep that never
    /// successfully typechecked. A was-terminal module keeps its table.
    pub(crate) fn reset_failed_modules(&self) {
        let reset = self.shared.scheduler.reset_all_failed_modules();
        for m in &reset {
            if !self.shared.scheduler.was_ever_terminal(m) {
                self.shared.symbol_tables.remove(m);
            }
        }
    }

    /// Set the current module path (REPL carry-forward).
    ///
    /// Sprint 67 Cluster B sub-fire 2d: writes the CompilerSession-owned
    /// `current_repl_module` field and mirrors the change into the
    /// session-stable `test_runner_state.current_module` (still on
    /// `SharedState` because the JIT-emitted test intrinsics dereference
    /// it via a raw pointer that must outlive the session). Also resets
    /// `shared.repl_check_state` to a fresh `CheckState` for the new
    /// module — REPL carry-forward state (subst, env, overloads) is lost
    /// on module switch, matching the prior behaviour.
    pub(crate) fn set_current_module(&mut self, path: ModuleFullPath) {
        cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &path);
        self.current_repl_module = path.clone();
        // Sprint 66 Wave 3a-γ: keep the test-runner state's `current_module`
        // in sync so `discover-tests` (with empty module arg) targets the
        // active REPL namespace after a `/mod` switch. The
        // `test_runner_state` lives behind the `Arc<SharedState>` so the
        // JIT-emitted intrinsics may dereference a stable pointer; only
        // the inner `Mutex<ModuleFullPath>` needs updating here.
        *self
            .shared
            .test_runner_state
            .current_module
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = path.clone();
        // Create a new CheckState for the new module.
        *self
            .repl_check_state
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(CheckState::new(path));
    }

    /// Get a read guard for the current module's symbol table.
    pub(crate) fn current_symbol_table(
        &self,
    ) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable> {
        let module = self.current_module_path();
        self.shared.symbol_tables.get(&module).unwrap_or_else(|| {
            unreachable!("invariant: current_module always exists in symbol_tables")
        })
    }

    /// Get a read guard for any module's symbol table.
    pub(crate) fn module_table(
        &self,
        path: &ModuleFullPath,
    ) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable>> {
        self.shared.symbol_tables.get(path)
    }

    /// Introduce a module into the session — the 4-branch lifecycle gate.
    ///
    /// Sprint 67 hack-back (FIXME 0192 Residual Task 2): the single
    /// orchestration entry point for module introduction. Routes to one of
    /// four outcomes:
    ///   1. **AlreadyPresent** — `path` already has a symbol table; no change.
    ///   2. **CachedLoad** — cache reports a valid metadata + `.o` for `path`;
    ///      decode the cached `SymbolTable`, advance the typecheck `next_id`
    ///      past any cached TypeId vars (the consistency invariant from the
    ///      old `restore_cached_module`), and atomically install the table
    ///      via `cranelisp_types::install_module`.
    ///   3. **SourceLoad** — no cache hit but a source file is registered for
    ///      `path`; signal the caller (scheduler) to enqueue compilation.
    ///   4. **Blank** — neither cache nor source is available; create an empty
    ///      symbol table at `path` via `cranelisp_types::ensure_module_exists`.
    ///
    /// The cache-hit branch shares its install primitive with `worker.rs`'s
    /// `try_cache_hit_load` (which retains the surrounding logic for transitive
    /// dep walking + platform re-resolution that the worker context owns).
    /// The source-load branch returns the outcome variant so the caller can
    /// decide whether/how to schedule — the orchestrator does not directly
    /// drive the scheduler (which has tighter shared-state contracts the
    /// session does not own).
    pub fn introduce_module(
        &self,
        path: &ModuleFullPath,
    ) -> Result<ModuleIntroductionOutcome, CranelispError> {
        // Branch 1 — already present.
        if self.shared.symbol_tables.contains_key(path) {
            return Ok(ModuleIntroductionOutcome::AlreadyPresent);
        }

        // Branch 2 — cache hit. Probe the backend cache for a valid entry;
        // if present, decode and install atomically.
        if let Some(decoded) = self.try_load_cached_for_introduction(path)? {
            cranelisp_typecheck::advance_next_id_past_table(&self.shared.next_type_id, &decoded);
            cranelisp_types::install_module(&self.shared.symbol_tables, path.clone(), decoded);
            // S102 CS-D3a (§6.2): uniformly with the worker's `try_cache_hit_load`
            // route, establish the session-env companions (prelude-fallback bit +
            // aliases) and the `file_path` authority from the restored table.
            crate::imports::install_module_session_env(
                &self.shared.symbol_tables,
                path,
                &self.shared.module_aliases,
                &self.shared.prelude_fallback,
            );
            if let Some(src_file) = self.find_module_source(path) {
                crate::worker::ensure_typecheck_product(&self.shared.typecheck_products, path);
                if let Some(mut tp) = self.shared.typecheck_products.get_mut(path) {
                    tp.file_path = Some(src_file);
                }
            }
            return Ok(ModuleIntroductionOutcome::CachedLoad);
        }

        // Branch 3 — source hit. The session has no scheduler in hand here;
        // signal the caller. Source presence is determined by inspecting the
        // worker's `file_to_module` reverse-mapping or by attempting source
        // lookup via cache_state's known paths.
        if self.find_module_source(path).is_some() {
            return Ok(ModuleIntroductionOutcome::SourceLoad);
        }

        // Branch 4 — blank create-if-absent.
        let _ = cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, path);
        Ok(ModuleIntroductionOutcome::Blank)
    }

    /// Cache probe for `introduce_module`'s branch 2. Returns
    /// `Some(decoded_table)` iff cache reports a valid entry with an `.o`
    /// file present. Errors (cache read failures) bubble up as
    /// `CranelispError::Internal` strings; absent entries return `Ok(None)`.
    pub(crate) fn try_load_cached_for_introduction(
        &self,
        path: &ModuleFullPath,
    ) -> Result<Option<cranelisp_types::SymbolTable<Code, ()>>, CranelispError> {
        use cranelisp_backend::cache;
        // Sprint 67 Cluster B sub-fire 3: read cache directory via the
        // ObjectCache facade method (was: locking `shared.cache_state`).
        let cache_dir = match self.shared.cache.cache_dir() {
            Some(d) => d,
            None => return Ok(None),
        };
        let cached = match cache::try_load_cached_module(&cache_dir, path) {
            Ok(Some(c)) => c,
            _ => return Ok(None),
        };
        if !cached.has_object {
            return Ok(None);
        }
        Ok(Some(cached.symbol_table.into_concrete::<Code, ()>()))
    }

    /// Branch-3 probe: returns the source file path for `module` if one is
    /// known to the session (registered in `file_to_module`'s reverse map).
    pub(crate) fn find_module_source(&self, module: &ModuleFullPath) -> Option<std::path::PathBuf> {
        let guard = self
            .shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        guard.iter().find_map(|(file, mp)| {
            if mp == module {
                Some(file.clone())
            } else {
                None
            }
        })
    }

    /// Resolve a module by name (for /exports command).
    ///
    /// Sprint 67 hack-back (FIXME 0192 method 7): the `TypeCheckEnv` method
    /// was deleted; the body relocated to `cranelisp_types` as a free fn.
    /// The session passes its `current_module_path()` as the scope root
    /// (replacing the prior `state.current_module` access).
    pub(crate) fn resolve_module_by_name(&self, name: &str) -> Option<ModuleFullPath> {
        cranelisp_types::resolve_module_by_name_chain(
            &self.shared.symbol_tables,
            &self.current_module_path(),
            name,
        )
    }

    /// Initialize the file watcher for REPL mode (repl/spec.md §14).
    ///
    /// Creates an OS-level file watcher and registers all currently known
    /// module source files. Call once after `wait_inmem_complete()` so
    /// that `file_to_module` is populated.
    pub fn init_watcher(&mut self) {
        let mut fw = match crate::watch::FileWatcher::new() {
            Some(fw) => fw,
            None => return,
        };

        // Register all source files already loaded (prelude + its deps).
        let file_to_mod = self
            .shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for path in file_to_mod.keys() {
            fw.watch_file(path);
        }
        drop(file_to_mod);

        self.watcher = Some(fw);
    }

    // -----------------------------------------------------------------------
    // Sprint 67 W3 — Facade-prescribed introspection accessors
    // (FIXME 0176 partial close; `facades/int.md` §"Introspection accessors")
    //
    // Pure read-side projections over `shared.symbol_tables` + `shared.introspection`.
    // No `&mut self` required for reads; the two mutating REPL-state methods
    // (`set_current_repl_module`, `set_repl_input_active`) write to
    // `CompilerSession`-side state per the SharedState alignment plan.
    //
    // Today these forward to the existing slash-command handler internals
    // (`handle_source`, `get_introspection`, etc.); subsequent /dev (int) fires
    // will pivot the slash-command handlers to call these new accessors first
    // so the accessors become the canonical entry points.
    // -----------------------------------------------------------------------

    /// REPL `/source` — original source text of a symbol, or `None` if the
    /// symbol has no introspection record (production batch mode) or no
    /// captured source. Reads `shared.introspection[fq]`.
    pub fn symbol_source(&self, fq: &FQSymbol) -> Option<String> {
        self.shared
            .introspection
            .as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.source.clone())
    }

    /// REPL `/sexp` — parsed s-expression of a symbol's defining form, or
    /// `None`. Reads `shared.introspection[fq]`.
    pub fn symbol_sexp(&self, fq: &FQSymbol) -> Option<Sexp> {
        self.shared
            .introspection
            .as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.sexp.clone())
    }

    /// REPL `/clif` — CLIF IR text of a symbol's compiled body, or `None`.
    /// Populated only when `CRANELISP_CODEGEN_TRACE` or REPL-trace mode is
    /// active. Reads `shared.introspection[fq]`.
    pub fn symbol_clif(&self, fq: &FQSymbol) -> Option<String> {
        self.shared
            .introspection
            .as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.clif_ir.clone())
    }
}

/// Is `form` a top-level **definition** form (§15.7 persisted forms) — one the
/// startup restore notice counts (FIXME 0674)? A definition-shaped head:
/// `defn`/`defn-`/`def`/`def-`/`const`/`const-`/`deftype`/`deftrait`/
/// `defmacro`/`defmacro-`/`impl`. Imports/exports/`mod`/`platform`/expressions
/// are NOT definitions and are excluded (so an imports-only file suppresses).
/// FIXME 0707 — the restored-definition count, single-sourced from the restore
/// record (not a bare re-parse). Counts persisted-definition forms in `source`,
/// then subtracts the module's `failed` persisted-definition forms (form-granular:
/// each failed form's verbatim `text` is re-parsed and its persisted-definition
/// forms subtracted — a degraded startup re-emits the failed forms into the file,
/// so a bare count over-reports them as "restored"). Returns `None` when the file
/// is empty OR no definition actually restored (imports-only / all-failed),
/// preserving the SUPPRESSED-notice contract (§15.2.2 / §6.2).
fn restored_definition_count(source: &str, failed: &[FailedForm]) -> Option<usize> {
    if source.trim().is_empty() {
        return None; // empty backing file — suppress
    }
    let forms = cranelisp_frontend::parse(source).ok()?;
    let total = forms
        .iter()
        .filter(|f| is_persisted_definition_form(f))
        .count();
    let failed_persisted: usize = failed
        .iter()
        .map(|f| {
            cranelisp_frontend::parse(&f.text)
                .ok()
                .map(|fs| {
                    fs.iter()
                        .filter(|x| is_persisted_definition_form(x))
                        .count()
                })
                .unwrap_or(0)
        })
        .sum();
    let count = total.saturating_sub(failed_persisted);
    if count == 0 {
        return None; // no definitions restored — suppress
    }
    Some(count)
}

fn is_persisted_definition_form(form: &cranelisp_types::Sexp) -> bool {
    let cranelisp_types::Sexp::List(children, _) = form else {
        return false;
    };
    let Some(cranelisp_types::Sexp::Symbol(head, _)) = children.first() else {
        return false;
    };
    matches!(
        head.as_str(),
        "defn"
            | "defn-"
            | "def"
            | "def-"
            | "const"
            | "const-"
            | "deftype"
            | "deftrait"
            | "defmacro"
            | "defmacro-"
            | "impl"
    )
}

impl CompilerSession {
    /// REPL `/list` — user-defined symbols in the current REPL module (excludes
    /// imports + special forms). Returns a `Vec<SymbolInfo>` per facade
    /// §"Introspection records".
    pub fn list_user_definitions(&self) -> Vec<SymbolInfo> {
        let current = self.current_module_path();
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(&current) {
            for (name, entry) in table.all_symbols() {
                // Skip internal compiler artifacts — `$`-mangled overload/mono
                // names and the synthetic `__expr` top-level-expression wrapper
                // are not user definitions (repl/spec.md §3.3; shared predicate
                // with `handle_list` / `/exports` / the harvest).
                if crate::worker::is_internal_listing_name(name.as_ref()) {
                    continue;
                }
                // Bucketing is the shared `classify_listing_entry` classifier
                // (FIXME 0440); `/list`'s structured surface skips special forms
                // + imports — those are surfaced by `/imports` separately. The
                // scheme/docstring facets are pulled per-entry below.
                let category = match crate::worker::classify_listing_entry(entry) {
                    Some(SymbolCategory::SpecialForm) | None => continue,
                    Some(c) => c,
                };
                let (scheme, docstring) = match entry {
                    ModuleEntry::Def {
                        scheme, docstring, ..
                    } => (Some(scheme.clone()), docstring.clone()),
                    ModuleEntry::TraitDecl { docstring, .. } => (None, docstring.clone()),
                    _ => (None, None),
                };
                out.push(SymbolInfo {
                    name: name.clone(),
                    category,
                    scheme,
                    docstring,
                });
            }
        }
        out
    }

    /// REPL `/imports [MODULE]` — list the import declarations in a target
    /// module. Returns one `ImportSpec` per `ModuleEntry::Import`, carrying
    /// the source module + the local binding name (per
    /// `cranelisp_types::ImportSpec`). Reexports are listed separately by
    /// `module_exports` when the module publishes them.
    ///
    /// Per-binding reconstruction shape: `ModuleEntry::Import` stores only
    /// the source `FQSymbol` per binding; the parse-time `ImportSpec` is not
    /// retained on the symbol table. Each returned spec is therefore a
    /// single-name `Specific([local_name])` against the source module, with
    /// `alias = None` and `span = Span::SYNTHETIC`. Aliased imports (local
    /// != source.symbol) collapse to the local name on the binding side —
    /// the source.symbol distinction is recoverable from the
    /// `module_exports` of the source module. Threading the original
    /// parse-time `ImportSpec` through to here is tracked by FIXME 0194.
    pub fn module_imports(&self, module: &ModuleFullPath) -> Vec<cranelisp_types::ImportSpec> {
        use cranelisp_types::{ImportNames, ImportSpec};
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(module) {
            for (name, entry) in table.all_symbols() {
                if let ModuleEntry::Import { source, .. } = entry {
                    out.push(ImportSpec {
                        module_path: source.module.clone(),
                        alias: None,
                        names: ImportNames::Specific(vec![name.clone()]),
                        span: Span::SYNTHETIC,
                    });
                }
            }
        }
        out
    }

    /// REPL `/exports MODULE` — list the publicly-visible symbols of a module.
    /// A symbol is public iff its `ModuleEntry` carries `Visibility::Public`
    /// (Def / TypeDef / TraitDecl / Macro / Constructor / Reexport).
    pub fn module_exports(&self, module: &ModuleFullPath) -> Vec<(Symbol, ModuleEntry<Code>)> {
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(module) {
            for (name, entry) in table.all_symbols() {
                // Uniform per-entry visibility accessor (S70 — covers Def
                // [incl. macro/constructor kinds], TypeDef, TraitDecl,
                // SpecialForm, and public-visibility Import re-export edges).
                if entry.is_public() {
                    out.push((name.clone(), entry.clone()));
                }
            }
        }
        out
    }

    /// Current REPL module (per facade §"CompilerSession.current_repl_module").
    ///
    /// Sprint 67 Cluster B sub-fire 2d: now reads the CompilerSession-owned
    /// field directly (PIF-relocate landed). Returns a `&ModuleFullPath` per
    /// facade L125 — no clone needed at the accessor boundary.
    pub fn current_repl_module(&self) -> &ModuleFullPath {
        &self.current_repl_module
    }

    /// Switch the REPL's active module (per `/mod NAME`). Writes
    /// `shared.current_module` + `shared.test_runner_state.current_module` +
    /// resets `shared.repl_check_state` to a fresh `CheckState` for the new
    /// module.
    pub fn set_current_repl_module(&mut self, module: ModuleFullPath) {
        self.set_current_module(module);
    }

    /// Update the watcher-input-active flag (per exec-flow-repl STEP 1 / STEP 3).
    ///
    /// Sprint 67 Cluster B sub-fire 2c: now writes the
    /// CompilerSession-owned `repl_input_active: Arc<AtomicBool>` field
    /// (PIF-relocate landed). The watcher event handler holds an
    /// `Arc::clone` of this atomic and consults it before triggering
    /// cascade reloads — wiring the watcher to actually consult the flag
    /// is FIXME 0205's broader scope (S68 facade refresh); landing the
    /// field + accessor here is the load-bearing structural change.
    pub fn set_repl_input_active(&self, active: bool) {
        self.repl_input_active
            .store(active, std::sync::atomic::Ordering::Release);
    }

    /// Accumulated session warnings (per facade L140).
    ///
    /// Sprint 67 Cluster B sub-fire 2c: returns the CompilerSession-owned
    /// `warnings` accumulator. Workers route warnings through this Vec via
    /// the eventual `warnings_mut()` / work-completion merge path
    /// (FIXME 0205); landing the accessor here is the facade method-surface
    /// landing — S68 wires workers without changing this call site.
    pub fn warnings(&self) -> &[Warning] {
        &self.warnings
    }

    /// Mutable accessor for the warnings accumulator. `eval` overwrites it with
    /// the merged per-cluster warning set at the end of a turn (`eval.rs`).
    pub fn warnings_mut(&mut self) -> &mut Vec<Warning> {
        &mut self.warnings
    }

    /// Register any newly-loaded module source files with the watcher.
    ///
    /// Called after eval/import so that newly discovered modules get watched.
    /// The watcher internally deduplicates already-watched directories.
    pub fn sync_watcher(&mut self) {
        let watcher = match &mut self.watcher {
            Some(w) => w,
            None => return,
        };
        let file_to_mod = self
            .shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for path in file_to_mod.keys() {
            watcher.watch_file(path);
        }
    }

    /// The dependent modules (+ backing file paths) that import ANY module in
    /// `changed`, excluding the changed modules themselves. **Single-sourced**
    /// for both the watcher cascade (`poll_and_reload`) and the T1 full-cure
    /// cascade (`redefine::reload_t1_dependents`) so the two never reload
    /// different sets (Principle 7 — no drift; the P7 hazard `/review` flagged).
    /// Path resolution is the `file_to_module` reverse map; a dependent absent
    /// from it is skipped in BOTH callers identically. `ImportSpec.module_path`
    /// is a `ModuleFullPath`, so the import match is a direct `==`.
    pub(crate) fn dependent_modules(
        &self,
        changed: &HashSet<ModuleFullPath>,
    ) -> Vec<(ModuleFullPath, PathBuf)> {
        let file_to_mod = self
            .shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let mut out: Vec<(ModuleFullPath, PathBuf)> = Vec::new();
        for entry in self.shared.symbol_tables.iter() {
            let dependent = entry.key().clone();
            if changed.contains(&dependent) {
                continue; // A changed module is reloaded directly, not as a dependent.
            }
            let depends_on_changed = entry
                .value()
                .imports
                .iter()
                .any(|spec| changed.contains(&spec.module_path));
            if !depends_on_changed {
                continue;
            }
            if let Some(path) = file_to_mod
                .iter()
                .find(|(_, mp)| **mp == dependent)
                .map(|(p, _)| p.clone())
                && !out.iter().any(|(mp, _)| mp == &dependent)
            {
                out.push((dependent, path));
            }
        }
        out
    }

    /// Poll the file watcher for changed source files and reload them.
    ///
    /// Returns a list of user-visible messages (one per reloaded module).
    /// On success, `reload_module` removes the module from `error_modules`
    /// and drops its retained `failed_forms` (the new file content is the
    /// authority — S102 W5R B-1). On failure, adds it to `error_modules`
    /// to block subsequent evals.
    ///
    /// Per repl/spec.md §14: notification format is `[updated: file.cl]`
    /// on success, `[errors: file.cl]` on failure. Cascade invalidation
    /// reloads modules that depend on changed modules.
    pub fn poll_and_reload(&mut self) -> Vec<String> {
        let watcher = match &mut self.watcher {
            Some(w) => w,
            None => return Vec::new(),
        };

        let changed_paths = match watcher.poll_changes() {
            Some(paths) => paths,
            None => return Vec::new(),
        };

        // Map file paths → module paths via SharedState.file_to_module.
        let file_to_mod = self
            .shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let mut modules_to_reload: Vec<(ModuleFullPath, PathBuf)> = Vec::new();
        for path in &changed_paths {
            if let Some(module_path) = file_to_mod.get(path)
                && !modules_to_reload.iter().any(|(mp, _)| mp == module_path)
            {
                modules_to_reload.push((module_path.clone(), path.clone()));
            }
        }
        let changed_modules: HashSet<ModuleFullPath> =
            modules_to_reload.iter().map(|(mp, _)| mp.clone()).collect();
        drop(file_to_mod);
        // Cascade invalidation: find modules that import any changed module
        // and add them to the reload list — via the SHARED dependent-scan
        // helper the T1 full-cure cascade also uses (Principle 7: one
        // dependent set + path resolution, no drift).
        for (dep_module, dep_path) in self.dependent_modules(&changed_modules) {
            if !modules_to_reload.iter().any(|(mp, _)| mp == &dep_module) {
                modules_to_reload.push((dep_module, dep_path));
            }
        }

        let mut messages = Vec::new();
        for (module_path, file_path) in modules_to_reload {
            // Extract just the filename for the notification message.
            let file_name = file_path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_else(|| module_path.as_ref());
            match self.reload_module(&module_path, &file_path, &[]) {
                Ok(()) => {
                    // `reload_module` itself clears `error_modules` +
                    // `failed_forms` on success (S102 W5R B-1).
                    messages.push(format!("[updated: {}]", file_name));
                }
                Err(e) => {
                    self.error_modules.insert(module_path.clone());
                    messages.push(format!("[errors: {}]\n  {e}", file_name));
                }
            }
        }
        messages
    }

    /// Regenerate the backing .cl file for the current module.
    ///
    /// Called after successful eval of a definition (defn, deftype, deftrait,
    /// impl, defmacro) or structural change (import, mod, platform).
    /// Reads the current module's symbol table and structural metadata,
    /// generates source text, and writes atomically.
    ///
    /// On write failure, prints a warning and continues — in-memory state
    /// is the ground truth (design/int/session-persistence.md §3.3).
    ///
    /// S78: the former post-write republish into `SharedState::module_sexps`
    /// is gone — that cross-thread parking map is deleted. A persistent worker
    /// only typechecks a module from sexps that ride its scheduler work packet
    /// (`register_module` / `re_register_module`), so there is no shared sexps
    /// entry to keep current and no "no parsed sexps for module" residue to
    /// guard against.
    /// The startup restore notice (FIXME 0674, `repl/spec.md` §15.2.2). When REPL
    /// startup restores a **non-empty** backing file for `module`, returns
    /// `; resumed N definitions from <file>` where N is the count of restored
    /// **definitions** (§15.7 persisted forms — `defn`/`def`/`deftype`/`deftrait`/
    /// `defmacro`/`impl`/`const`, not transient expressions). Returns `None`
    /// (SUPPRESSED) when the backing file is **absent or empty**, so a first
    /// session in an empty directory reaches the prompt with no extra output
    /// (fresh-dir transcripts stay byte-identical, §6.2). Startup-only chrome —
    /// never persisted, never part of a value/definition response. REPL-only.
    pub fn startup_restore_notice(&self, module: &ModuleFullPath) -> Option<String> {
        let file_path = self.backing_file_path_for(module);
        let source = std::fs::read_to_string(&file_path).ok()?;
        // FIXME 0707: count from the RESTORE RECORD, not a bare re-parse. Under a
        // degraded startup (§18.8) the backing file re-emits the FAILED forms too
        // (`append_failed_forms`), so a bare re-parse over-counts them as
        // "restored". Subtract the module's persisted-definition FAILED forms —
        // the count of definitions the session actually restored (§15.2.2).
        let failed = self
            .failed_forms
            .get(module)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let count = restored_definition_count(&source, failed)?;
        let name = file_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("the backing file");
        let plural = if count == 1 {
            "definition"
        } else {
            "definitions"
        };
        Some(format!("; resumed {count} {plural} from {name}"))
    }

    /// Resolve `module`'s backing `.cl` path — the typecheck product's recorded
    /// path, else `{project_root}/{module}.cl` (the fresh-session default). Shared
    /// by [`Self::regenerate_backing_file`] and [`Self::startup_restore_notice`].
    fn backing_file_path_for(&self, module: &ModuleFullPath) -> std::path::PathBuf {
        match self.shared.typecheck_products.get(module) {
            Some(tp) => match &tp.file_path {
                Some(p) => p.clone(),
                None => self.shared.project_root.join(format!("{module}.cl")),
            },
            None => self.shared.project_root.join(format!("{module}.cl")),
        }
    }

    pub fn regenerate_backing_file(&mut self) {
        let module = self.current_module_path();

        // Get the backing file path (typecheck-product-recorded, else default).
        let file_path = self.backing_file_path_for(&module);

        // Read the symbol table for this module. Sprint 58 Step 5a: structural
        // decls (imports/exports/platforms/submodules) are now fields on the
        // SymbolTable itself; no separate read is needed.
        let st = match self.shared.symbol_tables.get(&module) {
            Some(st) => st.clone(),
            None => return, // No symbol table — nothing to save.
        };

        // FIXME 0343: submodule-body-preservation guard. A module whose backing
        // file holds an authored inline `(mod child form…)` block (the ModDecl
        // still carries `inline_body`) MUST NOT be regenerated from the parent's
        // table alone — the child's defns live in the child's table, so regen
        // would emit a bare `(mod child)` and DROP the body from disk (data
        // corruption). Preserve the file verbatim in that case.
        if !crate::save::should_regenerate(&st) {
            return;
        }

        // FIXME 0220 (/arch ruling S81): lazy on-demand introspection
        // rehydration for cache-loaded symbols. A module restored from the
        // compile cache has no REPL-only Introspection records, so a
        // cache-restored `UserFn` would be silently dropped from the
        // regenerated `.cl` (its source rides neither introspection nor
        // `macro_sexp`). Re-read the backing `.cl` (the cache key — always
        // present) and populate the missing UserFn records before regen.
        if let Some(intro) = self.shared.introspection.as_ref()
            && let Ok(backing_source) = std::fs::read_to_string(&file_path)
        {
            crate::save::rehydrate_userfn_introspection_from_source(
                &st,
                intro,
                &module,
                &backing_source,
            );
        }

        // Generate source text.
        let source =
            crate::save::generate_module_source(&st, self.shared.introspection.as_ref(), &module);

        // S102 CS-0489 (§18.8 no-silent-drop): re-emit the retained
        // failed-form verbatim texts — the degraded startup load's broken
        // definitions never entered the live table, so a regen built from
        // the table alone would silently drop them from the user's file.
        // Repaired symbols have already left the set
        // (`clear_repaired_failed_form`), so a fully-repaired module writes
        // a green file with no residue.
        let source = match self.failed_forms.get(&module) {
            Some(failed) => append_failed_forms(&source, failed),
            None => source,
        };

        // Skip writing empty source (no user-defined content).
        if source.trim().is_empty() {
            return;
        }

        // Compute content hash for watcher suppression.
        let hash = cranelisp_backend::cache::manifest::hash_source(&source);

        // Atomic write.
        if let Err(e) = crate::save::atomic_write(&file_path, &source) {
            eprintln!("Warning: failed to save {}: {e}", file_path.display());
            return;
        }

        // Update watcher content hash so the self-write is suppressed
        // (design/int/session-persistence.md §4).
        if let Some(ref mut watcher) = self.watcher {
            let canonical = file_path
                .canonicalize()
                .unwrap_or_else(|_| file_path.clone());
            watcher.update_content_hash(canonical.clone(), hash.clone());
        }

        // Register the file in file_to_module so the watcher can find it.
        if let Ok(canonical) = file_path.canonicalize() {
            self.shared
                .file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module.clone());
        }

        // S101 R18 fix — deterministic per-turn persist (spine §5.6 pin (ii)).
        // (a) Refresh the cache's source-hash stash to the JUST-WRITTEN
        //     backing source, so the nice worker's manifest record matches the
        //     on-disk `.cl` and the next session's cache-hit check converges
        //     (previously the stash kept the STARTUP hash forever, so a
        //     restart always missed and renumbered persisted GOT slots).
        // (b) Re-enqueue the module for object codegen so the `.o`/`.meta`
        //     pair is rewritten from the current live table; `/quit`'s
        //     `wait_object_complete` drains this deterministically instead of
        //     abandoning the last defining turns at shutdown.
        self.shared.cache.record_source_hash(&module, hash.clone());
        self.shared.scheduler.mark_object_stale(&module);

        // S78: the former `module_sexps[module]` republish is gone — there is
        // no shared sexps map to keep current. A persistent worker only
        // typechecks `module` from sexps that ride its scheduler work packet
        // (`register_module` / `re_register_module`), and the REPL eval path
        // re-derives from the form it is processing; neither reads a shared
        // map. The H5 "no parsed sexps for module" residue this republish
        // guarded cannot occur (the map it republished into is deleted).
    }

    /// Reload a single module from its source file.
    ///
    /// Clears the module's stale products, re-parses, and re-registers with
    /// the scheduler (the fresh sexps ride the re-register work packet — S78).
    /// The persistent priority workers pick up the re-registration and
    /// re-typecheck + re-codegen. Sprint 57 Wave 4 G11 per
    /// `persistent-workers.md` §4.6 — reload via scheduler falls out of
    /// persistent workers (same path as `register_module_with_source`).
    /// Reload a module from its backing `.cl`, plus a set of in-memory
    /// **instantiation-driver** forms appended to the parsed source before
    /// re-registration (`extra_forms` empty ⇒ a plain from-source reload).
    ///
    /// The from-source reload re-typechecks + re-codegens a module from its
    /// backing `.cl`, which is **definitions-only** (FIXME 0549 / §8 pin (v) —
    /// the synthetic `__expr` eval wrapper is no longer persisted). A same-module
    /// polymorphic mono variant (`g$Int`) originally minted by a REPL top-level
    /// expression therefore has no minter on a from-source reload. The T1 CS-1
    /// full-cure driver (`redefine.rs::drive_t1_full_cure`) captures those driver
    /// expressions from the live table BEFORE regen and passes them here so the
    /// workers re-mint exactly those mono variants against the reloaded
    /// definitions — the mono-instantiation obligation travelling the explicit
    /// in-memory channel, never the persisted `.cl` source channel
    /// (`design/int/session-transaction.md` §10 CS-1; Q1 strictly precedes Q2).
    pub(crate) fn reload_module(
        &mut self,
        module_path: &ModuleFullPath,
        file_path: &Path,
        extra_forms: &[Sexp],
    ) -> Result<(), CranelispError> {
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::RecompileModule,
            module_path.as_ref(),
        );
        let source =
            std::fs::read_to_string(file_path).map_err(|e| CranelispError::ModuleError {
                message: format!("cannot read {}: {e}", file_path.display()),
                location: ErrorLocation::from_span_file(
                    Span::new(0, 0),
                    Some(file_path.to_path_buf()),
                ),
            })?;

        // Remove stale products before recompilation.
        // Sprint 57 Wave 2 G6: `codegen_products` was deleted; compiled code
        // lives on `ModuleEntry::Def.code`.
        //
        // S101 (design/int/session-transaction.md §6.3): move each displaced
        // `Code` handle into the session retention pool instead of `None`-ing
        // it. The former comment here claimed "`kept_jits` keeps the old
        // mmap'd pages alive" — but `kept_jits` was dissolved in S58
        // (Decision 35; retention moved per-entry onto `Code::Jit`), so
        // `*code = None` dropped what may be the LAST Arc and freed machine
        // code that in-flight frames or heap closures could still execute.
        // The pool restores the intended policy ("old code stays callable for
        // in-flight calls"): pages stay mapped for the session lifetime.
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::ClearModuleState,
            module_path.as_ref(),
        );
        self.shared.typecheck_products.remove(module_path);
        if let Some(mut st) = self.shared.symbol_tables.get_mut(module_path) {
            let mut pool = self
                .shared
                .retained_code
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            for (name, entry) in st.symbols.iter_mut() {
                let slot = entry.callable_got_slot();
                if let ModuleEntry::Def { code, .. } = entry
                    && let Some(displaced) = code.take()
                {
                    pool.push(crate::redefine::RetainedCode::frozen(
                        module_path,
                        name,
                        slot,
                        displaced,
                    ));
                }
            }
        }

        // Parse the new source; the sexps ride the re-register work packet
        // (S78 — no shared `module_sexps` map). Persistent workers parked on
        // the priority-work condvar wake and process it (G11 per §4.6).
        // Q1 (FIXME 0549): the captured instantiation-driver forms are appended
        // in-memory so the reload re-mints the same-module mono variants they
        // instantiate — without those transient expressions entering the
        // definitions-only backing file.
        let mut parsed = cranelisp_frontend::parse(&source)?;
        parsed.extend_from_slice(extra_forms);
        let sexps: std::sync::Arc<[Sexp]> = std::sync::Arc::from(parsed);

        // Module-preamble wiring (§8.16.5; design/frontend/module-preamble.md §5):
        // a reload re-reads fresh source, so re-capture the leading `;;` block
        // onto the module's live table (disk is the source of truth on reload).
        crate::save::apply_module_preamble(&self.shared.symbol_tables, module_path, &source);

        // S82 reload-during-compile race: a worker sets `inmem_done = true`
        // partway through its codegen pass, BEFORE it reaches
        // `notify_typecheck_done` (the TypecheckWorking → TypecheckDone
        // transition). The initial `register_module_with_source` returns as
        // soon as `wait_inmem_complete_blocking` observes `inmem_done`, so the
        // worker may still be mid-pass when we get here. If it is,
        // `re_register_module` hits its "mid-typecheck — skip" guard, returns
        // false, and the `register_module` fallback below is a no-op (the
        // module already exists) — the reload would be silently dropped and the
        // stale table survives. Wait for the in-flight pass to settle so the
        // re-register reliably takes.
        self.shared
            .scheduler
            .wait_module_typecheck_settled(module_path);

        // `re_register_module` clears `inmem_done` and re-queues the module
        // for typecheck with the fresh sexps. `register_module` would be a
        // no-op because the module is already in `scheduler.modules`.
        let re_registered = self
            .shared
            .scheduler
            .re_register_module(module_path, sexps.clone());
        if !re_registered {
            // Module isn't known to the scheduler yet (first-time seed from
            // file watcher) — fall back to register_module.
            self.shared
                .scheduler
                .register_module(module_path.clone(), sexps, false);
        }

        // Block until inmem-done for every registered module. The workers
        // do the typecheck + in-memory codegen.
        self.shared.scheduler.wait_inmem_complete_blocking()?;

        // Check if the module ended up in Failed state (wait_inmem_complete_blocking
        // would have returned Err in that case, but double-check explicitly).
        if self.shared.scheduler.is_failed(module_path) {
            return Err(CranelispError::ModuleError {
                message: format!("module '{}' failed to compile", module_path.as_ref()),
                location: ErrorLocation::from_span_file(Span::new(0, 0), None),
            });
        }

        // S102 W5R B-1: a successful reload makes the NEW file content the
        // authority — drop any retained degraded-startup failed forms for
        // this module and lift the §14.4 error block. Without this, the next
        // defining turn's regen would re-append the stale broken text after
        // the user's external repair (silently undoing the hand-edit and
        // re-poisoning the file for the next restart). Cleared here — not at
        // the poll site — so EVERY successful reload path (watcher poll,
        // T2 module-grain degrade) restores the invariant that a non-empty
        // failed set implies membership in `error_modules`.
        self.failed_forms.remove(module_path);
        self.error_modules.remove(module_path);

        Ok(())
    }

    /// Register a module by name (pipeline-v4.md §3.1).
    ///
    /// Resolves source file, parses, enqueues for typechecking.
    /// TODO: currently runs inline worker loop. Will just enqueue
    /// once persistent workers are wired.
    pub fn register_module(&mut self, module_name: &str) -> Result<(), CranelispError> {
        self.register_entry_module(module_name)?;
        Ok(())
    }

    // `re_register_module` deliberately stays on the PARENT `session_v4.rs`
    // (S87 §2 — facade thin-forward kept at the struct's home; also satisfies
    // the `facade_pif_rows` row-45 source-text guard that greps
    // `src/session_v4.rs` for the method). See the parent file.

    /// Register a module with explicit source (internal + test helpers).
    ///
    /// Parses the source and registers the module with the scheduler (the
    /// sexps ride the work packet — S78); the persistent priority workers
    /// parked on `priority_work_available` wake and process it. The caller
    /// blocks on `wait_inmem_complete_blocking` until every registered module
    /// reaches inmem_done or failure. Sprint 57 Wave 4 G9 per
    /// `persistent-workers.md` §4.3.
    pub fn register_module_with_source(
        &mut self,
        module_name: &str,
        source: &str,
        entry_module_path: &Path,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        let sexps: std::sync::Arc<[Sexp]> =
            std::sync::Arc::from(cranelisp_frontend::parse(source)?);

        // Module-preamble wiring (§8.16.5; design/frontend/module-preamble.md §5):
        // capture the leading `;;` block from the SAME source and write it onto
        // this (entry) module's live `SymbolTable.module_preamble`.
        crate::save::apply_module_preamble(&self.shared.symbol_tables, &module, source);

        // S102 CS-D2 (§15.4.7 authorship fidelity): record the module's source
        // text for verbatim introspection capture — REPL only, mirroring the
        // dep-load path (`dependency.rs::register_dep` step 4). Without it the
        // ENTRY module's load-time introspection records fall back to
        // `pretty_print` (which desugars reader shorthand), so adopting a
        // hand-authored backing file destroyed the user's authored text on the
        // first regenerating turn (/port D2). Every consumer of the recorded
        // text consistency-gates its span slice (`verbatim_source_slice`), so
        // later REPL-turn spans against this load-time text can never
        // mis-record.
        if self.shared.introspection.is_some() && !source.is_empty() {
            crate::worker::ensure_typecheck_product(&self.shared.typecheck_products, &module);
            if let Some(mut tp) = self.shared.typecheck_products.get_mut(&module) {
                // S102 CS-D3a (§6.2.1): make `file_path` authoritative on the
                // entry route too — `regenerate_backing_file` reads it as the
                // save target (its `{root}/{module}.cl` fallback stops being
                // load-bearing), and it converges with the dep-load + cache
                // routes on one file authority.
                tp.file_path = Some(entry_module_path.to_path_buf());
                tp.source_text = Some(source.to_string());
            }
        }

        // Record source hash for manifest generation. Sprint 67 Cluster B
        // sub-fire 3: dispatch via the `ObjectCache` facade method.
        {
            let hash = cranelisp_backend::cache::manifest::hash_source(source);
            self.shared.cache.record_source_hash(&module, hash);
        }

        // Register module with scheduler (entry module, not delaying others).
        // The sexps ride the work packet (S78 — no shared `module_sexps` map);
        // a worker that wakes on the scheduler notify reads them off the
        // packet. Wakes parked priority workers via
        // `priority_work_available.notify_all()`.
        self.shared
            .scheduler
            .register_module(module.clone(), sexps, false);

        // Block until every registered module reaches inmem_done (or a
        // module fails). The persistent priority workers do the typecheck
        // + in-memory codegen and call `notify_inmem_codegen_complete` /
        // `notify_typecheck_done`, which wakes the scheduler's completion
        // condvar.
        self.shared.scheduler.wait_inmem_complete_blocking()?;

        Ok(Vec::new())
    }

    /// Execute the entry module's main function via the trampoline.
    ///
    /// For the v4 scheduler path: GOT is already populated by the worker
    /// loop. For the old path: flushes codegen queue first.
    ///
    /// Looks up `main` in the GOT, calls it, and runs the IO trampoline
    /// if the return type is IO.
    ///
    /// Returns the [`OwnedProgramResult`](crate::result_owner::OwnedProgramResult)
    /// — NOT a free-standing `(i64, Type)` tuple. The caller observes it (exit
    /// conversion) and finalizes it BEFORE any teardown
    /// (`design/int/result-owner.md` §4.3).
    pub fn trampoline(
        &mut self,
        module_name: &str,
    ) -> Result<crate::result_owner::OwnedProgramResult, CranelispError> {
        // Enforce the batch-mode signature `(Fn [] (IO _))` before running
        // (spec §10.6 / §12.6). `--run` reaches `main` through this seam (NOT
        // `link_by_name`), so the same `validate_main` gate the `--link` path
        // applies must be applied here — otherwise a bare-`Int`/`Bool` main
        // would be leniently accepted under `--run`. The REPL never calls
        // `trampoline`, so it stays exempt (§10.6.2).
        let module_path = ModuleFullPath::from(module_name);
        if let Some(table) = self.module_table(&module_path) {
            // 0611: the entry module's unresolved-return-poly-dispatch carrier
            // (EMPTY for every valid module) — `validate_main` rejects a `main`
            // whose body carries one with the §3.11 ambiguity (class (b)).
            let dispatch = self
                .shared
                .typecheck_products
                .get(&module_path)
                .map(|tp| tp.unresolved_dispatch.clone())
                .unwrap_or_default();
            crate::exe::validate_main(&table, &dispatch)?;
        }
        // (If the entry table is absent, the code-ptr lookup below produces the
        // "no `main`" diagnostic — no separate handling needed here.)

        // Look up main's compiled code on its symbol-table entry (G6). ONE read
        // yields the callable address, the declared result type, AND the code
        // lifetime owner — `design/int/result-owner.md` §4.3: the owner
        // constructor takes its type from the same read that produced the code
        // pointer, never from a second lookup that could fall back.
        let main = self.read_main_entry(module_name)?;
        let code_ptr = main.code_ptr;
        let result_type = main.result_type.clone();

        // Run the program via the unified C-ABI driver (FIXME 0366). The driver
        // owns the WHOLE clear→call→pre-IO-peek→trampoline→post-IO-peek sequence
        // — the same body the `--link` startup stub drives — and returns a
        // `ProgramOutcome` WITHOUT exiting (REPL-safe) and WITHOUT clearing the
        // error slots (we drain them below to build the structured error). This
        // is the single owner of the three former lockstep slot-check points;
        // the host no longer transcribes them.
        //
        // SAFETY: `code_ptr` is non-null — returned from `lookup_main_code_ptr`
        // which errors on None. It points to finalized JIT code compiled by
        // Cranelift via `compile_and_register_defn`, with the
        // `extern "C" fn() -> i64` calling convention (zero-arg defn, i64
        // return) the driver transmutes to.
        let outcome =
            cranelisp_intrinsics::panic::cranelisp_run_program(code_ptr, result_type.is_io());

        // Translate the outcome → structured error / (value, Type) for
        // `main.rs::run`. The host (NOT the driver) drains the SET slot to
        // compose the message — `error.rs`'s `PlatformError::DispatchError`
        // Display stays the host-side single source for the dispatch-fault text.
        match outcome.error_kind {
            // 1 = runtime error: the runtime-error slot is SET (drain for text).
            1 => {
                let err = cranelisp_intrinsics::panic::take_runtime_error()
                    .unwrap_or_else(|| "runtime panic".to_string());
                Err(CranelispError::CodegenError {
                    message: format!("runtime panic: {}", err),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })
            }
            // 2 = dispatch fault: the dispatch-fault slot is SET. int composes
            // the structured `PlatformError::DispatchError` from the
            // intrinsics-captured `(fn_name, cause)` (BC §4b invariant 14 / §5
            // invariant 9 — two-layer split).
            2 => {
                let fault =
                    cranelisp_intrinsics::panic::take_dispatch_fault().unwrap_or_else(|| {
                        cranelisp_intrinsics::panic::DispatchFault {
                            fn_name: "<unknown>".to_string(),
                            cause: "platform dispatch fault".to_string(),
                        }
                    });
                Err(CranelispError::Platform(
                    cranelisp_types::PlatformError::DispatchError {
                        fn_name: cranelisp_types::Symbol::from(fault.fn_name),
                        cause: fault.cause,
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    },
                ))
            }
            // 0 = clean: `outcome.exit_code` is the inner IO value (or main's own
            // result for a non-IO main). Ownership of that word crosses HERE,
            // into the ONE program-result owner (FIXME 0745). `IO a` is
            // unwrapped exactly once — at this driver boundary — so the owner
            // selects glue for the inner `a`, never for `IO a` (§4.4). The host
            // (`main.rs::run`) then observes the exit code and releases, in
            // that order, before any teardown.
            _ => {
                let result_type = if result_type.is_io() {
                    result_type.unwrap_io().clone()
                } else {
                    result_type
                };
                let resolver = crate::result_owner::SessionGlueResolver::for_result_code(
                    main.code_owner.as_ref(),
                    &self.shared.fresh_jit_drop_glues,
                );
                crate::result_owner::OwnedProgramResult::new(
                    outcome.exit_code,
                    result_type,
                    main.codegen_result_ty,
                    &ModuleFullPath::from(module_name),
                    &self.shared.symbol_tables,
                    &resolver,
                )
            }
        }
    }

    /// One read of the entry module's `main` entry, yielding everything the
    /// run path needs: the callable address, the declared result type, and the
    /// code lifetime owner that the result owner's release target must be
    /// paired with (`design/int/result-owner.md` §3.2 step 3 / §4.3).
    ///
    /// Replaces the former `lookup_main_code_ptr` + `lookup_main_return_type`
    /// pair. That pair took two independent reads and the type half fell back
    /// to `Type::Int` when the entry was absent — a fallback that must never
    /// reach the owner constructor as an authoritative classification. With
    /// one read there is no second lookup and therefore no fallback: an absent
    /// or non-`Fn`-schemed `main` produces the same "no `main`" diagnostic the
    /// pointer half always produced.
    fn read_main_entry(&self, module_name: &str) -> Result<MainEntryRead, CranelispError> {
        let module_path = ModuleFullPath::from(module_name);
        let no_main = || CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)"
                .into(),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        };

        // GOT is the single source of callable addresses (D41/D35); read
        // `main`'s pointer from its GOT slot rather than a `Code::ptr`.
        // The callable slot now rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        let table = self
            .shared
            .symbol_tables
            .get(&module_path)
            .ok_or_else(no_main)?;
        let entry = table.get("main").ok_or_else(no_main)?;
        let ModuleEntry::Def {
            code: Some(code_owner),
            scheme,
            ..
        } = entry
        else {
            return Err(no_main());
        };
        let slot = entry.callable_got_slot().ok_or_else(no_main)?;
        let code_ptr = table.got.load_slot(slot);
        if code_ptr.is_null() {
            return Err(no_main());
        }
        // `validate_main` (run before this read) guarantees `(Fn [] (IO _))`,
        // so a non-`Fn` scheme here is unreachable; it takes the same
        // diagnostic rather than defaulting to a type nobody derived.
        let Type::Fn(_, ret) = &scheme.ty else {
            return Err(no_main());
        };
        Ok(MainEntryRead {
            code_ptr,
            result_type: *ret.clone(),
            code_owner: Some(code_owner.clone()),
            codegen_result_ty: entry.codegen_view().map(|view| view.body.ty().clone()),
        })
    }

    /// Wait until all registered modules have object codegen complete.
    ///
    /// Block until all in-memory codegen (JIT) is complete.
    pub fn wait_inmem_complete(&self) -> Result<(), crate::scheduler::SchedulerError> {
        self.shared.scheduler.wait_inmem_complete()
    }

    /// Hand the ENTRY module over to the eval thread (S93, Invariant SW —
    /// structural successor to the retired `eval_owned` flag). Called by the
    /// REPL driver (`main.rs`) once startup typecheck has completed and the eval
    /// loop is about to take over.
    ///
    /// After startup the entry module sits in its terminal pool
    /// (`TypecheckDone`) — it is NOT in any typecheck queue, so no pool worker
    /// can re-claim it for typecheck. The eval thread is therefore its sole
    /// orchestrator *by construction*: a dependency gap the eval thread hits
    /// during a REPL form is driven by the eval thread's own wait+retry
    /// (`register_dep_for_eval`), and the entry never enters `TypecheckBlocked`
    /// (the eval path records a cycle-check edge via
    /// `register_dep_edge_for_cycle_check` instead), so `try_unblock_locked`
    /// cannot requeue it. This closes the B1 dual-orchestration with no role
    /// flag. The call drops the entry's startup sexps so even a stray dispatch
    /// would find an empty cluster (belt-and-braces).
    pub fn mark_entry_eval_owned(&self) {
        self.shared
            .scheduler
            .release_entry_sexps(&self.entry_module);
    }

    /// Promotes nice workers to normal priority before blocking, ensuring
    /// object codegen completes promptly (e.g., before linking). Wakes
    /// the `object_work_available` condvar so workers observe the promotion
    /// flag on their next loop iteration.
    pub fn wait_object_complete(&self) -> Result<(), crate::scheduler::SchedulerError> {
        // When no nice workers are running (e.g., tests with nice_workers: 0),
        // no .o files will be produced. Skip the wait to avoid blocking
        // forever. Sprint 67 Cluster B sub-fire 2a/2b: nice-worker count
        // read via the `WorkerPool` facade method.
        if self.worker_pool.nice_worker_count() == 0 {
            return Ok(());
        }

        // Promote nice workers so object codegen runs at full speed.
        self.shared
            .promote_nice_workers
            .store(true, std::sync::atomic::Ordering::Release);
        // Wake workers so they observe the promotion flag.
        self.shared.scheduler.wake_object_workers();

        let result = self.shared.scheduler.wait_object_complete();

        // Flush the cache manifest to disk so the next session can detect
        // cache hits. Sprint 67 Cluster B sub-fire 3: ObjectCache facade.
        self.shared.cache.flush_manifest();

        result
    }

    /// Flush the final `.o`/`.meta.json` persist for the REPL's mutated
    /// modules (S101 R18 — deterministic final persist at `/quit`).
    ///
    /// Defining turns already re-enqueue their module per-turn
    /// (`regenerate_backing_file` → `mark_object_stale`), but EXPRESSION
    /// turns mutate the live table too (the synthetic `__expr` wrapper
    /// allocates a live GOT slot on the module's monotone counter) without
    /// any persist trigger — so the on-disk meta's `next_got_slot` snapshot
    /// raced whatever turn the nice worker last observed. Marking the REPL's
    /// active modules stale here, BEFORE the caller's `wait_object_complete`,
    /// pins the persisted snapshot to the session's FINAL table state.
    pub fn flush_final_persist(&self) {
        self.shared.scheduler.mark_object_stale(&self.entry_module);
        if self.current_repl_module != self.entry_module {
            self.shared
                .scheduler
                .mark_object_stale(&self.current_repl_module);
        }
    }

    /// Shut down the session: signal workers to drain and exit.
    ///
    /// Sets the scheduler shutdown flag (wakes all condvars) and joins
    /// both the persistent priority and nice worker pools. Workers
    /// observe the shutdown flag via `take_priority_work_blocking` /
    /// `take_object_codegen` returning `None` and exit their loops.
    ///
    /// Idempotent: safe to call twice; the second call joins no
    /// additional handles. Called automatically by `Drop` as a safety net
    /// for tests that never call `shutdown()` explicitly.
    /// Sprint 57 Wave 4 G9 per `persistent-workers.md` §5.2.
    pub fn shutdown(&mut self) {
        // S91 Pillar 3 — bounded settle for the importable-symbol burn-down
        // (REPL only; the index is armed only in REPL, R17). Give the in-flight
        // burn-down a BRIEF chance to finish so a short interactive (or piped)
        // session over a small reachable set still warms the index `.meta`s
        // (§25.5 "the small burn-down completes promptly"). This is a bounded
        // best-effort grace period, NOT a drain-to-completion correctness gate:
        // R18 (abandon-on-shutdown) holds — atomic `.meta` writes mean a
        // timeout leaves at worst some modules unindexed (re-derived next
        // session), never a corrupt `.meta`. The cap keeps shutdown prompt for a
        // large reachable set (the worklist is simply abandoned).
        if self.shared.run_mode.is_repl() && self.shared.importable_indices.is_armed() {
            // Un-promote the nice workers for the settle: `wait_object_complete`
            // (the pre-shutdown caller) may have set `promote_nice_workers`,
            // which makes the nice-worker loop object-codegen-scoped (it skips
            // index work while promoted, R18 abandon-on-flush). Clearing it +
            // waking the workers lets the in-flight burn-down drain in the grace
            // window. (Object codegen is already complete by this point — the
            // REPL loop ran `wait_object_complete`.)
            self.shared
                .promote_nice_workers
                .store(false, std::sync::atomic::Ordering::Relaxed);
            self.shared.scheduler.wake_object_workers();
            let deadline = std::time::Instant::now() + SHUTDOWN_INDEX_SETTLE_TIMEOUT;
            while self.shared.importable_indices.pending_count() > 0 {
                if std::time::Instant::now() >= deadline {
                    break;
                }
                std::thread::sleep(SHUTDOWN_INDEX_SETTLE_POLL);
            }
        }
        self.shared.scheduler.shutdown();
        // Sprint 67 Cluster B sub-fire 2a/2b: join routing migrated through
        // `WorkerPool::shutdown` (the facade method-surface landing). The
        // priority + nice handle drains live inside `WorkerPool`; this call
        // is the load-bearing entry point — S68 may reshape internals
        // freely without changing this call site.
        self.worker_pool.shutdown();
    }

    /// Scaffold a default `{project_root}/Cranelisp.toml` if one does not
    /// already exist (S91 FIXME 0410). REPL-only convenience: the caller
    /// (`main.rs` REPL arm, gated on the §0.5 rule-3 directory target) renders
    /// the `[created Cranelisp.toml]` notice from an `Ok(true)` return.
    ///
    /// Delegates to `session_setup::scaffold_project_config` against this
    /// session's own resolved `project_root` — never overwrites, atomic,
    /// graceful on a read-only dir, resolution-neutral (every key commented).
    pub fn scaffold_project_config(&self) -> std::io::Result<bool> {
        crate::session_setup::scaffold_project_config(&self.shared.project_root)
    }

    // -----------------------------------------------------------------------
    // Degraded startup load (S102 CS-0489; repl/spec.md §18.8 restart floor;
    // design/int/s102-defect-wave.md §5.2)
    // -----------------------------------------------------------------------

    /// Recover from an entry-module startup failure in REPL mode: the §18.8
    /// floor — "the restart MUST reach a prompt". Batch-cluster atomicity is
    /// what turns one broken defn into a wholesale lockout; the REPL's own
    /// per-form semantics are the natural degraded mode.
    ///
    /// 1. Reset the failed scheduler state and re-register the entry EMPTY,
    ///    reaching the ordinary fresh-REPL scheduler state (terminal pool;
    ///    the eval thread becomes the sole orchestrator exactly as on a
    ///    healthy start).
    /// 2. Re-read the backing source (disk-read-only — the loader itself
    ///    never regenerates) and drive it FORM-BY-FORM through the ordinary
    ///    eval path, output suppressed. Green forms commit; failing forms
    ///    are retained as [`FailedForm`]s (symbol + error + verbatim text).
    /// 3. Report: `[errors: <file>]` + one indented line per failed form
    ///    naming the symbol and carrying the underlying error (§5.1/§14.3
    ///    format family); the caller prints it before the banner.
    /// 4. While the failed set is non-empty the entry sits in
    ///    `error_modules` (§14.4: expressions refused, definitions accepted
    ///    as the repair — the `process_commands` carve-out).
    ///
    /// Startup-print ruling (S102 W5, noted for /design): the degraded
    /// re-drive against a warm (cache-preloaded) table classifies
    /// Def-over-Def outcomes and would print `stale:`/cascade sections —
    /// suppressed here (`pending_cascade_reports` drained), because startup
    /// is a LOAD, not a user redefinition turn.
    ///
    /// Returns `Some(report)` when forms failed; `None` when the degraded
    /// load came up fully green (the failure was transient — e.g. a
    /// batch-order artifact) or no backing source could be read (the session
    /// proceeds as an empty REPL).
    pub fn recover_startup_failure(&mut self, module_name: &str) -> Option<String> {
        let module = ModuleFullPath::from(module_name);

        // 1. Reset failed scheduler state (entry + any failed deps are
        //    removed; deps re-register on demand through the eval dep drive).
        //    Scheduler-only — the entry's table is re-seeded just below and the
        //    degraded re-drive re-populates from source, so no table purge here
        //    (contrast the autoload-retry reset, which drops stale dep tables).
        let _ = self.shared.scheduler.reset_all_failed_modules();
        cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &module);
        let empty: std::sync::Arc<[Sexp]> = std::sync::Arc::from(Vec::<Sexp>::new());
        self.shared
            .scheduler
            .register_module(module.clone(), empty, false);
        let _ = self.shared.scheduler.wait_inmem_complete_blocking();

        // 2. Disk-read-only re-read + degraded form-by-form load.
        // S102 W5R M-4: a failed startup must not be zero-diagnostic — the
        // resolve/read failure is eprinted (one line) before the session
        // proceeds as an empty REPL.
        let lib_dirs = self.lib_dirs();
        let path = match crate::pipeline::resolve_module_file(
            &module,
            &self.shared.project_root,
            &lib_dirs,
        ) {
            Some(p) => p,
            None => {
                eprintln!(
                    "Warning: startup recovery: no backing source file found for \
                     module '{module_name}' — starting with an empty REPL"
                );
                return None;
            }
        };
        let source = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "Warning: startup recovery: cannot read {}: {e} — starting \
                     with an empty REPL",
                    path.display()
                );
                return None;
            }
        };
        let file_name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or(module_name)
            .to_string();
        let failed = self.degraded_form_load(&source);

        // Startup-print suppression (ruling above).
        self.pending_cascade_reports.clear();

        if failed.is_empty() {
            self.failed_forms.remove(&module);
            self.error_modules.remove(&module);
            return None;
        }
        let report = render_startup_error_report(&file_name, &failed);
        self.error_modules.insert(module.clone());
        self.failed_forms.insert(module, failed);
        Some(report)
    }

    /// Drive `source` form-by-form through the ordinary eval path (each
    /// toplevel form its own cluster, output suppressed), collecting the
    /// forms that fail. A whole-source parse failure retains the entire text
    /// as one symbol-less [`FailedForm`] (regen must not drop it either).
    fn degraded_form_load(&mut self, source: &str) -> Vec<FailedForm> {
        let sexps = match cranelisp_frontend::parse(source) {
            Ok(s) => s,
            Err(e) => {
                return vec![FailedForm {
                    symbol: None,
                    error: first_line(&e.to_string()),
                    text: source.trim_end().to_string(),
                }];
            }
        };
        let mut failed = Vec::new();
        for sexp in &sexps {
            match self.process_single_form(sexp) {
                Ok(_) => {} // green form committed; output suppressed
                Err(e) => {
                    let span = sexp.span();
                    let text = source
                        .get(span.start as usize..span.end as usize)
                        .map(str::to_string)
                        .unwrap_or_else(|| crate::pretty::pretty_print_plain(sexp));
                    failed.push(FailedForm {
                        symbol: defined_symbol_of_form(sexp),
                        error: first_line(&e.to_string()),
                        text,
                    });
                }
            }
        }
        failed
    }

    /// Remove a genuinely (re)defined symbol from its module's failed-form
    /// set (§18.8: a successful definition turn IS the repair). When the set
    /// empties, the module leaves `error_modules` — the §14.4 gate reopens
    /// and the next regen writes a green backing file. Display-only `Def`s
    /// (`defined: false`) and expression turns never clear anything.
    pub(crate) fn clear_repaired_failed_form(&mut self, result: &super::EvalResult) {
        let super::EvalResult::Def {
            symbol,
            defined: true,
            ..
        } = result
        else {
            return;
        };
        let Some(list) = self.failed_forms.get_mut(&symbol.module) else {
            return;
        };
        list.retain(|f| f.symbol.as_ref() != Some(&symbol.symbol));
        if list.is_empty() {
            self.failed_forms.remove(&symbol.module);
            self.error_modules.remove(&symbol.module);
        }
    }

    /// §3.1: Register entry module by name. Session resolves the source
    /// file from project_root + lib_dirs, reads it, and registers with
    /// the scheduler.
    pub fn register_entry_module(
        &mut self,
        module_name: &str,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        // Resolve source file: project_root (tier 2) then lib_dirs (tier 3).
        let lib_dirs = self.lib_dirs();
        let file_path =
            crate::pipeline::resolve_module_file(&module, &self.shared.project_root, &lib_dirs);
        let (source, entry_path) = match file_path {
            Some(path) => {
                let src = std::fs::read_to_string(&path).unwrap_or_default();
                (src, path)
            }
            None => {
                // No file found — empty module (e.g., fresh REPL).
                let default_path = self.shared.project_root.join(format!("{module_name}.cl"));
                (String::new(), default_path)
            }
        };

        // Register the entry module's own file in file_to_module so the
        // file watcher can detect changes to it (not just its dependencies).
        if let Ok(canonical) = entry_path.canonicalize() {
            self.shared
                .file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module.clone());
        }

        // S101 persistence pins (ii)–(iv) (spine §5.6; design/int/
        // session-transaction.md §8): when the entry module's persisted
        // `.meta.json` is still valid for THIS source, pre-seed the live
        // table from it BEFORE the from-source recompile. Persisted GOT slot
        // numbers are load-bearing against the cached `.o`'s machine code —
        // the recompile's staging→live commit then REUSES each symbol's
        // persisted slot (the ordinary redefinition discipline) instead of
        // renumbering from 0, `next_got_slot` restores the high-water mark so
        // new definitions allocate strictly above every frozen hole, and the
        // holes survive un-renumbered. Bodies are still recompiled from
        // source (no stale code is ever served — the §18.8 floor); only the
        // slot assignments and schemes carry over.
        self.preload_entry_slot_assignments(&module, &source);

        self.register_module_with_source(module_name, &source, &entry_path)
    }

    /// Pre-seed the entry module's live table from its persisted `.meta.json`
    /// when (and only when) the cache manifest validates the CURRENT backing
    /// source — the slot-stability half of the L-R5 persistence pins. On any
    /// miss (no cache, hash changed, schema bump, decode failure) this is a
    /// silent no-op and the from-source build starts from an empty table
    /// (fresh numbering — correct, since the persisted slots' `.o` is invalid
    /// anyway).
    fn preload_entry_slot_assignments(&self, module: &ModuleFullPath, source: &str) {
        use cranelisp_backend::cache;

        if source.trim().is_empty() {
            return;
        }
        let Some(cache_dir) = self.shared.cache.cache_dir() else {
            return;
        };
        let hash = cache::manifest::hash_source(source);
        if !self
            .shared
            .cache
            .is_cache_valid(module, &hash, &std::collections::HashMap::new())
        {
            return;
        }
        let Ok(Some(cached)) = cache::try_load_cached_module(&cache_dir, module) else {
            return;
        };
        let mut table = cached.symbol_table.into_concrete::<Code, ()>();
        // The synthetic `__expr` wrapper is a per-turn artifact, not a user
        // definition — dropping it keeps the codegen batch sweep from
        // recompiling a stale persisted expression body.
        table.symbols.remove(crate::worker::SYNTHETIC_EXPR_WRAPPER);
        // Fresh type vars must not collide with the persisted schemes' ids.
        cranelisp_typecheck::advance_next_id_past_table(&self.shared.next_type_id, &table);
        cranelisp_types::install_module(&self.shared.symbol_tables, module.clone(), table);
    }

    /// §8: Link by module name. Collects .o files produced by nice workers,
    /// generates a startup stub, and invokes the system linker.
    ///
    /// Must be called after `wait_object_complete()` — all .o files must
    /// be ready.
    pub fn link_by_name(
        &mut self,
        module_name: &str,
        output_override: Option<&Path>,
    ) -> Result<(), CranelispError> {
        let module = ModuleFullPath::from(module_name);

        // Validate main exists and determine return kind (Int vs IO).
        let entry_table =
            self.module_table(&module)
                .ok_or_else(|| CranelispError::ModuleError {
                    message: format!("entry module '{}' not found in typechecker", module_name),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                })?;
        // Enforce the batch-mode signature `(Fn [] (IO _))` (spec §10.6 /
        // §12.6). A valid `main` always returns `IO _` after this gate — the
        // startup stub therefore always trampolines the IO result.
        // 0611: the entry module's unresolved-return-poly-dispatch carrier
        // (EMPTY for every valid module) routes a `main` whose body carries one
        // to the §3.11 ambiguity (class (b)) instead of `main has no GOT slot`.
        let dispatch = self
            .shared
            .typecheck_products
            .get(&module)
            .map(|tp| tp.unresolved_dispatch.clone())
            .unwrap_or_default();
        crate::exe::validate_main(&entry_table, &dispatch)?;
        drop(entry_table);
        // FIXME 0406 (test-discovery.md §4.5): refuse a `--link` build that
        // references a dev-session-only `PrimitiveExtern` (`discover-tests`)
        // BEFORE invoking `cc` — a friendly compile-time diagnostic instead of
        // the raw `undefined reference to discover-tests` linker error. Scans
        // every linked module (not just the entry); the offending callee can
        // live in any module dragged into the link.
        crate::exe::reject_dev_session_externs_in_link(&self.shared.symbol_tables)?;
        let entry_table =
            self.module_table(&module)
                .ok_or_else(|| CranelispError::ModuleError {
                    message: format!("entry module '{}' not found in typechecker", module_name),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                })?;
        // Sprint 58 Wave 2 / Decision 36: read the entry module's `main`
        // GOT slot index now (before dropping the table guard). The alias
        // `.o` (emitted below) routes the system linker's `_main` import
        // through this slot via `__cranelisp_got_{entry_module}`.
        let main_got_slot = crate::exe::entry_main_got_slot(&entry_table)?;
        drop(entry_table);

        // Every main accepted by `validate_main` returns `IO _`, so the startup
        // stub always includes the IO trampoline.
        let main_returns_io = true;

        // Collect .o paths from nice workers. Sprint 67 Cluster B sub-fire 3:
        // ObjectCache facade.
        let o_paths = self.shared.cache.all_paths();

        if o_paths.is_empty() {
            return Err(CranelispError::ModuleError {
                message: "no .o files produced — cannot link".into(),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        }

        // Source the platforms the program loaded at compile time (via
        // `(platform "…")` → `load_and_register_platform`, retained on
        // `kept_dlls`) and derive the three `--link` inputs from them
        // (platform-interface.md §7.3): the rlib paths the linker force-loads,
        // the manifest symbol names the startup stub calls, and the per-platform
        // layout-hash checks the startup stub bakes.
        let (platform_manifest_names, platform_rlib_paths, platform_layout_checks) =
            self.linked_platform_link_data()?;

        // Sprint 58 Wave 2 / Decision 36: every user-defined function is
        // declared bare-`Linkage::Local` by `compile_to_module` (no
        // module-qualified naming). The startup stub references the user-main
        // symbol as `Linkage::Import`; the linker resolves it against the alias
        // `.o` we emit below, which exports that symbol and tail-calls through
        // the entry module's GOT.
        //
        // FIXME 0324 (§11.3): the entry-stub and user-main symbol names are
        // host-dependent. macOS keeps `start` / `main` (custom crt-bypassing
        // entry). Linux routes through crt by emitting the stub as C `main`, so
        // the user-main alias is renamed `cranelisp_user_main` to avoid
        // colliding with the C `main`. Both come from `host_entry_symbols()`.
        let (stub_entry_symbol, entry_fn_name) = crate::exe::host_entry_symbols()?;

        // Generate startup .o stub. The per-platform layout-hash checks
        // (platform-interface.md §5.5.4 `--link` gate) are derived above from the
        // linked platforms (`linked_platform_link_data`): for each platform that
        // exported a layout hash, the compiler regenerates the schema from the
        // live `platform.<name>` table and bakes the resulting expected hash, so
        // a stale platform builds but aborts at process start. Empty when no
        // platform is linked (the as-built no-platform path).
        let startup_bytes = crate::exe::generate_startup_object(
            &platform_manifest_names,
            main_returns_io,
            entry_fn_name,
            stub_entry_symbol,
            &platform_layout_checks,
        )?;

        // Sprint 67 Cluster B sub-fire 3: cache dir via ObjectCache facade.
        let cache_dir =
            self.shared
                .cache
                .cache_dir()
                .ok_or_else(|| CranelispError::ModuleError {
                    message: "cache directory not configured — cannot write startup .o".into(),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                })?;
        let startup_o_path = cache_dir.join("__startup.o");
        std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write startup .o: {e}"),
                location: ErrorLocation::from_span_file(
                    Span::SYNTHETIC,
                    Some(startup_o_path.clone()),
                ),
            }
        })?;

        // Sprint 58 Wave 2 / Decision 36 `--link` exception: emit the
        // `_main` Export alias `.o` that tail-calls into the entry
        // module's GOT slot for `main`. Without this alias the system
        // linker has no `_main` symbol to resolve (the entry module's
        // bare `main` is `Linkage::Local`), and link fails with
        // "undefined symbol _main".
        let alias_bytes =
            crate::exe::generate_main_alias_object(&module, main_got_slot, entry_fn_name)?;
        let alias_o_path = cache_dir.join("__main_alias.o");
        std::fs::write(&alias_o_path, &alias_bytes).map_err(|e| CranelispError::ModuleError {
            message: format!("failed to write main alias .o: {e}"),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(alias_o_path.clone())),
        })?;

        // Find the runtime bundle library.
        let bundle_lib = crate::exe::find_bundle_lib()?;

        // Output path (repl/spec.md §0.2.1.1, FIXME 0550): the artifact is named
        // after the entry (root) module's source-file STEM and written BESIDE
        // that source — in the project root, the directory holding
        // `{module}.cl` — NOT the entry stem in the CWD. `-o <path>` overrides
        // verbatim. E.g. `--link examples/hello.cl` → `examples/hello`;
        // `--link myproject` (entry `user`) → `myproject/user`. This resolves
        // the original CWD name-collision (writing `./user` from the repo root
        // clashed with the `user/` docs directory).
        let output_path =
            derive_link_output_path(&self.shared.project_root, module_name, output_override);

        // Collision floor (§0.2.1.1 MUST): a directory at the resolved output
        // path is a clear cranelisp diagnostic naming the path, never a raw
        // `ld`/`cc` "cannot open output file … Is a directory" error.
        reject_output_path_is_directory(&output_path)?;

        // Compose the final .o list: nice-worker module .o files +
        // the `_main` alias .o. The alias is appended last so its Export
        // `_main` resolves the startup stub's Import.
        let mut all_o_paths = o_paths;
        all_o_paths.push(alias_o_path);

        // Link.
        crate::exe::link_executable(
            &output_path,
            &all_o_paths,
            &startup_o_path,
            &bundle_lib,
            &platform_rlib_paths,
        )
    }

    /// Derive the three `--link` platform inputs from the loaded-platform
    /// registry (`SharedState::kept_dlls`) — platform-interface.md §7.3.
    ///
    /// Each `(platform "<name>")` declaration in the entry program loaded a DLL
    /// at compile time, retained on `kept_dlls`. For the standalone binary the
    /// linker must statically link those platforms instead. Returns, in order:
    ///
    /// - **manifest names** — the symbol the startup stub calls to populate each
    ///   platform's GOT (`collect_platform_manifest_names`);
    /// - **rlib paths** — the static archives the linker `-force_load`s
    ///   (`find_platform_rlibs`), so the platform's `#[export_name]` GOT +
    ///   manifest + layout-hash symbols resolve in the produced binary;
    /// - **layout-hash checks** — for each platform that exported a layout hash
    ///   (i.e. marshals ADTs), the compiler regenerates the schema from the live
    ///   `platform.<name>` table (the same backend generator the load-time gate
    ///   runs) and bakes the expected hash into the startup stub, so a stale
    ///   statically-linked platform aborts at process start (§5.5.4 `--link`
    ///   gate).
    pub(crate) fn linked_platform_link_data(
        &self,
    ) -> Result<
        (
            Vec<String>,
            Vec<PathBuf>,
            Vec<cranelisp_backend::exe::PlatformLayoutCheck>,
        ),
        CranelispError,
    > {
        // Dedup by platform identity (name) BEFORE handing the enumeration to
        // the backend. `kept_dlls` carries one `LoadedPlatform` per *processed*
        // `(platform <P>)` form, and a multi-module program re-processes the
        // entry module's `(platform <P>)` form on every retry-from-top
        // dependency drive (S78 cluster orchestration) — so the SAME platform
        // appears in `kept_dlls` once per retry. Without dedup the backend
        // startup-stub emitter (`exe.rs` ~:221/:236) tries to `define_data` the
        // same `__cranelisp_expected_hash_<P>` / `__cranelisp_layout_name_<P>`
        // symbols once per duplicate → "Duplicate definition of identifier"
        // (DEF-4), and `find_platform_rlibs` lists the same `.rcgu.o` set twice
        // → "multiple definition" on layout-hash-less platforms. Each platform
        // must contribute exactly one layout-check entry and one kept-DLL entry
        // regardless of how many modules (or retries) reference it.
        let platform_names: Vec<String> = {
            let guard = self
                .shared
                .kept_dlls
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            dedup_platform_names_preserving_order(guard.iter().map(|p| p.name.as_str()))
        };

        // Per-platform-namespaced manifest symbols (DEF-5 / §5.5.5): the deduped
        // platform NAMES drive the symbol list, not the count, so two distinct
        // platforms produce two distinct `cranelisp_platform_manifest_<name>`
        // imports instead of colliding on a shared bare name.
        let manifest_names = crate::exe::collect_platform_manifest_names(&platform_names);

        let rlib_paths = crate::exe::find_platform_rlibs(
            &platform_names,
            &self.shared.project_root,
            &self.lib_dirs(),
            &self.platform_dirs(),
        )?;

        // Per-platform layout-hash checks: only for platforms that exported a
        // layout hash. The expected hash is regenerated from the live tables (NOT
        // read from the DLL) — the `--link` gate compares the compiler's
        // freshly-computed hash against the statically-linked
        // `__cranelisp_layout_hash_<name>`, so a drifted platform refuses.
        //
        // Driven off the SAME deduped name list as the manifest/rlib inputs so
        // each platform's gate symbols are emitted exactly once. A platform that
        // exported a layout hash is identified by its (unique) name; we re-read
        // the layout-hash presence from the first matching `kept_dlls` entry.
        let mut layout_checks = Vec::new();
        for name in &platform_names {
            let has_layout_hash = {
                let guard = self
                    .shared
                    .kept_dlls
                    .lock()
                    .unwrap_or_else(|e| e.into_inner());
                guard
                    .iter()
                    .find(|p| p.name == *name)
                    .map(|p| p.layout_hash.is_some())
                    .unwrap_or(false)
            };
            if !has_layout_hash {
                // Scalar-only platform (no ADTs) exports no hash — no gate.
                continue;
            }
            {
                let module_path = ModuleFullPath::from(format!("platform.{}", name));
                let roots = self
                    .shared
                    .symbol_tables
                    .get(&module_path)
                    .map(|t| cranelisp_backend::schema::platform_effect_roots(&t))
                    .unwrap_or_default();
                let expected_hash = cranelisp_backend::schema::compute_layout_hash(
                    &self.shared.symbol_tables,
                    &roots,
                );
                layout_checks.push(cranelisp_backend::exe::PlatformLayoutCheck {
                    name: name.clone(),
                    expected_hash,
                });
            }
        }

        Ok((manifest_names, rlib_paths, layout_checks))
    }
}

impl Drop for CompilerSession {
    fn drop(&mut self) {
        // Defensive: ensure workers are signalled and joined before this
        // session is destroyed. Prevents hangs (and mmap'd JIT pages going
        // out of scope while a worker still dereferences them) if the
        // session is dropped without an explicit `shutdown()` call — e.g.
        // during test teardown or panic unwinding. Sprint 57 Wave 4 G9
        // per `persistent-workers.md` §5.2.
        //
        // `shutdown()` is idempotent; calling it in Drop is safe even if
        // the caller already called it.
        self.shutdown();
    }
}

// ---------------------------------------------------------------------------
// Degraded-startup pure seams (S102 CS-0489; unit-tested below — the
// lifecycle decision paths FIXME 0496 item 3 asks for)
// ---------------------------------------------------------------------------

/// The symbol a top-level form DEFINES, when it is a defining special form
/// (`defn`/`defn-`/`defmacro`/`defmacro-`/`deftype`/`deftrait`). Structural
/// forms (`import`/`export`/`mod`/`platform`), expressions, and malformed
/// defining forms yield `None`. The degraded loader uses this to key
/// [`FailedForm`]s so the load error can NAME the broken symbol (§18.8) and
/// a later definition turn can repair it.
pub(crate) fn defined_symbol_of_form(sexp: &Sexp) -> Option<Symbol> {
    if let Sexp::List(items, _) = sexp
        && items.len() >= 2
        && let Sexp::Symbol(head, _) = &items[0]
        && matches!(
            head.as_str(),
            "defn" | "defn-" | "defmacro" | "defmacro-" | "deftype" | "deftrait"
        )
        && let Sexp::Symbol(name, _) = &items[1]
    {
        return Some(Symbol::from(name.as_str()));
    }
    None
}

/// Render the degraded-load startup report: the §14.3/§14.4 `[errors: <file>]`
/// header + one indented line per failed form, naming the symbol (§18.8's
/// naming MUST) — or, for a symbol-less form, its leading text — and carrying
/// the underlying error.
pub(crate) fn render_startup_error_report(file_name: &str, failed: &[FailedForm]) -> String {
    let mut out = format!("[errors: {file_name}]");
    for f in failed {
        let label = match &f.symbol {
            Some(sym) => sym.to_string(),
            None => f
                .text
                .lines()
                .next()
                .unwrap_or("")
                .chars()
                .take(40)
                .collect(),
        };
        out.push_str(&format!("\n  {} — {}", label, f.error));
    }
    out
}

/// Append the retained failed-form verbatim texts to a regenerated module
/// source (§18.8 no-silent-drop: the failed forms never entered the live
/// table, so a regen built from the table alone would drop them from the
/// user's file). Re-emitted until each form's symbol is repaired or the user
/// removes it externally.
pub(crate) fn append_failed_forms(generated: &str, failed: &[FailedForm]) -> String {
    if failed.is_empty() {
        return generated.to_string();
    }
    let mut out = generated.trim_end().to_string();
    for f in failed {
        if !out.is_empty() {
            out.push_str("\n\n");
        }
        out.push_str(f.text.trim_end());
    }
    out.push('\n');
    out
}

/// First line of an error rendering (report display).
fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or(s).trim().to_string()
}

pub(crate) fn populate_ring0_got_slots(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let Some(table) = symbol_tables.get(&primitives_path) else {
        // primitives module not seeded — register_builtins ordering broken.
        // Quietly skip; the regular pipeline error path will surface the
        // missing-module condition when a Ring 0 call is compiled.
        return;
    };
    // PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>. Deref the
    // LazyLock to the Arc, then `.as_ref()` to get `&SymbolTable`.
    let static_table = (*cranelisp_primitives::PRIMITIVES_TABLE).as_ref();
    // The callable slot rides on the `DefKind` variant (S83 reshape, FIXME
    // 0356/0357) — read both the static-source and session-dest slots via the
    // `callable_got_slot()` chokepoint.
    for (name, static_entry) in static_table.symbols.iter() {
        let Some(src_slot) = static_entry.callable_got_slot() else {
            continue;
        };
        let ptr = static_table.got.load_slot(src_slot);
        let Some(session_entry) = table.get(name.as_ref()) else {
            continue;
        };
        let Some(dst_slot) = session_entry.callable_got_slot() else {
            continue;
        };
        table.got.store_slot(dst_slot, ptr);
    }
}

/// Derive the `--link` output-executable path per `repl/spec.md` §0.2.1.1
/// (FIXME 0550).
///
/// The artifact is named after the entry (root) module's source-file **stem**
/// and written **beside that source** — i.e. into the project root, which is the
/// directory holding `{entry_module}.cl` (§0.5.1). One rule covers both cases:
///
/// - file target `examples/hello.cl` (project root `examples/`, entry `hello`)
///   → `examples/hello`;
/// - directory-project `myproject` (project root `myproject/`, entry `user`)
///   → `myproject/user` — **not** `myproject/myproject`, **not** `./user`.
///
/// An explicit `-o <path>` override wins verbatim; a relative override is left
/// relative, so the linker resolves it against the process cwd. On platforms
/// with an executable suffix (Windows) the suffix is appended to the *derived*
/// name (`myproject/user.exe`); an `-o` override is used exactly as given.
pub(crate) fn derive_link_output_path(
    project_root: &Path,
    entry_module_name: &str,
    output_override: Option<&Path>,
) -> PathBuf {
    if let Some(o) = output_override {
        return o.to_path_buf();
    }
    // Defensive `.cl` strip — the resolved entry module name is already
    // extension-free (§0.5.1), but never let a stray `.cl` leak into the name.
    let stem = entry_module_name
        .strip_suffix(".cl")
        .unwrap_or(entry_module_name);
    let mut name = stem.to_string();
    name.push_str(std::env::consts::EXE_SUFFIX);
    project_root.join(name)
}

/// Collision-diagnostic floor (`repl/spec.md` §0.2.1.1, MUST): if the resolved
/// `--link` output path is an existing **directory**, reject with a clear
/// cranelisp diagnostic naming the path, rather than surfacing a raw `ld`/`cc`
/// "cannot open output file … Is a directory" error (FIXME 0550).
fn reject_output_path_is_directory(output_path: &Path) -> Result<(), CranelispError> {
    if output_path.is_dir() {
        return Err(CranelispError::ModuleError {
            message: format!(
                "output path '{}' is a directory — use -o <path> to choose a \
                 different output",
                output_path.display()
            ),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        });
    }
    Ok(())
}

#[cfg(test)]
mod link_output_path_tests {
    use super::*;

    // spec: repl/spec.md §0.2.1.1 — file target: the artifact is the entry
    // module stem beside its source (project root), not the stem in the CWD.
    // `examples/hello.cl` (project root `examples/`, entry `hello`) → `examples/hello`.
    #[test]
    fn file_target_output_is_entry_stem_beside_source() {
        let out = derive_link_output_path(Path::new("/work/examples"), "hello", None);
        assert_eq!(
            out,
            PathBuf::from(format!(
                "/work/examples/hello{}",
                std::env::consts::EXE_SUFFIX
            ))
        );
    }

    // spec: repl/spec.md §0.2.1.1 — directory-project target: entry defaults to
    // `user`, source at `myproject/user.cl`, so the artifact is `myproject/user`
    // (beside the source), NOT `myproject/myproject` and NOT `./user`.
    #[test]
    fn directory_project_output_is_user_stem_in_project_root() {
        let out = derive_link_output_path(Path::new("/work/myproject"), "user", None);
        assert_eq!(
            out,
            PathBuf::from(format!(
                "/work/myproject/user{}",
                std::env::consts::EXE_SUFFIX
            ))
        );
        // Negative: it is NOT the project-directory name, NOT the CWD stem.
        assert_ne!(out, PathBuf::from("/work/myproject/myproject"));
        assert_ne!(out, PathBuf::from("user"));
    }

    // spec: repl/spec.md §0.2.1.1 — `-o <path>` override wins verbatim; a
    // relative override is left relative (linker resolves it against cwd).
    #[test]
    fn output_override_wins_verbatim() {
        let abs = derive_link_output_path(
            Path::new("/work/myproject"),
            "user",
            Some(Path::new("/tmp/out/bin")),
        );
        assert_eq!(abs, PathBuf::from("/tmp/out/bin"));
        let rel = derive_link_output_path(
            Path::new("/work/myproject"),
            "user",
            Some(Path::new("build/app")),
        );
        assert_eq!(rel, PathBuf::from("build/app"));
    }

    // spec: repl/spec.md §0.2.1.1 — defensive `.cl` strip: a stray extension on
    // the entry name never leaks into the artifact name.
    #[test]
    fn entry_name_with_cl_extension_is_stripped() {
        let out = derive_link_output_path(Path::new("/work"), "hello.cl", None);
        assert_eq!(
            out,
            PathBuf::from(format!("/work/hello{}", std::env::consts::EXE_SUFFIX))
        );
    }

    // spec: repl/spec.md §0.2.1.1 — collision floor: an existing directory at
    // the output path yields a clear cranelisp diagnostic naming it as a
    // directory, exit-worthy, NOT a raw `ld`/`cc` error.
    #[test]
    fn existing_directory_output_path_is_rejected_with_diagnostic() {
        let td = tempfile::tempdir().unwrap();
        let dir_path = td.path().join("user");
        std::fs::create_dir(&dir_path).unwrap();
        let err = reject_output_path_is_directory(&dir_path)
            .expect_err("a directory output path must be rejected");
        let msg = format!("{err:?}");
        assert!(
            msg.to_lowercase().contains("directory"),
            "diagnostic must name that the path is a directory: {msg}"
        );
        // Negative: no raw linker error phrasing leaks from the cranelisp floor.
        assert!(
            !msg.contains("cannot open output file"),
            "must not be a raw ld error: {msg}"
        );
    }

    // spec: repl/spec.md §0.2.1.1 — a non-directory (or absent) output path is
    // accepted by the collision floor.
    #[test]
    fn non_directory_output_path_is_accepted() {
        let td = tempfile::tempdir().unwrap();
        // Absent path: fine.
        assert!(reject_output_path_is_directory(&td.path().join("user")).is_ok());
        // A regular file at the path: fine (it will be overwritten by the linker).
        let file_path = td.path().join("prog");
        std::fs::write(&file_path, b"old").unwrap();
        assert!(reject_output_path_is_directory(&file_path).is_ok());
    }
}

#[cfg(test)]
mod degraded_startup_tests {
    use super::*;

    fn p(src: &str) -> Sexp {
        cranelisp_frontend::parse(src).unwrap().remove(0)
    }

    fn failed(symbol: Option<&str>, error: &str, text: &str) -> FailedForm {
        FailedForm {
            symbol: symbol.map(Symbol::from),
            error: error.to_string(),
            text: text.to_string(),
        }
    }

    // spec: repl/spec.md §18.8; 07-traits §§7.1–7.1.1 — the load error names
    // the broken symbol; the fixture uses the normative trait-method syntax;
    // degraded loader keys failed forms by the DEFINING form's name. Matrix A
    // "backing BROKEN" row, classification cells.
    #[test]
    fn defined_symbol_of_form_defining_heads_yield_symbol() {
        assert_eq!(
            defined_symbol_of_form(&p("(defn k [:Int y] (f y))")),
            Some("k".into())
        );
        assert_eq!(
            defined_symbol_of_form(&p("(defmacro m [e] e)")),
            Some("m".into())
        );
        assert_eq!(
            defined_symbol_of_form(&p("(deftype P [:Int x])")),
            Some("P".into())
        );
        assert_eq!(
            defined_symbol_of_form(&p("(deftrait Show (show [a] String))")),
            Some("Show".into())
        );
    }

    // Negative cells: structural forms define no repairable symbol;
    // expressions and malformed defining forms yield None.
    // spec: repl/spec.md §18.8
    #[test]
    fn defined_symbol_of_form_neg_structural_expression_malformed() {
        assert_eq!(defined_symbol_of_form(&p("(import [m [mf]])")), None);
        assert_eq!(defined_symbol_of_form(&p("(mod child)")), None);
        assert_eq!(defined_symbol_of_form(&p("(k 1)")), None);
        assert_eq!(defined_symbol_of_form(&p("42")), None);
        // Defining head with a non-symbol name slot (the D1 poison shape).
        assert_eq!(defined_symbol_of_form(&p("(defn (weird) [] 1)")), None);
    }

    // spec: repl/spec.md §18.8 + §14.3 format family — the startup report is
    // `[errors: <file>]` + one indented line per failed form naming the
    // symbol and carrying the underlying error; a symbol-less form is
    // identified by its leading text.
    #[test]
    fn render_startup_error_report_names_symbols_and_errors() {
        let report = render_startup_error_report(
            "user.cl",
            &[
                failed(
                    Some("k"),
                    "type error at 49..60: expected Int",
                    "(defn k [:Int y] (f y))",
                ),
                failed(None, "macro error: boom", "(mystery-form 1)"),
            ],
        );
        assert_eq!(
            report,
            "[errors: user.cl]\n  k — type error at 49..60: expected Int\n  (mystery-form 1) — macro error: boom"
        );
    }

    // spec: repl/spec.md §18.8 — regen MUST NOT silently drop a broken
    // definition: retained failed-form texts are re-emitted VERBATIM after
    // the generated source; an empty failed set leaves the source untouched.
    #[test]
    fn append_failed_forms_reemits_verbatim_and_is_noop_when_empty() {
        let generated = "(defn f [:String s] (str-len s))\n";
        let out = append_failed_forms(
            generated,
            &[failed(
                Some("k"),
                "type error",
                "(defn k [:Int y]\n  (f y))",
            )],
        );
        assert_eq!(
            out, "(defn f [:String s] (str-len s))\n\n(defn k [:Int y]\n  (f y))\n",
            "authored text is the authority — appended verbatim, own block"
        );
        assert_eq!(
            append_failed_forms(generated, &[]),
            generated,
            "no failed forms — regen output unchanged"
        );
        // An empty generated source still carries the failed forms (a module
        // whose every form failed must not regenerate to an empty file).
        assert_eq!(
            append_failed_forms("", &[failed(None, "parse error", "(broken (")]),
            "(broken (\n"
        );
    }

    // spec: repl/spec.md §18.8 (FIXME 0496 — src/ unit-tier drain; the T1
    // full-cure CS-3 regen-fidelity adjacency). The PRIVATE defining heads
    // (`defn-`/`defmacro-`) are repairable/regenerable symbols exactly like
    // their public forms — a T1 reload failure that retains a private def as a
    // FailedForm must key it by name so regen re-emits it and `/info` names it.
    #[test]
    fn defined_symbol_of_form_private_defining_heads_yield_symbol() {
        assert_eq!(
            defined_symbol_of_form(&p("(defn- helper [x] x)")),
            Some("helper".into())
        );
        assert_eq!(
            defined_symbol_of_form(&p("(defmacro- m- [e] e)")),
            Some("m-".into())
        );
    }

    // spec: repl/spec.md §18.8 (FIXME 0496) — the CS-3 error-blocked floor may
    // retain MORE THAN ONE failed form (e.g. a caller AND a transitively
    // ill-typed sibling). Each rides its own verbatim block, in order, after
    // the generated source — never merged, never dropped, never reordered.
    #[test]
    fn append_failed_forms_multiple_forms_each_own_block_in_order() {
        let out = append_failed_forms(
            "(defn f ([:Int x] x) ([:String s] (str-len s)))\n",
            &[
                failed(Some("g"), "ambiguous call to 'f'", "(defn g [y] (f y))"),
                failed(Some("h"), "ambiguous call to 'f'", "(defn h [z] (f z))"),
            ],
        );
        assert_eq!(
            out,
            "(defn f ([:Int x] x) ([:String s] (str-len s)))\n\n\
             (defn g [y] (f y))\n\n(defn h [z] (f z))\n",
            "each retained failed form is a verbatim block, in retention order"
        );
    }

    // spec: repl/spec.md §18.5 (FIXME 0496) — `first_line` reduces a
    // multi-line error rendering to its §18.3 one-line reason (leading line,
    // trimmed); a single-line or empty input passes through.
    #[test]
    fn first_line_reduces_to_leading_trimmed_line() {
        assert_eq!(
            first_line("  type error at 0..4: boom  \n  detail\n more"),
            "type error at 0..4: boom"
        );
        assert_eq!(first_line("single line"), "single line");
        assert_eq!(first_line(""), "");
    }
}

#[cfg(test)]
mod restore_notice_tests {
    use super::FailedForm;
    use super::{is_persisted_definition_form, restored_definition_count};

    fn parse_one(src: &str) -> cranelisp_types::Sexp {
        cranelisp_frontend::parse(src).unwrap().remove(0)
    }

    fn failed_form(text: &str) -> FailedForm {
        FailedForm {
            symbol: None,
            error: "load error".to_string(),
            text: text.to_string(),
        }
    }

    // FIXME 0674 — the startup restore notice counts §15.7 persisted DEFINITION
    // forms; imports/exports/expressions are excluded (so an imports-only file
    // suppresses the notice).
    // spec: repl/spec.md §15.2.2 — restored-definition count.
    #[test]
    fn persisted_definition_forms_are_classified() {
        for src in [
            "(defn f [] 1)",
            "(defn- g [] 2)",
            "(def x 1)",
            "(const c 3)",
            "(deftype Color Red Green)",
            "(deftrait Show (show [a] a))",
            "(defmacro m [] 1)",
            "(impl Show Int (defn show [x] x))",
        ] {
            assert!(
                is_persisted_definition_form(&parse_one(src)),
                "def form: {src}"
            );
        }
    }

    #[test]
    fn non_definition_forms_are_excluded() {
        for src in [
            "(import [primitives [Int]])",
            "(export [foo [bar]])",
            "(mod child)",
            "(+ 1 2)",
            "42",
        ] {
            assert!(
                !is_persisted_definition_form(&parse_one(src)),
                "non-def: {src}"
            );
        }
    }

    // FIXME 0707 — the count is taken from the restore RECORD: a backing file
    // holding K succeeded + M failed persisted-definition forms (the degraded
    // startup re-emits the M failed forms into the file, so a bare re-parse sees
    // K+M) yields `K`, never `K+M`. Fail-on-revert: dropping the failed-form
    // subtraction makes this return `Some(3)`.
    // spec: repl/spec.md §15.2.2 — restored-definition count from the record.
    #[test]
    fn restored_count_subtracts_failed_persisted_forms() {
        // 2 green defs + 1 failed def, all present in the (re-emitted) file.
        let source = "(defn f [] 1)\n(defn g [] 2)\n(defn h [] (bad))\n";
        let failed = [failed_form("(defn h [] (bad))")];
        assert_eq!(
            restored_definition_count(source, &failed),
            Some(2),
            "count reflects restored defs (K), not file forms (K+M)",
        );
    }

    // No failed forms → all persisted defs count (the ordinary green path).
    #[test]
    fn restored_count_all_green_counts_all() {
        let source = "(defn f [] 1)\n(def x 1)\n";
        assert_eq!(restored_definition_count(source, &[]), Some(2));
    }

    // Every persisted def failed → nothing restored → suppress (None), not 0.
    #[test]
    fn restored_count_all_failed_suppresses() {
        let source = "(defn f [] (bad))\n";
        let failed = [failed_form("(defn f [] (bad))")];
        assert_eq!(restored_definition_count(source, &failed), None);
    }

    // A failed form that is NOT a persisted definition (an expression/import) is
    // not subtracted — it never contributed to the count.
    #[test]
    fn restored_count_ignores_non_definition_failed_form() {
        let source = "(defn f [] 1)\n";
        let failed = [failed_form("(+ 1 2)")];
        assert_eq!(restored_definition_count(source, &failed), Some(1));
    }

    // Empty / imports-only backing file suppresses (None), unchanged contract.
    #[test]
    fn restored_count_empty_and_imports_only_suppress() {
        assert_eq!(restored_definition_count("", &[]), None);
        assert_eq!(restored_definition_count("   \n", &[]), None);
        assert_eq!(
            restored_definition_count("(import [primitives [Int]])\n", &[]),
            None
        );
    }
}
