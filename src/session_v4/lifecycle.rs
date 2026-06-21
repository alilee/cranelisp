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
    CranelispError, DefKind, ErrorLocation, FQSymbol, ModuleEntry, ModuleFullPath, Sexp, Span,
    Symbol, Type, Warning,
};

use cranelisp_typecheck::CheckState;

use crate::code::{Code, SessionSymbolTable};
use crate::scheduler::CompileScheduler;

use super::{
    dedup_platform_names_preserving_order, nice_worker_loop, resolve_priority_worker_count,
    CompilerSession, ModuleIntroductionOutcome, SessionSettings, SharedState, SymbolCategory,
    SymbolInfo, TestRunnerState,
};

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
    pub fn new(
        settings: SessionSettings,
        project_root: PathBuf,
        entry_module_name: &str,
    ) -> Self {
        // Lib dirs: stdlib location(s), NOT including project_root.
        // Project root is tier 2 in §8.11.2, searched separately.
        let lib_dirs = crate::session_setup::assemble_lib_dirs(&project_root);

        // Platform dirs: extra search locations from env var (§8.11.5).
        let platform_dirs = crate::session_setup::assemble_platform_dirs();

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

        let (priority_worker_handles, nice_worker_handles) =
            Self::spawn_worker_threads(&shared, priority_workers, nice_workers);

        CompilerSession {
            shared,
            error_modules: HashSet::new(),
            watcher: None,
            worker_pool: crate::worker_pool::WorkerPool::new(
                priority_worker_handles, nice_worker_handles, nice_workers,
            ),
            // S78 §1: the REPL cursor + carry-forward CheckState start at the
            // ENTRY module (its real name), not a hardcoded "user".
            current_repl_module: entry_module.clone(),
            repl_check_state: Mutex::new(Some(CheckState::new(entry_module.clone()))),
            repl_input_active: std::sync::Arc::new(AtomicBool::new(false)),
            warnings: Vec::new(),
            entry_module,
        }
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
        let cache_state = cache_dir_opt.as_ref()
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
            typecheck_products: dashmap::DashMap::new(),
            // Sprint 58 Wave 3b: kept_jits / kept_linkers dissolved per
            // Decision 35; Arc retention now lives on each Code::Jit /
            // Code::Linker on `ModuleEntry::Def.code`.
            kept_dlls: Mutex::new(Vec::new()),
            // D1b: the introspection STORE is REPL-only — `Some(empty map)`
            // under `RunMode::Repl`, `None` in `--run`/`--link` (no allocation
            // in batch). Same `run_mode` carrier that gates population (D1 §4).
            introspection: run_mode.populates_introspection().then(dashmap::DashMap::new),
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
        self.shared.lib_dirs.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Convenience accessor: platform DLL search directories (snapshot clone).
    pub fn platform_dirs(&self) -> Vec<PathBuf> {
        self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Update the lib directory set. Sprint 57 Wave 4 G9: tests and the
    /// CLI call this after `new()` to override defaults; workers take a
    /// fresh clone for each file-resolution call, so the change is
    /// observed by subsequent typechecks.
    pub fn set_lib_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self.shared.lib_dirs.lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Update the platform search directory set. Same semantics as
    /// `set_lib_dirs`.
    pub fn set_platform_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Append a single platform search directory to the current set.
    /// Convenience wrapper around `set_platform_dirs` for tests/CLI.
    pub fn push_platform_dir(&mut self, dir: PathBuf) {
        let mut guard = self.shared.platform_dirs.lock()
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
        *self.shared.test_runner_state.current_module.lock()
            .unwrap_or_else(|e| e.into_inner()) = path.clone();
        // Create a new CheckState for the new module.
        *self.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(CheckState::new(path));
    }

    /// Get a read guard for the current module's symbol table.
    pub(crate) fn current_symbol_table(&self) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable> {
        let module = self.current_module_path();
        self.shared.symbol_tables.get(&module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in symbol_tables"))
    }

    /// Get a read guard for any module's symbol table.
    pub(crate) fn module_table(&self, path: &ModuleFullPath) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable>> {
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
            cranelisp_typecheck::advance_next_id_past_table(
                &self.shared.next_type_id, &decoded,
            );
            cranelisp_types::install_module(
                &self.shared.symbol_tables, path.clone(), decoded,
            );
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
        let _ = cranelisp_types::ensure_module_exists(
            &self.shared.symbol_tables, path,
        );
        Ok(ModuleIntroductionOutcome::Blank)
    }

    /// Backwards-compatible alias for the Blank branch only. Kept for callers
    /// that want create-if-absent semantics without inspecting the outcome.
    #[allow(dead_code)]
    pub fn introduce_module_blank(&self, path: &ModuleFullPath) {
        let _ = cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, path);
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
        Ok(Some(
            cached.metadata.symbol_table.into_concrete::<Code, ()>(),
        ))
    }

    /// Branch-3 probe: returns the source file path for `module` if one is
    /// known to the session (registered in `file_to_module`'s reverse map).
    pub(crate) fn find_module_source(&self, module: &ModuleFullPath) -> Option<std::path::PathBuf> {
        let guard = self.shared.file_to_module.lock()
            .unwrap_or_else(|e| e.into_inner());
        guard.iter()
            .find_map(|(file, mp)| if mp == module { Some(file.clone()) } else { None })
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
        let file_to_mod = self.shared.file_to_module
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
        self.shared.introspection.as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.source.clone())
    }

    /// REPL `/sexp` — parsed s-expression of a symbol's defining form, or
    /// `None`. Reads `shared.introspection[fq]`.
    pub fn symbol_sexp(&self, fq: &FQSymbol) -> Option<Sexp> {
        self.shared.introspection.as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.sexp.clone())
    }

    /// REPL `/clif` — CLIF IR text of a symbol's compiled body, or `None`.
    /// Populated only when `CRANELISP_CODEGEN_TRACE` or REPL-trace mode is
    /// active. Reads `shared.introspection[fq]`.
    pub fn symbol_clif(&self, fq: &FQSymbol) -> Option<String> {
        self.shared.introspection.as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.clif_ir.clone())
    }

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
                // Skip imports / reexports + special forms — those are surfaced
                // by `/imports` separately.
                let (category, scheme, docstring) = match entry {
                    ModuleEntry::Def { scheme, docstring, kind, .. } => {
                        let cat = match kind.as_ref() {
                            DefKind::Constructor { .. } => SymbolCategory::Constructor,
                            DefKind::Macro { .. } => SymbolCategory::Macro,
                            _ => SymbolCategory::Fn,
                        };
                        (cat, Some(scheme.clone()), docstring.clone())
                    }
                    ModuleEntry::TypeDef { .. } =>
                        (SymbolCategory::Type, None, None),
                    ModuleEntry::TraitDecl { docstring, .. } =>
                        (SymbolCategory::Trait, None, docstring.clone()),
                    // Special forms + imports are surfaced by `/imports`.
                    _ => continue,
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
        self.repl_input_active.store(active, std::sync::atomic::Ordering::Release);
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

    /// Mutable accessor for the warnings accumulator. Used by the eventual
    /// worker → session warning merge path; for now the public method
    /// surface is the load-bearing change.
    #[allow(dead_code)]
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
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for path in file_to_mod.keys() {
            watcher.watch_file(path);
        }
    }

    /// Poll the file watcher for changed source files and reload them.
    ///
    /// Returns a list of user-visible messages (one per reloaded module).
    /// On success, removes the module from `error_modules`. On failure,
    /// adds it to `error_modules` to block subsequent evals.
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
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let mut modules_to_reload: Vec<(ModuleFullPath, PathBuf)> = Vec::new();
        for path in &changed_paths {
            if let Some(module_path) = file_to_mod.get(path)
                && !modules_to_reload.iter().any(|(mp, _)| mp == module_path) {
                    modules_to_reload.push((module_path.clone(), path.clone()));
                }
        }
        // Cascade invalidation: find modules that import any changed module
        // and add them to the reload list. Sprint 58 Step 5a: read `imports`
        // off the per-module SymbolTable directly (was: parallel
        // `module_structures.import_specs`).
        let changed_modules: HashSet<ModuleFullPath> = modules_to_reload
            .iter()
            .map(|(mp, _)| mp.clone())
            .collect();
        for entry in self.shared.symbol_tables.iter() {
            let dependent_module = entry.key().clone();
            if changed_modules.contains(&dependent_module) {
                continue; // Already being reloaded directly.
            }
            let depends_on_changed = entry.value().imports.iter().any(|spec| {
                let import_mod = ModuleFullPath::from(spec.module_path.as_ref());
                changed_modules.contains(&import_mod)
            });
            if depends_on_changed {
                // Find the file path for this dependent module.
                if let Some(dep_path) = file_to_mod.iter()
                    .find(|(_, mp)| **mp == dependent_module)
                    .map(|(p, _)| p.clone())
                {
                    modules_to_reload.push((dependent_module, dep_path));
                }
            }
        }
        drop(file_to_mod);

        let mut messages = Vec::new();
        for (module_path, file_path) in modules_to_reload {
            // Extract just the filename for the notification message.
            let file_name = file_path.file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_else(|| module_path.as_ref());
            match self.reload_module(&module_path, &file_path) {
                Ok(()) => {
                    self.error_modules.remove(&module_path);
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
    pub fn regenerate_backing_file(&mut self) {
        let module = self.current_module_path();

        // Get the backing file path from typecheck product.
        let file_path = match self.shared.typecheck_products.get(&module) {
            Some(tp) => match &tp.file_path {
                Some(p) => p.clone(),
                None => {
                    // Entry module may not have a file path yet (fresh session).
                    // Default to {project_root}/{module}.cl.
                    self.shared.project_root.join(format!("{}.cl", module))
                }
            },
            None => self.shared.project_root.join(format!("{}.cl", module)),
        };

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
        let source = crate::save::generate_module_source(
            &st,
            self.shared.introspection.as_ref(),
            &module,
        );

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
            let canonical = file_path.canonicalize().unwrap_or_else(|_| file_path.clone());
            watcher.update_content_hash(canonical.clone(), hash);
        }

        // Register the file in file_to_module so the watcher can find it.
        if let Ok(canonical) = file_path.canonicalize() {
            self.shared.file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module.clone());
        }

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
    pub(crate) fn reload_module(
        &mut self,
        module_path: &ModuleFullPath,
        file_path: &Path,
    ) -> Result<(), CranelispError> {
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::RecompileModule,
            module_path.as_ref(),
        );
        let source = std::fs::read_to_string(file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read {}: {e}", file_path.display()),
                location: ErrorLocation::from_span_file(Span::new(0, 0), Some(file_path.to_path_buf())),
            }
        })?;

        // Remove stale products before recompilation.
        // Sprint 57 Wave 2 G6: `codegen_products` was deleted; compiled code
        // lives on `ModuleEntry::Def.code`. Walk the module's symbols and
        // clear each `code` field so stale pointers are not callable during
        // recompilation. The `Arc<Jit>` handles in `kept_jits` keep the old
        // mmap'd pages alive until the session ends (preserves the Phase-2
        // redefinition policy of "old code stays callable for in-flight
        // calls" — same behaviour as before, just via a different store).
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::ClearModuleState,
            module_path.as_ref(),
        );
        self.shared.typecheck_products.remove(module_path);
        if let Some(mut st) = self.shared.symbol_tables.get_mut(module_path) {
            for entry in st.symbols.values_mut() {
                if let ModuleEntry::Def { code, .. } = entry {
                    *code = None;
                }
            }
        }

        // Parse the new source; the sexps ride the re-register work packet
        // (S78 — no shared `module_sexps` map). Persistent workers parked on
        // the priority-work condvar wake and process it (G11 per §4.6).
        let sexps: std::sync::Arc<[Sexp]> =
            std::sync::Arc::from(cranelisp_frontend::parse(&source)?);

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
        self.shared.scheduler.wait_module_typecheck_settled(module_path);

        // `re_register_module` clears `inmem_done` and re-queues the module
        // for typecheck with the fresh sexps. `register_module` would be a
        // no-op because the module is already in `scheduler.modules`.
        let re_registered = self.shared.scheduler.re_register_module(module_path, sexps.clone());
        if !re_registered {
            // Module isn't known to the scheduler yet (first-time seed from
            // file watcher) — fall back to register_module.
            self.shared.scheduler.register_module(module_path.clone(), sexps, false);
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

        Ok(())
    }

    /// Register a module by name (pipeline-v4.md §3.1).
    ///
    /// Resolves source file, parses, enqueues for typechecking.
    /// TODO: currently runs inline worker loop. Will just enqueue
    /// once persistent workers are wired.
    pub fn register_module(
        &mut self,
        module_name: &str,
    ) -> Result<(), CranelispError> {
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
        _entry_module_path: &Path,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        let sexps: std::sync::Arc<[Sexp]> =
            std::sync::Arc::from(cranelisp_frontend::parse(source)?);

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
        self.shared.scheduler.register_module(module.clone(), sexps, false);

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
    pub fn trampoline(
        &mut self,
        module_name: &str,
    ) -> Result<(i64, Type), CranelispError> {
        // Enforce the batch-mode signature `(Fn [] (IO _))` before running
        // (spec §10.6 / §12.6). `--run` reaches `main` through this seam (NOT
        // `link_by_name`), so the same `validate_main` gate the `--link` path
        // applies must be applied here — otherwise a bare-`Int`/`Bool` main
        // would be leniently accepted under `--run`. The REPL never calls
        // `trampoline`, so it stays exempt (§10.6.2).
        let module_path = ModuleFullPath::from(module_name);
        if let Some(table) = self.module_table(&module_path) {
            crate::exe::validate_main(&table)?;
        }
        // (If the entry table is absent, the code-ptr lookup below produces the
        // "no `main`" diagnostic — no separate handling needed here.)

        // Look up main's compiled code on its symbol-table entry (G6).
        let main_sym = cranelisp_types::Symbol::from("main");
        let code_ptr = self.lookup_main_code_ptr(module_name, &main_sym)?;
        let result_type = self.lookup_main_return_type(module_name);

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
        let outcome = cranelisp_intrinsics::panic::cranelisp_run_program(
            code_ptr,
            result_type.is_io(),
        );

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
                let fault = cranelisp_intrinsics::panic::take_dispatch_fault()
                    .unwrap_or_else(|| cranelisp_intrinsics::panic::DispatchFault {
                        fn_name: "<unknown>".to_string(),
                        cause: "platform dispatch fault".to_string(),
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
            // result for a non-IO main). The host applies its own type-driven
            // exit-code reduction in `main.rs::run`.
            _ => {
                if result_type.is_io() {
                    let inner_type = result_type.unwrap_io().clone();
                    Ok((outcome.exit_code, inner_type))
                } else {
                    Ok((outcome.exit_code, result_type))
                }
            }
        }
    }

    /// Look up the code pointer for `main` on its `ModuleEntry::Def.code`
    /// (Sprint 57 Wave 2 G6 — replaces the deleted `codegen_products` lookup).
    pub(crate) fn lookup_main_code_ptr(
        &self,
        module_name: &str,
        main_sym: &cranelisp_types::Symbol,
    ) -> Result<*const u8, CranelispError> {
        let module_path = ModuleFullPath::from(module_name);

        // GOT is the single source of callable addresses (D41/D35); read
        // `main`'s pointer from its GOT slot rather than a `Code::ptr`.
        // The callable slot now rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        if let Some(table) = self.shared.symbol_tables.get(&module_path)
            && let Some(entry @ ModuleEntry::Def { code: Some(_), .. }) =
                table.get(main_sym.as_ref())
            && let Some(slot) = entry.callable_got_slot()
        {
            let ptr = table.got.load_slot(slot);
            if !ptr.is_null() {
                return Ok(ptr);
            }
        }

        Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)"
                .into(),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })
    }

    /// Look up the return type of `main` from the typechecker.
    pub(crate) fn lookup_main_return_type(&self, module_name: &str) -> Type {
        let module_path = ModuleFullPath::from(module_name);
        let main_sym = Symbol::from("main");

        if let Some(table) = self.module_table(&module_path)
            && let Some(cranelisp_types::ModuleEntry::Def { scheme, .. }) =
                table.get(main_sym.as_ref())
            && let Type::Fn(_, ret) = &scheme.ty
        {
            return *ret.clone();
        }
        Type::Int
    }

    /// Wait until all registered modules have object codegen complete.
    ///
    /// Block until all in-memory codegen (JIT) is complete.
    pub fn wait_inmem_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
        self.shared.scheduler.wait_inmem_complete()
    }

    /// Transfer orchestration ownership of the ENTRY module to the eval thread
    /// (S78 §3 / B1). Called by the REPL driver (`main.rs`) once startup
    /// typecheck has completed and the eval loop is about to take over.
    ///
    /// After this, the eval thread is the entry module's *sole* orchestrator:
    /// a dependency gap the eval thread hits during a REPL form is driven by
    /// the eval thread's own wait+retry (`register_dep_for_eval`), and the
    /// scheduler will NOT requeue the entry onto the pool for a concurrent
    /// re-typecheck of its own sexps. This closes the B1 dual-orchestration —
    /// keyed on the entry module's orchestration role (`eval_owned`), carried
    /// as data on its `ModuleState`, never on the name `"user"`.
    pub fn mark_entry_eval_owned(&self) {
        self.shared.scheduler.mark_eval_owned(&self.entry_module);
    }

    /// Promotes nice workers to normal priority before blocking, ensuring
    /// object codegen completes promptly (e.g., before linking). Wakes
    /// the `object_work_available` condvar so workers observe the promotion
    /// flag on their next loop iteration.
    pub fn wait_object_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
        // When no nice workers are running (e.g., tests with nice_workers: 0),
        // no .o files will be produced. Skip the wait to avoid blocking
        // forever. Sprint 67 Cluster B sub-fire 2a/2b: nice-worker count
        // read via the `WorkerPool` facade method.
        if self.worker_pool.nice_worker_count() == 0 {
            return Ok(());
        }

        // Promote nice workers so object codegen runs at full speed.
        self.shared.promote_nice_workers.store(
            true,
            std::sync::atomic::Ordering::Release,
        );
        // Wake workers so they observe the promotion flag.
        self.shared.scheduler.wake_object_workers();

        let result = self.shared.scheduler.wait_object_complete();

        // Flush the cache manifest to disk so the next session can detect
        // cache hits. Sprint 67 Cluster B sub-fire 3: ObjectCache facade.
        self.shared.cache.flush_manifest();

        result
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
        self.shared.scheduler.shutdown();
        // Sprint 67 Cluster B sub-fire 2a/2b: join routing migrated through
        // `WorkerPool::shutdown` (the facade method-surface landing). The
        // priority + nice handle drains live inside `WorkerPool`; this call
        // is the load-bearing entry point — S68 may reshape internals
        // freely without changing this call site.
        self.worker_pool.shutdown();
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
        let file_path = crate::pipeline::resolve_module_file(&module, &self.shared.project_root, &lib_dirs);
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
            self.shared.file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module);
        }

        self.register_module_with_source(module_name, &source, &entry_path)
    }

    /// §8: Link by module name. Collects .o files produced by nice workers,
    /// generates a startup stub, and invokes the system linker.
    ///
    /// Must be called after `wait_object_complete()` — all .o files must
    /// be ready.
    pub fn link_by_name(
        &mut self,
        module_name: &str,
    ) -> Result<(), CranelispError> {
        let module = ModuleFullPath::from(module_name);

        // Validate main exists and determine return kind (Int vs IO).
        let entry_table = self.module_table(&module).ok_or_else(|| {
            CranelispError::ModuleError {
                message: format!("entry module '{}' not found in typechecker", module_name),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
        })?;
        // Enforce the batch-mode signature `(Fn [] (IO _))` (spec §10.6 /
        // §12.6). A valid `main` always returns `IO _` after this gate — the
        // startup stub therefore always trampolines the IO result.
        crate::exe::validate_main(&entry_table)?;
        drop(entry_table);
        // FIXME 0406 (test-discovery.md §4.5): refuse a `--link` build that
        // references a dev-session-only `PrimitiveExtern` (`discover-tests`)
        // BEFORE invoking `cc` — a friendly compile-time diagnostic instead of
        // the raw `undefined reference to discover-tests` linker error. Scans
        // every linked module (not just the entry); the offending callee can
        // live in any module dragged into the link.
        crate::exe::reject_dev_session_externs_in_link(&self.shared.symbol_tables)?;
        let entry_table = self.module_table(&module).ok_or_else(|| {
            CranelispError::ModuleError {
                message: format!("entry module '{}' not found in typechecker", module_name),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
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
        let cache_dir = self.shared.cache.cache_dir().ok_or_else(|| {
            CranelispError::ModuleError {
                message: "cache directory not configured — cannot write startup .o".into(),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
        })?;
        let startup_o_path = cache_dir.join("__startup.o");
        std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write startup .o: {e}"),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(startup_o_path.clone())),
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
        std::fs::write(&alias_o_path, &alias_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write main alias .o: {e}"),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(alias_o_path.clone())),
            }
        })?;

        // Find the runtime bundle library.
        let bundle_lib = crate::exe::find_bundle_lib()?;

        // Output path: entry module stem in CWD (not project root).
        // E.g., `cranelisp --link examples/hello.cl` produces `./hello`.
        let output_path = PathBuf::from(module_name.replace(".cl", ""));

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
        let manifest_names =
            crate::exe::collect_platform_manifest_names(&platform_names);

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
                let module_path =
                    ModuleFullPath::from(format!("platform.{}", name));
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
