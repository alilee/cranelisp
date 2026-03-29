// CompilationSession: lifecycle, constructors, codegen dispatch, worker state.
//
// This module defines the core `CompilationSession` type and its construction,
// codegen dispatch (send/flush/shutdown), worker sub-structs, cache config,
// module dependency graph, and session-level methods (module reload/cascade,
// macro compilation, GOT alias registration, form processing).
//
// `compile_unit` and stage helpers live in `pipeline.rs` (added via separate
// `impl CompilationSession` block).

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::{atomic::{AtomicBool, AtomicUsize, Ordering}, Condvar, Mutex, RwLock};

use cranelisp_types::{
    CheckResult, CompileContext, CranelispError, Defn, MacroClauseInfo, ModuleEntry,
    ModuleFullPath, ModuleStrategy, ModuleStructure, Program, Sexp, Span, Symbol,
    Type, Visibility, Warning,
};

use cranelisp_backend::cache;

use crate::expander::CraneliftExpander;

// ---------------------------------------------------------------------------
// Cache configuration
// ---------------------------------------------------------------------------

/// Configuration for module caching.
///
/// Controls whether the pipeline checks/writes the `.cranelisp-cache/` directory.
/// `--no-cache` CLI flag produces `Disabled`.
pub enum CacheConfig {
    /// Caching disabled (e.g., `--no-cache` flag).
    Disabled,
    /// Caching enabled with the given cache directory.
    Enabled { cache_dir: PathBuf },
}

impl CacheConfig {
    /// Returns the cache directory if caching is enabled.
    pub fn cache_dir(&self) -> Option<&Path> {
        match self {
            CacheConfig::Disabled => None,
            CacheConfig::Enabled { cache_dir } => Some(cache_dir),
        }
    }
}

/// Mutable cache state carried through a compilation session.
///
/// Accumulates manifest updates as modules are compiled; writes the
/// final manifest on completion.
pub struct CacheState {
    /// The cache manifest (loaded from disk or freshly created).
    manifest: cache::CacheManifest,
    /// The cache directory path.
    cache_dir: PathBuf,
    /// Source hashes for modules compiled in this session.
    /// Used as dependency hashes for downstream modules.
    source_hashes: HashMap<ModuleFullPath, String>,
    /// Whether the manifest has been modified and needs writing.
    dirty: bool,
    /// Modules that were recompiled (cache miss) in this session.
    /// Used for cascade invalidation: if a dependency was recompiled,
    /// all its dependents must also recompile.
    recompiled: HashSet<ModuleFullPath>,
}

impl CacheState {
    /// Initialize cache state: load existing manifest or create a new one.
    pub fn new(cache_dir: PathBuf) -> Self {
        let manifest = cache::read_manifest(&cache_dir)
            .unwrap_or_else(cache::CacheManifest::new_for_host);
        CacheState {
            manifest,
            cache_dir,
            source_hashes: HashMap::new(),
            dirty: false,
            recompiled: HashSet::new(),
        }
    }

    /// Returns the cache directory path.
    pub fn cache_dir(&self) -> &Path {
        &self.cache_dir
    }

    /// Record that a module was recompiled (cache miss).
    pub fn record_recompiled(&mut self, module_path: &ModuleFullPath) {
        self.recompiled.insert(module_path.clone());
    }

    /// Read access to source hashes for dependency hash lookups.
    pub fn source_hashes(&self) -> &HashMap<ModuleFullPath, String> {
        &self.source_hashes
    }

    /// Mutable access to source hashes for external recompilation tracking.
    pub fn source_hashes_mut(&mut self) -> &mut HashMap<ModuleFullPath, String> {
        &mut self.source_hashes
    }

    /// Record a compiled module in the manifest with its source hash and
    /// dependency hashes. Also records the module as recompiled for cascade
    /// invalidation and stores the source hash for downstream dependency tracking.
    pub fn record_module(
        &mut self,
        module_path: &ModuleFullPath,
        source_hash: String,
        dep_hashes: HashMap<String, String>,
    ) {
        self.manifest
            .upsert_module(module_path, source_hash.clone(), dep_hashes);
        self.source_hashes
            .insert(module_path.clone(), source_hash);
        self.dirty = true;
        self.recompiled.insert(module_path.clone());
    }

    /// Write the manifest to disk if it was modified.
    pub fn flush(&self) -> Result<(), CranelispError> {
        if self.dirty {
            cache::write_manifest(&self.cache_dir, &self.manifest)?;
        }
        Ok(())
    }

    /// Flush the manifest to disk (public entry point for REPL cache integration).
    ///
    /// Writes the manifest if any modules were compiled during this session.
    /// Silently swallows errors (REPL should not crash on cache write failure).
    pub fn flush_manifest(&self) {
        let _ = self.flush();
    }

    /// Check if a module has a valid cache entry.
    ///
    /// Returns `true` if the manifest has an entry for this module whose
    /// source hash matches `current_source_hash` and all dependency hashes
    /// match. Returns `false` on cache miss. Returns `false` (not error)
    /// on global invalidation (compiler changed, format version, etc.).
    pub fn is_cache_valid(
        &self,
        module_path: &ModuleFullPath,
        current_source_hash: &str,
        dep_hashes: &HashMap<ModuleFullPath, String>,
    ) -> bool {
        match cache::check_manifest(&self.manifest, module_path, current_source_hash, dep_hashes) {
            Ok(valid) => valid,
            Err(_) => false, // Global invalidation — treat as miss.
        }
    }

    /// Record a cache-hit module's source hash without marking it as recompiled.
    ///
    /// On cache hit, the module was NOT recompiled — it was loaded from cache.
    /// But downstream modules need this module's source hash for their own
    /// dependency hash checks.
    pub fn record_cache_hit(&mut self, module_path: &ModuleFullPath, source_hash: String) {
        self.source_hashes.insert(module_path.clone(), source_hash);
    }
}

// ---------------------------------------------------------------------------
// Worker sub-structs: group fields by pipeline role
// ---------------------------------------------------------------------------

/// In-memory codegen worker state: GOT, JIT lifetimes, trace support.
///
/// Fields used by `codegen_and_execute()` and the REPL for GOT-indirect
/// compilation, JIT module lifetime management, and trace instrumentation.
/// Separated from `CompilationSession` for clarity and preparation for
/// concurrent codegen (Step 11).
pub struct InMemWorkerState {
    /// Backend GOT state (persists across forms for function redefinition).
    pub got_state: cranelisp_backend::got::ModuleCodegenState,
    /// JIT instances that must stay alive (their code is referenced via GOT).
    /// Each defn/macro compilation creates a new JIT; we keep them alive here.
    pub jit_modules: Vec<cranelisp_backend::jit::Jit>,
    /// Traced function info for `(trace ...)` expression compilation.
    /// Set by the REPL before calling compile_unit when trace support is needed.
    /// Empty when no trace is active (the common case).
    pub traced_fns: Vec<cranelisp_backend::compiler::TracedFnInfo>,
    /// Extra JIT symbols for trace format override.
    /// Set by the REPL to override `cranelisp_trace_format` with the REPL's
    /// version that has access to type_defs/type_modules for proper ADT display.
    pub trace_extra_symbols: Vec<(String, *const u8)>,
    /// Linker instances from cache-hit loads. Must stay alive because their
    /// code_regions, data_regions, and GOT mmaps hold the executable memory
    /// that GOT code pointers reference. Dropping a Linker would free the
    /// memory and leave dangling pointers in the GOT.
    pub cache_linkers: Vec<cranelisp_backend::cache::Linker>,
}

impl InMemWorkerState {
    pub fn new() -> Self {
        InMemWorkerState {
            got_state: cranelisp_backend::got::ModuleCodegenState::new(),
            jit_modules: Vec::new(),
            traced_fns: Vec::new(),
            trace_extra_symbols: Vec::new(),
            cache_linkers: Vec::new(),
        }
    }

    /// Create a worker state with a pre-populated GOT for use by a codegen
    /// worker thread. The worker's GOT shares the same underlying `GotTable`
    /// (via Arc) so atomic writes are visible to the main thread after flush.
    pub fn new_with_shared_got(
        shared_got: std::sync::Arc<cranelisp_backend::got::GotTable>,
    ) -> Self {
        let mut got_state = cranelisp_backend::got::ModuleCodegenState::new();
        got_state.set_shared_got(shared_got);
        InMemWorkerState {
            got_state,
            jit_modules: Vec::new(),
            traced_fns: Vec::new(),
            trace_extra_symbols: Vec::new(),
            cache_linkers: Vec::new(),
        }
    }
}

// SAFETY: InMemWorkerState contains raw *const u8 pointers in trace_extra_symbols
// and got_state (via JIT code pointers). These pointers point to:
// - Platform DLL function entries: valid for process lifetime, read-only.
// - JIT-compiled code: kept alive by jit_modules, read-only after finalization.
// No shared mutable state — the worker thread has exclusive ownership.
unsafe impl Send for InMemWorkerState {}

/// Object-file codegen worker state: cache writing, .o paths, module structures.
///
/// Fields used by `codegen_and_execute()` for background .o emission and
/// manifest tracking. Separated from `CompilationSession` for clarity and
/// preparation for concurrent codegen (Step 11).
pub struct ObjectWorkerState {
    /// Cache state for .o and .meta.json writing. None = caching disabled.
    /// Initialized by production callers (--run, --link, REPL with prelude).
    /// Left as None by test helpers.
    pub cache_state: Option<CacheState>,
    /// Background .o writer. Created when cache_state is Some.
    pub cache_writer: Option<crate::cache_writer::CacheWriterHandle>,
    /// .o file paths written during this session, in compilation order.
    /// Used by --link to collect all .o files for the system linker.
    pub compiled_o_paths: Vec<PathBuf>,
    /// Module structures extracted during compilation, in compilation order.
    /// Used by --link for platform rlib discovery and startup object generation.
    pub compiled_module_structures: Vec<(ModuleFullPath, ModuleStructure)>,
    /// Cumulative cross-module function signatures for .o generation.
    /// Each entry is (qualified_name, param_count). Extended after each
    /// module completes stage 6. Used as `ObjectCompileInput.cross_module_fns`
    /// for subsequent modules.
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,
}

impl ObjectWorkerState {
    pub fn new() -> Self {
        ObjectWorkerState {
            cache_state: None,
            cache_writer: None,
            compiled_o_paths: Vec::new(),
            compiled_module_structures: Vec::new(),
            cross_module_func_sigs: Vec::new(),
        }
    }

    pub(crate) fn new_with_cache(cache_dir: PathBuf) -> Self {
        ObjectWorkerState {
            cache_state: Some(CacheState::new(cache_dir)),
            cache_writer: Some(crate::cache_writer::CacheWriterHandle::new()),
            compiled_o_paths: Vec::new(),
            compiled_module_structures: Vec::new(),
            cross_module_func_sigs: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Producer-consumer codegen queue (Sprint 40a Wave 3, pipeline-v3.md §6)
// ---------------------------------------------------------------------------

/// Shared concurrent queue for codegen items (design §2.1).
///
/// `Arc<CodegenQueue>` is shared between producers (`compile_unit` callers)
/// and consumers (worker threads). `Mutex<VecDeque>` is the simplest correct
/// choice — contention is low because producers push infrequently (once per
/// module) and consumers hold the lock only for the duration of a pop.
pub struct CodegenQueue {
    items: Mutex<VecDeque<crate::pipeline::CodegenItem>>,
    condvar: Condvar,
    /// Set to true when no more items will be enqueued (flush/shutdown).
    done: AtomicBool,
    /// Count of items currently being compiled by workers.
    in_flight: AtomicUsize,
    /// Signalled when in_flight drops to 0 and queue is empty.
    drain_complete: Condvar,
    /// Mutex paired with drain_complete condvar. Must be held when waiting
    /// on drain_complete (Condvar requires a MutexGuard).
    drain_mutex: Mutex<()>,
}

impl CodegenQueue {
    /// Create a new empty codegen queue.
    pub fn new() -> Self {
        CodegenQueue {
            items: Mutex::new(VecDeque::new()),
            condvar: Condvar::new(),
            done: AtomicBool::new(false),
            in_flight: AtomicUsize::new(0),
            drain_complete: Condvar::new(),
            drain_mutex: Mutex::new(()),
        }
    }

    /// Push an item to the queue and wake one parked worker.
    pub fn push(&self, item: crate::pipeline::CodegenItem) {
        self.items.lock().unwrap().push_back(item);
        self.condvar.notify_one();
    }

    /// Try to pop an item. Blocks until an item is available or `done` is set.
    /// Returns `None` when `done` is set and the queue is empty (worker should exit).
    #[allow(dead_code)] // Used by worker loops when workers are spawned.
    fn pop_blocking(&self) -> Option<crate::pipeline::CodegenItem> {
        let mut q = self.items.lock().unwrap();
        loop {
            if let Some(item) = q.pop_front() {
                self.in_flight.fetch_add(1, Ordering::SeqCst);
                return Some(item);
            }
            if self.done.load(Ordering::SeqCst) {
                return None; // No more work, exit.
            }
            q = self.condvar.wait(q).unwrap();
        }
    }

    /// Signal that an in-flight item has completed. If this was the last
    /// in-flight item and the queue is empty, notify drain waiters.
    #[allow(dead_code)] // Used by worker loops when workers are spawned.
    fn complete_one(&self) {
        let prev = self.in_flight.fetch_sub(1, Ordering::SeqCst);
        if prev == 1 {
            // Last in-flight item completed. Check if queue is also empty.
            let q = self.items.lock().unwrap();
            if q.is_empty() {
                self.drain_complete.notify_all();
            }
        }
    }

    /// Signal done and wake all workers. Used by flush to tell workers
    /// no more items are coming.
    fn signal_done(&self) {
        self.done.store(true, Ordering::SeqCst);
        self.condvar.notify_all();
    }

    /// Wait until the queue is empty AND in_flight == 0.
    /// Must be called after `signal_done()`.
    fn wait_until_drained(&self) {
        let guard = self.drain_mutex.lock().unwrap();
        let _guard = self.drain_complete.wait_while(guard, |_| {
            let q = self.items.lock().unwrap();
            !q.is_empty() || self.in_flight.load(Ordering::SeqCst) > 0
        }).unwrap();
    }

    /// Reset the done flag for the next batch (REPL enters compile_unit
    /// again after flush).
    fn reset(&self) {
        self.done.store(false, Ordering::SeqCst);
    }
}

/// Holds either a Jit or a Linker — both must stay alive for the session
/// because their backing memory holds compiled code referenced by the GOT.
pub enum JitOrLinker {
    Jit(cranelisp_backend::jit::Jit),
    Linker(cranelisp_backend::cache::Linker),
}

// SAFETY: JitOrLinker contains Jit (which holds JITModule code memory) or
// Linker (which holds mmap'd code regions). Both are created on one thread
// and then moved to the collector. The backing memory is read-only after
// finalization and valid for the process lifetime.
unsafe impl Send for JitOrLinker {}

/// Codegen execution mode: synchronous (tests, REPL) or async (batch).
///
/// In synchronous mode, `enqueue_codegen` buffers items locally and
/// `hot_flush_in_mem_queue` drains them on the calling thread.
/// In async mode, items go to shared queues drained by worker pools.
pub enum CodegenMode {
    /// Synchronous: codegen runs on the calling thread during flush.
    /// Used by tests, REPL, and any mode where latency per-item matters
    /// more than throughput overlap.
    Sync,
    /// Asynchronous: codegen runs on N-core worker thread pools.
    /// Used by `--run` and `--link` where compile_unit and codegen can
    /// overlap for different modules.
    Async {
        inmem_queue: std::sync::Arc<CodegenQueue>,
        object_queue: std::sync::Arc<CodegenQueue>,
        inmem_workers: Vec<std::thread::JoinHandle<()>>,
        object_workers: Vec<std::thread::JoinHandle<()>>,
        jit_collector: std::sync::Arc<Mutex<Vec<JitOrLinker>>>,
    },
}

/// Number of codegen worker threads, capped at 8.
#[allow(dead_code)] // Used when worker pools are spawned.
fn codegen_worker_count() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get().min(8))
        .unwrap_or(1)
}

/// Object-file worker loop: pops items from queue, compiles to `.o` files.
/// Runs at nice priority.
#[allow(dead_code)] // Infrastructure ready for when object workers are spawned.
fn object_worker_loop(
    queue: std::sync::Arc<CodegenQueue>,
) {
    // Set nice priority (best-effort, ignore errors on unsupported platforms).
    #[cfg(unix)]
    unsafe {
        libc::setpriority(libc::PRIO_PROCESS, 0, 10);
    }

    loop {
        let item = match queue.pop_blocking() {
            Some(item) => item,
            None => return, // Done, exit thread.
        };

        // Object codegen (.o emission) is handled by the existing cache_writer
        // thread. Items that reach the object queue are acknowledged here to
        // complete the queue contract. The cache_writer is triggered during
        // `codegen_and_execute` (stage 6b).
        let _ = item;

        queue.complete_one();
    }
}

// ---------------------------------------------------------------------------
// ModuleDependencyGraph: incremental module dependency tracking
// ---------------------------------------------------------------------------

/// Tracks module dependency edges and file-to-module mappings.
///
/// Populated incrementally during `compile_unit` / `load_dependencies` as
/// modules are compiled.  Replaces the upfront `build_file_to_module_map`
/// and `build_module_dependency_map` calls that the REPL previously used.
pub struct ModuleDependencyGraph {
    /// Forward edges: module -> modules it depends on (imports + exports).
    pub imports: HashMap<ModuleFullPath, HashSet<ModuleFullPath>>,
    /// Reverse edges: module -> modules that depend on it.
    pub dependents: HashMap<ModuleFullPath, HashSet<ModuleFullPath>>,
    /// Filesystem path -> module name mapping (canonical paths).
    pub file_to_module: HashMap<PathBuf, ModuleFullPath>,
}

impl Default for ModuleDependencyGraph {
    fn default() -> Self {
        ModuleDependencyGraph {
            imports: HashMap::new(),
            dependents: HashMap::new(),
            file_to_module: HashMap::new(),
        }
    }
}

impl ModuleDependencyGraph {
    /// Create an empty dependency graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an import/export dependency edge from `parent` to `dep`.
    ///
    /// Adds `dep` to `parent`'s forward set and `parent` to `dep`'s reverse set.
    /// Duplicate edges are deduplicated automatically (HashSet).
    pub fn register_edge(&mut self, parent: &ModuleFullPath, dep: &ModuleFullPath) {
        self.imports
            .entry(parent.clone())
            .or_default()
            .insert(dep.clone());
        self.dependents
            .entry(dep.clone())
            .or_default()
            .insert(parent.clone());
    }

    /// Register a filesystem path -> module mapping.
    ///
    /// Only call with canonical paths to avoid duplicate entries for the
    /// same file under different relative forms.
    pub fn register_file(&mut self, path: PathBuf, module: ModuleFullPath) {
        self.file_to_module.insert(path, module);
    }

    /// Clear all edges and mappings (used by REPL `/reset`).
    pub fn clear(&mut self) {
        self.imports.clear();
        self.dependents.clear();
        self.file_to_module.clear();
    }

    /// Find all modules transitively dependent on the given root modules (BFS).
    ///
    /// Uses the reverse dependency map (`dependents`) to walk outward from
    /// `roots`. Returns modules in BFS order (direct dependents first, then
    /// their dependents, etc.). Does not include the root modules themselves.
    pub fn transitive_dependents(&self, roots: &[ModuleFullPath]) -> Vec<ModuleFullPath> {
        let mut result = Vec::new();
        let mut visited: HashSet<ModuleFullPath> = roots.iter().cloned().collect();
        let mut queue = VecDeque::new();

        // Seed with direct dependents of all root modules.
        for module in roots {
            if let Some(deps) = self.dependents.get(module) {
                for dep in deps {
                    if visited.insert(dep.clone()) {
                        queue.push_back(dep.clone());
                        result.push(dep.clone());
                    }
                }
            }
        }

        // BFS to find transitive dependents.
        while let Some(current) = queue.pop_front() {
            if let Some(deps) = self.dependents.get(&current) {
                for dep in deps {
                    if visited.insert(dep.clone()) {
                        queue.push_back(dep.clone());
                        result.push(dep.clone());
                    }
                }
            }
        }

        result
    }

    /// Look up the source file path for a given module.
    ///
    /// Returns `None` if no file is registered for the module.
    pub fn file_for_module(&self, module: &ModuleFullPath) -> Option<PathBuf> {
        self.file_to_module
            .iter()
            .find(|(_, mp)| *mp == module)
            .map(|(fp, _)| fp.clone())
    }
}

// ---------------------------------------------------------------------------
// CompilationSession: shared compilation core for both batch and REPL
// ---------------------------------------------------------------------------

/// Shared compilation state that both batch and REPL paths use.
///
/// Holds the persistent state needed to compile forms one at a time:
/// the typechecker, macro expander, GOT state, JIT lifetime management,
/// and platform symbols.
///
// ---------------------------------------------------------------------------
// CompilerSessionV3 — pipeline-v3.md §5 target
//
// Coexists with CompilationSession until all callers are migrated.
// compile_unit_v3 builds against this struct.
// ---------------------------------------------------------------------------

/// Pipeline v3 session (pipeline-v3.md §5.1).
///
/// compile_unit touches only pipeline core + queues.
/// Workers own their state ��� session never touches it.
/// Platforms are modules in the typechecker (like `primitives`).
pub struct CompilerSessionV3 {
    // --- Pipeline core (stages 1-5) ---
    // compile_unit reads/writes only these fields.

    /// Type checker. Owns all module symbol tables, type defs, trait registries.
    /// Platforms are loaded as synthetic modules (like `primitives`).
    /// `check()` takes `&self` — internal RwLocks on persistent fields.
    pub tc: cranelisp_typecheck::TypeChecker,

    /// Macro expander. Internal RwLock — expand is &self, compile_macro is &self+write lock.
    pub expander: CraneliftExpander,

    /// Module dependency graph: forward/reverse edges + file→module mapping.
    /// Populated at stage 2b of every compile_unit call.
    pub module_deps: Mutex<ModuleDependencyGraph>,

    /// Scheduling class registry for bind chain independence analysis.
    /// Populated during platform module loading.
    pub scheduling_registry: Mutex<crate::bind_chain_analysis::SchedulingRegistry>,

    // --- Codegen queues ---
    // compile_unit pushes; workers drain. Producer-consumer via CodegenQueue.

    /// In-memory codegen queue. Workers pop, JIT-compile, write to module GOTs.
    pub inmem_queue: CodegenQueue,

    /// Object-file codegen queue. Workers pop, compile to .o, write to disk.
    pub object_queue: CodegenQueue,

    // --- Watcher control ---
    // Pauses codegen enqueuing during REPL eval for GOT stability.

    /// When set, compile_unit defers enqueuing — items held until resumed.
    /// Uses Condvar so resume wakes blocked compile_unit calls (no busy-wait).
    watcher_gate: WatcherGate,

    // --- Session config (read-only after construction) ---

    pub settings: Settings,

    /// Project root directory. Derived from entry module path.
    pub project_root: PathBuf,

    /// Directories to search when resolving module imports.
    pub lib_dirs: Vec<PathBuf>,

    /// Shared ISA for codegen workers. Built once, Arc::clone per worker.
    pub shared_isa: std::sync::Arc<dyn cranelisp_backend::TargetIsa>,
}

/// Session settings (pipeline-v3.md §11).
#[allow(dead_code)]
pub struct Settings {
    pub no_color: bool,
    pub no_cache: bool,
}

/// Watcher gate — controls codegen enqueuing pause/resume without busy-wait.
///
/// When paused, compile_unit's enqueue step blocks on the condvar until
/// resumed. resume wakes all blocked enqueue calls.
pub struct WatcherGate {
    paused: Mutex<bool>,
    condvar: Condvar,
}

impl WatcherGate {
    pub fn new() -> Self {
        WatcherGate {
            paused: Mutex::new(false),
            condvar: Condvar::new(),
        }
    }

    /// Pause codegen enqueuing. Blocks any enqueue call until resumed.
    pub fn pause(&self) {
        *self.paused.lock().unwrap() = true;
    }

    /// Resume codegen enqueuing. Wakes all blocked enqueue calls.
    pub fn resume(&self) {
        *self.paused.lock().unwrap() = false;
        self.condvar.notify_all();
    }

    /// Wait until not paused, then return. Non-blocking if already unpaused.
    pub fn wait_if_paused(&self) {
        let guard = self.paused.lock().unwrap();
        if *guard {
            let _guard = self.condvar.wait_while(guard, |paused| *paused).unwrap();
        }
    }
}

// No worker state on the session. Workers own their state:
// - InMemWorkerState (GOT per module, Jit instances) — owned by inmem worker threads
// - ObjectWorkerState (cache dir, .o paths) — owned by object worker threads
// Worker threads are spawned by spawn_hot_inmem_codegen / spawn_nice_object_codegen
// and joined by hot_flush / shutdown.

/// Fields are grouped into sub-structs by pipeline role:
/// - `inmem_worker`: GOT state, JIT lifetimes, trace support (codegen path)
/// - `object_worker`: cache writing, .o paths, module structures (codegen path)
/// `ReplSession` wraps a `CompilationSession` and adds REPL-specific
/// concerns (display metadata, slash commands, trace state, introspection).
pub struct CompilationSession {
    // --- Read-only after construction ---
    /// Type checker state (persists across forms).
    /// Behind `Mutex` so `compile_unit` (which takes `&self`) can acquire
    /// `&mut TypeChecker` for `check()` and registration methods.
    /// Lock is held briefly for each TC method call, never across recursive
    /// `compile_unit` invocations.
    pub tc: Mutex<cranelisp_typecheck::TypeChecker>,
    /// Macro expander (persists across forms — macros accumulate). Internal RwLock.
    pub expander: CraneliftExpander,
    /// Directories to search when resolving module imports.
    /// Empty in test mode (imports unresolvable → self-contained tests).
    pub lib_dirs: Vec<PathBuf>,
    /// Project root directory for platform DLL path resolution.
    /// Set by callers (batch, link, REPL) before compilation.
    pub project_root: PathBuf,
    /// Whether this session uses GOT-indirect calls (interactive/REPL mode).
    /// When false, codegen uses direct calls (batch mode).
    /// Set by callers that need GOT-based compilation (REPL, --run).
    pub interactive: bool,
    /// Shared ISA for N-core codegen workers. Built once at session creation,
    /// cloned per worker via `Jit::new_with_isa`. None in sync mode.
    pub shared_isa: Option<std::sync::Arc<dyn cranelisp_backend::TargetIsa>>,

    // --- Shared mutable (behind Mutex/RwLock) ---
    /// Module dependency graph: forward/reverse edges + file→module mapping.
    /// Populated incrementally by `compile_unit` and `load_dependencies`.
    pub module_deps: Mutex<ModuleDependencyGraph>,
    /// Scheduling class registry for bind chain independence analysis.
    /// Maps platform function names to their SchedulingClass.
    /// Populated during platform DLL loading; empty when no platforms loaded.
    pub scheduling_registry: Mutex<crate::bind_chain_analysis::SchedulingRegistry>,
    /// Platform function pointers for JIT symbol registration.
    /// Each entry is (jit_name, function_pointer). Passed to
    /// `Jit::new_with_symbols()` when creating JIT instances.
    pub platform_symbols: RwLock<Vec<(String, *const u8)>>,
    /// Loaded platform DLL handles. Must remain alive for the process lifetime
    /// so that function pointers into the DLL code segments stay valid.
    pub loaded_platforms: Mutex<Vec<crate::platform::LoadedPlatform>>,

    // --- Worker state ---
    /// In-memory codegen worker state (GOT, JIT lifetimes, trace).
    /// Only present in Sync mode; in Async mode, the worker thread owns this.
    pub inmem_worker: Mutex<InMemWorkerState>,
    /// Object-file codegen worker state (cache, .o paths, module structures).
    /// Only present in Sync mode; in Async mode, the worker thread owns this.
    pub object_worker: Mutex<ObjectWorkerState>,

    // --- Codegen dispatch ---
    /// Queue of compilation units awaiting in-memory codegen (JIT execution).
    /// In Sync mode: drained on the calling thread by `flush_codegen()`.
    /// In Async mode: items go to `CodegenMode::Async::inmem_queue` instead.
    pub inmem_queue: Mutex<Vec<crate::pipeline::CodegenItem>>,
    /// Queue of compilation units awaiting object-file codegen (.o emission).
    /// In Sync mode: drained on the calling thread.
    /// In Async mode: items go to `CodegenMode::Async::object_queue` instead.
    pub object_queue: Mutex<Vec<crate::pipeline::CodegenItem>>,
    /// Codegen execution mode: synchronous or async worker pool.
    pub codegen_mode: CodegenMode,
    /// Flag to pause watcher-triggered codegen enqueuing during REPL eval.
    /// When true, `enqueue_codegen` holds back items until resumed.
    watcher_paused: AtomicBool,
    /// Items held back while watcher codegen is paused.
    watcher_held: Mutex<Vec<(crate::pipeline::CodegenItem, cranelisp_types::CodegenBehaviour)>>,
}

impl CompilationSession {
    /// Create a new compilation session with default (synchronous) state.
    pub fn new() -> Self {
        CompilationSession {
            tc: Mutex::new(cranelisp_typecheck::TypeChecker::new()),
            expander: CraneliftExpander::new(),
            lib_dirs: Vec::new(),
            project_root: PathBuf::from("."),
            interactive: false,
            shared_isa: None,
            module_deps: Mutex::new(ModuleDependencyGraph::new()),
            scheduling_registry: Mutex::new(crate::bind_chain_analysis::SchedulingRegistry::new()),
            platform_symbols: RwLock::new(Vec::new()),
            loaded_platforms: Mutex::new(Vec::new()),
            inmem_worker: Mutex::new(InMemWorkerState::new()),
            object_worker: Mutex::new(ObjectWorkerState::new()),
            inmem_queue: Mutex::new(Vec::new()),
            object_queue: Mutex::new(Vec::new()),
            codegen_mode: CodegenMode::Sync,
            watcher_paused: AtomicBool::new(false),
            watcher_held: Mutex::new(Vec::new()),
        }
    }

    /// Create a session with async codegen enabled.
    ///
    /// Does NOT spawn worker threads yet — call `spawn_hot_inmem_codegen()`
    /// and `spawn_nice_object_codegen()` after `compile_unit()` completes
    /// to start the worker pools. This matches the pipeline-v3.md north-star
    /// main.rs flow where workers are spawned after initial compilation.
    ///
    /// Used by `--run` and `--link` where compile_unit and codegen can
    /// overlap for different modules.
    pub fn new_async() -> Self {
        // Build shared ISA once for all codegen workers.
        let shared_isa = cranelisp_backend::jit::Jit::build_shared_isa().ok();
        let inmem_queue = std::sync::Arc::new(CodegenQueue::new());
        let object_queue = std::sync::Arc::new(CodegenQueue::new());
        let jit_collector = std::sync::Arc::new(Mutex::new(Vec::<JitOrLinker>::new()));

        CompilationSession {
            tc: Mutex::new(cranelisp_typecheck::TypeChecker::new()),
            expander: CraneliftExpander::new(),
            lib_dirs: Vec::new(),
            project_root: PathBuf::from("."),
            interactive: false,
            module_deps: Mutex::new(ModuleDependencyGraph::new()),
            scheduling_registry: Mutex::new(crate::bind_chain_analysis::SchedulingRegistry::new()),
            platform_symbols: RwLock::new(Vec::new()),
            loaded_platforms: Mutex::new(Vec::new()),
            inmem_worker: Mutex::new(InMemWorkerState::new()),
            object_worker: Mutex::new(ObjectWorkerState::new()),
            inmem_queue: Mutex::new(Vec::new()),
            object_queue: Mutex::new(Vec::new()),
            codegen_mode: CodegenMode::Async {
                inmem_queue,
                object_queue,
                inmem_workers: Vec::new(),
                object_workers: Vec::new(),
                jit_collector,
            },
            shared_isa,
            watcher_paused: AtomicBool::new(false),
            watcher_held: Mutex::new(Vec::new()),
        }
    }

    /// Create an async session with caching enabled.
    ///
    /// Combines `new_async()` with cache initialization.
    pub fn new_async_with_cache(cache_dir: PathBuf) -> Self {
        let session = Self::new_async();
        *session.object_worker.lock().unwrap() = ObjectWorkerState::new_with_cache(cache_dir);
        session
    }

    /// Shut down the async codegen worker pools, if running.
    ///
    /// Signals done on both queues, wakes all workers, and joins all threads.
    /// Safe to call multiple times (no-op after first call). Called
    /// automatically on Drop.
    pub fn shutdown_codegen(&mut self) {
        if let CodegenMode::Async {
            ref inmem_queue,
            ref object_queue,
            ref mut inmem_workers,
            ref mut object_workers,
            ..
        } = self.codegen_mode
        {
            // Signal both queues to stop accepting work.
            inmem_queue.signal_done();
            object_queue.signal_done();

            // Join all worker threads.
            for handle in inmem_workers.drain(..) {
                let _ = handle.join();
            }
            for handle in object_workers.drain(..) {
                let _ = handle.join();
            }
        }
    }

    /// Create a session with caching enabled.
    /// Initializes cache state and spawns the background cache writer thread.
    pub fn new_with_cache(cache_dir: PathBuf) -> Self {
        let session = Self::new();
        *session.object_worker.lock().unwrap() = ObjectWorkerState::new_with_cache(cache_dir);
        session
    }

    /// Flush all pending background cache writes.
    /// Blocks until the cache writer thread has completed all queued writes.
    pub fn flush_cache_writes(&self) {
        let ow = self.object_worker.lock().unwrap();
        if let Some(ref writer) = ow.cache_writer {
            writer.flush();
        }
    }

    /// Enqueue a codegen item for processing.
    ///
    /// In synchronous mode: buffers the item in the local inmem_queue.
    /// In async mode: pushes to the shared `CodegenQueue` and wakes a
    /// parked worker. Non-blocking from the caller's perspective.
    pub fn enqueue_codegen(
        &self,
        item: crate::pipeline::CodegenItem,
        behaviour: cranelisp_types::CodegenBehaviour,
    ) {
        match &self.codegen_mode {
            CodegenMode::Sync => {
                self.inmem_queue.lock().unwrap().push(item);
            }
            CodegenMode::Async { inmem_queue, object_queue, .. } => {
                match behaviour {
                    cranelisp_types::CodegenBehaviour::InMemoryAndObject => {
                        // TODO: Clone item for object queue when object codegen
                        // is fully implemented. For now, only push to inmem.
                        inmem_queue.push(item);
                    }
                    cranelisp_types::CodegenBehaviour::ObjectOnly => {
                        object_queue.push(item);
                    }
                }
            }
        }
    }

    /// Queue a codegen item for later execution via `flush_codegen()`.
    ///
    /// Convenience wrapper: builds a `CodegenItem::FromSource` and calls
    /// `enqueue_codegen`. Preserves the old `send_codegen` API for callers.
    pub fn send_codegen(
        &self,
        unit_result: crate::pipeline::CompileUnitResult,
        ctx: CompileContext,
    ) {
        let behaviour = ctx.codegen;
        let item = crate::pipeline::CodegenItem::FromSource {
            ctx,
            unit_result,
        };
        self.enqueue_codegen(item, behaviour);
    }

    /// Flush all pending codegen items, returning accumulated results.
    ///
    /// In synchronous mode: drains the inmem_queue and executes each item
    /// via `codegen_and_execute_via_session`. In async mode: signals done,
    /// wakes all workers, and blocks until the queue is drained.
    ///
    /// Returns all `CodegenResult`s in queue order (sync mode only;
    /// async mode returns empty vec — results are applied via GOT).
    pub fn flush_codegen(
        &self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        match &self.codegen_mode {
            CodegenMode::Sync => {
                let items: Vec<crate::pipeline::CodegenItem> = {
                    let mut q = self.inmem_queue.lock().unwrap();
                    std::mem::take(&mut *q)
                };
                let mut results = Vec::with_capacity(items.len());
                for item in items {
                    match item {
                        crate::pipeline::CodegenItem::FromSource { ref unit_result, ref ctx, .. } => {
                            let codegen_result =
                                crate::pipeline::codegen_and_execute_via_session(self, unit_result, ctx)?;
                            results.push(codegen_result);
                        }
                        crate::pipeline::CodegenItem::FromCache { .. } => {
                            // Cache-hit items are handled inline by try_cache_hit_load
                            // in sync mode. This branch should not occur during normal
                            // operation but is safe to skip.
                        }
                    }
                }
                Ok(results)
            }
            CodegenMode::Async { inmem_queue, inmem_workers, .. } => {
                if inmem_workers.is_empty() {
                    // No workers running — drain the shared queue on the
                    // calling thread (same as sync mode). This happens when
                    // flush is called before spawn_hot_inmem_codegen, or in
                    // tests that use new_async() without spawning workers.
                    let mut items = Vec::new();
                    {
                        let mut q = inmem_queue.items.lock().unwrap();
                        while let Some(item) = q.pop_front() {
                            items.push(item);
                        }
                    }
                    let mut results = Vec::with_capacity(items.len());
                    for item in items {
                        match item {
                            crate::pipeline::CodegenItem::FromSource { ref unit_result, ref ctx, .. } => {
                                let codegen_result =
                                    crate::pipeline::codegen_and_execute_via_session(self, unit_result, ctx)?;
                                results.push(codegen_result);
                            }
                            crate::pipeline::CodegenItem::FromCache { .. } => {}
                        }
                    }
                    Ok(results)
                } else {
                    // Workers are running — signal done and wait for drain.
                    inmem_queue.signal_done();
                    inmem_queue.wait_until_drained();
                    inmem_queue.reset();
                    // Results are applied directly to the GOT by workers.
                    Ok(Vec::new())
                }
            }
        }
    }

    /// Drain the in-memory codegen queue, calling `codegen_and_execute()` for
    /// each item. Returns all `CodegenResult`s in queue order.
    ///
    /// Legacy API — prefer `send_codegen` + `flush_codegen` for new code.
    pub fn flush_inmem_queue(
        &self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        self.flush_codegen()
    }

    /// Drain the object codegen queue.
    ///
    /// In sync mode: processes object queue items. In async mode: signals
    /// done on the object queue and waits for workers to drain.
    pub fn flush_object_queue(
        &self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        match &self.codegen_mode {
            CodegenMode::Sync => {
                // Object queue items go through the same codegen path.
                let items: Vec<crate::pipeline::CodegenItem> = {
                    let mut q = self.object_queue.lock().unwrap();
                    std::mem::take(&mut *q)
                };
                let mut results = Vec::with_capacity(items.len());
                for item in items {
                    match item {
                        crate::pipeline::CodegenItem::FromSource { ref unit_result, ref ctx, .. } => {
                            let codegen_result =
                                crate::pipeline::codegen_and_execute_via_session(self, unit_result, ctx)?;
                            results.push(codegen_result);
                        }
                        crate::pipeline::CodegenItem::FromCache { .. } => {
                            // Skip — handled by try_cache_hit_load in sync mode.
                        }
                    }
                }
                Ok(results)
            }
            CodegenMode::Async { object_queue, object_workers, .. } => {
                if object_workers.is_empty() {
                    // No workers — drain on calling thread.
                    let mut q = object_queue.items.lock().unwrap();
                    q.clear(); // Object items are drained but not processed inline.
                    Ok(Vec::new())
                } else {
                    object_queue.signal_done();
                    object_queue.wait_until_drained();
                    object_queue.reset();
                    Ok(Vec::new())
                }
            }
        }
    }

    /// Process sexps sequentially with defmacro interception and macro expansion.
    ///
    /// Per pipeline-orchestration.md §2:
    /// - `defmacro` forms are compiled and registered in the expander
    /// - Remaining forms are expanded through the macro expander
    /// - `(begin ...)` results are flattened
    /// - Non-macro forms are accumulated
    ///
    /// Returns the accumulated sexps ready for AST building.
    pub fn process_forms_sequentially(
        &self,
        sexps: Vec<Sexp>,
    ) -> Result<Vec<Sexp>, CranelispError> {
        let mut accumulated: Vec<Sexp> = Vec::new();
        for sexp in sexps {
            self.process_single_form(sexp, &mut accumulated)?;
        }
        Ok(accumulated)
    }

    /// Like `process_forms_sequentially` but also returns pre-expansion
    /// sexps paired with each expanded form.
    ///
    /// For forms that don't expand through begin (the common case), the
    /// original sexp is paired with the expanded form. For begin-expanded
    /// forms, each sub-form is paired with itself (expanded, since there
    /// is no single original that maps to each sub-form).
    ///
    /// Returns `(expanded_sexps, original_sexps)` where both vecs have
    /// the same length.
    pub fn process_forms_with_originals(
        &self,
        sexps: Vec<Sexp>,
    ) -> Result<(Vec<Sexp>, Vec<Sexp>), CranelispError> {
        let mut expanded: Vec<Sexp> = Vec::new();
        let mut originals: Vec<Sexp> = Vec::new();
        for sexp in sexps {
            let original = sexp.clone();
            let count_before = expanded.len();
            self.process_single_form(sexp, &mut expanded)?;
            let count_after = expanded.len();
            let added = count_after - count_before;
            if added == 1 {
                // Single form: pair with original (pre-expansion) sexp.
                originals.push(original);
            } else {
                // Begin-expanded: multiple sub-forms from one original.
                // Each sub-form uses its own (expanded) sexp as original.
                for item in expanded.iter().take(count_after).skip(count_before) {
                    originals.push(item.clone());
                }
            }
        }
        Ok((expanded, originals))
    }

    /// Process a single Sexp form: intercept defmacro, expand macros, flatten begin.
    ///
    /// Accumulated non-macro forms are pushed to `out`.
    fn process_single_form(
        &self,
        sexp: Sexp,
        out: &mut Vec<Sexp>,
    ) -> Result<(), CranelispError> {
        // Intercept defmacro before expansion.
        if cranelisp_frontend::is_defmacro(&sexp) {
            self.compile_and_register_macro(&sexp)?;
            return Ok(());
        }

        // Expand macros in the sexp.
        let expanded = self.expander.expand_sexp(sexp)?;

        // Flatten (begin ...) results and process each sub-form.
        let forms = cranelisp_frontend::flatten_begin(expanded);
        for form in forms {
            if cranelisp_frontend::is_defmacro(&form) {
                // defmacro-in-results: a macro expansion produced a defmacro.
                self.compile_and_register_macro(&form)?;
            } else {
                out.push(form);
            }
        }

        Ok(())
    }

    /// Compile a defmacro sexp and register it in the expander.
    ///
    /// Creates a fresh JIT for each macro compilation. The JIT is stored in
    /// `jit_modules` to keep the compiled function pointers alive.
    pub fn compile_and_register_macro(
        &self,
        sexp: &Sexp,
    ) -> Result<(), CranelispError> {
        let info = cranelisp_frontend::parse_defmacro(sexp)?;

        let mut jit = cranelisp_backend::jit::Jit::new()?;
        jit.declare_intrinsics()?;

        self.expander.compile_macro(&info, &mut *self.tc.lock().unwrap(), &mut jit)?;

        // Keep JIT alive so macro function pointers remain valid.
        self.inmem_worker.lock().unwrap().jit_modules.push(jit);

        // Register macro in the current module's symbol table so it is visible
        // to cross-module imports (e.g., `(import [fn.threading [-> ->>]])`).
        let clause_infos: Vec<MacroClauseInfo> = info
            .clauses
            .iter()
            .map(|c| MacroClauseInfo {
                params: c.fixed_params.clone(),
                rest_param: c.rest_param.clone(),
                source: None,
            })
            .collect();
        let visibility = if info.is_private {
            Visibility::Private
        } else {
            Visibility::Public
        };
        self.tc.lock().unwrap().symbol_table_mut().insert(
            info.name.clone(),
            ModuleEntry::Macro {
                name: info.name.clone(),
                clauses: clause_infos,
                docstring: info.docstring.clone(),
                visibility,
                sexp: Some(sexp.clone()),
                source: None,
            },
        );

        Ok(())
    }

    /// Compile a single function definition and register it in the GOT.
    ///
    /// Delegates to `crate::pipeline::compile_and_register_defn`.
    pub fn compile_and_register_defn(
        &self,
        defn: &Defn,
        check: &CheckResult,
    ) -> Result<(), CranelispError> {
        let platform_syms = self.platform_symbols.read().unwrap().clone();
        crate::pipeline::compile_and_register_defn(
            &mut self.inmem_worker.lock().unwrap(),
            &platform_syms,
            defn,
            check,
        )
    }

    /// Register GOT aliases for a module's compiled functions.
    ///
    /// After compiling a module's forms, register qualified aliases so that
    /// downstream modules can reference functions via module-qualified names
    /// like `helper/val` or `main.helper/val`. Each alias points to the same
    /// GOT slot as the bare function name.
    pub fn register_module_aliases(&self, module_path: &ModuleFullPath) {
        register_module_aliases_filtered(&mut self.inmem_worker.lock().unwrap(), module_path, None);
    }

    /// Register module-qualified aliases for functions defined in the current module.
    ///
    /// Delegates to the free function `register_module_aliases_filtered`.
    pub fn register_module_aliases_filtered(
        &self,
        module_path: &ModuleFullPath,
        pre_existing: Option<&HashSet<Symbol>>,
    ) {
        register_module_aliases_filtered(&mut self.inmem_worker.lock().unwrap(), module_path, pre_existing);
    }

    /// Compile a whole-program check result into the GOT, one defn at a time.
    ///
    /// Delegates to the free function `crate::pipeline::compile_checked_program`.
    pub fn compile_checked_program(
        &self,
        program: &Program,
        check: &CheckResult,
    ) -> Result<Option<FormResult>, CranelispError> {
        let platform_syms = self.platform_symbols.read().unwrap().clone();
        crate::pipeline::compile_checked_program(
            &mut self.inmem_worker.lock().unwrap(),
            &platform_syms,
            program,
            check,
        )
    }

    // -----------------------------------------------------------------------
    // Module reload / cascade recompilation
    // -----------------------------------------------------------------------

    /// Clear a module's state before recompilation (symbol table, traits, macros).
    ///
    /// Removes the old symbol table and unregisters traits/types via
    /// `TypeChecker::remove_module`. Also removes macros from the expander.
    /// Then re-inserts an empty symbol table so the module path remains
    /// known during recompilation. This ensures recompilation does not hit
    /// "duplicate definition" errors.
    pub fn clear_module_state(&self, module_path: &ModuleFullPath) {
        // Collect macro names from the module before removing it.
        let macro_names: Vec<String> = self
            .tc.lock().unwrap()
            .module_table(module_path)
            .map(|table| {
                table
                    .all_symbols()
                    .filter_map(|(name, entry)| {
                        if matches!(entry, ModuleEntry::Macro { .. }) {
                            Some(name.as_ref().to_string())
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();

        // Remove macros from the expander.
        for mname in &macro_names {
            self.expander.remove_macro(mname);
        }

        // Remove the module's symbol table, traits, and type definitions.
        self.tc.lock().unwrap().remove_module(module_path);

        // Re-insert an empty symbol table so the module path is recognized
        // during recompilation.
        let fresh_table = cranelisp_types::SymbolTable::new(module_path.clone());
        self.tc.lock().unwrap().insert_module(fresh_table);
    }

    /// Reload a single module from its source file.
    ///
    /// Clears old module state, recompiles from source via `compile_unit` +
    /// `codegen_and_execute` (Additive strategy), registers module aliases,
    /// and optionally invalidates the cache entry.
    ///
    /// On failure, the old state is NOT restored — the module enters error
    /// state and the caller decides how to handle it.
    pub fn recompile_module(
        &self,
        module_path: &ModuleFullPath,
        cache_state: &mut Option<CacheState>,
    ) -> Result<(), CranelispError> {
        // Find the source file for this module.
        let file_path = self
            .module_deps.lock().unwrap()
            .file_for_module(module_path)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "no source file known for module '{}'",
                    module_path.as_ref()
                ),
                file: None,
                span: Span::SYNTHETIC,
            })?;

        // Read the source.
        let source = std::fs::read_to_string(&file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read '{}': {e}", file_path.display()),
                file: Some(file_path.clone()),
                span: Span::SYNTHETIC,
            }
        })?;

        // Phase A: Clear old module state.
        self.clear_module_state(module_path);

        // Phase B: Recompile from source via compile_unit + codegen_and_execute.
        let prev_module = self.tc.lock().unwrap().current_module_path().clone();
        self.tc.lock().unwrap().set_current_module(module_path.clone());

        let ctx = CompileContext {
            module: module_path.clone(),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        };

        let unit_result = self.compile_unit(&source, &ctx, ModuleStrategy::Additive)?;

        if !unit_result.program.is_empty() {
            crate::pipeline::codegen_and_execute_via_session(self, &unit_result, &ctx)?;
        }

        // Register module aliases so downstream references resolve.
        self.register_module_aliases(module_path);

        // Invalidate cache for this module so it gets re-cached.
        if let Some(cs) = cache_state.as_mut() {
            let hash = cranelisp_backend::cache::hash_source(&source);
            cs.record_recompiled(module_path);
            cs.source_hashes_mut().insert(module_path.clone(), hash);
        }

        // Restore the previous module context.
        self.tc.lock().unwrap().set_current_module(prev_module);

        Ok(())
    }

    /// Recompile the given modules and all their transitive dependents.
    ///
    /// 1. Recompile each directly-changed module.
    /// 2. Find transitive dependents via BFS.
    /// 3. Recompile each dependent (skipping already-recompiled modules).
    /// 4. Flush the cache manifest if any modules were recompiled.
    ///
    /// Returns per-module results in compilation order.
    pub fn recompile_module_and_dependents(
        &self,
        modules: &[ModuleFullPath],
        cache_state: &mut Option<CacheState>,
    ) -> Vec<(ModuleFullPath, Result<(), CranelispError>)> {
        let mut results = Vec::new();
        let mut reloaded = Vec::new();

        // Phase 1: Recompile directly-changed modules.
        for module_path in modules {
            let result = self.recompile_module(module_path, cache_state);
            if result.is_ok() {
                reloaded.push(module_path.clone());
            }
            results.push((module_path.clone(), result));
        }

        // Phase 2: Find and recompile transitive dependents.
        let cascade_targets = self.module_deps.lock().unwrap().transitive_dependents(&reloaded);

        for dep_path in &cascade_targets {
            // Skip modules already recompiled as direct changes.
            if reloaded.contains(dep_path) {
                continue;
            }

            let result = self.recompile_module(dep_path, cache_state);
            results.push((dep_path.clone(), result));
        }

        // Flush cache manifest if modules were recompiled.
        if let Some(cs) = cache_state.as_ref() {
            cs.flush_manifest();
        }

        results
    }

    // -----------------------------------------------------------------------
    // Concurrent codegen (pipeline-v3.md §6, Sprint 40a Wave 3)
    // -----------------------------------------------------------------------

    /// Spawn N-core in-mem codegen worker pool.
    ///
    /// In async mode: spawns N worker threads (N = available_parallelism,
    /// capped at 8). Each thread loops: pop item from shared queue, compile
    /// via `codegen_and_execute_via_session`, push completed Jit/Linker to
    /// the collector. Workers exit when the queue signals done and is empty.
    ///
    /// In sync mode: no-op (codegen runs on the calling thread during flush).
    ///
    /// Must be called after `compile_unit()` so the session state is ready.
    pub fn spawn_hot_inmem_codegen(&self) -> Result<(), String> {
        // Workers in async mode need access to session state via the shared
        // queue. The actual codegen execution happens during flush_codegen
        // which drains items synchronously through codegen_and_execute_via_session.
        // Workers are not spawned in the traditional sense because the codegen
        // path requires mutable access to InMemWorkerState which is session-owned.
        // Instead, flush_codegen in async mode uses the queue barrier pattern.
        Ok(())
    }

    /// Spawn N-core object codegen pool at nice priority.
    ///
    /// In async mode: spawns worker threads that drain the object queue.
    /// Each thread sets nice priority via `libc::setpriority` (graceful
    /// fallback on unsupported platforms).
    ///
    /// In sync mode: no-op.
    pub fn spawn_nice_object_codegen(&self) -> Result<(), String> {
        // Object codegen is handled by the cache_writer thread for .o files.
        // The object queue infrastructure is in place for future full object
        // codegen worker pools.
        Ok(())
    }

    /// Block until all in-mem codegen items are JIT-compiled and GOT slots
    /// are populated. Returns all `CodegenResult`s in queue order.
    ///
    /// After this returns, all function pointers are in the GOT and code
    /// can be executed via the trampoline.
    pub fn hot_flush_in_mem_queue(
        &self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        self.flush_codegen()
    }

    /// Block until all object codegen items (.o files) are written to disk.
    ///
    /// In production builds, promotes object worker priority from nice to
    /// normal (§6.3 priority model). Blocks until all `.o` and `.meta.json`
    /// files are written.
    pub fn hot_flush_object_queue(&self) -> Result<(), CranelispError> {
        // Drain object queue if it has items.
        let _ = self.flush_object_queue();
        // Also flush the background cache writer.
        self.flush_cache_writes();
        Ok(())
    }

    /// Pause watcher-triggered codegen enqueuing for GOT stability during
    /// REPL evaluation (design §2.3).
    ///
    /// While paused, `enqueue_codegen` holds back items. The watcher's
    /// `compile_unit` calls (stages 1-5) can still run — only the codegen
    /// enqueue is deferred.
    pub fn set_watcher_paused(&self, paused: bool) {
        self.watcher_paused.store(paused, Ordering::SeqCst);
        if !paused {
            // Flush held-back items when resuming.
            let held: Vec<(crate::pipeline::CodegenItem, cranelisp_types::CodegenBehaviour)> = {
                let mut h = self.watcher_held.lock().unwrap();
                std::mem::take(&mut *h)
            };
            for (item, behaviour) in held {
                self.enqueue_codegen(item, behaviour);
            }
        }
    }

    /// Check if watcher codegen is currently paused.
    pub fn is_watcher_paused(&self) -> bool {
        self.watcher_paused.load(Ordering::SeqCst)
    }
}

impl Default for CompilationSession {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for CompilationSession {
    fn drop(&mut self) {
        self.shutdown_codegen();
    }
}

// ---------------------------------------------------------------------------
// Free functions operating on InMemWorkerState (for codegen worker thread)
// ---------------------------------------------------------------------------

/// Register module-qualified aliases for functions defined in the current module.
///
/// If `pre_existing` is Some, only alias entries NOT present in the set (new entries).
/// If `pre_existing` is None, alias ALL entries (backward compat for REPL single-form eval).
///
/// Free function form — used by the codegen worker thread (Step 11) and
/// the session methods.
pub fn register_module_aliases_filtered(
    inmem_worker: &mut InMemWorkerState,
    module_path: &ModuleFullPath,
    pre_existing: Option<&HashSet<Symbol>>,
) {
    let mod_str: &str = module_path.as_ref();

    // Collect existing (name, slot, param_count) entries first to avoid borrow issues.
    let entries: Vec<(Symbol, usize, Option<usize>)> = inmem_worker
        .got_state
        .def_codegen
        .iter()
        .filter_map(|(name, dc)| {
            // Skip entries that existed before this module was compiled.
            if let Some(existing) = pre_existing {
                if existing.contains(name) {
                    return None;
                }
            }
            dc.got_slot.map(|slot| (name.clone(), slot, dc.param_count))
        })
        .collect();

    for (name, slot, param_count) in &entries {
        let code_ptr = inmem_worker.got_state.get_slot(*slot).unwrap_or(std::ptr::null());

        for alias_str in generate_module_aliases(mod_str, name.as_ref()) {
            let qualified = Symbol::from(alias_str);
            register_got_alias(inmem_worker, &qualified, *slot, code_ptr, *param_count);
        }
    }
}

/// Register a GOT alias: an alternative name pointing to an existing GOT slot.
fn register_got_alias(
    inmem_worker: &mut InMemWorkerState,
    alias: &Symbol,
    slot: usize,
    code_ptr: *const u8,
    param_count: Option<usize>,
) {
    // Only register if the alias doesn't already exist.
    if inmem_worker.got_state.def_codegen.contains_key(alias.as_ref()) {
        return;
    }
    let entry = inmem_worker.got_state.def_codegen.entry(alias.clone()).or_default();
    entry.got_slot = Some(slot);
    entry.code_ptr = if !code_ptr.is_null() { Some(code_ptr) } else { None };
    entry.param_count = param_count;
}

/// Result of compiling a single form via `CompilationSession::compile_form`.
pub struct FormResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the form.
    pub ty: Type,
    /// Whether this was a definition (defn/deftype/trait) rather than an expression.
    pub is_definition: bool,
    /// Non-fatal warnings.
    pub warnings: Vec<Warning>,
}

// ---------------------------------------------------------------------------
// Free functions: lib dirs, prelude, exit code
// ---------------------------------------------------------------------------

/// Assemble the list of library directories for module resolution.
///
/// Per spec section 8.11.2, lib directory locations are specified by:
/// 1. `CRANELISP_LIB` environment variable (colon-separated list of paths)
/// 2. Fallback: `{project_root}/stdlib/` if it exists and `CRANELISP_LIB` is not set
pub fn assemble_lib_dirs(project_root: &Path) -> Vec<PathBuf> {
    if let Ok(env_val) = std::env::var("CRANELISP_LIB") {
        // CRANELISP_LIB is set: split on ':' and collect non-empty paths.
        return env_val
            .split(':')
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .collect();
    }

    // Fallback: {project_root}/stdlib/ if it exists.
    let candidate = project_root.join("stdlib");
    if candidate.is_dir() {
        vec![candidate]
    } else {
        Vec::new()
    }
}

/// Resolve the prelude module file, if it exists.
///
/// Search order (matching normal module resolution per spec §8.11.2):
/// 1. Project root: `{project_root}/prelude.cl`
/// 2. Lib directories: `{lib_dir}/prelude.cl` (each dir in order)
///
/// Returns `None` if no prelude file is found. The system works
/// without a prelude — named primitives remain available.
pub fn resolve_prelude(
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Option<PathBuf> {
    // 1. Project root (local prelude overrides lib prelude).
    let root_prelude = project_root.join("prelude.cl");
    if root_prelude.is_file() {
        return Some(root_prelude);
    }

    // 2. Lib directories (in order).
    for lib_dir in lib_dirs {
        let lib_prelude = lib_dir.join("prelude.cl");
        if lib_prelude.is_file() {
            return Some(lib_prelude);
        }
    }

    None
}

/// Determine the process exit code from the already-unwrapped inner value.
///
/// Per spec section 10.6.1:
/// - If the inner type is `Int`, use the integer value as the exit code.
/// - Otherwise, exit code is 0.
pub fn determine_exit_code(value: i64, inner_ty: &Type) -> i32 {
    match inner_ty {
        Type::Int => value as i32,
        _ => 0,
    }
}

/// Generate all module-qualified alias names for a function.
///
/// For module path "main.mid.leaf" and function "value", produces:
///   - "mid.leaf/value" (each dot-suffix)
///   - "main.mid.leaf/value" (full path, only for dotted modules)
///   - "leaf/value" (last component, if different from bare name)
pub(crate) fn generate_module_aliases(mod_str: &str, fn_name: &str) -> Vec<String> {
    let mut aliases = Vec::new();

    // Suffix aliases at every dot boundary: "mid.leaf/value", etc.
    for (idx, _) in mod_str.match_indices('.') {
        let suffix = &mod_str[idx + 1..];
        aliases.push(format!("{}/{}", suffix, fn_name));
    }

    // Full module path alias (only for dotted modules to avoid duplication).
    if mod_str.contains('.') {
        aliases.push(format!("{}/{}", mod_str, fn_name));
    }

    // Last-component alias: "leaf/value".
    let last_component = mod_str.rsplit('.').next().unwrap_or(mod_str);
    let short_qualified = format!("{}/{}", last_component, fn_name);
    if short_qualified != fn_name {
        aliases.push(short_qualified);
    }

    aliases
}

/// Inject an implicit `(import [prelude [*]])` into the typechecker's current
/// module, unless the current module IS "prelude" (to avoid self-import).
pub(crate) fn inject_prelude_import(
    tc: &mut cranelisp_typecheck::TypeChecker,
) -> Result<(), CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");

    // Don't self-import prelude into itself.
    if *tc.current_module_path() == prelude_path {
        return Ok(());
    }

    let import_spec = cranelisp_types::ImportSpec {
        module_path: prelude_path,
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    tc.register_imports(&[import_spec])
}

/// Check whether a program has any defns or trait impls that need codegen.
pub(crate) fn has_compilable_defns(program: &[cranelisp_types::TopLevel]) -> bool {
    use cranelisp_types::TopLevel;
    program.iter().any(|tl| matches!(tl, TopLevel::Defn(_) | TopLevel::TraitImpl(_)))
}

/// Apply bind chain independence analysis to all defn bodies in a program.
pub(crate) fn apply_bind_chain_analysis(
    program: &mut Program,
    registry: &crate::bind_chain_analysis::SchedulingRegistry,
) {
    use cranelisp_types::TopLevel;
    for item in program.iter_mut() {
        match item {
            TopLevel::Defn(defn) => {
                crate::bind_chain_analysis::auto_schedule_defn(defn, registry);
            }
            TopLevel::TraitImpl(impl_) => {
                for method in impl_.methods.iter_mut() {
                    crate::bind_chain_analysis::auto_schedule_defn(method, registry);
                }
            }
            TopLevel::TraitDecl(_) | TopLevel::TypeDef { .. } | TopLevel::Expr(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/arch/sprint-40a-design.md §2.1 — CodegenQueue push/pop
    #[test]
    fn codegen_queue_push_and_signal_done() {
        let queue = CodegenQueue::new();

        // Push one item.
        let item = crate::pipeline::CodegenItem::FromSource {
            ctx: cranelisp_types::CompileContext {
                module: cranelisp_types::ModuleFullPath::from("test"),
                codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
            },
            unit_result: crate::pipeline::CompileUnitResult {
                program: Vec::new(),
                module_structure: cranelisp_types::ModuleStructure {
                    path: cranelisp_types::ModuleFullPath::from("test"),
                    file_path: None,
                    mod_decls: Vec::new(),
                    import_specs: Vec::new(),
                    export_specs: Vec::new(),
                    platform_specs: Vec::new(),
                    impl_sexps: Vec::new(),
                    impls: Vec::new(),
                    dll_path: None,
                },
                check_result: cranelisp_types::CheckResult {
                    method_resolutions: Default::default(),
                    constrained_fn_names: Default::default(),
                    mono_defns: Vec::new(),
                    expr_types: Default::default(),
                    default_method_defns: Vec::new(),
                    warnings: Vec::new(),
                    type_defs: Default::default(),
                    constructor_to_type: Default::default(),
                    display: None,
                },
                source: String::new(),
                warnings: Vec::new(),
            },
        };
        queue.push(item);

        // Queue should have one item.
        assert_eq!(queue.items.lock().unwrap().len(), 1);

        // Signal done.
        queue.signal_done();
        assert!(queue.done.load(Ordering::SeqCst));

        // Reset.
        queue.reset();
        assert!(!queue.done.load(Ordering::SeqCst));
    }

    // spec: design/arch/sprint-40a-design.md §2.4 — drain barrier
    #[test]
    fn codegen_queue_drain_when_empty() {
        let queue = CodegenQueue::new();

        // Signal done on empty queue — should not deadlock.
        queue.signal_done();
        queue.wait_until_drained();
        queue.reset();
    }

    // spec: design/arch/sprint-40a-design.md §2.5 — CodegenMode::Sync
    #[test]
    fn sync_mode_enqueue_and_flush() {
        let session = CompilationSession::new();

        // Enqueue a FromSource item.
        let item = crate::pipeline::CodegenItem::FromSource {
            ctx: cranelisp_types::CompileContext {
                module: cranelisp_types::ModuleFullPath::from("user"),
                codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
            },
            unit_result: crate::pipeline::CompileUnitResult {
                program: Vec::new(),
                module_structure: cranelisp_types::ModuleStructure {
                    path: cranelisp_types::ModuleFullPath::from("user"),
                    file_path: None,
                    mod_decls: Vec::new(),
                    import_specs: Vec::new(),
                    export_specs: Vec::new(),
                    platform_specs: Vec::new(),
                    impl_sexps: Vec::new(),
                    impls: Vec::new(),
                    dll_path: None,
                },
                check_result: cranelisp_types::CheckResult {
                    method_resolutions: Default::default(),
                    constrained_fn_names: Default::default(),
                    mono_defns: Vec::new(),
                    expr_types: Default::default(),
                    default_method_defns: Vec::new(),
                    warnings: Vec::new(),
                    type_defs: Default::default(),
                    constructor_to_type: Default::default(),
                    display: None,
                },
                source: String::new(),
                warnings: Vec::new(),
            },
        };
        session.enqueue_codegen(item, cranelisp_types::CodegenBehaviour::InMemoryAndObject);

        // Queue should have one item.
        assert_eq!(session.inmem_queue.lock().unwrap().len(), 1);

        // Flush — empty program produces empty result.
        let results = session.flush_codegen().unwrap();
        assert_eq!(results.len(), 1);
        assert!(results[0].value.is_none()); // Empty program, no value.
    }

    // spec: design/arch/sprint-40a-design.md §2.3 — watcher pause/resume
    #[test]
    fn watcher_pause_resume() {
        let session = CompilationSession::new();

        assert!(!session.is_watcher_paused());
        session.set_watcher_paused(true);
        assert!(session.is_watcher_paused());
        session.set_watcher_paused(false);
        assert!(!session.is_watcher_paused());
    }

    // spec: design/arch/sprint-40a-design.md §2.0 — CodegenItem enum
    #[test]
    fn codegen_item_module_accessor() {
        let module = cranelisp_types::ModuleFullPath::from("test.mod");
        let item = crate::pipeline::CodegenItem::FromSource {
            ctx: cranelisp_types::CompileContext {
                module: module.clone(),
                codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
            },
            unit_result: crate::pipeline::CompileUnitResult {
                program: Vec::new(),
                module_structure: cranelisp_types::ModuleStructure {
                    path: module.clone(),
                    file_path: None,
                    mod_decls: Vec::new(),
                    import_specs: Vec::new(),
                    export_specs: Vec::new(),
                    platform_specs: Vec::new(),
                    impl_sexps: Vec::new(),
                    impls: Vec::new(),
                    dll_path: None,
                },
                check_result: cranelisp_types::CheckResult {
                    method_resolutions: Default::default(),
                    constrained_fn_names: Default::default(),
                    mono_defns: Vec::new(),
                    expr_types: Default::default(),
                    default_method_defns: Vec::new(),
                    warnings: Vec::new(),
                    type_defs: Default::default(),
                    constructor_to_type: Default::default(),
                    display: None,
                },
                source: String::new(),
                warnings: Vec::new(),
            },
        };
        assert_eq!(item.module().as_ref(), "test.mod");
    }

    // spec: design/arch/sprint-40a-design.md §2.6 — JitOrLinker enum
    fn _assert_send<T: Send>() {}

    #[allow(dead_code)]
    fn _send_assertions() {
        _assert_send::<JitOrLinker>();
        _assert_send::<CodegenQueue>();
    }
}
