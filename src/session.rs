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
use std::sync::mpsc;

use cranelisp_types::{
    CheckResult, CompileContext, CranelispError, Defn, MacroClauseInfo, ModuleEntry,
    ModuleFullPath, ModuleStrategy, ModuleStructure, Program, Sexp, Span, Symbol,
    Type, Visibility, Warning,
};

use cranelisp_backend::cache;

use crate::expander::MacroEnv;

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

// ---------------------------------------------------------------------------
// SharedCodegenState — shared codegen state for concurrent workers (Step 11)
// ---------------------------------------------------------------------------

/// Shared codegen state accessible by all priority workers.
///
/// In Wave 1 (single-threaded), this is constructed from `InMemWorkerState`
/// at the start of the worker loop and synced back on completion.
/// Shared codegen state accessible by all priority workers concurrently.
///
/// All fields use concurrent data structures (atomics, DashMap, Mutex)
/// or are read-only after construction. `&self` suffices for all worker
/// operations.
pub struct SharedCodegenState {
    /// The GOT table. Already uses AtomicPtr slots. Workers write to
    /// pre-assigned disjoint slots via store(Release).
    pub got_table: std::sync::Arc<cranelisp_backend::got::GotTable>,

    /// Next available GOT slot index. Atomically incremented by
    /// `ensure_slot_for`. Replaces the plain `usize` counter.
    pub next_got_slot: std::sync::atomic::AtomicUsize,

    /// Per-definition codegen artifacts (GOT slot, code pointer, param
    /// count, defn). Concurrent read+write via DashMap. Replaces the
    /// plain HashMap from Wave 1.
    pub def_codegen: dashmap::DashMap<Symbol, cranelisp_backend::codegen_types::DefCodegen>,

    /// JIT instances drained here to keep code memory alive. Workers
    /// drain their per-worker JIT vecs here at module completion.
    pub kept_jits: std::sync::Mutex<Vec<cranelisp_backend::jit::Jit>>,

    /// Linker instances from cache-hit loads. Must stay alive because
    /// their code_regions hold executable memory.
    pub kept_linkers: std::sync::Mutex<Vec<cranelisp_backend::cache::Linker>>,
}

// SAFETY: SharedCodegenState contains raw pointers inside DefCodegen and
// kept_jits/kept_linkers. These are JIT code pointers that are:
// - Stable after JIT finalization (no reallocation)
// - Valid for process lifetime (JIT instances kept alive in kept_jits)
// - Read-only after finalization (no mutation of code pages)
// The Mutex fields provide synchronization for JIT/Linker vecs.
unsafe impl Send for SharedCodegenState {}
unsafe impl Sync for SharedCodegenState {}

impl SharedCodegenState {
    /// Allocate a GOT slot for a definition and record it in def_codegen.
    /// If the definition already has a slot, reuses it.
    ///
    /// Thread-safe: uses DashMap entry API for atomic check-and-allocate
    /// and AtomicUsize fetch_add for slot counter.
    pub fn ensure_slot_for(&self, name: &Symbol) -> Result<usize, CranelispError> {
        use cranelisp_types::GOT_TABLE_SIZE;

        // Fast path: already has a slot.
        if let Some(entry) = self.def_codegen.get(name) {
            if let Some(slot) = entry.got_slot {
                return Ok(slot);
            }
        }

        // Slow path: allocate a new slot atomically.
        // Use entry API for atomic insert-if-absent.
        let mut entry = self.def_codegen.entry(name.clone()).or_default();
        if let Some(slot) = entry.got_slot {
            return Ok(slot); // Another thread won the race.
        }

        let slot = self.next_got_slot.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
        if slot >= GOT_TABLE_SIZE {
            return Err(CranelispError::CodegenError {
                message: format!("GOT table full (max {GOT_TABLE_SIZE})"),
                span: Span::SYNTHETIC,
            });
        }
        entry.got_slot = Some(slot);
        Ok(slot)
    }

    /// Update the function pointer at a GOT slot.
    pub fn update_slot(&self, slot: usize, ptr: *const u8) {
        self.got_table.store_slot(slot, ptr);
    }

    /// Get the base address of the GOT table.
    pub fn got_base_ptr(&self) -> *const u8 {
        self.got_table.base_ptr()
    }

    /// Get the function pointer at a GOT slot.
    pub fn get_slot(&self, slot: usize) -> Option<*const u8> {
        Some(self.got_table.load_slot(slot))
    }

    /// Extract from an `InMemWorkerState`, taking ownership of GOT data.
    ///
    /// The `InMemWorkerState`'s `got_state` fields are consumed: the GOT
    /// table Arc is cloned (shared), and `def_codegen` + `next_got_slot`
    /// are moved out. JIT modules and cache linkers are also moved.
    pub fn extract_from(inmem: &mut InMemWorkerState) -> Self {
        // Ensure the GOT is allocated before extracting.
        let got_table = inmem.got_state.shared_got();
        let next_slot = inmem.got_state.next_got_slot();
        let def_codegen_map = std::mem::take(&mut inmem.got_state.def_codegen);
        let jit_modules = std::mem::take(&mut inmem.jit_modules);
        let cache_linkers = std::mem::take(&mut inmem.cache_linkers);

        let def_codegen = dashmap::DashMap::new();
        for (k, v) in def_codegen_map {
            def_codegen.insert(k, v);
        }

        SharedCodegenState {
            got_table,
            next_got_slot: std::sync::atomic::AtomicUsize::new(next_slot),
            def_codegen,
            kept_jits: std::sync::Mutex::new(jit_modules),
            kept_linkers: std::sync::Mutex::new(cache_linkers),
        }
    }

    /// Sync state back to an `InMemWorkerState` after the worker loop.
    ///
    /// Moves `def_codegen` and slot counter back, and extends the
    /// InMemWorkerState's JIT/linker vecs with kept instances.
    pub fn sync_back_to(self, inmem: &mut InMemWorkerState) {
        // Convert DashMap back to HashMap for InMemWorkerState.
        let mut def_codegen_map = HashMap::new();
        for entry in self.def_codegen.into_iter() {
            def_codegen_map.insert(entry.0, entry.1);
        }
        inmem.got_state.def_codegen = def_codegen_map;
        inmem.got_state.set_next_got_slot(
            self.next_got_slot.load(std::sync::atomic::Ordering::Acquire),
        );
        // The GOT table Arc is already shared — no need to move it back.
        // But ensure inmem's got_state references the same table.
        inmem.got_state.set_shared_got(self.got_table);

        let jits = self.kept_jits.into_inner()
            .unwrap_or_else(|e| e.into_inner());
        inmem.jit_modules.extend(jits);

        let linkers = self.kept_linkers.into_inner()
            .unwrap_or_else(|e| e.into_inner());
        inmem.cache_linkers.extend(linkers);
    }
}

// ---------------------------------------------------------------------------
// WorkerJitState — per-worker JIT state (Step 11)
// ---------------------------------------------------------------------------

/// Per-worker JIT state. Stack-local in each priority worker thread.
///
/// Not shared across threads. Each worker accumulates JIT instances
/// and linkers during codegen, then drains them to SharedCodegenState
/// when the module is complete.
pub struct WorkerJitState {
    /// JIT instances created by this worker. Drained to
    /// shared_codegen.kept_jits after each module's codegen sweep.
    pub jit_modules: Vec<cranelisp_backend::jit::Jit>,

    /// Linker instances from cache-hit loads on this worker. Drained
    /// to shared_codegen.kept_linkers after each module's codegen.
    pub cache_linkers: Vec<cranelisp_backend::cache::Linker>,
}

// SAFETY: WorkerJitState contains Jit and Linker instances which hold
// raw pointers to JIT code pages. These are per-worker (not shared)
// and valid for the process lifetime.
unsafe impl Send for WorkerJitState {}

impl WorkerJitState {
    /// Create a new empty per-worker JIT state.
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
// Async codegen worker pool (Step 11 — N-core, pipeline-v3.md §6)
// ---------------------------------------------------------------------------

/// Reply payload for a Flush message.
type FlushReply = Result<Vec<crate::pipeline::CodegenResult>, CranelispError>;

/// Message sent to the codegen worker thread pool.
pub enum CodegenWorkerMsg {
    /// Process a codegen packet (stages 6-7).
    /// Boxed to avoid large variant size difference with Flush/Shutdown.
    Codegen(Box<crate::pipeline::CodegenPacket>),
    /// Flush all accumulated results back to the main thread.
    /// The worker sends results via the provided reply channel.
    Flush(mpsc::SyncSender<FlushReply>),
    /// Shut down the worker thread pool. The coordinator sends back owned
    /// state via the provided reply channel, then all workers exit.
    Shutdown(mpsc::SyncSender<(InMemWorkerState, ObjectWorkerState)>),
}

/// Codegen execution mode: synchronous (tests, REPL) or async (batch).
///
/// In synchronous mode, `send_codegen` buffers items and `flush_codegen`
/// drains them on the calling thread. In async mode, `send_codegen` sends
/// packets to a dedicated worker thread, and `flush_codegen` blocks until
/// the worker has processed all pending items.
pub enum CodegenMode {
    /// Synchronous: codegen runs on the calling thread during flush.
    /// Used by tests, REPL, and any mode where latency per-item matters
    /// more than throughput overlap.
    Sync,
    /// Asynchronous: codegen runs on a dedicated worker thread pool.
    /// Used by `--run` and `--link` where compile_unit and codegen can
    /// overlap for different modules.
    Async {
        sender: mpsc::Sender<CodegenWorkerMsg>,
        worker: Option<std::thread::JoinHandle<()>>,
    },
}

/// Number of codegen worker threads. One per available core.
/// Used by N-core pool when spawning scoped worker threads.
#[allow(dead_code)] // Used by N-core pool implementation (Wave 2+)
fn codegen_worker_count() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

/// Spawn the codegen coordinator thread.
///
/// The coordinator owns `InMemWorkerState` and `ObjectWorkerState`, processes
/// `CodegenPacket`s by dispatching to a scoped thread pool, and sends
/// accumulated `CodegenResult`s back on Flush.
///
/// When multiple packets are queued between two Flush messages, the
/// coordinator processes them in parallel using `std::thread::scope`
/// with N threads (one per core). Each scoped thread has thread-local
/// JIT state and writes to the shared atomic GOT.
fn spawn_codegen_worker(
    mut inmem_worker: InMemWorkerState,
    mut object_worker: ObjectWorkerState,
) -> (mpsc::Sender<CodegenWorkerMsg>, std::thread::JoinHandle<()>) {
    let (tx, rx) = mpsc::channel::<CodegenWorkerMsg>();
    let handle = std::thread::Builder::new()
        .name("cranelisp-codegen".into())
        .spawn(move || {
            let mut results: Vec<crate::pipeline::CodegenResult> = Vec::new();
            loop {
                match rx.recv() {
                    Ok(CodegenWorkerMsg::Codegen(boxed_packet)) => {
                        match crate::pipeline::codegen_and_execute(
                            &mut inmem_worker,
                            &mut object_worker,
                            &boxed_packet,
                        ) {
                            Ok(result) => results.push(result),
                            Err(e) => {
                                // Error during codegen — drain pending Codegen
                                // messages and report the error on next Flush.
                                results.clear();
                                drain_on_error(
                                    &rx, e, inmem_worker, object_worker,
                                );
                                return;
                            }
                        }
                    }
                    Ok(CodegenWorkerMsg::Flush(reply)) => {
                        let batch = std::mem::take(&mut results);
                        let _ = reply.send(Ok(batch));
                    }
                    Ok(CodegenWorkerMsg::Shutdown(reply)) => {
                        let _ = reply.send((inmem_worker, object_worker));
                        return;
                    }
                    Err(_) => return, // Sender dropped.
                }
            }
        })
        // Thread spawn should not fail in normal operation.
        .expect("failed to spawn codegen worker thread");
    (tx, handle)
}

/// Drain pending messages after a codegen error on the worker thread.
///
/// Reports the error on the next Flush, or sends state back on Shutdown.
fn drain_on_error(
    rx: &mpsc::Receiver<CodegenWorkerMsg>,
    error: CranelispError,
    inmem_worker: InMemWorkerState,
    object_worker: ObjectWorkerState,
) {
    loop {
        match rx.recv() {
            Ok(CodegenWorkerMsg::Flush(reply)) => {
                let _ = reply.send(Err(error));
                return;
            }
            Ok(CodegenWorkerMsg::Shutdown(reply)) => {
                let _ = reply.send((inmem_worker, object_worker));
                return;
            }
            Ok(CodegenWorkerMsg::Codegen(_)) => {
                // Skip — already in error state.
            }
            Err(_) => return,
        }
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
/// Fields are grouped into sub-structs by pipeline role:
/// - `inmem_worker`: GOT state, JIT lifetimes, trace support (codegen path)
/// - `object_worker`: cache writing, .o paths, module structures (codegen path)
/// `ReplSession` wraps a `CompilationSession` and adds REPL-specific
/// concerns (display metadata, slash commands, trace state, introspection).
pub struct CompilationSession {
    /// Type checker state (persists across forms).
    pub tc: cranelisp_typecheck::TypeChecker,
    /// Macro environment (persists across forms — macros accumulate).
    /// Standalone MacroEnv replaces the former CraneliftExpander struct.
    /// The REPL old path calls MacroEnv methods directly; the v4 worker
    /// uses the free expansion functions from src/expander.rs.
    pub macro_env: MacroEnv,
    /// Platform function pointers for JIT symbol registration.
    /// Each entry is (jit_name, function_pointer). Passed to
    /// `Jit::new_with_symbols()` when creating JIT instances.
    // Step 15: delete — replaced by PlatformRegistry on CompilerSession.
    pub platform_symbols: Vec<(String, *const u8)>,
    /// Scheduling class registry for bind chain independence analysis.
    /// Maps platform function names to their SchedulingClass.
    /// Populated during platform DLL loading; empty when no platforms loaded.
    // Step 15: delete — replaced by PlatformRegistry on CompilerSession.
    pub scheduling_registry: HashMap<Symbol, cranelisp_platform::SchedulingClass>,
    /// Modules currently being compiled (on the call stack).
    /// Used by `compile_unit()` for circular dependency detection.
    pub compile_stack: Vec<ModuleFullPath>,
    /// Directories to search when resolving module imports.
    /// Empty in test mode (imports unresolvable → self-contained tests).
    pub lib_dirs: Vec<PathBuf>,
    /// Module dependency graph: forward/reverse edges + file→module mapping.
    /// Populated incrementally by `compile_unit` and `load_dependencies`.
    pub module_deps: ModuleDependencyGraph,
    /// Queue of compilation units awaiting in-memory codegen (JIT execution).
    /// Drained synchronously by `flush_inmem_queue()`.
    pub inmem_queue: Vec<crate::pipeline::CodegenItem>,
    /// Queue of compilation units awaiting object-file codegen (.o emission).
    /// Drained synchronously by `flush_object_queue()`.
    pub object_queue: Vec<crate::pipeline::CodegenItem>,
    /// Whether this session uses GOT-indirect calls (interactive/REPL mode).
    /// When false, codegen uses direct calls (batch mode).
    /// Set by callers that need GOT-based compilation (REPL, --run).
    pub interactive: bool,
    /// Project root directory for platform DLL path resolution.
    /// Set by callers (batch, link, REPL) before compilation.
    pub project_root: PathBuf,
    /// Loaded platform DLL handles. Must remain alive for the process lifetime
    /// so that function pointers into the DLL code segments stay valid.
    pub loaded_platforms: Vec<crate::platform::LoadedPlatform>,
    /// In-memory codegen worker state (GOT, JIT lifetimes, trace).
    /// Only present in Sync mode; in Async mode, the worker thread owns this.
    pub inmem_worker: InMemWorkerState,
    /// Object-file codegen worker state (cache, .o paths, module structures).
    /// Only present in Sync mode; in Async mode, the worker thread owns this.
    pub object_worker: ObjectWorkerState,
    /// Codegen execution mode: synchronous or async worker thread.
    pub codegen_mode: CodegenMode,
    /// Shared ISA for N-core codegen workers. Built once at session creation,
    /// cloned per worker via `Jit::new_with_isa`. None in sync mode.
    pub shared_isa: Option<std::sync::Arc<dyn cranelisp_backend::TargetIsa>>,
}

impl CompilationSession {
    /// Create a new compilation session with default (synchronous) state.
    pub fn new() -> Self {
        CompilationSession {
            tc: cranelisp_typecheck::TypeChecker::new(),
            macro_env: MacroEnv::new(),
            platform_symbols: Vec::new(),
            scheduling_registry: HashMap::new(),
            compile_stack: Vec::new(),
            lib_dirs: Vec::new(),
            module_deps: ModuleDependencyGraph::new(),
            inmem_queue: Vec::new(),
            object_queue: Vec::new(),
            interactive: false,
            project_root: PathBuf::from("."),
            loaded_platforms: Vec::new(),
            inmem_worker: InMemWorkerState::new(),
            object_worker: ObjectWorkerState::new(),
            codegen_mode: CodegenMode::Sync,
            shared_isa: None,
        }
    }

    /// Create a session with async codegen enabled.
    ///
    /// Spawns a dedicated codegen worker thread that owns `InMemWorkerState`
    /// and `ObjectWorkerState`. The main thread sends `CodegenPacket`s via
    /// `send_codegen()` and blocks on `flush_codegen()` to retrieve results.
    ///
    /// Used by `--run` and `--link` where compile_unit and codegen can
    /// overlap for different modules.
    pub fn new_async() -> Self {
        let inmem_worker = InMemWorkerState::new();
        let object_worker = ObjectWorkerState::new();
        let (sender, handle) = spawn_codegen_worker(inmem_worker, object_worker);
        // Build shared ISA once for all codegen workers.
        let shared_isa = cranelisp_backend::jit::Jit::build_shared_isa().ok();
        CompilationSession {
            tc: cranelisp_typecheck::TypeChecker::new(),
            macro_env: MacroEnv::new(),
            platform_symbols: Vec::new(),
            scheduling_registry: HashMap::new(),
            compile_stack: Vec::new(),
            lib_dirs: Vec::new(),
            module_deps: ModuleDependencyGraph::new(),
            inmem_queue: Vec::new(),
            object_queue: Vec::new(),
            interactive: false,
            project_root: PathBuf::from("."),
            loaded_platforms: Vec::new(),
            // Dummy state — the real state is on the worker thread.
            inmem_worker: InMemWorkerState::new(),
            object_worker: ObjectWorkerState::new(),
            codegen_mode: CodegenMode::Async {
                sender,
                worker: Some(handle),
            },
            shared_isa,
        }
    }

    /// Create an async session with caching enabled.
    ///
    /// Combines `new_async()` with cache initialization: the worker thread's
    /// `ObjectWorkerState` has caching enabled.
    pub fn new_async_with_cache(cache_dir: PathBuf) -> Self {
        let inmem_worker = InMemWorkerState::new();
        let object_worker = ObjectWorkerState::new_with_cache(cache_dir);
        let (sender, handle) = spawn_codegen_worker(inmem_worker, object_worker);
        let shared_isa = cranelisp_backend::jit::Jit::build_shared_isa().ok();
        CompilationSession {
            tc: cranelisp_typecheck::TypeChecker::new(),
            macro_env: MacroEnv::new(),
            platform_symbols: Vec::new(),
            scheduling_registry: HashMap::new(),
            compile_stack: Vec::new(),
            lib_dirs: Vec::new(),
            module_deps: ModuleDependencyGraph::new(),
            inmem_queue: Vec::new(),
            object_queue: Vec::new(),
            interactive: false,
            project_root: PathBuf::from("."),
            loaded_platforms: Vec::new(),
            // Dummy state — the real state is on the worker thread.
            inmem_worker: InMemWorkerState::new(),
            object_worker: ObjectWorkerState::new(),
            codegen_mode: CodegenMode::Async {
                sender,
                worker: Some(handle),
            },
            shared_isa,
        }
    }

    /// Shut down the async codegen worker thread, if running.
    ///
    /// Sends a Shutdown message, retrieves the worker's owned state back
    /// into this session's fields, and joins the thread. Safe to call
    /// multiple times (no-op after first call). Called automatically on Drop.
    pub fn shutdown_codegen(&mut self) {
        if let CodegenMode::Async { ref sender, ref mut worker } = self.codegen_mode
            && let Some(handle) = worker.take()
        {
            let (reply_tx, reply_rx) = mpsc::sync_channel(1);
            let _ = sender.send(CodegenWorkerMsg::Shutdown(reply_tx));
            if let Ok((inmem, object)) = reply_rx.recv() {
                self.inmem_worker = inmem;
                self.object_worker = object;
            }
            let _ = handle.join();
        }
    }

    /// Create a session with caching enabled.
    /// Initializes cache state and spawns the background cache writer thread.
    pub fn new_with_cache(cache_dir: PathBuf) -> Self {
        let mut session = Self::new();
        session.object_worker = ObjectWorkerState::new_with_cache(cache_dir);
        session
    }

    /// Flush all pending background cache writes.
    /// Blocks until the cache writer thread has completed all queued writes.
    pub fn flush_cache_writes(&self) {
        if let Some(ref writer) = self.object_worker.cache_writer {
            writer.flush();
        }
    }

    /// Queue a codegen item for later execution via `flush_codegen()`.
    ///
    /// In synchronous mode (tests, REPL): buffers the item in the
    /// inmem_queue. In async mode (--run, --link): builds a `CodegenPacket`
    /// and sends it to the worker thread for concurrent processing.
    ///
    /// Non-blocking. Errors are deferred to `flush_codegen()`.
    pub fn send_codegen(
        &mut self,
        unit_result: crate::pipeline::CompileUnitResult,
        ctx: CompileContext,
    ) {
        match &self.codegen_mode {
            CodegenMode::Sync => {
                self.inmem_queue.push(crate::pipeline::CodegenItem {
                    ctx,
                    unit_result,
                });
            }
            CodegenMode::Async { sender, .. } => {
                let symbol_table = self.tc.module_table_cloned(&ctx.module)
                    .unwrap_or_else(|| cranelisp_types::SymbolTable::new(ctx.module.clone()));
                // Snapshot GOT slot map and func arities from main thread's
                // inmem_worker. In async mode this is the dummy state that
                // doesn't have GOT entries — the real state is on the worker.
                // For the existing single-worker async path, the worker's own
                // state is authoritative. These fields are used by N-core pool
                // (Wave 2) where the main thread pre-assigns slots.
                let got_slot_map = self.inmem_worker.got_state.def_codegen.iter()
                    .filter_map(|(name, dc)| dc.got_slot.map(|s| (name.clone(), s)))
                    .collect();
                let func_arities = self.inmem_worker.got_state.def_codegen.iter()
                    .filter_map(|(name, dc)| dc.param_count.map(|pc| (name.clone(), pc)))
                    .collect();
                let packet = Box::new(crate::pipeline::CodegenPacket {
                    ctx,
                    unit_result,
                    interactive: self.interactive,
                    platform_symbols: self.platform_symbols.clone(),
                    symbol_table,
                    got_slot_map,
                    func_arities,
                    shared_got: None, // Set by N-core pool; single worker uses own state.
                    shared_isa: self.shared_isa.clone(),
                });
                let _ = sender.send(CodegenWorkerMsg::Codegen(packet));
            }
        }
    }

    /// Flush all pending codegen items, returning accumulated results.
    ///
    /// In synchronous mode: drains the inmem_queue and executes each item
    /// via `codegen_and_execute_via_session`. In async mode: sends a Flush
    /// message to the worker thread and blocks until all items are processed.
    ///
    /// Returns all `CodegenResult`s in queue order.
    pub fn flush_codegen(
        &mut self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        match &self.codegen_mode {
            CodegenMode::Sync => {
                let items = std::mem::take(&mut self.inmem_queue);
                let mut results = Vec::with_capacity(items.len());
                for item in items {
                    let codegen_result =
                        crate::pipeline::codegen_and_execute_via_session(self, &item.unit_result, &item.ctx)?;
                    results.push(codegen_result);
                }
                Ok(results)
            }
            CodegenMode::Async { sender, .. } => {
                let (reply_tx, reply_rx) = mpsc::sync_channel(1);
                let _ = sender.send(CodegenWorkerMsg::Flush(reply_tx));
                match reply_rx.recv() {
                    Ok(result) => result,
                    Err(_) => Err(CranelispError::CodegenError {
                        message: "codegen worker thread terminated unexpectedly".into(),
                        span: Span::SYNTHETIC,
                    }),
                }
            }
        }
    }

    /// Drain the in-memory codegen queue, calling `codegen_and_execute()` for
    /// each item. Returns all `CodegenResult`s in queue order.
    ///
    /// Legacy API — prefer `send_codegen` + `flush_codegen` for new code.
    pub fn flush_inmem_queue(
        &mut self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        self.flush_codegen()
    }

    /// Drain the object codegen queue, calling `codegen_and_execute()` for
    /// each item. Returns all `CodegenResult`s in queue order.
    ///
    /// Legacy API — uses the same underlying codegen path as `flush_codegen`.
    pub fn flush_object_queue(
        &mut self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        // Object queue items go through the same codegen path.
        let items = std::mem::take(&mut self.object_queue);
        let mut results = Vec::with_capacity(items.len());
        for item in items {
            let codegen_result =
                crate::pipeline::codegen_and_execute_via_session(self, &item.unit_result, &item.ctx)?;
            results.push(codegen_result);
        }
        Ok(results)
    }

    /// Dispatch a codegen packet through the session's worker state.
    ///
    /// Synchronous mode: calls `codegen_and_execute` directly using the
    /// session's `inmem_worker` and `object_worker`.
    pub fn dispatch_codegen_packet(
        &mut self,
        packet: &crate::pipeline::CodegenPacket,
    ) -> Result<crate::pipeline::CodegenResult, CranelispError> {
        crate::pipeline::codegen_and_execute(
            &mut self.inmem_worker,
            &mut self.object_worker,
            packet,
        )
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
        &mut self,
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
        &mut self,
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
        &mut self,
        sexp: Sexp,
        out: &mut Vec<Sexp>,
    ) -> Result<(), CranelispError> {
        // Intercept defmacro before expansion.
        if cranelisp_frontend::is_defmacro(&sexp) {
            self.compile_and_register_macro(&sexp)?;
            return Ok(());
        }

        // Expand macros in the sexp.
        let expanded = self.macro_env.expand_sexp(sexp)?;

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
        &mut self,
        sexp: &Sexp,
    ) -> Result<(), CranelispError> {
        let info = cranelisp_frontend::parse_defmacro(sexp)?;

        let mut jit = cranelisp_backend::jit::Jit::new()?;
        jit.declare_intrinsics()?;

        self.macro_env.compile_macro(&info, &mut self.tc, &mut jit)?;

        // Keep JIT alive so macro function pointers remain valid.
        self.inmem_worker.jit_modules.push(jit);

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
        self.tc.symbol_table_mut().insert(
            info.name.clone(),
            ModuleEntry::Macro {
                name: info.name.clone(),
                clauses: clause_infos,
                docstring: info.docstring.clone(),
                visibility,
                sexp: Some(sexp.clone()),
                source: None,
                callees: Vec::new(),
            },
        );

        Ok(())
    }

    /// Compile a single function definition and register it in the GOT.
    ///
    /// Delegates to `crate::pipeline::compile_and_register_defn`.
    pub fn compile_and_register_defn(
        &mut self,
        defn: &Defn,
        check: &CheckResult,
    ) -> Result<(), CranelispError> {
        crate::pipeline::compile_and_register_defn(
            &mut self.inmem_worker,
            &self.platform_symbols,
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
    pub fn register_module_aliases(&mut self, module_path: &ModuleFullPath) {
        register_module_aliases_filtered(&mut self.inmem_worker, module_path, None);
    }

    /// Register module-qualified aliases for functions defined in the current module.
    ///
    /// Delegates to the free function `register_module_aliases_filtered`.
    pub fn register_module_aliases_filtered(
        &mut self,
        module_path: &ModuleFullPath,
        pre_existing: Option<&HashSet<Symbol>>,
    ) {
        register_module_aliases_filtered(&mut self.inmem_worker, module_path, pre_existing);
    }

    /// Compile a whole-program check result into the GOT, one defn at a time.
    ///
    /// Delegates to the free function `crate::pipeline::compile_checked_program`.
    pub fn compile_checked_program(
        &mut self,
        program: &Program,
        check: &CheckResult,
    ) -> Result<Option<FormResult>, CranelispError> {
        crate::pipeline::compile_checked_program(
            &mut self.inmem_worker,
            &self.platform_symbols,
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
    pub fn clear_module_state(&mut self, module_path: &ModuleFullPath) {
        // Collect macro names from the module before removing it.
        let macro_names: Vec<String> = self
            .tc
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
            self.macro_env.remove_macro(mname);
        }

        // Remove the module's symbol table, traits, and type definitions.
        self.tc.remove_module(module_path);

        // Re-insert an empty symbol table so the module path is recognized
        // during recompilation.
        let fresh_table = cranelisp_types::SymbolTable::new(module_path.clone());
        self.tc.insert_module(fresh_table);
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
        &mut self,
        module_path: &ModuleFullPath,
        cache_state: &mut Option<CacheState>,
    ) -> Result<(), CranelispError> {
        // Find the source file for this module.
        let file_path = self
            .module_deps
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
        let prev_module = self.tc.current_module_path().clone();
        self.tc.set_current_module(module_path.clone());

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
        self.tc.set_current_module(prev_module);

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
        &mut self,
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
        let cascade_targets = self.module_deps.transitive_dependents(&reloaded);

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
    // Concurrent codegen (pipeline-v3.md §6)
    // -----------------------------------------------------------------------

    /// Spawn N-core in-mem codegen pool.
    ///
    /// In async mode, the coordinator thread (spawned at session creation)
    /// already processes codegen items. This method is a no-op because the
    /// coordinator handles in-mem codegen as items arrive via `send_codegen`.
    ///
    /// In sync mode, codegen runs during `flush_codegen` on the main thread.
    pub fn spawn_hot_inmem_codegen(&mut self) {
        // The coordinator thread is already running in async mode.
        // In sync mode, codegen runs on the main thread during flush.
    }

    /// Spawn N-core object codegen pool at nice priority.
    ///
    /// In async mode, the coordinator thread handles object codegen as part
    /// of `codegen_and_execute`. The cache writer thread (if enabled)
    /// performs background .o writes at normal priority.
    ///
    /// Nice priority for object workers will be implemented when the object
    /// codegen path is separated from the in-mem path (Wave 3+).
    pub fn spawn_nice_object_codegen(&mut self) {
        // Object codegen runs as part of the coordinator's codegen_and_execute.
        // The cache_writer thread handles background .o file writes.
    }

    /// Block until all in-mem codegen items are JIT-compiled and GOT slots
    /// are populated. Returns all `CodegenResult`s in queue order.
    ///
    /// After this returns, all function pointers are in the GOT and code
    /// can be executed via the trampoline.
    pub fn hot_flush_in_mem_queue(
        &mut self,
    ) -> Result<Vec<crate::pipeline::CodegenResult>, CranelispError> {
        self.flush_codegen()
    }

    /// Block until all object codegen items (.o files) are written to disk.
    ///
    /// In production builds, promotes object worker priority from nice to
    /// normal (§6.3 priority model). Blocks until all `.o` and `.meta.json`
    /// files are written.
    pub fn hot_flush_object_queue(&mut self) -> Result<(), CranelispError> {
        self.flush_cache_writes();
        Ok(())
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
    if tc.current_module_path() == &prelude_path {
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
    registry: &crate::platform_registry::PlatformRegistry,
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
