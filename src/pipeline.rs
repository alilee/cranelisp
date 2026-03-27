// Pipeline orchestration: source text -> parse -> build -> typecheck -> codegen -> execute.
//
// Two modes:
//   1. Single-file batch: `compile_and_run()` — compiles one source string.
//   2. Multi-file batch: `compile_module_graph()` — discovers modules, toposorts, compiles in order.
//
// Both modes use `CompilationSession` for the core compilation loop:
//   parse -> expand (defmacro interception) -> build AST -> typecheck -> codegen -> GOT register.
//
// No `unwrap()` in this module -- all errors use `?`.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::mpsc;

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
    fn cache_dir(&self) -> Option<&Path> {
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
    recompiled: std::collections::HashSet<ModuleFullPath>,
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
            recompiled: std::collections::HashSet::new(),
        }
    }

    /// Returns the cache directory path.
    pub fn cache_dir(&self) -> &std::path::Path {
        &self.cache_dir
    }

    /// Record that a module was recompiled (cache miss).
    pub fn record_recompiled(&mut self, module_path: &ModuleFullPath) {
        self.recompiled.insert(module_path.clone());
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
}

impl InMemWorkerState {
    fn new() -> Self {
        InMemWorkerState {
            got_state: cranelisp_backend::got::ModuleCodegenState::new(),
            jit_modules: Vec::new(),
            traced_fns: Vec::new(),
            trace_extra_symbols: Vec::new(),
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
    /// See design/arch/pipeline-v2.md §16.5.
    pub cache_state: Option<CacheState>,
    /// Background .o writer. Created when cache_state is Some.
    /// See design/arch/pipeline-v2.md §16.12.
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
    fn new() -> Self {
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
// Async codegen worker (Step 11)
// ---------------------------------------------------------------------------

/// Reply payload for a Flush message.
type FlushReply = Result<Vec<crate::pipeline_v2::CodegenResult>, CranelispError>;

/// Message sent to the codegen worker thread.
pub enum CodegenWorkerMsg {
    /// Process a codegen packet (stages 6-7).
    /// Boxed to avoid large variant size difference with Flush/Shutdown.
    Codegen(Box<crate::pipeline_v2::CodegenPacket>),
    /// Flush all accumulated results back to the main thread.
    /// The worker sends results via the provided reply channel.
    Flush(mpsc::SyncSender<FlushReply>),
    /// Shut down the worker thread. The worker sends back its owned state
    /// via the provided reply channel, then exits.
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
    /// Asynchronous: codegen runs on a dedicated worker thread.
    /// Used by `--run` and `--link` where compile_unit and codegen can
    /// overlap for different modules.
    Async {
        sender: mpsc::Sender<CodegenWorkerMsg>,
        worker: Option<std::thread::JoinHandle<()>>,
    },
}

/// Spawn the codegen worker thread.
///
/// The worker owns `InMemWorkerState` and `ObjectWorkerState`, processes
/// `CodegenPacket`s as they arrive, and sends accumulated `CodegenResult`s
/// back on Flush. On Shutdown, the worker sends its state back and exits.
fn spawn_codegen_worker(
    mut inmem_worker: InMemWorkerState,
    mut object_worker: ObjectWorkerState,
) -> (mpsc::Sender<CodegenWorkerMsg>, std::thread::JoinHandle<()>) {
    let (tx, rx) = mpsc::channel::<CodegenWorkerMsg>();
    let handle = std::thread::Builder::new()
        .name("cranelisp-codegen".into())
        .spawn(move || {
            let mut results: Vec<crate::pipeline_v2::CodegenResult> = Vec::new();
            loop {
                match rx.recv() {
                    Ok(CodegenWorkerMsg::Codegen(boxed_packet)) => {
                        match crate::pipeline_v2::codegen_and_execute(
                            &mut inmem_worker,
                            &mut object_worker,
                            &boxed_packet,
                        ) {
                            Ok(result) => results.push(result),
                            Err(e) => {
                                // Error during codegen — drain pending Codegen
                                // messages and report the error on next Flush.
                                results.clear();
                                loop {
                                    match rx.recv() {
                                        Ok(CodegenWorkerMsg::Flush(reply)) => {
                                            let _ = reply.send(Err(e));
                                            break;
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
    /// Macro expander (persists across forms — macros accumulate).
    pub expander: CraneliftExpander,
    /// Platform function pointers for JIT symbol registration.
    /// Each entry is (jit_name, function_pointer). Passed to
    /// `Jit::new_with_symbols()` when creating JIT instances.
    pub platform_symbols: Vec<(String, *const u8)>,
    /// Scheduling class registry for bind chain independence analysis.
    /// Maps platform function names to their SchedulingClass.
    /// Populated during platform DLL loading; empty when no platforms loaded.
    pub scheduling_registry: crate::bind_chain_analysis::SchedulingRegistry,
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
    pub inmem_queue: Vec<crate::pipeline_v2::CodegenItem>,
    /// Queue of compilation units awaiting object-file codegen (.o emission).
    /// Drained synchronously by `flush_object_queue()`.
    pub object_queue: Vec<crate::pipeline_v2::CodegenItem>,
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
}

impl CompilationSession {
    /// Create a new compilation session with default (synchronous) state.
    pub fn new() -> Self {
        CompilationSession {
            tc: cranelisp_typecheck::TypeChecker::new(),
            expander: CraneliftExpander::new(),
            platform_symbols: Vec::new(),
            scheduling_registry: crate::bind_chain_analysis::SchedulingRegistry::new(),
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
        CompilationSession {
            tc: cranelisp_typecheck::TypeChecker::new(),
            expander: CraneliftExpander::new(),
            platform_symbols: Vec::new(),
            scheduling_registry: crate::bind_chain_analysis::SchedulingRegistry::new(),
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
        CompilationSession {
            tc: cranelisp_typecheck::TypeChecker::new(),
            expander: CraneliftExpander::new(),
            platform_symbols: Vec::new(),
            scheduling_registry: crate::bind_chain_analysis::SchedulingRegistry::new(),
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
        unit_result: crate::pipeline_v2::CompileUnitResult,
        ctx: cranelisp_types::CompileContext,
    ) {
        match &self.codegen_mode {
            CodegenMode::Sync => {
                self.inmem_queue.push(crate::pipeline_v2::CodegenItem {
                    ctx,
                    unit_result,
                });
            }
            CodegenMode::Async { sender, .. } => {
                let symbol_table = self.tc.module_table(&ctx.module)
                    .cloned()
                    .unwrap_or_else(|| cranelisp_types::SymbolTable::new(ctx.module.clone()));
                let packet = Box::new(crate::pipeline_v2::CodegenPacket {
                    ctx,
                    unit_result,
                    interactive: self.interactive,
                    platform_symbols: self.platform_symbols.clone(),
                    symbol_table,
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
    ) -> Result<Vec<crate::pipeline_v2::CodegenResult>, CranelispError> {
        match &self.codegen_mode {
            CodegenMode::Sync => {
                let items = std::mem::take(&mut self.inmem_queue);
                let mut results = Vec::with_capacity(items.len());
                for item in items {
                    let codegen_result =
                        crate::pipeline_v2::codegen_and_execute_via_session(self, &item.unit_result, &item.ctx)?;
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
    ) -> Result<Vec<crate::pipeline_v2::CodegenResult>, CranelispError> {
        self.flush_codegen()
    }

    /// Drain the object codegen queue, calling `codegen_and_execute()` for
    /// each item. Returns all `CodegenResult`s in queue order.
    ///
    /// Legacy API — uses the same underlying codegen path as `flush_codegen`.
    pub fn flush_object_queue(
        &mut self,
    ) -> Result<Vec<crate::pipeline_v2::CodegenResult>, CranelispError> {
        // Object queue items go through the same codegen path.
        let items = std::mem::take(&mut self.object_queue);
        let mut results = Vec::with_capacity(items.len());
        for item in items {
            let codegen_result =
                crate::pipeline_v2::codegen_and_execute_via_session(self, &item.unit_result, &item.ctx)?;
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
        packet: &crate::pipeline_v2::CodegenPacket,
    ) -> Result<crate::pipeline_v2::CodegenResult, CranelispError> {
        crate::pipeline_v2::codegen_and_execute(
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
        &mut self,
        sexp: &Sexp,
    ) -> Result<(), CranelispError> {
        let info = cranelisp_frontend::parse_defmacro(sexp)?;

        let mut jit = cranelisp_backend::jit::Jit::new()?;
        jit.declare_intrinsics()?;

        self.expander.compile_macro(&info, &mut self.tc, &mut jit)?;

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
            },
        );

        Ok(())
    }

    /// Compile a single function definition and register it in the GOT.
    ///
    /// Delegates to `crate::pipeline_v2::compile_and_register_defn`.
    pub fn compile_and_register_defn(
        &mut self,
        defn: &Defn,
        check: &CheckResult,
    ) -> Result<(), CranelispError> {
        crate::pipeline_v2::compile_and_register_defn(
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
        pre_existing: Option<&std::collections::HashSet<Symbol>>,
    ) {
        register_module_aliases_filtered(&mut self.inmem_worker, module_path, pre_existing);
    }

    /// Compile a whole-program check result into the GOT, one defn at a time.
    ///
    /// Delegates to the free function `crate::pipeline_v2::compile_checked_program`.
    pub fn compile_checked_program(
        &mut self,
        program: &Program,
        check: &CheckResult,
    ) -> Result<Option<FormResult>, CranelispError> {
        crate::pipeline_v2::compile_checked_program(
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
            self.expander.remove_macro(mname);
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
            strategy: ModuleStrategy::Additive,
            codegen_target: cranelisp_types::CodegenTarget::JitAndCache,
        };

        let unit_result = crate::pipeline_v2::compile_unit(self, &source, &ctx)?;

        if !unit_result.program.is_empty() {
            crate::pipeline_v2::codegen_and_execute_via_session(self, &unit_result, &ctx)?;
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
    pre_existing: Option<&std::collections::HashSet<Symbol>>,
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

// build_check_for_backend() deleted — v2 pipeline passes CheckResult directly
// to the backend. The backend ignores display, and mono_defns are compiled
// within compile_checked_program. See design/arch/pipeline-v2.md §15.2.

// ---------------------------------------------------------------------------
// Single-file batch pipeline (existing)
// ---------------------------------------------------------------------------

/// Result of compiling and executing a source program.
pub struct PipelineResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the last expression or main function's return.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Compile and execute source text via the unified v2 pipeline.
///
/// Thin wrapper around `compile_unit()` that preserves the `PipelineResult`
/// interface used by 449+ test call sites. Creates a fresh session per call.
pub fn compile_and_run(
    source: &str,
) -> Result<PipelineResult, CranelispError> {
    let mut session = CompilationSession::new();
    let ctx = CompileContext {
        module: ModuleFullPath::from("user"),
        strategy: ModuleStrategy::Additive,
        codegen_target: cranelisp_types::CodegenTarget::JitAndCache,
    };
    let unit_result = crate::pipeline_v2::compile_unit(&mut session, source, &ctx)?;
    let warnings_from_unit = unit_result.warnings.clone();
    session.inmem_queue.push(crate::pipeline_v2::CodegenItem {
        ctx,
        unit_result,
    });
    let mut codegen_results = session.flush_inmem_queue()?;
    let codegen_result = match codegen_results.pop() {
        Some(r) => r,
        None => unreachable!("invariant: flush_inmem_queue must return one result per queued item"),
    };

    let mut warnings = warnings_from_unit;
    warnings.extend(codegen_result.warnings);

    Ok(PipelineResult {
        value: codegen_result.value.unwrap_or(0),
        ty: codegen_result.result_type.unwrap_or(Type::Int),
        warnings,
    })
}

// ---------------------------------------------------------------------------
// Multi-file module graph pipeline
// ---------------------------------------------------------------------------

/// A node in the module dependency graph.
#[derive(Debug, Clone)]
pub struct ModuleNode {
    /// Module's full dotted path (e.g., "util", "core.math").
    pub path: ModuleFullPath,
    /// Filesystem path to the .cl source file.
    pub file_path: PathBuf,
    /// Modules this module depends on (declared via `mod`).
    pub dependencies: Vec<ModuleFullPath>,
}

/// The complete module dependency graph for a project.
#[derive(Debug)]
pub struct ModuleGraph {
    /// All modules, keyed by full path.
    pub nodes: HashMap<ModuleFullPath, ModuleNode>,
    /// The entry module's path.
    pub entry: ModuleFullPath,
    /// Project root directory (parent of the entry file).
    pub project_root: PathBuf,
    /// Library directories for module resolution (searched in order after project root).
    pub lib_dirs: Vec<PathBuf>,
}

/// Result of compiling a multi-file module graph (compile + execute).
pub struct CompiledModuleGraph {
    /// The i64 result value from executing the entry module's entry point.
    pub value: i64,
    /// The inferred type of the entry point's return value.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Discover the module dependency graph starting from an entry file.
///
/// Parses each file to extract `(mod name)` declarations, resolves file paths
/// per spec section 8.2.5, and recurses into submodules. Detects circular
/// dependencies.
///
/// `lib_dirs` provides library search paths for module resolution (searched in
/// order after the project root). Pass `&[]` to disable library resolution
/// (e.g. in tests with controlled fixtures).
pub fn discover_module_graph(
    entry: &Path,
    lib_dirs: &[PathBuf],
) -> Result<ModuleGraph, CranelispError> {
    let entry = entry.canonicalize().map_err(|e| CranelispError::ModuleError {
        message: format!("cannot resolve entry file '{}': {}", entry.display(), e),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let project_root = entry.parent().ok_or_else(|| CranelispError::ModuleError {
        message: "entry file has no parent directory".to_string(),
        file: Some(entry.clone()),
        span: Span::SYNTHETIC,
    })?.to_path_buf();

    // Derive module name from entry file stem.
    let entry_stem = entry
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| CranelispError::ModuleError {
            message: "entry file has no valid stem".to_string(),
            file: Some(entry.clone()),
            span: Span::SYNTHETIC,
        })?;
    let entry_path = ModuleFullPath::from(entry_stem);

    let mut graph = ModuleGraph {
        nodes: HashMap::new(),
        entry: entry_path.clone(),
        project_root: project_root.clone(),
        lib_dirs: lib_dirs.to_vec(),
    };

    // BFS/DFS discovery with cycle detection.
    let mut visiting: Vec<ModuleFullPath> = Vec::new();
    discover_module_recursive(
        &entry_path,
        &entry,
        &project_root,
        &graph.lib_dirs,
        &mut graph.nodes,
        &mut visiting,
    )?;

    Ok(graph)
}

/// Recursively discover a module and its submodules.
///
/// `visiting` tracks the current discovery path for cycle detection.
fn discover_module_recursive(
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
    // Cycle detection: if we're already visiting this module, we have a cycle.
    if visiting.contains(module_path) {
        let cycle_start = visiting.iter().position(|p| p == module_path).unwrap_or(0);
        let cycle: Vec<String> = visiting[cycle_start..]
            .iter()
            .map(|p| p.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!(
                "circular module dependency: {} -> {}",
                cycle.join(" -> "),
                module_path
            ),
            file: Some(file_path.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }

    // Already discovered (not a cycle, just already processed).
    if nodes.contains_key(module_path) {
        return Ok(());
    }

    visiting.push(module_path.clone());

    // Parse the file to extract module declarations.
    let source = std::fs::read_to_string(file_path).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot read '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;

    let sexps = cranelisp_frontend::parse(&source).map_err(|e| CranelispError::ModuleError {
        message: format!("parse error in '{}': {}", file_path.display(), e),
        file: Some(file_path.to_path_buf()),
        span: e.span(),
    })?;

    let (structure, _remaining) = cranelisp_frontend::extract_module_declarations(
        module_path.clone(),
        Some(file_path.to_path_buf()),
        sexps,
    )?;

    // Resolve submodule file paths and recurse.
    let mut dependencies = Vec::new();

    for mod_decl in &structure.mod_decls {
        // Handle inline submodules: they would need file extraction first.
        // For now, we only support file-based submodules.
        if mod_decl.inline_body.is_some() {
            // TODO: Extract inline module body to a file per spec section 8.2.2.
            // For now, skip inline modules — they need file creation before discovery.
            continue;
        }

        let submod_name = &mod_decl.name;

        // Build the child module's full path.
        let child_path = if module_path.0.is_empty() {
            ModuleFullPath::from(submod_name.as_ref())
        } else {
            ModuleFullPath::from(format!("{}.{}", module_path, submod_name))
        };

        // Resolve file per spec section 8.2.5:
        // 1. Child directory: {parent_dir}/{stem}/{name}.cl
        // 2. Sibling file: {parent_dir}/{name}.cl
        let resolved = resolve_submodule_file(
            file_path,
            submod_name.as_ref(),
            project_root,
            lib_dirs,
        )?;

        dependencies.push(child_path.clone());

        // Recurse into the submodule.
        discover_module_recursive(
            &child_path,
            &resolved,
            project_root,
            lib_dirs,
            nodes,
            visiting,
        )?;
    }

    // Also discover modules referenced by import specs (spec §8.10.1).
    // Import paths may reference modules not declared via (mod ...).
    discover_import_dependencies(
        &structure,
        module_path,
        file_path,
        project_root,
        lib_dirs,
        nodes,
        visiting,
        &mut dependencies,
    )?;

    // Register this module in the graph.
    nodes.insert(
        module_path.clone(),
        ModuleNode {
            path: module_path.clone(),
            file_path: file_path.to_path_buf(),
            dependencies,
        },
    );

    visiting.pop();
    Ok(())
}

/// Synthetic modules seeded by the compiler (no corresponding files).
const SYNTHETIC_MODULES: &[&str] = &["primitives", "macros"];

/// Discover modules referenced by import and export specs that aren't already in the graph.
///
/// Import and export specs reference modules by their full dotted path (e.g., "util",
/// "core.option"). This function resolves the root module name and discovers
/// it if not already known. Synthetic modules (`primitives`, `macros`) and
/// `super` references are skipped — they have no files.
///
/// Export specs are included in discovery so that re-export-only modules
/// (like the prelude) can reference root-level domain modules without
/// needing separate import declarations.
#[allow(clippy::too_many_arguments)] // Module graph discovery needs full context
fn discover_import_dependencies(
    structure: &ModuleStructure,
    module_path: &ModuleFullPath,
    file_path: &Path,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    nodes: &mut HashMap<ModuleFullPath, ModuleNode>,
    visiting: &mut Vec<ModuleFullPath>,
    dependencies: &mut Vec<ModuleFullPath>,
) -> Result<(), CranelispError> {
    // Discover modules referenced by import and export specs.
    // Both are included so that re-export-only modules (like the prelude)
    // trigger discovery of their referenced domain modules.
    let all_module_paths = structure
        .import_specs
        .iter()
        .map(|s| &s.module_path)
        .chain(structure.export_specs.iter().map(|s| &s.module_path));
    for ref_module_path in all_module_paths {
        let ref_path: &str = ref_module_path.as_ref();

        // Skip synthetic modules — they are compiler-seeded with no files.
        if is_synthetic_or_special(ref_path) {
            continue;
        }

        // Extract the root module name (first component before any dot).
        // E.g., "core.option" -> "core", "util" -> "util".
        let root_name = ref_path.split('.').next().unwrap_or(ref_path);

        // The path may be relative (bare name) or prefixed with the
        // current module path (e.g., "main.util" when current is "main").
        // Check both the bare path and a child-qualified version.
        let candidate_path = if module_path.0.is_empty() {
            ModuleFullPath::from(root_name)
        } else {
            // Check if the path already starts with the module path prefix.
            let mod_prefix = format!("{}.", module_path);
            if ref_path.starts_with(&mod_prefix) {
                // Already fully qualified relative to this module — use as-is.
                ref_module_path.clone()
            } else {
                // Bare name — resolve as a root-level module.
                ModuleFullPath::from(root_name)
            }
        };

        // Always record the dependency edge (even if the module was already
        // discovered by another path). Without this, the toposort may place
        // the depended-on module AFTER the dependent module.
        if dependencies.contains(&candidate_path) {
            // Already in this module's dependency list — skip.
            continue;
        }

        if nodes.contains_key(&candidate_path) {
            // Module already discovered by another path — record the
            // dependency edge but don't re-discover.
            dependencies.push(candidate_path.clone());
            continue;
        }

        // Try to resolve the module file.
        let resolved = match resolve_submodule_file(
            file_path,
            root_name,
            project_root,
            lib_dirs,
        ) {
            Ok(path) => path,
            Err(_) => {
                // Module file not found — it might be compiled later or be
                // a qualified reference to an already-loaded module. Skip
                // silently; the typechecker will produce a proper error if
                // the import cannot be resolved.
                continue;
            }
        };

        dependencies.push(candidate_path.clone());

        // Recurse into the discovered module.
        discover_module_recursive(
            &candidate_path,
            &resolved,
            project_root,
            lib_dirs,
            nodes,
            visiting,
        )?;
    }

    Ok(())
}

/// Check if a module path refers to a synthetic or special module.
///
/// Synthetic modules (`primitives`, `macros`) are compiler-seeded.
/// `super` is a relative reference to the parent module.
/// `prelude` is loaded separately via `load_prelude`.
fn is_synthetic_or_special(module_path: &str) -> bool {
    let root = module_path.split('.').next().unwrap_or(module_path);
    SYNTHETIC_MODULES.contains(&root) || root == "super" || root == "prelude"
}

/// Resolve a submodule's file path per spec section 8.2.5 and 8.11.2.
///
/// Search order:
/// 1. Child directory: `{parent_dir}/{stem}/{name}.cl`
/// 2. Sibling file: `{parent_dir}/{name}.cl`
/// 3. Project root: `{project_root}/{name}.cl`
/// 4. Lib directories: `{lib_dir}/{name}.cl` (each dir in order)
fn resolve_submodule_file(
    parent_file: &Path,
    name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Result<PathBuf, CranelispError> {
    let parent_dir = parent_file.parent().unwrap_or(Path::new("."));
    let stem = parent_file
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("");

    let filename = format!("{name}.cl");

    // 1. Child directory: {parent_dir}/{stem}/{name}.cl
    let child = parent_dir.join(stem).join(&filename);
    if child.is_file() {
        return Ok(child);
    }

    // 2. Sibling file: {parent_dir}/{name}.cl
    let sibling = parent_dir.join(&filename);
    if sibling.is_file() {
        return Ok(sibling);
    }

    // 3. Project root: {project_root}/{name}.cl (if different from parent_dir)
    if parent_dir != project_root {
        let root_file = project_root.join(&filename);
        if root_file.is_file() {
            return Ok(root_file);
        }
    }

    // 4. Lib directories: {lib_dir}/{name}.cl (each dir in order)
    for lib_dir in lib_dirs {
        let lib_file = lib_dir.join(&filename);
        if lib_file.is_file() {
            return Ok(lib_file);
        }
    }

    Err(CranelispError::ModuleError {
        message: format!(
            "cannot find module '{}' (searched child dir '{}/{}/', sibling '{}/{}', \
             project root, and lib directories)",
            name, parent_dir.display(), stem, parent_dir.display(), filename
        ),
        file: Some(parent_file.to_path_buf()),
        span: Span::SYNTHETIC,
    })
}

/// Topological sort of the module graph using Kahn's algorithm.
///
/// Returns modules in compilation order: leaves (no dependencies) first,
/// entry module last.
pub fn toposort(graph: &ModuleGraph) -> Result<Vec<ModuleFullPath>, CranelispError> {
    // Build in-degree map.
    let mut in_degree: HashMap<ModuleFullPath, usize> = HashMap::new();
    let mut adj: HashMap<ModuleFullPath, Vec<ModuleFullPath>> = HashMap::new();

    for (path, node) in &graph.nodes {
        in_degree.entry(path.clone()).or_insert(0);
        for dep in &node.dependencies {
            // dep -> path: if dep is a dependency, it must be compiled before path.
            // So path has an incoming edge from dep.
            adj.entry(dep.clone()).or_default().push(path.clone());
            *in_degree.entry(path.clone()).or_insert(0) += 1;
        }
    }

    // Seed queue with zero in-degree nodes.
    let mut queue: VecDeque<ModuleFullPath> = in_degree
        .iter()
        .filter(|(_, deg)| **deg == 0)
        .map(|(path, _)| path.clone())
        .collect();

    let mut sorted = Vec::with_capacity(graph.nodes.len());

    while let Some(current) = queue.pop_front() {
        sorted.push(current.clone());

        if let Some(dependents) = adj.get(&current) {
            for dependent in dependents {
                if let Some(deg) = in_degree.get_mut(dependent) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(dependent.clone());
                    }
                }
            }
        }
    }

    if sorted.len() != graph.nodes.len() {
        // Remaining nodes form a cycle (should have been caught earlier, but guard here).
        let remaining: Vec<String> = graph
            .nodes
            .keys()
            .filter(|k| !sorted.iter().any(|s| s == *k))
            .map(|k| k.to_string())
            .collect();
        return Err(CranelispError::ModuleError {
            message: format!("circular dependency among modules: {}", remaining.join(", ")),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    Ok(sorted)
}

/// Parse source and extract module declarations (imports/exports/mods).
///
/// Phase 1 of module compilation: no TypeChecker interaction. Returns the
/// Collected defns with slot assignments for `.o` compilation.
pub(crate) struct CollectedDefns {
    defns: Vec<(Defn, cranelisp_types::Scheme)>,
    fn_slot_assignments: HashMap<Symbol, cache::object::FnSlotInfo>,
    next_slot: usize,
}

/// Collect defns (functions, trait methods, mono specializations, default methods)
/// from a program and check result, assigning GOT slots to each.
pub(crate) fn collect_defns_for_cache(
    program: Option<&Program>,
    check: Option<&CheckResult>,
) -> CollectedDefns {
    use cranelisp_types::TopLevel;

    let mut defns: Vec<(Defn, cranelisp_types::Scheme)> = Vec::new();
    let mut fn_slot_assignments: HashMap<Symbol, cache::object::FnSlotInfo> = HashMap::new();
    let mut next_slot: usize = 0;

    let Some(prog) = program else {
        return CollectedDefns { defns, fn_slot_assignments, next_slot };
    };

    for tl in prog.iter() {
        if let TopLevel::Defn(defn) = tl {
            // Skip constrained fn base definitions.
            if let Some(ch) = check
                && ch.constrained_fn_names.contains(&defn.name)
            {
                continue;
            }
            let scheme = scheme_for_defn(defn, check);
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: defn.params().len(),
                },
            );
            defns.push((defn.clone(), scheme));
        }
        // TraitImpl methods have unmangled names (e.g., "+"). The mangled
        // versions ("Num.+$Int") are in check.default_method_defns and are
        // collected below. Skipping TraitImpl here avoids DuplicateDefinition
        // errors in the object compilation path.
    }

    // Also include monomorphised specializations and default methods.
    if let Some(ch) = check {
        for mono in &ch.mono_defns {
            let scheme = scheme_for_defn(&mono.defn, Some(ch));
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                mono.defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: mono.defn.params().len(),
                },
            );
            defns.push((mono.defn.clone(), scheme));
        }
        for defn in &ch.default_method_defns {
            let scheme = scheme_for_defn(defn, Some(ch));
            let slot = next_slot;
            next_slot += 1;
            fn_slot_assignments.insert(
                defn.name.clone(),
                cache::object::FnSlotInfo {
                    slot,
                    param_count: defn.params().len(),
                },
            );
            defns.push((defn.clone(), scheme));
        }
    }

    CollectedDefns { defns, fn_slot_assignments, next_slot }
}

/// Build a `Scheme` for a defn using real types from the `CheckResult`.
///
/// The typechecker records the full `Type::Fn(params, ret)` at `defn.span`
/// in `expr_types`. This function looks it up to get precise parameter and
/// return types. Falls back to `Type::Int` placeholder if the type is not
/// recorded (e.g., when `check` is `None`).
pub(crate) fn scheme_for_defn(defn: &Defn, check: Option<&CheckResult>) -> cranelisp_types::Scheme {
    let ty = check
        .and_then(|ch| ch.expr_types.get(&defn.span))
        .cloned()
        .unwrap_or_else(|| {
            // Fallback: construct a placeholder Fn type.
            Type::Fn(
                defn.params().iter().map(|_| Type::Int).collect(),
                Box::new(Type::Int),
            )
        });
    cranelisp_types::Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

/// Collected cross-module function references for `.o` import declarations.
pub(crate) struct CrossModuleRefs {
    fn_to_module: HashMap<Symbol, ModuleFullPath>,
    cross_module_fns: Vec<(Symbol, usize)>,
}

/// Map external function references to their source modules and collect
/// cross-module function signatures for ObjectModule import declarations.
///
/// Prior `func_sigs` entries represent functions from earlier modules
/// that this module might call.
pub(crate) fn collect_cross_module_refs(
    func_sigs: &[(Symbol, usize)],
) -> CrossModuleRefs {
    let mut fn_to_module: HashMap<Symbol, ModuleFullPath> = HashMap::new();
    let mut cross_module_fns: Vec<(Symbol, usize)> = Vec::new();

    for (name, param_count) in func_sigs {
        // Extract module path from qualified names (e.g., "core.num/+" -> "core.num").
        if let Some(slash) = name.as_ref().find('/') {
            let mod_part = &name.as_ref()[..slash];
            fn_to_module.insert(name.clone(), ModuleFullPath::from(mod_part));
        }
        // Include all prior functions as potential cross-module references.
        // The ObjectModule compiler uses these to declare imports so the linker
        // can resolve cross-module calls (both qualified and bare imported names).
        cross_module_fns.push((name.clone(), *param_count));
    }

    CrossModuleRefs { fn_to_module, cross_module_fns }
}

/// Build `ObjectCompileInput` for `.o` file compilation.
///
/// Collects defns with their inferred schemes from the program and check
/// result, builds the intrinsic table, and assembles fn_slot_assignments
/// and fn_to_module maps.
pub(crate) fn build_object_compile_input(
    module_path: &ModuleFullPath,
    program: Option<&Program>,
    check: Option<&CheckResult>,
    func_sigs: &[(Symbol, usize)],
) -> cache::ObjectCompileInput {
    let collected = collect_defns_for_cache(program, check);
    let cross_refs = collect_cross_module_refs(func_sigs);
    let intrinsics = build_intrinsic_table();

    cache::ObjectCompileInput {
        module_path: module_path.clone(),
        defns: collected.defns,
        method_resolutions: check
            .map(|ch| ch.method_resolutions.clone())
            .unwrap_or_default(),
        fn_slot_assignments: collected.fn_slot_assignments,
        fn_to_module: cross_refs.fn_to_module,
        intrinsics,
        type_defs: check
            .map(|ch| ch.type_defs.clone())
            .unwrap_or_default(),
        constructor_to_type: check
            .map(|ch| ch.constructor_to_type.clone())
            .unwrap_or_default(),
        expr_types: check
            .map(|ch| ch.expr_types.clone())
            .unwrap_or_default(),
        next_got_slot: collected.next_slot,
        cross_module_fns: cross_refs.cross_module_fns,
    }
}

/// Build the `IntrinsicTable` listing all runtime and primitive functions
/// that compiled code may reference.
///
/// Delegates to `cranelisp_backend::jit::intrinsic_symbols()` — the single
/// source of truth for intrinsic name/pointer/param-count mappings.
pub(crate) fn build_intrinsic_table() -> cache::IntrinsicTable {
    let mut table = cache::IntrinsicTable::new();

    for sym in cranelisp_backend::jit::intrinsic_symbols() {
        let entry = cache::IntrinsicEntry {
            user_name: Symbol::from(sym.name),
            jit_name: sym.name.to_string(),
            param_count: sym.param_count,
        };
        if sym.is_runtime {
            table.runtime_fns.push(entry);
        } else {
            table.primitive_fns.push(entry);
        }
    }

    table
}

/// Assemble the list of library directories for module resolution.
///
/// Per spec section 8.11.2, lib directory locations are specified by:
/// 1. `CRANELISP_LIB` environment variable (colon-separated list of paths)
/// 2. Fallback: `{project_root}/stdlib/` if it exists and `CRANELISP_LIB` is not set
///
/// When `CRANELISP_LIB` is set (even to empty), the fallback is NOT used — the
/// env var takes full control of the library search path.
///
// NOTE: spec/08-modules.md §8.11 says lib dirs come from (1) Cranelisp.toml
// project config and (2) CRANELISP_LIB env var. Cranelisp.toml is Ring 4 scope.
// Current implementation (CRANELISP_LIB → stdlib/ fallback) is correct for
// Ring 0–3. The stdlib/ fallback is a practical default, not spec-mandated.
// Ring 4 will add Cranelisp.toml support.
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

/// Inject an implicit `(import [prelude [*]])` into the typechecker's current
/// module, unless the current module IS "prelude" (to avoid self-import).
///
/// Per spec §8.8.1, all non-prelude modules receive this implicit import so
/// that prelude-defined traits and macros are available without explicit import.
pub(crate) fn inject_prelude_import(
    tc: &mut cranelisp_typecheck::TypeChecker,
) -> Result<(), CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");

    // Don't self-import prelude into itself.
    if tc.current_module_path() == &prelude_path {
        return Ok(());
    }

    // Register the implicit glob import. Duplicate same-source imports are
    // silently deduplicated by insert_imports_detecting_ambiguity, so this
    // is safe to call even if the module already has a prelude import
    // (e.g., "user" which received one from load_prelude).
    let import_spec = cranelisp_types::ImportSpec {
        module_path: prelude_path,
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    tc.register_imports(&[import_spec])
}

/// Determine the process exit code from the already-unwrapped inner value.
///
/// The caller is responsible for extracting the inner value from any IO wrapper
/// (via the trampoline) before calling this function. This function receives
/// the unwrapped inner type, not the IO-wrapped type.
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

/// Compile a multi-file module graph via the v2 pipeline and execute main.
///
/// Used by tests and callers that do not need caching.
/// Discovers module graph, compiles each module via `compile_unit`,
/// then executes the entry module's `main` function.
pub fn compile_module_graph(
    entry: &Path,
    lib_dirs: &[PathBuf],
) -> Result<CompiledModuleGraph, CranelispError> {
    compile_module_graph_cached(entry, lib_dirs, &CacheConfig::Disabled)
}

/// Compile a multi-file module graph via the v2 pipeline and execute main.
///
/// Pipeline:
/// 1. Discover module graph from entry file
/// 2. Topological sort (dependencies first)
/// 3. For each module: read source, compile via `compile_unit` (which
///    handles prelude loading, platform DLLs, imports/exports internally),
///    flush in-memory codegen
/// 4. Execute the entry module's `main` function
///
/// The `cache_config` parameter controls module caching. When enabled,
/// the session uses `.cranelisp-cache/` for cached .o files and metadata.
pub fn compile_module_graph_cached(
    entry: &Path,
    lib_dirs: &[PathBuf],
    cache_config: &CacheConfig,
) -> Result<CompiledModuleGraph, CranelispError> {
    let graph = discover_module_graph(entry, lib_dirs)?;
    let order = toposort(&graph)?;

    let mut all_warnings: Vec<Warning> = Vec::new();
    let mut session = match cache_config.cache_dir() {
        Some(dir) => {
            let _ = std::fs::create_dir_all(dir);
            CompilationSession::new_with_cache(dir.to_path_buf())
        }
        None => CompilationSession::new(),
    };
    session.interactive = true;

    // Set up lib_dirs: entry file's parent dir + provided lib_dirs.
    let entry_dir = entry
        .canonicalize()
        .ok()
        .and_then(|p| p.parent().map(|d| d.to_path_buf()));
    let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(dir) = &entry_dir {
        all_lib_dirs.push(dir.clone());
    }
    all_lib_dirs.extend(lib_dirs.iter().cloned());
    session.lib_dirs = all_lib_dirs;
    session.project_root = entry_dir.unwrap_or_else(|| PathBuf::from("."));

    // Compile each module in topological order via compile_unit.
    // The entry module is last in topo order (dependencies come first).
    let mut entry_codegen: Option<crate::pipeline_v2::CodegenResult> = None;
    for module_path in &order {
        let node = &graph.nodes[module_path];
        let source = std::fs::read_to_string(&node.file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read '{}': {}", node.file_path.display(), e),
                file: Some(node.file_path.clone()),
                span: Span::SYNTHETIC,
            }
        })?;

        let ctx = CompileContext {
            module: module_path.clone(),
            strategy: ModuleStrategy::Additive,
            codegen_target: cranelisp_types::CodegenTarget::JitAndCache,
        };

        let source_hash = cache::hash_source(&source);
        let unit_result = crate::pipeline_v2::compile_unit(&mut session, &source, &ctx)?;
        all_warnings.extend(unit_result.warnings.clone());
        session.inmem_queue.push(crate::pipeline_v2::CodegenItem {
            ctx,
            unit_result,
        });
        let mut codegen_results = session.flush_inmem_queue()?;
        if module_path == &graph.entry {
            entry_codegen = codegen_results.pop();
        }
        for codegen_result in codegen_results {
            all_warnings.extend(codegen_result.warnings);
        }

        // Update cache manifest for this module (source hash + dependency hashes).
        if let Some(cs) = session.object_worker.cache_state.as_mut() {
            let node = &graph.nodes[module_path];
            let dep_hashes: HashMap<String, String> = node
                .dependencies
                .iter()
                .filter_map(|dep| {
                    cs.source_hashes
                        .get(dep)
                        .map(|h| (dep.0.clone(), h.clone()))
                })
                .collect();
            cs.record_module(module_path, source_hash, dep_hashes);
        }
    }

    // Flush background .o writes and cache manifest.
    session.flush_cache_writes();
    if let Some(cs) = &session.object_worker.cache_state {
        let _ = cs.flush();
    }

    // Extract value and type from the entry module's compilation.
    let entry_result = entry_codegen.ok_or_else(|| CranelispError::ModuleError {
        message: "entry module produced no codegen result".into(),
        file: Some(entry.to_path_buf()),
        span: Span::SYNTHETIC,
    })?;
    all_warnings.extend(entry_result.warnings);

    // Verify main exists in the GOT.
    let main_sym = Symbol::from("main");
    let qualified_main = Symbol::from(format!("{}/main", graph.entry.as_ref()));
    let got = &session.inmem_worker.got_state;
    let main_exists = got.def_codegen.contains_key(&main_sym)
        || got.def_codegen.contains_key(&qualified_main);
    if !main_exists {
        return Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)".into(),
            file: Some(entry.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }

    let raw_value = entry_result.value.unwrap_or(0);
    let result_type = entry_result.result_type.unwrap_or(Type::Int);

    let (value, ty) = if result_type.is_io() {
        let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
        let inner_type = result_type.io_inner_type();
        (inner_value, inner_type)
    } else {
        (raw_value, result_type)
    };

    Ok(CompiledModuleGraph {
        value,
        ty,
        warnings: all_warnings,
    })
}

/// Generate all module-qualified alias names for a function.
///
/// For module path "main.mid.leaf" and function "value", produces:
///   - "mid.leaf/value" (each dot-suffix)
///   - "main.mid.leaf/value" (full path, only for dotted modules)
///   - "leaf/value" (last component, if different from bare name)
///
/// Used by `register_module_aliases` (GOT), `load_cached_object_into_session`
/// (cached symbols), and `accumulate_func_sigs` (batch JIT).
fn generate_module_aliases(mod_str: &str, fn_name: &str) -> Vec<String> {
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

/// Check whether a program has any defns or trait impls that need codegen.
pub(crate) fn has_compilable_defns(program: &[cranelisp_types::TopLevel]) -> bool {
    use cranelisp_types::TopLevel;
    program.iter().any(|tl| matches!(tl, TopLevel::Defn(_) | TopLevel::TraitImpl(_)))
}

// ---------------------------------------------------------------------------
// Bind chain independence analysis integration
// ---------------------------------------------------------------------------

/// Apply bind chain independence analysis to all defn bodies in a program.
///
/// Transforms eligible bind chains into `Expr::ParBind` nodes for automatic
/// IO scheduling. Only called when the scheduling registry is non-empty
/// (i.e., platform DLLs have been loaded) and `CRANELISP_NO_IO_SCHEDULE`
/// is not set.
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
            // TraitImpl methods are also defns — transform their bodies too.
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

    // --- IO type detection (now on Type methods, tested in cranelisp-types) ---

    // spec: 10-io §10.6.1 — determine_exit_code for Int result
    #[test]
    fn test_determine_exit_code_int() {
        assert_eq!(determine_exit_code(0, &Type::Int), 0);
        assert_eq!(determine_exit_code(42, &Type::Int), 42);
        assert_eq!(determine_exit_code(1, &Type::Int), 1);
    }

    // spec: 10-io §10.6.1 — determine_exit_code for non-Int result
    #[test]
    fn test_determine_exit_code_non_int() {
        assert_eq!(determine_exit_code(42, &Type::String), 0);
        assert_eq!(determine_exit_code(42, &Type::Bool), 0);
    }

    // --- Single-file pipeline tests (existing) ---

    #[test]
    fn test_pipeline_simple_int() {
        let result = compile_and_run("(defn main [] 42)").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_pipeline_bool_true() {
        let result = compile_and_run("(defn main [] true)").unwrap();
        assert_eq!(result.value, 1);
        assert_eq!(result.ty, Type::Bool);
    }

    #[test]
    fn test_pipeline_parse_error() {
        let result = compile_and_run("(defn main [] ");
        assert!(result.is_err());
    }

    #[test]
    fn test_pipeline_returns_correct_value() {
        // Previously tested CompileMode::Interactive; after CompileMode removal
        // compile_and_run always uses batch codegen (direct calls, no GOT).
        let result = compile_and_run("(defn main [] 42)").unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Module graph discovery tests ---

    #[test]
    fn test_discover_single_file() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 1);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert_eq!(graph.entry, ModuleFullPath::from("main"));
    }

    #[test]
    fn test_discover_with_submodule() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod util)\n(defn main [] 42)").unwrap();

        // Create sibling module file.
        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 1)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.util")));
    }

    #[test]
    fn test_discover_child_directory_priority() {
        // Per spec 8.2.5: child directory is searched before sibling.
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("app.cl");
        std::fs::write(&entry, "(mod handler)").unwrap();

        // Create child directory version.
        let child_dir = dir.path().join("app");
        std::fs::create_dir_all(&child_dir).unwrap();
        std::fs::write(child_dir.join("handler.cl"), "(defn handle [] 1)").unwrap();

        // Also create sibling version (should be ignored).
        std::fs::write(dir.path().join("handler.cl"), "(defn handle [] 2)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        let handler_node = &graph.nodes[&ModuleFullPath::from("app.handler")];
        // Should resolve to child directory version.
        assert!(handler_node.file_path.to_str().unwrap().contains("app/handler.cl"));
    }

    #[test]
    fn test_discover_missing_module_error() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod nonexistent)").unwrap();

        let result = discover_module_graph(&entry, &[]);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message().contains("cannot find module 'nonexistent'"));
    }

    #[test]
    fn test_discover_circular_dependency() {
        let dir = tempfile::tempdir().unwrap();
        let a_file = dir.path().join("a.cl");
        let b_file = dir.path().join("b.cl");

        // a.cl declares mod b, b.cl declares mod a -> cycle.
        // But note: (mod b) in a.cl makes b a submodule of a,
        // and (mod a) in b.cl would look for a submodule of b, not create a cycle
        // in the same way. Let's create the actual cycle structure:
        let a_dir = dir.path().join("a");
        let b_dir = dir.path().join("b");
        std::fs::create_dir_all(&a_dir).unwrap();
        std::fs::create_dir_all(&b_dir).unwrap();

        std::fs::write(&a_file, "(mod b)").unwrap();
        // b is at a/b.cl and declares (mod a) which would look for a/b/a.cl
        // This doesn't create a true cycle as discovered because each path is unique.
        // To get a real cycle we need to be more creative.
        // Actually, cycles are caught in the toposort if they manage to form,
        // or in discover_module_recursive if the same ModuleFullPath is visited twice.
        // Let's test the toposort cycle detection instead.

        // Clean up and just test toposort cycle detection.
        let mut nodes = HashMap::new();
        nodes.insert(
            ModuleFullPath::from("a"),
            ModuleNode {
                path: ModuleFullPath::from("a"),
                file_path: a_file.clone(),
                dependencies: vec![ModuleFullPath::from("b")],
            },
        );
        nodes.insert(
            ModuleFullPath::from("b"),
            ModuleNode {
                path: ModuleFullPath::from("b"),
                file_path: b_file.clone(),
                dependencies: vec![ModuleFullPath::from("a")],
            },
        );
        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("a"),
            project_root: dir.path().to_path_buf(),
            lib_dirs: Vec::new(),
        };

        let result = toposort(&graph);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message().contains("circular dependency"));
    }

    #[test]
    fn test_toposort_order() {
        // c depends on nothing, b depends on c, a depends on b and c.
        let mut nodes = HashMap::new();
        nodes.insert(
            ModuleFullPath::from("a"),
            ModuleNode {
                path: ModuleFullPath::from("a"),
                file_path: PathBuf::from("a.cl"),
                dependencies: vec![
                    ModuleFullPath::from("b"),
                    ModuleFullPath::from("c"),
                ],
            },
        );
        nodes.insert(
            ModuleFullPath::from("b"),
            ModuleNode {
                path: ModuleFullPath::from("b"),
                file_path: PathBuf::from("b.cl"),
                dependencies: vec![ModuleFullPath::from("c")],
            },
        );
        nodes.insert(
            ModuleFullPath::from("c"),
            ModuleNode {
                path: ModuleFullPath::from("c"),
                file_path: PathBuf::from("c.cl"),
                dependencies: vec![],
            },
        );

        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("a"),
            project_root: PathBuf::from("."),
            lib_dirs: Vec::new(),
        };

        let order = toposort(&graph).unwrap();
        assert_eq!(order.len(), 3);

        // c must come before b, b must come before a.
        let pos_a = order.iter().position(|p| p == "a").unwrap();
        let pos_b = order.iter().position(|p| p == "b").unwrap();
        let pos_c = order.iter().position(|p| p == "c").unwrap();
        assert!(pos_c < pos_b);
        assert!(pos_b < pos_a);
    }

    #[test]
    fn test_toposort_single_node() {
        let mut nodes = HashMap::new();
        nodes.insert(
            ModuleFullPath::from("main"),
            ModuleNode {
                path: ModuleFullPath::from("main"),
                file_path: PathBuf::from("main.cl"),
                dependencies: vec![],
            },
        );

        let graph = ModuleGraph {
            nodes,
            entry: ModuleFullPath::from("main"),
            project_root: PathBuf::from("."),
            lib_dirs: Vec::new(),
        };

        let order = toposort(&graph).unwrap();
        assert_eq!(order, vec![ModuleFullPath::from("main")]);
    }

    // --- compile_module_graph tests ---

    #[test]
    fn test_compile_single_file_project() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_compile_file_not_found() {
        let result = compile_module_graph(Path::new("/nonexistent/path/main.cl"), &[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_sibling_module() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file that declares a submodule.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod util)\n(defn main [] 99)").unwrap();

        // Create the sibling module (util.cl).
        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 1)").unwrap();

        // Discovery should find both modules.
        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 2);

        // Toposort should put util before main.
        let order = toposort(&graph).unwrap();
        let pos_main = order.iter().position(|p| p == "main").unwrap();
        let pos_util = order.iter().position(|p| p == "main.util").unwrap();
        assert!(pos_util < pos_main);
    }

    #[test]
    fn test_resolve_lib_module() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] 1)").unwrap();

        // Create lib/ directory with the module.
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("helper.cl"), "(defn help [] 2)").unwrap();

        let graph = discover_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.helper")));
    }

    #[test]
    fn test_nested_submodules() {
        let dir = tempfile::tempdir().unwrap();

        // main.cl -> mod a -> a has mod b
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod a)\n(defn main [] 1)").unwrap();

        // a.cl (sibling of main.cl)
        let a_file = dir.path().join("a.cl");
        std::fs::write(&a_file, "(mod b)").unwrap();

        // a/b.cl (child directory of a)
        let a_dir = dir.path().join("a");
        std::fs::create_dir_all(&a_dir).unwrap();
        std::fs::write(a_dir.join("b.cl"), "(defn leaf [] 3)").unwrap();

        let graph = discover_module_graph(&entry, &[]).unwrap();
        assert_eq!(graph.nodes.len(), 3);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main")));
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.a")));
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.a.b")));

        // Toposort: b before a before main.
        let order = toposort(&graph).unwrap();
        let pos_main = order.iter().position(|p| p == "main").unwrap();
        let pos_a = order.iter().position(|p| p == "main.a").unwrap();
        let pos_b = order.iter().position(|p| p == "main.a.b").unwrap();
        assert!(pos_b < pos_a);
        assert!(pos_a < pos_main);
    }

    #[test]
    fn test_cross_module_import_resolution() {
        // This test documents the limitation that compile_module_graph
        // does not yet wire cross-module imports. When a module imports
        // a symbol from another module, the import is not resolved.
        //
        // To fix: after compiling each non-entry module, register its
        // exports so downstream modules can resolve imports against them.
        let dir = tempfile::tempdir().unwrap();

        let entry = dir.path().join("main.cl");
        std::fs::write(
            &entry,
            "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))",
        )
        .unwrap();

        let util_file = dir.path().join("util.cl");
        std::fs::write(&util_file, "(defn helper [] 42)").unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Macro integration tests ---

    // spec: 09-macros.md §9.2 — defmacro in batch pipeline
    #[test]
    fn test_batch_defmacro_identity() {
        // Define a macro and use it in the same file.
        let source = r#"
            (defmacro id [x] x)
            (defn main [] (id 42))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md §9.4.2 — quasiquote macro in batch pipeline
    #[test]
    fn test_batch_defmacro_quasiquote() {
        let source = r#"
            (defmacro inc1 [x] `(primitives/add-i64 1 ~x))
            (defn main [] (inc1 41))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md §9.2 — multiple macros, later uses earlier
    #[test]
    fn test_batch_macro_uses_earlier_macro() {
        let source = r#"
            (defmacro id [x] x)
            (defmacro id2 [x] (id x))
            (defn main [] (id2 99))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 99);
    }

    // spec: 09-macros.md §9.2.6 — multi-clause macro dispatch
    #[test]
    fn test_batch_multi_clause_macro() {
        let source = r#"
            (defmacro pick ([x] x) ([x y] x))
            (defn main [] (pick 77))
        "#;
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 77);
    }

    // spec: 09-macros.md — no macros: pipeline still works
    #[test]
    fn test_batch_no_macros_unchanged() {
        let source = "(defn main [] (primitives/add-i64 1 2))";
        let result = compile_and_run(source).unwrap();
        assert_eq!(result.value, 3);
    }

    // spec: 09-macros.md §9.2 — defmacro in module graph pipeline
    #[test]
    fn test_module_graph_defmacro() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(
            &entry,
            "(defmacro id [x] x)\n(defn main [] (id 42))",
        )
        .unwrap();

        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Prelude loading tests ---

    // spec: 08-modules.md — prelude loading from lib/
    #[test]
    fn test_prelude_loading_from_lib() {
        let dir = tempfile::tempdir().unwrap();

        // Create lib/prelude.cl with a simple macro.
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(
            stdlib_dir.join("prelude.cl"),
            "(defmacro id [x] x)",
        )
        .unwrap();

        // Entry file uses the macro from the prelude.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] (id 55))").unwrap();

        let result = compile_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        assert_eq!(result.value, 55);
    }

    // spec: 08-modules.md — system works without prelude
    #[test]
    fn test_no_prelude_still_works() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] 42)").unwrap();

        // No lib/ directory, no prelude.
        let result = compile_module_graph(&entry, &[]).unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 08-modules.md — prelude resolution: project root overrides lib/
    #[test]
    fn test_prelude_project_root_overrides_lib() {
        let dir = tempfile::tempdir().unwrap();

        // Create lib/prelude.cl with one macro.
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(
            stdlib_dir.join("prelude.cl"),
            "(defmacro id [x] `(add-i64 100 ~x))",
        )
        .unwrap();

        // Create project root prelude.cl with different behavior.
        std::fs::write(
            dir.path().join("prelude.cl"),
            "(defmacro id [x] x)",
        )
        .unwrap();

        // Entry file uses the macro — should get the project root version.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(defn main [] (id 42))").unwrap();

        let result = compile_module_graph(&entry, &[stdlib_dir.clone()]).unwrap();
        // Project root prelude: (id 42) -> 42
        // Lib prelude: (id 42) -> (add-i64 100 42) -> 142
        assert_eq!(result.value, 42);
    }

    // spec: 08-modules.md — resolve_prelude returns None when no prelude exists
    #[test]
    fn test_resolve_prelude_none() {
        let dir = tempfile::tempdir().unwrap();
        let result = resolve_prelude(dir.path(), &[]);
        assert!(result.is_none());
    }

    // spec: 08-modules.md — resolve_prelude finds lib/ prelude
    #[test]
    fn test_resolve_prelude_from_lib() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "").unwrap();

        let result = resolve_prelude(dir.path(), &[stdlib_dir.clone()]);
        assert!(result.is_some());
        assert!(result.unwrap().ends_with("prelude.cl"));
    }

    // spec: 08-modules.md — resolve_prelude prefers project root
    #[test]
    fn test_resolve_prelude_project_root_priority() {
        let dir = tempfile::tempdir().unwrap();
        let stdlib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&stdlib_dir).unwrap();
        std::fs::write(stdlib_dir.join("prelude.cl"), "").unwrap();
        std::fs::write(dir.path().join("prelude.cl"), "").unwrap();

        let result = resolve_prelude(dir.path(), &[stdlib_dir.clone()]);
        assert!(result.is_some());
        // Should be the project root version, not lib/.
        let path = result.unwrap();
        assert!(!path.to_str().unwrap().contains("lib"));
    }

    // --- assemble_lib_dirs tests ---

    // spec: 08-modules.md §8.11.2 — fallback to {project_root}/stdlib/
    #[test]
    fn test_assemble_lib_dirs_fallback_stdlib() {
        // When CRANELISP_LIB is not set, falls back to {project_root}/stdlib/.
        let dir = tempfile::tempdir().unwrap();
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        // Temporarily remove CRANELISP_LIB if it is set.
        // SAFETY: Test-only; env var manipulation is not thread-safe but
        // acceptable in unit tests.
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::remove_var("CRANELISP_LIB"); }

        let dirs = assemble_lib_dirs(dir.path());

        // Restore.
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        }

        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0], stdlib);
    }

    // spec: 08-modules.md §8.11.2 — no stdlib dir, no env var -> empty
    #[test]
    fn test_assemble_lib_dirs_empty_fallback() {
        let dir = tempfile::tempdir().unwrap();
        // No stdlib/ directory exists.

        // SAFETY: Test-only; env var manipulation is not thread-safe.
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::remove_var("CRANELISP_LIB"); }

        let dirs = assemble_lib_dirs(dir.path());

        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        }

        assert!(dirs.is_empty());
    }

    // spec: 08-modules.md §8.11.2 — CRANELISP_LIB overrides fallback
    #[test]
    fn test_assemble_lib_dirs_env_var() {
        let dir = tempfile::tempdir().unwrap();
        let lib_a = dir.path().join("lib_a");
        let lib_b = dir.path().join("lib_b");
        std::fs::create_dir_all(&lib_a).unwrap();
        std::fs::create_dir_all(&lib_b).unwrap();

        // Also create stdlib/ — should be IGNORED when CRANELISP_LIB is set.
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        // SAFETY: Test-only; env var manipulation is not thread-safe.
        let saved = std::env::var("CRANELISP_LIB").ok();
        let env_val = format!("{}:{}", lib_a.display(), lib_b.display());
        unsafe { std::env::set_var("CRANELISP_LIB", &env_val); }

        let dirs = assemble_lib_dirs(dir.path());

        // Restore.
        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        } else {
            unsafe { std::env::remove_var("CRANELISP_LIB"); }
        }

        assert_eq!(dirs.len(), 2);
        assert_eq!(dirs[0], lib_a);
        assert_eq!(dirs[1], lib_b);
    }

    // spec: 08-modules.md §8.11.2 — CRANELISP_LIB empty string -> no dirs
    #[test]
    fn test_assemble_lib_dirs_env_var_empty() {
        let dir = tempfile::tempdir().unwrap();
        // Create stdlib/ — should be IGNORED when CRANELISP_LIB is set (even empty).
        let stdlib = dir.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        // SAFETY: Test-only; env var manipulation is not thread-safe.
        let saved = std::env::var("CRANELISP_LIB").ok();
        unsafe { std::env::set_var("CRANELISP_LIB", ""); }

        let dirs = assemble_lib_dirs(dir.path());

        if let Some(val) = saved {
            unsafe { std::env::set_var("CRANELISP_LIB", val); }
        } else {
            unsafe { std::env::remove_var("CRANELISP_LIB"); }
        }

        assert!(dirs.is_empty());
    }

    // spec: 08-modules.md §8.11.2 — module found via CRANELISP_LIB
    #[test]
    fn test_module_resolution_via_cranelisp_lib() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] 1)").unwrap();

        // Create a separate lib directory with the module.
        let lib_dir = dir.path().join("mylibs");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(lib_dir.join("helper.cl"), "(defn help [] 2)").unwrap();

        // Pass lib_dir explicitly (same as what assemble_lib_dirs would produce).
        let graph = discover_module_graph(&entry, &[lib_dir]).unwrap();
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.nodes.contains_key(&ModuleFullPath::from("main.helper")));
    }

    // spec: 08-modules.md §8.11.2 — multiple lib dirs, first match wins
    #[test]
    fn test_multiple_lib_dirs_first_wins() {
        let dir = tempfile::tempdir().unwrap();

        // Create entry file that uses a macro from prelude.
        let entry = dir.path().join("main.cl");
        std::fs::write(&entry, "(mod helper)\n(defn main [] (helper/val))").unwrap();

        // Two lib directories with the same module name.
        let lib_first = dir.path().join("first");
        let lib_second = dir.path().join("second");
        std::fs::create_dir_all(&lib_first).unwrap();
        std::fs::create_dir_all(&lib_second).unwrap();
        std::fs::write(lib_first.join("helper.cl"), "(defn val [] 100)").unwrap();
        std::fs::write(lib_second.join("helper.cl"), "(defn val [] 200)").unwrap();

        // First lib dir should win.
        let result = compile_module_graph(&entry, &[lib_first, lib_second]).unwrap();
        assert_eq!(result.value, 100, "first lib dir should take precedence");
    }
}
