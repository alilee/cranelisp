// Session: worker state types, cache state, and utility functions.
//
// This module provides the shared state types used by the v4 pipeline:
// - CacheState: manifest tracking for .o caching
// - InMemWorkerState: per-session GOT + JIT state
// - SharedCodegenState: concurrent GOT state for worker threads
// - WorkerJitState: per-worker JIT lifetime tracking
// - ObjectWorkerState: .o file generation state
// - Utility functions: lib dirs, prelude resolution, module aliases

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CranelispError, ModuleFullPath, Program, Span, Symbol,
    Type,
};

use cranelisp_backend::cache;

// ---------------------------------------------------------------------------
// Cache state
// ---------------------------------------------------------------------------

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
        cache::check_manifest(&self.manifest, module_path, current_source_hash, dep_hashes)
            .unwrap_or_default() // Global invalidation — treat as miss.
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
/// Fields used by codegen and the REPL for GOT-indirect compilation,
/// JIT module lifetime management, and trace instrumentation.
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

impl Default for InMemWorkerState {
    fn default() -> Self {
        InMemWorkerState {
            got_state: cranelisp_backend::got::ModuleCodegenState::new(),
            jit_modules: Vec::new(),
            traced_fns: Vec::new(),
            trace_extra_symbols: Vec::new(),
            cache_linkers: Vec::new(),
        }
    }
}

impl InMemWorkerState {
    pub fn new() -> Self {
        Self::default()
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
// SharedCodegenState — shared codegen state for concurrent workers
// ---------------------------------------------------------------------------

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
        if let Some(entry) = self.def_codegen.get(name)
            && let Some(slot) = entry.got_slot
        {
            return Ok(slot);
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
// WorkerJitState — per-worker JIT state
// ---------------------------------------------------------------------------

/// Per-worker JIT state. Stack-local in each priority worker thread.
///
/// Not shared across threads. Each worker accumulates JIT instances
/// and linkers during codegen, then drains them to SharedCodegenState
/// when the module is complete.
#[derive(Default)]
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
        Self::default()
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
/// Fields used for background .o emission and manifest tracking.
#[derive(Default)]
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
    pub compiled_module_structures: Vec<(ModuleFullPath, cranelisp_types::ModuleStructure)>,
    /// Cumulative cross-module function signatures for .o generation.
    /// Each entry is (qualified_name, param_count). Extended after each
    /// module completes stage 6. Used as `ObjectCompileInput.cross_module_fns`
    /// for subsequent modules.
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,
}

impl ObjectWorkerState {
    pub fn new() -> Self {
        Self::default()
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
// Free functions: GOT alias registration
// ---------------------------------------------------------------------------

/// Register module-qualified aliases for functions defined in the current module.
///
/// If `pre_existing` is Some, only alias entries NOT present in the set (new entries).
/// If `pre_existing` is None, alias ALL entries (backward compat for REPL single-form eval).
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
            dc.got_slot.map(|slot| (name.clone(), slot, dc.param_count))
        })
        .collect();

    for (name, slot, param_count) in entries {
        if let Some(pre) = pre_existing {
            if pre.contains(&name) {
                continue;
            }
        }

        let code_ptr = inmem_worker.got_state.shared_got().load_slot(slot);
        let pc = param_count.unwrap_or(0);

        for alias in generate_module_aliases(mod_str, name.as_ref()) {
            let qualified = Symbol::from(alias);
            register_got_alias(inmem_worker, &qualified, slot, code_ptr, pc);
        }
    }
}

fn register_got_alias(
    inmem_worker: &mut InMemWorkerState,
    qualified: &Symbol,
    slot: usize,
    code_ptr: *const u8,
    param_count: usize,
) {
    let entry = inmem_worker.got_state.def_codegen.entry(qualified.clone()).or_default();
    entry.got_slot = Some(slot);
    entry.code_ptr = Some(code_ptr);
    entry.param_count = Some(param_count);
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

/// Assemble extra platform DLL search directories (§8.11.5 tier 3).
///
/// Sources, in order:
/// 1. `CRANELISP_PLATFORM_PATH` environment variable (colon-separated).
///
/// Project-root and lib-dir platform subdirectories (tiers 1-2) are handled
/// by `resolve_platform_path` directly — they don't need to be in this list.
pub fn assemble_platform_dirs() -> Vec<PathBuf> {
    if let Ok(env_val) = std::env::var("CRANELISP_PLATFORM_PATH") {
        return env_val
            .split(':')
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .collect();
    }
    Vec::new()
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
