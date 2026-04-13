// Session: cache state and utility functions.
//
// This module provides:
// - CacheState: manifest tracking for .o caching
// - Utility functions: lib dirs, prelude resolution, exit code

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

/// Inject an implicit `(import [prelude [*]])` into the typechecker's current
/// module, unless the current module IS "prelude" (to avoid self-import).
pub(crate) fn inject_prelude_import(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut cranelisp_typecheck::CheckState,
    current_module: &ModuleFullPath,
) -> Result<(), CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");

    // Don't self-import prelude into itself.
    if *current_module == prelude_path {
        return Ok(());
    }

    let import_spec = cranelisp_types::ImportSpec {
        module_path: prelude_path,
        alias: None,
        names: cranelisp_types::ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    let tc = cranelisp_typecheck::TypeCheckEnv::new(symbol_tables, next_type_id);
    tc.register_imports(check_state, &[import_spec])
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
