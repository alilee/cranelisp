// Session: cache state and utility functions.
//
// This module provides:
// - CacheState: manifest tracking for .o caching
// - Utility functions: lib dirs, prelude resolution, exit code

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CranelispError, ModuleFullPath, Program, Span,
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

/// Project configuration file schema (Sprint 58 Wave 4 Step 5d (iii)).
///
/// Read from `{project_root}/Cranelisp.toml` by `load_project_config_lib_dirs`.
/// All fields are optional; absent fields default to empty values per
/// `serde(default)`.
///
/// See `design/int/cranelisp-toml.md` for the schema rationale.
#[derive(Debug, Clone, Default, serde::Deserialize)]
struct ProjectConfig {
    /// Lib directory list. Paths are relative to the project root or
    /// absolute. When `Cranelisp.toml` is present, the resolved list
    /// fully replaces the env/default tiers per spec §8.11.4 item 2.
    #[serde(default, rename = "lib-dirs")]
    lib_dirs: Vec<PathBuf>,
}

/// Read `{project_root}/Cranelisp.toml` and return its `lib-dirs` resolved
/// against `project_root`.
///
/// Returns:
/// - `Ok(None)` if the file does not exist (callers fall through to env/default tiers).
/// - `Ok(Some(dirs))` if the file is present and parsed successfully (may be empty).
/// - `Err(...)` if the file exists but is unreadable or malformed (caller surfaces).
///
/// Path resolution: relative paths are joined onto `project_root`; absolute
/// paths are used unchanged. No tilde expansion (spec hand-edit format).
///
/// Spec: 08-modules.md §8.11.4 item 2.
pub fn load_project_config_lib_dirs(
    project_root: &Path,
) -> Result<Option<Vec<PathBuf>>, CranelispError> {
    let candidate = project_root.join("Cranelisp.toml");
    if !candidate.is_file() {
        return Ok(None);
    }
    let contents = std::fs::read_to_string(&candidate).map_err(|e| {
        CranelispError::ModuleError {
            message: format!(
                "cannot read project config '{}': {}",
                candidate.display(),
                e
            ),
            file: Some(candidate.clone()),
            span: Span::SYNTHETIC,
        }
    })?;
    let config: ProjectConfig = toml::from_str(&contents).map_err(|e| {
        CranelispError::ModuleError {
            message: format!(
                "malformed project config '{}': {} (spec §8.11.4)",
                candidate.display(),
                e
            ),
            file: Some(candidate.clone()),
            span: Span::SYNTHETIC,
        }
    })?;
    let resolved: Vec<PathBuf> = config
        .lib_dirs
        .iter()
        .map(|p| {
            if p.is_absolute() {
                p.clone()
            } else {
                project_root.join(p)
            }
        })
        .collect();
    Ok(Some(resolved))
}

/// Assemble the list of library directories for module resolution.
///
/// Per spec section 8.11.4, lib directory locations are assembled from
/// (in precedence order; first hit fully controls):
/// 1. **Project configuration file** (`Cranelisp.toml`): when present,
///    its `lib-dirs` fully replaces the lower tiers. Spec §8.11.4 item 2.
/// 2. `CRANELISP_LIB` environment variable (colon-separated list of paths).
///    Spec §8.11.4 item 3.
/// 3. Fallback: `{project_root}/stdlib/` if it exists. Spec §8.11.4 item 4.
///
/// Tier 1 (explicit programmatic additions) is layered on top by callers
/// via `SharedState.lib_dirs` setters; this function returns the
/// configuration-derived baseline only.
///
/// On project-config parse error: returns the env/default tiers and
/// silently ignores the malformed file. Callers that want the parse
/// error surfaced should call `load_project_config_lib_dirs` directly.
pub fn assemble_lib_dirs(project_root: &Path) -> Vec<PathBuf> {
    // Tier 2 (highest non-programmatic): project config file.
    if let Ok(Some(dirs)) = load_project_config_lib_dirs(project_root) {
        return dirs;
    }

    // Tier 3: CRANELISP_LIB environment variable.
    if let Ok(env_val) = std::env::var("CRANELISP_LIB") {
        return env_val
            .split(':')
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .collect();
    }

    // Tier 4: {project_root}/stdlib/ if it exists.
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
#[allow(dead_code)]
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

// Sprint 58 Step 5b: `has_compilable_defns` was a presence-check helper used
// by the now-defunct `codegen_programs` stash drain in `compile_module_object`.
// The replacement is `SymbolTable::defined_symbols().count() > 0`, which is
// the same predicate the priority worker uses (Decision 22). Helper deleted.

/// Apply bind chain independence analysis to all defn bodies in a program.
#[allow(dead_code)]
pub(crate) fn apply_bind_chain_analysis(
    program: &mut Program,
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    current_module: &ModuleFullPath,
) {
    use cranelisp_types::TopLevel;
    for item in program.iter_mut() {
        match item {
            TopLevel::Defn(defn) => {
                crate::bind_chain_analysis::auto_schedule_defn(
                    defn, symbol_tables, current_module,
                );
            }
            TopLevel::TraitImpl(impl_) => {
                for method in impl_.methods.iter_mut() {
                    crate::bind_chain_analysis::auto_schedule_defn(
                        method, symbol_tables, current_module,
                    );
                }
            }
            TopLevel::TraitDecl(_) | TopLevel::TypeDef { .. } | TopLevel::Expr(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Sprint 58 Wave 4 Step 5d (iii) — Cranelisp.toml project configuration tests.
// spec: 08-modules.md §8.11.4 item 2.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod project_config_tests {
    use super::*;
    use serial_test::serial;

    fn write_project_config(dir: &Path, contents: &str) {
        std::fs::write(dir.join("Cranelisp.toml"), contents).unwrap();
    }

    // spec: 08-modules.md §8.11.4 item 2 — Cranelisp.toml.lib-dirs is read.
    #[test]
    fn project_config_reads_lib_dirs_relative_paths() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), r#"lib-dirs = ["vendor", "shared"]"#);

        let dirs = load_project_config_lib_dirs(tmp.path()).unwrap().unwrap();
        assert_eq!(dirs.len(), 2);
        assert_eq!(dirs[0], tmp.path().join("vendor"));
        assert_eq!(dirs[1], tmp.path().join("shared"));
    }

    // spec: 08-modules.md §8.11.4 item 2 — absolute paths bypass project_root.
    #[test]
    fn project_config_preserves_absolute_paths() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(
            tmp.path(),
            r#"lib-dirs = ["/usr/local/share/cranelisp"]"#,
        );

        let dirs = load_project_config_lib_dirs(tmp.path()).unwrap().unwrap();
        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0], PathBuf::from("/usr/local/share/cranelisp"));
    }

    // Missing-config: returns Ok(None) so caller falls through to env/default.
    #[test]
    fn project_config_absent_returns_none() {
        let tmp = tempfile::tempdir().unwrap();
        // Don't create the file.
        let result = load_project_config_lib_dirs(tmp.path()).unwrap();
        assert!(result.is_none(), "absent config must return Ok(None)");
    }

    // Malformed TOML: surfaces a helpful error citing the file path + spec.
    #[test]
    fn project_config_malformed_emits_helpful_diagnostic() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), "lib-dirs = [\"oops");
        let result = load_project_config_lib_dirs(tmp.path());
        match result {
            Err(CranelispError::ModuleError { message, file, .. }) => {
                assert!(
                    message.contains("malformed project config"),
                    "error must self-identify as project-config parse failure: {message}"
                );
                assert!(
                    message.contains("§8.11.4"),
                    "error must cite spec §8.11.4: {message}"
                );
                assert!(
                    file.is_some(),
                    "error must carry the file path for IDE diagnostics"
                );
            }
            other => panic!("expected ModuleError, got {other:?}"),
        }
    }

    // Empty lib-dirs key: returns Ok(Some(empty)) — a valid config-driven
    // "no lib dirs" choice. (Matches CRANELISP_LIB="" semantics per spec.)
    #[test]
    fn project_config_empty_lib_dirs_returns_empty_vec() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), r#"lib-dirs = []"#);
        let dirs = load_project_config_lib_dirs(tmp.path()).unwrap().unwrap();
        assert!(dirs.is_empty(), "explicit empty list must round-trip as empty");
    }

    // Missing lib-dirs key entirely: serde(default) yields an empty vec —
    // treated as "config file says no lib dirs" (same as `lib-dirs = []`).
    #[test]
    fn project_config_missing_lib_dirs_key_returns_empty_vec() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), "# config with no lib-dirs key\n");
        let dirs = load_project_config_lib_dirs(tmp.path()).unwrap().unwrap();
        assert!(
            dirs.is_empty(),
            "missing lib-dirs key reads as empty per serde(default)"
        );
    }

    // Precedence: project config takes precedence over CRANELISP_LIB.
    // Marked #[serial] because it manipulates the process-global CRANELISP_LIB.
    #[test]
    #[serial]
    fn assemble_lib_dirs_project_config_overrides_env_var() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), r#"lib-dirs = ["vendor"]"#);

        // Save and restore CRANELISP_LIB. SAFETY: the test is `#[serial]`
        // so no concurrent test reads/writes the env var.
        let prev = std::env::var("CRANELISP_LIB").ok();
        // SAFETY: serial_test serializes env mutations; no race with
        // other Rust threads observing CRANELISP_LIB during this test.
        unsafe {
            std::env::set_var("CRANELISP_LIB", "/should/be/overridden");
        }
        let dirs = assemble_lib_dirs(tmp.path());
        // Restore (and only after capturing dirs).
        unsafe {
            match prev {
                Some(v) => std::env::set_var("CRANELISP_LIB", v),
                None => std::env::remove_var("CRANELISP_LIB"),
            }
        }
        assert_eq!(dirs.len(), 1, "project config must fully replace env tier");
        assert_eq!(
            dirs[0],
            tmp.path().join("vendor"),
            "project-config dir must win over CRANELISP_LIB"
        );
    }

    // Precedence: when no config file, CRANELISP_LIB still works (regression).
    #[test]
    #[serial]
    fn assemble_lib_dirs_env_var_still_consulted_when_no_config() {
        let tmp = tempfile::tempdir().unwrap();
        // No Cranelisp.toml created.

        let prev = std::env::var("CRANELISP_LIB").ok();
        unsafe {
            std::env::set_var("CRANELISP_LIB", "/from/env/var");
        }
        let dirs = assemble_lib_dirs(tmp.path());
        unsafe {
            match prev {
                Some(v) => std::env::set_var("CRANELISP_LIB", v),
                None => std::env::remove_var("CRANELISP_LIB"),
            }
        }
        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0], PathBuf::from("/from/env/var"));
    }

    // Precedence: when no config and no env var, falls through to {root}/stdlib.
    #[test]
    #[serial]
    fn assemble_lib_dirs_default_stdlib_when_no_config_and_no_env() {
        let tmp = tempfile::tempdir().unwrap();
        let stdlib = tmp.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        let prev = std::env::var("CRANELISP_LIB").ok();
        unsafe {
            std::env::remove_var("CRANELISP_LIB");
        }
        let dirs = assemble_lib_dirs(tmp.path());
        unsafe {
            if let Some(v) = prev {
                std::env::set_var("CRANELISP_LIB", v);
            }
        }
        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0], stdlib);
    }
}
