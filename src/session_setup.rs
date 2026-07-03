// Session: cache state and utility functions.
//
// This module provides:
// - CacheState: manifest tracking for .o caching
// - Utility functions: lib dirs, prelude resolution, exit code

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use cranelisp_types::{ErrorLocation, 
    CranelispError, ModuleFullPath, Program, Span,
    Type,
};

use cranelisp_backend::cache::manifest as cache_manifest;

// ---------------------------------------------------------------------------
// Cache state
// ---------------------------------------------------------------------------

/// Mutable cache state carried through a compilation session.
///
/// Accumulates manifest updates as modules are compiled; writes the
/// final manifest on completion.
pub struct CacheState {
    /// The cache manifest (loaded from disk or freshly created).
    manifest: cache_manifest::CacheManifest,
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
    ///
    /// **Global-key convergence (S101 obligation).** The session loads the
    /// on-disk manifest into memory here and re-flushes THAT object after
    /// recompiles — global keys preserved. A manifest whose global keys no
    /// longer match the running environment (compiler rebuilt →
    /// `compiler_mtime` stale; format-version / target-triple / cranelift /
    /// ownership-polarity mismatch likewise) must therefore be discarded at
    /// load, not carried: carrying it means every post-recompile flush
    /// re-writes the STALE fingerprint, so every future session misses
    /// forever (a permanent cache miss after any compiler rebuild). Starting
    /// from `new_for_host()` makes the first post-rebuild session a wholesale
    /// recompile whose flush stamps CURRENT keys — the next session hits.
    /// This is the src/-side cure for the class; backend's `read_manifest`
    /// already cures the ownership-polarity instance the same way.
    pub fn new(cache_dir: PathBuf) -> Self {
        let manifest = cache_manifest::read_manifest(&cache_dir)
            .filter(manifest_globals_current)
            .unwrap_or_else(cache_manifest::CacheManifest::new_for_host);
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
            cache_manifest::write_manifest(&self.cache_dir, &self.manifest)?;
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
        cache_manifest::check_manifest(&self.manifest, module_path, current_source_hash, dep_hashes)
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

/// True iff a loaded manifest's GLOBAL invalidation keys match the current
/// environment (compiler fingerprint, format version, target triple,
/// cranelift version, ownership polarity).
///
/// Probed through `check_manifest` with a module name that can never exist —
/// the global checks run first and return `Err(CacheInvalidReason)` on any
/// mismatch; a globally-valid manifest reaches the per-module lookup and
/// answers `Ok(false)` for the absent probe. Reusing the one validity gate
/// keeps this check covering any future global key without a second list
/// (Principle 7).
fn manifest_globals_current(manifest: &cache_manifest::CacheManifest) -> bool {
    cache_manifest::check_manifest(
        manifest,
        &ModuleFullPath::from("__manifest_global_key_probe__"),
        "",
        &HashMap::new(),
    )
    .is_ok()
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
    /// absolute. Under the additive model (FIXME 0410, spec §8.11.4),
    /// entries here are ADDED to the resolved set — they never replace or
    /// suppress `CRANELISP_LIB`, the programmatic additions, or the
    /// `{project_root}/stdlib/` default. An absent key / absent file /
    /// `lib-dirs = []` all contribute nothing and remove nothing.
    #[serde(default, rename = "lib-dirs")]
    lib_dirs: Vec<PathBuf>,
    /// Platform DLL search directory list (§8.11.5). Same additive
    /// semantics as `lib_dirs` — entries are ADDED to the platform-dir set.
    #[serde(default, rename = "platform-dirs")]
    platform_dirs: Vec<PathBuf>,
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
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(candidate.clone())),
        }
    })?;
    let config: ProjectConfig = toml::from_str(&contents).map_err(|e| {
        CranelispError::ModuleError {
            message: format!(
                "malformed project config '{}': {} (spec §8.11.4)",
                candidate.display(),
                e
            ),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(candidate.clone())),
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

/// Render the default `Cranelisp.toml` scaffold contents.
///
/// Every key is COMMENTED OUT, so `toml::from_str` of the result yields
/// `ProjectConfig::default()` (all-empty) — the scaffold is resolution-neutral
/// by construction (the additive model's guarantee). The current
/// `CRANELISP_LIB` paths (if any) are captured on a commented line so the user
/// can see what was in effect at scaffold time and uncomment to pin it; no
/// machine-specific path is ever written as live config.
fn render_scaffold_contents(env_lib: Option<&str>) -> String {
    let mut out = String::new();
    out.push_str("# Cranelisp.toml — project configuration (auto-created)\n");
    out.push_str("#\n");
    out.push_str("# Lib directories. Paths are relative to this file's directory, or absolute.\n");
    out.push_str("# Under the additive model (spec §8.11.4), entries here are ADDED to the set\n");
    out.push_str("# already resolved from CRANELISP_LIB and {project-root}/stdlib/ — they never\n");
    out.push_str("# replace or suppress those sources. Uncomment to make a path permanent.\n");
    out.push_str("#\n");
    out.push_str("# lib-dirs = [\n");
    out.push_str("#   \"stdlib\",          # example: a vendored stdlib beside this file\n");
    out.push_str("# ]\n");

    // Capture the current CRANELISP_LIB paths, commented, only when set+non-empty.
    let captured: Vec<PathBuf> = match env_lib {
        Some(v) if !v.is_empty() => split_env_path_list(v),
        _ => Vec::new(),
    };
    if !captured.is_empty() {
        out.push('\n');
        out.push_str(
            "# Captured from CRANELISP_LIB at scaffold time (commented — uncomment to pin):\n",
        );
        let rendered: Vec<String> = captured
            .iter()
            .map(|p| format!("\"{}\"", p.display()))
            .collect();
        out.push_str(&format!("# lib-dirs = [{}]\n", rendered.join(", ")));
    }

    out.push('\n');
    out.push_str("# Platform DLL search dirs (§8.11.5). Same additive semantics.\n");
    out.push_str("# platform-dirs = [\"target/debug\"]\n");
    out
}

/// Scaffold a default `{project_root}/Cranelisp.toml` if (and only if) one
/// does not already exist.
///
/// Returns `Ok(true)` if a file was newly created, `Ok(false)` if one already
/// existed (no-op) OR a write failure was caught gracefully (the scaffold is a
/// convenience — never a launch gate). This function emits NO output; the
/// caller (the REPL §0.5-rule-3 path only) renders the `[created …]` notice
/// from an `Ok(true)` return.
///
/// Invariants (per `design/int/cranelisp-toml.md §12.3`):
/// - **Never overwrite** — the exists-check is the first statement; an existing
///   file (any content) is left verbatim. Idempotent.
/// - **Never write outside the resolved project root** — a single
///   non-recursive `project_root.join(...)`.
/// - **Atomic** — temp-then-rename via `save::atomic_write`.
/// - **Graceful on read-only dir** — a write failure returns `Ok(false)`, not
///   an error, so the caller never fails the REPL launch.
/// - **REPL-only** — called from the REPL §0.5-rule-3 path; never from
///   `--run` / `--link`.
///
/// Spec: 08-modules.md §8.11.4 (additive model) + repl/spec.md §0.5 rule 3.
pub fn scaffold_project_config(project_root: &Path) -> std::io::Result<bool> {
    let candidate = project_root.join("Cranelisp.toml");
    // Never overwrite: an existing file (any content) is left verbatim.
    if candidate.exists() {
        return Ok(false);
    }
    let env_lib = std::env::var("CRANELISP_LIB").ok();
    let contents = render_scaffold_contents(env_lib.as_deref());
    // Atomic write; graceful on a read-only directory — a write failure is
    // non-fatal (the absent-file resolution path is well-defined and unchanged).
    match crate::save::atomic_write(&candidate, &contents) {
        Ok(()) => Ok(true),
        Err(_) => Ok(false),
    }
}

/// Split a colon-separated environment variable value into path entries,
/// dropping empty segments.
fn split_env_path_list(env_val: &str) -> Vec<PathBuf> {
    env_val
        .split(':')
        .filter(|s| !s.is_empty())
        .map(PathBuf::from)
        .collect()
}

/// Order-preserving dedup: keep each path at its FIRST (highest-precedence)
/// occurrence, so first-match search order is preserved.
fn dedup_preserve_order(paths: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut seen: HashSet<PathBuf> = HashSet::new();
    let mut out: Vec<PathBuf> = Vec::with_capacity(paths.len());
    for p in paths {
        if seen.insert(p.clone()) {
            out.push(p);
        }
    }
    out
}

/// Read `{project_root}/Cranelisp.toml`'s `platform-dirs`, resolved against
/// `project_root` (relative) or used verbatim (absolute).
///
/// Returns `Ok(None)` when the file is absent, `Ok(Some(dirs))` when present
/// (possibly empty), `Err` when malformed. Mirrors
/// `load_project_config_lib_dirs` shape — the additive caller folds the result.
///
/// Spec: 08-modules.md §8.11.5.
pub fn load_project_config_platform_dirs(
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
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(candidate.clone())),
        }
    })?;
    let config: ProjectConfig = toml::from_str(&contents).map_err(|e| {
        CranelispError::ModuleError {
            message: format!(
                "malformed project config '{}': {} (spec §8.11.5)",
                candidate.display(),
                e
            ),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(candidate.clone())),
        }
    })?;
    let resolved: Vec<PathBuf> = config
        .platform_dirs
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
/// Additive model (FIXME 0410, spec §8.11.4): the resolved set is the
/// order-preserving, deduplicated UNION of all sources, in **search order**
/// (first-match precedence on a name present in more than one dir):
///
/// 1. `CRANELISP_LIB` environment variable (colon-separated). §8.11.4 item 3.
/// 2. `Cranelisp.toml` `lib-dirs` (resolved against the project root). Only
///    ADDS paths — an absent key / absent file / `lib-dirs = []` contribute
///    nothing and suppress nothing. §8.11.4 item 2.
/// 3. `{project_root}/stdlib/` default, if it exists. Always contributes
///    when present — it is no longer a fallback an earlier source turns off.
///    §8.11.4 item 4.
///
/// The highest-precedence tier (explicit programmatic / CLI additions) is
/// layered on top by callers via `SharedState.lib_dirs` setters; this
/// function returns the configuration-derived baseline only, in the order
/// above so the caller's prepended additions remain highest-precedence.
///
/// On project-config parse error: the malformed config contributes nothing
/// and is silently ignored. Callers that want the parse error surfaced
/// should call `load_project_config_lib_dirs` directly.
pub fn assemble_lib_dirs(project_root: &Path) -> Vec<PathBuf> {
    let mut dirs: Vec<PathBuf> = Vec::new();

    // Tier: CRANELISP_LIB env var (search-first among config sources).
    if let Ok(env_val) = std::env::var("CRANELISP_LIB") {
        dirs.extend(split_env_path_list(&env_val));
    }

    // Tier: Cranelisp.toml lib-dirs (additive — only ever adds).
    if let Ok(Some(config_dirs)) = load_project_config_lib_dirs(project_root) {
        dirs.extend(config_dirs);
    }

    // Tier: {project_root}/stdlib/ default, searched last, when present.
    let candidate = project_root.join("stdlib");
    if candidate.is_dir() {
        dirs.push(candidate);
    }

    dedup_preserve_order(dirs)
}

/// Assemble extra platform DLL search directories (§8.11.5).
///
/// Additive model (FIXME 0410), mirroring `assemble_lib_dirs` in search order:
///
/// 1. `CRANELISP_PLATFORM_PATH` environment variable (colon-separated).
/// 2. `Cranelisp.toml` `platform-dirs` (resolved against `project_root`) —
///    additive; only ever adds.
///
/// There is no default tier here (project-root and lib-dir platform
/// subdirectories — §8.11.5 tiers 1-2 — are handled by `resolve_platform_path`
/// directly). A malformed config contributes nothing.
pub fn assemble_platform_dirs(project_root: &Path) -> Vec<PathBuf> {
    let mut dirs: Vec<PathBuf> = Vec::new();

    if let Ok(env_val) = std::env::var("CRANELISP_PLATFORM_PATH") {
        dirs.extend(split_env_path_list(&env_val));
    }

    if let Ok(Some(config_dirs)) = load_project_config_platform_dirs(project_root) {
        dirs.extend(config_dirs);
    }

    dedup_preserve_order(dirs)
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
///
/// Sprint 67 hack-back: narrowed to `pub(crate)` + `#[allow(dead_code)]` —
/// no current callers (the exit-code derivation is currently inline in
/// `main.rs`); retained as the canonical spec §10.6.1 mapping.
#[allow(dead_code)]
pub(crate) fn determine_exit_code(value: i64, inner_ty: &Type) -> i32 {
    match inner_ty {
        Type::Int => value as i32,
        _ => 0,
    }
}

// `inject_prelude_import` DELETED (S76 W-Absorb). It was a dead `pub(crate)`
// helper (zero call sites) wrapping the struck `cranelisp_typecheck::
// register_imports`. Implicit prelude injection happens in
// `worker.rs::ensure_prelude_imported` via `crate::imports::install_imports`.

// Sprint 58 Step 5b: `has_compilable_defns` was a presence-check helper used
// by the now-defunct `codegen_programs` stash drain in `compile_module_object`.
// The replacement is `SymbolTable::defined_symbols().count() > 0`, which is
// the same predicate the priority worker uses (Decision 22). Helper deleted.

/// Apply bind chain independence analysis to all defn bodies in a program.
///
/// Wired live at the `finalize_cluster` seam (S85, FIXME 0367) — runs over the
/// post-Pass-2 `final_working` program (wrapped exprs + appended default-method
/// defns), after macro expansion and before `check_program_compat`. Genericized
/// over the symbol table's store params so it accepts the session's live
/// `SymbolTable<Code, ()>` directly (no `into_concrete` / view projection).
pub(crate) fn apply_bind_chain_analysis<
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
>(
    program: &mut Program,
    symbol_tables: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable<C, L>>,
    current_module: &ModuleFullPath,
) {
    use cranelisp_types::TopLevel;
    // Multi-sig (overloaded / multi-clause) defns are NOT auto-scheduled —
    // `auto_schedule_defn` asserts single-sig (each clause body would need its
    // own transform sweep, and the bind-chain analysis is defined over a single
    // body). Skipping them keeps the assert an invariant rather than a crash on
    // the live path: a `(defn f ([a] ..) ([a b] ..))` form is a `Defn` with
    // `is_multi_sig() == true` and must be left untouched.
    for item in program.iter_mut() {
        match item {
            TopLevel::Defn(defn) if !defn.is_multi_sig() => {
                crate::bind_chain_analysis::auto_schedule_defn(
                    defn, symbol_tables, current_module,
                );
            }
            TopLevel::TraitImpl(impl_) => {
                for method in impl_.methods.iter_mut() {
                    if !method.is_multi_sig() {
                        crate::bind_chain_analysis::auto_schedule_defn(
                            method, symbol_tables, current_module,
                        );
                    }
                }
            }
            TopLevel::Defn(_)
            | TopLevel::TraitDecl(_)
            | TopLevel::TypeDef { .. }
            | TopLevel::Expr(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// S101 — manifest global-key convergence tests (accumulated obligation 2).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod manifest_convergence_tests {
    use super::*;

    fn write_manifest_json(dir: &Path, compiler_mtime: &str) {
        // Build a manifest with CURRENT global keys, then stamp a stale
        // compiler fingerprint — isolates the compiler_mtime key.
        let mut manifest = cache_manifest::CacheManifest::new_for_host();
        manifest.compiler_mtime = compiler_mtime.to_string();
        manifest.upsert_module(
            &ModuleFullPath::from("user"),
            "stale-module-hash".to_string(),
            HashMap::new(),
        );
        cache_manifest::write_manifest(dir, &manifest).unwrap();
    }

    // spec: design/int/session-transaction.md §8 — after a compiler rebuild
    // the loaded manifest's stale global fingerprint must NOT be carried into
    // the session (and re-flushed forever); the session starts from a fresh
    // host manifest so the first post-rebuild flush stamps CURRENT keys and
    // the NEXT session's cache-hit check converges.
    #[test]
    fn stale_compiler_fingerprint_manifest_is_discarded_and_flush_converges() {
        let tmp = tempfile::tempdir().unwrap();
        write_manifest_json(tmp.path(), "mtime-1.1");

        let mut cs = CacheState::new(tmp.path().to_path_buf());
        // Record a recompiled module and flush — the manifest on disk must
        // now carry the CURRENT compiler fingerprint, not the stale one.
        cs.record_module(
            &ModuleFullPath::from("user"),
            "fresh-hash".to_string(),
            HashMap::new(),
        );
        cs.flush().unwrap();

        let reread = cache_manifest::read_manifest(tmp.path()).expect("manifest re-reads");
        assert_eq!(
            reread.compiler_mtime,
            cache_manifest::binary_fingerprint(),
            "post-rebuild flush must stamp the CURRENT compiler fingerprint"
        );
        assert_ne!(reread.compiler_mtime, "mtime-1.1");
        // The stale per-module entries were discarded with the stale manifest
        // (they reference caches the fingerprint invalidated wholesale).
        assert_eq!(
            reread
                .get_module(&ModuleFullPath::from("user"))
                .map(|m| m.source_hash.as_str()),
            Some("fresh-hash"),
            "the fresh session's own record survives"
        );
    }

    // spec: (same anchor) — negative: a manifest whose global keys are
    // CURRENT is preserved (its module entries stay valid across sessions).
    #[test]
    fn current_manifest_neg_is_preserved_not_discarded() {
        let tmp = tempfile::tempdir().unwrap();
        let mut manifest = cache_manifest::CacheManifest::new_for_host();
        manifest.upsert_module(
            &ModuleFullPath::from("user"),
            "kept-hash".to_string(),
            HashMap::new(),
        );
        cache_manifest::write_manifest(tmp.path(), &manifest).unwrap();

        let cs = CacheState::new(tmp.path().to_path_buf());
        assert!(
            cs.is_cache_valid(&ModuleFullPath::from("user"), "kept-hash", &HashMap::new()),
            "a globally-current manifest's module entries must survive the load"
        );
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
            Err(CranelispError::ModuleError { message, location, .. }) => {
                assert!(
                    message.contains("malformed project config"),
                    "error must self-identify as project-config parse failure: {message}"
                );
                assert!(
                    message.contains("§8.11.4"),
                    "error must cite spec §8.11.4: {message}"
                );
                assert!(
                    location.file.is_some(),
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

    // Helper: run `f` with CRANELISP_LIB set to `val`, restoring the prior
    // value afterward. SAFETY: callers are `#[serial]`, so no concurrent test
    // reads/writes the env var.
    fn with_env_lib<T>(val: Option<&str>, f: impl FnOnce() -> T) -> T {
        let prev = std::env::var("CRANELISP_LIB").ok();
        unsafe {
            match val {
                Some(v) => std::env::set_var("CRANELISP_LIB", v),
                None => std::env::remove_var("CRANELISP_LIB"),
            }
        }
        let out = f();
        unsafe {
            match prev {
                Some(v) => std::env::set_var("CRANELISP_LIB", v),
                None => std::env::remove_var("CRANELISP_LIB"),
            }
        }
        out
    }

    // Additive model (FIXME 0410): `assemble_lib_dirs` returns the UNION of
    // CRANELISP_LIB + Cranelisp.toml lib-dirs + {root}/stdlib/, in search
    // order. The config dir does NOT replace the env tier — both contribute.
    #[test]
    #[serial]
    fn assemble_lib_dirs_unions_env_config_and_default() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), r#"lib-dirs = ["vendor"]"#);
        let stdlib = tmp.path().join("stdlib");
        std::fs::create_dir_all(&stdlib).unwrap();

        let dirs = with_env_lib(Some("/env/dir"), || assemble_lib_dirs(tmp.path()));

        // All three sources contribute, in §11.1 search order:
        // env → toml config → {root}/stdlib.
        assert_eq!(
            dirs,
            vec![
                PathBuf::from("/env/dir"),
                tmp.path().join("vendor"),
                stdlib,
            ],
            "additive union must include all three tiers in search order"
        );
    }

    // Additive NEG: an empty `lib-dirs` (and equivalently an absent key)
    // removes nothing — the env tier is still present.
    #[test]
    #[serial]
    fn assemble_lib_dirs_empty_config_does_not_suppress_env() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), "lib-dirs = []\n");

        let dirs = with_env_lib(Some("/env/dir"), || assemble_lib_dirs(tmp.path()));
        assert!(
            dirs.contains(&PathBuf::from("/env/dir")),
            "an empty lib-dirs must not suppress the env tier; got {dirs:?}"
        );
    }

    // Additive dedup: a directory named by BOTH CRANELISP_LIB and the config
    // file appears once, at its EARLIEST (env) position — first-match order.
    #[test]
    #[serial]
    fn assemble_lib_dirs_dedups_at_earliest_position() {
        let tmp = tempfile::tempdir().unwrap();
        let shared = tmp.path().join("shared");
        // Config names the same absolute path as the env var.
        let cfg = format!(r#"lib-dirs = ["{}"]"#, shared.display());
        write_project_config(tmp.path(), &cfg);

        let dirs = with_env_lib(Some(shared.to_str().unwrap()), || {
            assemble_lib_dirs(tmp.path())
        });
        let count = dirs.iter().filter(|p| **p == shared).count();
        assert_eq!(count, 1, "a dir in both env+config must appear once; got {dirs:?}");
        assert_eq!(
            dirs[0], shared,
            "the deduped entry must sit at its earliest (env) position"
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

    // -------------------------------------------------------------------
    // FIXME 0410 — additive platform-dirs union (§8.11.5).
    // -------------------------------------------------------------------

    // Additive: `assemble_platform_dirs` unions CRANELISP_PLATFORM_PATH +
    // Cranelisp.toml platform-dirs, in search order, deduped.
    #[test]
    #[serial]
    fn assemble_platform_dirs_unions_env_and_config() {
        let tmp = tempfile::tempdir().unwrap();
        write_project_config(tmp.path(), r#"platform-dirs = ["plat"]"#);

        let prev = std::env::var("CRANELISP_PLATFORM_PATH").ok();
        unsafe {
            std::env::set_var("CRANELISP_PLATFORM_PATH", "/env/plat");
        }
        let dirs = assemble_platform_dirs(tmp.path());
        unsafe {
            match prev {
                Some(v) => std::env::set_var("CRANELISP_PLATFORM_PATH", v),
                None => std::env::remove_var("CRANELISP_PLATFORM_PATH"),
            }
        }
        assert_eq!(
            dirs,
            vec![PathBuf::from("/env/plat"), tmp.path().join("plat")],
            "platform-dirs union: env then config, additive"
        );
    }

    // -------------------------------------------------------------------
    // FIXME 0410 — `scaffold_project_config` writer (§12.4 acceptance).
    // -------------------------------------------------------------------

    // Creates: on a dir with no Cranelisp.toml, scaffold writes one that
    // parses to ProjectConfig::default() (every key commented ⇒ all-empty).
    #[test]
    #[serial]
    fn scaffold_creates_default_neutral_config() {
        let tmp = tempfile::tempdir().unwrap();
        let created = with_env_lib(None, || scaffold_project_config(tmp.path()).unwrap());
        assert!(created, "scaffold of a fresh dir must return Ok(true)");

        let path = tmp.path().join("Cranelisp.toml");
        assert!(path.is_file(), "the file must now exist");

        let contents = std::fs::read_to_string(&path).unwrap();
        let config: ProjectConfig = toml::from_str(&contents).unwrap();
        assert!(
            config.lib_dirs.is_empty() && config.platform_dirs.is_empty(),
            "every key is commented ⇒ scaffold parses to the empty default"
        );
    }

    // No-overwrite / idempotent: a pre-existing file (any content) is left
    // byte-identical, and the call returns Ok(false). A second call after a
    // create is also Ok(false).
    #[test]
    #[serial]
    fn scaffold_never_overwrites_existing_byte_identical() {
        let tmp = tempfile::tempdir().unwrap();
        let sentinel = "# hand-written\nlib-dirs = [\"keep\"]\n";
        std::fs::write(tmp.path().join("Cranelisp.toml"), sentinel).unwrap();

        let created = scaffold_project_config(tmp.path()).unwrap();
        assert!(!created, "an existing file must return Ok(false)");
        let after = std::fs::read_to_string(tmp.path().join("Cranelisp.toml")).unwrap();
        assert_eq!(after, sentinel, "existing file must be byte-identical");

        // Idempotent: a second call on a now-existing file is also Ok(false).
        let again = scaffold_project_config(tmp.path()).unwrap();
        assert!(!again, "second call after create must be Ok(false)");
    }

    // CRANELISP_LIB capture: when set, the scaffold carries the paths on a
    // COMMENTED line; when unset, no such commented machine-path line appears.
    #[test]
    #[serial]
    fn scaffold_captures_cranelisp_lib_commented() {
        // Set: the paths appear, but only on comment lines.
        let tmp = tempfile::tempdir().unwrap();
        with_env_lib(Some("/x:/y"), || {
            assert!(scaffold_project_config(tmp.path()).unwrap());
        });
        let contents = std::fs::read_to_string(tmp.path().join("Cranelisp.toml")).unwrap();
        for needle in ["/x", "/y"] {
            let on_comment = contents
                .lines()
                .filter(|l| l.contains(needle))
                .all(|l| l.trim_start().starts_with('#'));
            let present = contents.contains(needle);
            assert!(present, "captured env path {needle} must appear");
            assert!(
                on_comment,
                "captured env path {needle} must appear only COMMENTED"
            );
        }

        // Unset: no captured machine-path block at all.
        let tmp2 = tempfile::tempdir().unwrap();
        with_env_lib(None, || {
            assert!(scaffold_project_config(tmp2.path()).unwrap());
        });
        let contents2 = std::fs::read_to_string(tmp2.path().join("Cranelisp.toml")).unwrap();
        assert!(
            !contents2.contains("Captured from CRANELISP_LIB"),
            "no capture block when CRANELISP_LIB is unset"
        );
    }

    // Read-only dir: scaffolding into a read-only directory does not panic and
    // does not return a launch-fatal error — it returns the graceful Ok(false)
    // and writes no file.
    #[test]
    #[serial]
    #[cfg(unix)]
    fn scaffold_graceful_on_read_only_dir() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = tempfile::tempdir().unwrap();
        let ro = tmp.path().join("ro");
        std::fs::create_dir(&ro).unwrap();
        // Make the directory read-only (no write/execute-create).
        std::fs::set_permissions(&ro, std::fs::Permissions::from_mode(0o500)).unwrap();

        let result = with_env_lib(None, || scaffold_project_config(&ro));
        // Graceful: Ok(false), never an Err that would fail the REPL launch.
        assert_eq!(
            result.ok(),
            Some(false),
            "read-only dir must yield the graceful Ok(false), not Err"
        );
        assert!(
            !ro.join("Cranelisp.toml").is_file(),
            "no file is written into a read-only dir"
        );

        // Restore perms so the tempdir can be cleaned up.
        let _ = std::fs::set_permissions(&ro, std::fs::Permissions::from_mode(0o700));
    }
}
