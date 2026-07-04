// session_v4::index_worker — Pillar-3 importable-symbol indexer (S91).
//
// The nice-worker background facility that answers `/search <name>|<scheme>`
// over symbols REACHABLE BUT NOT YET IMPORTED (lib-search-path ∪ project-root).
// Design of record: `design/int/agent.md §25`,
// `design/arch/repl-embedded-agent.md §11` (R13–R18), `repl/spec.md §17.19`.
//
// This is a DEFAULT-BUILD facility (NOT `#[cfg(feature="agent")]`): the index is
// built by the nice workers, which run regardless of the agent feature; `/search`
// is an ordinary REPL command. The agent reaches it via the ordinary read-only
// pull (`src/agent/pull.rs` ALLOWLIST).
//
// The model is read-or-produce-`.meta`, one-artifact (R13):
//   (a) module present in the scheduler ModuleState registry  -> SKIP (real path
//       owns it; the indexer reads its `.meta` later).
//   (b) valid `.meta` (schema+BUILD_ID gate AND int's source-content gate)
//       -> deserialise the SymbolTable, read its public entries, NO typecheck.
//   (c) no/stale `.meta`  -> typecheck once on the nice worker against throwaway
//       staging (the validate_forms_dry_run discard substrate), wrapped in CF.2
//       `catch_unwind`, then `cache::write_meta` (no `.o`, no register_module),
//       then read public entries.
//
// REPL-only by construction (R17): the worklist is enumerated ONLY at REPL
// startup; `--run`/`--link`/`--release` never enumerate it.
//
// Abandon-on-flush/shutdown (R18): the burn-down is best-effort warm-up, never a
// correctness obligation. Index work yields to object codegen and is never
// drained-to-completion at a flush; the loop checks the shutdown flag between
// `IndexModule` tasks.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Mutex;

use cranelisp_types::{ModuleEntry, ModuleFullPath, Symbol, Type};

use super::SharedState;

/// The two purpose-built lookup indices (R3, R16) — int-private, derived
/// read-caches over the `.meta` cache. NOT a symbol table, NOT serialized, NO
/// `CACHE_SCHEMA_VERSION` bump. Rebuildable by a `.meta`-scan over the reachable
/// modules. Placed on `SharedState` (the nice workers receive `&SharedState`),
/// a sibling to `introspection` — guard-excluded.
#[derive(Debug, Default)]
pub(crate) struct ImportableIndices {
    inner: Mutex<IndicesInner>,
}

#[derive(Debug, Default)]
struct IndicesInner {
    /// Index A — name lookup: `symbol → modules`, exact OR substring.
    by_symbol: HashMap<Symbol, Vec<ModuleFullPath>>,
    /// Index B — type lookup: `(scheme, symbol, module)`, exact OR partial
    /// (structural-contains) via the `cranelisp-typecheck` predicates (§25.7).
    by_scheme: Vec<(Type, Symbol, ModuleFullPath)>,
    /// Burn-down progress / skip-state guard: modules already processed (any
    /// branch). Doubles as the worklist-completeness signal.
    indexed: HashSet<ModuleFullPath>,
    /// The `IndexModule` worklist — reachable modules awaiting an index pass.
    /// Separate from the object-codegen worklist (no `.o` entanglement, §25.1).
    /// `None` until the burn-down is armed (REPL-only, R17); `Some(empty)` once
    /// armed-but-drained. `armed` records whether enumeration has happened so a
    /// `--run`/`--link` session that never arms is observably distinct.
    worklist: VecDeque<ModuleFullPath>,
    /// Total module count enumerated onto the worklist (for the
    /// "indexing N modules…" partial-results note, §25.5 / spec §17.19.3).
    enumerated_total: usize,
    /// Whether the burn-down has been armed (REPL-startup enumeration ran).
    armed: bool,
}

/// One result row of a `/search` (the four facets, spec §17.19.2).
#[derive(Debug, Clone)]
pub(crate) struct SearchHit {
    pub name: Symbol,
    pub module: ModuleFullPath,
    /// The matched signature, for the `:Type` facet.
    pub scheme: Type,
}

impl ImportableIndices {
    /// True once the burn-down has been armed (REPL-startup enumeration ran).
    pub(crate) fn is_armed(&self) -> bool {
        self.inner.lock().unwrap_or_else(|e| e.into_inner()).armed
    }

    /// Number of reachable modules NOT yet indexed — the "indexing N modules…"
    /// partial-results count (0 ⇒ burn-down complete).
    pub(crate) fn pending_count(&self) -> usize {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        g.enumerated_total.saturating_sub(g.indexed.len())
    }

    /// Enumerate the reachable set onto the `IndexModule` worklist (R17 — armed
    /// at REPL startup only). Idempotent: a second call is a no-op once armed.
    /// `modules` is the discovered reachable set (lib-path ∪ project-root via
    /// `pipeline::resolve_module_file`).
    pub(crate) fn arm(&self, modules: Vec<ModuleFullPath>) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        if g.armed {
            return;
        }
        g.armed = true;
        for m in modules {
            if !g.indexed.contains(&m) {
                g.worklist.push_back(m);
            }
        }
        g.enumerated_total = g.worklist.len();
    }

    /// Pop the next `IndexModule` task, if any. `None` ⇒ worklist drained (the
    /// nice worker falls back to parking). The shutdown flag is checked by the
    /// caller between tasks (R18 abandon-on-shutdown).
    fn take_index_task(&self) -> Option<ModuleFullPath> {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        g.worklist.pop_front()
    }

    /// Mark a module as indexed with no entries (branch a SKIP, or a CF.2 /
    /// branch-(c) Err skip) so it is not retried.
    fn mark_skipped(&self, module: &ModuleFullPath) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        g.indexed.insert(module.clone());
    }

    /// Record the public entries of `module` into both indices and mark it
    /// indexed. Each `(name, scheme.ty)` is one importable symbol.
    fn record_entries(&self, module: &ModuleFullPath, entries: Vec<(Symbol, Type)>) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        for (name, scheme) in entries {
            g.by_symbol
                .entry(name.clone())
                .or_default()
                .push(module.clone());
            g.by_scheme.push((scheme, name, module.clone()));
        }
        g.indexed.insert(module.clone());
    }

    /// `record_entries` variant taking the `.meta`-write triple
    /// `(name, scheme.ty, entry)` — drops the entry, records `(name, ty)`.
    fn record_triples(
        &self,
        module: &ModuleFullPath,
        entries: Vec<(Symbol, Type, ModuleEntry<crate::code::Code>)>,
    ) {
        let pairs: Vec<(Symbol, Type)> =
            entries.into_iter().map(|(n, t, _e)| (n, t)).collect();
        self.record_entries(module, pairs);
    }

    /// Search by NAME — exact OR case-insensitive substring (§25.7 partial
    /// name). Returns `(name, module)` pairs; the caller resolves the scheme
    /// for the row from `by_scheme`.
    pub(crate) fn search_by_name(&self, query: &str) -> Vec<SearchHit> {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let lc = query.to_lowercase();
        let mut hits = Vec::new();
        for (scheme, name, module) in &g.by_scheme {
            if name.as_ref().to_lowercase().contains(&lc) {
                hits.push(SearchHit {
                    name: name.clone(),
                    module: module.clone(),
                    scheme: scheme.clone(),
                });
            }
        }
        hits
    }

    /// Search by SCHEME — exact OR partial (structural-contains), calling the
    /// `cranelisp-typecheck` predicates (§25.7). int CALLS them; does not own
    /// them.
    pub(crate) fn search_by_scheme(&self, query: &Type) -> Vec<SearchHit> {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let mut hits = Vec::new();
        for (scheme, name, module) in &g.by_scheme {
            let matched = cranelisp_typecheck::signature_matches_exact(query, scheme)
                || cranelisp_typecheck::signature_matches_partial(query, scheme);
            if matched {
                hits.push(SearchHit {
                    name: name.clone(),
                    module: module.clone(),
                    scheme: scheme.clone(),
                });
            }
        }
        hits
    }
}

// ---------------------------------------------------------------------------
// Discovery + arming (R10 reachable-set enumeration; R17 REPL-startup-only)
// ---------------------------------------------------------------------------

/// Enumerate the reachable set — every `.cl` module on the lib search path ∪ the
/// project root (R10) — and arm the burn-down (R17 — REPL startup only). Idempotent.
/// Wakes the nice workers so they begin draining the `IndexModule` worklist.
///
/// The reachable set uses the SAME directories `import` searches
/// (`pipeline::resolve_module_file` — project root + lib dirs); discovery here is
/// a directory walk over those roots producing module paths. The per-module pass
/// (`index_one_module`) then re-resolves each via `resolve_module_file` so the
/// search semantics are identical (no new search rules, §25.1).
pub(crate) fn arm_burndown(shared: &SharedState) {
    if shared.importable_indices.is_armed() {
        return;
    }
    let lib_dirs = shared
        .lib_dirs
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone();

    let mut modules: Vec<ModuleFullPath> = Vec::new();
    let mut seen: HashSet<ModuleFullPath> = HashSet::new();
    // A directory that is itself a lib-dir is NOT walked as part of the project
    // root: a file `lib/mathx.cl` on a lib-dir resolves to module `mathx` (the
    // lib-dir is a search ROOT), not `lib.mathx` (which would be the project-root
    // relative path). Excluding lib-dirs from the project-root walk makes the
    // discovered module names match `resolve_module_file`'s `module → path`
    // mapping exactly (§25.1 — same search semantics, no double-listing).
    let canonical_lib_dirs: HashSet<std::path::PathBuf> = lib_dirs
        .iter()
        .filter_map(|d| std::fs::canonicalize(d).ok())
        .collect();
    // Project root is searched FIRST (import precedence, §8.11.2) — but skipping
    // any subtree that is a lib-dir — then the lib dirs as their own roots.
    enumerate_cl_modules_excluding(
        &shared.project_root,
        &shared.project_root,
        &canonical_lib_dirs,
        &mut modules,
        &mut seen,
    );
    for dir in &lib_dirs {
        enumerate_cl_modules(dir, dir, &mut modules, &mut seen);
    }

    shared.importable_indices.arm(modules);
    // Wake the nice workers parked on the object-codegen condvar so they begin
    // draining the index worklist (the arm-wake, §25.5).
    shared.scheduler.wake_object_workers();
}

/// Recursively enumerate `.cl` files under `dir` as dotted module paths relative
/// to `root` (mirroring `resolve_module_file`'s `module → path` mapping inverse:
/// `a/b.cl` ⇒ module `a.b`). Skips the cache directory and hidden dirs. First
/// occurrence wins (project-root precedence). `prelude.cl` is skipped (it is the
/// implicit outer scope, not an importable module).
fn enumerate_cl_modules(
    root: &std::path::Path,
    dir: &std::path::Path,
    out: &mut Vec<ModuleFullPath>,
    seen: &mut HashSet<ModuleFullPath>,
) {
    let no_exclude = HashSet::new();
    enumerate_cl_modules_excluding(root, dir, &no_exclude, out, seen);
}

/// As [`enumerate_cl_modules`] but skips any subdirectory whose canonical path is
/// in `exclude` (used to keep lib-dir subtrees out of the project-root walk so a
/// `lib/mathx.cl` resolves to module `mathx`, not `lib.mathx`).
fn enumerate_cl_modules_excluding(
    root: &std::path::Path,
    dir: &std::path::Path,
    exclude: &HashSet<std::path::PathBuf>,
    out: &mut Vec<ModuleFullPath>,
    seen: &mut HashSet<ModuleFullPath>,
) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with('.') {
            continue; // hidden + `.cranelisp-cache`
        }
        if path.is_dir() {
            // Skip a subdirectory that is itself a lib-dir search root.
            if let Ok(canon) = std::fs::canonicalize(&path)
                && exclude.contains(&canon)
            {
                continue;
            }
            enumerate_cl_modules_excluding(root, &path, exclude, out, seen);
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) != Some("cl") {
            continue;
        }
        let Ok(rel) = path.strip_prefix(root) else {
            continue;
        };
        // `a/b.cl` → `a.b`; `foo.cl` → `foo`.
        let rel_str = rel.with_extension("");
        let dotted = rel_str.to_string_lossy().replace(std::path::MAIN_SEPARATOR, ".");
        if dotted == "prelude" || dotted.is_empty() {
            continue;
        }
        let module = ModuleFullPath::from(dotted.as_str());
        if seen.insert(module.clone()) {
            out.push(module);
        }
    }
}

// ---------------------------------------------------------------------------
// The per-module index pass (the three branches, R13–R16)
// ---------------------------------------------------------------------------

/// Drain ONE `IndexModule` task and run its index pass. Called by the nice
/// worker loop when no object-codegen work is pending (object codegen first,
/// index in the slack — §25.5 / R17). Returns `true` if a task was processed,
/// `false` if the worklist was empty (the worker should park).
///
/// The shutdown flag is checked by the caller BEFORE this call (R18); a task
/// already popped runs to completion (atomic `.meta` write ⇒ no corruption even
/// if the next task is abandoned).
pub(crate) fn run_one_index_task(shared: &SharedState) -> bool {
    let Some(module) = shared.importable_indices.take_index_task() else {
        return false;
    };
    index_one_module(shared, &module);
    true
}

/// The three-branch per-module step (§25.1). Takes EXACTLY one branch.
fn index_one_module(shared: &SharedState, module: &ModuleFullPath) {
    // Branch (a): the real path owns any module in the scheduler registry (any
    // pool state). SKIP — its `.meta` is read later (a real-typechecked module
    // always has a `.meta` from the Phase-1 writer). No typecheck, no write.
    if shared.scheduler.is_registered(module) {
        shared.importable_indices.mark_skipped(module);
        return;
    }

    // Resolve the module's source file with the SAME rules `import` uses (R10).
    let lib_dirs = shared
        .lib_dirs
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone();
    let Some(file) = crate::pipeline::resolve_module_file(module, &shared.project_root, &lib_dirs)
    else {
        // No source file — nothing to index. Mark indexed so it is not retried.
        shared.importable_indices.mark_skipped(module);
        return;
    };

    let Some(cache_dir) = shared.cache.cache_dir() else {
        // Caching disabled — fall through to branch (c) typecheck-in-memory
        // (no `.meta` to read, none written). We still index the module so
        // `/search` works without a cache directory.
        index_branch_c(shared, module, &file, None);
        return;
    };

    // Branch (b): valid `.meta` (schema+BUILD_ID gate AND int's source-content
    // gate). Read the public entries with NO typecheck (R16).
    if let Some(entries) = try_branch_b(shared, module, &file, &cache_dir) {
        shared.importable_indices.record_entries(module, entries);
        return;
    }

    // Branch (c): no/stale `.meta` — typecheck once, write `.meta`, populate.
    index_branch_c(shared, module, &file, Some(cache_dir));
}

/// Branch (b): read the module's `.meta` if it is valid on BOTH gates — the
/// backend schema+BUILD_ID gate (`cache::load_meta`) AND int's source-content
/// gate (`is_cache_valid` over the freshly-hashed source). Returns the public
/// entries on a hit; `None` on any miss (caller falls to branch c).
fn try_branch_b(
    shared: &SharedState,
    module: &ModuleFullPath,
    file: &std::path::Path,
    cache_dir: &std::path::Path,
) -> Option<Vec<(Symbol, Type)>> {
    use cranelisp_backend::cache;

    // Source-content gate: hash the live source and consult the manifest loaded
    // at session start. A source edit since the `.meta` was written invalidates
    // it here (caught exactly like the real path's `is_cache_valid`).
    let source = std::fs::read_to_string(file).ok()?;
    let source_hash = cache::manifest::hash_source(&source);
    // Record the hash so a later real `/import` of this module is a cache-hit on
    // the live import path (§25.5 — index→import is a `.meta` cache-hit).
    shared.cache.record_source_hash(module, source_hash.clone());
    let empty_deps = HashMap::new();
    if !shared.cache.is_cache_valid(module, &source_hash, &empty_deps) {
        return None;
    }

    // Schema+BUILD_ID gate: deserialise the SymbolTable from the `.meta`.
    let (meta_path, _o_path) = cache::module_cache_path(cache_dir, module);
    let table = cache::serialize::load_meta(&meta_path).ok()?;
    Some(public_entries_from_table(&table))
}

/// Branch (c): typecheck once on the nice worker through the real
/// import-installing + typecheck path (`cluster::process_cluster`, the discard
/// substrate's full sibling — it installs the module's own `(import …)` decls
/// and runs `check_forms`), wrapped in CF.2 `catch_unwind` (§25.4). On a clean
/// check the typed entries land in the LIVE `symbol_tables[module]` table; the
/// indexer reads its public entries, writes a benign `.meta` (no `.o`, no
/// `register_module`), records the indices, then REMOVES the live residue so the
/// four `SharedState` maps stay byte-unchanged (R13). On an Err or a caught
/// panic, the per-module index-skip leaves NO `.meta` and continues the
/// burn-down — never a crash, never a killed worker.
fn index_branch_c(
    shared: &SharedState,
    module: &ModuleFullPath,
    file: &std::path::Path,
    cache_dir: Option<std::path::PathBuf>,
) {
    match checked_typecheck_module(shared, module, file) {
        Ok(Some(entries)) => {
            // Clean check. Write a benign `.meta` (no `.o`, no register_module)
            // so a later real `/import` of this module is a cache-hit (§25.5),
            // built from the typed entries we read out of live before cleanup.
            if let Some(dir) = cache_dir.as_deref() {
                write_index_meta(shared, module, dir, &entries);
            }
            shared
                .importable_indices
                .record_triples(module, entries);
        }
        Ok(None) => {
            // No checkable forms (empty module) — mark indexed, nothing to add.
            shared.importable_indices.mark_skipped(module);
        }
        Err(reason) => {
            // CF.2 / typecheck Err: per-module index-skip. NO `.meta` written
            // (the typecheck never completed). The module is simply absent from
            // results — never a crash, never a killed worker (§25.4).
            if std::env::var("CRANELISP_MODULE_TRACE").is_ok() {
                eprintln!("index: could not index {module}: {reason}");
            }
            shared.importable_indices.mark_skipped(module);
        }
    }
}

/// Write a benign branch-(c) `.meta` for `module` built from its typed public
/// entries — byte-compatible with the real Phase-1 writer's serialised
/// `SymbolTable` (R13/R14). No `.o`. The `.meta` makes a later real `/import` a
/// cache-hit (§25.5). Also records the module's source hash so `is_cache_valid`
/// finds it on the import path.
fn write_index_meta(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &std::path::Path,
    entries: &[(Symbol, Type, ModuleEntry<crate::code::Code>)],
) {
    use cranelisp_backend::cache;
    use cranelisp_types::SymbolTable;

    // Build a fresh SymbolTable carrying the typed entries (the importable
    // public defs). This mirrors what the real path's Phase-1 writer would
    // serialise for this module.
    let mut table: crate::code::SessionSymbolTable =
        SymbolTable::<crate::code::Code, ()>::new_with_params(module.clone());
    for (name, _ty, entry) in entries {
        table.insert(name.clone(), entry.clone());
    }

    let (meta_path, _o) = cache::module_cache_path(cache_dir, module);
    if let Some(parent) = meta_path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    if let Err(e) =
        cache::serialize::write_meta(&meta_path, &table, cache::CACHE_SCHEMA_VERSION)
        && std::env::var("CRANELISP_MODULE_TRACE").is_ok()
    {
        eprintln!("index: .meta write failed for {module}: {}", e.message());
    }
    // Record the source hash + manifest entry so a later real `/import` is a
    // cache-hit on the live import path (§25.5 — index→import cache-hit).
    if let Ok(source) = std::fs::read_to_string(
        crate::pipeline::resolve_module_file(
            module,
            &shared.project_root,
            &shared.lib_dirs.lock().unwrap_or_else(|e| e.into_inner()),
        )
        .unwrap_or_default(),
    ) {
        let hash = cache::manifest::hash_source(&source);
        shared.cache.record_source_hash(module, hash.clone());
        shared
            .cache
            .record_compiled(module, hash, std::collections::HashMap::new());
    }
}

/// Run the real import-installing + typecheck path for `module` over its source,
/// wrapped in CF.2 `catch_unwind` (§25.4 — the nice-worker catch, NOT inherited
/// from the priority worker), then read its typed public entries OUT of live and
/// REMOVE the live residue (R13). Returns:
///   `Ok(Some(entries))` — clean check; entries are `(name, scheme.ty, entry)`.
///   `Ok(None)`          — no checkable forms.
///   `Err(reason)`       — a typecheck error/gap OR a caught panic (0432-shaped).
///
/// The module is NEVER `register_module`'d (no scheduler entry). The four
/// `SharedState` maps are restored to their pre-index state on EVERY path — the
/// session-state-residue invariant (R13).
#[allow(clippy::type_complexity)]
fn checked_typecheck_module(
    shared: &SharedState,
    module: &ModuleFullPath,
    file: &std::path::Path,
) -> Result<Option<Vec<(Symbol, Type, ModuleEntry<crate::code::Code>)>>, String> {
    let source = std::fs::read_to_string(file).map_err(|e| format!("read error: {e}"))?;
    let sexps = cranelisp_frontend::parse(&source).map_err(|e| format!("parse error: {e}"))?;

    // ZERO shared-state mutation (R13 by construction; race-free against the
    // eval thread). The indexer runs the import-install + typecheck against a
    // PRIVATE, isolated symbol-tables map — a shallow snapshot of the live
    // tables for dependency reads (`primitives`, `prelude`, …) plus a fresh
    // entry for the indexed module. The four `SharedState` maps are NEVER
    // written, so there is no residue and no TOCTOU race with a concurrent
    // real `(import …)` of the same module on the eval thread (the prior
    // process_cluster-into-live approach mutated `shared.symbol_tables` and
    // raced — a concurrent eval-thread import of the same module could be
    // clobbered by the indexer's cleanup). Discovery/dependency resolution is
    // read-only against live; all writes land in the private map, dropped at
    // function end.
    let private_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    for entry in shared.symbol_tables.iter() {
        private_tables.insert(entry.key().clone(), entry.value().clone());
    }
    // The indexed module starts FRESH in the private map (Replace semantics —
    // an `import`-only or stale live entry must not shadow the source).
    private_tables.insert(
        module.clone(),
        cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(module.clone()),
    );
    let private_aliases = cranelisp_types::ModuleAliases::default();

    let module_cl = module.clone();

    // CF.2: wrap the whole import+typecheck pass in `catch_unwind` (§25.4 — the
    // nice-worker catch, NOT inherited from the priority worker). A 0432-shaped
    // module (an unannotated multi-clause `defn` tripping a monomorphiser
    // `debug_assert!`) would otherwise kill the nice worker. A caught unwind
    // becomes a clean per-module skip; the worker survives.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        index_typecheck_into_private(
            &private_tables,
            &private_aliases,
            &shared.prelude_fallback,
            &module_cl,
            &sexps,
        )
    }));

    match outcome {
        Ok(Ok(())) => {
            // Read the typed public entries OUT of the PRIVATE module table.
            match private_tables.get(module) {
                Some(t) => {
                    let e = public_entries_with_entry(&t);
                    if e.is_empty() {
                        Ok(None)
                    } else {
                        Ok(Some(e))
                    }
                }
                None => Ok(None),
            }
        }
        Ok(Err(reason)) => Err(reason),
        Err(_panic) => Err("typecheck panicked (skipped)".to_string()),
    }
}

/// Install the module's own `(import …)` decls into the PRIVATE table, then run
/// `check_forms` over the private tables (staging-mode, so the typed defns land
/// in the private module table). Pure with respect to live state — `priv_tables`
/// is the indexer's isolated copy; `prelude_fallback` is read-only.
fn index_typecheck_into_private(
    priv_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    priv_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    sexps: &[cranelisp_types::Sexp],
) -> Result<(), String> {
    use cranelisp_typecheck::SymbolTableAccess;

    // Pass-0 structural peel: extract the module's own import/export decls and
    // install them into the PRIVATE module table (so the body's bare refs
    // resolve). `super` is resolved at the frontend boundary.
    let (decls, remaining) =
        cranelisp_frontend::extract_module_declarations(module, sexps)
            .map_err(|e| format!("structural peel error: {e}"))?;

    crate::imports::install_imports(priv_tables, module, priv_aliases, prelude_fallback, &decls.import_specs)
        .map_err(|e| format!("import install error: {e}"))?;
    crate::imports::install_exports(priv_tables, module, prelude_fallback, &decls.export_specs)
        .map_err(|e| format!("export install error: {e}"))?;

    let program = crate::worker::build_program_compat(&remaining)
        .map_err(|e| format!("build error: {e}"))?;
    let parsed = crate::worker::top_level_to_parsed_entries(&program);
    if parsed.is_empty() {
        return Ok(()); // structural-only / empty module — no checkable defns.
    }

    // Staging-mode `check_forms`: typed entries land in the private module table
    // (the cluster view shadows it). `prelude_fallback` is read-only.
    let mut staging: crate::code::SessionSymbolTable =
        cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(module.clone());
    let mut ctx: SymbolTableAccess<'_, crate::code::Code, ()> =
        SymbolTableAccess::cluster(priv_tables, &mut staging, module.clone());
    let res = cranelisp_typecheck::check_forms(
        parsed,
        &mut ctx,
        priv_tables,
        priv_aliases,
        prelude_fallback,
    );
    drop(ctx);
    match res {
        Ok(_warnings) => {
            // Commit the staged typed entries into the private module table so
            // the caller reads them out (the private table is discarded after).
            if let Some(mut live) = priv_tables.get_mut(module) {
                for (name, entry) in staging.symbols.into_iter() {
                    live.insert(name, entry);
                }
            }
            Ok(())
        }
        Err(e) => Err(format!("typecheck error: {e:?}")),
    }
}

/// Read the PUBLIC, callable entries of a live module table into
/// `(name, scheme.ty, entry-clone)` triples — the importable symbols + their
/// cloned `ModuleEntry` for the `.meta` write. Mirrors
/// `public_entries_from_table` but also clones the entry.
fn public_entries_with_entry(
    table: &crate::code::SessionSymbolTable,
) -> Vec<(Symbol, Type, ModuleEntry<crate::code::Code>)> {
    let mut out = Vec::new();
    for (sym, entry) in table.all_symbols() {
        if matches!(entry, ModuleEntry::Import { .. }) {
            continue;
        }
        if !entry.is_public() {
            continue;
        }
        let name = sym.as_ref();
        if name.contains('$') || name.starts_with("__") {
            continue;
        }
        if let ModuleEntry::Def { scheme, .. } = entry {
            out.push((sym.clone(), scheme.ty.clone(), entry.clone()));
        }
    }
    out
}

/// Read the PUBLIC, callable entries of a (deserialised or staged) symbol table
/// into `(name, scheme.ty)` pairs — the importable symbols. Skips imports,
/// non-public entries, and `$`-mangled internal names (mirrors `/exports`).
fn public_entries_from_table(
    table: &cranelisp_types::SymbolTable<impl cranelisp_types::CodeStore, impl cranelisp_types::LinkerStore>,
) -> Vec<(Symbol, Type)> {
    let mut out = Vec::new();
    for (sym, entry) in table.all_symbols() {
        if matches!(entry, ModuleEntry::Import { .. }) {
            continue;
        }
        if !entry.is_public() {
            continue;
        }
        let name = sym.as_ref();
        if name.contains('$') || name.starts_with("__") {
            continue;
        }
        // Only function/value defs carry a usable scheme for the `:Type` facet.
        if let ModuleEntry::Def { scheme, .. } = entry {
            out.push((sym.clone(), scheme.ty.clone()));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Unit tests (S91 — the seams: indices, name/scheme match, partial-progress,
// arm-idempotence). The three-branch / residue / CF.2 seams are e2e-tested in
// `tests/search.rs` (they need the full session + nice workers + a real
// reachable tree, which the two-tier strategy keeps out of unit scope).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Type;

    fn m(s: &str) -> ModuleFullPath {
        ModuleFullPath::from(s)
    }
    fn sym(s: &str) -> Symbol {
        Symbol::from(s)
    }
    /// `(Fn [Int Int] Int)` — the gcd2 shape.
    fn int_arrow_int() -> Type {
        Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Int),
        )
    }

    // spec: design/int/agent.md §25.3 — Index A name lookup, exact match.
    #[test]
    fn search_by_name_exact_hit() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![(sym("gcd2"), int_arrow_int())]);
        let hits = idx.search_by_name("gcd2");
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].name.as_ref(), "gcd2");
        assert_eq!(hits[0].module.as_ref(), "mathx");
    }

    // spec: design/int/agent.md §25.7 — Index A partial = case-insensitive
    // substring (the §25.7 partial-name rule).
    #[test]
    fn search_by_name_partial_substring_case_insensitive() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![(sym("is-zero"), int_arrow_int())]);
        assert_eq!(idx.search_by_name("ZERO").len(), 1, "case-insensitive substring");
        assert_eq!(idx.search_by_name("is-zero").len(), 1, "exact also matches");
        assert!(idx.search_by_name("nope").is_empty(), "non-substring misses");
    }

    // spec: design/int/agent.md §25.7 — Index B scheme lookup via the typecheck
    // predicates. Exact-shape query matches the same shape.
    #[test]
    fn search_by_scheme_exact_shape() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![(sym("gcd2"), int_arrow_int())]);
        let hits = idx.search_by_scheme(&int_arrow_int());
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].name.as_ref(), "gcd2");
    }

    // spec: design/int/agent.md §25.7 — Index B partial = structural-contains:
    // a bare `Int` query matches a scheme MENTIONING Int (the §25.7 example).
    #[test]
    fn search_by_scheme_partial_contains() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![(sym("gcd2"), int_arrow_int())]);
        let hits = idx.search_by_scheme(&Type::Int);
        assert_eq!(hits.len(), 1, "Int is a sub-structure of (Fn [Int Int] Int)");
    }

    // spec: design/int/agent.md §25.3 — `record_entries` marks the module
    // indexed; the `mark_skipped` (branch a / CF.2 skip) path also marks it,
    // both feeding `pending_count` (the partial-results note signal).
    #[test]
    fn pending_count_tracks_arm_minus_indexed() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("a"), m("b"), m("c")]);
        assert_eq!(idx.pending_count(), 3, "3 enumerated, 0 indexed");
        idx.mark_skipped(&m("a")); // branch-a SKIP
        idx.record_entries(&m("b"), vec![(sym("f"), int_arrow_int())]); // branch b/c
        assert_eq!(idx.pending_count(), 1, "2 of 3 processed");
    }

    // spec: design/int/agent.md §25.5 — arm is REPL-startup-only + idempotent (a
    // second arm is a no-op; the burn-down is armed exactly once).
    #[test]
    fn arm_is_idempotent() {
        let idx = ImportableIndices::default();
        assert!(!idx.is_armed(), "starts unarmed (batch-mode-inert default)");
        idx.arm(vec![m("a"), m("b")]);
        assert!(idx.is_armed());
        assert_eq!(idx.pending_count(), 2);
        idx.arm(vec![m("c"), m("d"), m("e")]); // ignored
        assert_eq!(idx.pending_count(), 2, "second arm is a no-op");
    }

    // spec: design/int/agent.md §25.6 — empty query / no match returns no hits
    // (the caller renders the self-documenting "no importable symbols matched").
    #[test]
    fn no_match_returns_empty() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![(sym("gcd2"), int_arrow_int())]);
        assert!(idx.search_by_name("absent").is_empty());
    }

    // spec: design/int/agent.md §25.3 — a take_index_task drains the worklist in
    // FIFO order; an empty worklist yields None (the nice worker then parks).
    #[test]
    fn take_index_task_drains_fifo_then_none() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("a"), m("b")]);
        assert_eq!(idx.take_index_task().as_ref().map(|m| m.to_string()), Some("a".to_string()));
        assert_eq!(idx.take_index_task().as_ref().map(|m| m.to_string()), Some("b".to_string()));
        assert!(idx.take_index_task().is_none(), "drained → None");
    }
}
