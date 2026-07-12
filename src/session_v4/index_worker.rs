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
    /// The importable-symbol table — one row per indexed public symbol, carrying
    /// the three matchable axes (name / scheme / docstring, §17.19.1). Name,
    /// scheme (exact OR structural-contains via the `cranelisp-typecheck`
    /// predicates, §25.7), and docstring (case-insensitive substring, S106 FIXME
    /// 0540) matching all iterate this single table.
    entries: Vec<IndexedEntry>,
    /// Burn-down progress / skip-state guard: modules already processed (any
    /// branch). Doubles as the worklist-completeness signal.
    indexed: HashSet<ModuleFullPath>,
    /// The `IndexModule` worklist — reachable modules awaiting an index pass.
    /// Separate from the object-codegen worklist (no `.o` entanglement, §25.1).
    /// `None` until the burn-down is armed (REPL-only, R17); `Some(empty)` once
    /// armed-but-drained. `armed` records whether enumeration has happened so a
    /// `--run`/`--link` session that never arms is observably distinct.
    worklist: VecDeque<ModuleFullPath>,
    /// Total module count accounted onto the reachable set (for the
    /// "indexing N modules…" partial-results note, §25.5 / spec §17.19.3). This
    /// counts BOTH the file-resolved worklist modules AND the directly-read
    /// seeded modules (`record_preindexed`), so `pending_count =
    /// enumerated_total − indexed.len()` stays correct: a seeded module is in
    /// both `enumerated_total` and `indexed`, so it is never "pending".
    enumerated_total: usize,
    /// Whether the burn-down has been armed (REPL-startup enumeration ran).
    armed: bool,
    /// Timing (b) gate (spec §17.19.3, S108): set once a "indexing N modules…"
    /// not-ready note has been served to the user this session. The completion
    /// notice (`take_completion_notice`) fires ONLY after a note was shown, so a
    /// session that never saw the index building is never told it finished
    /// (and every non-TTY golden — which never triggers a note — is untouched).
    note_shown: bool,
    /// One-shot completion-notice latch (spec §17.19.3, S108): set the first
    /// time `take_completion_notice` reports completion, so `search index
    /// complete.` is emitted at most once per session.
    announced: bool,
}

impl IndicesInner {
    /// The SINGLE pending-count formula (spec §17.19.3): reachable modules
    /// enumerated onto the reachable set but not yet indexed. Both
    /// `pending_count` (the "indexing N modules…" note) and
    /// `take_completion_notice` (the completion latch) read it, so the two
    /// accounting sites share ONE source of truth and cannot drift (S-1).
    fn pending(&self) -> usize {
        self.enumerated_total.saturating_sub(self.indexed.len())
    }
}

/// One indexed importable symbol — the three matchable axes plus its origin.
#[derive(Debug, Clone)]
struct IndexedEntry {
    name: Symbol,
    module: ModuleFullPath,
    scheme: Type,
    /// The symbol's docstring text (the same text `/doc` shows), for the
    /// docstring axis (§17.19.1, S106) and the excerpt facet (§17.19.2 facet 5).
    docstring: Option<String>,
}

/// Relevance tier of a `/search` hit — the §17.19.1a total order, strongest
/// first. `Ord` sorts stronger (lower discriminant) before weaker so the ranking
/// is a plain `sort_by_key`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum MatchTier {
    /// 1 — the query equals the symbol name exactly.
    ExactName = 1,
    /// 2 — the query type-shape matches the scheme up to alpha-renaming.
    ExactScheme = 2,
    /// 3 — the symbol name starts with the query.
    PrefixName = 3,
    /// 4 — the query appears elsewhere inside the symbol name.
    SubstringName = 4,
    /// 5 — the query type-shape is a sub-structure of the scheme.
    StructuralScheme = 5,
    /// 6 — the query matched ONLY in the docstring (name/scheme did not match).
    DocstringOnly = 6,
}

/// One result row of a `/search` (the facets of spec §17.19.2 + its ranking
/// tier §17.19.1a).
#[derive(Debug, Clone)]
pub(crate) struct SearchHit {
    pub name: Symbol,
    pub module: ModuleFullPath,
    /// The matched signature, for the `:Type` facet.
    pub scheme: Type,
    /// The symbol's docstring, for the excerpt facet on a docstring-only hit.
    pub docstring: Option<String>,
    /// Which axis/strength this hit matched on (§17.19.1a).
    pub tier: MatchTier,
}

impl ImportableIndices {
    /// True once the burn-down has been armed (REPL-startup enumeration ran).
    pub(crate) fn is_armed(&self) -> bool {
        self.inner.lock().unwrap_or_else(|e| e.into_inner()).armed
    }

    /// Number of reachable modules NOT yet indexed — the "indexing N modules…"
    /// partial-results count (0 ⇒ burn-down complete).
    pub(crate) fn pending_count(&self) -> usize {
        self.inner.lock().unwrap_or_else(|e| e.into_inner()).pending()
    }

    /// Latch that a "indexing N modules…" not-ready note was served this
    /// session (spec §17.19.3, timing (b)) — the gate for the completion
    /// notice. Called by `/search` (`repl.rs::handle_search`) whenever it
    /// appends the not-ready note (`pending_count > 0`).
    pub(crate) fn mark_note_shown(&self) {
        self.inner.lock().unwrap_or_else(|e| e.into_inner()).note_shown = true;
    }

    /// The one-shot `search index complete.` completion latch (spec §17.19.3,
    /// timing (b), S108). Under the single mutex, a check-and-set that returns
    /// `true` EXACTLY ONCE — when ALL of:
    ///   - the burn-down is `armed` and complete (`pending_count == 0`),
    ///   - a not-ready note was shown this session (`note_shown`, timing (b)),
    ///   - it has not already been announced (`!announced`).
    ///
    /// On the firing call it sets `announced`, so every later call returns
    /// `false`. Polled by the `main.rs` REPL read loop at the clean prompt
    /// boundary (single-writer — no worker-side stdout).
    pub(crate) fn take_completion_notice(&self) -> bool {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let complete = g.armed && g.pending() == 0;
        if complete && g.note_shown && !g.announced {
            g.announced = true;
            true
        } else {
            false
        }
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
        let before = g.worklist.len();
        for m in modules {
            if !g.indexed.contains(&m) {
                g.worklist.push_back(m);
            }
        }
        // ACCUMULATE (not assign): a seeded module already accounted by
        // `record_preindexed` before `arm` must not be wiped by an assignment,
        // and its file duplicate is already dropped by the `!indexed.contains`
        // guard above — so the arm-vs-preindex call order no longer matters
        // (S-1 order-independence). `arm` runs at most once (the `armed` guard),
        // so this adds the freshly-enumerated file modules exactly once.
        g.enumerated_total += g.worklist.len() - before;
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

    /// Record the public entries of `module` into the index and mark it indexed.
    /// Each `(name, scheme.ty, docstring)` is one importable symbol.
    fn record_entries(&self, module: &ModuleFullPath, entries: Vec<(Symbol, Type, Option<String>)>) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        for (name, scheme, docstring) in entries {
            g.entries.push(IndexedEntry {
                name,
                module: module.clone(),
                scheme,
                docstring,
            });
        }
        g.indexed.insert(module.clone());
    }

    /// Record a **built-in seeded** module's public symbols (spec §17.19 R10,
    /// S108) read DIRECTLY from the live symbol table, accounting for it in BOTH
    /// `enumerated_total` AND `indexed` atomically under the one mutex. This is
    /// the sibling of `record_entries` for the seeded feed: seeded modules are
    /// already typechecked-and-mounted, so they are indexed SYNCHRONOUSLY at arm
    /// time — never staged, never a `.meta`, never on the worklist, and never
    /// "pending". Counting the module in `enumerated_total` as well as `indexed`
    /// is load-bearing: if it landed only in `indexed`, `pending_count =
    /// enumerated_total − indexed.len()` would UNDERCOUNT N (and the not-ready
    /// note + completion notice would fire early). Idempotent: a re-add of an
    /// already-indexed module is a no-op (no double count, no duplicate rows).
    fn record_preindexed(
        &self,
        module: &ModuleFullPath,
        entries: Vec<(Symbol, Type, Option<String>)>,
    ) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        if !g.indexed.insert(module.clone()) {
            return; // already indexed — do not double-count or double-push.
        }
        g.enumerated_total += 1;
        for (name, scheme, docstring) in entries {
            g.entries.push(IndexedEntry {
                name,
                module: module.clone(),
                scheme,
                docstring,
            });
        }
    }

    /// `record_entries` variant taking the `.meta`-write triple
    /// `(name, scheme.ty, entry)` — reads the docstring off the entry's
    /// `ModuleEntry::Def.docstring` (the docstring axis, S106) then records
    /// `(name, ty, docstring)`.
    fn record_triples(
        &self,
        module: &ModuleFullPath,
        entries: Vec<(Symbol, Type, ModuleEntry<crate::code::Code>)>,
    ) {
        let rows: Vec<(Symbol, Type, Option<String>)> = entries
            .into_iter()
            .map(|(n, t, e)| {
                let doc = match &e {
                    ModuleEntry::Def { docstring, .. } => docstring.clone(),
                    _ => None,
                };
                (n, t, doc)
            })
            .collect();
        self.record_entries(module, rows);
    }

    /// Search by NAME — exact OR case-insensitive substring (§25.7 partial
    /// name), each hit carrying its §17.19.1a tier (exact/prefix/substring).
    pub(crate) fn search_by_name(&self, query: &str) -> Vec<SearchHit> {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let lc = query.to_lowercase();
        let mut hits = Vec::new();
        for e in &g.entries {
            if let Some(tier) = name_match_tier(e.name.as_ref(), &lc) {
                hits.push(e.hit(tier));
            }
        }
        hits
    }

    /// Search by DOCSTRING — case-insensitive substring against the symbol's
    /// docstring text (§17.19.1, S106 FIXME 0540). Every hit is a
    /// `DocstringOnly` candidate; the caller merges with name hits and keeps the
    /// stronger tier when a symbol matches on both axes (§17.19.1a tier 6).
    pub(crate) fn search_by_docstring(&self, query: &str) -> Vec<SearchHit> {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let lc = query.to_lowercase();
        let mut hits = Vec::new();
        for e in &g.entries {
            if let Some(doc) = &e.docstring
                && doc.to_lowercase().contains(&lc)
            {
                hits.push(e.hit(MatchTier::DocstringOnly));
            }
        }
        hits
    }

    /// Search by SCHEME — exact OR partial (structural-contains), calling the
    /// `cranelisp-typecheck` predicates (§25.7). int CALLS them; does not own
    /// them. Exact matches carry `ExactScheme`, structural-contains matches
    /// `StructuralScheme` (§17.19.1a tiers 2/5).
    pub(crate) fn search_by_scheme(&self, query: &Type) -> Vec<SearchHit> {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let mut hits = Vec::new();
        for e in &g.entries {
            let tier = if cranelisp_typecheck::signature_matches_exact(query, &e.scheme) {
                Some(MatchTier::ExactScheme)
            } else if cranelisp_typecheck::signature_matches_partial(query, &e.scheme) {
                Some(MatchTier::StructuralScheme)
            } else {
                None
            };
            if let Some(tier) = tier {
                hits.push(e.hit(tier));
            }
        }
        hits
    }
}

impl IndexedEntry {
    /// Build a `SearchHit` for this entry at the given relevance tier.
    fn hit(&self, tier: MatchTier) -> SearchHit {
        SearchHit {
            name: self.name.clone(),
            module: self.module.clone(),
            scheme: self.scheme.clone(),
            docstring: self.docstring.clone(),
            tier,
        }
    }
}

/// The §17.19.1a name-axis tier for `name` against a lowercased `query`:
/// exact → `ExactName`, prefix → `PrefixName`, interior substring →
/// `SubstringName`, no match → `None`. Case-insensitive throughout (the name
/// axis is case-insensitive, §17.19.1).
fn name_match_tier(name: &str, query_lc: &str) -> Option<MatchTier> {
    let nl = name.to_lowercase();
    if nl == query_lc {
        Some(MatchTier::ExactName)
    } else if nl.starts_with(query_lc) {
        Some(MatchTier::PrefixName)
    } else if nl.contains(query_lc) {
        Some(MatchTier::SubstringName)
    } else {
        None
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

    // The built-in SEEDED modules (spec §17.19 R10, S108) are indexed below by a
    // DIRECT read, NOT via the file worklist. Filter their names OUT of the
    // enumerated `.cl` set FIRST so the two feeds are DISJOINT by construction
    // (Principle 18 — enforce invariants structurally): a user file named
    // `primitives.cl`/`macros.cl` on the project root or a lib-dir must not enter
    // the worklist AND be counted a second time by `record_preindexed`. That
    // double-count (I-1) left `pending_count ≥ 1` forever — `search index
    // complete.` never fired and every `/search` showed a perpetual
    // `indexing 1 module(s)…` note. The seeded module WINS: it is already
    // typechecked-and-mounted, so a same-named file is dropped from the file set.
    let seeded_modules = crate::bootstrap::seeded_importable_modules();
    modules.retain(|m| !seeded_modules.contains(m));

    shared.importable_indices.arm(modules);

    // Index the built-in SEEDED modules by a DIRECT read of their public symbols
    // straight from the live session symbol table. These modules (`primitives`,
    // seeded `macros`) have NO `.cl` file and are already typechecked-and-mounted,
    // so they BYPASS the typecheck-to-index-then-discard file dance entirely
    // (branches a/b/c) — nothing to stage, nothing to discard, no `.meta`.
    // `record_preindexed` counts each in BOTH `enumerated_total` and `indexed`
    // (see its doc) so seeded modules are never "pending". The seeded list is
    // sourced from `bootstrap::seeded_importable_modules()` — the single source of
    // what bootstrap mounts (Principle 19), not a name-literal here.
    for module in &seeded_modules {
        if let Some(table) = shared.symbol_tables.get(module) {
            let entries = public_entries_from_table(table.value());
            shared.importable_indices.record_preindexed(module, entries);
        }
    }

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
) -> Option<Vec<(Symbol, Type, Option<String>)>> {
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
/// into `(name, scheme.ty, docstring)` triples — the importable symbols. Skips
/// imports, non-public entries, and `$`-mangled internal names (mirrors
/// `/exports`). The docstring feeds the §17.19.1 docstring axis (S106).
fn public_entries_from_table(
    table: &cranelisp_types::SymbolTable<impl cranelisp_types::CodeStore, impl cranelisp_types::LinkerStore>,
) -> Vec<(Symbol, Type, Option<String>)> {
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
        if let ModuleEntry::Def { scheme, docstring, .. } = entry {
            out.push((sym.clone(), scheme.ty.clone(), docstring.clone()));
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
    /// A `(name, scheme, no-docstring)` row for the common test case.
    fn row(name: &str, ty: Type) -> (Symbol, Type, Option<String>) {
        (sym(name), ty, None)
    }
    /// A `(name, scheme, docstring)` row for the docstring-axis tests.
    fn row_doc(name: &str, ty: Type, doc: &str) -> (Symbol, Type, Option<String>) {
        (sym(name), ty, Some(doc.to_string()))
    }

    // spec: design/int/agent.md §25.3 — Index A name lookup, exact match. An
    // exact hit carries the ExactName tier (§17.19.1a tier 1).
    #[test]
    fn search_by_name_exact_hit() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![row("gcd2", int_arrow_int())]);
        let hits = idx.search_by_name("gcd2");
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].name.as_ref(), "gcd2");
        assert_eq!(hits[0].module.as_ref(), "mathx");
        assert_eq!(hits[0].tier, MatchTier::ExactName);
    }

    // spec: design/int/agent.md §25.7 — Index A partial = case-insensitive
    // substring (the §25.7 partial-name rule).
    #[test]
    fn search_by_name_partial_substring_case_insensitive() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![row("is-zero", int_arrow_int())]);
        assert_eq!(idx.search_by_name("ZERO").len(), 1, "case-insensitive substring");
        assert_eq!(idx.search_by_name("is-zero").len(), 1, "exact also matches");
        assert!(idx.search_by_name("nope").is_empty(), "non-substring misses");
    }

    // spec: repl/spec.md §17.19.1a — the name axis assigns exact/prefix/substring
    // tiers (1/3/4). `beta` is exact, `beta-gamma` is a prefix, `alpha-beta` is an
    // interior substring.
    #[test]
    fn search_by_name_assigns_exact_prefix_substring_tiers() {
        let idx = ImportableIndices::default();
        idx.record_entries(
            &m("g"),
            vec![
                row("beta", int_arrow_int()),
                row("beta-gamma", int_arrow_int()),
                row("alpha-beta", int_arrow_int()),
            ],
        );
        let hits = idx.search_by_name("beta");
        let tier_of = |n: &str| hits.iter().find(|h| h.name.as_ref() == n).map(|h| h.tier);
        assert_eq!(tier_of("beta"), Some(MatchTier::ExactName));
        assert_eq!(tier_of("beta-gamma"), Some(MatchTier::PrefixName));
        assert_eq!(tier_of("alpha-beta"), Some(MatchTier::SubstringName));
    }

    // spec: repl/spec.md §17.19.1 — the docstring axis (S106 FIXME 0540): a query
    // that appears only in the docstring surfaces the symbol at DocstringOnly tier;
    // a symbol with no docstring cannot match; a non-substring query misses.
    #[test]
    fn search_by_docstring_substring_hit_and_misses() {
        let idx = ImportableIndices::default();
        idx.record_entries(
            &m("docmod"),
            vec![
                row_doc("gcd2", int_arrow_int(), "greatest common divisor of two ints"),
                row("no-doc", int_arrow_int()), // no docstring — cannot match
            ],
        );
        let hits = idx.search_by_docstring("DIVISOR"); // case-insensitive
        assert_eq!(hits.len(), 1, "only the docstring-bearing hit matches");
        assert_eq!(hits[0].name.as_ref(), "gcd2");
        assert_eq!(hits[0].tier, MatchTier::DocstringOnly);
        assert!(
            idx.search_by_docstring("absent-text").is_empty(),
            "a non-substring docstring query misses"
        );
    }

    // spec: design/int/agent.md §25.7 — Index B scheme lookup via the typecheck
    // predicates. Exact-shape query matches the same shape at ExactScheme tier.
    #[test]
    fn search_by_scheme_exact_shape() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![row("gcd2", int_arrow_int())]);
        let hits = idx.search_by_scheme(&int_arrow_int());
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].name.as_ref(), "gcd2");
        assert_eq!(hits[0].tier, MatchTier::ExactScheme);
    }

    // spec: design/int/agent.md §25.7 — Index B partial = structural-contains:
    // a bare `Int` query matches a scheme MENTIONING Int (the §25.7 example) at
    // the StructuralScheme tier (§17.19.1a tier 5).
    #[test]
    fn search_by_scheme_partial_contains() {
        let idx = ImportableIndices::default();
        idx.record_entries(&m("mathx"), vec![row("gcd2", int_arrow_int())]);
        let hits = idx.search_by_scheme(&Type::Int);
        assert_eq!(hits.len(), 1, "Int is a sub-structure of (Fn [Int Int] Int)");
        assert_eq!(hits[0].tier, MatchTier::StructuralScheme);
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
        idx.record_entries(&m("b"), vec![row("f", int_arrow_int())]); // branch b/c
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
        idx.record_entries(&m("mathx"), vec![row("gcd2", int_arrow_int())]);
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

    // =======================================================================
    // S108 (Increment 2) — seeded-module direct-read accounting (E1) +
    // indexing-lifecycle latches (E2). The e2e harness cannot deterministically
    // hold the burn-down open (tests/search.rs FIXME(/testing)), so E2 is pinned
    // HERE at the `IndicesInner` seam, where it IS deterministic.
    // =======================================================================
    use cranelisp_types::{DefKind, Scheme, Visibility};

    /// A live symbol table for `module` carrying one PUBLIC `Def` named `name`
    /// with scheme `ty` — the seeded-module shape `arm_burndown` direct-reads.
    fn public_def_table(module: &str, name: &str, ty: Type) -> crate::code::SessionSymbolTable {
        let mut table = crate::code::SessionSymbolTable::new_with_params(m(module));
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty,
        };
        table.insert(
            sym(name),
            ModuleEntry::def(scheme, DefKind::PrimitiveExtern)
                .visibility(Visibility::Public)
                .build(),
        );
        table
    }

    // spec: repl/spec.md §17.19.3 — `record_preindexed` accounting: a seeded
    // module recorded at arm time is counted in BOTH `enumerated_total` AND
    // `indexed`, so it is NEVER "pending". After arming with K file modules plus
    // the seeded modules, `pending_count == K`; after the K file modules burn
    // down, `pending_count == 0`. (If a seeded module landed only in `indexed`,
    // N would undercount and completion would fire early.)
    #[test]
    fn record_preindexed_counts_seeded_in_both_tallies() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("a"), m("b"), m("c")]); // K = 3 file modules
        // Seeded modules recorded synchronously at arm time (direct read).
        idx.record_preindexed(&m("primitives"), vec![row("vec-len", int_arrow_int())]);
        idx.record_preindexed(&m("macros"), vec![row("sconcat", int_arrow_int())]);
        assert_eq!(
            idx.pending_count(),
            3,
            "seeded modules are indexed synchronously — only the 3 file modules pend"
        );
        // Burn down the three file modules (skip / record).
        idx.mark_skipped(&m("a"));
        idx.record_entries(&m("b"), vec![row("f", int_arrow_int())]);
        idx.record_entries(&m("c"), vec![row("g", int_arrow_int())]);
        assert_eq!(idx.pending_count(), 0, "after burn-down nothing is pending");
    }

    // spec: repl/spec.md §17.19.3 — `record_preindexed` is idempotent: a re-add
    // of an already-indexed seeded module neither double-counts `enumerated_total`
    // nor double-pushes its rows.
    #[test]
    fn record_preindexed_is_idempotent() {
        let idx = ImportableIndices::default();
        idx.arm(vec![]); // 0 file modules
        idx.record_preindexed(&m("primitives"), vec![row("vec-len", int_arrow_int())]);
        idx.record_preindexed(&m("primitives"), vec![row("vec-len", int_arrow_int())]);
        assert_eq!(idx.pending_count(), 0, "still complete, no double count");
        assert_eq!(
            idx.search_by_name("vec-len").len(),
            1,
            "the seeded symbol is indexed exactly once, not duplicated"
        );
    }

    // spec: repl/spec.md §17.19.3 (timing (b), S108) — `take_completion_notice`
    // is a one-shot check-and-set gated on `note_shown`: it fires `true` exactly
    // once when `armed && pending==0 && note_shown`, returns `false` when no
    // not-ready note was shown (timing (b)), and `false` on every later call.
    #[test]
    fn take_completion_notice_one_shot_gated_on_note_shown() {
        let idx = ImportableIndices::default();
        // Unarmed → never fires (nothing to complete).
        assert!(!idx.take_completion_notice(), "unarmed → no completion notice");
        idx.arm(vec![]); // armed, 0 file modules
        idx.record_preindexed(&m("primitives"), vec![row("vec-len", int_arrow_int())]);
        // Armed + complete, but NO not-ready note shown → timing (b) suppresses.
        assert!(
            !idx.take_completion_notice(),
            "no `indexing N…` note shown this session → completion suppressed (timing b)"
        );
        idx.mark_note_shown();
        assert!(
            idx.take_completion_notice(),
            "armed + complete + note shown → fires"
        );
        assert!(
            !idx.take_completion_notice(),
            "one-shot: the second call is false"
        );
    }

    // spec: repl/spec.md §17.19.3 — the completion notice requires the burn-down
    // to be COMPLETE: with a not-ready note already shown but modules still
    // pending, `take_completion_notice` is `false`; it fires only once the last
    // module drains to zero.
    #[test]
    fn take_completion_notice_requires_pending_zero() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("a")]); // one pending file module
        idx.mark_note_shown();
        assert!(
            !idx.take_completion_notice(),
            "still pending → not complete → no completion notice"
        );
        idx.mark_skipped(&m("a")); // drain the last module
        assert!(
            idx.take_completion_notice(),
            "now complete + note shown → fires once"
        );
        assert!(!idx.take_completion_notice(), "one-shot");
    }

    // spec: repl/spec.md §17.19.3 (S108, I-1) — a seeded-named file collision
    // must NOT double-count. `arm_burndown` filters the seeded names out of the
    // file worklist so the two feeds are disjoint; the `IndicesInner` accounting
    // is ALSO order-independent (S-1), so even if a seeded module is recorded
    // BEFORE `arm` enumerates a same-named file, the `!indexed.contains` guard
    // drops the file duplicate and the seeded module is counted EXACTLY ONCE.
    // Without both, `pending_count` sticks ≥ 1 forever (completion never fires,
    // every `/search` shows a perpetual `indexing 1 module(s)…` note).
    #[test]
    fn seeded_name_file_collision_counts_once_and_completes() {
        let idx = ImportableIndices::default();
        // Seeded module recorded FIRST (direct read), so `macros` is in `indexed`
        // before `arm` sees a same-named file — the order-independent path.
        idx.record_preindexed(&m("macros"), vec![row("sconcat", int_arrow_int())]);
        // `arm` enumerates a file worklist that COLLIDES on `macros` (a user
        // `macros.cl`) plus one genuine file module `a`. The `!indexed.contains`
        // guard drops the `macros` duplicate; only `a` is added to the worklist.
        idx.arm(vec![m("macros"), m("a")]);
        assert_eq!(
            idx.pending_count(),
            1,
            "seeded `macros` counted once (not twice) — only the file module `a` pends"
        );
        idx.mark_note_shown(); // a `/search` served the not-ready note this session
        // Burn down the one genuine file module.
        idx.record_entries(&m("a"), vec![row("f", int_arrow_int())]);
        assert_eq!(idx.pending_count(), 0, "no perpetual pending — burn-down completes");
        assert!(
            idx.take_completion_notice(),
            "completion fires once the file module drains (the collision no longer wedges it)"
        );
        assert_eq!(
            idx.search_by_name("sconcat").len(),
            1,
            "the seeded symbol is indexed exactly once, not duplicated"
        );
    }

    // spec: repl/spec.md §17.19 R10 (S108) — a seeded module's PUBLIC symbols,
    // read directly from the live symbol table (as `arm_burndown` does) via
    // `public_entries_from_table` + `record_preindexed`, land in the index: a
    // `vec-len`-shaped lookup hits `primitives` at the ExactName tier.
    #[test]
    fn seeded_public_symbols_land_in_index() {
        let table = public_def_table("primitives", "vec-len", int_arrow_int());
        let entries = public_entries_from_table(&table);
        assert_eq!(entries.len(), 1, "the public Def is extracted");
        let idx = ImportableIndices::default();
        idx.record_preindexed(&m("primitives"), entries);
        let hits = idx.search_by_name("vec-len");
        assert_eq!(hits.len(), 1, "the seeded primitive is searchable");
        assert_eq!(hits[0].name.as_ref(), "vec-len");
        assert_eq!(hits[0].module.as_ref(), "primitives");
        assert_eq!(hits[0].tier, MatchTier::ExactName);
    }
}
