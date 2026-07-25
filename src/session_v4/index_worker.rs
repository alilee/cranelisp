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
// IN-MEMORY ISOLATION (S91, `design/int/index-worker-isolation.md` §3.1): the
// index typecheck runs entirely against a function-local PRIVATE substrate (a
// deep-cloned `symbol_tables` snapshot + fresh aliases + a private
// prelude-fallback snapshot, §3.2), so the live `SharedState` maps are
// byte-unchanged BY CONSTRUCTION — there is no residue to remove (the retired
// "typecheck-into-live then REMOVE the residue (R13)" model). The feed's
// primary output is the in-memory `importable_indices` rows.
//
// The DISK cache half (the §25.5 index→import `.meta` cache-hit) is NOT yet
// severed: branch (c) still writes a benign `.meta` + manifest entry. Its
// retirement is proposed by `index-worker-isolation.md` §3.3 but is DEFERRED —
// it (a) does NOT fix the FIXME-0604 phantom (the index feed is inert under the
// `--run` recipe; the writer is FOREGROUND — re-scoped, see 0604's S110
// disposition) and (b) breaks the committed §25.5 e2e pins in `tests/search.rs`,
// so the §25.5 retirement must be a /design-coordinated wave (agent.md §25 +
// /qa test updates), not a unilateral /dev severance (FIXME 0626).
//
// The three per-module branches (§25.1):
//   (a) module present in the scheduler ModuleState registry  -> read its rows
//       from the LIVE table (E3 loaded-module feed) or skip (row-less).
//   (b) valid `.meta` (schema+BUILD_ID gate AND int's source-content gate)
//       -> deserialise the SymbolTable, read its public entries, NO typecheck.
//   (c) no/stale `.meta`  -> typecheck once on the nice worker against the
//       PRIVATE substrate, wrapped in CF.2 `catch_unwind`, read public entries
//       out of the private snapshot, then write a benign `.meta` (§25.5; no
//       `.o`, no `register_module`).
//
// REPL-only by construction (R17): the worklist is enumerated ONLY at REPL
// startup (`arm_burndown`); `--run`/`--link`/`--release` never enumerate it, so
// no index pass runs and no `.meta` is ever read or written in batch modes.
//
// Abandon-on-flush/shutdown (R18): the burn-down is best-effort warm-up, never a
// correctness obligation. Index work yields to object codegen and is never
// drained-to-completion at a flush; the loop checks the shutdown flag between
// `IndexModule` tasks.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Mutex;

use cranelisp_types::{DefKind, ModuleEntry, ModuleFullPath, Symbol, Type};

use super::SharedState;
use crate::scheduler::ModulePool;

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
    /// The modules `arm` counted onto `enumerated_total` via the FILE worklist
    /// (E3 loaded-module feed, `resolve-home-enumeration.md` §4). A loaded module
    /// recorded through `record_loaded_replace` uses this to decide its tally
    /// shape: a file-enumerated module was already counted by `arm` (single-tally
    /// — no bump), a module OUTSIDE the file set (a late `/import` of a
    /// non-lib-path module) takes the `record_preindexed` dual-tally shape. Held
    /// so `pending_count = enumerated_total − indexed.len()` stays exact once the
    /// loaded feed lands rows for a module the file worklist also enumerated.
    file_enumerated: HashSet<ModuleFullPath>,
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
    /// Full paths of PRIVATE `(mod- X)` submodules — hence their whole subtrees —
    /// declared by any module enumerated at arm time (`private_submodule_paths`,
    /// §8.2.3, 0570). A `/search` hit whose HOME lies within one of these subtrees
    /// is surfaced ONLY to a searcher whose current module also lies within the
    /// SAME subtree (`search_visible_from`). This is the SINGLE privacy
    /// enforcement point over the ASSEMBLED index — the only place that sees the
    /// searcher's module — so it covers EVERY feed uniformly (file worklist,
    /// seeded, AND the loaded-module E3 feed), closing the 0570 residual where a
    /// LOADED private submodule (`user.test`) bypassed the arm-time file-worklist
    /// drop and leaked to an outside-subtree searcher.
    private_roots: HashSet<ModuleFullPath>,
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
    /// Whether the entry is a macro (`DefKind::Macro`) — carries the §1.1
    /// classification through the index so a `/search` row renders the canonical
    /// macro envelope (`; defmacro`), never a placeholder scalar `:Type`
    /// (§17.19.2a, 0569). The index is the authority; the renderer never
    /// re-probes the live table (an importable-but-unloaded module has no live
    /// entry to consult).
    is_macro: bool,
}

/// One importable symbol's index payload — the projection
/// `public_entries_from_table` (and the branch-c `record_triples`) hand the
/// recorders. A named row (not a bare tuple, `src/CLAUDE.md`) so the §1.1
/// classification (`is_macro`) rides alongside the scheme/docstring rather than
/// being re-derived at render time.
#[derive(Debug, Clone)]
struct ImportableRow {
    name: Symbol,
    scheme: Type,
    docstring: Option<String>,
    is_macro: bool,
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
    /// Whether the hit is a macro — drives the `; defmacro` canonical envelope
    /// on the row's primary line (§17.19.2a, 0569).
    pub is_macro: bool,
}

impl ImportableIndices {
    /// True once the burn-down has been armed (REPL-startup enumeration ran).
    pub(crate) fn is_armed(&self) -> bool {
        self.inner.lock().unwrap_or_else(|e| e.into_inner()).armed
    }

    /// Number of reachable modules NOT yet indexed — the "indexing N modules…"
    /// partial-results count (0 ⇒ burn-down complete).
    pub(crate) fn pending_count(&self) -> usize {
        self.inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .pending()
    }

    /// Latch that a "indexing N modules…" not-ready note was served this
    /// session (spec §17.19.3, timing (b)) — the gate for the completion
    /// notice. Called by `/search` (`repl.rs::handle_search`) whenever it
    /// appends the not-ready note (`pending_count > 0`).
    pub(crate) fn mark_note_shown(&self) {
        self.inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .note_shown = true;
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

    /// Record the PRIVATE `(mod- X)` submodule roots (`private_submodule_paths`)
    /// so the search-time §8.2.3 subtree-visibility filter (`search_visible_from`)
    /// can consult them. Merges into any prior set (idempotent; `arm` runs once).
    pub(crate) fn record_private_roots(&self, roots: HashSet<ModuleFullPath>) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        g.private_roots.extend(roots);
    }

    /// §8.2.3 subtree visibility: may a symbol whose HOME is `home` be surfaced by
    /// `/search` to a searcher whose current module is `searcher`? A symbol inside
    /// a private-submodule subtree (`home` within some `private_roots` entry) is
    /// visible ONLY when `searcher` is also inside that SAME subtree; every other
    /// symbol is unconditionally visible. The declared-`mod-`-bit filter, NOT a
    /// name probe (Principle 19) — mirrors the load-time import filter
    /// (`imports::is_in_subtree`), applied here to the assembled index so no feed
    /// can leak a private submodule to an outside-subtree searcher (0570 residual).
    pub(crate) fn search_visible_from(
        &self,
        home: &ModuleFullPath,
        searcher: &ModuleFullPath,
    ) -> bool {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        g.private_roots
            .iter()
            .all(|p| !path_in_subtree(home, p) || path_in_subtree(searcher, p))
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
                // Record the file-enumerated set so the E3 loaded-module feed
                // single-tallies a module the file worklist also enumerated.
                g.file_enumerated.insert(m.clone());
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
    fn record_entries(&self, module: &ModuleFullPath, entries: Vec<ImportableRow>) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        for ImportableRow {
            name,
            scheme,
            docstring,
            is_macro,
        } in entries
        {
            g.entries.push(IndexedEntry {
                name,
                module: module.clone(),
                scheme,
                docstring,
                is_macro,
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
    fn record_preindexed(&self, module: &ModuleFullPath, entries: Vec<ImportableRow>) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        if !g.indexed.insert(module.clone()) {
            return; // already indexed — do not double-count or double-push.
        }
        g.enumerated_total += 1;
        for ImportableRow {
            name,
            scheme,
            docstring,
            is_macro,
        } in entries
        {
            g.entries.push(IndexedEntry {
                name,
                module: module.clone(),
                scheme,
                docstring,
                is_macro,
            });
        }
    }

    /// Record — or REPLACE — a mounted/loaded module's public symbols read
    /// DIRECTLY from the live symbol table (E3, spec §17.19 R10;
    /// `resolve-home-enumeration.md` §4). The loaded-module feed, used by three
    /// call sites uniformly: the arm-time sweep (already-terminal registered
    /// modules), the per-worklist branch (a) (a registered module popped in a
    /// terminal state), and the publication-edge hook (`on_module_published` — a
    /// module reaching terminal AFTER arm: late `/import`, watcher reload).
    ///
    /// REPLACE-rows refresh semantics: existing `IndexedEntry` rows for `module`
    /// are dropped before the new set is inserted, so a watcher reload or REPL
    /// redefinition neither duplicates nor stale-serves rows.
    ///
    /// Accounting (the §4 dual-tally invariant, guarded by unit scenarios per
    /// Principle 23): `module` is counted in `enumerated_total` at MOST once,
    /// atomically under the one mutex. A module already on the file worklist
    /// (`file_enumerated`) was counted by `arm` — the single-tally path, no bump.
    /// A module OUTSIDE the file-enumerated set (a late import of a non-lib-path
    /// module) takes the `record_preindexed` dual-tally shape: its first record
    /// bumps `enumerated_total` so `pending_count = enumerated_total −
    /// indexed.len()` stays ≥ 0 and reaches 0. Idempotent on both tallies across
    /// re-records (a re-record neither double-counts nor double-pushes).
    fn record_loaded_replace(&self, module: &ModuleFullPath, entries: Vec<ImportableRow>) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        // REPLACE: drop any existing rows for this module first (refresh).
        g.entries.retain(|e| &e.module != module);
        for ImportableRow {
            name,
            scheme,
            docstring,
            is_macro,
        } in entries
        {
            g.entries.push(IndexedEntry {
                name,
                module: module.clone(),
                scheme,
                docstring,
                is_macro,
            });
        }
        // Tally the module EXACTLY once. A first-time record of a module outside
        // the file-enumerated set is dual-tallied (enumerated_total + indexed); a
        // file-enumerated module was already counted by `arm` (single-tally). A
        // re-record (already indexed) touches neither tally.
        let newly_indexed = g.indexed.insert(module.clone());
        if newly_indexed && !g.file_enumerated.contains(module) {
            g.enumerated_total += 1;
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
        let rows: Vec<ImportableRow> = entries
            .into_iter()
            .map(|(name, scheme, e)| {
                let (docstring, is_macro) = match &e {
                    ModuleEntry::Def {
                        docstring, kind, ..
                    } => (
                        docstring.clone(),
                        matches!(kind.as_ref(), DefKind::Macro { .. }),
                    ),
                    _ => (None, false),
                };
                ImportableRow {
                    name,
                    scheme,
                    docstring,
                    is_macro,
                }
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
            is_macro: self.is_macro,
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

    // §8.2.3 (0570): a `(mod- X)` PRIVATE submodule — and its whole subtree — is
    // NOT importable from outside its parent, so its symbols MUST NOT enter the
    // `/search` index (surfacing one with an `(import …)` hint advertises exactly
    // what §8.2.3 forbids). Privacy is the PARENT-declared `ModDecl.visibility`
    // bit (Principle 19 — a declared module attribute, read here via a cheap
    // syntactic scan of each enumerated file), NEVER a `.test`/name heuristic.
    // Drop every enumerated module that IS a private submodule or a DESCENDANT of
    // one. The import path enforces the same rule at load time
    // (`check_private_submodule_import`); this is the index-surface half.
    let private_roots = private_submodule_paths(&modules, &shared.project_root, &lib_dirs);
    // Record the roots so the SEARCH-time §8.2.3 subtree-visibility filter
    // (`search_visible_from`) can enforce privacy over the ASSEMBLED index — the
    // single point that sees the searcher's module, so it covers the loaded-module
    // E3 feed too (a LOADED private submodule bypasses the file-worklist drop
    // below; that was the 0570 residual leak).
    shared
        .importable_indices
        .record_private_roots(private_roots.clone());
    if !private_roots.is_empty() {
        modules.retain(|m| !private_roots.iter().any(|p| path_in_subtree(m, p)));
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

    // E3 (spec §17.19 R10, `resolve-home-enumeration.md` §4): sweep the scheduler
    // registry for modules ALREADY in a terminal typecheck state at arm time and
    // index their public symbols DIRECTLY from the live table — the loaded-module
    // feed (i). A registered/loaded module absent from `/search` is the E3 defect
    // (branch (a) recorded ZERO rows via `mark_skipped`); the classic sighting is
    // a module brought in by the prelude's own imports (e.g. `(import [foo
    // [other]])` loads `foo`, whose sibling `count` is importable-but-not-in-scope
    // yet was invisible). Modules reaching terminal LATER (late `/import`,
    // watcher reload) are caught by the publication-edge hook
    // (`on_module_published`). `prelude` is the implicit outer scope, not an
    // importable module (mirrors `enumerate_cl_modules`'s prelude skip); seeded
    // modules were indexed above.
    let prelude_path = ModuleFullPath::from("prelude");
    for module in shared.scheduler.terminal_typecheck_modules() {
        if module == prelude_path || seeded_modules.contains(&module) {
            continue;
        }
        feed_loaded_module(shared, &module);
    }

    // Wake the nice workers parked on the object-codegen condvar so they begin
    // draining the index worklist (the arm-wake, §25.5).
    shared.scheduler.wake_object_workers();
}

/// Read `module`'s PUBLIC symbols from the live symbol table and record them into
/// the importable index with REPLACE-rows semantics (E3 loaded-module feed,
/// `resolve-home-enumeration.md` §4). No-op when the module has no live table.
/// The single projection both the arm-time sweep and the publication-edge hook
/// share (Principle 7 — one table→rows reader, `public_entries_from_table`).
fn feed_loaded_module(shared: &SharedState, module: &ModuleFullPath) {
    if let Some(table) = shared.symbol_tables.get(module) {
        let entries = public_entries_from_table(table.value());
        shared
            .importable_indices
            .record_loaded_replace(module, entries);
    }
}

/// The publication-edge hook (E3, `resolve-home-enumeration.md` §4): fed by the
/// immediate caller of `notify_typecheck_done` (`worker::handle_typecheck_work_shared`)
/// when a module reaches a TERMINAL typecheck state. When the importable index is
/// ARMED, records the just-terminal module's public symbols from the live table
/// (REPLACE-rows) — covering the in-flight-at-arm, late-`/import`, and
/// watcher-reload cases uniformly, with no polling and no worker respin. A no-op
/// when the index is not armed (`--run`/`--link`/`--release`, or pre-arm during
/// startup), so batch modes stay index-inert (R9). `prelude`/seeded modules are
/// skipped (the sweep's exclusions; they are handled at arm time / are the outer
/// scope).
pub(crate) fn on_module_published(shared: &SharedState, module: &ModuleFullPath) {
    if !shared.importable_indices.is_armed() {
        return;
    }
    if module.as_ref() == "prelude"
        || crate::bootstrap::seeded_importable_modules().contains(module)
    {
        return;
    }
    feed_loaded_module(shared, module);
}

/// The failure-edge hook (E3 / FIXME 0562, `resolve-home-enumeration.md` §4):
/// the symmetric peer of [`on_module_published`], fed at every `notify_module_failed`
/// site (`worker.rs`) — i.e. wherever a module transitions to `ModulePool::Failed`.
/// When the importable index is ARMED, marks the just-failed module SKIPPED so the
/// `/search` burn-down completes: a failed module publishes no valid public
/// symbols, so zero rows is the truthful outcome (§4 rule 2). This covers a module
/// that fails AFTER its worklist pop (popped in-flight, left pending, then fails) —
/// without it that module would wedge `pending_count ≥ 1` forever, the I-1 wedge
/// shape. Branch (a) handles the pre-pop case (registered + already `Failed` when
/// the worklist pops it). A no-op when the index is not armed
/// (`--run`/`--link`/`--release`, or pre-arm during startup), so batch modes stay
/// index-inert (R9). Idempotent — `mark_skipped` is a set insert, so a redundant
/// call (pop-time skip + failure-hook skip for the same module) does not double
/// count. `prelude`/seeded modules are skipped (they are never on the worklist and
/// are handled at arm time / are the outer scope).
pub(crate) fn on_module_failed(shared: &SharedState, module: &ModuleFullPath) {
    if !shared.importable_indices.is_armed() {
        return;
    }
    if module.as_ref() == "prelude"
        || crate::bootstrap::seeded_importable_modules().contains(module)
    {
        return;
    }
    shared.importable_indices.mark_skipped(module);
}

/// Whether `module` has reached a terminal typecheck state (its signatures are
/// published) per the scheduler pool — the gate for branch (a) recording a
/// registered module's rows now vs leaving it pending for the publication hook.
fn is_terminal(shared: &SharedState, module: &ModuleFullPath) -> bool {
    shared
        .scheduler
        .module_pool(module)
        .is_some_and(|p| p.is_terminal_typecheck())
}

/// Collect the full paths of PRIVATE submodules (`(mod- X)`) declared by any
/// enumerated module, by a cheap syntactic scan of each module's file (§8.2.3,
/// 0570). A private submodule is declared by its PARENT via `ModDecl.visibility`
/// (Principle 19 — a declared module attribute, NOT a name heuristic), so the
/// returned set holds `{parent}.{X}` full paths; the caller drops those and their
/// subtrees from the `/search` index. Parse/read errors on a file are skipped
/// (the module is simply not treated as declaring privacy — the branch-b/c index
/// pass surfaces any real error). Never typechecks — purely syntactic.
/// Whether `module` lies within the subtree rooted at `ancestor` — itself, or a
/// dotted descendant (`{ancestor}.…`). The §8.2.3 subtree predicate, shared by
/// `search_visible_from` (sibling of `imports::is_in_subtree`, kept local so the
/// index surface owns its own copy without widening the import module's API).
fn path_in_subtree(module: &ModuleFullPath, ancestor: &ModuleFullPath) -> bool {
    module == ancestor || module.as_ref().starts_with(&format!("{ancestor}."))
}

fn private_submodule_paths(
    modules: &[ModuleFullPath],
    project_root: &std::path::Path,
    lib_dirs: &[std::path::PathBuf],
) -> HashSet<ModuleFullPath> {
    let mut private_roots: HashSet<ModuleFullPath> = HashSet::new();
    for m in modules {
        let Some(file) = crate::pipeline::resolve_module_file(m, project_root, lib_dirs) else {
            continue;
        };
        let Ok(source) = std::fs::read_to_string(&file) else {
            continue;
        };
        let Ok(sexps) = cranelisp_frontend::parse(&source) else {
            continue;
        };
        let Ok((decls, _)) = cranelisp_frontend::extract_module_declarations(m, &sexps) else {
            continue;
        };
        for d in &decls.mod_decls {
            if d.visibility == cranelisp_types::Visibility::Private {
                private_roots.insert(ModuleFullPath::from(format!("{m}.{}", d.name.as_ref())));
            }
        }
    }
    private_roots
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
        let dotted = rel_str
            .to_string_lossy()
            .replace(std::path::MAIN_SEPARATOR, ".");
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
    // Branch (a): a module registered with the scheduler is LOADED into the live
    // session — its public symbols come from the live symbol table, NOT a
    // never-read `.meta` (E3, spec §17.19 R10; `resolve-home-enumeration.md` §4).
    // The prior `mark_skipped` recorded ZERO rows for a loaded module, so its
    // importable-but-not-in-scope symbols were invisible to `/search` — the E3
    // defect. Now: if the module has reached a terminal typecheck state, record
    // its rows from the live table now (REPLACE-rows); if still in-flight, leave
    // it pending — the publication-edge hook (`on_module_published`) records it
    // when it reaches terminal, so no source is marked complete with zero rows.
    if shared.scheduler.is_registered(module) {
        if is_terminal(shared, module) {
            if shared.symbol_tables.contains_key(module) {
                feed_loaded_module(shared, module);
            } else {
                // Registered + terminal but no live table (should not happen) —
                // genuinely row-less, so a zero-row skip is legal (§4 rule 2).
                shared.importable_indices.mark_skipped(module);
            }
        } else if matches!(
            shared.scheduler.module_pool(module),
            Some(ModulePool::Failed)
        ) {
            // Registered but FAILED typecheck (e.g. a broken lib module the
            // prelude imports, registered + `Failed` before this worklist pop):
            // a failed module publishes NO valid public symbols, so it is
            // genuinely row-less — mark it skipped so the burn-down completes
            // (§4 rule 2; the terminal-pool set deliberately excludes `Failed`,
            // so without this the module would wedge `pending_count ≥ 1`
            // forever — the I-1 wedge shape). A later watcher-reload fix flows
            // through the real typecheck → `notify_typecheck_done` → the
            // publication hook feeds rows with REPLACE semantics, so recovery is
            // already correct (FIXME 0562).
            shared.importable_indices.mark_skipped(module);
        }
        // In-flight (not terminal, not failed): do nothing — leave pending; the
        // publication hook (`on_module_published`) records it at its terminal
        // transition, or the failure hook (`on_module_failed`) skips it if it
        // fails AFTER this pop.
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

    // Branch (c): no/stale `.meta` — typecheck once (into the private substrate),
    // write `.meta`, populate.
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
) -> Option<Vec<ImportableRow>> {
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
    if !shared
        .cache
        .is_cache_valid(module, &source_hash, &empty_deps)
    {
        return None;
    }

    // Schema+BUILD_ID gate: deserialise the SymbolTable from the `.meta`.
    let (meta_path, _o_path) = cache::module_cache_path(cache_dir, module);
    let table = cache::serialize::load_meta(&meta_path).ok()?;
    Some(public_entries_from_table(&table))
}

/// Branch (c): typecheck once on the nice worker against a **function-local,
/// isolated private substrate** (`checked_typecheck_module` — a deep-cloned
/// private `symbol_tables` snapshot + fresh aliases + a private prelude-fallback
/// snapshot; it installs the module's own `(import …)` decls and runs
/// `check_forms` against those PRIVATE maps only), wrapped in CF.2 `catch_unwind`
/// (§25.4). On a clean check the typed entries are read back OUT of the private
/// snapshot (dropped at function return), a benign `.meta` is written (no `.o`,
/// no `register_module`) so a later real `/import` is a cache-hit (§25.5), and
/// the indices are recorded.
///
/// In-memory isolation (S91, `index-worker-isolation.md` §3.1): the live
/// `symbol_tables` / `module_aliases` / `prelude_fallback` maps are
/// byte-unchanged **by construction** — the typecheck runs entirely against the
/// private snapshot, so there is no residue to remove (the retired
/// "typecheck-into-live then REMOVE the residue (R13)" / `process_cluster`
/// model). On an Err or a caught panic, the per-module index-skip leaves NO
/// `.meta` and continues the burn-down — never a crash, never a killed worker.
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
            // built from the typed entries we read out of the private snapshot.
            //
            // EXCEPT for a MACRO-carrying module (0569 regression fence): its
            // index `.meta` is INCOMPLETE for a real import — it holds the macro's
            // classified entry (searchable) but NOT the compiled clause code, and
            // the indexer writes no `.o`. A macro-only module has no
            // `defined_symbols()` codegen targets, so `cache_validity_check` would
            // ACCEPT that `.meta` as a valid cache-hit and INSTALL the macro
            // without ever compiling its clauses — a later `(my-double 21)` then
            // has no clause code. So we index the entries for `/search`
            // (`record_triples`) but do NOT write the import cache `.meta` when any
            // entry is a macro; the import then fully compiles (clauses included).
            // Non-macro modules keep the index→import cache-hit optimization.
            let has_macro = entries.iter().any(|(_, _, e)| {
                matches!(e, ModuleEntry::Def { kind, .. }
                    if matches!(kind.as_ref(), DefKind::Macro { .. }))
            });
            if let Some(dir) = cache_dir.as_deref()
                && !has_macro
            {
                write_index_meta(shared, module, dir, &entries);
            }
            shared.importable_indices.record_triples(module, entries);
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
///
/// (This benign-`.meta` write is the §25.5 index→import cache-hit optimization.
/// Its retirement is proposed by `index-worker-isolation.md` §3.3 but is NOT
/// landed here — it re-scopes with FIXME 0604; see that FIXME's S110 disposition.
/// The in-memory isolation the contract ratifies IS in place: the typecheck runs
/// against `checked_typecheck_module`'s private snapshot, never live.)
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
    if let Err(e) = cache::serialize::write_meta(&meta_path, &table, cache::CACHE_SCHEMA_VERSION)
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

/// Run the real import-installing + typecheck path for `module` over its source
/// against a **function-local, isolated private substrate**, wrapped in CF.2
/// `catch_unwind` (§25.4 — the nice-worker catch, NOT inherited from the
/// priority worker), then read its typed public entries out of that private
/// substrate (dropped at function return). Returns:
///   `Ok(Some(entries))` — clean check; entries are `(name, scheme.ty, entry)`.
///   `Ok(None)`          — no checkable forms.
///   `Err(reason)`       — a typecheck error/gap OR a caught panic (0432-shaped).
///
/// INDEX-ISOLATION (S110, `index-worker-isolation.md` §2/§3): the module is
/// NEVER `register_module`'d, and NONE of the live `SharedState` substrate is
/// written — not `symbol_tables`, not `module_aliases`, and (as of §3.2) not
/// `prelude_fallback` either. The four maps are byte-unchanged **by
/// construction, not by undo**: there is no residue to remove because there is
/// no live write to make (the retired "typecheck-into-live then REMOVE the
/// residue (R13)" model). Every intermediate the index typecheck needs is a
/// private snapshot dropped at function end.
#[allow(clippy::type_complexity)]
fn checked_typecheck_module(
    shared: &SharedState,
    module: &ModuleFullPath,
    file: &std::path::Path,
) -> Result<Option<Vec<(Symbol, Type, ModuleEntry<crate::code::Code>)>>, String> {
    let source = std::fs::read_to_string(file).map_err(|e| format!("read error: {e}"))?;
    let sexps = cranelisp_frontend::parse(&source).map_err(|e| format!("parse error: {e}"))?;

    // ZERO shared-state mutation (INDEX-ISOLATION by construction; race-free
    // against the eval thread). The indexer runs the import-install + typecheck
    // against a PRIVATE, isolated symbol-tables map — a deep snapshot of the live
    // tables for dependency reads (`primitives`, `prelude`, …) plus a fresh entry
    // for the indexed module. The live `SharedState` maps are NEVER written, so
    // there is no residue and no TOCTOU race with a concurrent real `(import …)`
    // of the same module on the eval thread. All writes land in the private map,
    // dropped at function end.
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
    // §3.2 — snapshot the prelude-fallback bits into a PRIVATE clone. The index
    // typecheck's installers/`check_forms` only READ the fallback today, but a
    // live `&shared.prelude_fallback` handle threaded into an install/typecheck
    // call is a standing invitation for a future write leak and defeats the §5
    // reviewer grep ("no live `&shared.*` map into an install/typecheck/register
    // call"). Reading a consistent private snapshot makes the isolation total by
    // construction (the fallback bits are session-stable, so the snapshot is a
    // faithful read view). Same clone shape as `private_tables`.
    let private_prelude_fallback: cranelisp_typecheck::PreludeFallback =
        shared.prelude_fallback.clone();

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
            &private_prelude_fallback,
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
                    if e.is_empty() { Ok(None) } else { Ok(Some(e)) }
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
    let (decls, remaining) = cranelisp_frontend::extract_module_declarations(module, sexps)
        .map_err(|e| format!("structural peel error: {e}"))?;

    crate::imports::install_imports(
        priv_tables,
        module,
        priv_aliases,
        prelude_fallback,
        &decls.import_specs,
    )
    .map_err(|e| format!("import install error: {e}"))?;
    // FIXME 0604 §2.2: the BACKGROUND index typecheck is isolated (R13 — never
    // writes live session state), so it passes `None` for `declared_exports` — it
    // records no `D(M)` into the live map. (Its private tables are discarded; the
    // gate here is a no-op over `D(M) == None`.)
    crate::imports::install_exports(
        priv_tables,
        module,
        prelude_fallback,
        None,
        &decls.export_specs,
    )
    .map_err(|e| format!("export install error: {e}"))?;

    // Register `defmacro` entries so user macros are SEARCHABLE (0569). Macro
    // registration is int-orchestrated (`register_macro_in_module`) and is NOT
    // run by `check_forms`; moreover `build_forms` DROPS `ParsedEntry::Macro`
    // (frontend contract). An index typecheck that only ran `check_forms`
    // therefore omitted every user macro from the index. Route each defmacro
    // through the SAME registration seam the eval/worker path uses (reuse, not a
    // mirror — Principle 7) into the PRIVATE module table, with NO introspection
    // (REPL-only) and NO clause compilation (indexing needs only the classified
    // `DefKind::Macro` entry, from which `public_entries_with_entry` reads the
    // name + `is_macro`). The non-macro forms fall through to `check_forms`.
    let mut regular: Vec<cranelisp_types::Sexp> = Vec::with_capacity(remaining.len());
    for form in remaining {
        if cranelisp_frontend::is_defmacro(&form) {
            let info = cranelisp_frontend::parse_defmacro(&form)
                .map_err(|e| format!("defmacro parse error: {e}"))?;
            crate::process_form::form_dispatch::register_macro_in_module(
                &crate::process_form::form_dispatch::MacroRegisterEnv {
                    symbol_tables: priv_tables,
                    introspection: None,
                    module_aliases: priv_aliases,
                    prelude_fallback,
                },
                module,
                &info.name,
                &info,
                &form,
                &form,
                None,
            )
            .map_err(|e| format!("macro register error: {}", e.message()))?;
        } else {
            regular.push(form);
        }
    }

    let program =
        crate::worker::build_program_compat(&regular).map_err(|e| format!("build error: {e}"))?;
    let parsed = crate::worker::top_level_to_parsed_entries(&program);
    if parsed.is_empty() {
        // Regular-defn typecheck is a no-op, but any macros registered above are
        // already in the private table — the caller reads them out (0569).
        return Ok(());
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
        Ok(_check) => {
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
    table: &cranelisp_types::SymbolTable<
        impl cranelisp_types::CodeStore,
        impl cranelisp_types::LinkerStore,
    >,
) -> Vec<ImportableRow> {
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
        // Only function/value/macro defs carry a usable index row. A macro's
        // `scheme.ty` is a placeholder scalar (§17.19.2a); `is_macro` carries the
        // §1.1 classification so the row renders `; defmacro` instead of it (0569).
        if let ModuleEntry::Def {
            scheme,
            docstring,
            kind,
            ..
        } = entry
        {
            out.push(ImportableRow {
                name: sym.clone(),
                scheme: scheme.ty.clone(),
                docstring: docstring.clone(),
                is_macro: matches!(kind.as_ref(), DefKind::Macro { .. }),
            });
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
        Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))
    }
    /// A `(name, scheme, no-docstring)` row for the common test case.
    fn row(name: &str, ty: Type) -> ImportableRow {
        ImportableRow {
            name: sym(name),
            scheme: ty,
            docstring: None,
            is_macro: false,
        }
    }
    /// A `(name, scheme, docstring)` row for the docstring-axis tests.
    fn row_doc(name: &str, ty: Type, doc: &str) -> ImportableRow {
        ImportableRow {
            name: sym(name),
            scheme: ty,
            docstring: Some(doc.to_string()),
            is_macro: false,
        }
    }
    /// A macro index row (`is_macro = true`) for the §17.19.2a classification test.
    fn row_macro(name: &str, ty: Type) -> ImportableRow {
        ImportableRow {
            name: sym(name),
            scheme: ty,
            docstring: None,
            is_macro: true,
        }
    }

    // spec: repl/spec.md §17.19.2a (0569) — the `is_macro` classification rides
    // the index from record to `SearchHit`, so the row renderer can emit the
    // `; defmacro` envelope rather than the macro's placeholder scalar scheme.
    #[test]
    fn search_hit_carries_is_macro_classification() {
        let idx = ImportableIndices::default();
        idx.record_entries(
            &m("macx"),
            vec![row_macro("twice", Type::Int), row("gcd2", int_arrow_int())],
        );
        let macro_hit = idx.search_by_name("twice");
        assert_eq!(macro_hit.len(), 1);
        assert!(
            macro_hit[0].is_macro,
            "a macro entry's hit must carry is_macro"
        );
        let fn_hit = idx.search_by_name("gcd2");
        assert_eq!(fn_hit.len(), 1);
        assert!(
            !fn_hit[0].is_macro,
            "a fn entry's hit must NOT carry is_macro"
        );
    }

    // spec: spec/08-modules.md §8.2.3 (0570) — `private_submodule_paths` reads the
    // PARENT-declared `(mod- X)` visibility bit (a syntactic scan, not a name
    // heuristic) and returns the private submodule's full path; the caller drops
    // it (and its subtree) from the `/search` index. A `(mod pub)` sibling is NOT
    // returned.
    #[test]
    fn private_submodule_paths_reads_mod_dash_bit_not_a_name() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        std::fs::write(
            root.join("host.cl"),
            "(import [primitives [Int]])\n(mod- priv)\n(mod pub)\n(defn host-fn [] :Int 1)\n",
        )
        .unwrap();
        std::fs::create_dir_all(root.join("host")).unwrap();
        std::fs::write(
            root.join("host/priv.cl"),
            "(import [primitives [Int]])\n(defn secret [] :Int 42)\n",
        )
        .unwrap();
        std::fs::write(
            root.join("host/pub.cl"),
            "(import [primitives [Int]])\n(defn shown [] :Int 7)\n",
        )
        .unwrap();

        let modules = vec![m("host"), m("host.priv"), m("host.pub")];
        let private = private_submodule_paths(&modules, root, &[]);
        assert!(
            private.contains(&m("host.priv")),
            "the `(mod- priv)` child must be reported private; got {private:?}"
        );
        assert!(
            !private.contains(&m("host.pub")),
            "a `(mod pub)` child must NOT be reported private; got {private:?}"
        );
        assert!(
            !private.contains(&m("host")),
            "the parent module itself is not a private submodule; got {private:?}"
        );
    }

    // spec: spec/08-modules.md §8.2.3 (0570 residual) — the search-time
    // subtree-visibility filter. A symbol whose home is inside a private
    // `(mod- test)` subtree is visible ONLY to a searcher inside that same
    // subtree; an OUTSIDE searcher (a sibling) MUST NOT see it (regardless of how
    // the row entered the index — this is the single enforcement point over the
    // loaded-module feed that bypasses the arm-time file-worklist drop). A
    // non-private home is unconditionally visible.
    #[test]
    fn search_visible_from_hides_private_submodule_only_outside_its_subtree() {
        let idx = ImportableIndices::default();
        idx.record_private_roots(HashSet::from([m("user.test")]));
        // A sibling OUTSIDE `user.test`'s subtree cannot see the private symbol.
        assert!(
            !idx.search_visible_from(&m("user.test"), &m("sibling")),
            "a private submodule symbol MUST be hidden from an outside-subtree searcher"
        );
        // A DESCENDANT home is likewise hidden from outside.
        assert!(
            !idx.search_visible_from(&m("user.test.deep"), &m("user")),
            "a private submodule's descendant is hidden from a searcher above the private root"
        );
        // A searcher INSIDE the subtree (the private module itself, or a
        // descendant) CAN see it — the filter is subtree-relative, not absolute.
        assert!(
            idx.search_visible_from(&m("user.test"), &m("user.test")),
            "a searcher in the private module itself sees its own symbols"
        );
        assert!(
            idx.search_visible_from(&m("user.test"), &m("user.test.child")),
            "a searcher deeper in the private subtree sees the symbol"
        );
        // A NON-private home is unconditionally visible.
        assert!(
            idx.search_visible_from(&m("mathx"), &m("sibling")),
            "a non-private module's symbols are visible to any searcher"
        );
        // With NO private roots recorded, everything is visible.
        let empty = ImportableIndices::default();
        assert!(empty.search_visible_from(&m("user.test"), &m("sibling")));
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
        assert_eq!(
            idx.search_by_name("ZERO").len(),
            1,
            "case-insensitive substring"
        );
        assert_eq!(idx.search_by_name("is-zero").len(), 1, "exact also matches");
        assert!(
            idx.search_by_name("nope").is_empty(),
            "non-substring misses"
        );
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
                row_doc(
                    "gcd2",
                    int_arrow_int(),
                    "greatest common divisor of two ints",
                ),
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
        assert_eq!(
            hits.len(),
            1,
            "Int is a sub-structure of (Fn [Int Int] Int)"
        );
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
        assert_eq!(
            idx.take_index_task().as_ref().map(|m| m.to_string()),
            Some("a".to_string())
        );
        assert_eq!(
            idx.take_index_task().as_ref().map(|m| m.to_string()),
            Some("b".to_string())
        );
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
        assert!(
            !idx.take_completion_notice(),
            "unarmed → no completion notice"
        );
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
        assert_eq!(
            idx.pending_count(),
            0,
            "no perpetual pending — burn-down completes"
        );
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

    // =======================================================================
    // S108 (Increment 3) — E3 loaded-module feed (`resolve-home-enumeration.md`
    // §4). The arm-time sweep + branch (a) + the publication-edge hook all land
    // rows through `record_loaded_replace`; the SharedState-level wiring (the
    // scheduler pool read, the live-table projection) is e2e-covered by
    // `tests/search.rs`, while the accounting/replace/dual-tally invariants — the
    // arm-vs-load timing cases the racy e2e cannot pin (the Inc2 rationale) — are
    // pinned HERE at the `IndicesInner` seam, deterministically.
    // =======================================================================

    // spec: repl/spec.md §17.19 R10 — obligation 1 (arm-time sweep): an already-
    // terminal registered module recorded from the live table
    // (`public_entries_from_table` → `record_loaded_replace`) lands searchable
    // rows and is SINGLE-tallied (it was already counted by `arm` as a file
    // module — no `enumerated_total` bump). This is the classic E3 sighting: a
    // module loaded by the prelude's own imports whose sibling symbol is
    // importable-but-not-in-scope.
    #[test]
    fn loaded_feed_records_file_enumerated_module_single_tally() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("foo"), m("a")]); // 2 file modules; enum=2, pending=2
        let table = public_def_table("foo", "count", int_arrow_int());
        idx.record_loaded_replace(&m("foo"), public_entries_from_table(&table));
        assert_eq!(
            idx.pending_count(),
            1,
            "foo single-tallied (already counted by arm) — only `a` pends"
        );
        let hits = idx.search_by_name("count");
        assert_eq!(
            hits.len(),
            1,
            "the loaded module's importable symbol is searchable"
        );
        assert_eq!(hits[0].module.as_ref(), "foo");
        assert_eq!(hits[0].tier, MatchTier::ExactName);
    }

    // spec: repl/spec.md §17.19 R10 — obligation 2 (publication-edge hook): a
    // file-enumerated module that is still in-flight at arm is LEFT PENDING by
    // branch (a); when it reaches terminal AFTER arm, the publication hook records
    // it (modelled here by the deferred `record_loaded_replace`) and the burn-down
    // completes — no polling, no worker respin.
    #[test]
    fn loaded_feed_publication_hook_records_inflight_module_after_arm() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("foo")]); // enum=1, pending=1
        // In-flight at arm: branch (a) records nothing → foo stays pending.
        assert_eq!(
            idx.pending_count(),
            1,
            "an in-flight registered module is left pending"
        );
        // foo reaches terminal later → the publication hook feeds it.
        let table = public_def_table("foo", "count", int_arrow_int());
        idx.record_loaded_replace(&m("foo"), public_entries_from_table(&table));
        assert_eq!(
            idx.pending_count(),
            0,
            "the publication hook completes the burn-down"
        );
        assert_eq!(idx.search_by_name("count").len(), 1);
    }

    // spec: repl/spec.md §17.19 R10 + §17.19.3 — obligation 3 (late `/import`): a
    // module OUTSIDE the file-enumerated set recorded via the hook takes the
    // dual-tally shape (enumerated_total + indexed), so it stays searchable and
    // the accounting stays complete; it does NOT fire a SECOND completion notice
    // (the latch is one-shot).
    #[test]
    fn loaded_feed_late_import_dual_tallies_no_second_completion_note() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("a")]); // one file module; enum=1
        idx.mark_note_shown(); // a /search served the not-ready note this session
        idx.record_entries(&m("a"), vec![row("f", int_arrow_int())]);
        assert_eq!(idx.pending_count(), 0);
        assert!(
            idx.take_completion_notice(),
            "burn-down complete + note shown → the completion notice fires once"
        );
        // A late `/import` of `bar` (not on the file worklist) → dual tally.
        let table = public_def_table("bar", "count", int_arrow_int());
        idx.record_loaded_replace(&m("bar"), public_entries_from_table(&table));
        assert_eq!(
            idx.pending_count(),
            0,
            "the late load dual-tallies (enum + indexed) — pending stays 0"
        );
        assert_eq!(
            idx.search_by_name("count").len(),
            1,
            "the late-loaded symbol is searchable"
        );
        assert!(
            !idx.take_completion_notice(),
            "a late load fires NO second completion notice (one-shot latch)"
        );
    }

    // spec: repl/spec.md §17.19 R10 — obligation 4 (REPLACE-rows refresh): a
    // re-record (watcher reload / REPL redefinition) REPLACES a module's rows —
    // no duplicates, no stale rows — and perturbs neither tally.
    #[test]
    fn loaded_feed_rerecord_replaces_rows_no_duplicates_or_stale() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("foo")]);
        let t1 = public_def_table("foo", "count", int_arrow_int());
        idx.record_loaded_replace(&m("foo"), public_entries_from_table(&t1));
        assert_eq!(
            idx.search_by_name("count")
                .iter()
                .filter(|h| h.name.as_ref() == "count")
                .count(),
            1
        );
        // Watcher reload: `foo` redefined — `count` renamed to `counter`.
        let t2 = public_def_table("foo", "counter", int_arrow_int());
        idx.record_loaded_replace(&m("foo"), public_entries_from_table(&t2));
        assert_eq!(
            idx.search_by_name("counter").len(),
            1,
            "the new `counter` row is present after re-record"
        );
        assert!(
            !idx.search_by_name("count")
                .iter()
                .any(|h| h.name.as_ref() == "count"),
            "the stale exact `count` row is REPLACED, not duplicated or retained"
        );
        assert_eq!(
            idx.pending_count(),
            0,
            "a re-record does not perturb the tallies"
        );
    }

    // spec: repl/spec.md §17.19.3 — obligation 5 (accounting): `pending_count =
    // enumerated_total − indexed.len()` stays ≥ 0, reaches 0, and is
    // ORDER-INDEPENDENT across the loaded feed vs `arm` (the S-1 property extended
    // to loaded modules) — the feed may record `foo` BEFORE `arm` enumerates a
    // same-named `foo.cl`; the `!indexed.contains` guard drops the file duplicate
    // and foo is counted exactly once.
    #[test]
    fn loaded_feed_accounting_order_independent_and_reaches_zero() {
        let idx = ImportableIndices::default();
        // Loaded feed records `foo` FIRST (outside any file set yet → dual tally).
        let table = public_def_table("foo", "count", int_arrow_int());
        idx.record_loaded_replace(&m("foo"), public_entries_from_table(&table));
        assert_eq!(
            idx.pending_count(),
            0,
            "pending never negative — foo dual-tallied once"
        );
        // arm enumerates a file worklist COLLIDING on `foo` (a `foo.cl`) plus `a`.
        idx.arm(vec![m("foo"), m("a")]);
        assert_eq!(
            idx.pending_count(),
            1,
            "foo counted once (dup dropped); only `a` pends"
        );
        idx.mark_skipped(&m("a"));
        assert_eq!(idx.pending_count(), 0, "the burn-down reaches zero");
        assert_eq!(
            idx.search_by_name("count").len(),
            1,
            "foo's row survives the collision"
        );
    }

    // spec: repl/spec.md §17.19 R10 — obligation 6 (no zero-row skip for a
    // registered module): the E3 fix records a loaded module's rows via the
    // loaded feed; `mark_skipped`-with-zero-rows is legal ONLY for a genuinely
    // row-less outcome (empty module / no source file), NEVER for "registered".
    #[test]
    fn loaded_feed_registered_module_contributes_rows_not_mark_skipped() {
        let idx = ImportableIndices::default();
        idx.arm(vec![m("foo")]);
        let table = public_def_table("foo", "count", int_arrow_int());
        idx.record_loaded_replace(&m("foo"), public_entries_from_table(&table));
        assert!(
            !idx.search_by_name("count").is_empty(),
            "a registered/loaded module MUST contribute its importable rows (E3), \
             not be `mark_skipped` with zero rows"
        );
        // Contrast: a genuinely row-less outcome legitimately marks zero rows and
        // still completes the burn-down.
        let idx2 = ImportableIndices::default();
        idx2.arm(vec![m("empty")]);
        idx2.mark_skipped(&m("empty"));
        assert!(
            idx2.search_by_name("count").is_empty(),
            "a row-less skip adds no rows"
        );
        assert_eq!(
            idx2.pending_count(),
            0,
            "a row-less skip still completes the burn-down"
        );
    }

    // =======================================================================
    // S108 (Increment 3) — FIXME 0562: the E3 failure-path regression. Branch
    // (a)'s "leave in-flight modules pending for the publication hook" missed
    // the FAILURE exit from in-flight — a registered module that FAILS typecheck
    // is never fed and never skipped, wedging `pending_count ≥ 1` forever. These
    // two pins drive the REAL `SharedState`-level dispatch (the scheduler-pool
    // read + the failure-edge hook), so a revert of either half wedges them RED.
    // =======================================================================

    /// A minimal `SharedState` for the FIXME-0562 branch-(a)/hook pins. Mirrors
    /// `worker/tests.rs::test_shared_state`; no workers spawned, no codegen runs.
    /// The only fields the index-worker branch reads are `scheduler`,
    /// `symbol_tables`, and `importable_indices`. Caching disabled.
    fn test_shared_state() -> SharedState {
        use std::sync::Mutex;
        use std::sync::atomic::{AtomicBool, AtomicU32};
        SharedState {
            scheduler: crate::scheduler::CompileScheduler::new(),
            project_root: std::path::PathBuf::new(),
            lib_dirs: Mutex::new(Vec::new()),
            platform_dirs: Mutex::new(Vec::new()),
            module_aliases: cranelisp_types::ModuleAliases::default(),
            prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
            declared_exports: crate::imports::DeclaredExports::default(),
            cache: std::sync::Arc::new(crate::cache::ObjectCache::new(None, None)),
            promote_nice_workers: AtomicBool::new(false),
            file_to_module: Mutex::new(HashMap::new()),
            symbol_tables: dashmap::DashMap::new(),
            next_type_id: AtomicU32::new(0),
            typecheck_products: dashmap::DashMap::new(),
            kept_dlls: Mutex::new(Vec::new()),
            introspection: Some(dashmap::DashMap::new()),
            importable_indices: ImportableIndices::default(),
            broken: dashmap::DashMap::new(),
            retained_code: Mutex::new(Vec::new()),
            fresh_jit_drop_glues: dashmap::DashMap::new(),
            run_mode: crate::session_v4::RunMode::Repl,
            test_runner_state: Box::new(crate::session_v4::TestRunnerState::stub()),
        }
    }

    // spec: design/int/index-worker-isolation.md §2/§3.1/§3.2 (FIXME 0604) —
    // IN-MEMORY INDEX-ISOLATION: `checked_typecheck_module` runs the index
    // typecheck against a function-local PRIVATE substrate (deep-cloned
    // `symbol_tables` snapshot + fresh aliases + a private prelude-fallback
    // snapshot), so it mutates NO live `SharedState` map — not `symbol_tables`,
    // not `module_aliases`, and (as of §3.2) not `prelude_fallback`. The indexed
    // module never appears in the LIVE `symbol_tables` (it is read out of the
    // private snapshot, which is dropped). Fail-on-revert: reintroduce the retired
    // typecheck-into-live model (or thread `&shared.prelude_fallback` and let a
    // callee write it) and one assertion below flips RED.
    // defect: class=shared-state-write-race locus=src/session_v4/index_worker.rs::checked_typecheck_module found=S110 owner=/dev
    #[test]
    fn index_typecheck_mutates_no_live_shared_state() {
        let shared = test_shared_state();
        let module = m("mod1");

        // Seed live state so a mutation would be observable: a prelude-fallback
        // bit for the indexed module and an unrelated live table.
        shared.prelude_fallback.insert(module.clone(), true);
        shared.symbol_tables.insert(
            m("other"),
            cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(m("other")),
        );
        let fallback_before: Vec<(ModuleFullPath, bool)> = shared
            .prelude_fallback
            .iter()
            .map(|e| (e.key().clone(), *e.value()))
            .collect();
        let live_keys_before: HashSet<ModuleFullPath> = shared
            .symbol_tables
            .iter()
            .map(|e| e.key().clone())
            .collect();

        // Drive the index typecheck against a real source file. Its outcome
        // (Ok/Err) is immaterial to this pin — the invariant is that NONE of the
        // live maps are written, whatever the result.
        let tmp = tempfile::tempdir().unwrap();
        let src = tmp.path().join("mod1.cl");
        std::fs::write(
            &src,
            "(import [primitives [Int]])\n(defn f [:Int x] :Int x)\n",
        )
        .unwrap();
        let _ = checked_typecheck_module(&shared, &module, &src);

        // The indexed module was typechecked into the PRIVATE snapshot and MUST
        // NOT have been written into the live `symbol_tables` (the S91 isolation;
        // the retired mutate-live model would leave a `mod1` entry here).
        assert!(
            !shared.symbol_tables.contains_key(&module),
            "IN-MEMORY ISOLATION §3.1: the indexed module MUST NOT be written into \
             the live symbol_tables (typecheck runs against the private snapshot)"
        );
        // The live table set is byte-unchanged (no adds, no drops).
        let live_keys_after: HashSet<ModuleFullPath> = shared
            .symbol_tables
            .iter()
            .map(|e| e.key().clone())
            .collect();
        assert_eq!(
            live_keys_before, live_keys_after,
            "IN-MEMORY ISOLATION: the index typecheck must not add/remove live tables"
        );
        // §3.2: the prelude-fallback map is byte-unchanged — the index typecheck
        // reads a private snapshot, never the live map.
        let fallback_after: Vec<(ModuleFullPath, bool)> = shared
            .prelude_fallback
            .iter()
            .map(|e| (e.key().clone(), *e.value()))
            .collect();
        assert_eq!(
            fallback_before, fallback_after,
            "ISOLATION §3.2: the index typecheck must not mutate the live \
             prelude_fallback (it reads a private snapshot)"
        );
    }

    /// Register `module` with the scheduler and drive it to `ModulePool::Failed`.
    fn register_and_fail(shared: &SharedState, module: &ModuleFullPath) {
        shared
            .scheduler
            .register_module(module.clone(), std::sync::Arc::from(Vec::new()), false);
        shared.scheduler.notify_module_failed(
            module,
            cranelisp_types::CranelispError::ModuleError {
                message: "type error in broken lib module".to_string(),
                location: cranelisp_types::ErrorLocation::from_span_file(
                    cranelisp_types::Span::SYNTHETIC,
                    None,
                ),
            },
        );
    }

    // spec: repl/spec.md §17.19.3 + resolve-home-enumeration.md §4 rule 2 (FIXME
    // 0562) — a file-enumerated module registered AND `Failed` at pop time: branch
    // (a) sees `is_registered → not terminal → pool == Failed` and `mark_skipped`s
    // it (a failed module publishes no importable rows), so the burn-down reaches
    // `pending_count == 0` instead of wedging `≥ 1` forever, and the completion
    // notice can fire. Fail-on-revert: delete the branch-(a) `Some(Failed)` arm and
    // the module is left pending → this wedges RED (`indexing 1 module(s)…`
    // perpetual, the I-1 shape).
    #[test]
    fn index_branch_a_registered_failed_module_completes_burndown() {
        let shared = test_shared_state();
        let broken = m("brokenlib");
        // Registered + Failed BEFORE the worklist pops it (startup load precedes
        // arm) — the deterministic wedge trigger from the FIXME.
        register_and_fail(&shared, &broken);
        assert_eq!(
            shared.scheduler.module_pool(&broken),
            Some(ModulePool::Failed),
            "precondition: registered + Failed"
        );
        // Arm the burn-down with the broken module on the file worklist (enum=1).
        shared.importable_indices.arm(vec![broken.clone()]);
        shared.importable_indices.mark_note_shown(); // a /search served the note
        assert_eq!(
            shared.importable_indices.pending_count(),
            1,
            "one pending at arm"
        );

        // Pop + dispatch the real branch (a) — the failure arm marks it skipped.
        assert!(
            run_one_index_task(&shared),
            "a task was popped and processed"
        );

        assert_eq!(
            shared.importable_indices.pending_count(),
            0,
            "a registered+Failed module completes the burn-down (no I-1 wedge)"
        );
        assert!(
            shared.importable_indices.take_completion_notice(),
            "burn-down complete + note shown → the completion notice fires"
        );
        assert!(
            shared
                .importable_indices
                .search_by_name("anything")
                .is_empty(),
            "a Failed module contributes no importable rows"
        );
    }

    // spec: repl/spec.md §17.19.3 + resolve-home-enumeration.md §4 (FIXME 0562) —
    // the POST-POP failure: a registered module popped while still in-flight is
    // left pending by branch (a); when it fails typecheck AFTER the pop, the
    // failure-edge hook `on_module_failed` marks it skipped so the burn-down
    // completes — symmetric with `on_module_published` for the success exit.
    // Fail-on-revert: neuter `on_module_failed` (make it a no-op) and the post-pop
    // module stays pending → this wedges RED.
    #[test]
    fn on_module_failed_hook_completes_burndown_for_postpop_failure() {
        let shared = test_shared_state();
        let foo = m("foo");
        // Register + arm with foo IN-FLIGHT (TypecheckNext, not terminal/failed).
        shared
            .scheduler
            .register_module(foo.clone(), std::sync::Arc::from(Vec::new()), false);
        shared.importable_indices.arm(vec![foo.clone()]);
        shared.importable_indices.mark_note_shown();

        // Pop + dispatch branch (a): in-flight → LEFT PENDING (the hook owns it).
        assert!(
            run_one_index_task(&shared),
            "the in-flight module is popped"
        );
        assert_eq!(
            shared.importable_indices.pending_count(),
            1,
            "an in-flight registered module is left pending after its pop"
        );

        // foo now FAILS typecheck AFTER the pop → the failure-edge hook fires.
        shared.scheduler.notify_module_failed(
            &foo,
            cranelisp_types::CranelispError::ModuleError {
                message: "post-pop type error".to_string(),
                location: cranelisp_types::ErrorLocation::from_span_file(
                    cranelisp_types::Span::SYNTHETIC,
                    None,
                ),
            },
        );
        on_module_failed(&shared, &foo);

        assert_eq!(
            shared.importable_indices.pending_count(),
            0,
            "the failure-edge hook completes the burn-down for a post-pop failure"
        );
        assert!(
            shared.importable_indices.take_completion_notice(),
            "complete + note shown → completion notice fires"
        );
        // Idempotent: a redundant hook call (e.g. a cascaded failure) does not
        // perturb the accounting or re-fire the one-shot latch.
        on_module_failed(&shared, &foo);
        assert_eq!(
            shared.importable_indices.pending_count(),
            0,
            "hook is idempotent"
        );
        assert!(
            !shared.importable_indices.take_completion_notice(),
            "one-shot latch: no second completion notice"
        );
    }

    // spec: resolve-home-enumeration.md §4 — `on_module_failed` is armed-gated: an
    // UNARMED index (batch `--run`/`--link`, or pre-arm startup) is index-inert, so
    // the hook is a no-op and records nothing (R9 batch-inertness).
    #[test]
    fn on_module_failed_is_armed_gated_noop_when_unarmed() {
        let shared = test_shared_state();
        let foo = m("foo");
        assert!(
            !shared.importable_indices.is_armed(),
            "unarmed by default (batch)"
        );
        on_module_failed(&shared, &foo); // no-op: not armed
        // Arming afterwards enumerates foo fresh — the pre-arm hook left no trace
        // in `indexed` (which would have wrongly pre-satisfied the burn-down).
        shared.importable_indices.arm(vec![foo.clone()]);
        assert_eq!(
            shared.importable_indices.pending_count(),
            1,
            "the pre-arm hook was inert — foo is genuinely pending after arm"
        );
    }
}
