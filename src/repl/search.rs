// REPL `/search` UI subsystem — the interactive-search half of
// `session_v4/index_worker.rs` (index-worker-isolation.md). Extracted from
// `repl.rs` per `design/int/repl-decomposition.md` §1.1 (S110, FIXME 0606).
// Pure relocation, behaviour-invariant.


use super::*;
use super::format::*;
use super::commands::*;


/// Bounded wait for the importable-symbol burn-down to drain before a
/// `/search` serves results (§25.5 — small projects index promptly; a large
/// reachable set times out and serves partial results + the progress note).
const SEARCH_INDEX_SETTLE_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(5);

/// Poll interval while waiting on the `/search` index settle.
const SEARCH_INDEX_SETTLE_POLL: std::time::Duration = std::time::Duration::from_millis(10);

/// A `/search` result row = an index hit plus whether it is already in scope
/// (which flips facet 4 from an `(import …)` form to the marker, §17.19.2 R13).
struct SearchRow {
    hit: crate::session_v4::index_worker::SearchHit,
    in_scope: bool,
}

/// Maximum characters shown either side of the matched substring in a
/// docstring-only excerpt (§17.19.2 facet 5).
const DOC_EXCERPT_WINDOW: usize = 30;

/// Build a short excerpt of `doc` around the first case-insensitive occurrence
/// of `query`, elided with `…` on either side when the docstring extends past
/// the window (§17.19.2 facet 5). Returns `None` when `query` is not found (the
/// caller then omits the facet).
///
/// The match position is located by scanning the ORIGINAL text's char
/// boundaries (per-char lowercased comparison) — NOT via a byte offset into
/// `doc.to_lowercase()`, whose byte length can differ from `doc`'s when a
/// codepoint's lowercase form is a different byte length (e.g. `İ` → `i` + U+0307).
/// A byte offset from the lowercased string is not a valid boundary in `doc` and
/// would split a codepoint or exceed `doc.len()`, panicking on user-supplied
/// docstring text (src/CLAUDE.md — never panic on user input). All windowing is
/// on `char` boundaries.
fn docstring_excerpt(doc: &str, query: &str) -> Option<String> {
    let query_lc = query.to_lowercase();
    if query_lc.is_empty() {
        return None;
    }
    let chars: Vec<char> = doc.chars().collect();
    // Find the char index where a case-insensitive match of `query` begins, by
    // lowercasing each candidate tail of the ORIGINAL text (so the returned
    // index is always a valid `chars` position).
    let match_char_start = (0..chars.len()).find(|&i| {
        let tail: String = chars[i..].iter().collect();
        tail.to_lowercase().starts_with(&query_lc)
    })?;
    let match_char_len = query.chars().count();
    let start = match_char_start.saturating_sub(DOC_EXCERPT_WINDOW);
    let end = (match_char_start + match_char_len + DOC_EXCERPT_WINDOW).min(chars.len());
    let mut excerpt = String::new();
    if start > 0 {
        excerpt.push_str("… ");
    }
    excerpt.extend(&chars[start..end]);
    if end < chars.len() {
        excerpt.push_str(" …");
    }
    Some(excerpt)
}

/// Build the `StyledDoc` for one `/search` result row (§10.3 K7, §17.19.2). A
/// free function (uses no session state) so the K7 role composition is unit-pinnable
/// without constructing a `CompilerSession` (`src/CLAUDE.md` testability discipline;
/// mirrors `render_search_row`'s peer `_doc` producers).
///
/// `:{sig} {name}\n  in {module}   — {action}\n` — the sig is R4, the name R15, the
/// module column R7 (dim), the rest Plain; a docstring-only hit appends a `; doc:`
/// excerpt as R6 metadata.
fn render_search_row_doc(row: &SearchRow, query: &str) -> StyledDoc {
    {
        use crate::session_v4::index_worker::MatchTier;
        let hit = &row.hit;
        let name = hit.name.as_ref();
        let module = hit.module.as_ref();
        // Facet 4: import form, or the in-scope marker for an exact in-scope hit.
        let action = if row.in_scope {
            "already in scope — no import needed".to_string()
        } else {
            format!("(import [{module} [{name}]])")
        };
        // Primary line — the canonical §1.1 envelope. A MACRO row is
        // `:{module}/{name} ; defmacro [- doc]` (§17.19.2a, 0569), mirroring the
        // bare-lookup / `/info` macro envelope; its `scheme.ty` is a placeholder
        // scalar and MUST NOT render as a `:Type`. A value/fn row keeps
        // `:{sig} {name}` — sig R4, name R15 (§10.3 K7).
        let mut out = StyledDoc::new();
        if hit.is_macro {
            push_type_annotation(&mut out, &format!("{module}/{name}"));
            out.plain(" ");
            push_metadata(
                &mut out,
                append_docstring_comment("; defmacro".to_string(), hit.docstring.as_deref()),
            );
        } else {
            let sig = crate::display::format_type_qualified(&hit.scheme);
            push_type_annotation(&mut out, &sig);
            out.plain(" ");
            out.plain(name);
        }
        // Facet 3 + 4: originating module column (R7, dim) and the action.
        out.plain("\n  in ");
        out.push(Role::ModulePrefix, module);
        out.plain(format!("   — {action}\n"));
        // Facet 5: docstring excerpt, only for a docstring-only hit — R6 metadata.
        if hit.tier == MatchTier::DocstringOnly
            && let Some(doc) = &hit.docstring
            && let Some(excerpt) = docstring_excerpt(doc, query)
        {
            push_metadata(&mut out, format!("  ; doc: {excerpt}"));
            out.plain("\n");
        }
        out
    }
}

impl CompilerSession {
    /// `/search <query>` handler — Pillar-3 importable-symbol search
    /// (repl/spec.md §17.19, design/int/agent.md §25). A NORMAL default-build
    /// command (NOT agent-gated). Searches the importable-symbol indices (built
    /// by the nice-worker burn-down over reachable-but-unimported modules) by
    /// name OR scheme, exact OR partial, and renders the four-facet result row
    /// (name + `:Type` signature + originating module + the `(import …)` form).
    ///
    /// Name-vs-scheme is distinguished by a leading `(Fn` / `(` (a type-shape
    /// query → Index B) or a bare fragment (→ Index A) — at implementation
    /// discretion (§25.6 / spec §17.19.1); both indices are searchable. A query
    /// landing before the burn-down completes serves partial results + an
    /// "indexing N modules…" note (§25.5 / spec §17.19.3).
    /// The "still indexing" progress-note text (spec §17.19.3) — `Some` while the
    /// burn-down is in flight (`pending > 0`), `None` once the index is complete.
    /// PURE (no `&self`, no side effects) so the §17.19.3 message-selection is
    /// unit-testable at the seam without driving a whole session, and so the
    /// note text has ONE source of truth (both the empty-result and the
    /// partial-result-append paths derive from it).
    fn indexing_note_text(pending: usize) -> Option<String> {
        (pending > 0).then(|| format!("; indexing {pending} module(s)… (results may be incomplete)"))
    }

    /// Message for an EMPTY `/search` result (spec §17.19.3, tightened S108).
    /// "Nothing matched yet, still building" and "nothing matched a complete
    /// index" are DISTINCT states that MUST NOT be conflated — they call for
    /// opposite reader actions (retry vs. rephrase). While the burn-down is in
    /// flight (`pending > 0`) this serves ONLY the not-ready note, never the `no
    /// importable symbols matched` note; the no-match note is served ONLY once
    /// the index is complete (`pending == 0`). PURE for unit-testability.
    fn empty_result_message(query: &str, pending: usize) -> String {
        let _ = query;
        match Self::indexing_note_text(pending) {
            Some(note) => note,
            // The note names the OUTCOME, not the query: echoing the query back
            // would re-surface the name of a symbol that is deliberately NOT
            // importable — e.g. a `(mod- priv)` private-submodule symbol filtered
            // from the index (§8.2.3, 0570) — which a `_neg` guard reads as the
            // private name "surfacing". The user's own input line already carries
            // the query; the note only needs to report that nothing matched.
            None => "; no importable symbols matched".to_string(),
        }
    }

    pub(crate) fn handle_search(&self, query: &str) -> String {
        let query = query.trim();
        if query.is_empty() {
            return "Usage: /search <name-or-scheme>".to_string();
        }

        // Wait (bounded) for the burn-down to drain so results are complete for
        // the common small-project case (§25.5 — "for a small fixture the
        // burn-down completes promptly"). If the wait times out (a large
        // reachable set), serve partial results + the "indexing N modules…"
        // note below (spec §17.19.3) rather than blocking the prompt
        // indefinitely. The index is armed at REPL startup (R17), so this is a
        // join on in-flight warm-up, not a trigger.
        self.wait_for_index_settled(SEARCH_INDEX_SETTLE_TIMEOUT);

        // Distinguish a scheme query (a leading `(` — `(Fn …)`, `(Vec Int)`)
        // from a name query (a bare fragment, possibly FQ-leaf like
        // `primitives/Int`). A bare FQ type-leaf (`primitives/Int`) is treated
        // as a SCHEME query so structural-contains matches schemes mentioning
        // that type (spec §17.19.1 example). Heuristic: if it parses as a type
        // expression that resolves to a real `Type`, search Index B; otherwise
        // fall back to a name (Index A) search.
        // Collect the raw hits per the query shape (spec §17.19.1):
        //   - a scheme-shaped query (leading `(` or FQ leaf) → the SCHEME axis;
        //   - a plain-text query → BOTH the NAME axis and the DOCSTRING axis,
        //     merged so a symbol matching on both keeps its stronger (name) tier.
        let scheme_hits = self.try_search_by_scheme(query);
        let is_name_query = scheme_hits.is_none();
        let hits = match scheme_hits {
            Some(scheme_hits) => scheme_hits,
            None => self.collect_name_and_docstring_hits(query),
        };

        // Scope filter (spec §17.19 + R13, S106): a symbol already resident in the
        // current session is normally excluded (`/search` covers what is
        // importable-but-not-yet-in-scope). EXCEPTION: an EXACT-name match is
        // surfaced regardless of scope — shown MARKED when it is already in scope.
        // Partial / scheme hits keep the old behaviour (in-scope ⇒ excluded).
        let current = self.current_module_path();
        use crate::session_v4::index_worker::MatchTier;
        let mut rows: Vec<SearchRow> = hits
            .into_iter()
            .filter_map(|hit| {
                // §8.2.3 subtree visibility (0570 residual): a private `(mod- X)`
                // submodule's symbol is NOT importable from outside its subtree, so
                // it must not be a `/search` row (whose import hint §8.2.3 rejects)
                // for a searcher outside that subtree — regardless of match tier
                // (an EXACT name match is no more importable). The single privacy
                // enforcement point over the assembled index: covers every feed,
                // including the loaded-module E3 feed that bypasses the arm-time
                // file-worklist drop.
                if !self
                    .shared
                    .importable_indices
                    .search_visible_from(&hit.module, &current)
                {
                    return None;
                }
                let in_scope = self.is_already_in_scope(&hit.name, &hit.module, &current);
                if hit.tier == MatchTier::ExactName || !in_scope {
                    Some(SearchRow { hit, in_scope })
                } else {
                    None // a partial / scheme match already in scope stays excluded
                }
            })
            .collect();

        // Exact-in-scope synthesis (R13): an exact-name match resolvable bare in
        // the current scope but NOT present in the index (e.g. a prelude symbol,
        // which the indexer excludes) must still surface, marked. Only for a
        // plain-text (name) query.
        if is_name_query
            && let Some(hit) = self.exact_in_scope_hit(query)
            && !rows
                .iter()
                .any(|r| r.hit.name == hit.name && r.hit.module == hit.module)
        {
            rows.push(SearchRow { hit, in_scope: true });
        }

        // Dedup identical (name, module) rows (a symbol may match on more than one
        // axis in the same collection), keeping the strongest tier.
        rows.sort_by(|a, b| {
            (a.hit.module.as_ref(), a.hit.name.as_ref())
                .cmp(&(b.hit.module.as_ref(), b.hit.name.as_ref()))
                .then(a.hit.tier.cmp(&b.hit.tier))
        });
        rows.dedup_by(|a, b| a.hit.name == b.hit.name && a.hit.module == b.hit.module);

        // Relevance ranking (spec §17.19.1a): total order by tier (strongest
        // first), alphabetical (module, name) tie-break within a tier for
        // deterministic output (§17.19.5).
        rows.sort_by(|a, b| {
            a.hit
                .tier
                .cmp(&b.hit.tier)
                .then((a.hit.module.as_ref(), a.hit.name.as_ref()).cmp(&(
                    b.hit.module.as_ref(),
                    b.hit.name.as_ref(),
                )))
        });

        // Progress note when the burn-down is still in flight (spec §17.19.3).
        // Serving the note latches `note_shown` — the timing-(b) gate for the
        // `search index complete.` completion notice (spec §17.19.3, S108): the
        // completion notice fires only after a not-ready note was shown this
        // session, so a session that never saw the index building is never told
        // it finished.
        let pending = self.shared.importable_indices.pending_count();
        let not_ready_note = Self::indexing_note_text(pending);
        if not_ready_note.is_some() {
            self.shared.importable_indices.mark_note_shown();
        }

        if rows.is_empty() {
            return Self::empty_result_message(query, pending);
        }

        // Lead with a newline so the first result row starts on its own line
        // below the prompt (matching the spec §17.19.2 examples, which show the
        // rows beneath the `user> /search …` line) rather than glued to the
        // prompt in a non-TTY/piped session where the input is not echoed.
        let mut out = StyledDoc::new();
        out.plain("\n");
        for row in &rows {
            out.extend(self.render_search_row(row, query));
        }
        // A partial (still-indexing) result appends the not-ready note beneath
        // the rows it DID find (§17.19.3 partial-results-plus-a-note); a complete
        // result has no note (R6 lifecycle metadata).
        if let Some(note) = &not_ready_note {
            push_metadata(&mut out, note.clone());
        }
        // Trim trailing newlines from the rendered text (the `\n` are Plain, so
        // popping them is byte-safe under both colour modes).
        let mut rendered = render(&out);
        while rendered.ends_with('\n') {
            rendered.pop();
        }
        rendered
    }

    /// Collect the NAME-axis and DOCSTRING-axis hits for a plain-text query
    /// (spec §17.19.1) and merge them: a symbol matching on both axes keeps its
    /// stronger (name) tier — it is NOT re-reported as a docstring-only hit
    /// (§17.19.1a tier 6). Dedup key is `(name, module)`.
    fn collect_name_and_docstring_hits(
        &self,
        query: &str,
    ) -> Vec<crate::session_v4::index_worker::SearchHit> {
        let mut hits = self.shared.importable_indices.search_by_name(query);
        let mut seen: std::collections::HashSet<(String, String)> = hits
            .iter()
            .map(|h| (h.name.to_string(), h.module.to_string()))
            .collect();
        for doc_hit in self.shared.importable_indices.search_by_docstring(query) {
            let key = (doc_hit.name.to_string(), doc_hit.module.to_string());
            if seen.insert(key) {
                hits.push(doc_hit);
            }
        }
        hits
    }

    /// Synthesize an exact-in-scope `SearchHit` for `query` when it resolves
    /// bare in the current scope to a `Def` (R13, S106) — e.g. a prelude symbol,
    /// which the importable index deliberately excludes. Returns `None` when the
    /// query does not resolve, or resolves to a non-`Def` (special form, type).
    fn exact_in_scope_hit(
        &self,
        query: &str,
    ) -> Option<crate::session_v4::index_worker::SearchHit> {
        use crate::session_v4::index_worker::{MatchTier, SearchHit};
        let (entry, module) = self.lookup_with_prelude_fallback(query)?;
        let (resolved, origin) = self.resolve_entry_for_display(&entry, &module);
        if let ModuleEntry::Def { scheme, docstring, kind, .. } = resolved {
            Some(SearchHit {
                name: Symbol::from(query),
                module: origin,
                scheme: scheme.ty.clone(),
                docstring: docstring.clone(),
                tier: MatchTier::ExactName,
                is_macro: matches!(kind.as_ref(), DefKind::Macro { .. }),
            })
        } else {
            None
        }
    }

    /// Render one `/search` result row — the facets of spec §17.19.2. Facet 4 is
    /// the `(import …)` form, REPLACED by the `already in scope — no import
    /// needed` marker for an exact in-scope match (R13); facet 5 is the `; doc:`
    /// excerpt, present ONLY on a docstring-only hit (§17.19.1a tier 6).
    fn render_search_row(&self, row: &SearchRow, query: &str) -> StyledDoc {
        render_search_row_doc(row, query)
    }

    /// Bounded wait for the importable-symbol burn-down to drain (pending → 0).
    /// Polls the worklist count; returns early when settled or when `timeout`
    /// elapses (then `/search` serves partial results + the progress note). A
    /// no-op when the index was never armed (batch mode — but `/search` is a
    /// REPL command, so this only runs in REPL).
    fn wait_for_index_settled(&self, timeout: std::time::Duration) {
        let deadline = std::time::Instant::now() + timeout;
        while self.shared.importable_indices.pending_count() > 0 {
            if std::time::Instant::now() >= deadline {
                return;
            }
            std::thread::sleep(SEARCH_INDEX_SETTLE_POLL);
        }
    }

    /// Try to parse `query` as a type-scheme and search Index B (exact OR
    /// partial). Returns `None` if the query does not parse/resolve as a type
    /// (→ the caller does a name search instead).
    fn try_search_by_scheme(
        &self,
        query: &str,
    ) -> Option<Vec<crate::session_v4::index_worker::SearchHit>> {
        // Only attempt a scheme parse for a query that looks like a type: a
        // leading `(` (a compound type form) or an FQ type-leaf (`mod/Type`).
        let looks_like_type = query.starts_with('(') || query.contains('/');
        if !looks_like_type {
            return None;
        }
        let expr = cranelisp_frontend::parse_type_expr(query).ok()?;
        let module = self.current_module_path();
        let mut ctx =
            cranelisp_typecheck::SymbolTableAccess::live(&self.shared.symbol_tables, module.clone());
        let ty = cranelisp_typecheck::check_type_expr(
            &expr,
            &mut ctx,
            &self.shared.symbol_tables,
            &self.shared.module_aliases,
            &self.shared.prelude_fallback,
            &module,
            Span::SYNTHETIC,
        )
        .ok()?;
        Some(self.shared.importable_indices.search_by_scheme(&ty))
    }

    /// Whether `name` (from originating `module`) is ALREADY in scope in
    /// `current` — i.e. already imported (resolves locally and chains to the
    /// same originating module) or natively defined there. Such a symbol is
    /// resident, not reachable-but-unimported, so `/search` must not re-offer it
    /// with an `(import …)` form (spec §17.19 — the already-imported `_neg`).
    fn is_already_in_scope(
        &self,
        name: &Symbol,
        module: &ModuleFullPath,
        current: &ModuleFullPath,
    ) -> bool {
        // A symbol defined natively in / imported into the current module:
        // resolve it locally; if it resolves to the SAME originating module it
        // is already in scope.
        if current == module {
            return true;
        }
        match self.lookup_with_prelude_fallback(name.as_ref()) {
            Some((ModuleEntry::Import { source, .. }, _)) => &source.module == module,
            Some((_, resolved_module)) => &resolved_module == module,
            None => false,
        }
    }

    /// Whether `sym` (a bare name) is bound anywhere in the live session —
    /// the current module, prelude (outer scope), or any loaded module.
    /// Used by `/refs`/`/tests-for` to distinguish a typo (unbound) from a
    /// genuinely-unreferenced symbol (repl/spec.md §17.6.1, §4.1.10).
    pub(crate) fn symbol_is_bound(&self, sym: &str) -> bool {
        if self.lookup_with_prelude_fallback(sym).is_some() {
            return true;
        }
        // Also accept a name defined in any loaded module (the scan target may
        // be a symbol the user names without it being in the current scope).
        self.shared
            .symbol_tables
            .iter()
            .any(|t| t.get(sym).is_some())
    }

    /// Scan every loaded module's definitions for bodies that reference `target`.
    ///
    /// Returns the fully-qualified names of referring definitions, sorted. When
    /// `tests_only` is set, only test functions (the `test-` prefix +
    /// nullary-test shape, §16.1) are considered (the `/tests-for` filter).
    ///
    /// Reference detection (§9.2): a body references `target` if `target`
    /// appears as a whole symbol token in the definition's stored source. The
    /// scan reads the int `Introspection.source` (REPL-evaled defns) or its
    /// `sexp`; a definition with no stored body (e.g. cache-restored modules
    /// carrying no introspection) cannot be scanned and is skipped. This is the
    /// MVP token-scan; an AST-walk refinement is noted in the design as a later
    /// precision knob.
    pub(crate) fn scan_referers(&self, target: &str, tests_only: bool) -> Vec<String> {
        let mut referers: Vec<String> = Vec::new();
        let intr = match self.shared.introspection.as_ref() {
            Some(m) => m,
            None => return referers, // batch mode: no introspection store.
        };
        for table in self.shared.symbol_tables.iter() {
            let module = table.key().clone();
            for (name, entry) in table.defined_symbols() {
                // A symbol never counts as referencing itself.
                if name.as_ref() == target {
                    continue;
                }
                if tests_only && !is_test_function(name.as_ref(), entry) {
                    continue;
                }
                let fq = FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                };
                let Some(record) = intr.get(&fq) else {
                    continue;
                };
                if body_references(&record, target) {
                    referers.push(format!("{}/{}", module.as_ref(), name.as_ref()));
                }
            }
        }
        referers.sort();
        referers.dedup();
        referers
    }
}


#[cfg(test)]
mod search_message_selection_tests {
    
    
    

    use super::CompilerSession;

    // spec: repl/spec.md §17.19.3 (S108, I-2) — an EMPTY `/search` result MUST
    // NOT conflate the two distinct states. While the burn-down is in flight
    // (pending > 0) the reader is served ONLY the "indexing N modules…" note
    // (retry), never the "no importable symbols matched" note. This asserts the
    // still-indexing branch of the pure message selector serves the note and
    // does NOT emit the no-match text.
    #[test]
    fn empty_result_still_indexing_serves_only_the_note_not_no_match() {
        let msg = CompilerSession::empty_result_message("foo", 3);
        assert!(
            msg.contains("indexing 3 module(s)…"),
            "still-indexing empty result must serve the not-ready note, got: {msg:?}"
        );
        assert!(
            !msg.contains("no importable symbols matched"),
            "still-indexing empty result must NOT serve the no-match note (§17.19.3 \
             non-conflation), got: {msg:?}"
        );
    }

    // spec: repl/spec.md §17.19.3 (S108, I-2) — the COMPLETE-index empty result
    // (pending == 0) is the OTHER state: it serves ONLY the "no importable
    // symbols matched" note (rephrase) and NEVER the "indexing N…" note. The two
    // asserts together pin the non-conflation from both sides.
    #[test]
    fn empty_result_complete_index_serves_only_no_match_not_the_note() {
        let msg = CompilerSession::empty_result_message("foo", 0);
        assert!(
            msg.contains("no importable symbols matched"),
            "complete-index empty result must serve the no-match note, got: {msg:?}"
        );
        // The note must NOT echo the query — a filtered private name (§8.2.3,
        // 0570) must not re-surface through the miss note.
        assert!(
            !msg.contains("foo"),
            "the no-match note must not echo the query, got: {msg:?}"
        );
        assert!(
            !msg.contains("indexing"),
            "complete-index empty result must NOT serve the not-ready note (§17.19.3 \
             non-conflation), got: {msg:?}"
        );
    }

    // spec: repl/spec.md §17.19.3 — the note text is `Some` only while pending,
    // `None` at completion (the single source both the empty-result and the
    // partial-append paths derive from).
    #[test]
    fn indexing_note_text_present_iff_pending() {
        assert!(CompilerSession::indexing_note_text(0).is_none(), "complete → no note");
        assert_eq!(
            CompilerSession::indexing_note_text(2).as_deref(),
            Some("; indexing 2 module(s)… (results may be incomplete)"),
            "pending → the not-ready note text"
        );
    }
}

#[cfg(test)]
mod search_excerpt_tests {
    use super::*;
    
    

    

    // spec: repl/spec.md §17.19.2 facet 5 — the docstring excerpt is produced
    // around the matched substring, elided with `…` when the docstring extends
    // past the window.
    #[test]
    fn excerpt_surrounds_match_with_ellipses() {
        // The match sits well inside a docstring long enough on BOTH sides to
        // overflow the window, so both ellipses appear.
        let doc = "a long preamble that pads out the left side beyond the window, computes the \
                   greatest common divisor of two integers, and then keeps going far past the \
                   right edge of the window too";
        let ex = docstring_excerpt(doc, "greatest common").expect("query is present");
        assert!(ex.contains("greatest common"), "excerpt shows the match: {ex:?}");
        assert!(ex.starts_with("… ") && ex.ends_with(" …"), "elided both ends: {ex:?}");
    }

    // spec: repl/spec.md §17.19.2 facet 5 — a query absent from the docstring
    // yields no excerpt (the caller then omits the facet).
    #[test]
    fn excerpt_absent_query_is_none() {
        assert!(docstring_excerpt("some documentation text", "absent").is_none());
    }

    // spec: src/CLAUDE.md — never panic on user input. A docstring whose
    // lowercase form is a DIFFERENT byte length than the original (`İ`, U+0130,
    // is 2 bytes but lowercases to `i` + U+0307 = 3 bytes) must not panic: a byte
    // offset into `doc.to_lowercase()` is NOT a valid boundary in the original
    // `doc`. Regression guard for the Unicode byte-offset bug (/review Important).
    #[test]
    fn excerpt_case_length_changing_docstring_no_panic() {
        // `İİx`: two U+0130 chars (2 bytes each) then `x` — original len 5 bytes;
        // lowercased len 7 bytes. The match for `x` is at lowercased byte 6, which
        // is out of bounds in the 5-byte original. Must not panic and must show x.
        let doc = "İİx";
        let ex = docstring_excerpt(doc, "x").expect("query `x` is present");
        assert!(ex.contains('x'), "excerpt contains the match: {ex:?}");

        // A `ß`/`SS` case-fold widening in the middle of the text: the match after
        // it must still land on a valid original boundary.
        let doc2 = "straße number is the key detail here in the docs";
        let ex2 = docstring_excerpt(doc2, "NUMBER").expect("case-insensitive match");
        assert!(ex2.contains("number"), "excerpt contains the match: {ex2:?}");
    }
}

#[cfg(test)]
mod fq_arg_search_tests {
    use super::*;
    
    
    use crate::repl::test_support::*;
    
    use cranelisp_types::{
        ModuleFullPath,
        Symbol, Visibility,
    };
    

    // §8.8.1 at the `/search` synthesis seam: `exact_in_scope_hit` synthesizes an
    // in-scope result row for an exact query that resolves bare but is absent from
    // the public index (a prelude symbol). It inherits the `lookup_with_prelude_
    // fallback` public-only gate, so a PRIVATE prelude head synthesizes NO row
    // (None) — the private name never appears as a `/search` result. A PUBLIC
    // prelude head still synthesizes its row. spec: repl/spec.md §17.19 (R13)
    #[test]
    fn exact_in_scope_hit_drops_private_prelude_head() {
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let scope = s.current_module_path();
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(Symbol::from("secret"), userfn_def_vis(Visibility::Private));
        ptbl.insert(Symbol::from("shown"), userfn_def_vis(Visibility::Public));
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        s.shared.prelude_fallback.insert(scope, true);

        assert!(
            s.exact_in_scope_hit("secret").is_none(),
            "a PRIVATE prelude binding MUST NOT synthesize a `/search` result row \
             (§8.8.1) — the leak the public-only gate closes"
        );
        assert!(
            s.exact_in_scope_hit("shown").is_some(),
            "a PUBLIC prelude binding still synthesizes its in-scope `/search` row"
        );
    }
}

#[cfg(test)]
mod styling_search_row_tests {
    use super::*;
    
    
    use crate::style::test_support::ColorGuard;

    // K7 — a `/search` row: the `:Type` sig is R4 cyan, the name R15, the `in
    // <module>` column R7 dim, the `(import …)` snippet Plain; the `\n` line
    // breaks stay Plain (§10.3 K7 composition). Fail-on-revert pin for the
    // `render_search_row_doc` role composition.
    // spec: repl/spec.md §10.3 R4/R7/R15 — `/search` result row.
    #[test]
    fn colour_on_k7_search_row_composition() {
        use crate::session_v4::index_worker::{MatchTier, SearchHit};
        let _g = ColorGuard::force(true);
        let row = SearchRow {
            hit: SearchHit {
                name: Symbol::from("count"),
                module: ModuleFullPath::from("collections.vec"),
                scheme: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                docstring: None,
                tier: MatchTier::ExactName,
                is_macro: false,
            },
            in_scope: false,
        };
        assert_eq!(
            render(&render_search_row_doc(&row, "count")),
            "\x1b[36m:(Fn [primitives/Int] primitives/Int)\x1b[0m count\n  in \
             \x1b[2mcollections.vec\x1b[0m   — (import [collections.vec [count]])\n"
        );
    }
    // 0569 / §17.19.2a — a MACRO search row's primary line is the canonical
    // `:{module}/{name} ; defmacro [- doc]` envelope (mirroring bare lookup),
    // NEVER the placeholder scalar `:Type` the macro's `scheme.ty` would render.
    // spec: repl/spec.md §17.19.2a — macro `/search` row classification.
    #[test]
    fn search_row_macro_renders_defmacro_envelope_not_scalar_type() {
        use crate::session_v4::index_worker::{MatchTier, SearchHit};
        let row = SearchRow {
            hit: SearchHit {
                name: Symbol::from("twice"),
                module: ModuleFullPath::from("macx"),
                // A placeholder scalar scheme (as a real macro entry carries) —
                // it MUST NOT reach the rendered row.
                scheme: Type::Int,
                docstring: Some("double it".to_string()),
                tier: MatchTier::ExactName,
                is_macro: true,
            },
            in_scope: false,
        };
        let rendered = render(&render_search_row_doc(&row, "twice"));
        assert!(
            rendered.contains(":macx/twice") && rendered.contains("; defmacro"),
            "macro row must carry the `:macx/twice ; defmacro` envelope, got: {rendered:?}"
        );
        assert!(
            rendered.contains("double it"),
            "the macro's docstring rides the `; defmacro` comment, got: {rendered:?}"
        );
        assert!(
            !rendered.contains(":primitives/Int") && !rendered.contains(":(Fn"),
            "a macro row MUST NOT render a placeholder scalar `:Type`, got: {rendered:?}"
        );
    }
}
