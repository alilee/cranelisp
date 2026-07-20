// agent/harvest.rs — the harvester + relevance ranker (design/int/agent.md §5).
//
// "Push the shape of everything; pull the bodies" (`repl-embedded-agent.md §4.3`).
// Every turn, the harvester assembles a context block from in-process FREE
// signals — it READS the live symbol tables / introspection the compiler just
// wrote (Principle 7: the symbol table is the single source of truth; the harvest
// is a read, never a copy-store). Token budget is the governing constraint (§5.4):
// omniscient ≠ dump everything.
//
// Push priority (§5.2), the graceful-degradation ladder (§5.4):
//   1. Current module — full source, PINNED (never dropped; the floor).
//   2. Last ~6 mentioned modules — preamble (`SymbolTable.module_preamble`,
//      FIXME 0428) + export surface (public `defined_symbols`).
//   3. Last ~10 mentioned fns — full source (`get_introspection(fq).source`).
// "Mentioned" = named in the turn text or surfaced this session. Under budget
// pressure the cheapest-value tail drops first; the current module survives at
// the floor.

#![cfg(feature = "agent")]

use crate::session_v4::CompilerSession;

/// Max mentioned modules / fns carried (§5.2 "last ~6 modules", "last ~10 fns").
const MAX_MENTIONED_MODULES: usize = 6;
const MAX_MENTIONED_FNS: usize = 10;

/// A rough char-per-token proxy for the budget (§5.4). The budget is expressed
/// in approximate tokens; we gate on chars at ~4 chars/token. This is a tuning
/// knob, not architecture (§5.2).
const CHARS_PER_TOKEN: usize = 4;

/// Default token budget for the harvested push (§5.4 — a runtime-config knob in
/// the full design; a constant here for the MVP). Generous: the current module
/// pin plus a handful of mentioned fns/modules.
pub const DEFAULT_TOKEN_BUDGET: usize = 4000;

/// Testability seam (Principle 5, §23.2 / test-plan "Testability seams" #2): an
/// env lever that forces a small in-process `char_budget` so the budget-degrade
/// ladder of the `== in scope ==` block can be exercised e2e. Sibling to the
/// §17.10 agent env surface; agent-gated (this whole module is
/// `#[cfg(feature = "agent")]`). Absent / unparseable ⇒ no override (the
/// `token_budget` argument's `char_budget` stands). The value is a CHAR budget
/// (not tokens) — the harvester gates on chars (`CHARS_PER_TOKEN`).
const HARVEST_BUDGET_ENV: &str = "CRANELISP_AGENT_HARVEST_BUDGET";

impl CompilerSession {
    /// Assemble the harvested context block for a turn (§5), under `token_budget`.
    ///
    /// `mentions` are the symbol/module names named in the turn (and, in a fuller
    /// design, accumulated across the session); the harvester ranks by mention +
    /// recency and pushes the top-budget slice. The current module's full source
    /// is the PINNED floor — included first, never dropped (§5.4).
    pub(crate) fn harvest_context(&self, mentions: &[String], token_budget: usize) -> String {
        // The char budget governs the §5.4 graceful-degradation ladder. The
        // `CRANELISP_AGENT_HARVEST_BUDGET` test lever (§23.2) forces a small
        // in-process budget so the `== in scope ==` grain-degrade ladder can be
        // exercised e2e; absent / unparseable ⇒ the `token_budget` argument's
        // char budget stands.
        let char_budget = std::env::var(HARVEST_BUDGET_ENV)
            .ok()
            .and_then(|v| v.trim().parse::<usize>().ok())
            .unwrap_or_else(|| token_budget.saturating_mul(CHARS_PER_TOKEN));
        let mut out = String::new();

        // 1. Current module — full source, PINNED (§5.2 #1, the §5.4 floor).
        //    Always included even if it alone exceeds the budget: the agent must
        //    never be blind to the user's cursor context.
        let cur = self.current_module_path();
        out.push_str(&format!("== Current module: {} ==\n", cur.as_ref()));
        // The current module's preamble is part of its pinned context (§5.2 #1 /
        // §17.3 read-back): a Document-mode preamble edit on the cursor module
        // must surface in the very next turn's harvest, and on a fresh session
        // the regenerated `.cl`'s captured `module_preamble` is read back here —
        // the rung-6-write → rung-3-read loop ("memory is the code"). The
        // mentioned-module arm (#2) covers OTHER modules; this covers the cursor
        // module (which #2 skips because it is already pinned).
        if let Some(table) = self.shared.symbol_tables.get(&cur)
            && let Some(preamble) = table.module_preamble.as_ref()
        {
            out.push_str(&format!("== module {} preamble ==\n{preamble}\n", cur.as_ref()));
        }
        self.push_module_full_source(&cur, &mut out);

        // 1a. Recent-errored-turn feed (E5, §5.5) — the fourth harvest source.
        //     A failed `(defn …)` never commits, so it is absent from every
        //     symbol table and therefore from the committed-state harvest above;
        //     this ring is the ONLY place that signal lives. Emitted right after
        //     the current-module pin so it rides high on the §5.4 ladder: the
        //     single most-recent errored turn is PINNED to the floor (never
        //     dropped — the uniquely-unrecoverable signal), older errored turns
        //     degrade next, and green turns (kept only for deixis — "that" / "the
        //     last one") are the first to drop.
        self.push_recent_turns_block(char_budget, &mut out);

        // 1b. == in scope == — Pillar 2 (§23): ambient awareness of every symbol
        //     in scope (current-module own defns + explicit imports + implicit
        //     prelude) at name + `:Type` signature + docstring grain, so the
        //     agent never has to spend a turn on `/list`/`/imports`/`/exports`
        //     before referencing an in-scope signature. The block rides the same
        //     `char_budget` ladder; under pressure it degrades GRAIN (sig+doc →
        //     sig → name) per symbol, never silently truncating the symbol LIST
        //     (`repl/spec.md §17.18.2`).
        self.push_in_scope_block(&cur, char_budget, &mut out);

        // Partition the mentions into modules and fns/symbols. A mention is a
        // module if a symbol table exists at that path; otherwise treat it as a
        // (possibly fn) symbol. De-dupe, preserve mention order (recency proxy:
        // earlier-listed = more recently named by the caller).
        let mut seen = std::collections::HashSet::new();
        let mut mentioned_modules: Vec<String> = Vec::new();
        let mut mentioned_fns: Vec<String> = Vec::new();
        for m in mentions {
            let m = m.trim();
            if m.is_empty() || !seen.insert(m.to_string()) {
                continue;
            }
            if m == cur.as_ref() {
                continue; // already pinned as the current module
            }
            if self.shared.symbol_tables.contains_key(&cranelisp_types::ModuleFullPath::from(m)) {
                mentioned_modules.push(m.to_string());
            } else if self.symbol_is_mentionable(m) {
                mentioned_fns.push(m.to_string());
            }
        }
        mentioned_modules.truncate(MAX_MENTIONED_MODULES);
        mentioned_fns.truncate(MAX_MENTIONED_FNS);

        // 2. Last ~10 mentioned fns — full source (§5.2 #3). Higher value than
        //    module preambles, so push these before module surfaces (the ladder
        //    drops preambles before fn bodies). Each addition is budget-gated.
        let mut fn_block = String::new();
        for f in &mentioned_fns {
            if let Some(src) = self.get_introspection(f).and_then(|i| i.source.clone()) {
                fn_block.push_str(&format!("== fn {f} ==\n{src}\n"));
            }
        }
        if !fn_block.is_empty() && out.len() + fn_block.len() <= char_budget {
            out.push_str(&fn_block);
        }

        // 3. Last ~6 mentioned modules — preamble + exports (§5.2 #2). The
        //    cheapest-value tail: preamble first, then exports; under tight budget
        //    the whole block (or just preambles) drops (§5.4 ladder).
        let mut with_preamble = String::new();
        let mut exports_only = String::new();
        for module in &mentioned_modules {
            let mp = cranelisp_types::ModuleFullPath::from(module.as_str());
            if let Some(table) = self.shared.symbol_tables.get(&mp) {
                let exports: Vec<String> = table
                    .public_symbols()
                    .map(|(s, _)| s.as_ref().to_string())
                    .collect();
                let exports_line = format!("== module {module} exports ==\n{}\n", exports.join(" "));
                exports_only.push_str(&exports_line);

                let mut block = String::new();
                if let Some(preamble) = table.module_preamble.as_ref() {
                    block.push_str(&format!("== module {module} preamble ==\n{preamble}\n"));
                }
                block.push_str(&exports_line);
                with_preamble.push_str(&block);
            }
        }
        // Ladder: prefer preamble+exports; if that overflows, exports only; if
        // even that overflows, drop the module block entirely (floor reached).
        if !with_preamble.is_empty() && out.len() + with_preamble.len() <= char_budget {
            out.push_str(&with_preamble);
        } else if !exports_only.is_empty() && out.len() + exports_only.len() <= char_budget {
            out.push_str(&exports_only);
        }

        out
    }

    /// Push the `== in scope ==` block (§23): every symbol in scope of the
    /// current module, at name + `:Type` signature + docstring grain.
    ///
    /// The three feeders (§23.1 / `repl/spec.md §17.18.1`):
    ///   1. current-module own defns — `defined_symbols()`;
    ///   2. explicit imports — the current module's `ModuleEntry::Import` entries,
    ///      resolved through the import chain to the canonical entry (mirroring
    ///      `resolve_entry_for_display`, the path `/sig` / bare-symbol display use);
    ///   3. implicit prelude — `prelude_implicit_names()` (gated on the
    ///      `prelude_fallback` bit), each resolved to its canonical prelude entry.
    ///
    /// The signature rendering REUSES the existing FQ formatter (Principle 7 —
    /// single source of truth): `format_def_entry` → `format_scheme_display` →
    /// `display::format_type_qualified`, which qualifies primitive names
    /// (`primitives/Int`) exactly as the bare-symbol display does when a human
    /// types the name. No second signature formatter is written here.
    ///
    /// Budget degrades GRAIN, not membership (§23.2): the block is assembled per
    /// symbol at the richest grain that still fits the running `char_budget`,
    /// dropping the docstring first, then the signature, never the NAME.
    fn push_in_scope_block(
        &self,
        cur: &cranelisp_types::ModuleFullPath,
        char_budget: usize,
        out: &mut String,
    ) {
        // Collect (name, rendered-grains) for every in-scope symbol. De-dupe by
        // name (own defn shadows an import of the same name; explicit import
        // shadows the implicit prelude).
        let mut seen = std::collections::HashSet::new();
        let mut entries: Vec<InScopeEntry> = Vec::new();

        // 1. Current-module own defns + 2. explicit imports — both live in the
        //    current module's own table. COLLECT owned `(name, entry)` pairs while
        //    holding the table guard, then DROP the guard BEFORE resolve/render
        //    (0666): `render_in_scope_entry` → `format_def_entry_doc` re-acquires
        //    `symbol_tables.get(module)` (the D1 overloaded read-follow), a
        //    same-shard recursive read that can deadlock a queued writer under
        //    `--features agent` if the `cur` guard is still held. Collect-then-
        //    render closes the window. Skip mangled overload/multi-sig variants,
        //    the synthetic `__expr` wrapper, and special forms (mirrors the
        //    `/list` filter, shared `is_internal_listing_name`).
        let own: Vec<(String, cranelisp_types::ModuleEntry<crate::code::Code>)> =
            if let Some(table) = self.shared.symbol_tables.get(cur) {
                table
                    .all_symbols()
                    .filter(|(sym, entry)| {
                        !crate::worker::is_internal_listing_name(sym.as_ref())
                            && !matches!(entry, cranelisp_types::ModuleEntry::SpecialForm { .. })
                    })
                    .map(|(sym, entry)| (sym.as_ref().to_string(), entry.clone()))
                    .collect()
            } else {
                Vec::new()
            };
        for (name, entry) in own {
            if !seen.insert(name.clone()) {
                continue;
            }
            // Resolve an import to the canonical entry + its defining module so the
            // rendered signature is the real one (FQ), mirroring `/sig` for a
            // re-exported name. ALL feeders render at full grain by default (§23.1 /
            // `repl/spec.md §17.18.1`); the §23.2 budget ladder drops the docstring
            // under pressure, not the symbol's SOURCE. No table guard is held here.
            let (resolved, home) = self.resolve_entry_for_display(&entry, cur);
            entries.push(self.render_in_scope_entry(&resolved, &name, &home));
        }

        // 3. Implicit prelude — gated on the `prelude_fallback` bit by
        //    `prelude_implicit_names`. Same collect-then-render discipline (0666):
        //    gather owned entries under the prelude guard, drop it, then render.
        //    `prelude_implicit_names()` is read BEFORE the guard (it consults
        //    session state).
        let prelude_path = cranelisp_types::ModuleFullPath::from("prelude");
        let prelude_names = self.prelude_implicit_names();
        let prelude_entries: Vec<(String, cranelisp_types::ModuleEntry<crate::code::Code>)> =
            if let Some(ptable) = self.shared.symbol_tables.get(&prelude_path) {
                prelude_names
                    .into_iter()
                    .filter_map(|name| ptable.get(&name).map(|e| (name, e.clone())))
                    .collect()
            } else {
                Vec::new()
            };
        for (name, entry) in prelude_entries {
            if !seen.insert(name.clone()) {
                continue; // an own defn / explicit import already shadows it
            }
            // Implicit-prelude symbols render at full grain too (§23.1); the guard
            // is already dropped, so the D1 read-follow cannot deadlock.
            let (resolved, home) = self.resolve_entry_for_display(&entry, &prelude_path);
            entries.push(self.render_in_scope_entry(&resolved, &name, &home));
        }

        if entries.is_empty() {
            return;
        }

        // Emit the block, degrading grain per symbol to fit the running budget.
        // The header is part of the floor — once we commit to emitting symbols,
        // every NAME survives (names-only floor); only the per-symbol DETAIL
        // (docstring, then signature) is dropped under pressure (§23.2).
        let header = "== in scope ==\n";
        out.push_str(header);
        for e in &entries {
            // Pick the richest grain whose line still fits the remaining budget;
            // the name-only line is the floor and is emitted even if it overflows
            // (the symbol must never be silently absent).
            // `< char_budget` (not `+ 1 <=`) leaves room for the trailing
            // newline pushed after each line.
            let line = if out.len() + e.full.len() < char_budget {
                &e.full
            } else if out.len() + e.sig.len() < char_budget {
                &e.sig
            } else {
                &e.name
            };
            out.push_str(line);
            out.push('\n');
        }
    }

    /// Render one in-scope symbol at all three grains (§23.2 ladder rungs):
    /// `full` (name + `:Type` sig + docstring), `sig` (name + `:Type` sig, no
    /// docstring), `name` (bare name floor). Reuses `format_def_entry` (the FQ
    /// renderer) for the rich grains — Principle 7, no second formatter.
    fn render_in_scope_entry(
        &self,
        entry: &cranelisp_types::ModuleEntry<crate::code::Code>,
        name: &str,
        home: &cranelisp_types::ModuleFullPath,
    ) -> InScopeEntry {
        // Sig grain: name + FQ `:Type` signature, docstring stripped. Clearing
        // the docstring and re-rendering through the SAME formatter keeps it the
        // single source of truth (Principle 7) rather than string-stripping.
        let stripped = strip_entry_docstring(entry.clone());
        // FIXME 0542: harvest renders the bare-symbol display a human gets by
        // typing the name — the pure-introspection grain — byte-identical to a
        // bare lookup / `/sig` (FIXME 0647: an empty trait `; impl:` section is
        // omitted uniformly, no bare-lookup-vs-echo flag).
        let sig = self.format_def_entry(&stripped, name, home);
        // Full grain: name + FQ `:Type` signature + docstring — the bare-symbol
        // display a human gets by typing the name. EVERY feeder (own defn,
        // explicit import, implicit prelude) carries its docstring at full grain
        // (§23.1 / `repl/spec.md §17.18.1` — all three feeders carry the
        // docstring facet, incl. a primitive's §A.5 Description). The §23.2
        // budget ladder, not the symbol's source, drops the docstring (full →
        // sig → name) under pressure — `strip_entry_docstring` is that sig rung,
        // never the default for imports/prelude.
        let full = self.format_def_entry(entry, name, home);
        InScopeEntry { name: name.to_string(), sig, full }
    }

    /// Push the full source of a module — every defined symbol's stored source —
    /// into `out`. Reads the int `Introspection.source` for REPL-evaled defns;
    /// falls back to the symbol table's recorded `source_text` when present.
    fn push_module_full_source(&self, module: &cranelisp_types::ModuleFullPath, out: &mut String) {
        if let Some(table) = self.shared.symbol_tables.get(module) {
            let names: Vec<String> = table
                .defined_symbols()
                // Exclude internal compiler artifacts ($-mangled names + the
                // synthetic `__expr` wrapper) from the harvested module source.
                .filter(|(s, _)| !crate::worker::is_internal_listing_name(s.as_ref()))
                .map(|(s, _)| s.as_ref().to_string())
                .collect();
            for name in names {
                if let Some(src) = self.get_introspection(&name).and_then(|i| i.source.clone()) {
                    out.push_str(&src);
                    out.push('\n');
                }
            }
        }
    }

    /// Push the recent-errored-turn feed (E5, §5.5(3)) — the ring of recent REPL
    /// eval turns, surfaced **errored-first, newest-first**. The single
    /// most-recent errored turn is PINNED (emitted unconditionally, even past the
    /// budget — the uniquely-unrecoverable signal committed state cannot
    /// reconstruct); older errored turns and any green turns (kept for deixis)
    /// are budget-gated, green turns dropping first. A no-op when the agent is
    /// unconfigured or the ring is empty.
    fn push_recent_turns_block(&self, char_budget: usize, out: &mut String) {
        use crate::agent::types::ReplTurn;

        let ring = match self.agent.as_ref() {
            Some(agent) => &agent.turn_ring,
            None => return,
        };
        if ring.is_empty() {
            return;
        }

        // Partition newest-first (`push_back` newest ⇒ iterate reversed).
        let mut errored: Vec<&ReplTurn> = Vec::new();
        let mut green: Vec<&ReplTurn> = Vec::new();
        for t in ring.iter().rev() {
            if t.outcome.is_error() {
                errored.push(t);
            } else {
                green.push(t);
            }
        }

        out.push_str("== recent REPL turns ==\n");

        // The single most-recent errored turn is PINNED (unconditional — like the
        // current-module pin, it is the §5.4 floor and never dropped).
        let mut iter_errored = errored.iter();
        if let Some(first) = iter_errored.next() {
            out.push_str(&render_recent_turn(first));
        }
        // Older errored turns, newest-first, budget-gated.
        for t in iter_errored {
            let rendered = render_recent_turn(t);
            if out.len() + rendered.len() <= char_budget {
                out.push_str(&rendered);
            }
        }
        // Green turns (deixis only), newest-first, budget-gated — first to drop.
        for t in &green {
            let rendered = render_recent_turn(t);
            if out.len() + rendered.len() <= char_budget {
                out.push_str(&rendered);
            }
        }
    }

    /// Is `name` a symbol worth harvesting (defined somewhere live)? Reuses the
    /// same liveness gate the reverse-query commands use — a name the user typed
    /// that resolves to a real def, not a typo.
    fn symbol_is_mentionable(&self, name: &str) -> bool {
        if self.lookup_with_prelude_fallback(name).is_some() {
            return true;
        }
        self.shared.symbol_tables.iter().any(|t| t.get(name).is_some())
    }
}

/// One in-scope symbol rendered at all three §23.2 grains. `full` = name +
/// `:Type` sig + docstring; `sig` = name + `:Type` sig (docstring dropped);
/// `name` = bare name (the never-dropped floor).
struct InScopeEntry {
    name: String,
    sig: String,
    full: String,
}

/// Return a clone of `entry` with its docstring cleared, so re-rendering it
/// through `format_def_entry` yields the signature-only grain (the ladder's
/// middle rung, §23.2). Only the docstring-bearing variants are affected; all
/// other fields are preserved. Keeps `format_def_entry` the single source of
/// truth for the rendering (Principle 7) rather than string-stripping its output.
fn strip_entry_docstring(
    mut entry: cranelisp_types::ModuleEntry<crate::code::Code>,
) -> cranelisp_types::ModuleEntry<crate::code::Code> {
    use cranelisp_types::ModuleEntry::*;
    match &mut entry {
        Def { docstring, .. }
        | SpecialForm { docstring, .. }
        | TypeDef { docstring, .. }
        | IntrinsicType { docstring, .. }
        | TraitDecl { docstring, .. } => {
            *docstring = None;
        }
        _ => {}
    }
    entry
}

/// Render one recent REPL turn (E5, §5.5) as a labelled block: the exact source
/// the user submitted followed by the string they saw (the verbatim diagnostic
/// for an errored turn, the rendered result for a green one). No re-derivation —
/// both strings are the ones the display boundary already produced (Principle 7).
fn render_recent_turn(turn: &crate::agent::types::ReplTurn) -> String {
    use crate::agent::types::ReplTurnOutcome;
    let (label, saw) = match &turn.outcome {
        ReplTurnOutcome::Error(diag) => ("errored", diag.as_str()),
        ReplTurnOutcome::Ok(result) => ("ok", result.as_str()),
    };
    format!("-- recent turn ({label}) --\ninput: {}\n{saw}\n", turn.input)
}

/// Extract candidate symbol/module mentions from a turn's text (§5.3 "names in
/// the message"). Tokenizes on whitespace and keeps word-like tokens (symbols
/// may contain `-`, `/`, `?`, `!`, etc.). Stripping of surrounding punctuation
/// keeps a trailing `?` from a question out of the lookup.
pub fn mentions_from_text(text: &str) -> Vec<String> {
    text.split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | ',' | '"'))
        .map(|tok| tok.trim_matches(|c: char| matches!(c, '?' | '.' | ':' | ';' | '\'')))
        .filter(|tok| !tok.is_empty())
        .map(|tok| tok.to_string())
        .collect()
}

#[cfg(test)]
mod in_scope_tests {
    use super::*;
    use crate::agent::test_support::repl_session;
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, Symbol, Type, UserFnState, Visibility};

    /// Insert an own-module `defn`-shaped `Def` named `name` with an
    /// `(Fn [Int] Int)` scheme and `docstring` into the current module's table.
    fn insert_own_defn(s: &CompilerSession, name: &str, docstring: &str) {
        let module = s.current_module_path();
        let scheme = Scheme {
            type_vars: Vec::new(),
            constraints: std::collections::HashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        };
        let entry = ModuleEntry::def(
            scheme,
            DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
            },
        )
        .visibility(Visibility::Public)
        .docstring(docstring.to_string())
        .build();
        if let Some(mut table) = s.shared.symbol_tables.get_mut(&module) {
            table.insert(Symbol::from(name), entry);
        }
    }

    /// Slice the `== in scope ==` block out of a harvest dump — what the e2e
    /// tests assert against (split on the header, stop before the next `==`
    /// section / end).
    fn in_scope_block(harvest: &str) -> String {
        harvest
            .split("== in scope ==")
            .nth(1)
            .unwrap_or("")
            .to_string()
    }

    // spec: repl/spec.md §17.18.1 — the in-scope block carries, for an own
    // defn, name + FQ `:Type` signature + docstring (the 3 facets), and the
    // signature uses the qualified `primitives/Int` form (Principle-7 reuse of
    // the `/sig`-grain formatter), not a bare `Int`.
    #[test]
    fn in_scope_block_renders_own_defn_at_full_grain() {
        let s = repl_session();
        insert_own_defn(&s, "inc-doc", "adds one to its argument");
        let harvest = s.harvest_context(&[], DEFAULT_TOKEN_BUDGET);
        let block = in_scope_block(&harvest);
        assert!(block.contains("inc-doc"), "name present: {block}");
        assert!(
            block.contains("(Fn [primitives/Int] primitives/Int)"),
            "FQ signature present (not bare `Int`): {block}"
        );
        assert!(
            block.contains("adds one to its argument"),
            "docstring present at full grain for an own defn: {block}"
        );
    }

    // spec: repl/spec.md §17.18.2 — budget degrades GRAIN, not membership: under
    // a tight `char_budget` the in-scope symbol's NAME still appears, but the
    // heaviest detail (docstring) is dropped first (sig→name ladder). Drives the
    // `CRANELISP_AGENT_HARVEST_BUDGET`-equivalent in-process by passing a tiny
    // `token_budget` (the same `char_budget` the env lever forces).
    #[test]
    fn in_scope_block_degrades_grain_keeps_name_under_tight_budget() {
        let s = repl_session();
        insert_own_defn(
            &s,
            "inc-doc",
            "a long descriptive docstring that costs many characters",
        );
        // Roomy: full grain (docstring present).
        let roomy = in_scope_block(&s.harvest_context(&[], DEFAULT_TOKEN_BUDGET));
        assert!(
            roomy.contains("a long descriptive docstring"),
            "docstring present under a roomy budget: {roomy}"
        );
        // Tight: ~1 token (~4 chars) — the name survives (floor), the docstring
        // (and even the sig) are dropped. Membership is never silently truncated.
        let tight = in_scope_block(&s.harvest_context(&[], 1));
        assert!(
            tight.contains("inc-doc"),
            "the symbol NAME survives the tight budget (membership floor): {tight}"
        );
        assert!(
            !tight.contains("a long descriptive docstring"),
            "the docstring DETAIL is dropped under the tight budget (grain degrades \
             sig→name; docstrings go first): {tight}"
        );
    }

    // The grain ladder is monotone: the sig-grain rendering is a prefix-shaped
    // subset of the full-grain rendering (same name + same FQ signature, minus
    // the docstring) — the reuse-not-reimplement guard (Principle 7) that the
    // sig grain is the SAME formatter with the docstring cleared.
    #[test]
    fn sig_grain_is_full_grain_without_docstring() {
        let s = repl_session();
        insert_own_defn(&s, "inc-doc", "a docstring");
        let module = s.current_module_path();
        let table = s.shared.symbol_tables.get(&module).unwrap();
        let entry = table.get("inc-doc").unwrap().clone();
        drop(table);
        let rendered = s.render_in_scope_entry(&entry, "inc-doc", &module);
        assert!(rendered.full.contains("a docstring"), "full carries doc: {}", rendered.full);
        assert!(!rendered.sig.contains("a docstring"), "sig drops doc: {}", rendered.sig);
        assert!(
            rendered.sig.contains("(Fn [primitives/Int] primitives/Int)")
                && rendered.full.contains("(Fn [primitives/Int] primitives/Int)"),
            "both grains carry the FQ signature: sig={} full={}",
            rendered.sig,
            rendered.full
        );
        assert_eq!(rendered.name, "inc-doc");
    }
}

#[cfg(test)]
mod recent_turns_tests {
    //! E5 — the recent-errored-turn harvest feed (design/int/agent.md §5.5). The
    //! ring is fed via `record_repl_turn` (the read-loop seam) and surfaced by
    //! `harvest_context`'s fourth source. These pin the enumerated Wave-A unit
    //! obligations (tests/plan/PLAN.md §C): (1) inclusion of a failed turn's form
    //! + diagnostic; (2) the most-recent errored turn pinned to the floor;
    //! (3) errored-first / newest-first ordering; (4) ring cap = `TURN_RING_CAP`;
    //! (5) `record_repl_turn` no-op when the agent is unconfigured.

    use super::*;
    use crate::agent::test_support::repl_session;
    use crate::agent::types::{ReplTurnOutcome, TURN_RING_CAP};

    /// A session whose agent is enabled-but-dormant (no provider) — enough to
    /// carry the ring; `record_repl_turn` records against it, `harvest_context`
    /// reads it. The dormant path needs no API key (like `/context`).
    fn session_with_agent() -> crate::session_v4::CompilerSession {
        let mut s = repl_session();
        s.agent = Some(crate::agent::provider::build_agent_state(false));
        s
    }

    // spec: repl/spec.md §17.11 / design/int/agent.md §5.5 — after a failed
    // `(defn …)` turn is recorded, the harvest carries BOTH the exact failed form
    // and its verbatim diagnostic (the signal committed state cannot reconstruct).
    // defect: class=enumeration-miss locus=src/agent/harvest.rs::harvest_context found=S108 owner=/dev
    #[test]
    fn harvest_includes_recent_errored_turn_form_and_diagnostic() {
        let mut s = session_with_agent();
        let failed_form = "(defn rotations [g] (rem g mod))";
        let diagnostic = "Error: type error at 34..35: ambiguous type; add an annotation";
        s.record_repl_turn(failed_form, ReplTurnOutcome::Error(diagnostic.to_string()));

        let harvest = s.harvest_context(&[], DEFAULT_TOKEN_BUDGET);
        assert!(
            harvest.contains("recent REPL turns"),
            "the recent-turns block header must be present: {harvest}"
        );
        assert!(
            harvest.contains(failed_form),
            "the failed form's exact source must be harvested: {harvest}"
        );
        assert!(
            harvest.contains(diagnostic),
            "the failed form's verbatim diagnostic must be harvested: {harvest}"
        );
    }

    // spec: design/int/agent.md §5.4/§5.5 — the single most-recent errored turn
    // is PINNED to the floor: under a budget so tight that green turns drop, the
    // errored turn survives (+neg: the green turn's form is absent).
    #[test]
    fn most_recent_errored_turn_pinned_under_tight_budget_drops_green() {
        let mut s = session_with_agent();
        s.record_repl_turn(
            "(defn broken [x] (frobnicate x))",
            ReplTurnOutcome::Error("Error: undefined variable: frobnicate".to_string()),
        );
        // A later GREEN turn — newest, but a green turn is the first to drop.
        s.record_repl_turn("(+ 1 2)", ReplTurnOutcome::Ok(":primitives/Int 3".to_string()));

        // Tight budget: ~1 token (~4 chars). The pinned error survives; the green
        // turn's rendering does not fit and is dropped.
        let tight = s.harvest_context(&[], 1);
        assert!(
            tight.contains("frobnicate"),
            "the pinned most-recent errored turn survives the tight budget: {tight}"
        );
        assert!(
            !tight.contains(":primitives/Int 3"),
            "the green turn's DETAIL is dropped under the tight budget (green drops \
             first): {tight}"
        );
    }

    // spec: design/int/agent.md §5.5(3) — the block is ordered errored-first,
    // newest-first: with two errored turns and a green turn interleaved, the
    // newer error precedes the older error, and both errors precede the green.
    #[test]
    fn recent_turns_ordered_errored_first_newest_first() {
        let mut s = session_with_agent();
        s.record_repl_turn("(older-err)", ReplTurnOutcome::Error("Error: OLDER-ERR".to_string()));
        s.record_repl_turn("(a-green)", ReplTurnOutcome::Ok(":GREEN-RESULT".to_string()));
        s.record_repl_turn("(newer-err)", ReplTurnOutcome::Error("Error: NEWER-ERR".to_string()));

        let harvest = s.harvest_context(&[], DEFAULT_TOKEN_BUDGET);
        let pos_newer = harvest.find("NEWER-ERR").expect("newer error present");
        let pos_older = harvest.find("OLDER-ERR").expect("older error present");
        let pos_green = harvest.find("GREEN-RESULT").expect("green turn present");
        assert!(
            pos_newer < pos_older,
            "newest error must precede the older error: {harvest}"
        );
        assert!(
            pos_older < pos_green,
            "both errored turns must precede the (deixis-only) green turn: {harvest}"
        );
    }

    // spec: design/int/agent.md §5.5(1) — the ring is bounded at `TURN_RING_CAP`:
    // recording more than the cap evicts the oldest, and the most-recent turns
    // are retained.
    #[test]
    fn ring_is_bounded_at_cap_evicting_oldest() {
        let mut s = session_with_agent();
        // Record cap + 2 turns; the two oldest must be evicted.
        for i in 0..(TURN_RING_CAP + 2) {
            s.record_repl_turn(
                &format!("(turn-{i})"),
                ReplTurnOutcome::Ok(format!(":RESULT-{i}")),
            );
        }
        let ring_len = s.agent.as_ref().unwrap().turn_ring.len();
        assert_eq!(ring_len, TURN_RING_CAP, "the ring must be bounded at the cap");

        let harvest = s.harvest_context(&[], DEFAULT_TOKEN_BUDGET);
        // The most-recent turn is retained; the two oldest (turn-0, turn-1) are
        // evicted before they can be harvested.
        assert!(
            harvest.contains(&format!("(turn-{})", TURN_RING_CAP + 1)),
            "the newest turn must be retained: {harvest}"
        );
        assert!(
            !harvest.contains("(turn-0)") && !harvest.contains("(turn-1)"),
            "the oldest turns beyond the cap must be evicted: {harvest}"
        );
    }

    // spec: design/int/agent.md §5.5(4) — `record_repl_turn` is a no-op when the
    // agent is unconfigured (`self.agent == None`): nothing is recorded, no agent
    // is created, and the harvest carries no recent-turns block.
    #[test]
    fn record_repl_turn_is_noop_without_agent() {
        let mut s = repl_session(); // agent == None
        assert!(s.agent.is_none(), "fixture precondition: no agent");
        s.record_repl_turn(
            "(defn x [y] y)",
            ReplTurnOutcome::Error("Error: whatever".to_string()),
        );
        assert!(s.agent.is_none(), "record_repl_turn must not construct an agent");
        let harvest = s.harvest_context(&[], DEFAULT_TOKEN_BUDGET);
        assert!(
            !harvest.contains("recent REPL turns"),
            "no recent-turns block without an agent: {harvest}"
        );
    }
}
