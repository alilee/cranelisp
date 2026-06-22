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

impl CompilerSession {
    /// Assemble the harvested context block for a turn (§5), under `token_budget`.
    ///
    /// `mentions` are the symbol/module names named in the turn (and, in a fuller
    /// design, accumulated across the session); the harvester ranks by mention +
    /// recency and pushes the top-budget slice. The current module's full source
    /// is the PINNED floor — included first, never dropped (§5.4).
    pub(crate) fn harvest_context(&self, mentions: &[String], token_budget: usize) -> String {
        let char_budget = token_budget.saturating_mul(CHARS_PER_TOKEN);
        let mut out = String::new();

        // 1. Current module — full source, PINNED (§5.2 #1, the §5.4 floor).
        //    Always included even if it alone exceeds the budget: the agent must
        //    never be blind to the user's cursor context.
        let cur = self.current_module_path();
        out.push_str(&format!("== Current module: {} ==\n", cur.as_ref()));
        self.push_module_full_source(&cur, &mut out);

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

    /// Push the full source of a module — every defined symbol's stored source —
    /// into `out`. Reads the int `Introspection.source` for REPL-evaled defns;
    /// falls back to the symbol table's recorded `source_text` when present.
    fn push_module_full_source(&self, module: &cranelisp_types::ModuleFullPath, out: &mut String) {
        if let Some(table) = self.shared.symbol_tables.get(module) {
            let names: Vec<String> = table
                .defined_symbols()
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
