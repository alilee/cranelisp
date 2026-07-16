// REPL slash-command handler battery (`handle_*`). Extracted from `repl.rs`
// per `design/int/repl-decomposition.md` §1.3 (S110, FIXME 0606). Pure
// relocation, behaviour-invariant.


use super::*;
use super::format::*;


/// Classification of an imported symbol for category-based display.
pub(crate) enum ImportClass {
    Macro,
    Trait,
    Type,
    Constructor,
    Fn,
}

/// Whether a definition is a test function (the `test-` prefix + a nullary
/// `Def`, per the test convention §16.1) — the `/tests-for` filter
/// (repl/spec.md §17.6.2). Structural (does not require the function to be
/// codegen'd), so it works over freshly-typechecked REPL state.
pub(crate) fn is_test_function(name: &str, entry: &ModuleEntry<Code>) -> bool {
    if !name.starts_with("test-") {
        return false;
    }
    matches!(entry, ModuleEntry::Def { param_names, .. } if param_names.is_empty())
}

impl CompilerSession {
    pub(crate) fn handle_sig(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /sig <name>".to_string();
        }
        if intrinsic_type_from_name(name).is_some() {
            return format!("{name} ; type - builtin type");
        }
        match self.resolve_entry_arg(name) {
            Some((entry, lookup_module, bare)) => {
                // §3.8 (FIXME 0492): `/sig`'s primary line MUST be byte-identical
                // to bare lookup's — fully-qualified type names (§1.4) AND a
                // fully-qualified symbol name (§1.1). EVERY resolved argument —
                // module-qualified, bare-imported, AND bare-LOCAL — routes
                // through the same `resolve_entry_for_display` +
                // `format_def_entry` composition the bare-value display path uses
                // (`format_eval_result_body`'s Def arm), so the two surfaces
                // cannot diverge. The former bare-local arm rendered the short,
                // UNqualified `format_entry_sig` form (`:(Fn [Int] Int) k`) — the
                // §3.8 non-conformance this flips.
                let (resolved_entry, resolved_module) =
                    self.resolve_entry_for_display(&entry, &lookup_module);
                // §3.8: `/sig` is byte-identical to a bare lookup — a pure
                // introspection surface, so a trait's `; impl:` section is
                // structural (`true`, FIXME 0542).
                let sig = self.format_def_entry(&resolved_entry, &bare, &resolved_module, true);
                // S101 (repl/spec.md §18.4): a broken symbol's /sig shows the
                // same primary line plus the provenance comment line.
                match self.broken_status_line(name, &resolved_module) {
                    Some(line) => format!("{sig}\n{line}"),
                    None => sig,
                }
            }
            None => format!("error: unknown symbol '{name}'"),
        }
    }

    /// /doc handler: show docstring of a symbol.
    pub(crate) fn handle_doc(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /doc <name>".to_string();
        }
        // §3.6 (FIXME 0487): accept a module-qualified argument, like the other
        // introspection commands. A bare name still routes through the
        // prelude-fallback lookup (unchanged); the module-preamble fallback
        // below is preserved for the `/doc <module>` form.
        let Some((local, lookup_module, _bare)) = self.resolve_entry_arg(name) else {
            // §17.5.1 / spec §8.16.4 — `/doc <module>` reads a module's preamble
            // (the leading `;;` block) when the name resolves to a module rather
            // than a symbol. The module's `module_preamble` is the durable record
            // a Document-mode `set-preamble` edit writes (S89 Cluster C); this is
            // the human read-back path (the harvester reads the same field).
            let module_path = cranelisp_types::ModuleFullPath::from(name);
            if let Some(table) = self.shared.symbol_tables.get(&module_path)
                && let Some(preamble) = table.module_preamble.as_ref()
            {
                return format!("{name} (module): \"{preamble}\"");
            }
            return format!("error: unknown symbol '{name}'");
        };
        // Follow import/re-export chains to the defining entry — a bare
        // primitive (`add-i64`) is reached through the prelude re-export, so
        // the local entry is an Import, not the Def. The chain-follow starts
        // from `lookup_module` (current module, or prelude when the fallback
        // hop fired) so the prelude→primitives edge is walked.
        let (entry, _resolved_module) = self.resolve_entry_for_display(&local, &lookup_module);
        match &entry {
            ModuleEntry::Def { docstring, .. } => {
                // FIXME 0308: primitive Defs now carry their Appendix A.5
                // description on `PrimitiveDef.docstring` (populated in
                // cranelisp-primitives) — read it through the entry's
                // `docstring` field directly; the parallel `builtin_docs` table
                // is retired.
                match docstring.as_deref() {
                    Some(doc) => format!("{name}: \"{doc}\""),
                    None => format!("{name}: no docstring"),
                }
            }
            ModuleEntry::SpecialForm { docstring, .. }
            | ModuleEntry::TraitDecl { docstring, .. } => match docstring {
                Some(doc) => format!("{name}: \"{doc}\""),
                None => format!("{name}: no docstring"),
            },
            _ => format!("{name}: no docstring"),
        }
    }

    /// /list handler: list symbols in current module.
    pub(crate) fn handle_list(&self, _filter: &str) -> String {
        let table_ref = self.current_symbol_table();
        let mut fns = Vec::new();
        let mut types = Vec::new();
        let mut traits = Vec::new();
        let mut macros = Vec::new();

        for (name, entry) in table_ref.symbols.iter() {
            // §3.3: internal compiler artifacts are not user definitions —
            // `$`-mangled names and the synthetic `__expr` top-level-expression
            // wrapper are excluded (shared predicate so the filter cannot drift
            // from the synthesis site).
            if crate::worker::is_internal_listing_name(name.as_ref()) {
                continue;
            }
            // §3.3: names only, no `: type` suffix — the layout block is shared
            // verbatim with /imports and /exports (which are names-only), so
            // cross-command byte-identity requires /list be names-only too. Type
            // detail is on `/sig`/`/info` or by typing the bare name. Bucketing
            // is the shared `classify_listing_entry` classifier (FIXME 0440);
            // /list's only presentation concern is dropping Constructors (part of
            // their type, not listed separately) and SpecialForms/Imports (shown
            // by /imports).
            match crate::worker::classify_listing_entry(entry) {
                Some(SymbolCategory::Macro) => macros.push(name.to_string()),
                Some(SymbolCategory::Trait) => traits.push(name.to_string()),
                Some(SymbolCategory::Type) => types.push(name.to_string()),
                // §3.3/§17.19.2b: each constructor is listed ONCE under its
                // canonical dotted `Type.Ctor` form (`Color.Red`), grouped with
                // its type under Types. Under the S109 canonical keying the
                // Constructor `Def`'s table key IS `Type.Ctor` (the bare `Red`
                // alias is a separate `Import` entry that `classify_listing_entry`
                // returns `None` for, so it is never double-listed). A single-ctor
                // product keys bare (`Point`) with type-name == ctor-name, so it
                // still appears exactly once.
                Some(SymbolCategory::Constructor) => types.push(name.to_string()),
                Some(SymbolCategory::Fn) => fns.push(name.to_string()),
                // Special forms + imports are shown by /imports.
                _ => {}
            }
        }

        macros.sort();
        traits.sort();
        types.sort();
        fns.sort();

        // Category order per §3.3: Modules, Macros, Traits, Types, Fns.
        // (Modules not yet populated here.) Each block is rendered through the
        // shared §3.3 L0–L4 layout formatter via `append_name_category`.
        let mut output = String::new();
        append_name_category(&mut output, "Macros", &macros);
        append_name_category(&mut output, "Traits", &traits);
        append_name_category(&mut output, "Types", &types);
        append_name_category(&mut output, "Fns", &fns);
        while output.ends_with('\n') {
            output.pop();
        }
        if output.is_empty() {
            "(no definitions)".to_string()
        } else {
            output
        }
    }

    /// `/context <path>` handler (repl/spec.md §17) — a debug tool.
    ///
    /// Dumps the FULL assembled agent request — exactly what `agent_turn` would
    /// send to the model on this turn — to `<path>` as readable labeled text.
    /// Reuses the existing `assemble_request` (Principle 7 — no re-implemented
    /// harvesting/primer), so the dump reflects the same primer + harvested
    /// session context + transcript the model would receive. `assemble_request`
    /// is PURE — it needs no API key and no reachable provider — so `/context`
    /// succeeds even when the agent is dormant (that is the point: inspect the
    /// grounding/harvest without a key). The `<path>` argument is the user-typed
    /// turn text fed to `assemble_request` so the harvest reflects what would be
    /// pushed for "ask about <path>"; the rendered request is then written there.
    ///
    /// A bad/unwritable path returns a graceful error line — never a panic
    /// (`src/CLAUDE.md` §Error Handling: no `unwrap`/`expect` in pipeline code).
    #[cfg(feature = "agent")]
    pub(crate) fn handle_context(&self, path: &str) -> String {
        let path = path.trim();
        if path.is_empty() {
            return "Usage: /context <path>".to_string();
        }
        // Assemble the SAME request a turn would send via the existing
        // `assemble_request` (Principle 7 — no re-implemented harvest/primer).
        // Pure — no provider/key needed — so this works regardless of dormancy
        // (the point of the command: inspect the grounding without an API call).
        //
        // There is no pending question, so the inspection drives the harvest off
        // the conversation so far: the concatenated prior user turns stand in for
        // the "current turn text", so the dump shows what the NEXT turn building
        // on this conversation would pull (the names the user has been asking
        // about). With no transcript yet, the text is empty and the harvest is
        // the pinned current-module floor alone.
        let driver = self.agent_context_driver_text();
        let req = self.assemble_request(&driver);
        let rendered = req.render_for_debug();
        match std::fs::write(path, &rendered) {
            Ok(()) => format!("wrote agent context to {path} ({} chars)", rendered.len()),
            Err(e) => format!("error: could not write agent context to {path}: {e}"),
        }
    }

    /// The mention-driver text for a `/context` dump: the concatenation of the
    /// prior user turns this session (so the harvest reflects what the user has
    /// been asking about). Empty when no transcript exists.
    #[cfg(feature = "agent")]
    fn agent_context_driver_text(&self) -> String {
        self.agent
            .as_ref()
            .map(|state| {
                state
                    .transcript
                    .iter()
                    .filter_map(|t| match t {
                        crate::agent::types::Turn::User(u) => Some(u.as_str()),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            })
            .unwrap_or_default()
    }

    /// `/refs <sym>` handler (repl/spec.md §17.6.1, design/int/agent.md §9).
    ///
    /// Lists the definitions in scope whose body references `<sym>` — the
    /// reverse of the forward name→source/sig/doc introspection. LLM-free,
    /// default build. An on-demand scan over the in-memory module bodies (no
    /// maintained reverse index, no invalidation in a mutating session — §9.2).
    /// Output uses the §3.3 L0–L4 layout (names only), byte-identical to `/list`
    /// for the same name set.
    pub(crate) fn handle_refs(&self, sym: &str) -> String {
        if sym.is_empty() {
            return "Usage: /refs <symbol-name>".to_string();
        }
        // §17.6.1 / FIXME 0487: accept a module-qualified argument (the cascade
        // report's own FQ names) — resolve to (home, bare); the token scan +
        // reverse-index target both key off the bare name.
        let (home, bare) = self.resolve_symbol_arg(sym);
        // §17.6.1: a genuinely-unbound name is distinguished from a bound-but-
        // unreferenced one — report `unbound symbol '<sym>'` (consistent with
        // §4.1.10) rather than silently reporting no references.
        if !self.symbol_is_bound(&bare) {
            return format!("unbound symbol '{sym}'");
        }
        let referers = self.collect_referers(&home, &bare, false);
        if referers.is_empty() {
            return format!("; no references to {sym}");
        }
        let mut out = format!("; references to {sym}\n");
        out.push_str(&format_symbol_layout(&referers).join("\n"));
        out
    }

    /// The `/refs` referer set (§17.6.1 / FIXME 0487): the union of the
    /// `redefine::ReverseIndex` callable-referent feed (`callers_of` over the
    /// serialized, 0470-widened `callees` — **present for cache-restored modules
    /// by construction**, so cross-project call sites do not silently vanish
    /// when introspection is absent) and the retained token-scan
    /// (`scan_referers`, which also catches non-callable referents — type names
    /// in annotations — that carry no `callees` edge). Union + dedup.
    ///
    /// NOTE (FIXME 0507 Issue 2 / F3): `ReverseIndex::build` excludes
    /// `__macro_*` clause defns as callers (the 0491 gate-exempt rule), so a
    /// persistent macro-clause reference to `target` is NOT surfaced by the
    /// callable feed. The token-scan leg only covers referents whose
    /// introspection body was recorded — macro clauses generally are not — so
    /// macro-clause references remain a `/refs` gap. Left for the 0507 drain
    /// (the design's textual-scan-must-cover-macro-clauses leg), not patched by
    /// weakening the 0491 exclusion here.
    fn collect_referers(
        &self,
        home: &ModuleFullPath,
        bare: &str,
        tests_only: bool,
    ) -> Vec<String> {
        let mut referers: Vec<String> = Vec::new();
        // Callable referents via the reverse index (skip for `/tests-for`,
        // which filters to the token-scanned test-fn shape).
        if !tests_only {
            let target = FQSymbol {
                module: home.clone(),
                symbol: Symbol::from(bare),
            };
            let index = crate::redefine::ReverseIndex::build(&self.shared.symbol_tables);
            for caller in index.callers_of_with_variants(&target) {
                // Report at BASE-defn grain: `ReverseIndex::build` records
                // `$`-mangled mono instances (e.g. `g$Int`) as callers. Surfacing
                // them verbatim leaks the internal mangled name and — when the
                // base body also token-references `target` — double-lists the same
                // logical caller (`m/g` vs `m/g$Int`) across the two legs. Strip to
                // base (mirroring `redefine::stale_callers`) so the sort+dedup below
                // merges both legs into one entry per logical caller. Unlike
                // `stale_callers`, `/refs` wants ALL referers (compiled or not), so
                // the `code: Some` compiled-filter is intentionally NOT applied here.
                let base = crate::redefine::base_fq(&caller);
                referers.push(format!("{}/{}", base.module.as_ref(), base.symbol.as_ref()));
            }
        }
        // Token scan for non-callable referents + introspection-recorded bodies.
        referers.extend(self.scan_referers(bare, tests_only));
        referers.sort();
        referers.dedup();
        referers
    }

    /// `/tests-for <sym>` handler (repl/spec.md §17.6.2, design/int/agent.md §9).
    ///
    /// A specialization of `/refs` filtered to test functions (the `test-`
    /// prefix + nullary test signature, §16.1). LLM-free, default build.
    pub(crate) fn handle_tests_for(&self, sym: &str) -> String {
        if sym.is_empty() {
            return "Usage: /tests-for <symbol-name>".to_string();
        }
        let (home, bare) = self.resolve_symbol_arg(sym);
        if !self.symbol_is_bound(&bare) {
            return format!("unbound symbol '{sym}'");
        }
        let referers = self.collect_referers(&home, &bare, true);
        if referers.is_empty() {
            return format!("; no tests reference {sym}");
        }
        let mut out = format!("; tests referencing {sym}\n");
        out.push_str(&format_symbol_layout(&referers).join("\n"));
        out
    }

    /// /mod handler: switch module namespace.
    pub(crate) fn handle_mod(&mut self, name: &str) {
        // S78 §1.4: `/mod` with no argument returns to the "home" module — the
        // ENTRY module — NOT a hardcoded "user". `"user"` is only the entry
        // module's default name when no CLI target is given.
        let path = if name.is_empty() {
            self.entry_module.clone()
        } else {
            ModuleFullPath::from(name)
        };
        self.set_current_module(path.clone());
        // S102 CS-D3a (§6.2.3): establish the target module's session-env
        // companions. `set_current_module` creates a blank table via
        // `ensure_module_exists` for a not-yet-loaded module — a blank module
        // cannot reference prelude, so its fallback bit is ON (its next defining
        // turn must compile with the implicit prelude, exactly as its file body
        // would). Idempotent for an already-loaded/cache-restored target
        // (recomputes the same bit + aliases from its own structural fields).
        crate::imports::install_module_session_env(
            &self.shared.symbol_tables,
            &path,
            &self.shared.module_aliases,
            &self.shared.prelude_fallback,
        );
    }

    /// /source handler: show original source text of a definition.
    pub(crate) fn handle_source(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /source <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name) {
            if let Some(ref src) = intr.source {
                return render(&code_block_doc(
                    &format!("; source for {name}"),
                    crate::pretty::pretty_print_str_doc(src),
                ));
            }
            if let Some(ref sexp) = intr.sexp {
                return render(&code_block_doc(
                    &format!("; source for {name}"),
                    crate::pretty::pretty_print_doc(sexp),
                ));
            }
        }
        crate::style::error_line(&format!("no source available for '{name}'"))
    }

    /// /sexp handler: show parsed S-expression of a definition.
    pub(crate) fn handle_sexp_cmd(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /sexp <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref sexp) = intr.sexp {
                return render(&code_block_doc(
                    &format!("; sexp for {name}"),
                    crate::pretty::pretty_print_doc(sexp),
                ));
            }
        crate::style::error_line(&format!("no sexp available for '{name}'"))
    }

    /// /ast handler: show AST of a definition.
    pub(crate) fn handle_ast(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /ast <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref defn) = intr.ast {
                return format!("; ast for {name}\n{:#?}", defn);
            }
        crate::style::error_line(&format!("no AST available for '{name}'"))
    }

    /// /clif handler: show Cranelift IR of a definition.
    pub(crate) fn handle_clif(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /clif <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref clif) = intr.clif_ir {
                return format!("; clif ir for {name}\n{}", clif);
            }
        crate::style::error_line(&format!("no CLIF IR available for '{name}'"))
    }

    /// /disasm handler: show disassembled native code of a definition.
    ///
    /// Per Decision 41 (`design/int/int.md` §8.2.1) disasm is NOT a stored
    /// field — it is re-derived on the keystroke. The handler resolves the
    /// symbol in the current module (same resolution as `/clif`'s
    /// `get_introspection`), reads the eagerly-captured `code_size` (the bridge
    /// `produce_disasm` needs), and forwards both to the already-public
    /// `cranelisp_backend::produce_disasm`, which resolves the GOT slot and
    /// reads the live code bytes. A symbol with no `code_size` (never compiled,
    /// or batch mode with no introspection map) or a backend `Err` (slot empty
    /// / not compilable) yields the graceful "no disassembly available" line.
    pub(crate) fn handle_disasm(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /disasm <name>".to_string();
        }
        let fq = FQSymbol {
            module: self.current_module_path(),
            symbol: Symbol::from(name),
        };
        let Some(code_size) = self
            .get_introspection(name)
            .and_then(|intr| intr.code_size)
        else {
            return crate::style::error_line(&format!("no disassembly available for '{name}'"));
        };
        match cranelisp_backend::produce_disasm(&fq, code_size, &self.shared.symbol_tables) {
            Ok(text) => format!("; disasm for {name}\n{text}"),
            Err(_) => crate::style::error_line(&format!("no disassembly available for '{name}'")),
        }
    }

    /// /info handler: show full details (sig + definition source + code size).
    pub(crate) fn handle_info(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /info <name>".to_string();
        }
        if intrinsic_type_from_name(name).is_some() {
            return self.format_builtin_type_display(name);
        }
        // §3.6 (FIXME 0487): accept a module-qualified argument — the FQ names
        // the cascade reports print MUST be pasteable into `/info`. `bare` is
        // the name without the qualifier so `format_def_entry` renders one
        // clean `module/name`, not `module/mod/name`.
        let (entry, lookup_module, bare) = match self.resolve_entry_arg(name) {
            Some(triple) => triple,
            None => return format!("error: unknown symbol '{name}'"),
        };
        let (resolved_entry, resolved_module) =
            self.resolve_entry_for_display(&entry, &lookup_module);
        // §3.6: `/info` is a pure-introspection surface — a trait's `; impl:`
        // section is structural (`true`, FIXME 0542).
        let sig = self.format_def_entry(&resolved_entry, &bare, &resolved_module, true);
        // §3.6 third MUST component (FIXME 0480): the definition source,
        // rendered for BOTH the broken and healthy arms.
        let source = self.info_definition_source(&bare, &resolved_module);
        // S101 (repl/spec.md §18.4): a broken symbol's /info shows the primary
        // line (last-good signature) + the provenance comment line + the
        // definition source, and MUST NOT display code-size stats — its
        // compiled code is gone, and the trap stub is an implementation
        // detail, not the symbol's code.
        if let Some(line) = self.broken_status_line(&bare, &resolved_module) {
            return match source {
                Some(src) => format!("{sig}\n{line}\n{src}"),
                None => format!("{sig}\n{line}"),
            };
        }
        let mut out = sig;
        if let Some(src) = source {
            out.push('\n');
            out.push_str(&src);
        }
        // Append code info if available.
        let is_macro = matches!(&resolved_entry,
            ModuleEntry::Def { kind, .. } if matches!(kind.as_ref(), DefKind::Macro { .. }));
        if !is_macro
            && !matches!(resolved_entry, ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. })
            && let Some(intr) = self.get_introspection(name) {
                let size_str = intr.code_size
                    .map(|s| format!("{s} bytes"))
                    .unwrap_or_else(|| "? bytes".to_string());
                out.push_str(&format!("\n  {size_str}"));
            }
        out
    }

    /// The definition-source component of `/info` (`repl/spec.md` §3.6 MUST,
    /// second display line; the §18.4 broken arm inherits it — FIXME 0480):
    /// the pretty-printed defining form as a 2-space-indented block, or
    /// `None` when no source is recoverable (batch mode, special forms,
    /// primitives with no recorded definition). Reads the introspection store
    /// first (populated at every REPL definition); on a miss, attempts the
    /// FIXME-0220 lazy rehydration from the module's backing `.cl` — the same
    /// resolution `redefine::resolve_recheck_sexps` uses for cache-restored
    /// modules — then re-reads.
    fn info_definition_source(&self, name: &str, module: &ModuleFullPath) -> Option<String> {
        // Accept both bare and module-qualified spellings (mirrors
        // `broken_status_line`).
        let (module, bare) = match name.rsplit_once('/') {
            Some((m, n)) => (ModuleFullPath::from(m), n),
            None => (module.clone(), name),
        };
        let fq = FQSymbol {
            module: module.clone(),
            symbol: Symbol::from(bare),
        };
        let intr_map = self.shared.introspection.as_ref()?;
        let render = |rec: &Introspection| -> Option<String> {
            // Original source text preferred; the parsed sexp is the fallback
            // (the same precedence as `handle_source`).
            if let Some(src) = rec.source.as_deref() {
                return Some(crate::pretty::pretty_print_str(src));
            }
            rec.sexp.as_ref().map(crate::pretty::pretty_print)
        };
        if let Some(rec) = intr_map.get(&fq)
            && let Some(text) = render(&rec)
        {
            return Some(indent_source_block(&text));
        }
        // Cache-restored modules never populate introspection; rehydrate from
        // the backing `.cl` (the cache key — normally present) and re-read.
        let backing_source = self
            .shared
            .typecheck_products
            .get(&module)
            .and_then(|tp| tp.file_path.clone())
            .and_then(|p| std::fs::read_to_string(p).ok())?;
        let table = {
            let st = self.shared.symbol_tables.get(&module)?;
            st.clone()
        };
        crate::save::rehydrate_userfn_introspection_from_source(
            &table,
            intr_map,
            &module,
            &backing_source,
        );
        let rec = intr_map.get(&fq)?;
        render(&rec).map(|text| indent_source_block(&text))
    }

    /// /type handler: typecheck expression without executing.
    pub(crate) fn handle_type(&mut self, expr_src: &str) -> String {
        if expr_src.is_empty() {
            return "usage: /type <expr>".to_string();
        }
        let result = self.typecheck_only(expr_src);
        match result {
            Ok(ty) => {
                let display = format_type_qualified(&ty);
                format!(":{display}")
            }
            Err(e) => crate::style::error_line(&e.to_string()),
        }
    }

    /// Parse, expand, and typecheck an expression without compiling or executing.
    ///
    /// Per Decision 44 (2026-05-13 third amendment) — routes through the
    /// collapsed `check_forms` surface via `worker::check_program_compat`.
    /// The pre-S66 `tc.check(...)` entry point (which fed a multi-pass
    /// pipeline driven by a public `ModuleCheckAccumulator`) is retired;
    /// the type query now lifts inferred-type data off the live `SymbolTable`
    /// after the cluster commit.
    pub(crate) fn typecheck_only(&mut self, expr_src: &str) -> Result<Type, CranelispError> {
        let sexps = cranelisp_frontend::parse(expr_src)?;
        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty expression".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        let module = self.current_module_path();

        // Build the input through the new `build_form` / `build_expr` boundary
        // (replacing the retired `build_repl_input`). A bare-expr REPL input
        // is wrapped as a synthetic `__expr` defn for typecheck dispatch.
        // Build is mode-agnostic; `(trace ...)` in `--link` standalone-binary
        // mode (not reachable via REPL) fails at link time via the
        // architecture's natural missing-symbol detection.
        let working_program =
            crate::worker::build_program_compat(&[sexps[0].clone()])?;
        let working_program = self.wrap_exprs_as_synthetic_defns(&working_program);

        // Ensure the current module exists before the live ClusterContext
        // tries to take a guard on it.
        cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &module);

        crate::worker::check_program_compat_no_gap(
            &self.shared.symbol_tables,
            &self.shared.module_aliases,
            &self.shared.prelude_fallback,
            &module,
            &working_program,
        )?;

        // Try to surface the inferred type of the synthetic `__expr` Defn
        // by reading back from the live `SymbolTable`. Fall back to `Int`
        // when no display info is available (matches pre-S66 fallback).
        Ok(self.lift_expr_type(&module).unwrap_or(Type::Int))
    }

    /// Local equivalent of the retired `wrap_exprs_as_defns` helper. Folds
    /// any `TopLevel::Expr` into a synthetic zero-arg `__expr` defn so it
    /// flows uniformly through the typecheck dispatch.
    pub(crate) fn wrap_exprs_as_synthetic_defns(&self, program: &[TopLevel]) -> Vec<TopLevel> {
        use cranelisp_types::{DefnVariant, Visibility};
        let mut working = Vec::with_capacity(program.len());
        for top in program {
            match top {
                TopLevel::Expr(expr) => {
                    let span = expr.span();
                    let wrapper_span = Span::new(
                        span.start.saturating_sub(1),
                        span.end.saturating_add(1),
                    );
                    working.push(TopLevel::Defn(cranelisp_types::Defn {
                        name: Symbol::from("__expr"),
                        docstring: None,
                        variants: vec![DefnVariant {
                            params: vec![],
                            body: expr.clone(),
                            span,
                        }],
                        visibility: Visibility::Public,
                        span: wrapper_span,
                    }));
                }
                other => working.push(other.clone()),
            }
        }
        working
    }

    /// Read back the inferred type of the synthetic `__expr` defn, if any.
    pub(crate) fn lift_expr_type(&self, module: &ModuleFullPath) -> Option<Type> {
        let table = self.shared.symbol_tables.get(module)?;
        match table.get("__expr")? {
            ModuleEntry::Def { scheme, .. } => {
                // Zero-arg defns have type `Fn([], ret)` — surface the return.
                if let Type::Fn(_, ret) = &scheme.ty {
                    Some((**ret).clone())
                } else {
                    Some(scheme.ty.clone())
                }
            }
            _ => None,
        }
    }

    /// S78 §2.6 — prelude's own public symbol names, for the `/imports`
    /// "Prelude (implicit)" group. Returns the sorted public names prelude
    /// makes available (its own `Def`s plus its `(export …)` re-exports such
    /// as `add-i64`) — but ONLY when the CURRENT module's prelude-fallback bit
    /// is ON. When the bit is OFF (the module refused/references prelude), or
    /// the current module IS prelude, or prelude is not loaded, returns empty
    /// so the group is absent (no implicit fallback is active).
    pub(crate) fn prelude_implicit_names(&self) -> Vec<String> {
        let current = self.current_module_path();
        let prelude_path = ModuleFullPath::from("prelude");
        if current == prelude_path {
            return Vec::new();
        }
        let on = self
            .shared
            .prelude_fallback
            .get(&current)
            .map(|b| *b)
            .unwrap_or(false);
        if !on {
            return Vec::new();
        }
        let Some(table) = self.shared.symbol_tables.get(&prelude_path) else {
            return Vec::new();
        };
        let mut names: Vec<String> = Vec::new();
        for (sym, entry) in table.all_symbols() {
            // Public symbols only — both prelude's own defs and its re-export
            // `(export …)` Import edges (e.g. `add-i64`) are user-visible.
            if !entry.is_public() {
                continue;
            }
            let name = sym.to_string();
            // Skip mangled multi-sig / overload variants and special forms
            // (special forms are surfaced from root in their own category).
            if name.contains('$') || matches!(entry, ModuleEntry::SpecialForm { .. }) {
                continue;
            }
            names.push(name);
        }
        names.sort();
        names.dedup();
        names
    }

    /// /imports handler: list imports in current module by category.
    pub(crate) fn handle_imports(&self, filter: &str) -> String {
        let table = self.current_symbol_table();
        let mut output = String::new();

        if filter.is_empty() {
            // Unfiltered mode: organize by category
            let mut special_forms: Vec<String> = Vec::new();
            let mut macros: Vec<String> = Vec::new();
            let mut traits: Vec<String> = Vec::new();
            let mut types: Vec<String> = Vec::new();
            let mut fns: Vec<String> = Vec::new();

            // Special forms always come from the root `""` module per
            // Principle 17 amendment (FIXME 0193). Sprint 67 hack-back
            // FIXME 0192 Residual Task 3 — `/imports` previously enumerated
            // special forms by iterating the current module; once special-form
            // registration shifted to root, that iteration stopped seeing
            // them. Probe the root explicitly.
            let root = ModuleFullPath::from("");
            if let Some(root_table) = self.shared.symbol_tables.get(&root) {
                for (sym, entry) in root_table.all_symbols() {
                    if matches!(entry, ModuleEntry::SpecialForm { .. }) {
                        special_forms.push(sym.to_string());
                    }
                }
            }

            for (sym, entry) in table.all_symbols() {
                let name = sym.to_string();
                match entry {
                    // Special forms live at root only (handled above); skip
                    // any locally-defined fns / primitives.
                    ModuleEntry::Import { source, .. } => {
                        if name.contains('$') {
                            continue;
                        }
                        let classification = self.classify_import(source);
                        match classification {
                            ImportClass::Macro => macros.push(name),
                            ImportClass::Trait => traits.push(name),
                            ImportClass::Type | ImportClass::Constructor => types.push(name),
                            ImportClass::Fn => fns.push(name),
                        }
                    }
                    _ => {} // locally defined / special form
                }
            }

            special_forms.sort();
            macros.sort();
            traits.sort();
            types.sort();
            fns.sort();

            append_name_category(&mut output, "Special forms", &special_forms);
            append_name_category(&mut output, "Macros", &macros);
            append_name_category(&mut output, "Traits", &traits);
            append_name_category(&mut output, "Types", &types);
            append_name_category(&mut output, "Fns", &fns);

            // S78 §2.6 — prelude is an OUTER SCOPE, not flattened into this
            // module's table, so prelude-provided names no longer appear in the
            // explicit categories above. When the per-module fallback bit is ON
            // (the module did not refuse/reference prelude), append a distinct
            // "Prelude (implicit)" group enumerating prelude's OWN public
            // symbols — preserving discoverability while making the inner/outer
            // scope layering visible. Absent when the bit is OFF (refusal).
            let prelude_names = self.prelude_implicit_names();
            if !prelude_names.is_empty() {
                // FIXME 0546: route the prelude group's names through the SAME
                // shared §3.3 L0–L4 layout as every other category (was a
                // one-name-per-line loop that bypassed `format_symbol_layout`).
                // The header suffix comment is preserved by the helper.
                output.push_str(&format_prelude_implicit_group(&prelude_names));
            }

            if special_forms.is_empty() && macros.is_empty() && traits.is_empty()
                && types.is_empty() && fns.is_empty() && prelude_names.is_empty()
            {
                output.push_str("(no imports)");
            }
        } else {
            // Filtered mode: show imports from named module only
            let mut names: Vec<String> = Vec::new();
            for (sym, entry) in table.all_symbols() {
                let source = match entry {
                    ModuleEntry::Import { source, .. } => source,
                    _ => continue,
                };
                let name = sym.to_string();
                if name.contains('$') {
                    continue;
                }
                if *source.module == *filter {
                    names.push(name);
                }
            }
            if names.is_empty() {
                // Silent for no matches
                return String::new();
            }
            names.sort();
            append_name_category(&mut output, &format!("From {filter}"), &names);
        }

        // Trim trailing newline
        while output.ends_with('\n') {
            output.pop();
        }
        output
    }

    /// Classify an imported symbol by following import chains to the definition.
    pub(crate) fn classify_import(&self, source: &FQSymbol) -> ImportClass {
        match self.resolve_to_definition(source) {
            Some(entry) => match entry {
                ModuleEntry::Def { kind, .. } if matches!(kind.as_ref(), DefKind::Macro { .. }) => {
                    ImportClass::Macro
                }
                ModuleEntry::Def { kind, .. }
                    if matches!(kind.as_ref(), DefKind::Constructor { .. }) =>
                {
                    ImportClass::Constructor
                }
                ModuleEntry::TraitDecl { .. } => ImportClass::Trait,
                ModuleEntry::TypeDef { .. } => ImportClass::Type,
                _ => ImportClass::Fn,
            },
            None => ImportClass::Fn,
        }
    }

    /// Follow Import/Reexport chains to find the ultimate definition entry.
    pub(crate) fn resolve_to_definition(&self, source: &FQSymbol) -> Option<ModuleEntry<Code>> {
        let mut current_module = source.module.clone();
        let mut current_name = source.symbol.to_string();
        for _ in 0..10 {
            let entry = {
                let table = self.module_table(&current_module)?;
                table.get(&current_name)?.clone()
            };
            match &entry {
                ModuleEntry::Import { source: next, .. } => {
                    current_module = next.module.clone();
                    current_name = next.symbol.to_string();
                }
                _ => return Some(entry),
            }
        }
        None
    }

    /// /exports handler: list a module's public symbols.
    pub(crate) fn handle_exports(&self, arg: &str) -> String {
        if arg.is_empty() {
            return "Usage: /exports <module-name>".to_string();
        }
        let mut parts = arg.splitn(2, char::is_whitespace);
        let mod_name = parts.next().unwrap_or("");
        let prefix_filter = parts.next().unwrap_or("").trim();

        let module_path = match self.resolve_module_by_name(mod_name) {
            Some(path) => path,
            None => return format!("Module '{mod_name}' not found"),
        };

        let table = match self.module_table(&module_path) {
            Some(t) => t,
            None => return format!("Module '{mod_name}' not found"),
        };

        let mut macros: Vec<String> = Vec::new();
        let mut traits: Vec<String> = Vec::new();
        let mut types: Vec<String> = Vec::new();
        let mut fns: Vec<String> = Vec::new();

        for (sym, entry) in table.all_symbols() {
            if matches!(entry, ModuleEntry::Import { .. }) {
                continue;
            }
            if !entry.is_public() {
                continue;
            }
            let name = sym.to_string();
            // §3.3: exclude `$`-mangled internal names and the synthetic
            // `__expr` top-level-expression wrapper (the wrapper is
            // `Visibility::Public`, so the `is_public()` gate above does not
            // catch it) — shared predicate, single source with the synthesis.
            if crate::worker::is_internal_listing_name(&name) {
                continue;
            }
            if !prefix_filter.is_empty()
                && !name.to_lowercase().starts_with(&prefix_filter.to_lowercase())
            {
                continue;
            }
            // Bucketing is the shared `classify_listing_entry` classifier (FIXME
            // 0440); /exports's only presentation concern is folding the
            // Constructor category into Types (a public ctor is listed under its
            // type) and dropping special forms.
            match crate::worker::classify_listing_entry(entry) {
                Some(SymbolCategory::Macro) => macros.push(name),
                Some(SymbolCategory::Trait) => traits.push(name),
                Some(SymbolCategory::Type) | Some(SymbolCategory::Constructor) => types.push(name),
                Some(SymbolCategory::Fn) => fns.push(name),
                _ => {}
            }
        }

        macros.sort();
        traits.sort();
        types.sort();
        fns.sort();

        let has_any = !macros.is_empty() || !traits.is_empty()
            || !types.is_empty() || !fns.is_empty();

        if !has_any {
            return format!("Module '{mod_name}' has no public symbols");
        }

        let mut output = format!("Module '{mod_name}':\n");
        append_name_category(&mut output, "Macros", &macros);
        append_name_category(&mut output, "Traits", &traits);
        append_name_category(&mut output, "Types", &types);
        append_name_category(&mut output, "Fns", &fns);
        while output.ends_with('\n') {
            output.pop();
        }
        output
    }

    /// /expand handler: macro-expand a form without evaluating.
    pub(crate) fn handle_expand(&mut self, form_src: &str) -> String {
        if form_src.is_empty() {
            return "usage: /expand <form>".to_string();
        }
        // Compile any uncompiled macros before expansion.
        if let Err(e) = self.compile_pending_macros() {
            return crate::style::error_line(&e.to_string());
        }
        match self.expand_form_sexp(form_src) {
            Ok(expanded) => format_sexp(&expanded),
            Err(e) => crate::style::error_line(&e.to_string()),
        }
    }

    /// Compile any macros in the TC symbol table that don't yet have code pointers.
    ///
    /// When a defmacro form is processed by the worker, it registers the macro
    /// in the TC but defers compilation until the macro is first used. For /expand
    /// we need to compile them eagerly.
    pub(crate) fn compile_pending_macros(&mut self) -> Result<(), CranelispError> {
        use crate::worker::ModuleCheckAccumulator;

        // Collect macro names + sexps that need compilation. S70/W-Absorb:
        // macros are `Def { kind: DefKind::Macro { clauses_meta } }`; the
        // defining `sexp` lives on the int-layer `Introspection` record
        // (Decision 41), keyed by `FQSymbol`, not on the symbol-table entry.
        let module = self.current_module_path();
        let mut to_compile: Vec<(Symbol, Sexp)> = Vec::new();
        {
            let table = self.current_symbol_table();
            for (sym, entry) in table.all_symbols() {
                let ModuleEntry::Def { kind, .. } = entry else {
                    continue;
                };
                let DefKind::Macro { clauses_meta, .. } = kind.as_ref() else {
                    continue;
                };
                let name = Symbol::from(sym.as_ref());
                let fq = FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                };
                let Some(sexp) = self
                    .shared
                    .introspection
                    .as_ref()
                    .and_then(|m| m.get(&fq))
                    .and_then(|i| i.sexp.clone())
                else {
                    continue;
                };
                let needs_compile = clauses_meta.iter().enumerate().any(|(idx, _)| {
                    let clause_name =
                        Symbol::from(format!("__macro_{}_clause_{}", name, idx));
                    let compiled = self
                        .shared
                        .symbol_tables
                        .get(&module)
                        .and_then(|t| match t.get(clause_name.as_ref())? {
                            ModuleEntry::Def { code, .. } => Some(code.is_some()),
                            _ => None,
                        })
                        .unwrap_or(false);
                    !compiled
                });
                if needs_compile {
                    to_compile.push((name, sexp));
                }
            }
        }

        for (_, sexp) in &to_compile {
            let module = self.current_module_path();
            let info = cranelisp_frontend::parse_defmacro(sexp)?;
            let mut accumulator = ModuleCheckAccumulator::new();

            cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &module);
            let repl_cs = self.repl_check_state.lock()
                .unwrap_or_else(|e| e.into_inner())
                .take()
                .unwrap_or_else(|| CheckState::new(module.clone()));
            let lib_dirs_snap = self.lib_dirs();
            let platform_dirs_snap = self.platform_dirs();
            let mut wctx = ModuleCompiler {
                symbol_tables: &self.shared.symbol_tables,
                next_type_id: &self.shared.next_type_id,
                module_aliases: &self.shared.module_aliases,
                prelude_fallback: &self.shared.prelude_fallback,
                check_state: repl_cs,
                current_module: module.clone(),
                scheduler: &self.shared.scheduler,
                typecheck_products: &self.shared.typecheck_products,
                // D1/D1b: introspection is REPL-only. The store is `Some` only
                // under `RunMode::Repl`, so `.as_ref()` is the single adaptor.
                introspection: self.shared.introspection.as_ref(),
                lib_dirs: &lib_dirs_snap,
                platform_dirs: &platform_dirs_snap,
                project_root: &self.shared.project_root,
                shared_state: Some(&self.shared),
                // S93 Invariant SW: REPL eval thread driving the entry module.
                eval_driven: true,
            };

            crate::process_form::compile_macro_for_repl(
                &mut wctx, &module, &info, Span::SYNTHETIC, &mut accumulator,
            )?;
            // Restore REPL check_state.
            *self.repl_check_state.lock()
                .unwrap_or_else(|e| e.into_inner()) = Some(wctx.check_state);
        }
        Ok(())
    }

    /// Parse and expand a form through the compiled macros in the session.
    pub(crate) fn expand_form_sexp(&self, form_src: &str) -> Result<Sexp, CranelispError> {
        let sexps = cranelisp_frontend::parse(form_src)?;
        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty form".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        let sexp = sexps.into_iter().next().ok_or_else(|| {
            CranelispError::ParseError {
                message: "empty form".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        let module = self.current_module_path();
        let mut resolver = ReadOnlyMacroResolver {
            symbol_tables: &self.shared.symbol_tables,
            module_aliases: &self.shared.module_aliases,
            prelude_fallback: &self.shared.prelude_fallback,
            current_module: module,
        };
        crate::expander::expand_sexp_recursive(sexp, &mut resolver, 0, None)
    }

    /// /time handler: evaluate with timing.
    pub(crate) fn handle_time(&mut self, expr_src: &str) -> String {
        if expr_src.is_empty() {
            return "usage: /time <expr>".to_string();
        }
        let start = std::time::Instant::now();
        match self.eval(expr_src) {
            Ok(Some(result)) => {
                let elapsed = start.elapsed();
                let display = self.format_eval_result(&result);
                format!("{display} ({}ms)", elapsed.as_millis())
            }
            Ok(None) => {
                let elapsed = start.elapsed();
                format!("(no result) ({}ms)", elapsed.as_millis())
            }
            Err(e) => crate::style::error_line(&e.to_string()),
        }
    }

    /// /mem handler: show allocation statistics.
    ///
    /// With no argument: report current live bytes, total allocations, total
    /// deallocations, and the delta (currently-live allocations) reflected by
    /// the runtime counters.
    ///
    /// With an argument: evaluate the expression and report the delta in each
    /// counter across the evaluation. This makes RC behaviour directly
    /// observable during a session.
    pub(crate) fn handle_mem(&mut self, expr_src: &str) -> String {
        if expr_src.is_empty() {
            return format_mem_snapshot();
        }

        let allocs_before = cranelisp_intrinsics::alloc_count();
        let deallocs_before = cranelisp_intrinsics::dealloc_count();
        let bytes_before = cranelisp_intrinsics::bytes_current();

        let eval_outcome = self.eval(expr_src);

        let allocs_after = cranelisp_intrinsics::alloc_count();
        let deallocs_after = cranelisp_intrinsics::dealloc_count();
        let bytes_after = cranelisp_intrinsics::bytes_current();

        let d_allocs = allocs_after.saturating_sub(allocs_before);
        let d_deallocs = deallocs_after.saturating_sub(deallocs_before);
        let d_bytes = (bytes_after as i64) - (bytes_before as i64);
        let live_delta = (d_allocs as i64) - (d_deallocs as i64);

        let header = match eval_outcome {
            Ok(Some(result)) => self.format_eval_result(&result),
            Ok(None) => "(no result)".to_string(),
            Err(e) => crate::style::error_line(&e.to_string()),
        };

        let delta_line = format!(
            "; delta: allocs +{d_allocs}  deallocs +{d_deallocs}  bytes {d_bytes:+}  live {live_delta:+}"
        );
        format!("{header}\n{delta_line}")
    }

    /// /run-tests handler: discover and execute test-* functions.
    ///
    /// Scans def_codegen for zero-arg functions named `test-*`, calls each
    /// directly, interprets the `(Option String)` result: None = pass,
    /// Some(reason) = fail.
    /// /run-tests handler: discover and run test-* functions.
    ///
    /// With no argument: tests in current module. With a module path: tests
    /// in that module. Runs all tests fast first, then re-runs failures with
    /// tracing to capture trace trees for diagnostics.
    pub(crate) fn handle_run_tests(&self, arg: &str) -> String {
        let module = if arg.is_empty() {
            self.current_module_path()
        } else {
            ModuleFullPath::from(arg)
        };
        // Core discovery — shared with discover_tests_extern.
        let test_names = discover_test_names(
            &self.shared.symbol_tables,
            &module,
        );
        if test_names.is_empty() {
            return if arg.is_empty() {
                "No test-* functions found.".to_string()
            } else {
                format!("No test-* functions found in '{arg}'.")
            };
        }
        self.format_test_run(&test_names)
    }

    /// /run-all-tests handler: discover and run tests in all project-root modules.
    /// `/platform-schema <name>` — print the compiler-generated schema artifact
    /// for a loaded platform (platform-interface.md §5.5.1 / §6.0).
    ///
    /// Looks up the loaded platform's `platform.<name>` symbol table, derives
    /// the referenced-ADT root set from its `DefKind::PlatformEffect` sigs, and
    /// calls the backend schema generator (the same closure-walk the load-time
    /// hash gate runs) to emit the artifact text (with the `;; layout-hash:`
    /// header). The author redirects this to the embed file. A thin caller of
    /// the backend generator — int does no schema logic of its own.
    pub(crate) fn handle_platform_schema(&self, name: &str) -> String {
        let name = name.trim();
        if name.is_empty() {
            return "Usage: /platform-schema <name>".to_string();
        }
        let module_path = ModuleFullPath::from(format!("platform.{name}"));
        let roots = match self.module_table(&module_path) {
            Some(table) => cranelisp_backend::schema::platform_effect_roots(&table),
            None => {
                return format!(
                    "Platform '{name}' is not loaded. Load it first with \
                     `(platform {name})`, then re-run /platform-schema."
                );
            }
        };
        cranelisp_backend::schema::generate_schema(&self.shared.symbol_tables, &roots)
    }

    pub(crate) fn handle_run_all_tests(&self) -> String {
        let mut all_names: Vec<String> = Vec::new();
        for entry in self.shared.typecheck_products.iter() {
            let module_path = entry.key();
            if let Some(ref fp) = entry.value().file_path
                && !fp.starts_with(&self.shared.project_root) {
                    continue;
                }
            let names = discover_test_names(
                &self.shared.symbol_tables,
                module_path,
            );
            all_names.extend(names);
        }
        all_names.sort();
        if all_names.is_empty() {
            return "No test-* functions found in any project module.".to_string();
        }
        self.format_test_run(&all_names)
    }

    /// Re-run a failing test with tracing by eval'ing `(trace (test-name))`.
    /// Format a test run: run all tests via shared core logic.
    pub(crate) fn format_test_run(&self, test_names: &[String]) -> String {
        let start = std::time::Instant::now();
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut lines = Vec::new();

        for name in test_names {
            // Core test execution — shared with run_test_extern.
            let outcome = run_test_by_name(
                &self.shared.symbol_tables,
                name,
                &self.current_repl_module,
            );
            let dots = ".".repeat(40usize.saturating_sub(name.len()));
            match &outcome {
                TestOutcome::Pass { .. } => {
                    lines.push(format!("  {name} {dots} ok"));
                    passed += 1;
                }
                TestOutcome::Fail { reason, .. } => {
                    lines.push(format!("  {name} {dots} FAILED: {reason}"));
                    failed += 1;
                }
                TestOutcome::Panic { reason, .. } => {
                    lines.push(format!("  {name} {dots} PANIC: {reason}"));
                    failed += 1;
                }
            }
        }

        let elapsed = start.elapsed();
        lines.push(String::new());
        if failed == 0 {
            lines.push(format!(
                "{passed} passed in {:.2}ms",
                elapsed.as_secs_f64() * 1000.0,
            ));
        } else {
            lines.push(format!(
                "{passed} passed, {failed} failed in {:.2}ms",
                elapsed.as_secs_f64() * 1000.0,
            ));
        }

        lines.join("\n")
    }
}


#[cfg(test)]
mod mem_command_tests {
    use super::*;
    
    

    

    // spec: repl/spec.md §3.1 — `/mem` dispatches to the Mem variant and
    // accepts the `/m` alias.
    #[test]
    fn mem_command_parses_with_alias() {
        match parse_slash_command("/mem") {
            Some(ReplCommand::Mem(arg)) => assert_eq!(arg, ""),
            _ => panic!("/mem must parse as ReplCommand::Mem"),
        }
        match parse_slash_command("/m") {
            Some(ReplCommand::Mem(arg)) => assert_eq!(arg, ""),
            _ => panic!("/m alias must parse as ReplCommand::Mem"),
        }
    }

    // spec: repl/spec.md §3.1 — `/mem <expr>` passes the expression text
    // through to the handler for delta measurement.
    #[test]
    fn mem_command_captures_expression_argument() {
        match parse_slash_command("/mem (+ 1 2)") {
            Some(ReplCommand::Mem(arg)) => assert_eq!(arg, "(+ 1 2)"),
            _ => panic!("/mem <expr> must capture the expression argument"),
        }
    }

    // spec: repl/spec.md §3.1 — `/mem` snapshot contains live/alloc/dealloc
    // counters. Format confirms the user-visible labels exist and the
    // counters are numeric.
    #[test]
    fn mem_snapshot_mentions_allocs_deallocs_and_numbers() {
        let out = format_mem_snapshot();
        assert!(out.contains("allocs:"), "snapshot must label allocs: {out}");
        assert!(out.contains("deallocs:"), "snapshot must label deallocs: {out}");
        assert!(out.contains("live:"), "snapshot must label live: {out}");
        // Every line must be a comment (starts with ';').
        for line in out.lines() {
            assert!(
                line.starts_with(';'),
                "every snapshot line must be a comment: {line}",
            );
        }
        // At least one digit must appear.
        assert!(
            out.chars().any(|c| c.is_ascii_digit()),
            "snapshot must contain at least one number: {out}",
        );
    }
}

// ---------------------------------------------------------------------------
// Sprint 60 Workstream G — /sig docstring format fix.
// spec: repl/spec.md §1.1 — universal output format mandates
//       `:Type name ; classification - docstring-first-line`.
// design: design/int/dual-path-persistence-collapse.md §9.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod sig_display_helper_tests {
    use super::*;
    
    

    
    use cranelisp_types::Scheme;
    use std::collections::HashMap as StdHashMap;

    // spec: repl/spec.md §4.1.5 — a special form's `:Type` prefix is rendered
    //   from the entry's own `Fn` scheme (single source), NOT a hardcoded sig
    //   table (FIXME 0338). `trace`'s `(Fn [a] Trace)` scheme renders `:(Fn …`.
    #[test]
    fn special_form_display_renders_type_prefix_from_fn_scheme() {
        let trace_ty = Type::Fn(
            vec![Type::Var(0)],
            Box::new(Type::ADT(
                cranelisp_types::FQTypeName {
                    module: ModuleFullPath::from("primitives"),
                    name: TypeName::from("Trace"),
                },
                vec![],
            )),
        );
        let scheme = Scheme { type_vars: vec![], constraints: StdHashMap::new(), ty: trace_ty };
        let out = format_special_form_display("trace", &scheme, "trace desc");
        assert!(
            out.starts_with(":(Fn ") && out.contains("trace ; special form - trace desc"),
            "Fn-scheme special form MUST carry a `:Type` prefix, got: {out}"
        );
    }

    // spec: repl/spec.md §4.1.5 — `if`'s registered scheme renders the exact
    //   `:(Fn [primitives/Bool a a] a)` prefix the control test pins (FIXME 0338).
    #[test]
    fn special_form_display_if_scheme_renders_bool_arrow() {
        let if_ty = Type::Fn(
            vec![Type::Bool, Type::Var(0), Type::Var(0)],
            Box::new(Type::Var(0)),
        );
        let scheme = Scheme { type_vars: vec![], constraints: StdHashMap::new(), ty: if_ty };
        let out = format_special_form_display("if", &scheme, "cond");
        assert!(
            out.starts_with(":(Fn [primitives/Bool a a] a) if ; special form"),
            "if MUST render the Bool→a arrow from its scheme, got: {out}"
        );
    }

    fn mk_clause(name: &str) -> cranelisp_types::MacroClauseInfo {
        cranelisp_types::MacroClauseInfo {
            params: vec![cranelisp_types::MacroParam::Name(Symbol::from(name))],
            rest_param: None,
        }
    }

    // spec: repl/spec.md §11.2.2 — a multi-clause macro card ends with a
    //   `N clauses` summary line (two leading spaces, no `;`).
    #[test]
    fn format_macro_display_multi_clause_shows_clause_count() {
        let module = ModuleFullPath::from("user");
        let clauses = vec![mk_clause("x"), mk_clause("y")];
        let out = format_macro_display("cond", &clauses, None, &module);
        assert!(
            out.contains("2 clauses"),
            "multi-clause macro card MUST end with the clause count, got: {out}"
        );
    }

    // spec: repl/spec.md §11.2.2 — the single-clause worked example shows NO
    //   count line; the gate is `clauses.len() > 1`.
    #[test]
    fn format_macro_display_single_clause_omits_clause_count() {
        let module = ModuleFullPath::from("user");
        let clauses = vec![mk_clause("x")];
        let out = format_macro_display("when", &clauses, None, &module);
        assert!(
            !out.contains("clauses"),
            "single-clause macro card MUST NOT carry a clause count, got: {out}"
        );
    }
}

#[cfg(test)]
mod fq_arg_commands_tests {
    use super::*;
    
    
    use crate::repl::test_support::*;
    
    use cranelisp_types::{
        ModuleAliasEntry, ModuleEntry, ModuleFullPath, Span,
        Symbol, Visibility,
    };
    

    // A bare argument keeps the current module as its home; the FQ split leaves
    // it untouched. spec: §17.6.1
    #[test]
    fn resolve_symbol_arg_bare_keeps_current_module() {
        let s = session();
        let (home, bare) = s.resolve_symbol_arg("foo");
        assert_eq!(home, s.current_module_path());
        assert_eq!(bare, "foo");
    }
    // A module-qualified argument splits on the LAST `/` into (home, bare).
    // spec: spec/08-modules.md §8.5.1
    #[test]
    fn resolve_symbol_arg_qualified_splits_home_and_bare() {
        let s = session();
        let (home, bare) = s.resolve_symbol_arg("m/mf");
        assert_eq!(home.as_ref(), "m");
        assert_eq!(bare, "mf");
    }
    // The qualifier is alias-substituted (§8.6.6): a `(mod util)`-style bare
    // alias `u → real.mod` resolves the home.
    #[test]
    fn resolve_symbol_arg_substitutes_module_alias() {
        let s = session();
        s.shared.module_aliases.insert(
            ModuleFullPath::from("u"),
            ModuleAliasEntry::new(ModuleFullPath::from("real.mod"), Visibility::Private, Span::SYNTHETIC),
        );
        let (home, bare) = s.resolve_symbol_arg("u/helper");
        assert_eq!(home.as_ref(), "real.mod");
        assert_eq!(bare, "helper");
    }
    // resolve_entry_arg finds a module-qualified symbol in its home table.
    #[test]
    fn resolve_entry_arg_qualified_finds_entry_in_home_table() {
        let s = session();
        install_m(&s, None);
        let got = s.resolve_entry_arg("m/mf");
        assert!(got.is_some(), "m/mf must resolve to the Def in module m");
        let (_, home, bare) = got.unwrap();
        assert_eq!(home.as_ref(), "m");
        assert_eq!(bare, "mf");
    }
    // /sig on a module-qualified name shows the full FQ signature line (not
    // `unknown symbol`). spec: §3.8
    #[test]
    fn handle_sig_accepts_fq_name() {
        let s = session();
        install_m(&s, Some("doc mf"));
        let out = s.handle_sig("m/mf");
        assert!(!out.contains("unknown symbol"), "got: {out}");
        assert!(out.contains("m/mf"), "the FQ name must appear; got: {out}");
        assert!(out.contains("(Fn ["), "the full signature must appear; got: {out}");
    }
    // §3.8 (FIXME 0492): /sig on a bare LOCAL name renders the SAME
    // fully-qualified primary line as bare-value display — the
    // `format_def_entry` composition — not the short unqualified
    // `:(Fn [Int] Int) dbl` form the pre-fix bare-local arm used. Asserted as
    // byte-equality with `format_def_entry` at the display seam so the two
    // surfaces cannot drift.
    #[test]
    fn handle_sig_bare_local_matches_format_def_entry_fully_qualified() {
        let s = session();
        let user = s.current_module_path();
        let entry = userfn_def(Some("Multiply by 2"));
        if let Some(mut table) = s.shared.symbol_tables.get_mut(&user) {
            table.insert(Symbol::from("dbl"), entry.clone());
        } else {
            let mut table = SessionSymbolTable::new_with_params(user.clone());
            table.insert(Symbol::from("dbl"), entry.clone());
            s.shared.symbol_tables.insert(user.clone(), table);
        }
        let sig = s.handle_sig("dbl");
        // `/sig` threads `full_trait_sections = true` (§3.8 pure introspection);
        // match it so the byte-equality holds (the flag is inert for a fn).
        let expected = s.format_def_entry(&entry, "dbl", &user, true);
        assert_eq!(
            sig, expected,
            "/sig bare-local MUST render the identical §3.8 primary line as \
             format_def_entry (bare-value display); got: {sig}"
        );
        assert!(
            sig.starts_with(":(Fn [primitives/Int] primitives/Int) user/dbl ; defn"),
            "primary line MUST be fully qualified in BOTH positions; got: {sig}"
        );
    }
    // spec: repl/spec.md §3.3/§17.19.2b — /list groups each constructor under its
    // canonical dotted `Type.Ctor` form beneath Types (the bare alias is an
    // `Import`, never a second row). The enumeration seam MUST surface `Color.Red`.
    #[test]
    fn list_surfaces_constructor_under_canonical_dotted_form() {
        let s = session();
        install_color_red(&s);
        let out = s.handle_list("");
        assert!(
            out.contains("Color.Red"),
            "/list MUST list the constructor under its canonical `Color.Red` form; \
             got:\n{out}"
        );
        assert!(
            !out.contains("Color.Color.Red"),
            "/list MUST NOT double the type segment; got:\n{out}"
        );
    }
    // /info on a module-qualified name resolves (not `unknown symbol`) and
    // renders one clean `module/name` (no `module/mod/name` double). spec: §3.6
    #[test]
    fn handle_info_accepts_fq_name_single_qualification() {
        let s = session();
        install_m(&s, Some("doc mf"));
        let out = s.handle_info("m/mf");
        assert!(!out.contains("unknown symbol"), "got: {out}");
        assert!(out.contains("m/mf"), "got: {out}");
        assert!(!out.contains("m/m/mf") && !out.contains("m/mf/mf"), "no double-qualification; got: {out}");
    }
    // /doc on a module-qualified name resolves the symbol (not `unknown
    // symbol`). spec: §3.6 / §17.5.1
    #[test]
    fn handle_doc_accepts_fq_name() {
        let s = session();
        install_m(&s, Some("doc mf"));
        let out = s.handle_doc("m/mf");
        assert!(!out.contains("unknown symbol"), "got: {out}");
        assert!(out.contains("doc mf"), "the docstring must appear; got: {out}");
    }
    // /sig on an unknown FQ name is graceful.
    #[test]
    fn handle_sig_unknown_fq_is_graceful() {
        let s = session();
        let out = s.handle_sig("nope/missing");
        assert!(out.contains("unknown symbol"), "got: {out}");
    }
    // collect_referers surfaces a caller via the reverse-index feed even when
    // the caller carries no introspection body (cache-restored-shape: the
    // `callees` edge is the authority). spec: §17.6.1
    #[test]
    fn collect_referers_reverse_index_finds_caller_without_introspection() {
        let s = session();
        let m = ModuleFullPath::from("m");
        let mut table = SessionSymbolTable::new_with_params(m.clone());
        table.insert(Symbol::from("mf"), userfn_def(None));
        // mg calls mf — the `callees` edge (serialized for cache-restored
        // modules) is present, but no introspection record exists.
        let mut mg = userfn_def(None);
        if let ModuleEntry::Def { callees, .. } = &mut mg {
            callees.push(FQSymbol { module: m.clone(), symbol: Symbol::from("mf") });
        }
        table.insert(Symbol::from("mg"), mg);
        s.shared.symbol_tables.insert(m.clone(), table);

        let referers = s.collect_referers(&m, "mf", false);
        assert!(
            referers.iter().any(|r| r == "m/mg"),
            "the reverse-index feed must list m/mg without an introspection body; got: {referers:?}",
        );
    }
    // A `$`-mangled mono variant caller (`g$Int`) is reported at BASE grain
    // (`m/g`), exactly once — never the internal mangled name `m/g$Int`, and
    // never double-listed when the base defn `g` is ALSO a reverse-index caller
    // of the target (both legs strip to `m/g`, then sort+dedup merges them).
    // spec: §17.6.1
    #[test]
    fn collect_referers_reports_mono_variant_caller_at_base_grain_once() {
        let s = session();
        let m = ModuleFullPath::from("m");
        let mut table = SessionSymbolTable::new_with_params(m.clone());
        table.insert(Symbol::from("mf"), userfn_def(None));
        // Base template `g` calls mf.
        let mut g = userfn_def(None);
        if let ModuleEntry::Def { callees, .. } = &mut g {
            callees.push(FQSymbol { module: m.clone(), symbol: Symbol::from("mf") });
        }
        table.insert(Symbol::from("g"), g);
        // A minted mono instance `g$Int` also calls mf — `ReverseIndex::build`
        // records the mangled name verbatim as a caller.
        let mut g_int = userfn_def(None);
        if let ModuleEntry::Def { callees, .. } = &mut g_int {
            callees.push(FQSymbol { module: m.clone(), symbol: Symbol::from("mf") });
        }
        table.insert(Symbol::from("g$Int"), g_int);
        s.shared.symbol_tables.insert(m.clone(), table);

        let referers = s.collect_referers(&m, "mf", false);
        assert!(
            !referers.iter().any(|r| r.contains('$')),
            "the internal mangled name (m/g$Int) must NOT leak; got: {referers:?}",
        );
        let base_hits = referers.iter().filter(|r| r.as_str() == "m/g").count();
        assert_eq!(
            base_hits, 1,
            "the mono variant + its base collapse to ONE m/g entry; got: {referers:?}",
        );
    }
}
