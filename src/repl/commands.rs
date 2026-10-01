// REPL slash-command handler battery (`handle_*`). Extracted from `repl.rs`
// per `design/int/int.md` §3.3 (S110, FIXME 0606). Pure
// relocation, behaviour-invariant.

use super::format::*;
use super::*;

/// What `/mod` reports beyond the switch itself (`design/int/int.md` §8.5.1).
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ModReport {
    /// No switch: the target names no module or its load failed. The current
    /// module is unchanged.
    Refused(String),
    /// The switch happened, and recompiling the cache-installed target from
    /// its file failed: each failed module's notification.
    RecompileFailed(String),
}

/// Classification of an imported symbol for category-based display.
pub(crate) enum ImportClass {
    Macro,
    Trait,
    Type,
    Constructor,
    Fn,
}

/// The `/imports` category of an imported name's definition.
pub(crate) fn classify_definition(entry: &Binding<Code>) -> ImportClass {
    match &entry.declaration {
        Decl::Macro(_) => ImportClass::Macro,
        Decl::Callable(callable) if matches!(callable.origin, CallableOrigin::Ctor { .. }) => {
            ImportClass::Constructor
        }
        Decl::Trait(_) => ImportClass::Trait,
        Decl::Type(_) => ImportClass::Type,
        _ => ImportClass::Fn,
    }
}

/// The docstring a declaration carries, whatever its kind — the one reader
/// `/doc` uses. Builtin docstrings live on the `primitives` entry itself
/// (`PrimitiveDef.docstring`), never in a parallel int-side table (FIXME 0308).
fn declaration_docstring(entry: &Binding<Code>) -> Option<&str> {
    match &entry.declaration {
        Decl::Callable(callable) => callable.docstring.as_deref(),
        Decl::Overloaded(declaration) => declaration.docstring.as_deref(),
        Decl::Macro(declaration) => declaration.docstring.as_deref(),
        Decl::Trait(record) => record.docstring.as_deref(),
        Decl::Type(
            TypeRecord::Defined { docstring, .. } | TypeRecord::Intrinsic { docstring, .. },
        ) => docstring.as_deref(),
        Decl::SpecialForm(record) => record.docstring.as_deref(),
        Decl::TraitMethod(record) => record.docstring.as_deref(),
        Decl::ImplShell(_) => None,
    }
}

impl CompilerSession {
    /// /sig handler: the §1.1 primary line of every candidate the spelling
    /// denotes (§3.8, §4.1.11).
    ///
    /// The lines ARE bare lookup's lines — the same candidate query and the
    /// same builder — so §3.8's byte-identity is structural rather than a rule
    /// two formatters have to keep.
    pub(crate) fn handle_sig(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /sig <name>".to_string();
        }
        if intrinsic_type_from_name(name).is_some() {
            return format!("{name} ; type - builtin type");
        }
        let symbols = self.resolve_candidates(name, SpecialFormTail::Consulted);
        if symbols.is_empty() {
            return format!("error: unknown symbol '{name}'");
        }
        render(&self.format_symbol_lines_doc(&symbols))
    }

    /// /doc handler: the docstring of every candidate the spelling denotes
    /// (§3.1, §11.2.4, §4.1.11). A candidate's docstring lives on its own
    /// defining entry — a bare re-exported primitive (`add-i64`) resolves to
    /// the `primitives` definition that carries it.
    pub(crate) fn handle_doc(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /doc <name>".to_string();
        }
        let candidates = self.resolve_candidates(name, SpecialFormTail::Consulted);
        if candidates.is_empty() {
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
        }
        // One declaration answers under the name the user wrote; several are
        // told apart by their canonical identity, the only thing that
        // distinguishes them (§4.1.11 compares no types).
        let qualify = candidates.len() > 1;
        candidates
            .iter()
            .map(|symbol| {
                let label = if qualify {
                    symbol.to_string()
                } else {
                    name.to_string()
                };
                let entry = self.entry_at(symbol);
                match entry.as_ref().and_then(declaration_docstring) {
                    Some(doc) => format!("{label}: \"{doc}\""),
                    None => format!("{label}: no docstring"),
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// /list handler: list symbols in current module.
    pub(crate) fn handle_list(&self, _filter: &str) -> String {
        let table_ref = self.current_symbol_table();
        let mut fns = Vec::new();
        let mut types = Vec::new();
        let mut traits = Vec::new();
        let mut macros = Vec::new();

        for (name, entry) in table_ref.all_symbols() {
            // §3.3: internal compiler artifacts are not user definitions —
            // `$`-mangled names and the synthetic `__expr` top-level-expression
            // wrapper are excluded (shared predicate so the filter cannot drift
            // from the synthesis site).
            if crate::worker::is_internal_listing_entry(name.as_ref(), entry) {
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
    fn collect_referers(&self, home: &ModuleFullPath, bare: &str, tests_only: bool) -> Vec<String> {
        let mut referers: Vec<String> = Vec::new();
        // Callable referents via the reverse index (skip for `/tests-for`,
        // whose token scan admits only test functions).
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
                let base =
                    crate::redefine::base_fq_from_tables(&self.shared.symbol_tables, &caller);
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
    /// A specialization of `/refs` filtered to test functions: the `test-`
    /// prefix and the §16.1 signature, as the test runner decides them.
    /// LLM-free, default build.
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

    /// /mod handler: switch to an existing module, loading it from its file
    /// when it is not yet loaded, and never create one
    /// (`design/int/int.md` §8.5.1; `repl/spec/03-slash-commands.md` §3.9).
    /// Bare `/mod` returns to the entry module.
    pub(crate) fn handle_mod(&mut self, name: &str) -> Option<ModReport> {
        let target = if name.is_empty() {
            self.entry_module.clone()
        } else {
            self.resolve_mod_target(name)
        };
        if !self.shared.symbol_tables.contains_key(&target)
            && let Err(refusal) = self.load_mod_target(&target)
        {
            return Some(ModReport::Refused(refusal));
        }
        let failure = self.recompile_cache_installed_module(&target);
        self.set_current_module(target);
        failure.map(ModReport::RecompileFailed)
    }

    /// The module `name` names from the current module, by the one
    /// bare-module-name resolver over its declared children
    /// (`design/int/int.md` §6.9). Import aliases are not module names.
    fn resolve_mod_target(&self, name: &str) -> ModuleFullPath {
        let current = self.current_module_path();
        let spelling = ModuleFullPath::from(name);
        match self.shared.symbol_tables.get(&current) {
            Some(table) => {
                crate::imports::DeclaredChildren::of(&current, &table.submodules).resolve(&spelling)
            }
            None => spelling,
        }
    }

    /// Load `target` through the language's load-on-reference: the module
    /// search, the dependency drive and the eval thread's wait. Returns the
    /// refusal to report when no file backs it or its load fails.
    ///
    /// A failed load runs the failed load's record over the modules it left
    /// `Failed` (`design/int/repl-lifecycle.md` §1.3.1): the target stands
    /// failed for a failure in its own source, its file failing to parse
    /// included, and waits when a dependency standing failed refused it.
    fn load_mod_target(&mut self, target: &ModuleFullPath) -> Result<(), String> {
        let lib_dirs = self.lib_dirs();
        if crate::pipeline::resolve_module_file(target, &self.shared.project_root, &lib_dirs)
            .is_none()
        {
            return Err(format!("Module '{target}' not found."));
        }
        let held = self.shared.scheduler.failed_modules();
        let current = self.current_module_path();
        let loaded = match self.with_eval_compiler(&current, |ctx| {
            crate::process_form::drive_module_dep(ctx, &current, target, Span::SYNTHETIC)
        }) {
            Err(error) => Err(self.reset_failed_load(&held, error)),
            Ok(()) => self.register_dep_for_eval(target, &held),
        };
        loaded.map_err(|mut failure| {
            self.record_failed_load(&mut failure.reset);
            failure.error.to_string()
        })
    }

    /// Make a cache-installed module editable: rebuild it and its dependents
    /// from their backing files through the one reload executor, so every
    /// generation regeneration writes was compiled from source this session
    /// (`design/int/session-persistence.md` §2.4.5). Returns the notification
    /// of each module that failed. The entry module, a module compiled from
    /// source and a module not yet loaded are left as they are.
    fn recompile_cache_installed_module(&mut self, module: &ModuleFullPath) -> Option<String> {
        if *module == self.entry_module || !self.shared.scheduler.is_cached_module(module) {
            return None;
        }
        let backing = self
            .shared
            .typecheck_products
            .get(module)
            .and_then(|product| product.file_path.clone())?;
        let failures: Vec<String> = self
            .run_reload_plan(vec![(module.clone(), backing)])
            .into_iter()
            .filter(|outcome| matches!(outcome.status, crate::session_v4::ReloadStatus::Failed(_)))
            .filter_map(|outcome| outcome.notice())
            .collect();
        (!failures.is_empty()).then(|| failures.join("\n"))
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
            && let Some(ref sexp) = intr.sexp
        {
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
            && let Some(ref defn) = intr.ast
        {
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
            && let Some(ref clif) = intr.clif_ir
        {
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
        let Some(code_size) = self.get_introspection(name).and_then(|intr| intr.code_size) else {
            return crate::style::error_line(&format!("no disassembly available for '{name}'"));
        };
        match cranelisp_backend::produce_disasm(&fq, code_size, &self.shared.symbol_tables) {
            Ok(text) => format!("; disasm for {name}\n{text}"),
            Err(_) => crate::style::error_line(&format!("no disassembly available for '{name}'")),
        }
    }

    /// /info handler: the full card of every candidate the spelling denotes —
    /// signature, definition source and code size (§3.6, §4.1.11). A
    /// module-qualified argument resolves like any other, so the FQ names the
    /// cascade reports print stay pasteable (FIXME 0487).
    pub(crate) fn handle_info(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /info <name>".to_string();
        }
        if intrinsic_type_from_name(name).is_some() {
            return self.format_builtin_type_display(name);
        }
        let cards: Vec<String> = self
            .resolve_candidates(name, SpecialFormTail::Consulted)
            .iter()
            .map(|symbol| self.info_card(symbol))
            .collect();
        if cards.is_empty() {
            return format!("error: unknown symbol '{name}'");
        }
        cards.join("\n")
    }

    /// One candidate's `/info` card, every component keyed by that candidate's
    /// own canonical identity.
    ///
    /// §3.6 is a pure-introspection surface (FIXME 0647: an empty trait
    /// `; impl:` section is omitted uniformly). S101 (repl/spec.md §18.4): a
    /// BROKEN symbol shows the primary line (last-good signature), the
    /// provenance comment line and the definition source, and MUST NOT show
    /// code-size stats — its compiled code is gone, and the trap stub is an
    /// implementation detail, not the symbol's code.
    fn info_card(&self, symbol: &FQSymbol) -> String {
        let bare = symbol.symbol.as_ref();
        let module = &symbol.module;
        let mut out = render(&self.format_definition_symbol_doc(symbol));
        // §3.6 third MUST component (FIXME 0480): the definition source,
        // rendered for BOTH the broken and healthy arms.
        if let Some(source) = self.info_definition_source(bare, module) {
            out.push('\n');
            out.push_str(&source);
        }
        let shows_code_size = self.broken_status_line(bare, module).is_none()
            && self.entry_at(symbol).is_some_and(|entry| {
                !matches!(
                    entry.declaration,
                    Decl::Macro(_) | Decl::Type(_) | Decl::Trait(_)
                )
            });
        if shows_code_size && let Some(record) = self.introspection_at(symbol) {
            let size = record
                .code_size
                .map(|bytes| format!("{bytes} bytes"))
                .unwrap_or_else(|| "? bytes".to_string());
            out.push_str(&format!("\n  {size}"));
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
        crate::save::rehydrate_introspection_from_source(
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

        // Bare expressions become synthetic __expr definitions for the same
        // typecheck path used by definitions.
        let working_program = crate::worker::build_program_compat(&[sexps[0].clone()])?;
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
                    let wrapper_span =
                        Span::new(span.start.saturating_sub(1), span.end.saturating_add(1));
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
        match table.get("__expr")?.callable() {
            Some(callable) => {
                // Zero-arg defns have type `Fn([], ret)` — surface the return.
                if let Type::Fn(_, ret) = &callable.arm.scheme.ty {
                    Some((*ret.clone()).clone())
                } else {
                    Some(callable.arm.scheme.ty.clone())
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
        // Public candidates only — both prelude's own defs and its `(export …)`
        // re-exports (e.g. `add-i64`) are user-visible. Collect them under the
        // prelude guard and drop it before resolving: `listable_definition`
        // takes its own table guard, which may be this same entry (0666).
        let Some(table) = self.shared.symbol_tables.get(&prelude_path) else {
            return Vec::new();
        };
        let candidates: Vec<(String, FQSymbol)> = table
            .public_name_candidates()
            .map(|(sym, candidate)| (sym.to_string(), candidate.source))
            .collect();
        drop(table);
        let mut names: Vec<String> = Vec::new();
        for (name, source) in candidates {
            let Some(entry) = self.listable_definition(&source) else {
                continue;
            };
            if matches!(entry.declaration, Decl::SpecialForm(_)) {
                continue;
            }
            names.push(name);
        }
        names.sort();
        names.dedup();
        names
    }

    /// `module`'s explicit imports: each name candidate whose source is another
    /// module, as `(spelling, source)`. The table guard is released before
    /// returning, so callers may resolve the sources (0666).
    pub(crate) fn explicit_import_sources(
        &self,
        module: &ModuleFullPath,
    ) -> Vec<(String, FQSymbol)> {
        let Some(table) = self.shared.symbol_tables.get(module) else {
            return Vec::new();
        };
        table
            .all_name_candidates()
            .filter(|(_, candidate)| candidate.source.module != *module)
            .map(|(sym, candidate)| (sym.to_string(), candidate.source))
            .collect()
    }

    /// The definition `source` names, unless it is an internal entry that no
    /// name listing shows (generated instances, `__expr`). Takes its own table
    /// guard: call it with none held.
    pub(crate) fn listable_definition(&self, source: &FQSymbol) -> Option<Binding<Code>> {
        let entry = self.resolve_to_definition(source)?;
        (!crate::worker::is_internal_listing_entry(source.symbol.as_ref(), &entry)).then_some(entry)
    }

    /// /imports handler: list imports in current module by category.
    pub(crate) fn handle_imports(&self, filter: &str) -> String {
        let current = self.current_module_path();
        let imports: Vec<(String, FQSymbol, Binding<Code>)> = self
            .explicit_import_sources(&current)
            .into_iter()
            .filter_map(|(name, source)| {
                let entry = self.listable_definition(&source)?;
                Some((name, source, entry))
            })
            .collect();
        let mut output = String::new();

        if filter.is_empty() {
            // Unfiltered mode: organize by category
            let mut special_forms: Vec<String> = Vec::new();
            let mut macros: Vec<String> = Vec::new();
            let mut traits: Vec<String> = Vec::new();
            let mut types: Vec<String> = Vec::new();
            let mut fns: Vec<String> = Vec::new();

            // Special forms are registered only in the root `""` module
            // (Principle 17), never in the current module's table.
            let root = ModuleFullPath::from("");
            if let Some(root_table) = self.shared.symbol_tables.get(&root) {
                for (sym, entry) in root_table.all_symbols() {
                    if matches!(entry.declaration, Decl::SpecialForm(_)) {
                        special_forms.push(sym.to_string());
                    }
                }
            }

            for (name, _, entry) in imports {
                match classify_definition(&entry) {
                    ImportClass::Macro => macros.push(name),
                    ImportClass::Trait => traits.push(name),
                    ImportClass::Type | ImportClass::Constructor => types.push(name),
                    ImportClass::Fn => fns.push(name),
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

            // The implicit prelude is a resolution fallback, not entries in
            // this module's table, so its names form their own group, present
            // only while the module's prelude-fallback bit is ON.
            let prelude_names = self.prelude_implicit_names();
            if !prelude_names.is_empty() {
                output.push_str(&format_prelude_implicit_group(&prelude_names));
            }

            if special_forms.is_empty()
                && macros.is_empty()
                && traits.is_empty()
                && types.is_empty()
                && fns.is_empty()
                && prelude_names.is_empty()
            {
                output.push_str("(no imports)");
            }
        } else {
            // Filtered mode: show imports from named module only
            let mut names: Vec<String> = imports
                .into_iter()
                .filter(|(_, source, _)| *source.module == *filter)
                .map(|(name, _, _)| name)
                .collect();
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

    /// The binding `source` names in its home module's table.
    pub(crate) fn resolve_to_definition(&self, source: &FQSymbol) -> Option<Binding<Code>> {
        let table = self.module_table(&source.module)?;
        table.get(source.symbol.as_ref()).cloned()
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

        // Owned, so the table guard is released before `resolve_to_definition`
        // takes its own.
        let candidates: Vec<(Symbol, FQSymbol)> = match self.module_table(&module_path) {
            Some(table) => table
                .public_name_candidates()
                .map(|(sym, candidate)| (sym.clone(), candidate.source))
                .collect(),
            None => return format!("Module '{mod_name}' not found"),
        };

        let mut macros: Vec<String> = Vec::new();
        let mut traits: Vec<String> = Vec::new();
        let mut types: Vec<String> = Vec::new();
        let mut fns: Vec<String> = Vec::new();

        for (sym, source) in candidates {
            let name = sym.to_string();
            if !prefix_filter.is_empty()
                && !name
                    .to_lowercase()
                    .starts_with(&prefix_filter.to_lowercase())
            {
                continue;
            }
            // Bucketing is the shared `classify_listing_entry` classifier (FIXME
            // 0440); /exports's only presentation concern is folding the
            // Constructor category into Types (a public ctor is listed under its
            // type) and dropping special forms.
            let Some(entry) = self.resolve_to_definition(&source) else {
                continue;
            };
            // §3.3: `$`-mangled internal names and the public synthetic
            // `__expr` wrapper are not listed. Keyed on the exposed spelling.
            if crate::worker::is_internal_listing_entry(&name, &entry) {
                continue;
            }
            // A local sum constructor is exposed twice for lookup: under its
            // canonical `Type.Ctor` binding and under the convenient bare
            // spelling. `/exports` describes declarations, not every lookup
            // spelling, so retain only the canonical local binding. External
            // re-export aliases remain visible because their source module is
            // different from the module being described.
            if source.module == module_path
                && source.symbol != sym
                && matches!(
                    &entry.declaration,
                    Decl::Callable(callable)
                        if matches!(callable.origin, CallableOrigin::Ctor { .. })
                )
            {
                continue;
            }
            match crate::worker::classify_listing_entry(&entry) {
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

        let has_any =
            !macros.is_empty() || !traits.is_empty() || !types.is_empty() || !fns.is_empty();

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
        match self.expand_form_sexp(form_src) {
            Ok(expanded) => format_sexp(&expanded),
            Err(e) => crate::style::error_line(&e.to_string()),
        }
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
        let sexp = sexps
            .into_iter()
            .next()
            .ok_or_else(|| CranelispError::ParseError {
                message: "empty form".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
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

        let mut eval_outcome = self.eval(expr_src);

        let header = match &mut eval_outcome {
            Ok(Some(result)) => {
                let rendered = self.format_eval_result(result);
                result.release_program_result();
                rendered
            }
            Ok(None) => "(no result)".to_string(),
            Err(e) => crate::style::error_line(&e.to_string()),
        };

        // Close the measurement only after the result has been observed and
        // released, so the delta describes the completed turn.
        let allocs_after = cranelisp_intrinsics::alloc_count();
        let deallocs_after = cranelisp_intrinsics::dealloc_count();
        let bytes_after = cranelisp_intrinsics::bytes_current();

        let d_allocs = allocs_after.saturating_sub(allocs_before);
        let d_deallocs = deallocs_after.saturating_sub(deallocs_before);
        let d_bytes = (bytes_after as i64) - (bytes_before as i64);
        let live_delta = (d_allocs as i64) - (d_deallocs as i64);

        let delta_line = format!(
            "; delta: allocs +{d_allocs}  deallocs +{d_deallocs}  bytes {d_bytes:+}  live {live_delta:+}"
        );
        format!("{header}\n{delta_line}")
    }

    /// `/run-tests [module]`: the shared test run over the current module, or
    /// over the named one (`repl/spec/16-test-discovery.md` §16.2.1).
    pub(crate) fn handle_run_tests(&self, arg: &str) -> String {
        let module = if arg.is_empty() {
            self.current_module_path()
        } else {
            ModuleFullPath::from(arg)
        };
        // A cache-restored parent enrolls its declared children synchronously,
        // but their object may still be queued for in-memory loading, so a
        // named, registered module is observed only after its in-memory
        // readiness boundary.
        if self.shared.scheduler.is_registered(&module)
            && let Err(error) = self
                .shared
                .scheduler
                .wait_module_inmem_complete_blocking(&module)
        {
            return crate::style::error_line(&error.to_string());
        }
        self.display_test_run(&[module])
    }

    /// `/run-all-tests`: the shared test run over every loaded module that is
    /// not a library module (`repl/spec/16-test-discovery.md` §16.2.2).
    pub(crate) fn handle_run_all_tests(&self) -> String {
        let modules = self.selection_inputs().non_library_modules();
        self.display_test_run(&modules)
    }

    /// Run the tests of `modules` and display the report text unchanged,
    /// preceded by one `; warning:` line per discovery warning.
    fn display_test_run(&self, modules: &[ModuleFullPath]) -> String {
        let report = self
            .shared
            .scheduler
            .wait_cached_loads_settled()
            .map_err(CranelispError::from)
            .and_then(|ready| self.run_test_modules(modules, ready));
        let report = match report {
            Ok(report) => report,
            Err(error) => return crate::style::error_line(&error.to_string()),
        };
        let mut doc = StyledDoc::new();
        for warning in report.warnings() {
            push_warning_line(&mut doc, &warning.message);
        }
        doc.plain(report.text());
        render(&doc)
    }

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
        assert!(
            out.contains("deallocs:"),
            "snapshot must label deallocs: {out}"
        );
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
// design: S60 Workstream G section of the retired dual-path collapse record —
//         `git show 7f834bf6:design/int/dual-path-persistence-collapse.md` §9.
//         No current design-of-record; the format rule is spec-owned above.
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
        let scheme = Scheme {
            type_vars: vec![],
            constraints: StdHashMap::new(),
            ty: trace_ty,
        };
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
        let scheme = Scheme {
            type_vars: vec![],
            constraints: StdHashMap::new(),
            ty: if_ty,
        };
        let out = format_special_form_display("if", &scheme, "cond");
        assert!(
            out.starts_with(":(Fn [primitives/Bool a a] a) if ; special form"),
            "if MUST render the Bool→a arrow from its scheme, got: {out}"
        );
    }

    fn mk_clause(name: &str) -> cranelisp_types::MacroClause<()> {
        clause(
            vec![cranelisp_types::MacroParam::Name(Symbol::from(name))],
            None,
        )
    }

    fn clause(
        params: Vec<cranelisp_types::MacroParam>,
        rest_param: Option<Symbol>,
    ) -> cranelisp_types::MacroClause<()> {
        cranelisp_types::MacroClause::new(
            cranelisp_types::CallableArmId::from_ordinal(0)
                .expect("fixture clause ordinal is representable"),
            params,
            rest_param,
            cranelisp_types::CallableArm::new(
                Scheme {
                    type_vars: Vec::new(),
                    constraints: StdHashMap::new(),
                    ty: Type::Int,
                },
                Vec::new(),
                cranelisp_types::Life::Declared { prior: None },
            ),
        )
    }

    #[test]
    fn format_macro_display_uses_compile_time_transform_signature() {
        let module = ModuleFullPath::from("user");
        let out = format_macro_display("n", &[clause(Vec::new(), None)], None, &module);
        assert_eq!(out, ":(Fn [] macros/Sexp) user/n ; defmacro");
    }

    #[test]
    fn format_macro_display_retains_variadic_pattern() {
        let module = ModuleFullPath::from("user");
        let out = format_macro_display(
            "many",
            &[clause(
                vec![cranelisp_types::MacroParam::Name(Symbol::from("x"))],
                Some(Symbol::from("rest")),
            )],
            None,
            &module,
        );
        assert_eq!(
            out,
            ":(Fn [macros/Sexp (macros/SList macros/Sexp)] macros/Sexp) user/many ; defmacro\n\
             ; pattern: [x & rest]"
        );
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

    use cranelisp_types::{ModuleAliasEntry, ModuleFullPath, Span, Symbol, Visibility};

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
            cranelisp_types::module_alias_key(&s.current_module_path(), "u"),
            ModuleAliasEntry::new(
                ModuleFullPath::from("real.mod"),
                Visibility::Private,
                Span::SYNTHETIC,
            ),
        );
        let (home, bare) = s.resolve_symbol_arg("u/helper");
        assert_eq!(home.as_ref(), "real.mod");
        assert_eq!(bare, "helper");
    }
    // The candidate query resolves a module-qualified symbol to the terminal
    // identity in its home table. spec: repl/spec/04-self-documentation.md §4.1.11
    #[test]
    fn qualified_argument_resolves_to_its_home_terminal() {
        let s = session();
        install_m(&s, None);
        assert_eq!(
            s.resolve_candidates("m/mf", SpecialFormTail::Consulted)
                .iter()
                .map(FQSymbol::to_string)
                .collect::<Vec<_>>(),
            vec!["m/mf".to_string()],
        );
    }

    // spec: repl/spec/04-self-documentation.md §4.1.11 — the candidate query is
    // the one lookup behind every introspection surface, so its cases are unit
    // cells at that seam: none, one, several, and identically typed candidates
    // (which are distinct declarations, never compared by type).
    #[test]
    fn candidate_query_answers_none_one_and_several() {
        let s = session();
        assert!(
            s.resolve_candidates("ghost", SpecialFormTail::Consulted)
                .is_empty(),
            "an unreachable spelling has no candidates"
        );

        install_m(&s, None);
        expose_import(&s, "mf", "m", "mf");
        assert_eq!(
            s.resolve_candidates("mf", SpecialFormTail::Consulted)
                .iter()
                .map(FQSymbol::to_string)
                .collect::<Vec<_>>(),
            vec!["m/mf".to_string()],
            "one import is one candidate"
        );

        // A second module exposing the SAME spelling with an identically typed
        // declaration: both are listed, in canonical order.
        let n = ModuleFullPath::from("n");
        let mut table = SessionSymbolTable::new_with_params(n.clone());
        let _ = install_userfn(&mut table, "mf", None, Visibility::Public);
        s.shared.symbol_tables.insert(n, table);
        expose_import(&s, "mf", "n", "mf");
        assert_eq!(
            s.resolve_candidates("mf", SpecialFormTail::Consulted)
                .iter()
                .map(FQSymbol::to_string)
                .collect::<Vec<_>>(),
            vec!["m/mf".to_string(), "n/mf".to_string()],
            "identically typed candidates are distinct declarations and both list"
        );
    }

    // spec: repl/spec/04-self-documentation.md §4.1.11 — the query lists
    // DECLARATIONS, never exposures: two exposures recording the same terminal
    // are ONE candidate. int adds no dedup of its own, so this pins its reliance
    // on the table keying exposures by canonical source, at the exposure shape
    // the unit layer can build. The genuinely distinct pair — a direct import
    // beside a re-export — is e2e evidence
    // (`repl_introspection::one_terminal_reached_two_ways_lists_once`).
    #[test]
    fn candidate_query_dedups_one_terminal_reached_two_ways() {
        let s = session();
        install_m(&s, None);
        expose_import(&s, "mf", "m", "mf");
        expose_import(&s, "mf", "m", "mf");
        assert_eq!(
            s.resolve_candidates("mf", SpecialFormTail::Consulted)
                .iter()
                .map(FQSymbol::to_string)
                .collect::<Vec<_>>(),
            vec!["m/mf".to_string()],
            "the terminal is one candidate however many exposures reach it"
        );
    }

    // spec: repl/spec.md §15.1 — a lookup is not a defining turn, whatever the
    // candidate count, so regeneration never fires on one.
    #[test]
    fn lookup_result_is_never_a_defining_turn() {
        let s = session();
        install_m(&s, None);
        expose_import(&s, "mf", "m", "mf");
        let result = s
            .check_bare_symbol_introspection(&Sexp::Symbol("mf".into(), Span::SYNTHETIC))
            .expect("an imported fn describes at lookup");
        assert!(!result.is_defining());
        assert_eq!(result.ty(), None);
    }

    // spec: repl/spec/03-slash-commands.md §3.8; spec/08-modules.md §8.4.6 — a
    // QUALIFIED spelling of a re-exported name resolves to its DEFINING
    // terminal, and the prompt and `/sig` answer from the same query. The raw
    // table probe the prompt used before missed here: a re-exporter holds a
    // candidate, not an entry, so the name fell through to the value path.
    #[test]
    fn qualified_reexport_resolves_to_its_terminal_on_both_surfaces() {
        let s = session();
        install_m(&s, Some("doc mf"));
        let r = ModuleFullPath::from("r");
        let mut table = SessionSymbolTable::new_with_params(r.clone());
        table
            .expose_candidate(
                Symbol::from("mf"),
                FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("mf"),
                },
                Visibility::Public,
            )
            .expect("re-export candidate fixture installs");
        s.shared.symbol_tables.insert(r, table);

        assert_eq!(
            s.resolve_candidates("r/mf", SpecialFormTail::Consulted)
                .iter()
                .map(FQSymbol::to_string)
                .collect::<Vec<_>>(),
            vec!["m/mf".to_string()],
            "§8.4.6 — a re-exported name is attributed to its defining module"
        );
        let lookup = s
            .check_bare_symbol_introspection(&Sexp::Symbol("r/mf".into(), Span::SYNTHETIC))
            .expect("a qualified re-exported name describes at the prompt");
        assert_eq!(
            s.handle_sig("r/mf"),
            s.format_eval_result(&lookup),
            "§3.8 — `/sig` is byte-identical to the prompt's line"
        );
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
        assert!(
            out.contains("(Fn ["),
            "the full signature must appear; got: {out}"
        );
    }
    // §3.8 (FIXME 0492): /sig on a bare LOCAL name renders the SAME
    // fully-qualified primary line the per-class display builder produces — not
    // the short unqualified `:(Fn [Int] Int) dbl` form the pre-fix bare-local
    // arm used. Asserted as byte-equality at the display seam so the two
    // surfaces cannot drift.
    #[test]
    fn handle_sig_bare_local_matches_format_def_entry_fully_qualified() {
        let s = session();
        let user = s.current_module_path();
        let entry = if let Some(mut table) = s.shared.symbol_tables.get_mut(&user) {
            install_userfn(&mut table, "dbl", Some("Multiply by 2"), Visibility::Public)
        } else {
            let mut table = SessionSymbolTable::new_with_params(user.clone());
            let entry =
                install_userfn(&mut table, "dbl", Some("Multiply by 2"), Visibility::Public);
            s.shared.symbol_tables.insert(user.clone(), table);
            entry
        };
        let sig = s.handle_sig("dbl");
        // `/sig` and the bare-value display share the ONE `format_def_entry`
        // (§3.8) — byte-equality holds by construction.
        let expected = s.format_def_entry(&entry, "dbl", &user);
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
        assert!(
            !out.contains("m/m/mf") && !out.contains("m/mf/mf"),
            "no double-qualification; got: {out}"
        );
    }
    // /imports lists a name imported from another module, in both the category
    // and the per-module view, and never the current module's own definition.
    // spec: repl/spec.md §3.4
    #[test]
    fn imports_lists_foreign_candidates_not_own_definitions() {
        let s = session();
        install_m(&s, None);
        {
            let mut table = s
                .shared
                .symbol_tables
                .get_mut(&s.current_module_path())
                .expect("current module table exists");
            let _ = install_userfn(&mut table, "localfn", None, Visibility::Public);
            table
                .expose_candidate(
                    Symbol::from("mf"),
                    FQSymbol {
                        module: ModuleFullPath::from("m"),
                        symbol: Symbol::from("mf"),
                    },
                    Visibility::Private,
                )
                .expect("import candidate");
        }
        let all = s.handle_imports("");
        assert!(all.contains("Fns") && all.contains("mf"), "got:\n{all}");
        assert!(!all.contains("localfn"), "own definition listed:\n{all}");
        let from_m = s.handle_imports("m");
        assert!(
            from_m.contains("From m") && from_m.contains("mf"),
            "got:\n{from_m}"
        );
        assert_eq!(
            s.handle_imports("user"),
            "",
            "own module is not an import source"
        );
    }
    // /doc on a module-qualified name resolves the symbol (not `unknown
    // symbol`). spec: §3.6 / §17.5.1
    #[test]
    fn handle_doc_accepts_fq_name() {
        let s = session();
        install_m(&s, Some("doc mf"));
        let out = s.handle_doc("m/mf");
        assert!(!out.contains("unknown symbol"), "got: {out}");
        assert!(
            out.contains("doc mf"),
            "the docstring must appear; got: {out}"
        );
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
        let _ = install_userfn(&mut table, "mf", None, Visibility::Public);
        // mg calls mf — the `callees` edge (serialized for cache-restored
        // modules) is present, but no introspection record exists.
        let _ = install_userfn_with_callees(
            &mut table,
            "mg",
            None,
            Visibility::Public,
            vec![FQSymbol {
                module: m.clone(),
                symbol: Symbol::from("mf"),
            }],
        );
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
        let _ = install_userfn(&mut table, "mf", None, Visibility::Public);
        // Base template `g` calls mf.
        let _ = install_userfn_with_callees(
            &mut table,
            "g",
            None,
            Visibility::Public,
            vec![FQSymbol {
                module: m.clone(),
                symbol: Symbol::from("mf"),
            }],
        );
        // A minted mono instance `g$Int` also calls mf — `ReverseIndex::build`
        // records the mangled name verbatim as a caller.
        let _ = install_userfn_with_callees(
            &mut table,
            "g$Int",
            None,
            Visibility::Public,
            vec![FQSymbol {
                module: m.clone(),
                symbol: Symbol::from("mf"),
            }],
        );
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

#[cfg(test)]
mod tests_for_filter_tests {
    use crate::repl::format::format_symbol_layout;
    use crate::repl::test_support::session;

    // spec: repl/spec/17-embedded-agent.md §17.6.2 — a test function has the
    // `test-` prefix and the §16.1 signature. The two referers differ only in
    // their scheme, so the exact output shows the exact-typed one is listed,
    // the mistyped one is not, and no warning text is added.
    #[test]
    fn tests_for_lists_only_referers_with_the_test_signature() {
        let mut s = session();
        for form in [
            "(import [primitives [*]])",
            "(defn f [x] (add-i64 x 1))",
            "(defn test-bad [] (f 1))",
            "(defn test-good [] (if (eq-i64 (f 1) 2) None (Some \"f 1 is not 2\")))",
        ] {
            s.eval(form)
                .unwrap_or_else(|e| panic!("fixture form `{form}` must compile: {e}"));
        }
        let expected = format!(
            "; tests referencing f\n{}",
            format_symbol_layout(&["user/test-good".to_string()]).join("\n")
        );
        assert_eq!(s.handle_tests_for("f"), expected);
    }
}
