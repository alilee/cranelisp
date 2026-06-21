// REPL experience — slash-command dispatch, prompt/banner formatting, the
// line-editor-facing entry points, and the introspection-display helpers
// (FIXME 0109 Wave D).
//
// Extracted from `session_v4.rs` per `design/int/int.md` §3.3. This is pure
// relocation: the `impl CompilerSession` methods moved here reach the session's
// (now `pub(crate)`) fields, and call the session-resident accessors via
// `crate::session_v4::*`. No behavioural change — including the known
// self-documentation defects (0338) which are fixed in place in a SEPARATE
// later deployment, not here.

use std::io::Write;

use cranelisp_types::{
    CranelispError, DefKind, ErrorLocation, FQSymbol, MacroClauseInfo,
    MacroParam, ModuleEntry, ModuleFullPath, OverloadVariant, Scheme, Sexp, Span, Symbol,
    TopLevel, TraitName, Type, TypeName,
};

use cranelisp_typecheck::CheckState;

use crate::code::{Code, SessionSymbolTable};
use crate::display::{format_result_value, format_scheme_display, format_type_qualified};
use crate::session_v4::{
    discover_test_names, intrinsic_type_from_name, is_comment_only, parens_balanced,
    run_test_by_name, CommandResult, CompilerSession, EvalResult, Introspection,
    ReadOnlyMacroResolver, SymbolCategory, SymbolDescription, TestOutcome,
};
use crate::worker::ModuleCompiler;

// ---------------------------------------------------------------------------
// Slash command types + top-level display free functions (relocated)
// ---------------------------------------------------------------------------

/// Parsed REPL slash command.
#[allow(dead_code)] // Not all variants dispatched yet — ported incrementally.
pub(crate) enum ReplCommand<'a> {
    Help,
    Quit,
    Sig(&'a str),
    Doc(&'a str),
    Type(&'a str),
    Info(&'a str),
    List(&'a str),
    Mem(&'a str),
    Time(&'a str),
    Expand(&'a str),
    Imports(&'a str),
    Exports(&'a str),
    Source(&'a str),
    SexpCmd(&'a str),
    Ast(&'a str),
    Clif(&'a str),
    Disasm(&'a str),
    Mod(&'a str),
    RunTests(&'a str),
    RunAllTests,
    /// `/platform-schema <name>` — print the compiler-generated schema artifact
    /// for a loaded platform (platform-interface.md §5.5.1 / §6.0). A thin
    /// caller of the backend schema generator over the loaded platform's tables.
    PlatformSchema(&'a str),
    Reset,
    Sh(&'a str),
    Unknown(&'a str),
}

/// Sentinel string returned by /quit to signal the REPL loop to exit.
pub const QUIT_SENTINEL: &str = "\x00QUIT";


/// Parse a slash command from trimmed input.
pub(crate) fn parse_slash_command(input: &str) -> Option<ReplCommand<'_>> {
    if !input.starts_with('/') {
        return None;
    }

    let (cmd, arg) = match input.split_once(char::is_whitespace) {
        Some((c, a)) => (c, a.trim()),
        None => (input, ""),
    };

    Some(match cmd {
        "/help" | "/h" => ReplCommand::Help,
        "/quit" | "/q" => ReplCommand::Quit,
        "/sig" | "/s" => ReplCommand::Sig(arg),
        "/doc" | "/d" => ReplCommand::Doc(arg),
        "/type" | "/t" => ReplCommand::Type(arg),
        "/info" | "/i" => ReplCommand::Info(arg),
        "/list" | "/l" => ReplCommand::List(arg),
        "/mem" | "/m" => ReplCommand::Mem(arg),
        "/time" => ReplCommand::Time(arg),
        "/expand" | "/e" => ReplCommand::Expand(arg),
        "/imports" => ReplCommand::Imports(arg),
        "/exports" => ReplCommand::Exports(arg),
        "/source" => ReplCommand::Source(arg),
        "/sexp" => ReplCommand::SexpCmd(arg),
        "/ast" => ReplCommand::Ast(arg),
        "/clif" => ReplCommand::Clif(arg),
        "/disasm" => ReplCommand::Disasm(arg),
        "/mod" => ReplCommand::Mod(arg),
        "/run-tests" | "/rt" => ReplCommand::RunTests(arg),
        "/run-all-tests" => ReplCommand::RunAllTests,
        "/platform-schema" => ReplCommand::PlatformSchema(arg),
        "/reset" => ReplCommand::Reset,
        "/sh" => ReplCommand::Sh(arg),
        _ => ReplCommand::Unknown(cmd),
    })
}

/// Print the /help command output to a writer.
pub(crate) fn print_help(stdout: &mut impl Write) {
    let _ = writeln!(stdout, "Available commands:");
    let _ = writeln!(stdout, "  /help (/h)          Show this help");
    let _ = writeln!(stdout, "  /quit (/q)          Exit REPL");
    let _ = writeln!(stdout, "  /sig (/s) NAME      Show type signature");
    let _ = writeln!(stdout, "  /doc (/d) NAME      Show docstring");
    let _ = writeln!(stdout, "  /type (/t) EXPR     Show type without evaluating");
    let _ = writeln!(stdout, "  /info (/i) NAME     Show full details");
    let _ = writeln!(stdout, "  /source NAME        Show original source text");
    let _ = writeln!(stdout, "  /sexp NAME          Show parsed S-expression");
    let _ = writeln!(stdout, "  /ast NAME           Show AST");
    let _ = writeln!(stdout, "  /clif NAME          Show Cranelift IR");
    let _ = writeln!(stdout, "  /disasm NAME        Show disassembled native code");
    let _ = writeln!(stdout, "  /list (/l) [FILTER] List symbols in current module");
    let _ = writeln!(stdout, "  /mem (/m) [EXPR]    Show allocation statistics (with delta if EXPR given)");
    let _ = writeln!(stdout, "  /time EXPR          Evaluate with timing breakdown");
    let _ = writeln!(stdout, "  /expand (/e) FORM   Macro-expand a form");
    let _ = writeln!(stdout, "  /imports [MODULE]   Show imports and special forms");
    let _ = writeln!(stdout, "  /exports MODULE     Show module's public symbols");
    let _ = writeln!(stdout, "  /mod [NAME]         Switch module namespace (default: user)");
    let _ = writeln!(stdout, "  /run-tests (/rt) [MOD]  Run test-* functions (current module or named)");
    let _ = writeln!(stdout, "  /run-all-tests      Run all tests in project modules");
    let _ = writeln!(stdout, "  /platform-schema NAME  Print the generated layout schema for a loaded platform");
    let _ = writeln!(stdout, "  /reset              Clear all state and reload prelude");
    let _ = writeln!(stdout, "  /sh <cmd>       Run a shell command");
}


/// Run a shell command with stdout/stderr passed through directly.
///
/// Uses `.status()` instead of `.output()` so the child process inherits
/// stdout/stderr from the REPL process. This ensures E2E test harnesses
/// (which capture subprocess stdout) see the shell command output.
pub(crate) fn run_shell_command(cmd: &str, stdout: &mut impl Write) {
    if cmd.is_empty() {
        let _ = writeln!(stdout, "Usage: /sh <command>");
        return;
    }
    match std::process::Command::new("sh")
        .arg("-c")
        .arg(cmd)
        .status()
    {
        Ok(status) => {
            if !status.success() {
                #[cfg(unix)]
                {
                    use std::os::unix::process::ExitStatusExt;
                    if let Some(sig) = status.signal() {
                        let _ = writeln!(stdout, "killed by signal: {sig}");
                        return;
                    }
                }
                if let Some(code) = status.code() {
                    let _ = writeln!(stdout, "exit status: {code}");
                }
            }
        }
        Err(e) => {
            let _ = writeln!(stdout, "error: {e}");
        }
    }
}

/// Format the `/mem` snapshot (no-expression form).
///
/// Reads the current allocation counters from `cranelisp-runtime` and
/// returns a two-line report: one data line with current live bytes, and
/// a comment line with total alloc / dealloc counts and the currently-live
/// allocation count (`allocs - deallocs`).
pub(crate) fn format_mem_snapshot() -> String {
    let allocs = cranelisp_intrinsics::alloc_count();
    let deallocs = cranelisp_intrinsics::dealloc_count();
    let bytes_live = cranelisp_intrinsics::bytes_current();
    let live = allocs.saturating_sub(deallocs);
    format!(
        "; live: {bytes_live} bytes ({live} allocations)\n; allocs: {allocs}  deallocs: {deallocs}"
    )
}

/// Format a module entry signature for /sig display.
pub(crate) fn format_entry_sig(entry: &ModuleEntry<Code>, name: &str) -> String {
    match entry {
        // S70 macro-unification / S69 Submission 35-36 (W-Absorb): constructors
        // and macros are now `Def` entries discriminated by `kind`; special
        // forms are their own `ModuleEntry::SpecialForm` variant.
        ModuleEntry::Def { scheme, kind, docstring, .. } => {
            match kind.as_ref() {
                DefKind::Overloaded { variants } if !variants.is_empty() => {
                    // Multi-sig: one line per variant per repl/spec.md §4.1.1.
                    format_overloaded_variants_bare(name, variants, docstring.as_deref())
                }
                DefKind::Constructor { type_name, .. } => {
                    format!(":{} {} ; constructor of {}", scheme.ty, name, type_name)
                }
                DefKind::Macro { clauses_meta, .. } => {
                    let arity = clauses_meta.first().map(|c| c.params.len()).unwrap_or(0);
                    format!(
                        "{name} ; defmacro ({} clause(s), arity {})",
                        clauses_meta.len(),
                        arity
                    )
                }
                _ => {
                    let classification = match kind.as_ref() {
                        DefKind::Overloaded { .. } => "defn (multi)",
                        _ => "defn",
                    };
                    let base = format!(":{} {} ; {}", scheme.ty, name, classification);
                    append_docstring_comment(base, docstring.as_deref())
                }
            }
        }
        ModuleEntry::SpecialForm { scheme, description, .. } => {
            format_special_form_display(name, scheme, description)
        }
        ModuleEntry::TypeDef { .. } => {
            format!("{name} ; deftype")
        }
        ModuleEntry::TraitDecl { info, .. } => {
            format!("{name} ; deftrait ({} method(s))", info.methods.len())
        }
        ModuleEntry::Import { source, .. } => {
            format!("{name} ; imported from {}/{}", source.module, source.symbol)
        }
        _ => name.to_string(),
    }
}

/// Format an overloaded (multi-sig) function as one line per variant, with
/// fully-qualified `module/name` per spec §4.1.1. Used by bare-symbol display
/// (`format_def_entry`).
///
/// First line carries the `; defn` classification + optional docstring; subsequent
/// variant lines carry only the type and qualified name. See repl/spec.md §1.3
/// + §4.1.1 and design/int/multi-sig-introspection.md.
pub(crate) fn format_overloaded_variants(
    name: &str,
    module: &ModuleFullPath,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
) -> String {
    let mut lines = Vec::with_capacity(variants.len());
    for (i, v) in variants.iter().enumerate() {
        let fn_ty = Type::Fn(v.param_types.clone(), Box::new(v.ret_type.clone()));
        let type_str = format_type_qualified(&fn_ty);
        let line = if i == 0 {
            let base = format!(":{type_str} {module}/{name} ; defn");
            append_docstring_comment(base, docstring)
        } else {
            format!(":{type_str} {module}/{name}")
        };
        lines.push(line);
    }
    lines.join("\n")
}

/// /sig variant of `format_overloaded_variants` — bare name (no module prefix)
/// to match the rest of `format_entry_sig`'s output. One line per variant.
pub(crate) fn format_overloaded_variants_bare(
    name: &str,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
) -> String {
    let mut lines = Vec::with_capacity(variants.len());
    for (i, v) in variants.iter().enumerate() {
        let fn_ty = Type::Fn(v.param_types.clone(), Box::new(v.ret_type.clone()));
        let type_str = format_type_qualified(&fn_ty);
        let line = if i == 0 {
            let base = format!(":{type_str} {name} ; defn");
            append_docstring_comment(base, docstring)
        } else {
            format!(":{type_str} {name}")
        };
        lines.push(line);
    }
    lines.join("\n")
}

impl CompilerSession {
    /// REPL `/info NAME` — one-shot description of a symbol resolved from
    /// `name` against the current REPL module. Returns the symbol's
    /// classification (Fn / Type / Trait / Macro / Constructor / SpecialForm),
    /// scheme (if applicable), docstring, and the captured source text.
    ///
    /// Pure read against `shared.symbol_tables` + `shared.introspection`.
    /// Returns `None` if the bare `name` does not resolve in the current
    /// module (no chain-follow performed at this layer — the caller may
    /// chain-follow if it wants imports + reexports resolved).
    pub fn describe_symbol(&self, name: &str) -> Option<SymbolDescription> {
        // Probe current module first, then the prelude outer-scope hop, then
        // root `""` (FIXME 0192 Residual Task 3 + FIXME 0193 — special-form
        // metadata lives at root, not in user-mode tables; S78 §2.7.6 — prelude
        // hop). Routes through the canonical `lookup_with_prelude_fallback`
        // (root tier ON) so the three-tier walk has a single definition
        // (S87 §4 dedup, Principle 7). The resolved module reflects where the
        // entry actually lives so the returned `FQSymbol` is correct.
        let (entry, resolved_module) = self.lookup_with_prelude_fallback(name)?;
        let fq = FQSymbol {
            module: resolved_module.clone(),
            symbol: Symbol::from(name),
        };
        let (category, scheme, docstring) = match &entry {
            ModuleEntry::Def { scheme, docstring, kind, .. } => {
                let cat = match kind.as_ref() {
                    DefKind::Constructor { .. } => SymbolCategory::Constructor,
                    DefKind::Macro { .. } => SymbolCategory::Macro,
                    _ => SymbolCategory::Fn,
                };
                (cat, Some(scheme.clone()), docstring.clone())
            }
            ModuleEntry::SpecialForm { scheme, docstring, .. } =>
                (SymbolCategory::SpecialForm, Some(scheme.clone()), docstring.clone()),
            ModuleEntry::TypeDef { .. } =>
                (SymbolCategory::Type, None, None),
            ModuleEntry::TraitDecl { docstring, .. } =>
                (SymbolCategory::Trait, None, docstring.clone()),
            _ => return None,
        };
        let source = self.shared.introspection.as_ref()
            .and_then(|m| m.get(&fq))
            .and_then(|intr| intr.source.clone());
        // FIXME 0194: populate `related` from the same cross-ref collectors the
        // universal-display paths (`format_type_display`/`format_trait_display`)
        // use, projected to `FQSymbol`s anchored at each referent's home module.
        let related = self.collect_related(&entry, &fq, &resolved_module);
        Some(SymbolDescription {
            fq,
            category,
            scheme,
            docstring,
            source,
            related,
        })
    }

    /// Collect the cross-reference `FQSymbol`s for `entry` (FIXME 0194).
    ///
    /// - **Type** (`TypeDef`, or a product ctor's type facet) → its constructor
    ///   FQs (the `; match:` arms), homed at the type's defining module.
    /// - **Trait** (`TraitDecl`) → its method-defn FQs (`; defn:`) homed at the
    ///   trait module, plus the implementing-type FQs (`; impl:`) each homed at
    ///   that type's defining module.
    /// - **Constructor** → its parent type's FQ (`; defn:`).
    ///
    /// Other kinds (plain fns, macros, special forms) have no structural
    /// cross-ref under §3.6 and return empty. Names that cannot be re-homed are
    /// skipped rather than emitted with a wrong module.
    pub(crate) fn collect_related(
        &self,
        entry: &ModuleEntry<crate::code::Code>,
        fq: &FQSymbol,
        resolved_module: &ModuleFullPath,
    ) -> Vec<FQSymbol> {
        collect_related_for(
            &self.shared.symbol_tables,
            &self.current_module_path(),
            entry,
            fq,
            resolved_module,
        )
    }

    // -- REPL eval and command dispatch (pipeline-v4.md §6) --

    /// Process REPL slash commands and blank/comment detection.
    ///
    /// Returns `Nothing` for blank/comment lines and side-effect commands,
    /// `Final` for commands that produce display output, `Compile` for
    /// source text that should be compiled via `eval()`.
    pub fn process_commands(&mut self, src: &str, stdout: &mut impl Write) -> CommandResult {
        let trimmed = src.trim();

        // Blank or comment-only.
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return CommandResult::Nothing;
        }

        // Slash commands.
        if let Some(cmd) = parse_slash_command(trimmed) {
            return self.dispatch_command(cmd, stdout);
        }

        // Special form feedback (bare special form names).
        if let Some(display) = self.special_form_feedback(trimmed) {
            return CommandResult::Final(display);
        }

        // Error blocking: refuse eval when modules have errors.
        if !self.error_modules.is_empty() {
            let names: Vec<String> = self.error_modules.iter()
                .map(|mp| mp.as_ref().to_string())
                .collect();
            let msg = format!(
                "Cannot evaluate: module '{}' has errors. Fix the source file and save.",
                names.join("', '"),
            );
            return CommandResult::Final(msg);
        }

        // Source text to compile.
        CommandResult::Compile(trimmed.to_string())
    }

    /// Dispatch a parsed slash command, returning a `CommandResult`.
    pub(crate) fn dispatch_command(
        &mut self,
        cmd: ReplCommand<'_>,
        stdout: &mut impl Write,
    ) -> CommandResult {
        match cmd {
            ReplCommand::Help => {
                print_help(stdout);
                CommandResult::Nothing
            }
            ReplCommand::Quit => {
                CommandResult::Quit
            }
            ReplCommand::Sig(name) => {
                let output = self.handle_sig(name);
                CommandResult::Final(output)
            }
            ReplCommand::Doc(name) => {
                let output = self.handle_doc(name);
                CommandResult::Final(output)
            }
            ReplCommand::List(filter) => {
                let output = self.handle_list(filter);
                CommandResult::Final(output)
            }
            ReplCommand::Mod(name) => {
                self.handle_mod(name);
                CommandResult::Nothing
            }
            ReplCommand::Source(name) => {
                CommandResult::Final(self.handle_source(name))
            }
            ReplCommand::SexpCmd(name) => {
                CommandResult::Final(self.handle_sexp_cmd(name))
            }
            ReplCommand::Ast(name) => {
                CommandResult::Final(self.handle_ast(name))
            }
            ReplCommand::Clif(name) => {
                CommandResult::Final(self.handle_clif(name))
            }
            ReplCommand::Disasm(name) => {
                CommandResult::Final(self.handle_disasm(name))
            }
            ReplCommand::Info(name) => {
                CommandResult::Final(self.handle_info(name))
            }
            ReplCommand::Type(expr) => {
                CommandResult::Final(self.handle_type(expr))
            }
            ReplCommand::Imports(filter) => {
                CommandResult::Final(self.handle_imports(filter))
            }
            ReplCommand::Exports(arg) => {
                CommandResult::Final(self.handle_exports(arg))
            }
            ReplCommand::Expand(form) => {
                CommandResult::Final(self.handle_expand(form))
            }
            ReplCommand::Time(expr) => {
                CommandResult::Final(self.handle_time(expr))
            }
            ReplCommand::Mem(expr) => {
                CommandResult::Final(self.handle_mem(expr))
            }
            ReplCommand::Sh(cmd) => {
                run_shell_command(cmd, stdout);
                CommandResult::Nothing
            }
            ReplCommand::Unknown(cmd) => {
                CommandResult::Final(format!(
                    "error: unknown command '{cmd}'. Type /help for available commands."
                ))
            }
            ReplCommand::RunTests(arg) => {
                CommandResult::Final(self.handle_run_tests(arg))
            }
            ReplCommand::RunAllTests => {
                CommandResult::Final(self.handle_run_all_tests())
            }
            ReplCommand::PlatformSchema(name) => {
                CommandResult::Final(self.handle_platform_schema(name))
            }
            ReplCommand::Reset => {
                // Clear file watcher state so stale watches don't persist.
                if let Some(ref mut w) = self.watcher {
                    w.clear_all();
                }
                self.error_modules.clear();
                CommandResult::Final("command not yet available in v4 REPL".to_string())
            }
        }
    }


    // -- Slash command handlers (subset for initial implementation) --

    /// /sig handler: show type signature of a symbol.
    /// S78 §2.7.6 — look up a bare name for introspection, honouring the
    /// prelude outer scope. Returns `(entry, lookup_module)` where
    /// `lookup_module` is the table the entry was found in (the current module,
    /// or `prelude` when the current table missed and the per-module fallback
    /// bit is ON). Used by `/sig`, `/doc` so prelude-provided bare names (e.g.
    /// `add-i64`) resolve even though prelude is no longer flattened into the
    /// current table.
    pub(crate) fn lookup_with_prelude_fallback(
        &self,
        name: &str,
    ) -> Option<(ModuleEntry<Code>, ModuleFullPath)> {
        self.lookup_with_prelude_fallback_opt(name, true)
    }

    /// Core of the prelude-fallback lookup (S87 §4 dedup, Principle 7).
    ///
    /// Walks current module → prelude (bit-gated, `current != prelude`) → root
    /// `""` and returns the first hit + the module it resolved in. The `root`
    /// flag controls the final tier:
    ///
    /// - `root: true` — also consult the root `""` table (special-form metadata
    ///   lives there). This is the canonical behaviour used by `/sig`, `/doc`,
    ///   `/info`, and `describe_symbol` (current → prelude → root).
    /// - `root: false` — stop after the prelude hop (current → prelude only, NO
    ///   root tier). This preserves `format_eval_result_body`'s two-tier walk:
    ///   a bare special-form name (`if`/`match`) must NOT resolve in the
    ///   eval-result value display — it falls through to the caller's `None`
    ///   arm. (The "let root resolve too" cleanup is deferred — see S87 §4.1.)
    pub(crate) fn lookup_with_prelude_fallback_opt(
        &self,
        name: &str,
        root: bool,
    ) -> Option<(ModuleEntry<Code>, ModuleFullPath)> {
        let module = self.current_module_path();
        if let Some(e) = self.current_symbol_table().get(name) {
            return Some((e.clone(), module));
        }
        let prelude_path = ModuleFullPath::from("prelude");
        // Prelude outer-scope hop (S78 §2.7) — a bare prelude-provided name not
        // in the current inner table resolves through prelude's own table when
        // the per-module fallback bit is ON.
        if module != prelude_path {
            let on = self
                .shared
                .prelude_fallback
                .get(&module)
                .map(|b| *b)
                .unwrap_or(false);
            if on
                && let Some(e) = self
                    .shared
                    .symbol_tables
                    .get(&prelude_path)
                    .and_then(|t| t.get(name).cloned())
            {
                return Some((e, prelude_path));
            }
        }
        if !root {
            return None;
        }
        // Root `""` tier — special-form metadata lives here (Principle 17
        // amendment, FIXME 0193). Falling back to root lets `/info`/`/sig`
        // resolve special forms (`if`/`match`/`trace`/…) instead of returning
        // `unknown symbol` (FIXME 0338). Always consulted — special forms are
        // global, independent of the prelude bit.
        let root_path = ModuleFullPath::from("");
        if module != root_path
            && let Some(e) = self
                .shared
                .symbol_tables
                .get(&root_path)
                .and_then(|t| t.get(name).cloned())
        {
            return Some((e, root_path));
        }
        None
    }

    pub(crate) fn handle_sig(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /sig <name>".to_string();
        }
        if intrinsic_type_from_name(name).is_some() {
            return format!("{name} ; type - builtin type");
        }
        match self.lookup_with_prelude_fallback(name) {
            Some((entry, _)) => format_entry_sig(&entry, name),
            None => format!("error: unknown symbol '{name}'"),
        }
    }

    /// /doc handler: show docstring of a symbol.
    pub(crate) fn handle_doc(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /doc <name>".to_string();
        }
        let Some((local, lookup_module)) = self.lookup_with_prelude_fallback(name) else {
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
            match entry {
                ModuleEntry::Def { kind, scheme, .. } => match kind.as_ref() {
                    DefKind::Macro { .. } => macros.push(format!("  {name}")),
                    // Constructors are part of their type — not listed
                    // separately.
                    DefKind::Constructor { .. } => {}
                    _ => {
                        // FIXME 0352: route through the same normalize +
                        // qualify renderer the definition-display / `/sig`
                        // paths use (Principle 7), NOT the raw `Type::Display`
                        // (which leaked internal `t1` vars and unqualified
                        // `Int`, violating repl/spec.md §1.4). One renderer
                        // closes both the `t1`→`a` and `Int`→`primitives/Int`
                        // leaks.
                        let type_str = crate::display::format_scheme_type(scheme);
                        fns.push(format!("  {name} : {type_str}"));
                    }
                },
                ModuleEntry::TypeDef { .. } => {
                    types.push(format!("  {name}"));
                }
                ModuleEntry::TraitDecl { .. } => {
                    traits.push(format!("  {name}"));
                }
                // SpecialForm, Import, Ambiguous: not listed (special forms +
                // imports are shown by /imports).
                _ => {}
            }
        }

        let mut parts = Vec::new();
        if !types.is_empty() {
            types.sort();
            parts.push(format!("Types:\n{}", types.join("\n")));
        }
        if !traits.is_empty() {
            traits.sort();
            parts.push(format!("Traits:\n{}", traits.join("\n")));
        }
        if !macros.is_empty() {
            macros.sort();
            parts.push(format!("Macros:\n{}", macros.join("\n")));
        }
        if !fns.is_empty() {
            fns.sort();
            parts.push(format!("Fns:\n{}", fns.join("\n")));
        }
        if parts.is_empty() {
            "(no definitions)".to_string()
        } else {
            parts.join("\n")
        }
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
        self.set_current_module(path);
    }

    /// Look up introspection data for a bare symbol name in the current module.
    pub(crate) fn get_introspection(&self, name: &str) -> Option<dashmap::mapref::one::Ref<'_, FQSymbol, Introspection>> {
        let fq = FQSymbol {
            module: self.current_module_path(),
            symbol: Symbol::from(name),
        };
        self.shared.introspection.as_ref().and_then(|m| m.get(&fq))
    }

    /// /source handler: show original source text of a definition.
    pub(crate) fn handle_source(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /source <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name) {
            if let Some(ref src) = intr.source {
                return format!("; source for {name}\n{}", crate::pretty::pretty_print_str(src));
            }
            if let Some(ref sexp) = intr.sexp {
                return format!("; source for {name}\n{}", crate::pretty::pretty_print(sexp));
            }
        }
        format!("Error: no source available for '{name}'")
    }

    /// /sexp handler: show parsed S-expression of a definition.
    pub(crate) fn handle_sexp_cmd(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /sexp <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref sexp) = intr.sexp {
                return format!("; sexp for {name}\n{}", crate::pretty::pretty_print(sexp));
            }
        format!("Error: no sexp available for '{name}'")
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
        format!("Error: no AST available for '{name}'")
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
        format!("Error: no CLIF IR available for '{name}'")
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
            return format!("Error: no disassembly available for '{name}'");
        };
        match cranelisp_backend::produce_disasm(&fq, code_size, &self.shared.symbol_tables) {
            Ok(text) => format!("; disasm for {name}\n{text}"),
            Err(_) => format!("Error: no disassembly available for '{name}'"),
        }
    }

    /// /info handler: show full details (sig + code size + compile time).
    pub(crate) fn handle_info(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /info <name>".to_string();
        }
        if intrinsic_type_from_name(name).is_some() {
            return self.format_builtin_type_display(name);
        }
        let (entry, lookup_module) = match self.lookup_with_prelude_fallback(name) {
            Some(pair) => pair,
            None => return format!("error: unknown symbol '{name}'"),
        };
        let (resolved_entry, resolved_module) =
            self.resolve_entry_for_display(&entry, &lookup_module);
        let sig = self.format_def_entry(&resolved_entry, name, &resolved_module);
        // Append code info if available.
        let is_macro = matches!(&resolved_entry,
            ModuleEntry::Def { kind, .. } if matches!(kind.as_ref(), DefKind::Macro { .. }));
        if !is_macro
            && !matches!(resolved_entry, ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. })
            && let Some(intr) = self.get_introspection(name) {
                let size_str = intr.code_size
                    .map(|s| format!("{s} bytes"))
                    .unwrap_or_else(|| "? bytes".to_string());
                return format!("{sig}\n  {size_str}");
            }
        sig
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
            Err(e) => format!("Error: {e}"),
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
                output.push_str(
                    "Prelude (implicit):  \
                     ; available via the prelude outer scope, \
                     shadowed by any explicit import/def of the same name\n",
                );
                for name in &prelude_names {
                    output.push_str("  ");
                    output.push_str(name);
                    output.push('\n');
                }
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
            if name.contains('$') {
                continue;
            }
            if !prefix_filter.is_empty()
                && !name.to_lowercase().starts_with(&prefix_filter.to_lowercase())
            {
                continue;
            }
            match entry {
                ModuleEntry::Def { kind, .. } if matches!(kind.as_ref(), DefKind::Macro { .. }) => {
                    macros.push(name)
                }
                ModuleEntry::Def { kind, .. }
                    if matches!(kind.as_ref(), DefKind::Constructor { .. }) =>
                {
                    types.push(name)
                }
                ModuleEntry::TraitDecl { .. } => traits.push(name),
                ModuleEntry::TypeDef { .. } => types.push(name),
                ModuleEntry::Def { .. } => fns.push(name),
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
            return format!("Error: {e}");
        }
        match self.expand_form_sexp(form_src) {
            Ok(expanded) => format_sexp(&expanded),
            Err(e) => format!("Error: {e}"),
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
        crate::expander::expand_sexp_recursive(sexp, &mut resolver, 0)
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
            Err(e) => format!("Error: {e}"),
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
            Err(e) => format!("Error: {e}"),
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

    /// Check if input is a bare special form name (for feedback display).
    ///
    /// Sprint 67 hack-back (FIXME 0192 Residual Task 3 — REPL regression):
    /// special-form metadata lives in the root `""` module per Principle 17
    /// amendment (FIXME 0193). The earlier `current_symbol_table()` probe
    /// stopped seeing these entries when special forms moved out of `user`;
    /// route lookups via `lookup_special_form` which probes root.
    pub(crate) fn special_form_feedback(&self, input: &str) -> Option<String> {
        let trimmed = input.trim();
        // Must be a single bare word (no parens, no spaces).
        if trimmed.contains('(') || trimmed.contains(' ') || trimmed.starts_with('/') {
            return None;
        }
        let (scheme, desc) = self.lookup_special_form(trimmed)?;
        Some(format_special_form_display(trimmed, &scheme, &desc))
    }

    /// Look up a special form by name, probing the root `""` module where
    /// special-form metadata is registered (Principle 17 amendment per FIXME
    /// 0193). Returns the form's `(scheme, description)` — the scheme is the
    /// single source for the `:Type` prefix (FIXME 0338). `None` if `name` is
    /// not a known special form.
    pub fn lookup_special_form(&self, name: &str) -> Option<(Scheme, String)> {
        let root = ModuleFullPath::from("");
        let table = self.shared.symbol_tables.get(&root)?;
        match table.get(name)? {
            ModuleEntry::SpecialForm { scheme, description, .. } => {
                Some((scheme.clone(), description.clone()))
            }
            _ => None,
        }
    }

    // -- REPL display utilities (pipeline-v4.md §6) --

    /// Print the session banner.
    pub fn print_banner(&self, stdout: &mut impl Write) {
        let _ = writeln!(stdout, "cranelisp REPL — type /help for help");
    }

    /// Current module name for prompt display.
    pub fn current_module_name(&self) -> String {
        self.current_module_path().to_string()
    }

    /// Write the REPL prompt with timing info.
    /// Format: `{compile_ms}+{eval_ms}ms; {module}> `
    pub fn write_prompt(&self, stdout: &mut impl Write, compile_ms: u64, eval_ms: u64) {
        let module = self.current_module_name();
        let _ = write!(stdout, "{compile_ms}+{eval_ms}ms; {module}> ");
        let _ = stdout.flush();
    }

    /// Write the continuation prompt (for multi-line input).
    pub fn write_continuation_prompt(&self, stdout: &mut impl Write, compile_ms: u64, eval_ms: u64) {
        let module = self.current_module_name();
        let prompt_len = format!("{compile_ms}+{eval_ms}ms; {module}> ").len();
        let _ = write!(stdout, "{:>width$}", "...", width = prompt_len);
        let _ = stdout.flush();
    }

    /// Check if input has balanced parentheses.
    pub fn parens_balanced(&self, input: &str) -> bool {
        parens_balanced(input)
    }

    /// Pretty-print a form (eval result string) to stdout.
    pub fn pretty_print(&self, form: &str, stdout: &mut impl Write) {
        let _ = writeln!(stdout, "{form}");
    }

    /// §9: Format an eval result for display.
    ///
    /// Produces the universal output format (spec §1.1):
    ///   `:Type {value|name} ; {classification} - {docstring}`
    pub fn format_eval_result(&self, result: &EvalResult) -> String {
        // S83 W2 (FIXME 0363): surface accumulated typecheck `Warning`s in the
        // REPL output. Warnings are DATA accumulated through the eval chain
        // (`src/CLAUDE.md` §Error Handling: "displayed by the binary crate"),
        // but no display site existed — so a `ShadowedName` warning (e.g. a
        // synthesised §5.2.6 accessor colliding with an existing binding) was
        // invisible. Render each as a `; warning: <message>` comment line
        // (the §1.1 comment style) ahead of the value/def display. Doing it
        // here is the single source of truth: every `format_eval_result`
        // caller (REPL loop + `--run` echo + bare-symbol introspection) gets
        // warning display uniformly.
        let body = self.format_eval_result_body(result);
        if result.warnings().is_empty() {
            return body;
        }
        let mut out = String::new();
        for w in result.warnings() {
            out.push_str("; warning: ");
            out.push_str(&w.message);
            out.push('\n');
        }
        out.push_str(&body);
        out
    }

    /// The value/definition rendering for an `EvalResult`, without warning
    /// surfacing. `format_eval_result` wraps this to prepend `; warning:`
    /// lines (FIXME 0363).
    fn format_eval_result_body(&self, result: &EvalResult) -> String {
        match result {
            EvalResult::Def { symbol, .. } => {
                let name = symbol.symbol.as_ref();
                let module = &symbol.module;

                // Builtin type names (Int, Bool, etc.) from primitives module.
                if module.as_ref() == "primitives" && intrinsic_type_from_name(name).is_some() {
                    return self.format_builtin_type_display(name);
                }

                let cur_module = self.current_module_path();
                // S78 §2.7.6 — prelude outer-scope hop. A bare prelude-provided
                // name (e.g. `add-i64`) is no longer flattened into the current
                // table; when the per-module fallback bit is ON, look it up in
                // prelude's own table (the `(export …)` re-export edge) so the
                // chain-follow below still reaches `primitives/add-i64`. Routes
                // through the canonical helper with `root: false` (S87 §4 dedup,
                // Principle 7) — the NO-root-tier walk is deliberate: a bare
                // special-form name must NOT resolve here (it falls through to
                // the `None` arm below); the root cleanup is deferred (§4.1).
                let (entry, lookup_module) =
                    match self.lookup_with_prelude_fallback_opt(name, false) {
                        Some((e, m)) => (Some(e), m),
                        None => (None, cur_module.clone()),
                    };
                // Follow import chains to the definition.
                let (entry, resolved_module) = match entry {
                    Some(ref e) => self.resolve_entry_for_display(e, &lookup_module),
                    None => {
                        // TraitImpl entries have `Trait.Type` names; not in symbol table.
                        if let Some((trait_name, target_type)) = name.split_once('.') {
                            return format!(
                                "impl {module}/{trait_name} for {module}/{target_type}"
                            );
                        }
                        return format!("{symbol} ; defined");
                    }
                };
                self.format_def_entry(&entry, name, &resolved_module)
            }
            EvalResult::Val { value, ty, .. } => {
                if ty.is_io() {
                    // Defensive path. In normal REPL flow `compile_and_execute_expr`
                    // has already run the trampoline and stripped the IO type via
                    // `unwrap_io_inline`, so this branch is unreachable for current
                    // callers. If a future caller ever constructs `EvalResult::Val`
                    // with an un-trampolined IO value, we must still honour
                    // Decision 24's consuming convention: `run_io_trampoline` is
                    // non-consuming, so `consume_io_tree` must release the outer
                    // tree afterwards. See `pipeline::unwrap_io_inline`.
                    let inner_value = cranelisp_intrinsics::run_io_trampoline(*value);
                    cranelisp_intrinsics::drop::consume_io_tree(*value);
                    let inner_type = ty.unwrap_io().clone();
                    format_result_value(
                        inner_value, &inner_type, &self.shared.symbol_tables,
                    )
                } else {
                    format_result_value(
                        *value, ty, &self.shared.symbol_tables,
                    )
                }
            }
        }
    }

    /// Format a definition entry with its classification (spec §1.1, §4.1).
    pub(crate) fn format_def_entry(
        &self,
        entry: &ModuleEntry<Code>,
        name: &str,
        module: &ModuleFullPath,
    ) -> String {
        match entry {
            ModuleEntry::Def { scheme, kind, docstring, .. } => {
                match kind.as_ref() {
                    // Multi-sig: emit one line per variant per repl/spec.md
                    // §1.3 + §4.1.1.
                    DefKind::Overloaded { variants } if !variants.is_empty() => {
                        return format_overloaded_variants(
                            name, module, variants, docstring.as_deref(),
                        );
                    }
                    DefKind::Constructor { type_name, type_def, .. } => {
                        let type_str = format_type_qualified(&scheme.ty);
                        let tn = TypeName::from(type_name.name.as_ref());
                        // Resolve the type's `TypeDefInfo` so `format_ctor_display`
                        // can suppress the redundant `Type.Ctor` dot for a
                        // single-ctor product (`Point`, not `Point.Point`). A
                        // single-ctor product type's `name` key is THIS ctor `Def`
                        // (type-name == ctor-name; FIXME 0319), so `type_def` on
                        // `kind` is the authoritative facet — prefer it; fall back
                        // to the chain lookup for sum/enum ctors whose type is a
                        // separate `TypeDef` entry. Reaching the spurious
                        // `{type_name}.{name}` branch (e.g. `user/Point.Point`,
                        // which the outer `{module}/` then double-qualifies to
                        // `user/user/Point.Point`) is the Root-C defect (FIXME 0321).
                        let ctor_display = {
                            let info = type_def.as_deref().cloned().or_else(|| {
                                let scope = self.current_module_path();
                                cranelisp_types::lookup_type_def_chain(
                                    &self.shared.symbol_tables, &scope, &tn,
                                )
                            });
                            match info {
                                Some(info) => crate::display::format_ctor_display(&tn, name, &info),
                                None => format!("{tn}.{name}"),
                            }
                        };
                        return format!(":{type_str} {module}/{ctor_display} ; deftype");
                    }
                    DefKind::Macro { clauses_meta, .. } => {
                        return format_macro_display(
                            name, clauses_meta, docstring.as_deref(), module,
                        );
                    }
                    _ => {}
                }
                // FIXME 0352 (Principle 7): both the constrained and
                // unconstrained arms render the scheme type through the single
                // `format_scheme_type` renderer (`format_scheme_display` is the
                // thin `:type module/name` wrapper around it).
                let base = format_scheme_display(name, scheme, module);
                let is_primitive = matches!(kind.as_ref(), DefKind::Primitive { .. });
                let classification = if is_primitive { "primitive" } else { "defn" };
                let base = format!("{base} ; {classification}");
                // FIXME 0308: primitive entries now carry their Appendix A.5
                // description on `PrimitiveDef.docstring`; read it through the
                // entry's `docstring` field directly (the parallel
                // `builtin_docs` table is retired), satisfying the §A.5 MUST +
                // the §1.1 `; primitive - <doc>` format.
                append_docstring_comment(base, docstring.as_deref())
            }
            ModuleEntry::SpecialForm { scheme, description, .. } => {
                format_special_form_display(name, scheme, description)
            }
            ModuleEntry::TypeDef { .. } => {
                self.format_type_display(name, module)
            }
            ModuleEntry::TraitDecl { docstring, .. } => {
                self.format_trait_display(name, docstring.as_deref())
            }
            _ => {
                // TraitImpl entries have `Trait.Type` symbol names and
                // aren't stored in the symbol table as named entries.
                if let Some((trait_name, target_type)) = name.split_once('.') {
                    format!("impl {module}/{trait_name} for {module}/{target_type}")
                } else {
                    format!("{module}/{name} ; defined")
                }
            }
        }
    }

    /// Resolve Import/Reexport chains to the underlying definition entry.
    ///
    /// Walks the full chain (user → prelude → primitives → …) so that
    /// bare-value, introspection, and call paths converge on the same
    /// terminal `ModuleEntry::Def` regardless of how many re-exports sit
    /// between the current module and the defining module. Depth-limited
    /// to match the typechecker's `resolve_to_terminal_entry_owned`
    /// (spec §8.6.2 IMPORT_CHAIN_DEPTH_LIMIT). On cycle / depth exhaustion
    /// or a broken link, falls back to the last successfully resolved
    /// entry + module.
    ///
    /// Fix site for Sprint 61 Slice 1 Defect 4 (bare-primitive-name
    /// invisibility). See `design/int/bare-primitive-value-path.md`
    /// candidate 2 — the match arms in `check_bare_symbol_introspection`
    /// do not cover `Import`/`Reexport`, and the prior one-hop resolver
    /// could terminate on a `Reexport` intermediate (user → prelude →
    /// primitives), causing the bare-value path to fall through while
    /// the call and introspection paths resolved via their own recursive
    /// walks. Aligning on a single recursive resolver closes the
    /// divergence.
    pub(crate) fn resolve_entry_for_display(
        &self,
        entry: &ModuleEntry<Code>,
        current_module: &ModuleFullPath,
    ) -> (ModuleEntry<Code>, ModuleFullPath) {
        const MAX_DEPTH: usize = 32;
        let mut cur_entry = entry.clone();
        let mut cur_module = current_module.clone();
        for _ in 0..MAX_DEPTH {
            match &cur_entry {
                ModuleEntry::Import { source, .. } => {
                    match self.shared.symbol_tables.get(&source.module) {
                        Some(module_table) => {
                            match module_table.get(source.symbol.as_ref()) {
                                Some(resolved) => {
                                    let next = resolved.clone();
                                    cur_module = source.module.clone();
                                    cur_entry = next;
                                    continue;
                                }
                                None => return (cur_entry, cur_module),
                            }
                        }
                        None => return (cur_entry, cur_module),
                    }
                }
                _ => return (cur_entry, cur_module),
            }
        }
        // Depth exhausted — return the last resolved entry/module.
        (cur_entry, cur_module)
    }

    /// Format a user-defined type for display (spec §4.1.3).
    ///
    /// Shows `:module/TypeName ; deftype` with `; match:` and `; impl:` sections.
    pub(crate) fn format_type_display(&self, type_name: &str, module: &ModuleFullPath) -> String {
        let mut result = format!(":{module}/{type_name} ; deftype");
        let tn = TypeName::from(type_name);
        let scope = self.current_module_path();
        // FIXME 0192 method 2: `get_type_constructors` deleted; inline the
        // 1-line wrapper over the relocated `lookup_type_def_chain`.
        if let Some(info) = cranelisp_types::lookup_type_def_chain(
            &self.shared.symbol_tables, &scope, &tn,
        ) && !info.constructors.is_empty() {
            // `TypeDefInfo.constructors` is now `Vec<Symbol>` (S70 — the
            // `ConstructorInfo` struct retired; ctor metadata lives on each
            // ctor's `DefKind::Constructor` entry).
            let names: Vec<&str> = info.constructors.iter().map(|c| c.as_ref()).collect();
            result.push_str(&format_related_section("match", &names));
        }
        let trait_names = cranelisp_types::get_impls_for_type_chain(
            &self.shared.symbol_tables, &scope, &tn,
        );
        if !trait_names.is_empty() {
            let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
            result.push_str(&format_related_section("impl", &names));
        }
        result
    }

    /// Format a trait for display (spec §4.1.4).
    ///
    /// Shows `:module/TraitName ; deftrait` with `; defn:` and `; impl:` sections.
    pub(crate) fn format_trait_display(&self, trait_name: &str, docstring: Option<&str>) -> String {
        let scope = self.current_module_path();
        // FIXME 0192 method 6: `defining_module_for` deleted; substitute with
        // the chain-follow from `resolve_terminal_entry_and_home` (Decision 45
        // Pattern B). If the trait isn't reachable, fall back to the scope —
        // the display layer treats unresolved chains as defined-here for
        // diagnostic continuity (no architectural workaround; just a display
        // fallback).
        let defining_module = match cranelisp_types::resolve_terminal_entry_and_home(
            &self.shared.symbol_tables, &scope, trait_name,
        ) {
            Some((ModuleEntry::TraitDecl { .. }, home)) => home,
            _ => scope.clone(),
        };
        let tn = TraitName::from(trait_name);
        let mut result = format!(":{defining_module}/{trait_name} ; deftrait");
        result = append_docstring_comment(result, docstring);
        // FIXME 0192 method 4: `get_trait_methods` deleted; inline the 1-line
        // wrapper over `lookup_trait_decl_chain`.
        if let Some(decl) = cranelisp_types::lookup_trait_decl_chain(
            &self.shared.symbol_tables, &scope, &tn,
        ) && !decl.methods.is_empty() {
            let names: Vec<&str> = decl.methods.iter().map(|m| m.name.as_ref()).collect();
            result.push_str(&format_related_section("defn", &names));
        }
        let impl_types = cranelisp_types::get_implementing_types_chain(
            &self.shared.symbol_tables, &scope, &tn,
        );
        if !impl_types.is_empty() {
            let names: Vec<&str> = impl_types.iter().map(|t| t.as_ref()).collect();
            result.push_str(&format_related_section("impl", &names));
        }
        result
    }

    /// Format a builtin type (Int, Bool, Float, String) for display (spec §4.1.3).
    pub(crate) fn format_builtin_type_display(&self, type_name: &str) -> String {
        let tn = TypeName::from(type_name);
        let scope = self.current_module_path();
        let mut result = format!(":primitives/{type_name} ; type");
        let trait_names = cranelisp_types::get_impls_for_type_chain(
            &self.shared.symbol_tables, &scope, &tn,
        );
        if !trait_names.is_empty() {
            let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
            result.push_str(&format_related_section("impl", &names));
        }
        result
    }
}

/// Free-function core of [`CompilerSession::collect_related`] (FIXME 0194),
/// taking the symbol tables + resolution scope explicitly so the cross-ref
/// projection is unit-testable without constructing a full `CompilerSession`
/// (`src/CLAUDE.md` testability discipline; mirrors the `worker::layout_hash_gate`
/// / `splice_inline_mod_to_bare` extractions). See the method docstring for the
/// per-category cross-ref rules.
pub(crate) fn collect_related_for(
    tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    scope: &ModuleFullPath,
    entry: &ModuleEntry<crate::code::Code>,
    fq: &FQSymbol,
    resolved_module: &ModuleFullPath,
) -> Vec<FQSymbol> {
    let mut related: Vec<FQSymbol> = Vec::new();
    // Helper: resolve a bare name to its home module (chain-follow); skip if
    // unreachable.
    let fq_at_home = |name: &str| -> Option<FQSymbol> {
        cranelisp_types::resolve_terminal_entry_and_home(tables, scope, name).map(
            |(_, home)| FQSymbol { module: home, symbol: Symbol::from(name) },
        )
    };
    match entry {
        // A `TypeDef` is a type → its constructors are the match arms.
        ModuleEntry::TypeDef { info, .. } => {
                for ctor in &info.constructors {
                    related.push(FQSymbol {
                        module: resolved_module.clone(),
                        symbol: ctor.clone(),
                    });
                }
            }
            // A `Constructor` Def → its parent type (defn-related). A product
            // ctor additionally carries the type facet's constructors.
            ModuleEntry::Def { kind, .. } => {
                if let DefKind::Constructor { type_name, type_def, .. } = kind.as_ref() {
                    related.push(FQSymbol {
                        module: type_name.module.clone(),
                        symbol: Symbol::from(type_name.name.as_ref()),
                    });
                    if let Some(td) = type_def {
                        for ctor in &td.constructors {
                            related.push(FQSymbol {
                                module: resolved_module.clone(),
                                symbol: ctor.clone(),
                            });
                        }
                    }
                }
            }
            // A `TraitDecl` → its method defns + its implementing types.
            ModuleEntry::TraitDecl { .. } => {
                let tn = TraitName::from(fq.symbol.as_ref());
                if let Some(decl) = cranelisp_types::lookup_trait_decl_chain(tables, scope, &tn) {
                    for m in &decl.methods {
                        related.push(FQSymbol {
                            module: resolved_module.clone(),
                            symbol: m.name.clone(),
                        });
                    }
                }
                for ty in cranelisp_types::get_implementing_types_chain(tables, scope, &tn) {
                    if let Some(fq) = fq_at_home(ty.as_ref()) {
                        related.push(fq);
                    }
                }
            }
            _ => {}
        }
        related
}

// =============================================================================
// Display formatting helpers (ported from repl/commands.rs)
// =============================================================================

/// Format a special form for display (spec §4.1.5).
///
/// The `:Type` prefix is rendered from the SpecialForm entry's own `scheme`
/// (the SINGLE SOURCE — registered in `bootstrap::register_special_forms`),
/// retiring the former hardcoded `match name { … }` sig table (FIXME 0338,
/// Principle 7). A scheme whose top type is a `Fn` produces the prefix; any
/// other shape (defensive — should not occur for a registered form) omits it.
pub(crate) fn format_special_form_display(
    name: &str,
    scheme: &Scheme,
    description: &str,
) -> String {
    if matches!(scheme.ty, Type::Fn(..)) {
        let type_str = format_type_qualified(&scheme.ty);
        format!(":{type_str} {name} ; special form - {description}")
    } else {
        format!("{name} ; special form - {description}")
    }
}

/// Format a macro for display (spec §4.1.6).
pub(crate) fn format_macro_display(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> String {
    let mut result = format!(":{module}/{name} ; defmacro");
    result = append_docstring_comment(result, docstring);
    for clause in clauses {
        let params = format_macro_clause_params(clause);
        result.push_str(&format!("\n; {params} -> Sexp"));
    }
    // repl/spec.md §11.2.2: a multi-clause macro card ends with a clause-count
    // summary line (two leading spaces, no `;`). The single-clause worked
    // example (`/info when`) shows NO count line, so gate on `> 1`. The count
    // is always >= 2 under this gate, so a fixed "clauses" is correct.
    if clauses.len() > 1 {
        result.push_str(&format!("\n  {} clauses", clauses.len()));
    }
    result
}

/// Format macro clause parameters as `[param1 param2 ...]`.
pub(crate) fn format_macro_clause_params(clause: &MacroClauseInfo) -> String {
    let mut parts = Vec::new();
    for param in &clause.params {
        match param {
            MacroParam::Name(name) => parts.push(name.to_string()),
            MacroParam::Bracket { fixed, rest } => {
                let mut inner: Vec<String> = fixed.iter().map(|f| f.to_string()).collect();
                if let Some(r) = rest {
                    inner.push(format!("& {r}"));
                }
                parts.push(format!("[{}]", inner.join(" ")));
            }
        }
    }
    if let Some(rest) = &clause.rest_param {
        parts.push(format!("& {rest}"));
    }
    format!("[{}]", parts.join(" "))
}

/// Format a related symbols section (spec §1.1).
pub(crate) fn format_related_section(label: &str, names: &[&str]) -> String {
    format!("\n; {label}:\n;  {}", names.join(" "))
}

/// Classification of an imported symbol for category-based display.
pub(crate) enum ImportClass {
    Macro,
    Trait,
    Type,
    Constructor,
    Fn,
}

/// Append a category of names to a string buffer (for /list, /imports, /exports).
pub(crate) fn append_name_category(buf: &mut String, label: &str, names: &[String]) {
    if names.is_empty() {
        return;
    }
    buf.push_str(label);
    buf.push_str(":\n");
    for name in names {
        buf.push_str("  ");
        buf.push_str(name);
        buf.push('\n');
    }
}

/// Format a Sexp value as a readable string.
pub(crate) fn format_sexp(sexp: &Sexp) -> String {
    match sexp {
        Sexp::Symbol(name, _) => name.clone(),
        Sexp::Int(n, _) => format!("{n}"),
        Sexp::Float(v, _) => {
            let s = format!("{v}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Sexp::Bool(b, _) => format!("{b}"),
        Sexp::Str(s, _) => format!("\"{s}\""),
        Sexp::List(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("({})", parts.join(" "))
        }
        Sexp::Bracket(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("[{}]", parts.join(" "))
        }
        Sexp::Comment(text, _) => {
            if text.is_empty() {
                ";".to_string()
            } else {
                format!("; {text}")
            }
        }
    }
}

/// Append docstring as a comment suffix.
pub(crate) fn append_docstring_comment(base: String, docstring: Option<&str>) -> String {
    match docstring {
        Some(doc) if !doc.is_empty() => {
            let first_line = doc.lines().next().unwrap_or("");
            if first_line.is_empty() {
                base
            } else {
                format!("{base} - {first_line}")
            }
        }
        _ => base,
    }
}

// ==============================================================================
// Tests migrated with their code from session_v4.rs (FIXME 0109 Wave D)
// ==============================================================================

#[cfg(test)]
mod collect_related_tests {
    use super::*;
    use cranelisp_types::{
        FQTypeName, ModuleFullPath, Scheme, TypeDefInfo, TypeName, Visibility,
    };
    use std::collections::HashMap;

    fn tables() -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        dashmap::DashMap::new()
    }

    fn ensure(tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>, path: &str) {
        let p = ModuleFullPath::from(path);
        tables
            .entry(p.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(p));
    }

    fn fq(module: &str, symbol: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(symbol),
        }
    }

    // spec: repl/spec.md §3.6 — `SymbolDescription.related` (FIXME 0194). A TYPE
    // symbol's related set is its constructors, homed at the type's defining
    // module. Before SW-C `related` was stubbed empty; this pins the population.
    #[test]
    fn related_populated_for_type_lists_its_constructors() {
        let tables = tables();
        ensure(&tables, "user");
        let user = ModuleFullPath::from("user");

        // (deftype Color [Red Green]) — a sum type with two nullary ctors.
        let type_entry = ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: FQTypeName::new(user.clone(), TypeName::from("Color")),
                type_params: vec![],
                constructors: vec![Symbol::from("Red"), Symbol::from("Green")],
            },
            visibility: Visibility::Public,
            docstring: None,
        };

        let related = collect_related_for(&tables, &user, &type_entry, &fq("user", "Color"), &user);

        assert!(
            related.contains(&fq("user", "Red")) && related.contains(&fq("user", "Green")),
            "a type's `related` MUST list its constructors homed at the type's \
             module (spec §3.6); got {related:?}",
        );
        assert!(
            !related.is_empty(),
            "`related` MUST NOT be the empty stub it was before FIXME 0194",
        );
    }

    // spec: repl/spec.md §3.6 — a CONSTRUCTOR's related set names its parent
    // type, homed at the type's defining module.
    #[test]
    fn related_populated_for_constructor_names_its_type() {
        let tables = tables();
        ensure(&tables, "user");
        let user = ModuleFullPath::from("user");

        let ctor_entry = ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::ADT(
                    FQTypeName::new(user.clone(), TypeName::from("Color")),
                    vec![],
                ),
            },
            DefKind::Constructor {
                got_slot: 0,
                type_name: FQTypeName::new(user.clone(), TypeName::from("Color")),
                type_def: None,
                tag: 0,
                field_count: 0,
                internal: false,
            },
        )
        .visibility(Visibility::Public)
        .build();

        let related = collect_related_for(&tables, &user, &ctor_entry, &fq("user", "Red"), &user);

        assert!(
            related.contains(&fq("user", "Color")),
            "a constructor's `related` MUST name its parent type (spec §3.6); \
             got {related:?}",
        );
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
// Sprint 58 Wave 4 Step 5d (ii): multi-sig REPL bare-symbol display.
// spec: repl/spec.md §1.3 + §4.1.1 — overloaded fn shows all variant
// signatures, one per line.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod overloaded_display_tests {
    use super::*;

    fn variant(params: Vec<Type>, ret: Type, mangled: &str) -> OverloadVariant {
        OverloadVariant {
            param_types: params,
            ret_type: ret,
            mangled_name: Symbol::from(mangled),
        }
    }

    // spec: repl/spec.md §1.3 + §4.1.1 — multi-sig display emits ≥2 lines.
    #[test]
    fn overloaded_display_emits_one_line_per_variant() {
        let module = ModuleFullPath::from("user");
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants("pick", &module, &variants, None);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(
            lines.len(),
            2,
            "two variants must produce two lines, got: {out}"
        );
        // Both lines mention the qualified name.
        for line in &lines {
            assert!(
                line.contains("user/pick"),
                "each variant line must include qualified name, got: {line}"
            );
        }
        // First variant's parameter shape: `[primitives/Int]`.
        assert!(
            lines[0].contains("[primitives/Int]"),
            "first line must show 1-arg signature, got: {}",
            lines[0]
        );
        // Second variant's parameter shape: `[primitives/Int primitives/Int]`.
        assert!(
            lines[1].contains("[primitives/Int primitives/Int]"),
            "second line must show 2-arg signature, got: {}",
            lines[1]
        );
        // Only the first line carries the `; defn` classification.
        assert!(
            lines[0].contains("; defn"),
            "first line must carry `; defn` classification, got: {}",
            lines[0]
        );
        assert!(
            !lines[1].contains("; defn"),
            "second line MUST NOT repeat `; defn` classification, got: {}",
            lines[1]
        );
    }

    // spec: repl/spec.md §4.1.1 — first variant carries the docstring; later
    // variants do not.
    #[test]
    fn overloaded_display_attaches_docstring_to_first_variant_only() {
        let module = ModuleFullPath::from("user");
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants(
            "pick", &module, &variants, Some("Pick one or sum two"),
        );
        let lines: Vec<&str> = out.lines().collect();
        assert!(
            lines[0].contains("Pick one or sum two"),
            "first line must include the docstring, got: {}",
            lines[0]
        );
        assert!(
            !lines[1].contains("Pick one or sum two"),
            "second line MUST NOT repeat the docstring, got: {}",
            lines[1]
        );
    }

    // spec: repl/spec.md §4.1.1 — single-variant degenerate case is correct
    // (one line, no duplication).
    #[test]
    fn overloaded_display_single_variant_emits_one_line() {
        let module = ModuleFullPath::from("user");
        let variants = vec![variant(vec![Type::Int], Type::Int, "id$Int")];
        let out = format_overloaded_variants("id", &module, &variants, None);
        assert_eq!(
            out.lines().count(),
            1,
            "single-variant Overloaded must emit one line, got: {out}"
        );
    }

    // /sig path uses bare names per `format_entry_sig` convention; make sure
    // bare variant of the helper drops the module prefix.
    #[test]
    fn overloaded_display_bare_omits_module_prefix() {
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants_bare("pick", &variants, None);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 2);
        for line in &lines {
            assert!(
                !line.contains("user/pick"),
                "bare variant must NOT include module prefix, got: {line}"
            );
            assert!(
                line.contains(" pick"),
                "bare variant must include the bare name, got: {line}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Sprint 60 Workstream G — /sig docstring format fix.
// spec: repl/spec.md §1.1 — universal output format mandates
//       `:Type name ; classification - docstring-first-line`.
// design: design/int/dual-path-persistence-collapse.md §9.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod format_entry_sig_tests {
    use super::*;
    use cranelisp_types::{DefKind, Scheme, Type, Visibility};
    use std::collections::HashMap as StdHashMap;

    fn mk_def_entry(
        ty: Type,
        docstring: Option<String>,
    ) -> ModuleEntry<Code> {
        let mut builder = ModuleEntry::def(
            Scheme { type_vars: vec![], constraints: StdHashMap::new(), ty },
            DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0 },
            },
        )
        .visibility(Visibility::Public);
        if let Some(doc) = docstring {
            builder = builder.docstring(doc);
        }
        builder.build()
    }

    // spec: repl/spec.md §1.1 — "; classification - docstring-first-line"
    #[test]
    fn format_entry_sig_defn_includes_docstring_after_dash() {
        let fn_ty = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        let entry = mk_def_entry(fn_ty, Some("Add two ints".to_string()));
        let out = format_entry_sig(&entry, "add");
        assert!(
            out.ends_with(" ; defn - Add two ints"),
            "output must end with `; defn - <doc>`, got: {out}"
        );
    }

    // spec: repl/spec.md §1.1 — "If the symbol has no docstring, only the
    //                           classification appears."
    #[test]
    fn format_entry_sig_defn_without_docstring_omits_dash() {
        let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let entry = mk_def_entry(fn_ty, None);
        let out = format_entry_sig(&entry, "id");
        assert!(
            out.ends_with(" ; defn"),
            "output must end with `; defn` (no trailing dash), got: {out}"
        );
        assert!(
            !out.contains(" - "),
            "no-docstring output MUST NOT contain ` - ` separator, got: {out}"
        );
    }

    // spec: repl/spec.md §1.1 — "The docstring is the first line of the
    //                           symbol's documentation."
    #[test]
    fn format_entry_sig_defn_docstring_uses_first_line_only() {
        let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let entry = mk_def_entry(
            fn_ty,
            Some("First line\nSecond line\nThird line".to_string()),
        );
        let out = format_entry_sig(&entry, "f");
        assert!(
            out.contains(" - First line"),
            "docstring first line must be appended, got: {out}"
        );
        assert!(
            !out.contains("Second line"),
            "only first line must be appended; second line leaked: {out}"
        );
        assert!(
            !out.contains("Third line"),
            "only first line must be appended; third line leaked: {out}"
        );
    }

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
