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
    /// `/ask <text>` — the embedded-agent escape hatch (repl/spec.md §17.1,
    /// design/int/agent.md §2.3). Registered in BOTH builds so the parser table
    /// is identical (so `/ask` is always recognised-not-unknown); the *dispatch
    /// body* is feature-split — agent-ON routes to `agent_turn`, agent-OFF prints
    /// "agent not built in".
    Ask(&'a str),
    /// `/refs <sym>` — reverse-query: definitions whose body references `<sym>`
    /// (repl/spec.md §17.6.1, agent.md §9). LLM-free, default build, unconditional.
    Refs(&'a str),
    /// `/tests-for <sym>` — reverse-query restricted to test functions
    /// (repl/spec.md §17.6.2, agent.md §9). LLM-free, default build, unconditional.
    TestsFor(&'a str),
    /// `/syntax [<topic>]` — the topic-indexed core-language cheat-sheet
    /// (repl/spec.md §17.17, agent.md §22). Bare → the topic-name index;
    /// `<topic>` → that topic's content; unknown → re-list the index (never a
    /// dead end). UNCONDITIONAL (default build) — not feature-gated; the static
    /// cheat-sheet asset is LLM-free. The agent *pull* of it rides the `agent`
    /// feature (the allowlist row), but the command is always present.
    Syntax(&'a str),
    /// `/context <path>` — debug: dump the assembled agent request (exactly what
    /// `agent_turn` would send to the model) to `<path>` as readable text
    /// (repl/spec.md §17). Registered in BOTH builds so the parser table is
    /// identical; the dispatch body is feature-split — agent-ON serializes the
    /// live `assemble_request` (no API call, works dormant), agent-OFF prints
    /// "agent not built in". Human-invoked debug only — NOT in the pull allowlist
    /// (it writes a file; the agent can never issue it).
    Context(&'a str),
    /// `/search <query>` — Pillar-3 importable-symbol search (repl/spec.md
    /// §17.19, agent.md §25). A NORMAL default-build session facility (NOT
    /// agent-gated): searches symbols reachable-but-unimported (lib-path ∪
    /// project-root) by name OR scheme, exact OR partial. Also reached by the
    /// agent via the ordinary read-only pull (`src/agent/pull.rs` ALLOWLIST).
    Search(&'a str),
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
        "/ask" => ReplCommand::Ask(arg),
        "/refs" => ReplCommand::Refs(arg),
        "/tests-for" => ReplCommand::TestsFor(arg),
        "/syntax" => ReplCommand::Syntax(arg),
        "/context" => ReplCommand::Context(arg),
        "/search" => ReplCommand::Search(arg),
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
    let _ = writeln!(stdout, "  /refs NAME          List definitions whose body references NAME");
    let _ = writeln!(stdout, "  /tests-for NAME     List test functions that reference NAME");
    let _ = writeln!(stdout, "  /syntax [TOPIC]     Core-language syntax cheat-sheet (bare lists topics)");
    let _ = writeln!(stdout, "  /search QUERY       Find an importable symbol by name or type signature");
    let _ = writeln!(stdout, "  /ask <text>         Ask the embedded agent (if built in)");
    let _ = writeln!(stdout, "  /context <path>     Dump the assembled agent request to a file (debug; if built in)");
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
/// Reads the current allocation counters from `cranelisp-intrinsics` and
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
        // Bucketing is the shared `classify_listing_entry` classifier (FIXME
        // 0440) — single-symbol describe surfaces every category incl.
        // SpecialForm. The scheme/docstring facets are pulled per-entry below.
        let category = crate::worker::classify_listing_entry(&entry)?;
        let (scheme, docstring) = match &entry {
            ModuleEntry::Def { scheme, docstring, .. } =>
                (Some(scheme.clone()), docstring.clone()),
            ModuleEntry::SpecialForm { scheme, docstring, .. } =>
                (Some(scheme.clone()), docstring.clone()),
            ModuleEntry::TraitDecl { docstring, .. } =>
                (None, docstring.clone()),
            _ => (None, None),
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

        // Error blocking (§14.4): refuse eval when modules have errors —
        // EXCEPT definition turns, which are always accepted while
        // error-blocked (they are the repair; repl/spec.md §18.8's explicit
        // carve-out — a successful definition clears its failed form via
        // `clear_repaired_failed_form`).
        if !self.error_modules.is_empty() && !is_repair_definition_turn(trimmed) {
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
            ReplCommand::Ask(text) => {
                // The variant + parse arm are unconditional (the parser table is
                // identical in both builds); the dispatch BODY is feature-split.
                // repl/spec.md §17.1, design/int/agent.md §2.3.
                #[cfg(feature = "agent")]
                {
                    // The REPL loop (`main.rs`) intercepts `/ask` BEFORE
                    // `process_commands` (feature-on) so the Build confirm-gate
                    // gets the stdin consent line-reader (§15.2). This arm is the
                    // fallback for any other caller reaching `/ask` through
                    // dispatch directly — it has no stdin source, so the gate
                    // declines by default (`NoConsent`).
                    let mut consent = crate::agent::types::NoConsent;
                    self.agent_turn(text, stdout, &mut consent);
                    CommandResult::Nothing
                }
                #[cfg(not(feature = "agent"))]
                {
                    let _ = text;
                    CommandResult::Final(
                        "agent not built in (rebuild with --features agent)".to_string(),
                    )
                }
            }
            ReplCommand::Refs(sym) => {
                CommandResult::Final(self.handle_refs(sym))
            }
            ReplCommand::TestsFor(sym) => {
                CommandResult::Final(self.handle_tests_for(sym))
            }
            ReplCommand::Syntax(topic) => {
                // Deterministic curated output (repl/spec.md §17.17.2) — a free
                // fn over the static cheat-sheet, NOT agent prose (no `▌` frame)
                // and NOT styled (the plain-text asset carries no ANSI, so it
                // degrades cleanly under --no-color with no new style role).
                CommandResult::Final(crate::syntax::handle_syntax(topic))
            }
            ReplCommand::Context(path) => {
                // The variant + parse arm are unconditional (identical parser
                // table); the dispatch BODY is feature-split. Agent-ON dumps the
                // assembled request (no API call — works dormant). Agent-OFF
                // mirrors `/ask`. repl/spec.md §17.
                #[cfg(feature = "agent")]
                {
                    CommandResult::Final(self.handle_context(path))
                }
                #[cfg(not(feature = "agent"))]
                {
                    let _ = path;
                    CommandResult::Final(
                        "agent not built in (rebuild with --features agent)".to_string(),
                    )
                }
            }
            ReplCommand::Search(query) => {
                CommandResult::Final(self.handle_search(query))
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
                // S102 W5R M-1: the retained degraded-startup failed forms go
                // with the error block (a non-empty failed set implies
                // `error_modules` membership; clearing one without the other
                // leaves regen re-appending stale broken text).
                self.failed_forms.clear();
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

    /// Resolve an introspection-command argument that may be a bare name or a
    /// module-qualified `module/name` (§3.8/§3.6/§17.6.1; FIXME 0487) to its
    /// home module + bare symbol. A `/`-qualified qualifier is alias-substituted
    /// (§8.6.6 longest-prefix, the same substitution the FQ-autoload boundary
    /// uses); a bare argument keeps the current REPL module as its home.
    ///
    /// This is the single argument-shape authority shared across `/sig`,
    /// `/info`, `/source`, `/sexp`, `/clif`, and `/refs` — the FQ names the
    /// transaction/cascade reports print (`; broken: n/ng — …`) MUST be
    /// pasteable into every introspection command (0487's operational
    /// complaint).
    pub(crate) fn resolve_symbol_arg(&self, name: &str) -> (ModuleFullPath, String) {
        match name.rsplit_once('/') {
            Some((module_part, bare)) => {
                let resolved = cranelisp_types::substitute_module_alias(
                    &self.shared.module_aliases,
                    &ModuleFullPath::from(module_part),
                );
                (resolved, bare.to_string())
            }
            None => (self.current_module_path(), name.to_string()),
        }
    }

    /// FQ-aware entry lookup for the introspection commands. For a
    /// module-qualified `module/name`, resolves the home module (alias-aware)
    /// and looks the bare symbol up in that module's own table. For a bare
    /// name, delegates to `lookup_with_prelude_fallback` (current → prelude →
    /// root) so bare resolution is unchanged. Returns `(entry, home_module,
    /// bare)`.
    pub(crate) fn resolve_entry_arg(
        &self,
        name: &str,
    ) -> Option<(ModuleEntry<Code>, ModuleFullPath, String)> {
        if name.contains('/') {
            let (home, bare) = self.resolve_symbol_arg(name);
            let entry = self.shared.symbol_tables.get(&home)?.get(&bare)?.clone();
            Some((entry, home, bare))
        } else {
            let (entry, module) = self.lookup_with_prelude_fallback(name)?;
            Some((entry, module, name.to_string()))
        }
    }

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
                Some(SymbolCategory::Fn) => fns.push(name.to_string()),
                // Constructors are part of their type; special forms + imports
                // are shown by /imports.
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
        let pending = self.shared.importable_indices.pending_count();
        let note = if pending > 0 {
            format!("\n; indexing {pending} module(s)… (results may be incomplete)")
        } else {
            String::new()
        };

        if rows.is_empty() {
            return format!("; no importable symbols matched '{query}'{note}");
        }

        // Lead with a newline so the first result row starts on its own line
        // below the prompt (matching the spec §17.19.2 examples, which show the
        // rows beneath the `user> /search …` line) rather than glued to the
        // prompt in a non-TTY/piped session where the input is not echoed.
        let mut out = String::from("\n");
        for row in &rows {
            out.push_str(&self.render_search_row(row, query));
        }
        out.push_str(note.trim_start_matches('\n'));
        while out.ends_with('\n') {
            out.pop();
        }
        out
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
        if let ModuleEntry::Def { scheme, docstring, .. } = resolved {
            Some(SearchHit {
                name: Symbol::from(query),
                module: origin,
                scheme: scheme.ty.clone(),
                docstring: docstring.clone(),
                tier: MatchTier::ExactName,
            })
        } else {
            None
        }
    }

    /// Render one `/search` result row — the facets of spec §17.19.2. Facet 4 is
    /// the `(import …)` form, REPLACED by the `already in scope — no import
    /// needed` marker for an exact in-scope match (R13); facet 5 is the `; doc:`
    /// excerpt, present ONLY on a docstring-only hit (§17.19.1a tier 6).
    fn render_search_row(&self, row: &SearchRow, query: &str) -> String {
        use crate::session_v4::index_worker::MatchTier;
        let hit = &row.hit;
        let sig = crate::display::format_type_qualified(&hit.scheme);
        let name = hit.name.as_ref();
        let module = hit.module.as_ref();
        // Facet 4: import form, or the in-scope marker for an exact in-scope hit.
        let action = if row.in_scope {
            "already in scope — no import needed".to_string()
        } else {
            format!("(import [{module} [{name}]])")
        };
        let mut out = format!(":{sig} {name}\n  in {module}   — {action}\n");
        // Facet 5: docstring excerpt, only for a docstring-only hit.
        if hit.tier == MatchTier::DocstringOnly
            && let Some(doc) = &hit.docstring
            && let Some(excerpt) = docstring_excerpt(doc, query)
        {
            out.push_str(&format!("  ; doc: {excerpt}\n"));
        }
        out
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
    fn symbol_is_bound(&self, sym: &str) -> bool {
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
    fn scan_referers(&self, target: &str, tests_only: bool) -> Vec<String> {
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

    /// Look up introspection data for a symbol name — bare (current module) or
    /// module-qualified (§17.6.1 / FIXME 0487: `/source`, `/sexp`, `/clif`, and
    /// `/info`'s code-size read accept the FQ names the reports print). A bare
    /// name keeps the current-module home, so bare-name behaviour is unchanged.
    pub(crate) fn get_introspection(&self, name: &str) -> Option<dashmap::mapref::one::Ref<'_, FQSymbol, Introspection>> {
        let (module, bare) = self.resolve_symbol_arg(name);
        let fq = FQSymbol {
            module,
            symbol: Symbol::from(bare),
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

    /// The REPL prompt string with timing info.
    /// Format: `{compile_ms}+{eval_ms}ms; {module}> `
    ///
    /// Used both by the non-TTY read loop (written to stdout) and by the TTY
    /// line editor (§10.8: passed to `readline`).
    pub fn prompt_string(&self, compile_ms: u64, eval_ms: u64) -> String {
        let module = self.current_module_name();
        format!("{compile_ms}+{eval_ms}ms; {module}> ")
    }

    /// The continuation-prompt string (for multi-line input) — right-aligned
    /// `...` to the width of the normal prompt.
    pub fn continuation_prompt_string(&self, compile_ms: u64, eval_ms: u64) -> String {
        let prompt_len = self.prompt_string(compile_ms, eval_ms).len();
        format!("{:>width$}", "...", width = prompt_len)
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
            EvalResult::Def { symbol, defined, .. } => {
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
                // FIXME 0542: a bare LOOKUP (`defined == false`) is pure
                // introspection — a trait's `; impl:` section is structural
                // (§4.1.4), shown even when empty. A definition ECHO
                // (`defined == true`) follows §1.1 and omits the empty section.
                let body =
                    self.format_def_entry(&entry, name, &resolved_module, !*defined);
                // S101 (repl/spec.md §18.4): bare lookup of a broken symbol is
                // self-documenting — the ordinary per-class display (last-good
                // signature) plus the provenance comment line.
                match self.broken_status_line(name, &resolved_module) {
                    Some(line) => format!("{body}\n{line}"),
                    None => body,
                }
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
                    // Drive through `cranelisp_run_io` (the reactor-driving entry
                    // under `concurrency-runtime`, byte-identical otherwise; it
                    // also consumes the tree internally) — same entry as
                    // `unwrap_io_inline` (FIXME 0457).
                    let inner_value = cranelisp_intrinsics::io::cranelisp_run_io(*value);
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
            // A runtime TRAP renders as the bare §18.5 line: the `runtime error: `
            // category prefix (§5.1) directly followed by the trap payload — no
            // `Error: ` prefix, no `codegen error at 0..0:` wrapper, no
            // `runtime panic: ` slot prefix (normalized away in `pipeline`).
            EvalResult::RuntimeError { message, .. } => {
                format!("runtime error: {message}")
            }
        }
    }

    /// Format a definition entry with its classification (spec §1.1, §4.1).
    pub(crate) fn format_def_entry(
        &self,
        entry: &ModuleEntry<Code>,
        name: &str,
        module: &ModuleFullPath,
        // FIXME 0542: when set, a trait entry's `; impl:` section is emitted
        // even when empty (§4.1.4 pure-introspection displays: bare lookup,
        // `/sig`, `/info`). A definition echo passes `false` (§1.1 omits the
        // empty section). Ignored for every non-trait entry.
        full_trait_sections: bool,
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
                // Both got-slotted primitives (`DefKind::Primitive`, e.g.
                // `add-i64`) and slot-less host-promised externs
                // (`DefKind::PrimitiveExtern`, e.g. the S96 `race`/`select`/
                // `sleep` builtins + `bind`/`discover-tests`/`catch-runtime-error`)
                // are `primitives`-module builtins and MUST classify as
                // `; primitive` per `repl/spec.md §1.1` — a `PrimitiveExtern`
                // dispatches by-name via `Linkage::Import` but is no less a
                // primitive to the user (FIXME 0481).
                let is_primitive = matches!(
                    kind.as_ref(),
                    DefKind::Primitive { .. } | DefKind::PrimitiveExtern
                );
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
                self.format_trait_display(name, docstring.as_deref(), full_trait_sections)
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
    pub(crate) fn format_trait_display(
        &self,
        trait_name: &str,
        docstring: Option<&str>,
        full_impl_section: bool,
    ) -> String {
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
        // FIXME 0542 (§4.1.4): a bare trait lookup MUST ALWAYS surface BOTH the
        // `; defn:` (method names) and `; impl:` (implementing types) sections —
        // for user-module traits and stdlib traits alike, and even when the
        // trait has no impls yet (the `; impl:` header appears with an empty
        // body). This is DELIBERATELY UNCONDITIONAL, unlike the type-display
        // rule (§4.1.3), where an empty `; impl:` section is omitted: a trait's
        // related sections are structural, a type's are conditional.
        // FIXME 0192 method 4: `get_trait_methods` deleted; inline the 1-line
        // wrapper over `lookup_trait_decl_chain`.
        let method_names: Vec<String> = cranelisp_types::lookup_trait_decl_chain(
            &self.shared.symbol_tables, &scope, &tn,
        )
        .map(|decl| decl.methods.iter().map(|m| m.name.to_string()).collect())
        .unwrap_or_default();
        let impl_type_names: Vec<String> = cranelisp_types::get_implementing_types_chain(
            &self.shared.symbol_tables, &scope, &tn,
        )
        .iter()
        .map(|t| t.to_string())
        .collect();
        let method_refs: Vec<&str> = method_names.iter().map(String::as_str).collect();
        let impl_refs: Vec<&str> = impl_type_names.iter().map(String::as_str).collect();
        result.push_str(&format_trait_related_sections(
            &method_refs,
            &impl_refs,
            full_impl_section,
        ));
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

/// Format a related symbols section (spec §1.1). The symbol block uses the
/// shared §3.3 layout formatter (repl/spec.md:198 — related lists use the same
/// normative L0–L4 layout as `/list`), rendered as comment rows.
pub(crate) fn format_related_section(label: &str, names: &[&str]) -> String {
    let owned: Vec<String> = names.iter().map(|n| n.to_string()).collect();
    let mut out = format!("\n; {label}:");
    for row in format_symbol_layout(&owned) {
        out.push_str("\n;  ");
        out.push_str(&row);
    }
    out
}

/// Render a trait's related-symbol sections for introspection display
/// (spec §4.1.4). The `; defn:` (method names) section is emitted whenever the
/// trait declares methods. The `; impl:` (implementing types) section is
/// emitted when the trait has impls OR when `full_impl_section` is set — the
/// FIXME-0542 fix: a **pure introspection** display (a bare trait lookup, and
/// its byte-identical `/sig`/`/info` siblings, §3.8/§3.6) MUST surface the
/// `; impl:` section STRUCTURALLY, even when the trait has no impls yet (the
/// header appears with an empty body). A **definition echo** (`(deftrait …)`
/// result) passes `full_impl_section = false` so it follows the §1.1 example,
/// which omits the empty `; impl:` for a freshly-defined impl-less trait — the
/// same omit-when-empty rule the type display (§4.1.3) uses. Extracted as a
/// free function so the emit contract is unit-testable without constructing a
/// `CompilerSession` (`src/CLAUDE.md` testability discipline; mirrors
/// `collect_related_for`).
pub(crate) fn format_trait_related_sections(
    method_names: &[&str],
    impl_type_names: &[&str],
    full_impl_section: bool,
) -> String {
    let mut out = String::new();
    if !method_names.is_empty() {
        out.push_str(&format_related_section("defn", method_names));
    }
    if full_impl_section || !impl_type_names.is_empty() {
        out.push_str(&format_related_section("impl", impl_type_names));
    }
    out
}

/// Indent every line of a rendered definition source by two spaces — the
/// `/info` block layout (`repl/spec.md` §3.6 worked example; the §18.4
/// broken-symbol example uses the same indentation).
fn indent_source_block(text: &str) -> String {
    text.lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Classification of an imported symbol for category-based display.
pub(crate) enum ImportClass {
    Macro,
    Trait,
    Type,
    Constructor,
    Fn,
}

/// Maximum number of names per body row in the breaking layout (L2/L3/L4).
const LAYOUT_ROW_CAP: usize = 6;

/// Threshold (exclusive) below which a category renders on a single line (L0/L1).
/// Fewer than 7 names → single line; 7 or more → breaking layout.
const LAYOUT_BREAK_THRESHOLD: usize = 7;

/// Whether a definition is a test function (the `test-` prefix + a nullary
/// `Def`, per the test convention §16.1) — the `/tests-for` filter
/// (repl/spec.md §17.6.2). Structural (does not require the function to be
/// codegen'd), so it works over freshly-typechecked REPL state.
fn is_test_function(name: &str, entry: &ModuleEntry<Code>) -> bool {
    if !name.starts_with("test-") {
        return false;
    }
    matches!(entry, ModuleEntry::Def { param_names, .. } if param_names.is_empty())
}

/// Whether a definition's stored body references `target` as a whole symbol
/// token (repl/spec.md §17.6, design/int/agent.md §9.2). Prefers a walk over
/// the stored `sexp` (precise — matches a `Symbol` node, not a substring);
/// falls back to a token-scan of the source text when no sexp is stored.
///
/// A qualified reference (`mod/target`) matches an unqualified `target` query
/// (the `/`-tail is compared), so `/refs grid-get` finds `solver/grid-get` uses.
fn body_references(record: &Introspection, target: &str) -> bool {
    if let Some(ref sexp) = record.sexp {
        return sexp_references(sexp, target);
    }
    if let Some(ref src) = record.source {
        return source_tokens_reference(src, target);
    }
    false
}

/// Walk a `Sexp` tree, returning true if any `Symbol` node names `target`
/// (bare or as the `/`-qualified tail).
fn sexp_references(sexp: &Sexp, target: &str) -> bool {
    match sexp {
        Sexp::Symbol(name, _) => symbol_token_matches(name, target),
        Sexp::List(items, _) | Sexp::Bracket(items, _) => {
            items.iter().any(|s| sexp_references(s, target))
        }
        _ => false,
    }
}

/// Token-scan a source string for `target` as a whole symbol token. A token is
/// a maximal run of non-delimiter chars (delimiters: whitespace, parens,
/// brackets, quotes). Comments (`;` to end of line) and string literals are
/// skipped so a mention inside a comment or string is not a reference.
fn source_tokens_reference(src: &str, target: &str) -> bool {
    let mut token = String::new();
    let mut in_string = false;
    let mut in_comment = false;
    let mut prev = '\0';
    let flush = |token: &mut String, target: &str| -> bool {
        let hit = !token.is_empty() && symbol_token_matches(token, target);
        token.clear();
        hit
    };
    for ch in src.chars() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            prev = ch;
            continue;
        }
        if in_string {
            if ch == '"' && prev != '\\' {
                in_string = false;
            }
            prev = ch;
            continue;
        }
        match ch {
            ';' => {
                if flush(&mut token, target) {
                    return true;
                }
                in_comment = true;
            }
            '"' => {
                if flush(&mut token, target) {
                    return true;
                }
                in_string = true;
            }
            c if c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']' => {
                if flush(&mut token, target) {
                    return true;
                }
            }
            c => token.push(c),
        }
        prev = ch;
    }
    flush(&mut token, target)
}

/// Whether a symbol token names `target` — exact match, or the `/`-qualified
/// tail of a module-qualified reference (`mod/target`).
fn symbol_token_matches(token: &str, target: &str) -> bool {
    token == target || token.rsplit_once('/').map(|(_, tail)| tail) == Some(target)
}

/// Whether a symbol name reads as an operator (non-alphabetic leading char).
/// Operators (`+`, `-`, `<=`, `!=`, …) sort before, and never share a row with,
/// alphabetic names (repl/spec.md §3.3 L2).
fn is_operator_name(name: &str) -> bool {
    name.chars().next().map(|c| !c.is_alphabetic()).unwrap_or(true)
}

/// The single normative symbol-layout formatter shared by `/list` (§3.3),
/// `/imports` (§3.4), `/exports` (§3.5), and related-symbol lists (§2).
///
/// Realises rules L0–L4 from repl/spec.md §3.3. Returns the BODY rows (names
/// only, no indent, no `: type` suffix) in order; callers add their own chrome
/// (the `Label:` header and two-space indent). The same name set MUST always
/// produce byte-for-byte identical output across all four commands.
///
/// - **L0/L1** — fewer than 7 names → a single space-separated row; 7+ break.
/// - **L2** — operators first, on their own rows, capped at 6/row; an operator
///   never shares a row with an alphabetic name.
/// - **L3** — alphabetic names grouped by first letter (case-insensitive) in
///   sorted order; a group flushes the current row when `count + size > 6`, so
///   a group never straddles a row boundary…
/// - **L4** — …except a single group of more than 6 names, which hard-wraps at
///   6/row within itself.
pub(crate) fn format_symbol_layout(names: &[String]) -> Vec<String> {
    if names.is_empty() {
        return Vec::new();
    }

    // Deterministic input ordering (callers already sort, but the formatter is
    // the single source of truth for the contract — sort defensively).
    let mut sorted: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
    sorted.sort();

    // L0/L1: below the threshold, one space-separated row, no breaking.
    if sorted.len() < LAYOUT_BREAK_THRESHOLD {
        return vec![sorted.join(" ")];
    }

    let mut rows: Vec<String> = Vec::new();

    // L2: operators first, on their own rows, capped at LAYOUT_ROW_CAP per row.
    // After the last operator a new row starts — operators never share a row
    // with an alphabetic name.
    let operators: Vec<&str> = sorted.iter().copied().filter(|n| is_operator_name(n)).collect();
    for chunk in operators.chunks(LAYOUT_ROW_CAP) {
        rows.push(chunk.join(" "));
    }

    // L3/L4: alphabetic names grouped by first letter (case-insensitive), in
    // sorted order. Build the contiguous letter groups (input is sorted, so
    // names sharing a first letter are already adjacent).
    let mut groups: Vec<Vec<&str>> = Vec::new();
    let mut current_letter: Option<char> = None;
    for name in sorted.iter().copied().filter(|n| !is_operator_name(n)) {
        let letter = name.chars().next().map(|c| c.to_ascii_lowercase());
        if letter != current_letter {
            current_letter = letter;
            groups.push(Vec::new());
        }
        if let Some(g) = groups.last_mut() {
            g.push(name);
        }
    }

    let mut row: Vec<&str> = Vec::new();
    for group in &groups {
        if group.len() > LAYOUT_ROW_CAP {
            // L4: an oversized single-letter group hard-wraps at 6/row. Flush
            // any in-progress row first so the group starts fresh.
            if !row.is_empty() {
                rows.push(row.join(" "));
                row.clear();
            }
            for chunk in group.chunks(LAYOUT_ROW_CAP) {
                rows.push(chunk.join(" "));
            }
            continue;
        }
        // L3: early-break to keep the group whole.
        if !row.is_empty() && row.len() + group.len() > LAYOUT_ROW_CAP {
            rows.push(row.join(" "));
            row.clear();
        }
        row.extend(group.iter().copied());
    }
    if !row.is_empty() {
        rows.push(row.join(" "));
    }

    rows
}

/// Emit the shared §3.3 L0–L4 layout rows for `names`, each indented two
/// spaces (the `/list` / `/imports` / `/exports` body format). Single-sources
/// the layout body used by both `append_name_category` and the `/imports`
/// "Prelude (implicit)" group (FIXME 0546 — the prelude group formerly dumped
/// one name per line, bypassing `format_symbol_layout`; routing both through
/// this helper is the Principle-7 fix).
fn append_layout_body(buf: &mut String, names: &[String]) {
    for row in format_symbol_layout(names) {
        buf.push_str("  ");
        buf.push_str(&row);
        buf.push('\n');
    }
}

/// Append a category of names to a string buffer (for /list, /imports, /exports),
/// rendering the symbol block through the shared §3.3 layout formatter.
pub(crate) fn append_name_category(buf: &mut String, label: &str, names: &[String]) {
    if names.is_empty() {
        return;
    }
    buf.push_str(label);
    buf.push_str(":\n");
    append_layout_body(buf, names);
}

/// Build the `/imports` "Prelude (implicit)" group (spec §3.4). The header line
/// carries a trailing suffix comment explaining the outer-scope semantics; the
/// prelude names render through the SAME shared §3.3 L0–L4 layout as every
/// other `/imports` category (FIXME 0546). The header suffix comment is
/// preserved verbatim — the layout applies only to the name body. Extracted as
/// a free function so the header-preservation + shared-layout routing is
/// unit-testable without a `CompilerSession`.
pub(crate) fn format_prelude_implicit_group(names: &[String]) -> String {
    let mut out = String::from(
        "Prelude (implicit):  \
         ; available via the prelude outer scope; a local def or a clashing \
         import of the same name conflicts — use the fully-qualified name\n",
    );
    append_layout_body(&mut out, names);
    out
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

/// Is `src` a pure DEFINITION (or structural) turn — the §14.4/§18.8 error-
/// blocking carve-out? While a module is error-blocked, expression turns are
/// refused with the §14.4 message but definition turns MUST be accepted:
/// they are the repair path (repl/spec.md §18.8). Pure over the text; every
/// top-level form must be a defining or structural special form — any
/// expression member (including inside a mixed input), an empty input, or a
/// parse failure classifies as NOT-a-definition-turn (refused; the parse
/// error re-surfaces once the module is repaired). `begin` is deliberately
/// excluded: a begin cluster may embed expressions the gate exists to refuse.
pub(crate) fn is_repair_definition_turn(src: &str) -> bool {
    let Ok(forms) = cranelisp_frontend::parse(src) else {
        return false;
    };
    if forms.is_empty() {
        return false;
    }
    forms.iter().all(|f| {
        if let Sexp::List(items, _) = f
            && let Some(Sexp::Symbol(head, _)) = items.first()
        {
            matches!(
                head.as_str(),
                "defn" | "defn-" | "defmacro" | "defmacro-" | "deftype" | "deftrait"
                    | "impl" | "import" | "export" | "mod" | "mod-" | "platform"
            )
        } else {
            false
        }
    })
}

// ==============================================================================
// Tests migrated with their code from session_v4.rs (FIXME 0109 Wave D)
// ==============================================================================

#[cfg(test)]
mod repair_definition_turn_tests {
    use super::is_repair_definition_turn;

    // spec: repl/spec.md §18.8 — a definition turn at the prompt MUST be
    // accepted while the entry module is error-blocked (it is the repair);
    // §14.4 — expression evaluation is refused.
    #[test]
    fn definition_and_structural_turns_pass_the_carve_out() {
        assert!(is_repair_definition_turn("(defn k [:String y] (f y))"));
        assert!(is_repair_definition_turn("(defmacro m [e] e)"));
        assert!(is_repair_definition_turn("(deftype P [:Int x])"));
        assert!(is_repair_definition_turn("(import [m [mf]])"));
        // Multi-form all-definition input is still a repair turn.
        assert!(is_repair_definition_turn("(defn a [] 1)\n(defn b [] 2)"));
    }

    // spec: repl/spec.md §14.4 — expressions (and anything not purely
    // defining) stay refused: bare calls, literals, bare symbols, mixed
    // defn+expression input, begin clusters (may embed expressions), empty
    // and unparseable input.
    #[test]
    fn neg_expressions_mixed_and_malformed_are_refused() {
        assert!(!is_repair_definition_turn("(k \"abcd\")"));
        assert!(!is_repair_definition_turn("42"));
        assert!(!is_repair_definition_turn("k"));
        assert!(!is_repair_definition_turn("(defn a [] 1)\n(a)"));
        assert!(!is_repair_definition_turn("(begin (defn a [] 1) (a))"));
        assert!(!is_repair_definition_turn(""));
        assert!(!is_repair_definition_turn("(defn broken ["));
    }
}

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
                mode_summary: None,
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

// ---------------------------------------------------------------------------
// CS-0487 (S102 Wave 7) — FQ introspection-argument resolution.
// spec: repl/spec.md §3.8 (/sig FQ) + §3.6 (/info FQ) + §17.6.1 (/refs FQ);
//       spec/08-modules.md §8.5.1 (module-qualified name is a symbol)
// ---------------------------------------------------------------------------
#[cfg(test)]
mod fq_arg_tests {
    use super::*;
    use crate::session_v4::{RunMode, SessionSettings};
    use cranelisp_types::{
        CodegenBehaviour, DefKind, ModuleAliasEntry, ModuleEntry, ModuleFullPath, Scheme, Span,
        Symbol, Type, UserFnState, Visibility,
    };
    use std::collections::HashMap as StdHashMap;

    fn session() -> CompilerSession {
        let tmp = tempfile::tempdir().unwrap();
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 1,
            run_mode: RunMode::Repl,
        };
        CompilerSession::new(settings, tmp.keep(), "user")
    }

    fn int_fn_scheme() -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: StdHashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        }
    }

    fn userfn_def(doc: Option<&str>) -> ModuleEntry<Code> {
        ModuleEntry::Def {
            scheme: int_fn_scheme(),
            visibility: Visibility::Public,
            docstring: doc.map(|s| s.to_string()),
            param_names: vec![Symbol::from("x")],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
            }),
            callees: Vec::new(),
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        }
    }

    /// Install module `m` with a single Def `mf`.
    fn install_m(s: &CompilerSession, doc: Option<&str>) {
        let m = ModuleFullPath::from("m");
        let mut table = SessionSymbolTable::new_with_params(m.clone());
        table.insert(Symbol::from("mf"), userfn_def(doc));
        s.shared.symbol_tables.insert(m, table);
    }

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

    // §18.5 (trap presentation): an `EvalResult::RuntimeError` renders as the
    // bare `runtime error: {payload}` line — the §5.1 category prefix directly
    // followed by the trap message, with NONE of the wrapper chain the pre-fix
    // path emitted (`Error: codegen error at 0..0: runtime error: runtime
    // panic: …`). spec: repl/spec.md §18.5
    #[test]
    fn runtime_error_renders_bare_normative_format() {
        let s = session();
        let payload = "user/g is broken by the redefinition of user/f: \
                       type error at 24..34: type mismatch: expected \
                       primitives/String, got primitives/Int";
        let out = s.format_eval_result(&super::EvalResult::RuntimeError {
            message: payload.to_string(),
            warnings: Vec::new(),
        });
        assert_eq!(out, format!("runtime error: {payload}"));
        assert!(!out.contains("Error:"), "no Error: prefix; got: {out}");
        assert!(!out.contains("codegen error"), "no codegen wrapper; got: {out}");
        assert!(!out.contains("runtime panic:"), "no slot prefix; got: {out}");
        assert!(!out.contains("0..0"), "no synthetic span; got: {out}");
    }
}

// ---------------------------------------------------------------------------
// FIXME 0542 — bare trait lookup always surfaces `; defn:` and `; impl:`
// sections. Unit-tests the extracted always-emit section builder
// (`format_trait_related_sections`) at the exact seam of the fix.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod trait_related_section_tests {
    use super::*;

    // spec: repl/spec.md §4.1.4 — a PURE INTROSPECTION display
    // (`full_impl_section = true`: bare lookup / `/sig` / `/info`) surfaces the
    // `; impl:` section even when the trait has NO implementing types yet (the
    // header with an empty body). This is the FIXME-0542 seam.
    #[test]
    fn trait_sections_full_emits_impl_header_when_impls_empty() {
        let out = format_trait_related_sections(&["show"], &[], true);
        assert!(
            out.contains("; defn:") && out.contains("show"),
            "the `; defn:` method section MUST list `show`; got:\n{out}",
        );
        assert!(
            out.contains("; impl:"),
            "a full introspection display MUST surface the `; impl:` section \
             even with no impls (§4.1.4, FIXME 0542); got:\n{out}",
        );
    }

    // spec: repl/spec.md §1.1 — a DEFINITION ECHO (`full_impl_section = false`)
    // of a freshly-defined impl-less trait OMITS the empty `; impl:` section
    // (matching the §1.1 example) so introspection lists exactly one `; impl:`
    // section for the trait. Regression guard for the negative /qa parser.
    #[test]
    fn trait_sections_echo_omits_empty_impl_header() {
        let out = format_trait_related_sections(&["show"], &[], false);
        assert!(
            out.contains("; defn:") && out.contains("show"),
            "the `; defn:` section MUST still appear on a definition echo; \
             got:\n{out}",
        );
        assert!(
            !out.contains("; impl:"),
            "a definition echo MUST omit the empty `; impl:` section (§1.1); \
             got:\n{out}",
        );
    }

    // spec: repl/spec.md §4.1.4 — when impls exist the `; impl:` section lists
    // the implementing types and NOTHING else (positive + negative in one).
    // With impls present the section appears regardless of the flag.
    #[test]
    fn trait_sections_impl_lists_only_implementing_types() {
        for full in [true, false] {
            let out = format_trait_related_sections(&["show"], &["Int"], full);
            // Isolate the `; impl:` body rows (comment lines after the header).
            let impl_body: Vec<&str> = out
                .lines()
                .skip_while(|l| l.trim() != "; impl:")
                .skip(1)
                .take_while(|l| l.trim_start().starts_with(';'))
                .collect();
            let joined = impl_body.join(" ");
            assert!(
                joined.contains("Int"),
                "the `; impl:` section MUST list `Int` (full={full}); \
                 body={impl_body:?}",
            );
            assert!(
                !joined.contains("Bool"),
                "the `; impl:` section MUST NOT leak an unrelated type `Bool` \
                 (full={full}); body={impl_body:?}",
            );
        }
    }
}

// ---------------------------------------------------------------------------
// FIXME 0546 — `/imports` "Prelude (implicit)" group renders through the shared
// §3.3 L0–L4 layout (not one name per line), preserving the header suffix
// comment. Unit-tests the extracted `format_prelude_implicit_group` at the fix
// seam + confirms `append_name_category` shares the same layout body.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod prelude_group_layout_tests {
    use super::*;

    // A 12-name set (2 operators + 10 letter-grouped names) that the shared
    // layout MUST pack multi-column (≤6/line), not one-per-line.
    fn names() -> Vec<String> {
        [
            "+", "-", "abs", "add", "ceil", "cons", "drop", "each", "map",
            "nth", "when", "zip",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    }

    // spec: repl/spec.md §3.4 — the "Prelude (implicit)" header suffix comment
    // is preserved verbatim by the shared-layout routing (FIXME 0546).
    #[test]
    fn prelude_group_preserves_header_suffix_comment() {
        let out = format_prelude_implicit_group(&names());
        let header = out.lines().next().unwrap_or("");
        assert!(
            header.starts_with("Prelude (implicit):")
                && header.contains("available via the prelude outer scope"),
            "the header suffix comment MUST be preserved; header={header:?}",
        );
        // The suffix MUST describe the §8.6.4 CONFLICT semantics, NOT "shadowing":
        // a def (or a clashing import) of a prelude name is a compile-time error
        // resolved by the fully-qualified name — never a silent override.
        assert!(
            header.contains("conflicts") && header.contains("fully-qualified"),
            "suffix MUST describe the §8.6.4 conflict + FQ resolution; header={header:?}",
        );
        assert!(
            !header.contains("shadow"),
            "prelude names are NOT shadowed by a def/import of the same name — \
             that is a §8.6.4 conflict; header={header:?}",
        );
    }

    // spec: repl/spec.md §3.3/§3.4 — the prelude names render through the SHARED
    // multi-column layout: some body row packs ≥2 names, none exceeds 6, and the
    // body is byte-identical to `format_symbol_layout` for the same name set —
    // NOT one name per line (FIXME 0546).
    #[test]
    fn prelude_group_body_uses_shared_layout() {
        let ns = names();
        let out = format_prelude_implicit_group(&ns);
        let body: Vec<&str> = out
            .lines()
            .skip(1) // header
            .map(|l| l.strip_prefix("  ").unwrap_or(l))
            .collect();
        assert!(
            body.iter().any(|l| l.split_whitespace().count() >= 2),
            "the prelude group MUST use the shared multi-column layout, not \
             one name per line; body={body:?}",
        );
        for row in &body {
            assert!(
                row.split_whitespace().count() <= 6,
                "a shared-layout row holds at most 6 names; row={row:?}",
            );
        }
        // Byte-identical to the shared formatter for this name set.
        let expected = format_symbol_layout(&ns);
        assert_eq!(
            body, expected,
            "the prelude group body MUST equal `format_symbol_layout` output \
             (single-sourced §3.3 layout)",
        );
    }

    // The prelude group and `append_name_category` share ONE layout body
    // (Principle 7) — the same names produce the same rows through both.
    #[test]
    fn prelude_group_and_category_share_layout_body() {
        let ns = names();
        let prelude = format_prelude_implicit_group(&ns);
        let prelude_body: Vec<&str> = prelude
            .lines()
            .skip(1)
            .map(|l| l.strip_prefix("  ").unwrap_or(l))
            .collect();

        let mut cat = String::new();
        append_name_category(&mut cat, "Fns", &ns);
        let cat_body: Vec<&str> = cat
            .lines()
            .skip(1) // "Fns:" header
            .map(|l| l.strip_prefix("  ").unwrap_or(l))
            .collect();

        assert_eq!(
            prelude_body, cat_body,
            "the prelude group and a normal category MUST share the layout body",
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
