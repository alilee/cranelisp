// REPL experience — slash-command dispatch, prompt/banner/line-editor, and the
// shared resolution/referer toolbox (the bottom layer all siblings depend on).
// The introspection-display formatter (`format.rs`), the `/search` UI
// (`search.rs`), and the `handle_*` command battery (`commands.rs`) are sibling
// submodules. Cut per `design/int/repl-decomposition.md` (S110, FIXME 0606);
// pure relocation, behaviour-invariant.


pub(crate) mod commands;
pub(crate) mod format;
pub(crate) mod search;


pub(crate) use std::io::Write;

pub(crate) use cranelisp_types::{
    CranelispError, DefKind, ErrorLocation, FQSymbol, MacroClauseInfo,
    MacroParam, ModuleEntry, ModuleFullPath, OverloadVariant, Scheme, Sexp, Span, Symbol,
    TopLevel, TraitName, Type, TypeName,
};

pub(crate) use cranelisp_typecheck::CheckState;

pub(crate) use crate::code::{Code, SessionSymbolTable};
pub(crate) use crate::display::format_type_qualified;
pub(crate) use crate::styled::{Role, StyledDoc, render};
pub(crate) use crate::session_v4::{
    discover_test_names, intrinsic_type_from_name, is_comment_only, parens_balanced,
    run_test_by_name, CommandResult, CompilerSession, EvalResult, Introspection,
    ReadOnlyMacroResolver, SymbolCategory, SymbolDescription, TestOutcome,
};
pub(crate) use crate::worker::ModuleCompiler;


use format::*;

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

impl CompilerSession {
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
            // The prelude provides only its PUBLIC names (spec §8.8.1: the
            // implicit prelude is `(import [prelude [*]])`, and `*` brings only
            // public names). A PRIVATE prelude head is not in scope through the
            // fallback — resolution never resolves it, so the display /
            // enumeration classifiers that inherit this seam must not classify
            // it "in scope" either (worst at `/search`'s "already in scope — no
            // import needed"). A private head falls through: to the root `""`
            // tier when `root`, else `None`. (The resolution-side terminal-vs-
            // head filter is the separate FIXME 0567, cranelisp-types.)
            if on
                && let Some(e) = self
                    .shared
                    .symbol_tables
                    .get(&prelude_path)
                    .and_then(|t| t.get(name).cloned())
                && e.is_public()
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
        // §10.3 R13 (Prompt / Banner) — dim. Colour-off the bytes are unchanged.
        let banner = render(&StyledDoc::span(
            Role::Prompt,
            "cranelisp REPL — type /help for help",
        ));
        let _ = writeln!(stdout, "{banner}");
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
    ///
    /// R13 (§10.3) styling — DOCUMENTED DEFERRAL (Wave-D2, /dev): the prompt is
    /// left PLAIN (not routed through the R13 dim seam) because of rustyline
    /// prompt handling. This string is (a) passed verbatim to `rustyline::readline`
    /// on the TTY branch and (b) its byte length is the alignment width for
    /// `continuation_prompt_string`. Wrapping it in R13-dim SGR under colour-ON
    /// would inflate that `.len()` and mis-align the continuation `...`, and the
    /// interactive line-editor surface has NO e2e guard (§10.8 — arrow keys /
    /// cursor positioning are manually verified only), so a width regression here
    /// would ship unguarded. Styling the prompt cleanly requires also making the
    /// continuation width measure the ANSI-stripped length — a coupled change on an
    /// untestable surface, deferred rather than risked. Colour-OFF (the non-TTY
    /// harness) is unaffected: the prompt is already plain there.
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
}


#[cfg(test)]
pub(crate) mod test_support {
    use super::*;
    use crate::session_v4::{RunMode, SessionSettings};
    use cranelisp_types::{CodegenBehaviour, UserFnState, Visibility};
    use std::collections::HashMap as StdHashMap;
    pub(crate) fn session() -> CompilerSession {
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
    pub(crate) fn int_fn_scheme() -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: StdHashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        }
    }
    pub(crate) fn userfn_def(doc: Option<&str>) -> ModuleEntry<Code> {
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
    pub(crate) fn install_m(s: &CompilerSession, doc: Option<&str>) {
        let m = ModuleFullPath::from("m");
        let mut table = SessionSymbolTable::new_with_params(m.clone());
        table.insert(Symbol::from("mf"), userfn_def(doc));
        s.shared.symbol_tables.insert(m, table);
    }
    /// Install a nullary constructor `Red` of the multi-ctor sum type
    /// `(deftype Color Red Green Blue)` into `user`, under BOTH the S109
    /// canonical dotted key `Color.Red` (the terminal ctor `Def`) and the bare
    /// alias `Red` (an `Import` edge), mirroring how the typechecker registers a
    /// sum ctor. Returns the terminal ctor `Def` entry.
    pub(crate) fn install_color_red(s: &CompilerSession) -> ModuleEntry<Code> {
        use cranelisp_types::{FQTypeName, TypeDefInfo, TypeName};
        let user = s.current_module_path();
        let fqtn = FQTypeName::new(user.clone(), TypeName::from("Color"));
        let info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: Vec::new(),
            // Multi-ctor sum ⇒ `format_ctor_display` KEEPS the `Color.` prefix
            // (the doubling-prone case, unlike a single-ctor product).
            constructors: vec![Symbol::from("Red"), Symbol::from("Green"), Symbol::from("Blue")],
        };
        let ctor = ModuleEntry::def(
            Scheme {
                type_vars: Vec::new(),
                constraints: StdHashMap::new(),
                ty: Type::ADT(fqtn.clone(), Vec::new()),
            },
            DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn,
                tag: 0,
                field_count: 0,
                internal: false,
                type_def: Some(Box::new(info)),
                mode_summary: None,
            },
        )
        .visibility(Visibility::Public)
        .build();
        let alias = ModuleEntry::Import {
            source: cranelisp_types::FQSymbol {
                module: user.clone(),
                symbol: Symbol::from("Color.Red"),
            },
            visibility: Visibility::Public,
        };
        if let Some(mut table) = s.shared.symbol_tables.get_mut(&user) {
            table.insert(Symbol::from("Color.Red"), ctor.clone());
            table.insert(Symbol::from("Red"), alias);
        } else {
            let mut table = SessionSymbolTable::new_with_params(user.clone());
            table.insert(Symbol::from("Color.Red"), ctor.clone());
            table.insert(Symbol::from("Red"), alias);
            s.shared.symbol_tables.insert(user.clone(), table);
        }
        ctor
    }
    // -----------------------------------------------------------------------
    // S108 Increment 3 — resolve-home-enumeration.md §5 (0558) + §5a (E8).
    // -----------------------------------------------------------------------

    /// A `TraitDecl` entry with `name`/`visibility`, no methods.
    pub(crate) fn trait_decl_entry(name: &str, vis: Visibility) -> ModuleEntry<Code> {
        ModuleEntry::TraitDecl {
            info: cranelisp_types::TraitDeclInfo {
                name: cranelisp_types::TraitName::from(name),
                type_params: vec![],
                methods: vec![],
            },
            visibility: vis,
            docstring: None,
        }
    }
    /// A `TraitImpl` entry `impl <trait> <type>` written to `home` (Decision 0045).
    pub(crate) fn impl_entry(home: &ModuleFullPath, trait_name: &str, type_name: &str) -> ModuleEntry<Code> {
        ModuleEntry::TraitImpl {
            trait_name: cranelisp_types::FQTraitName::new(
                home.clone(),
                cranelisp_types::TraitName::from(trait_name),
            ),
            impl_type: cranelisp_types::FQTypeName::new(
                home.clone(),
                cranelisp_types::TypeName::from(type_name),
            ),
            // S110 W0.1b: this fixture models a same-module impl (shell + method
            // bodies co-located at `home`), so `impl_module == home`.
            impl_module: home.clone(),
            methods: vec![],
            visibility: Visibility::Public,
        }
    }
    /// A user-fn `Def` with an explicit visibility (the public `userfn_def`
    /// helper's private-head sibling — for the prelude public-only gate tests).
    pub(crate) fn userfn_def_vis(vis: Visibility) -> ModuleEntry<Code> {
        match userfn_def(None) {
            ModuleEntry::Def { scheme, docstring, param_names, kind, callees, trait_origin, seq, ast, codegen_view, code, value_use, .. } => {
                ModuleEntry::Def { scheme, visibility: vis, docstring, param_names, kind, callees, trait_origin, seq, ast, codegen_view, code, value_use }
            }
            other => other,
        }
    }
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
mod prelude_fallback_tests {
    use super::*;
    
    
    use crate::repl::test_support::*;
    
    use cranelisp_types::{
        ModuleFullPath,
        Symbol, Visibility,
    };
    

    // §8.8.1 gate: the prelude provides only its PUBLIC names, so the
    // prelude-fallback seam MUST NOT return a PRIVATE prelude head — it falls
    // through (to the root tier, else `None`). Fail-on-revert: drop the
    // `is_public()` gate and the private head leaks as `Some`, failing this.
    // spec: spec/08-modules.md §8.8.1
    #[test]
    fn lookup_prelude_fallback_drops_private_head() {
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let scope = s.current_module_path();
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(Symbol::from("secret"), userfn_def_vis(Visibility::Private));
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        s.shared.prelude_fallback.insert(scope, true);

        // Two-tier (the display hop) — a private prelude head is NOT in scope.
        assert!(
            s.lookup_with_prelude_fallback_opt("secret", false).is_none(),
            "a PRIVATE prelude head MUST NOT resolve through the fallback (§8.8.1)"
        );
        // Three-tier (describe/`/sig`/`/search`) — the private head still does
        // not resolve; it falls through the root tier (which lacks `secret`).
        assert!(
            s.lookup_with_prelude_fallback_opt("secret", true).is_none(),
            "a PRIVATE prelude head MUST NOT resolve even with the root tier"
        );
    }
    // §8.8.1 positive: a PUBLIC prelude head still resolves through the
    // fallback, in the prelude module (unchanged behaviour — the gate only
    // drops private heads). spec: spec/08-modules.md §8.8.1
    #[test]
    fn lookup_prelude_fallback_resolves_public_head() {
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let scope = s.current_module_path();
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(Symbol::from("shown"), userfn_def_vis(Visibility::Public));
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        s.shared.prelude_fallback.insert(scope, true);

        let hit = s.lookup_with_prelude_fallback_opt("shown", false);
        assert!(hit.is_some(), "a PUBLIC prelude head MUST resolve through the fallback");
        assert_eq!(
            hit.unwrap().1,
            prelude,
            "the public prelude head resolves IN the prelude module"
        );
    }
}
