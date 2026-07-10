// agent/pull.rs — pull-as-visible-commands (design/int/agent.md §4, the keystone).
//
// A pull is the agent issuing a REPL command on the user's behalf. The model's
// "tools" are EXACTLY a small read-only subset of REPL commands (§4.2): there is
// NO private tool registry — the pull surface IS `dispatch_command`. A tool-call
// is synthesized into a command STRING (e.g. `/source foo`), run through the
// SAME `process_commands` path a keystroke uses, rendered as-if-typed, and its
// result fed back to the model.
//
// Safety: the allowlist is the consent gate (§4.2). In read-only Advise mode the
// agent CANNOT synthesize a write — `synthesize_command` rejects any command not
// in the read-only set, rendering a refusal rather than running it. This is how
// "auto-approve reads only" (§7.4) is structurally enforced this wave: writes are
// unconstructable.

#![cfg(feature = "agent")]

use std::io::Write;

use crate::agent::types::{
    AgentRequest, ConsentReader, ModelResponse, ToolCallRequest, ToolCallResult, ToolDef,
};
use crate::session_v4::{CommandResult, CompilerSession};

/// The Build write tool (`design/int/agent.md §15.1`, S89 Cluster B). The ONE
/// writing tool — it carries a form string (e.g. `(defn double [x] (* x 2))`) as
/// its argument and is routed, not through the read-only `synthesize_command`
/// allowlist, but through the confirm-gated `run_submit` write arm (§15.2). This
/// is the single allowlist widening (§15.1): one new branch at the `run_pull`
/// head; the read-only floor (`synthesize_command`) is byte-unchanged.
pub(crate) const SUBMIT_TOOL: &str = "submit";

/// The Document write tools (`design/int/agent.md §17.2`, S89 Cluster C). The
/// agent records durable understanding into the code itself ("memory is the
/// code", §17.3): `set-preamble <module> <text>` records a module preamble;
/// `set-doc <symbol> <text>` records a definition's docstring. Both route — like
/// `submit` — through a gated write arm (`run_document_edit`), NOT the read-only
/// `synthesize_command` allowlist. The discriminator is the tool NAME (§17.2): a
/// `submit` is code (the Build CONFIRM gate); a `set-preamble`/`set-doc` is
/// documentation (the Document CONSULTATIVE gate) — distinct wording, same `--yes`
/// blanket auto-accept (§20.2).
///
/// PERSISTENCE (FIXME 0430, RATIFIED S94 — `session-persistence.md §11.3a`): a
/// `set-doc` docstring is now durable across restart. `apply_docstring_edit` sets
/// the live `ModuleEntry::Def.docstring` (authoritative), and the docstring-aware
/// `save::render_decl_sexp` re-emits it into the §5.12 slot on regen — the same
/// "regen reads the live field" shape `set-preamble` uses for the module preamble.
pub(crate) const SET_PREAMBLE_TOOL: &str = "set-preamble";
pub(crate) const SET_DOC_TOOL: &str = "set-doc";

/// Cap on the silent pre-flight repair loop (`design/int/agent.md §16.3`). On
/// exhaustion the agent gives up gracefully — it NEVER submits broken code and
/// never surfaces a raw compiler error (U5, §16.4).
const MAX_REPAIR_ITERATIONS: usize = 3;

/// The read-only command allowlist (§4.2) — the ONLY tools the agent may emit.
/// Each entry is `(tool-name, leading-slash command, one-line description)`. The
/// `slash` is the actual command word `process_commands` dispatches; `name` is
/// what the model emits as a tool call. They are the same word here (no slash on
/// the model side). Writes / `/sh` / submit are deliberately ABSENT — they are
/// unconstructable in read-only Advise mode (the MVP consent boundary).
const ALLOWLIST: &[(&str, &str)] = &[
    ("source", "Show the source of a defined symbol: source <name>"),
    ("sexp", "Show the parsed s-expression of a symbol: sexp <name>"),
    ("info", "Show a symbol's type, kind, and related info: info <name>"),
    ("sig", "Show a symbol's type signature: sig <name>"),
    ("doc", "Show a symbol's (or module's) docstring: doc <name>"),
    ("type", "Show the inferred type of an expression: type <expr>"),
    ("imports", "List the current module's imports: imports"),
    ("exports", "List a module's exports: exports <module>"),
    ("list", "List symbols in scope: list"),
    ("refs", "List definitions whose body references a symbol: refs <name>"),
    (
        "tests-for",
        "List test functions referencing a symbol: tests-for <name>",
    ),
    (
        "syntax",
        "Show core-language syntax: bare for topics, syntax <topic> for detail",
    ),
    (
        "search",
        "Find an importable-but-unimported symbol by name or type: search <name-or-scheme>",
    ),
];

/// The tool definitions offered to the model in every request (§4.2, §6.1).
/// Built from the allowlist so the model is told exactly the read-only command
/// surface — and nothing else.
pub fn tool_defs() -> Vec<ToolDef> {
    let mut defs: Vec<ToolDef> = ALLOWLIST
        .iter()
        .map(|(name, desc)| ToolDef {
            name: (*name).to_string(),
            description: (*desc).to_string(),
        })
        .collect();
    // The ONE write tool (§15.1, Build mode). It is always offered but always
    // confirm-gated — the gate, not the offer, is the consent boundary (§15.1):
    // a `submit` that is not confirmed mutates nothing. Reads stay auto-run; the
    // read-only `ALLOWLIST` floor above is untouched.
    defs.push(ToolDef {
        name: SUBMIT_TOOL.to_string(),
        description: "Submit a definition to the session (confirm-gated write): \
                      submit <form>"
            .to_string(),
    });
    // The Document write tools (§17.2, Cluster C) — consultative-gated, always
    // offered but never auto-run. They record durable understanding (a module
    // preamble / a definition docstring) into the source itself.
    defs.push(ToolDef {
        name: SET_PREAMBLE_TOOL.to_string(),
        description: "Record a module's preamble — durable documentation written \
                      into the source (consultative-gated write): \
                      set-preamble <module> <text>"
            .to_string(),
    });
    defs.push(ToolDef {
        name: SET_DOC_TOOL.to_string(),
        description: "Record a definition's docstring — durable documentation \
                      written into the source (consultative-gated write): \
                      set-doc <symbol> <text>"
            .to_string(),
    });
    defs
}

/// Is `name` (a bare tool/command word) in the read-only allowlist?
fn is_allowed(name: &str) -> bool {
    ALLOWLIST.iter().any(|(n, _)| *n == name)
}

/// Synthesize a REPL command STRING from a model tool-call, enforcing the
/// read-only allowlist (§4.2). Returns:
///   - `Ok(cmd_string)` — an allowed command, e.g. `"/source foo"`.
///   - `Err(refusal)` — a non-read command: a refusal notice (never a command).
///
/// A command not in the allowlist (a write, `/sh`, a `(defn …)` submission, or
/// any unknown name) is REFUSED at synthesis — the agent's capability surface is
/// the allowlist, so a write is structurally unconstructable (the consent gate).
pub fn synthesize_command(call: &ToolCallRequest) -> Result<String, String> {
    let name = call.name.trim().trim_start_matches('/');
    if !is_allowed(name) {
        return Err(format!(
            "agent attempted a non-read command '{}' — refused (read-only Advise mode)",
            call.name
        ));
    }
    let arg = call.argument.trim();
    if arg.is_empty() {
        Ok(format!("/{name}"))
    } else {
        Ok(format!("/{name} {arg}"))
    }
}

impl CompilerSession {
    /// Run a single model tool-call as a visible REPL command (§4.1).
    ///
    /// Synthesizes the command (allowlist-gated), runs it through the SAME
    /// `process_commands` path a keystroke uses, renders it as-if-typed to
    /// `stdout`, and returns the `ToolCallResult` to feed back to the model. A
    /// refused (non-read) command renders the refusal and feeds it back as the
    /// result — nothing is executed.
    pub(crate) fn run_pull(
        &mut self,
        call: &ToolCallRequest,
        stdout: &mut impl Write,
        consent: &mut dyn ConsentReader,
    ) -> ToolCallResult {
        // §15.1 — the SINGLE allowlist widening: a `submit` tool-call routes to
        // the confirm-gated write arm; everything else falls through to the
        // read-only `synthesize_command` path verbatim (the read-only floor is
        // untouched). A non-`submit` write / `/sh` / unknown name still hits the
        // read-only refusal below WITHOUT any confirm gate (the B.2 floor).
        let tool = call.name.trim().trim_start_matches('/');
        if tool == SUBMIT_TOOL {
            return self.run_submit(call, stdout, consent);
        }
        // §17.2 — the Document write tools route to the CONSULTATIVE gate arm
        // (sibling to `run_submit`'s confirm gate). The tool NAME is the
        // discriminator; both stay out of the read-only `synthesize_command`
        // allowlist (the §15.4 floor extends to Document writes).
        if tool == SET_PREAMBLE_TOOL || tool == SET_DOC_TOOL {
            return self.run_document_edit(call, stdout, consent);
        }
        match synthesize_command(call) {
            Err(refusal) => {
                // Render the refusal in normal REPL style (it is deterministic
                // output, not agent prose — §3.5). Fed back so the model sees it
                // was denied.
                let _ = writeln!(stdout, "{refusal}");
                ToolCallResult {
                    id: call.id.clone(),
                    command: format!("(refused: {})", call.name),
                    output: refusal,
                }
            }
            Ok(cmd) => {
                // Echo the command behind the agent-input prompt glyph (§14.2)
                // so the transcript reads honestly: who typed what. The command
                // itself renders in NORMAL REPL style (§4.4, §3.5 — agent
                // commands are not prose, so only the prompt is marked, not the
                // body framed). One prefix fn (`render::agent_input_prefix`) is
                // shared with the S89 Build-submit echo so they cannot diverge.
                let _ = writeln!(stdout, "{}{cmd}", crate::agent::render::agent_input_prefix());
                // Run through the SAME path a keystroke uses. Read-only commands
                // return `Final(text)` (or `Nothing`); a read can never reach the
                // `Compile` arm (the allowlist excludes eval/write).
                let result = self.process_commands(&cmd, stdout);
                let output = match result {
                    CommandResult::Final(text) => {
                        // §14.6 ANSI-leak fix (S89 Phase-6). A styled REPL command
                        // (`/source` etc.) returns SGR-coloured text when colour is
                        // on. The USER echo keeps that text verbatim — well-formed
                        // colour on a TTY, plain under `--no-color` (the one global
                        // `style::is_color_enabled` gate already decided it). But
                        // the MODEL-fed copy MUST be clean plain text: shipping raw
                        // SGR to the provider leaks mangled `1m`/`0m` fragments back
                        // into the displayed reply (the ESC byte is dropped in
                        // transport). So we strip ANSI from the fed-back `output`
                        // ONLY — render once, feed clean.
                        let _ = writeln!(stdout, "{text}");
                        crate::style::strip_ansi(&text)
                    }
                    CommandResult::Nothing => String::new(),
                    // A read-only command cannot produce these. Guard defensively
                    // so a future allowlist mistake fails closed (no eval).
                    CommandResult::Compile(_) | CommandResult::Quit => {
                        let msg = "(command produced no readable result)".to_string();
                        let _ = writeln!(stdout, "{msg}");
                        msg
                    }
                };
                // Pillar 4 (§27.1) — silent greppable log of this exploration pull
                // (the read command word + its argument). Off unless
                // `CRANELISP_AGENT_LOG` is set; never touches stdout.
                let pull_arg = call.argument.trim();
                let mut ev = crate::agent::log::LogEvent::new("pull")
                    .turn(self.agent_current_turn())
                    .tool(tool);
                if !pull_arg.is_empty() {
                    ev = ev.symbol(pull_arg);
                }
                crate::agent::log::record(ev);
                ToolCallResult {
                    id: call.id.clone(),
                    command: cmd,
                    output,
                }
            }
        }
    }

    /// The confirm-gated Build write arm (`design/int/agent.md §15.2`, S89). The
    /// single write site:
    ///   1. **Validate + silently repair** the proposed form (§16). The broken
    ///      intermediate + any compiler error NEVER reach `stdout` — only a clean
    ///      form proceeds (U5 silent contract). On give-up, render an honest
    ///      not-submitted notice and feed a declined result back.
    ///   2. **Render** the (clean) proposed form behind the agent-input prefix
    ///      (§15.2 step 1) — always shown, even under `--yes` (§20.2).
    ///   3. **Capture consent**: `--yes` auto-accepts (§20.2, the once-notice
    ///      fires here); else a blocking `[y/N]` line-read (default-decline).
    ///   4. **On confirm**, route the form through `process_commands`→`eval`→regen
    ///      — the SAME staging path a keystroke uses (§15.3, R3: no new eval
    ///      entry). **On decline**, write nothing; feed a "declined" result back.
    fn run_submit(
        &mut self,
        call: &ToolCallRequest,
        stdout: &mut impl Write,
        consent: &mut dyn ConsentReader,
    ) -> ToolCallResult {
        // (1) Validate + silently repair. The repair loop runs BEFORE any echo —
        // "the user structurally cannot see an agent compile failure" (§16.2) is
        // enforced by where the render call is: render happens only after this
        // returns Ok(clean_form). The submit tool_use `id` is threaded in so the
        // compiler-error feedback is recorded as a `tool_result` PAIRED with this
        // tool_use (NOT a bare user turn) — the Anthropic Messages API requires
        // every `tool_use` block to be immediately followed by its matching
        // `tool_result`, and the outer loop (`mod.rs`) already recorded this
        // submit as an assistant `tool_use` turn but pairs the OUTER tool_result
        // only AFTER `run_submit` returns. Without pairing here, the repair
        // request assembled mid-handling ends `…tool_use(submit), user(feedback)`
        // — an unpaired tool_use → live 400 (Phase-6 defect).
        let (clean, final_tool_use_id) = match self.validate_and_repair(&call.argument, &call.id) {
            Ok(pair) => pair,
            Err(give_up_id) => {
                // Give-up (§16.4): never submit broken code, never surface a raw
                // compiler error. The MODEL receives an honest abort (the fed-back
                // `tool_result` below) so it can adapt and re-submit, but the
                // user-facing "I couldn't produce a definition" line is NOT printed
                // here (Phase-6 fix, S89). A per-failed-submit give-up line is FALSE
                // mid-turn: the turn may CONTINUE and ultimately submit cleanly (the
                // live trace — fib was defined after the first submit's repair cap
                // exhausted). The line is deferred to TRUE turn-end (`agent_turn`),
                // emitted at most once and only if the turn produced no committed
                // write and no answer. Here we only RECORD that a submit gave up.
                if let Some(state) = self.agent.as_mut() {
                    state.submit_gave_up = true;
                }
                // Pillar 4 (§27.1) — silent greppable log of the submit give-up
                // (the struggled-over symbol + module). Off unless the env is set.
                crate::agent::log::record({
                    let mut ev = crate::agent::log::LogEvent::new("give_up")
                        .turn(self.agent_current_turn())
                        .module(self.current_module_path().as_ref());
                    if let Some(sym) = crate::agent::log::defined_symbol(&call.argument) {
                        ev = ev.symbol(sym);
                    }
                    ev
                });
                // PAIRING (Phase-6 give-up corner, the CURRENT 400): the repair
                // loop has recorded a chain of `submit` tool_use turns onto the
                // transcript, the LAST of which is UNPAIRED (its error feedback
                // was the prompt that exhausted the cap). The give-up tool_result
                // the OUTER loop records MUST pair against THAT last tool_use id
                // (`give_up_id`), NOT the original `call.id` — else the transcript
                // ends `…tool_use(repair-N), tool_result(orig)` and the NEXT
                // request 400s ("unexpected tool_use_id … no corresponding
                // tool_use"). When the loop never recorded a repair tool_use (the
                // first form was broken but NO repair tool_use was emitted, e.g. a
                // prose-only repair), `give_up_id` falls back to `call.id` — the
                // outer submit's own tool_use, which IS the last unpaired one.
                let result_id = give_up_id.unwrap_or_else(|| call.id.clone());
                return ToolCallResult {
                    id: result_id,
                    command: format!("(submit gave up: {})", call.name),
                    output: "submit aborted: could not produce compiling code".to_string(),
                };
            }
        };

        // (2) Render the proposed (clean) form behind the agent-input prefix —
        // always shown (§15.2 step 1 / §20.2 render-always), pretty-printed via
        // the SAME printer `/source`/`/sexp` use (Principle 7).
        let pretty = crate::pretty::pretty_print_str(clean.trim());
        let _ = writeln!(
            stdout,
            "{}{}",
            crate::agent::render::agent_input_prefix(),
            pretty.trim_end()
        );

        // (3) Capture consent. `--yes` short-circuits the prompt-read ONLY (§20.2);
        // the render above + the commit below are byte-identical either way.
        let consented = if self.agent_auto_accept() {
            // §20.4 first-use notice — once per session, before the first
            // auto-accepted write of either class.
            self.fire_auto_accept_notice_once(stdout);
            true
        } else {
            let _ = write!(stdout, "submit this definition? [y/N] ");
            let _ = stdout.flush();
            match consent.read_consent_line() {
                Some(line) => {
                    let a = line.trim().to_ascii_lowercase();
                    a == "y" || a == "yes"
                }
                None => false, // EOF ⇒ decline (the safe default)
            }
        };

        // The id the OUTER `agent_turn` loop will pair its recorded tool_result
        // against: the LAST recorded `submit` tool_use (the last repair's id when a
        // repair produced the clean form; the original `call.id` when the form was
        // clean first-try OR the final form came via prose — `None`). Pairing the
        // outer result against `call.id` unconditionally would, after a repair,
        // leave the transcript ending `…tool_use(repair-id), tool_result(orig-id)`
        // and 400 the NEXT (post-submit) request (the residual Phase-6 corner).
        let result_id = final_tool_use_id.unwrap_or_else(|| call.id.clone());

        if !consented {
            // §15.2 step 3 — decline: write nothing, feed "declined" back.
            return ToolCallResult {
                id: result_id,
                command: "(submit declined)".to_string(),
                output: "the user declined to submit this definition".to_string(),
            };
        }

        // (4) Confirm — route through the EXISTING process_commands→eval→regen
        // staging chain (§15.3, R3). Structurally the same caller `main.rs` is.
        self.submit_clean_form(&clean, &result_id, stdout)
    }

    /// Drive the confirmed clean form through `process_commands`→`eval`→regen
    /// (§15.3). On `Compile(src)` it evals (mirroring `main.rs:315`), renders the
    /// `:Type name` confirmation unframed (normal REPL output), regenerates the
    /// backing file on a successful def, and feeds the result back to the model.
    ///
    /// `result_id` is the tool_use id the OUTER loop's `record_tool_result` must
    /// pair against — the ACTUAL submitted tool_use (the last repair, or the
    /// original `call.id`), so the post-submit continuation request stays
    /// well-formed (Phase-6 residual corner).
    fn submit_clean_form(
        &mut self,
        clean: &str,
        result_id: &str,
        stdout: &mut impl Write,
    ) -> ToolCallResult {
        match self.process_commands(clean, stdout) {
            CommandResult::Compile(src) => match self.eval(&src) {
                Ok(Some(result)) => {
                    let text = self.format_eval_result(&result);
                    let _ = writeln!(stdout, "{text}");
                    // Genuine definitions only (F6) — the P8 mirror of the
                    // main.rs regen gate: a display-only bare-lookup Def must
                    // not rewrite the backing file.
                    if result.is_defining() {
                        self.regenerate_backing_file();
                    }
                    // The turn "produced something": a committed submit suppresses
                    // the end-of-turn give-up line (Phase-6, S89), even if an
                    // EARLIER submit this turn gave up.
                    if let Some(state) = self.agent.as_mut() {
                        state.submit_committed = true;
                    }
                    // Pillar 4 (§27.1) — silent greppable log of the committed
                    // submit (the defined symbol + module). Off unless env is set.
                    crate::agent::log::record({
                        let mut ev = crate::agent::log::LogEvent::new("submit")
                            .turn(self.agent_current_turn())
                            .module(self.current_module_path().as_ref());
                        if let Some(sym) = crate::agent::log::defined_symbol(clean) {
                            ev = ev.symbol(sym);
                        }
                        ev
                    });
                    ToolCallResult {
                        id: result_id.to_string(),
                        command: format!("submit {clean}"),
                        output: text,
                    }
                }
                Ok(None) => ToolCallResult {
                    id: result_id.to_string(),
                    command: format!("submit {clean}"),
                    output: "(submitted)".to_string(),
                },
                // The validator already proved this typechecks; an eval error
                // here is unexpected, but surface it as a fed-back result (NOT a
                // crash) rather than swallowing it.
                Err(e) => ToolCallResult {
                    id: result_id.to_string(),
                    command: format!("submit {clean}"),
                    output: format!("submit failed at eval: {e}"),
                },
            },
            // A submit that did not produce a Compile (e.g. blank) — nothing to do.
            CommandResult::Final(text) => ToolCallResult {
                id: result_id.to_string(),
                command: format!("submit {clean}"),
                output: text,
            },
            CommandResult::Nothing | CommandResult::Quit => ToolCallResult {
                id: result_id.to_string(),
                command: format!("submit {clean}"),
                output: "(submitted)".to_string(),
            },
        }
    }

    /// The consultative-gated Document write arm (`design/int/agent.md §17.2`,
    /// S89 Cluster C). The Document twin of `run_submit`, distinguished by the
    /// tool NAME (§17.2): a `set-preamble`/`set-doc` is documentation, not code,
    /// so it asks the CONSULTATIVE question ("record this as <X>'s preamble?")
    /// rather than the Build confirm ("submit this definition?"). No validator —
    /// a doc edit is not code (the validator is Build-only). The arm:
    ///   1. Parse the argument: `<TARGET> <TEXT>` split on the FIRST whitespace.
    ///   2. **Render** the proposed canonical `;;` block (set-preamble) / the
    ///      docstring (set-doc) — always shown, even under `--yes` (§17.15.2a).
    ///   3. **Capture consent**: `--yes` auto-accepts (§20.2, blanket — the same
    ///      once-notice as Build); else the consultative `[y/N]` line-read.
    ///   4. **On confirm**, apply: `set-preamble` → `save::apply_preamble_edit`
    ///      (field set) + byte-stable section-0 regen; `set-doc` → set the
    ///      symbol's live docstring + regen (docstring-aware `render_decl_sexp`
    ///      persists it, FIXME 0430). **On decline**, write nothing.
    fn run_document_edit(
        &mut self,
        call: &ToolCallRequest,
        stdout: &mut impl Write,
        consent: &mut dyn ConsentReader,
    ) -> ToolCallResult {
        let tool = call.name.trim().trim_start_matches('/');
        let is_preamble = tool == SET_PREAMBLE_TOOL;
        let noun = if is_preamble { "preamble" } else { "docstring" };

        // (1) Parse `<TARGET> <TEXT>` — split on the FIRST run of whitespace.
        let arg = call.argument.trim();
        let mut parts = arg.splitn(2, char::is_whitespace);
        let target = parts.next().unwrap_or("").trim().to_string();
        let text = parts.next().unwrap_or("").trim().to_string();
        if target.is_empty() || text.is_empty() {
            let msg = format!(
                "agent {tool} needs a target and text ({tool} <{}> <text>) — nothing recorded",
                if is_preamble { "module" } else { "symbol" }
            );
            let _ = writeln!(stdout, "{msg}");
            return ToolCallResult {
                id: call.id.clone(),
                command: format!("({tool} malformed)"),
                output: msg,
            };
        }

        // (2) Render the EXACT proposed documentation — the canonical `;;` block
        // for a preamble (via the shared `generate_preamble` emitter, §17.2), the
        // raw prose for a docstring. Always shown (§17.15.2a render-always),
        // behind the agent-input prefix so the transcript reads honestly.
        let shown = if is_preamble {
            crate::save::render_preamble_block(&text)
        } else {
            text.clone()
        };
        let _ = writeln!(
            stdout,
            "{}{}",
            crate::agent::render::agent_input_prefix(),
            shown
        );

        // (3) Capture consent. `--yes` is BLANKET (§20.2): it auto-accepts the
        // CONSULTATIVE gate exactly as it auto-accepts the Build confirm — the
        // consultative question is then SUPPRESSED, not asked-then-answered.
        let consented = if self.agent_auto_accept() {
            self.fire_auto_accept_notice_once(stdout);
            true
        } else {
            // The CONSULTATIVE wording — distinct from the Build `[y/N]` confirm
            // ("submit this definition?"). Tool-name discrimination surfaces here.
            let _ = write!(stdout, "record this as {target}'s {noun}? [y/N] ");
            let _ = stdout.flush();
            match consent.read_consent_line() {
                Some(line) => {
                    let a = line.trim().to_ascii_lowercase();
                    a == "y" || a == "yes"
                }
                None => false, // EOF ⇒ decline (the safe default)
            }
        };

        if !consented {
            // §17.15.2 decline: write nothing, feed "declined" back. No regen.
            return ToolCallResult {
                id: call.id.clone(),
                command: format!("({tool} declined)"),
                output: format!("the user declined to record this {noun}"),
            };
        }

        // (4) Confirm — apply the durable, byte-stable edit + regen. A docstring
        // edit can fail HONESTLY (no such definition / non-persisting target):
        // surface the error and DO NOT claim "recorded" (the embedded agent would
        // otherwise believe it persisted a docstring that silently vanished).
        let outcome = if is_preamble {
            self.apply_preamble_edit(&target, &text);
            Ok(())
        } else {
            self.apply_docstring_edit(&target, &text)
        };
        match outcome {
            Ok(()) => {
                let _ = writeln!(stdout, "recorded {target}'s {noun}");
                ToolCallResult {
                    id: call.id.clone(),
                    command: format!("{tool} {target}"),
                    output: format!("recorded {target}'s {noun}"),
                }
            }
            Err(msg) => {
                let _ = writeln!(stdout, "{msg}");
                ToolCallResult {
                    id: call.id.clone(),
                    command: format!("({tool} no-op)"),
                    output: msg,
                }
            }
        }
    }

    /// Apply a Document-mode preamble edit (`design/int/agent.md §17.1`): set the
    /// module's `module_preamble` field to the stripped prose + regenerate the
    /// backing file byte-stably (the §8.16.5 section-0 round-trip). The TARGET is
    /// a module name; it resolves to a full path (the current-module short name,
    /// or a literal full path). The edit is on the named module's table; regen
    /// runs against the current module's backing file (the named module is the
    /// current module in the MVP shape — §17.1).
    fn apply_preamble_edit(&mut self, module: &str, text: &str) {
        let module_path = self.resolve_document_module(module);
        crate::save::apply_preamble_edit(&self.shared.symbol_tables, &module_path, text);
        self.regenerate_backing_file();
    }

    /// Apply a Document-mode docstring edit (`design/int/agent.md §17.2`, FIXME
    /// 0430): set the live `ModuleEntry::Def.docstring` for the named symbol +
    /// regenerate. The live field is the AUTHORITATIVE docstring (§11.3a); the
    /// docstring-aware `save::render_decl_sexp` re-emits it into the §5.12 slot on
    /// regen so the edit survives a session restart (read back by `/doc <symbol>`).
    ///
    /// HONESTY GUARDS (`/review` S94): only a LOCAL `UserFn` `Def` in the current
    /// module persists across restart, so this refuses anything else rather than
    /// printing a false "recorded" — returning `Err(message)`:
    ///   - a symbol absent from the current module's table (covers a re-exported
    ///     `Import`, a non-`Def` entry, AND a qualified `mod/sym` whose key never
    ///     matches a local symbol) ⇒ `no such definition`;
    ///   - a `Def` that is not a `UserFn` (a `PrimitiveExtern`/`Constructor`/…) ⇒
    ///     refused, because `save::generate_fns_and_macros` only threads docstrings
    ///     for `UserFn` (other kinds hit `_ => continue`), so the field would show
    ///     via `/doc` in-session yet VANISH on restart — an ephemeral, dishonest
    ///     "recorded". On any refusal the backing file is NOT regenerated.
    fn apply_docstring_edit(&mut self, symbol: &str, text: &str) -> Result<(), String> {
        let module = self.current_module_path();
        let sym = cranelisp_types::Symbol::from(symbol);
        {
            let Some(mut table) = self.shared.symbol_tables.get_mut(&module) else {
                return Err(format!("no such definition: {symbol}"));
            };
            match table.symbols.get_mut(&sym) {
                Some(cranelisp_types::ModuleEntry::Def { kind, docstring, .. }) => {
                    if !matches!(kind.as_ref(), cranelisp_types::DefKind::UserFn { .. }) {
                        return Err(format!(
                            "cannot record a docstring on '{symbol}': only function \
                             definitions persist a docstring across restart"
                        ));
                    }
                    *docstring = Some(text.to_string());
                }
                // Absent, or present but not a local `Def` (Import / TypeDef / …).
                _ => return Err(format!("no such definition: {symbol}")),
            }
        }
        self.regenerate_backing_file();
        Ok(())
    }

    /// Resolve a Document-edit module TARGET to a full path. A bare short name
    /// that equals the current module's short name maps to the current module;
    /// otherwise it is treated as a literal full path (the harvester reads back
    /// by the same key, §17.3).
    ///
    /// MVP LIMITATION: only the CURRENT module's preamble persists across restart
    /// — `regenerate_backing_file` regenerates the current module's backing file
    /// only, so a preamble written onto a NON-current target table is live this
    /// session but is not written to disk. A multi-module Document edit is a future
    /// increment.
    fn resolve_document_module(&self, module: &str) -> cranelisp_types::ModuleFullPath {
        let current = self.current_module_path();
        if current.as_ref() == module {
            current
        } else {
            cranelisp_types::ModuleFullPath::from(module)
        }
    }

    /// The silent pre-flight validator + repair loop (`design/int/agent.md §16.2`,
    /// U5). Stages → checks → DISCARDS the proposed form (`validate_forms_dry_run`,
    /// §16.1 — never commits). On ANY `Err` (parse OR type — no classification),
    /// feeds the actual compiler error back to the model and re-prompts SILENTLY
    /// (the broken text never reaches `stdout`). Capped at `MAX_REPAIR_ITERATIONS`;
    /// on exhaustion returns `Err(())` (the give-up — §16.4). Returns the FIRST
    /// form string that validates clean.
    ///
    /// §20.3 (binding): takes NO `auto_accept` parameter and has no read path to
    /// it — the `--yes` flag cannot skip this validation floor.
    ///
    /// **Tool_use↔tool_result pairing (Phase-6 fix).** The outer `agent_turn` loop
    /// (`mod.rs`) already recorded the model's `submit` as an assistant `tool_use`
    /// turn (`record_assistant_tool_calls`) before invoking the pull, and only
    /// records the OUTER paired `tool_result` AFTER `run_submit` returns. So when
    /// this loop assembles its repair request mid-handling, the transcript's most
    /// recent unpaired turn is that `submit` tool_use. The compiler-error feedback
    /// MUST therefore be recorded as a `tool_result` referencing the submit
    /// tool_use `id` (`pending_tool_use`), NOT a bare user turn — else the request
    /// ends `…tool_use(submit), user(feedback)` and the Anthropic API 400s
    /// (unpaired tool_use). Each repair iteration that re-proposes via a fresh
    /// `submit` tool_use records ITS tool_use (`record_assistant_tool_calls`) and
    /// carries that new id forward, so the next error-feedback pairs against it. A
    /// repair that arrives as PROSE (no tool_use) records an assistant prose turn
    /// instead, and the following feedback is a plain user turn (no pairing owed —
    /// the prior turn was assistant prose). The invariant held at EVERY
    /// `assemble_request` call: every assistant `tool_use` turn is immediately
    /// followed by its matching `tool_result`.
    ///
    /// Returns `(clean_form, final_tool_use_id)`. `final_tool_use_id` is the id of
    /// the LAST `submit` tool_use recorded onto the transcript — the OUTER submit's
    /// id when the original form was clean, the LAST repair tool_use's id when a
    /// repair produced the clean form, or `None` when the clean form came via prose
    /// (no trailing tool_use). The caller (`run_submit`) MUST pair the OUTER
    /// success `tool_result` against THIS id, not the original `call.id` — else a
    /// repair leaves the transcript ending `…tool_use(repair-id), tool_result(orig-id)`,
    /// re-introducing the unpaired-tool_use 400 on the NEXT (post-submit) request.
    fn validate_and_repair(
        &mut self,
        initial_form: &str,
        submit_id: &str,
    ) -> Result<(String, Option<String>), Option<String>> {
        let mut form = initial_form.to_string();
        // The id of the tool_use whose form we are validating this iteration. When
        // `Some`, the next error-feedback is a PAIRED `tool_result`; when `None`
        // (the form arrived as prose, not a tool_use), the feedback is a plain user
        // turn. It starts as the outer submit's id (the form being validated now).
        let mut pending_tool_use: Option<String> = Some(submit_id.to_string());
        for iteration in 0..MAX_REPAIR_ITERATIONS {
            match self.validate_one_form(&form) {
                // The clean form's owning tool_use id (`pending_tool_use`) is
                // returned so the OUTER success tool_result pairs against the
                // ACTUAL submitted tool_use (the last repair, or the original).
                Ok(()) => return Ok((form, pending_tool_use)),
                Err(compiler_error) => {
                    // Pillar 4 (§27.1) — the KEYSTONE struggle signal: a silent
                    // greppable `repair` record carrying the struggled-over symbol,
                    // its module, the triggering compiler `error_class`, and the
                    // 1-based repair `iteration`. Off unless `CRANELISP_AGENT_LOG`
                    // is set; never touches stdout (the SILENT contract).
                    crate::agent::log::record({
                        // The `repair` record carries BOTH `turn` (the §28.2
                        // log↔trace correlation, distinct field) AND `iteration`
                        // (its own repair-loop count) — they no longer collide.
                        let mut ev = crate::agent::log::LogEvent::new("repair")
                            .turn(self.agent_current_turn())
                            .module(self.current_module_path().as_ref())
                            .error_class(crate::agent::log::classify_error(&compiler_error))
                            .iteration(iteration + 1);
                        if let Some(sym) = crate::agent::log::defined_symbol(&form) {
                            ev = ev.symbol(sym);
                        }
                        ev
                    });
                    // SILENT (§16.2): nothing rendered to the transcript. Record a
                    // HIDDEN repair turn on the agent state (so the next request has
                    // context) and re-prompt the model.
                    let feedback = format!(
                        "The code you proposed does not compile:\n{compiler_error}\n\
                         Reply with a corrected `submit` of the SAME definition that compiles."
                    );
                    // Record the feedback FIRST (paired as a tool_result when a
                    // tool_use is pending), THEN assemble — so the assembled
                    // request's last turn IS this feedback (the prompt the model
                    // answers) and the tool_use↔tool_result pairing holds.
                    if let Some(state) = self.agent.as_mut() {
                        match &pending_tool_use {
                            Some(id) => state.record_tool_result(ToolCallResult {
                                id: id.clone(),
                                command: format!("(submit {})", form),
                                output: feedback.clone(),
                            }),
                            None => state.record_user(&feedback),
                        }
                    }
                    let req = self.assemble_request(&feedback);
                    match self.agent_complete_for_repair(&req) {
                        Some(RepairResponse::ToolCall { id, argument }) => {
                            // The model re-proposed via a fresh `submit` tool_use —
                            // record ITS tool_use turn so the NEXT iteration's
                            // feedback pairs against it (the pairing invariant
                            // chains across iterations).
                            if let Some(state) = self.agent.as_mut() {
                                state.record_assistant_tool_calls(vec![ToolCallRequest {
                                    id: id.clone(),
                                    name: SUBMIT_TOOL.to_string(),
                                    argument: argument.clone(),
                                }]);
                            }
                            pending_tool_use = Some(id);
                            form = argument;
                        }
                        Some(RepairResponse::Prose { prose, form: next }) => {
                            // The model replied with prose (no tool_use). Record the
                            // assistant prose turn; the next feedback is a plain user
                            // turn (no pairing owed — prior turn is assistant prose).
                            if let Some(state) = self.agent.as_mut() {
                                state.record_assistant(&prose);
                            }
                            pending_tool_use = None;
                            form = next;
                        }
                        // No model / no extractable form: give up. At this point the
                        // feedback `tool_result` (or user turn) for THIS iteration
                        // was already recorded ABOVE, so any prior tool_use is
                        // paired — there is NO trailing unpaired tool_use. The
                        // returned `pending_tool_use` is only a HINT; `run_submit` +
                        // `record_pull_result` make the real wire-valid recording
                        // decision off the live transcript tail (a paired tail ⇒ the
                        // give-up outcome is carried as a benign user turn, not a
                        // spurious second tool_result).
                        None => return Err(pending_tool_use.clone()),
                    }
                }
            }
        }
        // Cap exhausted (the give-up the user observed). The LAST loop iteration
        // recorded a fresh `submit` tool_use (`record_assistant_tool_calls`) whose
        // error-feedback `tool_result` was NEVER recorded (the loop exited first) —
        // so `pending_tool_use` is the TRAILING UNPAIRED tool_use. `run_submit`
        // returns the give-up result with this id; `record_pull_result` then closes
        // the pairing with exactly one `tool_result` (the current 400 fix).
        Err(pending_tool_use.clone())
    }

    /// Validate one proposed form on staging (parse+expand half via
    /// `build_program_compat`, typecheck half via `validate_forms_dry_run`),
    /// always discarding (§16.1). Returns `Ok(())` clean, `Err(message)` on any
    /// parse OR type failure (U5 — no error-classification branch).
    fn validate_one_form(&self, form: &str) -> Result<(), String> {
        // Parse + macro-expand (the frontend half — a parse/expand failure is an
        // Err here, surfacing "parse OR type" uniformly, §16.1).
        let sexps = cranelisp_frontend::parse(form).map_err(|e| e.to_string())?;
        if sexps.is_empty() {
            return Ok(());
        }
        let program = crate::worker::build_program_compat(&sexps).map_err(|e| e.to_string())?;
        let module = self.current_module_path();
        crate::worker::validate_forms_dry_run(
            &self.shared.symbol_tables,
            &self.shared.module_aliases,
            &self.shared.prelude_fallback,
            &module,
            &program,
        )
        .map_err(|e| e.to_string())
    }

    /// Run one repair completion and extract the proposed form from the model's
    /// response. Returns `None` when no model is reachable or no form can be
    /// extracted (the loop then gives up). The discriminated result carries the
    /// **shape** of the reply (tool_use vs prose) so the caller can keep the
    /// transcript's tool_use↔tool_result pairing correct (a tool_use repair must
    /// be recorded as an assistant `tool_use` turn carrying its id; a prose repair
    /// as an assistant prose turn). Used ONLY by the silent repair loop.
    fn agent_complete_for_repair(&mut self, req: &AgentRequest) -> Option<RepairResponse> {
        let state = self.agent.as_mut()?;
        let model = state.model.as_mut()?;
        match model.complete(req) {
            Ok(ModelResponse::ToolCalls(calls)) => calls
                .into_iter()
                .find(|c| c.name.trim().trim_start_matches('/') == SUBMIT_TOOL)
                .map(|c| RepairResponse::ToolCall {
                    id: c.id,
                    argument: c.argument,
                }),
            Ok(ModelResponse::Done(prose)) => extract_form_from_prose(&prose)
                .map(|form| RepairResponse::Prose { prose, form }),
            Err(_) => None,
        }
    }

    /// The 1-based `agent_turn` loop-step index for the current iteration (§28.2),
    /// stashed on `AgentState.current_turn` by the `agent_turn` loop. The in-loop
    /// log record sites read it here to stamp `.turn(current)` — the log↔trace
    /// correlation key — without a threaded `turn` param (Principle 1). `0` when
    /// there is no agent (never collides with the 1-based live ids).
    pub(crate) fn agent_current_turn(&self) -> usize {
        self.agent.as_ref().map(|a| a.current_turn).unwrap_or(0)
    }

    /// `--yes` reader (§20.2). Dormant / feature-off ⇒ `false`. Read ONLY at the
    /// consent-gate site (§15.2 step 2) — NEVER by the validator (§20.3): the
    /// structural guard that `--yes` skips consent, not validation.
    pub(crate) fn agent_auto_accept(&self) -> bool {
        self.agent.as_ref().is_some_and(|a| a.auto_accept)
    }

    /// Fire the §20.4 first-use autonomy notice once per session (on the first
    /// auto-accepted write of either class). Check-and-set on `AgentState`.
    fn fire_auto_accept_notice_once(&mut self, stdout: &mut impl Write) {
        let should = self
            .agent
            .as_ref()
            .map(|a| !a.auto_accept_notice_shown)
            .unwrap_or(false);
        if should {
            let _ = write!(
                stdout,
                "{}",
                crate::style::agent_prose(
                    "--yes is on: the agent will now submit definitions WITHOUT asking \
                     for per-action confirmation. The pre-flight validator still gates \
                     correctness — only code that compiles cleanly is ever submitted."
                )
            );
            if let Some(state) = self.agent.as_mut() {
                state.auto_accept_notice_shown = true;
            }
        }
    }
}

/// The shape of a repair completion (`agent_complete_for_repair`). Carries enough
/// to keep the transcript's tool_use↔tool_result pairing correct across repair
/// iterations: a `ToolCall` repair must be recorded as an assistant `tool_use`
/// turn (so its id pairs with the NEXT iteration's error `tool_result`), while a
/// `Prose` repair is recorded as an assistant prose turn (no pairing owed).
enum RepairResponse {
    /// The model re-proposed via a `submit` tool-call. `id` is the new tool_use
    /// id (paired with the next feedback's `tool_result`); `argument` is the form.
    ToolCall { id: String, argument: String },
    /// The model replied with prose carrying a `(...)` form. `prose` is recorded
    /// as the assistant turn; `form` is the mined definition.
    Prose { prose: String, form: String },
}

/// Mine the first balanced `(...)` s-expression form out of model prose (a `Done`
/// reply that carries a definition without a `submit` tool-call). Returns the
/// substring from the first `(` through its matching `)`, or `None`.
fn extract_form_from_prose(prose: &str) -> Option<String> {
    let start = prose.find('(')?;
    let bytes = prose.as_bytes();
    let mut depth = 0usize;
    let mut end = None;
    for (i, &b) in bytes.iter().enumerate().skip(start) {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    end = Some(i + 1);
                    break;
                }
            }
            _ => {}
        }
    }
    end.map(|e| prose[start..e].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(name: &str, arg: &str) -> ToolCallRequest {
        ToolCallRequest {
            id: "c1".to_string(),
            name: name.to_string(),
            argument: arg.to_string(),
        }
    }

    // A read command synthesizes to a slash command string.
    #[test]
    fn read_command_synthesizes() {
        assert_eq!(synthesize_command(&call("source", "foo")).unwrap(), "/source foo");
        assert_eq!(synthesize_command(&call("list", "")).unwrap(), "/list");
        // A leading slash on the model side is tolerated.
        assert_eq!(synthesize_command(&call("/info", "bar")).unwrap(), "/info bar");
    }

    // A write / non-read command is refused at synthesis — unconstructable.
    #[test]
    fn write_command_refused() {
        assert!(synthesize_command(&call("sh", "rm -rf /")).is_err());
        assert!(synthesize_command(&call("submit", "(defn evil [] 0)")).is_err());
        assert!(synthesize_command(&call("def", "x 1")).is_err());
        // An unknown tool is also refused (fail closed).
        assert!(synthesize_command(&call("frobnicate", "x")).is_err());
    }

    // The tool-def set is the read-only allowlist PLUS the one Build write tool
    // `submit` (§15.1) — and nothing else. `submit` is offered but always
    // confirm-gated (the gate, not the offer, is the consent boundary); `/sh`
    // and other writes never leak in.
    #[test]
    fn tool_defs_are_read_only_plus_submit() {
        let defs = tool_defs();
        assert!(defs.iter().any(|d| d.name == "source"));
        assert!(!defs.iter().any(|d| d.name == "sh"));
        // The write tools are offered (Build §15.1 + Document §17.2) ...
        assert!(defs.iter().any(|d| d.name == "submit"));
        assert!(defs.iter().any(|d| d.name == "set-preamble"));
        assert!(defs.iter().any(|d| d.name == "set-doc"));
        // ... and the set is exactly the read-only allowlist + those 3 write
        // tools (submit / set-preamble / set-doc), all gated, none auto-run.
        assert_eq!(defs.len(), ALLOWLIST.len() + 3);
    }

    // -----------------------------------------------------------------------
    // run_pull result-content tests (S88 pull-loop defect). The model loops
    // when the fed-back tool_result content is empty — these pin that the
    // ToolCallResult a real read command produces CARRIES the command output,
    // and that it is rendered as-typed AND used as the model's tool_result.
    // -----------------------------------------------------------------------

    /// Build a session where `f` is a defined, mentionable symbol with
    /// introspection source — so `/source f` / `/info f` resolve to real output
    /// (mirrors the `mod.rs` harvest test fixture, Principle 7).
    fn session_with_defined_f() -> CompilerSession {
        use crate::agent::test_support::repl_session;
        let s = repl_session();
        let module = s.current_module_path();
        {
            use cranelisp_types::{DefKind, ModuleEntry, Symbol, Visibility};
            if let Some(mut table) = s.shared.symbol_tables.get_mut(&module) {
                let entry = ModuleEntry::def(
                    cranelisp_types::Scheme {
                        type_vars: Vec::new(),
                        constraints: std::collections::HashMap::new(),
                        ty: cranelisp_types::Type::Int,
                    },
                    DefKind::PrimitiveExtern,
                )
                .visibility(Visibility::Public)
                .build();
                table.insert(Symbol::from("f"), entry);
            }
        }
        if let Some(intr) = s.shared.introspection.as_ref() {
            intr.insert(
                cranelisp_types::FQSymbol {
                    module: module.clone(),
                    symbol: cranelisp_types::Symbol::from("f"),
                },
                crate::session_v4::Introspection {
                    source: Some("(defn f [x] x)".to_string()),
                    sexp: None,
                    expanded: None,
                    ast: None,
                    clif_ir: None,
                    code_size: None,
                },
            );
        }
        s
    }

    // A pull for a real read command returns a ToolCallResult whose `output`
    // is NON-EMPTY and CONTAINS the command's actual output (the source text) —
    // this is the content fed back to the model. An empty/placeholder result is
    // exactly what makes the model re-request the same tool forever (the pull
    // loop). The output is ALSO rendered as-typed to stdout (the transcript).
    #[test]
    fn run_pull_source_captures_command_output() {
        let mut s = session_with_defined_f();
        let mut sink: Vec<u8> = Vec::new();
        let result = s.run_pull(&call("source", "f"), &mut sink, &mut crate::agent::types::NoConsent);
        // The fed-back content is non-empty and carries the source.
        assert!(!result.output.is_empty(), "tool_result content must not be empty");
        assert!(
            result.output.contains("(defn f [x] x)"),
            "tool_result content must carry the command output, got: {:?}",
            result.output
        );
        // The same output is rendered as-typed to stdout (the transcript).
        let rendered = String::from_utf8_lossy(&sink);
        assert!(rendered.contains("/source f"), "the command is echoed as-typed: {rendered}");
        assert!(
            rendered.contains("(defn f [x] x)"),
            "the output is displayed in the transcript: {rendered}"
        );
    }

    // +neg: `/info` on a defined symbol likewise produces non-empty content —
    // a read command with output is NEVER silently reduced to an empty result.
    #[test]
    fn run_pull_info_is_not_empty() {
        let mut s = session_with_defined_f();
        let mut sink: Vec<u8> = Vec::new();
        let result = s.run_pull(&call("info", "f"), &mut sink, &mut crate::agent::types::NoConsent);
        assert!(
            !result.output.is_empty(),
            "an /info pull on a defined symbol must carry content, got empty"
        );
        // It is the symbol's name, not a placeholder.
        assert!(result.output.contains('f'), "info content must describe f: {:?}", result.output);
    }

    // spec: repl/spec.md §17 / §14.6 — ANSI-leak on PULL-command results (S89
    // Phase-6). A `/source` pull whose result is STYLED (colour ON) must:
    //   (a) feed the MODEL clean PLAIN text — no `\x1b`, no bare `1m`/`0m` SGR
    //       fragment (the residue the model echoes back, leaking into display);
    //   (b) echo to the USER with WELL-FORMED SGR only (every ESC introduces a
    //       `[`) — never an orphan ESC or a `\x1b[`-less `1m`/`0m` fragment.
    // The Wave-1 fix covered agent PROSE only, NOT the pull-result echo; this is
    // that hole. Uses the `style` `#[cfg(test)]` colour-force seam (the non-TTY
    // test process is colour-off by default, so colour-on is otherwise
    // unreachable from a unit test).
    #[test]
    fn pull_result_no_mangled_sgr_for_user_or_model() {
        let _guard = crate::style::test_support::ColorGuard::force(true);
        assert!(
            crate::style::is_color_enabled(),
            "the force seam must drive the gate ON, else this guard is vacuous"
        );
        let mut s = session_with_defined_f();
        let mut sink: Vec<u8> = Vec::new();
        let result = s.run_pull(&call("source", "f"), &mut sink, &mut crate::agent::types::NoConsent);

        // (a) the MODEL-fed copy is clean plain text — ANSI fully stripped.
        assert!(
            !result.output.contains('\u{1b}'),
            "the model-fed output must carry NO ESC byte: {:?}",
            result.output
        );
        // No SGR residue (the `1m`/`0m` the mangling left as literal text).
        assert!(
            !result.output.contains("1m") && !result.output.contains("0m"),
            "the model-fed output must carry no `1m`/`0m` SGR fragment: {:?}",
            result.output
        );
        // It still carries the real source content (strip removed only the SGR).
        assert!(
            result.output.contains("(defn f [x] x)"),
            "stripping must keep the command output, got: {:?}",
            result.output
        );

        // (b) the USER echo: every ESC introduces a well-formed SGR (ESC '['),
        // never an orphan ESC or a `\x1b[`-less `1m`/`0m` fragment.
        let rendered = String::from_utf8_lossy(&sink);
        for (i, _) in rendered.match_indices('\u{1b}') {
            let after = &rendered[i + 1..];
            assert!(
                after.starts_with('['),
                "every ESC in the user echo must introduce a well-formed SGR \
                 (ESC '['); orphan at {i}: {rendered:?}"
            );
        }
        // The user echo still shows the command + the source.
        assert!(rendered.contains("/source f"), "command echoed: {rendered:?}");
    }

    // -----------------------------------------------------------------------
    // S89 Cluster B — write arm, validator, allowlist widening, --yes guard.
    // -----------------------------------------------------------------------

    use crate::agent::stub::StubModel;
    use crate::agent::test_support::repl_session;
    use crate::agent::types::{AgentState, ConsentReader, ModelResponse};

    /// A scripted consent reader: yields its lines in order, then EOF (decline).
    struct ScriptedConsent(std::vec::IntoIter<String>);
    impl ScriptedConsent {
        fn new(lines: &[&str]) -> Self {
            Self(lines.iter().map(|s| s.to_string()).collect::<Vec<_>>().into_iter())
        }
    }
    impl ConsentReader for ScriptedConsent {
        fn read_consent_line(&mut self) -> Option<String> {
            self.0.next()
        }
    }

    /// Wire a session's agent to a stub model (with `auto_accept`), so a write
    /// turn can drive `run_submit` deterministically with zero network.
    fn session_with_agent(s: &mut CompilerSession, script: Vec<ModelResponse>, auto_accept: bool) {
        s.agent = Some(AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(StubModel::new(script))),
            provider_label: "stub (test)".to_string(),
            auto_accept,
            auto_accept_notice_shown: false,
            submit_gave_up: false,
            submit_committed: false,
            current_turn: 0,
        });
    }

    fn submit_call(form: &str) -> ToolCallRequest {
        ToolCallRequest {
            id: "s1".to_string(),
            name: "submit".to_string(),
            argument: form.to_string(),
        }
    }

    fn submit_call_with_id(id: &str, form: &str) -> ToolCallRequest {
        ToolCallRequest {
            id: id.to_string(),
            name: "submit".to_string(),
            argument: form.to_string(),
        }
    }

    // §15.1 — the allowlist widening: a `submit` tool-call routes to the
    // confirm-gated write arm (NOT the read-only refusal). With consent declined
    // (`n`), nothing is committed and the result reports the decline.
    #[test]
    fn submit_routes_to_write_arm_not_refused() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&["n"]);
        let result = s.run_pull(&submit_call("(defn idfn [x] x)"), &mut sink, &mut consent);
        assert!(
            !result.output.contains("refused"),
            "submit must route to the write arm, not the read-only refusal: {:?}",
            result.output
        );
        let rendered = String::from_utf8_lossy(&sink);
        assert!(rendered.contains("[y/N]"), "the confirm gate must prompt: {rendered}");
        assert!(result.output.contains("declined"), "decline result: {:?}", result.output);
        assert!(
            s.lookup_with_prelude_fallback("idfn").is_none(),
            "declined submit committed nothing"
        );
    }

    // §15.4 +neg — a non-read, non-`submit` tool (`/sh`) is STILL refused at
    // `synthesize_command`, WITHOUT any confirm gate. The floor was EXTENDED
    // (one write tool, confirm-gated), not loosened.
    #[test]
    fn non_submit_write_still_refused() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&[]);
        let result = s.run_pull(&call("sh", "echo pwned"), &mut sink, &mut consent);
        assert!(
            result.output.contains("refused"),
            "a non-submit write must be refused: {:?}",
            result.output
        );
        let rendered = String::from_utf8_lossy(&sink);
        assert!(!rendered.contains("[y/N]"), "no confirm gate for a refused write: {rendered}");
    }

    // §15.2/§15.3 — a clean submit, confirmed with `y`, commits: the def binds.
    #[test]
    fn submit_confirmed_commits_definition() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&["y"]);
        let result = s.run_pull(&submit_call("(defn idfn [x] x)"), &mut sink, &mut consent);
        assert!(
            s.lookup_with_prelude_fallback("idfn").is_some(),
            "a confirmed clean submit must bind the definition; result={:?}",
            result.output
        );
    }

    // §16.1 — the validator dry-run DISCARDS: a clean form validated does NOT
    // leak into live state (only a real submit binds).
    #[test]
    fn validate_dry_run_discards_does_not_commit() {
        let s = repl_session();
        assert!(s.validate_one_form("(defn ghost [x] x)").is_ok(), "the form is clean");
        assert!(
            s.lookup_with_prelude_fallback("ghost").is_none(),
            "validate_forms_dry_run must NEVER commit to live (§16.1 discard arm)"
        );
    }

    // §16.1 — a BROKEN form (unbalanced paren) fails the validator with an Err
    // (parse OR type — U5; a parse failure surfaces uniformly as Err).
    #[test]
    fn validate_broken_form_is_err() {
        let s = repl_session();
        assert!(
            s.validate_one_form("(defn broken [x] (add-i64 x x)").is_err(),
            "an unbalanced form must fail the validator (silent-repair trigger)"
        );
    }

    // §16.2 — broken-then-fixed: the repair loop stages→checks→discards the
    // broken form, re-prompts the (stub) model, and returns the CLEAN repaired
    // form. The broken text never escapes.
    #[test]
    fn validate_and_repair_returns_clean_after_broken() {
        let mut s = repl_session();
        session_with_agent(
            &mut s,
            vec![ModelResponse::ToolCalls(vec![submit_call("(defn fixed [x] x)")])],
            false,
        );
        // The outer `agent_turn` loop records the submit tool_use BEFORE invoking
        // the pull/repair; mirror that so the repair loop's iter-1 feedback
        // tool_result pairs against a real preceding tool_use (the wire-valid guard
        // at assemble_request rejects a bare leading tool_result).
        if let Some(state) = s.agent.as_mut() {
            state.record_assistant_tool_calls(vec![submit_call_with_id(
                "toolu_outer",
                "(defn fixed [x] x",
            )]);
        }
        let (clean, final_id) = s
            .validate_and_repair("(defn fixed [x] x", "toolu_outer")
            .expect("repair yields a clean form");
        assert_eq!(clean.trim(), "(defn fixed [x] x)", "the repaired clean form is returned");
        // The returned pairing id is the LAST repair tool_use's id (the stub
        // `submit_call` uses id "s1"), NOT the outer "toolu_outer" — so the outer
        // success tool_result pairs against the actually-submitted tool_use.
        assert_eq!(
            final_id.as_deref(),
            Some("s1"),
            "the final pairing id must be the repair tool_use's id, not the outer submit's"
        );
    }

    // §20.3 (CRITICAL) — `agent_auto_accept()` reads the field ONLY at the consent
    // site; the VALIDATOR takes no such param and behaves identically regardless
    // of the flag (proven by validating with auto_accept on).
    #[test]
    fn auto_accept_reader_reads_field_validator_unaffected() {
        let mut s = repl_session();
        assert!(!s.agent_auto_accept(), "no agent ⇒ auto_accept false");
        session_with_agent(&mut s, vec![], true);
        assert!(s.agent_auto_accept(), "the reader must reflect auto_accept=true");
        // The validator is UNAFFECTED by the flag (no read path — §20.3).
        assert!(
            s.validate_one_form("(defn b [x] (add-i64 x x)").is_err(),
            "broken Err with --yes ON"
        );
        assert!(s.validate_one_form("(defn c [x] x)").is_ok());
        assert!(
            s.lookup_with_prelude_fallback("c").is_none(),
            "validation never commits, --yes or not"
        );
    }

    // §20.2/§20.4 — under `--yes` the gate auto-accepts WITHOUT a `[y/N]` prompt,
    // the once-only first-use notice fires, and the clean form commits.
    #[test]
    fn yes_auto_accepts_without_prompt_and_fires_notice_once() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], true);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&[]);
        let _ = s.run_pull(&submit_call("(defn auto1 [x] x)"), &mut sink, &mut consent);
        let rendered = String::from_utf8_lossy(&sink);
        assert!(!rendered.contains("[y/N]"), "no confirm prompt under --yes: {rendered}");
        assert!(rendered.contains("--yes is on"), "first-use notice must fire: {rendered}");
        assert!(
            s.lookup_with_prelude_fallback("auto1").is_some(),
            "the clean form commits under --yes"
        );
        // The notice is once-per-session.
        let mut sink2: Vec<u8> = Vec::new();
        let _ = s.run_pull(&submit_call("(defn auto2 [x] x)"), &mut sink2, &mut consent);
        let rendered2 = String::from_utf8_lossy(&sink2);
        assert!(
            !rendered2.contains("--yes is on"),
            "the notice fires ONCE per session: {rendered2}"
        );
    }

    // -----------------------------------------------------------------------
    // S89 Cluster C — Document mode (set-preamble/set-doc, consultative gate).
    // -----------------------------------------------------------------------

    fn set_preamble_call(arg: &str) -> ToolCallRequest {
        ToolCallRequest {
            id: "d1".to_string(),
            name: "set-preamble".to_string(),
            argument: arg.to_string(),
        }
    }

    // §17.2 — a `set-preamble` routes to the CONSULTATIVE Document arm, NOT the
    // read-only refusal and NOT the Build confirm: the gate wording is "record
    // this as <module>'s preamble?" (distinct from the Build "[y/N]" confirm),
    // and the canonical `;;` block is shown verbatim. The tool name discriminates.
    #[test]
    fn set_preamble_uses_consultative_gate_distinct_from_build() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&["n"]);
        let module = s.current_module_path();
        let arg = format!("{} Solver core: propagation over a grid.", module.as_ref());
        let result = s.run_pull(&set_preamble_call(&arg), &mut sink, &mut consent);
        let rendered = String::from_utf8_lossy(&sink);
        assert!(
            !result.output.contains("refused"),
            "set-preamble must route to the Document arm, not the refusal: {:?}",
            result.output
        );
        // The CONSULTATIVE wording — distinct from the Build confirm.
        assert!(
            rendered.contains("record this as") && rendered.contains("preamble?"),
            "the consultative gate must ask 'record this as <module>'s preamble?': {rendered}"
        );
        assert!(
            !rendered.contains("submit this definition"),
            "the Document gate must NOT use the Build confirm wording: {rendered}"
        );
        // The exact canonical `;;` block is shown (§17.15.1 render-always).
        assert!(
            rendered.contains(";; Solver core: propagation over a grid."),
            "the proposed canonical block must be shown verbatim: {rendered}"
        );
    }

    // §17.1 — a confirmed `set-preamble` applies the byte-stable edit: the
    // module's `module_preamble` field carries the stripped prose afterwards
    // (the durable record `/doc <module>` + the harvester read back).
    #[test]
    fn set_preamble_confirmed_sets_module_preamble_field() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&["y"]);
        let module = s.current_module_path();
        let arg = format!("{} Solver core: propagation.", module.as_ref());
        let _ = s.run_pull(&set_preamble_call(&arg), &mut sink, &mut consent);
        let table = s.shared.symbol_tables.get(&module).expect("module table exists");
        assert_eq!(
            table.module_preamble.as_deref(),
            Some("Solver core: propagation."),
            "a confirmed set-preamble sets the stripped prose on module_preamble"
        );
    }

    // §17.15.2 +neg — a DECLINED set-preamble writes NOTHING: the
    // `module_preamble` field stays unset (the Document twin of the declined
    // Build submit floor).
    #[test]
    fn set_preamble_declined_writes_nothing_neg() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&["n"]);
        let module = s.current_module_path();
        let arg = format!("{} declined preamble.", module.as_ref());
        let result = s.run_pull(&set_preamble_call(&arg), &mut sink, &mut consent);
        assert!(result.output.contains("declined"), "decline result: {:?}", result.output);
        let preamble = s
            .shared
            .symbol_tables
            .get(&module)
            .and_then(|t| t.module_preamble.clone());
        assert_eq!(preamble, None, "a declined set-preamble must record nothing");
    }

    // §17.15.2a / §20.2 — under `--yes` the Document consultative gate is
    // SUPPRESSED (the "record this as ...?" question must NOT fire) yet the edit
    // is STILL applied (blanket auto-accept covers Document), and the proposed
    // block is STILL shown (render-always).
    #[test]
    fn set_preamble_yes_auto_accepts_suppresses_question_still_applies() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], true);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&[]);
        let module = s.current_module_path();
        let arg = format!("{} Auto preamble.", module.as_ref());
        let _ = s.run_pull(&set_preamble_call(&arg), &mut sink, &mut consent);
        let rendered = String::from_utf8_lossy(&sink);
        assert!(
            !rendered.contains("record this as"),
            "under --yes the consultative question must NOT fire: {rendered}"
        );
        assert!(
            rendered.contains(";; Auto preamble."),
            "the proposed block must STILL be shown under --yes (render-always): {rendered}"
        );
        let table = s.shared.symbol_tables.get(&module).expect("module table exists");
        assert_eq!(
            table.module_preamble.as_deref(),
            Some("Auto preamble."),
            "under --yes the edit must STILL be applied (blanket auto-accept)"
        );
    }

    // §17.2 — a `set-doc` tool-call routes to the Document arm and asks the
    // docstring-flavoured consultative question (NOT the preamble wording), and
    // on confirm sets the symbol's live docstring field.
    /// Insert a `UserFn` `Def` named `name` (the docstring-persisting kind) into
    /// the current module — the shape `set-doc` may durably document (§11.3a).
    fn insert_userfn(s: &CompilerSession, name: &str) {
        use cranelisp_types::{DefKind, ModuleEntry, Symbol, UserFnState, Visibility};
        let module = s.current_module_path();
        if let Some(mut table) = s.shared.symbol_tables.get_mut(&module) {
            let entry = ModuleEntry::def(
                cranelisp_types::Scheme {
                    type_vars: Vec::new(),
                    constraints: std::collections::HashMap::new(),
                    ty: cranelisp_types::Type::Int,
                },
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
                },
            )
            .visibility(Visibility::Public)
            .build();
            table.insert(Symbol::from(name), entry);
        }
    }

    #[test]
    fn set_doc_consultative_gate_sets_docstring() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let module = s.current_module_path();
        // A `UserFn` Def — the docstring-persisting kind (the path set-doc may
        // honestly record; a non-UserFn is now refused, see the +neg test below).
        insert_userfn(&s, "solve");
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&["y"]);
        let call = ToolCallRequest {
            id: "d2".to_string(),
            name: "set-doc".to_string(),
            argument: "solve Solve the grid.".to_string(),
        };
        let _ = s.run_pull(&call, &mut sink, &mut consent);
        let rendered = String::from_utf8_lossy(&sink);
        assert!(
            rendered.contains("record this as") && rendered.contains("docstring?"),
            "set-doc must ask the docstring consultative question: {rendered}"
        );
        assert!(rendered.contains("recorded"), "a UserFn set-doc reports success: {rendered}");
        let table = s.shared.symbol_tables.get(&module).expect("table");
        let doc = match table.symbols.get(&cranelisp_types::Symbol::from("solve")) {
            Some(cranelisp_types::ModuleEntry::Def { docstring, .. }) => docstring.clone(),
            _ => None,
        };
        assert_eq!(doc.as_deref(), Some("Solve the grid."), "the docstring is set on confirm");
    }

    // S1 (honesty) — `set-doc` on a symbol absent from the current module must
    // NOT claim "recorded": `apply_docstring_edit` returns `no such definition`
    // and `run_document_edit` surfaces it instead of a false success. (A qualified
    // `mod/sym` and a re-exported `Import` both land here — neither is a local
    // `Def` key.)
    #[test]
    fn set_doc_missing_symbol_reports_not_found_no_false_success() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        // The contained-lookup contract: a miss is an Err, never a silent no-op.
        let err = s.apply_docstring_edit("ghost", "doc").unwrap_err();
        assert!(err.contains("no such definition"), "miss must surface not-found: {err:?}");
        // …and through the gate, the tool result carries the error, not "recorded".
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = ScriptedConsent::new(&["y"]);
        let call = ToolCallRequest {
            id: "d3".to_string(),
            name: "set-doc".to_string(),
            argument: "ghost some docstring".to_string(),
        };
        let result = s.run_pull(&call, &mut sink, &mut consent);
        assert!(
            result.output.contains("no such definition"),
            "the fed-back result must be the not-found error: {:?}",
            result.output
        );
        let rendered = String::from_utf8_lossy(&sink);
        assert!(!rendered.contains("recorded"), "a miss must NOT print 'recorded': {rendered}");
    }

    // S2 (honesty) — `set-doc` on a non-`UserFn` `Def` (here a `PrimitiveExtern`)
    // is REFUSED: its docstring would show in-session but VANISH on restart
    // (`generate_fns_and_macros` only persists UserFn docstrings), so claiming
    // "recorded" would be dishonest. The live field is left unset.
    #[test]
    fn set_doc_non_userfn_refused_not_recorded() {
        use cranelisp_types::{DefKind, ModuleEntry, Symbol, Visibility};
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let module = s.current_module_path();
        if let Some(mut table) = s.shared.symbol_tables.get_mut(&module) {
            let entry = ModuleEntry::def(
                cranelisp_types::Scheme {
                    type_vars: Vec::new(),
                    constraints: std::collections::HashMap::new(),
                    ty: cranelisp_types::Type::Int,
                },
                DefKind::PrimitiveExtern,
            )
            .visibility(Visibility::Public)
            .build();
            table.insert(Symbol::from("prim"), entry);
        }
        let err = s.apply_docstring_edit("prim", "doc").unwrap_err();
        assert!(
            err.contains("cannot record a docstring") && err.contains("function"),
            "a non-UserFn target must be refused with a clear message: {err:?}"
        );
        // The live field stays unset — nothing ephemeral was written.
        let table = s.shared.symbol_tables.get(&module).expect("table");
        let doc = match table.symbols.get(&Symbol::from("prim")) {
            Some(ModuleEntry::Def { docstring, .. }) => docstring.clone(),
            _ => None,
        };
        assert_eq!(doc, None, "a refused set-doc must NOT set the docstring field");
    }

    // S2 (positive) — a `UserFn` target IS recorded: `apply_docstring_edit`
    // returns Ok and sets the live, persisting `Def.docstring`.
    #[test]
    fn set_doc_userfn_records_docstring() {
        let mut s = repl_session();
        session_with_agent(&mut s, vec![], false);
        let module = s.current_module_path();
        insert_userfn(&s, "double");
        assert!(s.apply_docstring_edit("double", "doubles its argument").is_ok());
        let table = s.shared.symbol_tables.get(&module).expect("table");
        let doc = match table.symbols.get(&cranelisp_types::Symbol::from("double")) {
            Some(cranelisp_types::ModuleEntry::Def { docstring, .. }) => docstring.clone(),
            _ => None,
        };
        assert_eq!(doc.as_deref(), Some("doubles its argument"), "UserFn docstring set");
    }

    // §17.2 +neg — the Document tools stay OUT of the read-only allowlist: a
    // `set-preamble`/`set-doc` is unconstructable through `synthesize_command`
    // (refused), exactly like a write — the gate (not the allowlist) is the
    // consent boundary.
    #[test]
    fn document_tools_refused_by_read_only_allowlist_neg() {
        assert!(
            synthesize_command(&call("set-preamble", "user x")).is_err(),
            "set-preamble must be refused by the read-only allowlist"
        );
        assert!(
            synthesize_command(&call("set-doc", "solve x")).is_err(),
            "set-doc must be refused by the read-only allowlist"
        );
        // The tool-def set offers them (gated), but they are not read-allowlisted.
        let defs = tool_defs();
        assert!(defs.iter().any(|d| d.name == "set-preamble"));
        assert!(defs.iter().any(|d| d.name == "set-doc"));
        assert!(!is_allowed("set-preamble") && !is_allowed("set-doc"));
    }
}
