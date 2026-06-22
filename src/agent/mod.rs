// Embedded agent — int-side module (Sprint 88 Phase 5, Wave 3 — Advisor MVP core).
//
// `design/int/agent.md` §3. This module is entirely `#[cfg(feature = "agent")]`
// (declared so in `lib.rs`), a sibling to `repl.rs` / `eval.rs` / `process_form.rs`
// in int's session decomposition (`src/CLAUDE.md §"Session/REPL module
// decomposition"`). Feature-off ⇒ this module does not exist and the binary is
// byte-identical to today (`agent.md §1`, `repl/spec.md §17.1`).
//
// WAVE 3 SCOPE (Advisor MVP core). The §5.3 dispatch classifier
// (`classify_for_agent`, this file) routes prose/unknowns to the agent; the real
// `agent_turn` model↔tool loop (this file) drives an `AgentModel` (the membrane
// over rig's `CompletionModel`, R3-amended — `types.rs`/`provider.rs`/`request.rs`),
// assembling the request from the always-on language primer (`primer.rs`) + the
// harvested session context (`harvest.rs`) + the transcript, handling `Done(prose)`
// (rendered in the agent frame) and `ToolCalls` (pull-as-visible-commands through
// `process_commands`, read-only allowlist — `pull.rs`). Provider selection
// (anthropic default / ollama local / stub) is runtime config (`provider.rs`);
// absent a reachable provider the agent is dormant. DEFERRED to a later step:
// spec-grep retrieval + the telemetry skeleton (the R5 release valve, §0).

pub mod harvest;
pub mod primer;
pub mod provider;
pub mod pull;
pub mod render;
pub mod request;
pub mod stub;
pub mod types;

use std::io::Write;

use crate::agent::types::{AgentRequest, ModelResponse};
use crate::session_v4::CompilerSession;

/// Cap on model↔tool loop iterations within one turn — a budget guard so a
/// misbehaving model cannot spin forever pulling commands (§3.2 "budget guard").
const MAX_TURN_ITERATIONS: usize = 8;

/// The dispatch-classifier routing decision (`agent.md §2.2`,
/// `repl/spec.md §17.1`). Computed one step earlier than evaluation, in the
/// `main.rs` read loop, on a *complete* buffer. The classifier never calls the
/// model — it routes purely on the parse result + the feature cut.
///
/// Only the `Agent` arm diverts from today's behaviour, and it only fires on
/// input that today produces a parse-error diagnostic anyway — so the
/// feature-OFF build is byte-identical by construction (the variant does not
/// exist there because the whole module is `#[cfg]`-gated).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Classify {
    /// Route to the deterministic REPL unchanged — slash command, blank/comment,
    /// or a buffer the reader accepts (a complete sexp / atom / literal: the §4
    /// self-documentation surface). Falls through to `process_commands`.
    Repl,
    /// Unclosed `(` / `[` — the existing `parens_balanced` continuation gate.
    Continuation,
    /// A parse error that is NOT an unclosed bracket (natural-language prose).
    /// Routes to the agent as a turn. Carries the original text.
    Agent(String),
}

impl CompilerSession {
    /// Classify a *complete* REPL buffer for agent dispatch (`agent.md §2.2`,
    /// `repl/spec.md §17.1` — refined classifier, user-directed 2026-06-22).
    ///
    /// Parseability alone is insufficient: this reader accepts a run of bare
    /// words (`how do I define a function`) as `Ok(N Symbol forms)`, so prose
    /// would otherwise route to the REPL. The refined rule resolves the bare
    /// symbols before deciding — only a buffer whose every bare atom is *known*
    /// (resolves, or is a literal) is the §4 self-documentation surface; any
    /// unbound bare symbol (a typo, a bare word, multi-word prose) is for the
    /// agent. Routing rules (first match wins):
    ///
    /// - starts with `/` → `Repl` (slash command, incl. `/ask`/`/refs`/`/tests-for`)
    /// - blank / comment-only → `Repl` (silent re-prompt)
    /// - `parse(buffer)`:
    ///   - `Err(unclosed '(' / '[')` → `Continuation` (the `parens_balanced` gate)
    ///   - `Err(other parse error)` → `Agent(text)` (not Cranelisp → prose)
    ///   - `Ok(forms)`:
    ///     - ANY compound form (`List`/`Bracket`, e.g. `(+ 1 2)`, `[1 2 3]`)
    ///       → `Repl` (it is code)
    ///     - else (all forms are bare atoms — symbols / literals):
    ///       - ALL known (every `Symbol` resolves via the same resolution path
    ///         `/info`/bare-symbol introspection uses, plus intrinsic type names;
    ///         literals always count) → `Repl` (the §4 describe surface)
    ///       - ANY unbound / unknown symbol → `Agent(text)`
    ///
    /// The symbol-lookup → `Agent` divergence lives ENTIRELY in this module,
    /// which is `#[cfg(feature = "agent")]`-gated (`lib.rs`): feature-off this
    /// method does not exist and the binary is byte-identical to today — a bare
    /// unbound symbol reaches today's `eval.rs` "unbound" introspection message
    /// via `process_commands`, not the agent.
    pub fn classify_for_agent(&self, buffer: &str) -> Classify {
        use cranelisp_types::Sexp;

        let trimmed = buffer.trim();

        // Slash command — unchanged path. (`/ask <text>` is dispatched to the
        // agent by `process_commands` → `dispatch_command`, not here.)
        if trimmed.starts_with('/') {
            return Classify::Repl;
        }

        // Blank / comment-only — unchanged (process_commands::Nothing).
        if trimmed.is_empty() || crate::session_v4::is_comment_only(trimmed) {
            return Classify::Repl;
        }

        // Consult the same reader the REPL already trusts.
        let forms = match cranelisp_frontend::parse(buffer) {
            Ok(forms) => forms,
            Err(_) => {
                // Distinguish "unclosed bracket" (a continuation the reader is
                // still waiting on) from a genuine parse error (prose). The REPL
                // read loop already gates continuations via `parens_balanced`
                // BEFORE reaching the classifier, so by the time we are here the
                // buffer is "complete" by the paren-balance test. A residual
                // parse error on a paren-balanced buffer is therefore NOT an
                // unclosed bracket — it is prose. But guard defensively: if the
                // buffer is somehow unbalanced, treat it as a continuation
                // rather than diverting to the agent.
                return if !crate::session_v4::parens_balanced(buffer) {
                    Classify::Continuation
                } else {
                    Classify::Agent(trimmed.to_string())
                };
            }
        };

        // `Ok(forms)`. Any compound form (a list/vector/application) is code —
        // route to the deterministic REPL untouched.
        let any_compound = forms
            .iter()
            .any(|f| matches!(f, Sexp::List(..) | Sexp::Bracket(..)));
        if any_compound {
            return Classify::Repl;
        }

        // Every form is a bare atom. Literals always count as known; a bare
        // `Symbol` is known iff it resolves through the same path bare-symbol
        // introspection / `/info` use (`lookup_with_prelude_fallback`: current
        // module → prelude outer scope → root, covering bound defs, special
        // forms, types, traits, operators, constructors), or it names an
        // intrinsic type (`Int`/`Bool`/`Float`/`String`, the §4.1.3 surface that
        // resolves outside the tables). ANY unbound symbol → the agent.
        let all_known = forms.iter().all(|f| match f {
            Sexp::Symbol(name, _) => self.symbol_is_known(name),
            Sexp::Int(..) | Sexp::Float(..) | Sexp::Bool(..) | Sexp::Str(..) => true,
            // No compound forms remain (handled above); a residual Comment is
            // inert (the comment-only buffer already routed to Repl) — treat as
            // known so it does not divert to the agent.
            _ => true,
        });

        if all_known {
            Classify::Repl
        } else {
            Classify::Agent(trimmed.to_string())
        }
    }

    /// Is a bare symbol *known* to the session — i.e. would the §4 bare-symbol
    /// introspection / `/info` path describe it rather than report it unbound?
    ///
    /// Reuses the canonical resolution path (`lookup_with_prelude_fallback`,
    /// the same `Some`/`None` gate `/sig`/`/info`/`describe_symbol` use to
    /// distinguish a described symbol from `unknown symbol '…'`), plus the
    /// intrinsic-type-name check those paths apply ahead of the table lookup
    /// (`Int`/`Bool`/`Float`/`String` — §4.1.3 names that live outside the
    /// symbol tables). No second resolver is hand-rolled (Principle 7).
    fn symbol_is_known(&self, name: &str) -> bool {
        crate::session_v4::intrinsic_type_from_name(name).is_some()
            || self.lookup_with_prelude_fallback(name).is_some()
    }

    /// Take one agent turn over the user's text (`agent.md §3.2`) — the real
    /// model↔tool loop (Wave 3 — Advisor MVP core).
    ///
    /// Synchronous to the user's Enter (it runs on the eval thread, holding the
    /// REPL-cadence `&mut CompilerSession`). It is NOT a new state window — every
    /// read goes through the existing introspection surface (the harvest) or
    /// re-enters via `process_commands` (a pull), never a bespoke state view
    /// (BC §6.3). The loop:
    ///   1. If no provider is reachable (dormant), render the U6 notice + return.
    ///   2. Assemble the request: primer + harvest + transcript + tools + turn.
    ///   3. `model.complete(req)` → `Done(prose)` renders in the agent frame and
    ///      breaks; `ToolCalls` runs each as a visible REPL command (read-only
    ///      allowlist), feeds the results back, and loops.
    ///
    /// Read-only Advise mode: a proposed `(defn …)` arrives inside the prose and
    /// is SHOWN (framed), never routed to `eval` — the agent has no write path
    /// this wave (the allowlist excludes writes; §3.2, §4.2).
    pub fn agent_turn(&mut self, text: &str, stdout: &mut impl Write) {
        // The agent must be configured (enable_agent ran) AND have a reachable
        // provider. Absent either, render the U6 dormant notice in the frame so
        // the user sees WHY (`agent.md §2.3`, §6.4 opt-in-twice).
        let dormant_label = match self.agent.as_ref() {
            None => Some("agent not enabled (run with --agent)".to_string()),
            Some(state) if state.is_dormant() => Some(format!(
                "agent enabled but no provider reachable: {}. \
                 Set a provider (Anthropic key + model, or a local Ollama) — \
                 a turn transmits your message + harvested source excerpts to the provider.",
                state.provider_label
            )),
            Some(_) => None,
        };
        if let Some(notice) = dormant_label {
            let _ = write!(stdout, "{}", crate::style::agent_prose(&notice));
            return;
        }

        // Record the user turn on the transcript before assembling (so the turn
        // is part of the session memory even if the model errors).
        if let Some(state) = self.agent.as_mut() {
            state.record_user(text);
        }

        for _ in 0..MAX_TURN_ITERATIONS {
            let req = self.assemble_request(text);

            // Run the model. Take the handle out across the call so we can mutate
            // `self` (for pulls) without aliasing the borrow.
            let resp = match self.agent_complete(&req) {
                Ok(r) => r,
                Err(e) => {
                    let _ = write!(
                        stdout,
                        "{}",
                        crate::style::agent_prose(&format!("agent error: {e}"))
                    );
                    return;
                }
            };

            match resp {
                ModelResponse::Done(prose) => {
                    // Cluster A (§14): the model's terminal prose is markdown —
                    // route it through the agent renderer (markdown→terminal +
                    // ```lisp fences pretty-printed, all inside the `▌` frame),
                    // not raw into `agent_prose`. This is the single styling site
                    // for prose (§14.6 style-once-at-the-leaf).
                    let _ = write!(stdout, "{}", crate::agent::render::render_agent_prose(&prose));
                    if let Some(state) = self.agent.as_mut() {
                        state.record_assistant(&prose);
                    }
                    return;
                }
                ModelResponse::ToolCalls(calls) => {
                    // Each tool call IS a visible REPL command (§4 keystone). The
                    // results are recorded onto the transcript — the next
                    // `assemble_request` folds them back into context from there
                    // (transcript-carried feedback is the only feedback path).
                    //
                    // Record the assistant `tool_use` turn FIRST, before the
                    // matching tool results. The Anthropic Messages API requires
                    // every `tool_result` block to be preceded by an assistant
                    // message carrying the matching `tool_use` block (same id);
                    // omitting it 400s the continuation request (§4.1). The pair
                    // is recorded in order: assistant tool-calls, then the
                    // user-side tool results.
                    if let Some(state) = self.agent.as_mut() {
                        state.record_assistant_tool_calls(calls.clone());
                    }
                    for call in &calls {
                        let result = self.run_pull(call, stdout);
                        if let Some(state) = self.agent.as_mut() {
                            state.record_tool_result(result);
                        }
                    }
                }
            }
        }

        // Iteration budget exhausted without a terminal Done.
        let _ = write!(
            stdout,
            "{}",
            crate::style::agent_prose("agent stopped: too many tool steps without an answer")
        );
    }

    /// Assemble the provider-neutral request for a turn (`agent.md §3.3`): the
    /// always-on primer + the harvested session context + the transcript + the
    /// read-only tool allowlist + the user turn. Tool results from prior loop
    /// steps re-enter via the transcript (recorded by `record_tool_result`); there
    /// is no separate feedback channel.
    pub(crate) fn assemble_request(&self, text: &str) -> AgentRequest {
        let mentions = crate::agent::harvest::mentions_from_text(text);
        let harvest =
            self.harvest_context(&mentions, crate::agent::harvest::DEFAULT_TOKEN_BUDGET);
        let transcript = self
            .agent
            .as_ref()
            .map(|s| s.transcript.clone())
            .unwrap_or_default();
        AgentRequest {
            primer: crate::agent::primer::language_primer().to_string(),
            harvest,
            transcript,
            tools: crate::agent::pull::tool_defs(),
            user: text.to_string(),
        }
    }

    /// Run one completion against the configured model. Split out so the borrow
    /// of `self.agent` is confined here (the model handle is mutably borrowed for
    /// the call; the surrounding loop mutates `self` for pulls separately).
    fn agent_complete(&mut self, req: &AgentRequest) -> Result<ModelResponse, String> {
        let state = self
            .agent
            .as_mut()
            .ok_or_else(|| "agent not enabled".to_string())?;
        let model = state
            .model
            .as_mut()
            .ok_or_else(|| "agent dormant".to_string())?;
        model.complete(req)
    }
}

/// Shared test helpers for the agent unit tests (`mod.rs` + `provider.rs`). A
/// single home for the session builder so the rig-loop test (`provider.rs`) and
/// the classifier/request tests (`mod.rs`) construct sessions the same way
/// (Principle 7 — one source of truth for the fixture).
#[cfg(test)]
pub(crate) mod test_support {
    use super::*;
    use crate::session_v4::{RunMode, SessionSettings};
    use cranelisp_types::CodegenBehaviour;

    /// Build a minimal REPL-mode session for agent unit tests. The classifier is
    /// a pure routing decision and the agent loop only needs a constructed
    /// session (no compiled state), so this builds the lightest viable session.
    pub(crate) fn repl_session() -> CompilerSession {
        let tmp = tempfile::tempdir().unwrap();
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 1,
            run_mode: RunMode::Repl,
        };
        // Keep the tempdir alive for the session's lifetime by leaking it — these
        // are short-lived unit-test sessions and the dir is OS-tmp.
        let root = tmp.keep();
        CompilerSession::new(settings, root, "user")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::test_support::repl_session;

    // spec: repl/spec.md §17.1 — a complete form routes to the deterministic REPL.
    #[test]
    fn form_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("(add-i64 1 2)"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a slash command routes to the deterministic REPL.
    #[test]
    fn slash_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("/list"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — blank / comment-only routes to the REPL.
    #[test]
    fn blank_and_comment_route_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent(""), Classify::Repl);
        assert_eq!(s.classify_for_agent("   "), Classify::Repl);
        assert_eq!(s.classify_for_agent("; just a comment"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a bare KNOWN symbol STILL routes to the REPL
    // (the §4 self-documentation surface is preserved; the agent does NOT
    // intercept a symbol that resolves). `if`/`defn` are special forms seeded at
    // root in every session; an intrinsic type name (`Int`) resolves outside the
    // tables. Both are "known" by the same resolution path `/info`/§4 use.
    #[test]
    fn bare_known_symbol_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("if"), Classify::Repl);
        assert_eq!(s.classify_for_agent("defn"), Classify::Repl);
        assert_eq!(s.classify_for_agent("Int"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a literal always counts as known and routes to
    // the REPL (the §4 bare-value display).
    #[test]
    fn bare_literal_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("42"), Classify::Repl);
        assert_eq!(s.classify_for_agent("3.14"), Classify::Repl);
        assert_eq!(s.classify_for_agent("true"), Classify::Repl);
        assert_eq!(s.classify_for_agent("\"hi\""), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a bare UNKNOWN symbol (a bare word, or a typo)
    // routes to the agent: it does NOT resolve through the introspection path,
    // so the refined classifier hands it to the agent rather than the §4
    // "unbound" message. (Feature-off this divergence does not exist — see the
    // Lane-B guard in tests/agent.rs.)
    #[test]
    fn bare_unknown_symbol_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent("yes") {
            Classify::Agent(text) => assert_eq!(text, "yes"),
            other => panic!("expected Agent for bare unknown 'yes', got {other:?}"),
        }
        match s.classify_for_agent("lenght") {
            Classify::Agent(text) => assert_eq!(text, "lenght"),
            other => panic!("expected Agent for typo 'lenght', got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — a compound form (list / vector) is code and
    // routes to the REPL, regardless of whether its head resolves.
    #[test]
    fn compound_form_routes_to_repl() {
        let s = repl_session();
        // `add-i64` is not bound in this bare session, but a list is code.
        assert_eq!(s.classify_for_agent("(add-i64 1 2)"), Classify::Repl);
        assert_eq!(s.classify_for_agent("[1 2 3]"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — multi-word prose parses as a run of bare
    // symbols (`Ok`), but those symbols do not resolve, so the refined
    // classifier routes it to the agent (the any-unbound rule). This is the U1
    // gap the refinement closes: parseability is insufficient.
    #[test]
    fn unsigiled_multiword_prose_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent("how do I define a function") {
            Classify::Agent(text) => assert_eq!(text, "how do I define a function"),
            other => panic!("expected Agent for prose, got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — a buffer mixing a known bare symbol with an
    // unknown one routes to the agent (any-unbound wins). `if` is known; `frob`
    // is not.
    #[test]
    fn mixed_known_and_unknown_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent("if frob") {
            Classify::Agent(text) => assert_eq!(text, "if frob"),
            other => panic!("expected Agent for mixed known+unknown, got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — a non-bracket parse error (stray `)`,
    // unterminated string) routes to the agent.
    #[test]
    fn non_bracket_parse_error_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent(")") {
            Classify::Agent(text) => assert_eq!(text, ")"),
            other => panic!("expected Agent for stray ')', got {other:?}"),
        }
        match s.classify_for_agent("\"unterminated") {
            Classify::Agent(_) => {}
            other => panic!("expected Agent for unterminated string, got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — an unclosed paren routes to continuation, NOT
    // the agent (the parens-balanced gate).
    #[test]
    fn unclosed_paren_routes_to_continuation() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("(add-i64 1"), Classify::Continuation);
    }

    // -----------------------------------------------------------------------
    // Wave-3 request-assembly / harvest — the `/dev`-owned request-content unit
    // tests (tests/plan/agent-testing-strategy.md §1.1(b), §3.2). These assert
    // WHAT the agent sent (the request the stub captured): the primer is always
    // present; the harvest carries the right slice; the transcript carries prior
    // turns; the tools are exactly the read-only allowlist. They run unit-tier
    // because the assembled `CompletionRequest` never surfaces through stdout.
    // -----------------------------------------------------------------------

    use crate::agent::stub::StubModel;
    use crate::agent::types::{AgentState, ModelResponse};
    use std::sync::{Arc, Mutex};

    /// Build a REPL session whose agent is wired to a deterministic stub model
    /// running `script`. Returns the session + the shared request-capture handle
    /// (assert against the requests the stub received).
    fn session_with_stub(
        script: Vec<ModelResponse>,
    ) -> (CompilerSession, Arc<Mutex<Vec<AgentRequest>>>) {
        let mut s = repl_session();
        let stub = StubModel::new(script);
        let capture = stub.requests.clone();
        s.agent = Some(AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(stub)),
            provider_label: "stub (test)".to_string(),
        });
        (s, capture)
    }

    /// Drive one turn over `text`, discarding rendered output.
    fn drive(s: &mut CompilerSession, text: &str) {
        let mut sink: Vec<u8> = Vec::new();
        s.agent_turn(text, &mut sink);
    }

    // spec: repl/spec.md §17 — every request carries the always-on language
    // primer (rung 2). The model is grounded in Cranelisp on every turn.
    #[test]
    fn request_always_carries_primer() {
        let (mut s, capture) = session_with_stub(vec![ModelResponse::Done("hi".to_string())]);
        drive(&mut s, "how do I define a function");
        let reqs = capture.lock().unwrap();
        assert_eq!(reqs.len(), 1, "one completion call for a Done turn");
        assert!(
            reqs[0].primer.contains(":Type"),
            "primer must carry the :Type convention, got: {}",
            &reqs[0].primer[..reqs[0].primer.len().min(80)]
        );
        assert!(reqs[0].primer.contains("deftype"), "primer must carry special forms");
    }

    // spec: repl/spec.md §17 — the read-only tool allowlist is offered every
    // turn, and contains NO write/`/sh`/submit tools (+neg, the consent gate).
    #[test]
    fn request_tools_are_read_only_allowlist() {
        let (mut s, capture) = session_with_stub(vec![ModelResponse::Done("ok".to_string())]);
        drive(&mut s, "anything");
        let reqs = capture.lock().unwrap();
        let names: Vec<&str> = reqs[0].tools.iter().map(|t| t.name.as_str()).collect();
        assert!(names.contains(&"source"), "source must be offered: {names:?}");
        assert!(names.contains(&"refs"));
        // +neg: no write tool leaks into the offered set.
        assert!(!names.contains(&"sh"), "no /sh tool: {names:?}");
        assert!(!names.contains(&"submit"));
        assert!(!names.iter().any(|n| n.contains("def")), "no def/write tool: {names:?}");
    }

    // spec: repl/spec.md §17 — a fn NAMED in the turn is harvested (its source);
    // a defined-but-UNMENTIONED fn is ABSENT (+neg, the ranker is selective, not
    // a dump — agent.md §5.1). The harvester's mentioned-fn arm reads the live
    // introspection source for a name that (a) appears in the turn AND (b) is
    // mentionable (resolves in some table). We inject both: a slot-less table
    // entry (so `symbol_is_mentionable` is true) + an introspection record (the
    // source). `target` is mentioned; `unrelated` is not — so the +neg holds.
    #[test]
    fn harvest_includes_mentioned_excludes_unmentioned() {
        let s = repl_session();
        let module = s.current_module_path();
        // Slot-less table entries so both names are "mentionable" (resolve).
        {
            use cranelisp_types::{DefKind, ModuleEntry, Symbol, Visibility};
            if let Some(mut table) = s.shared.symbol_tables.get_mut(&module) {
                for name in ["target", "unrelated"] {
                    let entry = ModuleEntry::def(
                        empty_scheme(),
                        DefKind::PrimitiveExtern,
                    )
                    .visibility(Visibility::Public)
                    .build();
                    table.insert(Symbol::from(name), entry);
                }
            }
        }
        // Introspection sources (the bodies the mentioned-fn arm harvests).
        if let Some(intr) = s.shared.introspection.as_ref() {
            let mk = |name: &str, body: &str| {
                (
                    cranelisp_types::FQSymbol {
                        module: module.clone(),
                        symbol: cranelisp_types::Symbol::from(name),
                    },
                    crate::session_v4::Introspection {
                        source: Some(body.to_string()),
                        sexp: None,
                        expanded: None,
                        ast: None,
                        clif_ir: None,
                        code_size: None,
                    },
                )
            };
            let (k1, v1) = mk("target", "(defn target [x] (mul-by-two x))");
            let (k2, v2) = mk("unrelated", "(defn unrelated [y] (negate-it y))");
            intr.insert(k1, v1);
            intr.insert(k2, v2);
        }
        // Mention only `target`.
        let harvest = s.harvest_context(
            &["target".to_string()],
            crate::agent::harvest::DEFAULT_TOKEN_BUDGET,
        );
        assert!(harvest.contains("Current module"), "pin header present: {harvest}");
        assert!(
            harvest.contains("mul-by-two"),
            "the mentioned fn `target` must be harvested: {harvest}"
        );
        // +neg: the unmentioned fn must NOT be pulled in by the mention arm.
        assert!(
            !harvest.contains("negate-it"),
            "an unmentioned fn must be absent from the harvest: {harvest}"
        );
    }

    /// A minimal empty scheme for slot-less test table entries (mirrors the
    /// `expander.rs` test helper of the same name).
    fn empty_scheme() -> cranelisp_types::Scheme {
        cranelisp_types::Scheme {
            type_vars: Vec::new(),
            constraints: std::collections::HashMap::new(),
            ty: cranelisp_types::Type::Int,
        }
    }

    // spec: repl/spec.md §17 — under a TIGHT budget the harvest degrades per the
    // §5.4 ladder: the current-module pin survives at the floor; the optional
    // mentioned-module preamble/exports block drops out (+neg). Reads the
    // `module_preamble` field (FIXME 0428) when the block is included.
    #[test]
    fn harvest_degrades_under_tight_budget_keeps_pin() {
        let s = repl_session();
        // Create a second module with a preamble + a public export, and "mention"
        // it; under a tiny budget its block must drop while the pin survives.
        let other = cranelisp_types::ModuleFullPath::from("geometry");
        {
            let mut table = crate::code::SessionSymbolTable::new_with_params(other.clone());
            table.module_preamble = Some(";; geometry — points and shapes.".to_string());
            s.shared.symbol_tables.insert(other.clone(), table);
        }
        // Tight budget: 1 token (~4 chars) — only the pin (always-included) fits.
        let tight = s.harvest_context(&["geometry".to_string()], 1);
        assert!(tight.contains("Current module"), "pin survives the floor: {tight}");
        assert!(
            !tight.contains("geometry preamble") && !tight.contains("geometry exports"),
            "the mentioned-module block must drop under a 1-token budget: {tight}"
        );
        // Generous budget: the mentioned module's preamble + exports appear, and
        // the preamble text is read from `module_preamble` (FIXME 0428).
        let roomy = s.harvest_context(&["geometry".to_string()], 4000);
        assert!(roomy.contains("geometry — points and shapes"),
            "module_preamble must be read into the harvest: {roomy}");
    }

    // spec: repl/spec.md §17 — across a multi-step turn (ToolCalls then Done),
    // the SECOND request carries the prior turn's tool result fed back into
    // context (rung 4 result-re-enters-context, agent.md §4.1). Uses an
    // allowlisted read command on a DEFINED symbol so the pull runs through
    // process_commands and produces real output.
    //
    // S88 pull-loop fix — STRENGTHENED: the prior version pulled `/list` and
    // asserted only the PRESENCE of a `Turn::ToolResult`. That passed even
    // though the live agent looped, because presence is not content: the model
    // loops precisely when the fed-back tool_result content is EMPTY. This now
    // asserts the fed-back tool_result `output` is NON-EMPTY and CONTAINS the
    // pulled command's actual output (the source text) — the assertion that
    // would have caught the loop.
    #[test]
    fn tool_result_re_enters_next_request() {
        // Define `f` with introspection source so `/source f` yields real output.
        let mut s = repl_session();
        let module = s.current_module_path();
        {
            use cranelisp_types::{DefKind, ModuleEntry, Symbol, Visibility};
            if let Some(mut table) = s.shared.symbol_tables.get_mut(&module) {
                let entry = ModuleEntry::def(empty_scheme(), DefKind::PrimitiveExtern)
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
        // Wire the stub with a source pull then a Done.
        let stub = StubModel::new(vec![
            ModelResponse::ToolCalls(vec![crate::agent::types::ToolCallRequest {
                id: "c1".to_string(),
                name: "source".to_string(),
                argument: "f".to_string(),
            }]),
            ModelResponse::Done("done".to_string()),
        ]);
        let capture = stub.requests.clone();
        s.agent = Some(AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(stub)),
            provider_label: "stub (test)".to_string(),
        });
        drive(&mut s, "show me the source of f");

        let reqs = capture.lock().unwrap();
        assert_eq!(reqs.len(), 2, "a pull turn drives two completion calls");
        // The second request's transcript must carry the tool-result turn fed
        // back — AND its `output` must carry the actual command output, not be
        // empty (the loop trigger).
        let tool_result_output = reqs[1].transcript.iter().find_map(|t| match t {
            crate::agent::types::Turn::ToolResult(r) => Some(r.output.clone()),
            _ => None,
        });
        let output = tool_result_output.expect("turn-2 request must carry the fed-back tool result");
        assert!(!output.is_empty(), "the fed-back tool_result content must NOT be empty");
        assert!(
            output.contains("(defn f [x] x)"),
            "the fed-back tool_result must carry the command output (the source), got: {output:?}"
        );
        // And the original user turn is in the transcript too.
        let has_user = reqs[1].transcript.iter().any(
            |t| matches!(t, crate::agent::types::Turn::User(u) if u == "show me the source of f"),
        );
        assert!(has_user, "turn-2 request must carry the user turn");
    }

    // spec: repl/spec.md §17.3 — a write/non-read tool-call is REFUSED by the
    // allowlist: nothing is executed, and the model gets a refusal back (+neg,
    // the read-only Advise consent boundary). The turn still completes (Done).
    #[test]
    fn write_tool_call_is_refused() {
        let (mut s, _capture) = session_with_stub(vec![
            ModelResponse::ToolCalls(vec![crate::agent::types::ToolCallRequest {
                id: "c1".to_string(),
                name: "sh".to_string(),
                argument: "rm -rf /".to_string(),
            }]),
            ModelResponse::Done("ok".to_string()),
        ]);
        let mut sink: Vec<u8> = Vec::new();
        s.agent_turn("run a shell command", &mut sink);
        let out = String::from_utf8_lossy(&sink);
        assert!(out.contains("refused"), "a write must be refused: {out}");
        // The refusal turn is recorded as a tool result with a refusal output.
        let refused = s
            .agent
            .as_ref()
            .unwrap()
            .transcript
            .iter()
            .any(|t| matches!(t, crate::agent::types::Turn::ToolResult(r) if r.output.contains("refused")));
        assert!(refused, "refusal must be fed back to the model");
    }

    // spec: repl/spec.md §17 — `/context <path>` dumps the FULL assembled agent
    // request (exactly what `agent_turn` would send) to a file, reusing the live
    // `assemble_request` (the primer + the harvested session context + the
    // transcript). The dump must contain the primer marker AND the harvested
    // symbol/source (proving it captured the REAL request, not a stub), and have
    // the labeled section headers. CRITICAL: it works with NO provider configured
    // (dormant) — `assemble_request` is pure and needs no API key.
    #[test]
    fn context_dumps_assembled_request_to_file_when_dormant() {
        // A session with a defined `f` carrying introspection source, mentioned
        // in a prior transcript turn — so the harvest pulls f's source in.
        let mut s = repl_session();
        let module = s.current_module_path();
        {
            use cranelisp_types::{DefKind, ModuleEntry, Symbol, Visibility};
            if let Some(mut table) = s.shared.symbol_tables.get_mut(&module) {
                let entry = ModuleEntry::def(empty_scheme(), DefKind::PrimitiveExtern)
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
                    source: Some("(defn f [x] (some-marker-body x))".to_string()),
                    sexp: None,
                    expanded: None,
                    ast: None,
                    clif_ir: None,
                    code_size: None,
                },
            );
        }
        // Dormant agent: enabled but NO provider/model. `/context` must still
        // succeed (assemble_request is pure).
        s.agent = Some(crate::agent::provider::build_agent_state(false));
        assert!(
            s.agent.as_ref().unwrap().is_dormant(),
            "the fixture agent must be dormant (no provider) — that is the point"
        );
        // Record a transcript turn mentioning `f` so the harvest pulls its source.
        if let Some(state) = s.agent.as_mut() {
            state.record_user("show me the source of f");
        }

        let tmp = tempfile::tempdir().unwrap();
        let path = tmp.path().join("ctx.txt");
        let path_str = path.to_string_lossy().to_string();

        let confirmation = s.handle_context(&path_str);
        assert!(
            confirmation.contains("wrote agent context") && confirmation.contains("chars"),
            "confirmation line: {confirmation}"
        );

        // The file exists and is non-empty.
        let dumped = std::fs::read_to_string(&path).expect("the context file must exist");
        assert!(!dumped.is_empty(), "the dumped context must be non-empty");

        // The three required section headers are present (send-order).
        assert!(dumped.contains("=== SYSTEM PRIMER ==="), "primer header: {dumped}");
        assert!(dumped.contains("=== HARVESTED CONTEXT ==="), "harvest header");
        assert!(dumped.contains("=== TRANSCRIPT ==="), "transcript header");

        // It dumped the REAL assembled request: the primer marker (:Type) AND the
        // harvested symbol/source (proving harvest ran), AND the transcript turn.
        assert!(dumped.contains(":Type"), "the real language primer must be present");
        assert!(
            dumped.contains("some-marker-body"),
            "the harvested source of `f` must be present (proves harvest ran): {dumped}"
        );
        assert!(
            dumped.contains("show me the source of f"),
            "the recorded transcript turn must be present: {dumped}"
        );
    }

    // spec: repl/spec.md §17 — `/context <bad/path>` returns a graceful error
    // line (no panic) when the target is unwritable.
    #[test]
    fn context_bad_path_returns_graceful_error() {
        let s = repl_session();
        // A path inside a non-existent directory cannot be written.
        let out = s.handle_context("/nonexistent-dir-xyz/sub/ctx.txt");
        assert!(out.starts_with("error:"), "expected a graceful error line, got: {out}");
        // An empty path is a usage hint, not a panic.
        assert_eq!(s.handle_context(""), "Usage: /context <path>");
    }

    // spec: repl/spec.md §17 — a dormant agent (no provider) renders the U6
    // "no provider" notice in the agent frame and does NOT call any model.
    #[test]
    fn dormant_agent_renders_notice() {
        let mut s = repl_session();
        s.agent = Some(crate::agent::provider::build_agent_state(false));
        let mut sink: Vec<u8> = Vec::new();
        s.agent_turn("hello", &mut sink);
        let out = String::from_utf8_lossy(&sink);
        // The prose frame gutter must be present (rendered through agent_prose).
        assert!(out.contains('\u{258c}'), "dormant notice must be framed: {out}");
    }
}
