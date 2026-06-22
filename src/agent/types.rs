// agent/types.rs — the agent's provider-neutral turn vocabulary + AgentState.
//
// design/int/agent.md §3.3 (request assembly vocabulary), §3.4 (agent state),
// §6.1 (what `agent_turn` speaks). These types are deliberately rig-free: the
// harvester (§5), primer (§7), pull (§4), and transcript machinery never see a
// rig type. `agent/request.rs` is the single membrane that translates this
// vocabulary into rig's `CompletionRequest` / `Message` / tool-call types.
//
// Object-safety membrane (Wave-3 implementation note). The design names the
// model handle `Box<dyn rig::completion::CompletionModel>` (§3.4), but rig's
// `CompletionModel` trait is NOT object-safe in 0.39.0 — it carries associated
// types (`Response`, `StreamingResponse`, `Client`), a `Clone` bound, and async
// methods (`-> impl Future`). A `Box<dyn CompletionModel>` does not compile. We
// preserve the design INTENT (a provider-neutral, runtime-selected, stub-mockable
// boundary — §6, Principle 5) with a thin object-safe internal trait `AgentModel`
// (this file): the stub and each rig-backed provider implement `AgentModel`,
// which speaks only this neutral vocabulary. rig's `CompletionModel` is still the
// real wire boundary inside the rig-backed `AgentModel` impl (`provider.rs`). The
// object-safety correction is filed as FIXME `target: /design`.

#![cfg(feature = "agent")]

/// One scripted/observed assistant response from the model, decomposed into the
/// two cases `agent_turn`'s loop branches on (§3.2). The membrane (`AgentModel`)
/// erases rig's `AssistantContent` into this neutral shape: rig `Text` →
/// `Done(prose)` carrying the accumulated prose; rig `ToolCall`(s) → `ToolCalls`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelResponse {
    /// Terminal: render `prose` in the agent frame and break the loop (§3.2).
    /// May carry a proposed `(defn …)` inside the prose — in read-only Advise
    /// mode it is SHOWN, never submitted (§3.2 read-only).
    Done(String),
    /// The model asks to run one or more REPL commands as tools (§4). Each is
    /// synthesized into a command string, run through `process_commands`, and
    /// the results fed back into the next request.
    ToolCalls(Vec<ToolCallRequest>),
}

/// A single tool-call request from the model — a read-only REPL command and its
/// argument(s) (§4.2). Provider-neutral: rig's `ToolCall { function: { name,
/// arguments } }` is lowered to this by the membrane. `name` is the bare command
/// (e.g. `"source"`, `"info"`); `argument` is the symbol/expr (e.g. `"foo"`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolCallRequest {
    /// The provider-supplied call id, echoed back with the result so multi-call
    /// turns correlate (some providers require it). Empty string if absent.
    pub id: String,
    /// The tool name = the bare REPL command word (no leading slash).
    pub name: String,
    /// The single string argument (a symbol name or expression).
    pub argument: String,
}

/// The result of running a pulled command, fed back to the model as a tool
/// result (§4.1). `command` is the rendered command line (e.g. `"/source foo"`)
/// for the transcript; `output` is the command's textual result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolCallResult {
    /// The originating call id (correlates with `ToolCallRequest::id`).
    pub id: String,
    /// The synthesized command line, as it would be typed.
    pub command: String,
    /// The command's textual output (or a refusal notice for a denied write).
    pub output: String,
}

/// One entry in the session transcript (§3.4) — a prior turn's user message,
/// model prose, model tool-call request(s), or tool-result, kept so each turn
/// carries the prior context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Turn {
    /// The user's message (the `/ask` text or the classified prose).
    User(String),
    /// The model's prose reply.
    Assistant(String),
    /// The model's tool-call request(s) for one loop step — the assistant
    /// `tool_use` turn (§4.1). The Anthropic Messages API REQUIRES that every
    /// `tool_result` block be preceded by an assistant message carrying the
    /// matching `tool_use` block (same id), so the loop records this turn BEFORE
    /// the `ToolResult`(s) it produced. `request.rs` lowers it to a rig
    /// assistant `Message` whose content is the `tool_call` block(s).
    AssistantToolCalls(Vec<ToolCallRequest>),
    /// A pulled command + its result (rendered as-typed in the transcript).
    ToolResult(ToolCallResult),
}

/// A tool the model may emit — exactly a read-only REPL command (§4.2). The
/// allowlist (`pull.rs`) is the set of these; the model is told about them in
/// the request's tool definitions (`request.rs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolDef {
    /// The bare command word (no slash), e.g. `"source"`.
    pub name: String,
    /// A one-line description for the model.
    pub description: String,
}

/// The object-safe internal boundary `agent_turn` drives (§6, the membrane).
///
/// The stub and each rig-backed provider implement this. It speaks only the
/// neutral vocabulary above — no rig type crosses it — so the agent loop is
/// tested against a deterministic stub with zero network (Principle 5,
/// `tests/plan/agent-testing-strategy.md §1`). `complete` is synchronous from
/// the loop's perspective: a rig-backed impl `block_on`s the async rig call
/// internally (`provider.rs`); the stub returns immediately from its script.
pub trait AgentModel: Send {
    /// Run one completion over the assembled request, returning the decomposed
    /// response. The request is the assembled prompt: system primer + harvest +
    /// transcript + tool defs + the current user turn.
    fn complete(&mut self, request: &AgentRequest) -> Result<ModelResponse, String>;
}

/// The provider-neutral assembled request (§3.3). `request.rs` translates this
/// to rig's `CompletionRequest`; the stub records it for assertion.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct AgentRequest {
    /// The always-on language primer (§7) — system content.
    pub primer: String,
    /// The harvested session context (§5) — system content.
    pub harvest: String,
    /// The conversation transcript so far this session (§3.4).
    pub transcript: Vec<Turn>,
    /// The read-only tool allowlist offered to the model (§4.2).
    pub tools: Vec<ToolDef>,
    /// The current user turn text.
    pub user: String,
}

/// The persistent agent state (§3.4) — transcript + the model handle. Lives on
/// `CompilerSession` as a `#[cfg(feature="agent")] Option<AgentState>` so
/// feature-off carries zero bytes. `None` until the first `/ask` or agent route.
pub struct AgentState {
    /// The conversation transcript (§3.4) — oldest turns drop first under budget.
    pub transcript: Vec<Turn>,
    /// The model handle (the membrane). `None` ⇒ dormant (no reachable provider,
    /// the U6 opt-in-twice "no key" path — §6.4); `/ask` then says so.
    pub model: Option<Box<dyn AgentModel>>,
    /// A short human label for the active provider (e.g. "anthropic", "ollama",
    /// "stub") or the dormancy reason, for the U6 disclosure notice.
    pub provider_label: String,
    /// `--yes` autonomous-submit (§20.1). When true, the write-consent gate
    /// (`run_submit` step 2, §15.2) auto-accepts WITHOUT a `[y/N]` line-read —
    /// the policy knob. CRITICAL (§20.3): this bit lives in the CONSENT branch
    /// only; it is read solely by `agent_auto_accept()` at the gate site and is
    /// STRUCTURALLY unreachable from the validator (`validate_forms_dry_run`
    /// takes no `auto_accept` param). `--yes` skips consent, NEVER validation.
    pub auto_accept: bool,
    /// Once-per-session flag for the §20.4 first-use notice — fired the first
    /// time an autonomous (`--yes`) write is auto-accepted, then never again.
    pub auto_accept_notice_shown: bool,
    /// Per-TURN bookkeeping for the user-facing give-up line (Phase-6, S89). A
    /// `submit` whose pre-flight repair cap exhausts feeds the MODEL an honest
    /// abort (`run_submit`), but it must NOT print the user-facing
    /// "I couldn't produce a definition" line per-failed-submit mid-turn — the
    /// turn may CONTINUE and ultimately submit cleanly (live trace, S89). These
    /// flags are reset at every `agent_turn` start and consulted at TRUE
    /// turn-end: the give-up line prints at most once, only when the turn
    /// produced NO committed write (`submit_committed == false`) AND at least one
    /// submit gave up (`submit_gave_up == true`), AND the turn did not end on a
    /// `Done` answer (the Done arm returns before the end-of-turn give-up site).
    pub submit_gave_up: bool,
    /// Set when a `submit` actually commits a definition this turn (the success
    /// that suppresses the give-up line — the turn "produced something").
    pub submit_committed: bool,
}

impl AgentState {
    /// True when no provider is reachable (the dormant / "no key" state — §6.4).
    pub fn is_dormant(&self) -> bool {
        self.model.is_none()
    }
}

/// The consent line-read seam for the Build write gate (§15.2 step 2).
///
/// `run_submit`'s confirm gate is a synchronous blocking line-read at the REPL
/// cadence (§15.2 step 2 / BC §6.3 — a prompt boundary, not a new state window).
/// The production reader (`main.rs`) pulls the next line off the REPL's own stdin
/// iterator; unit/e2e tests script the answers. Returns `None` at EOF (treated as
/// a decline). The reader is passed into `agent_turn` so the confirm gate reads
/// the SAME stdin the REPL loop reads — it never opens a second input handle.
pub trait ConsentReader {
    /// Read one line of consent input (without the trailing newline). `None` at
    /// EOF / no further input — the gate treats that as a decline.
    fn read_consent_line(&mut self) -> Option<String>;
}

/// A `ConsentReader` that never yields a line (EOF) — the no-consent reader used
/// where a write gate cannot be reached (a read-only pull through
/// `process_commands`). Any confirm gate it backs declines by default.
pub struct NoConsent;

impl ConsentReader for NoConsent {
    fn read_consent_line(&mut self) -> Option<String> {
        None
    }
}

/// A `ConsentReader` adapter over any `FnMut() -> Option<String>` — lets
/// `main.rs` wrap its stdin-lines iterator (and tests wrap a scripted vec)
/// without a bespoke type each.
pub struct FnConsent<F: FnMut() -> Option<String>>(pub F);

impl<F: FnMut() -> Option<String>> ConsentReader for FnConsent<F> {
    fn read_consent_line(&mut self) -> Option<String> {
        (self.0)()
    }
}

impl AgentRequest {
    /// Render the assembled request as readable, labeled text — exactly the
    /// content `agent_turn` sends to the model, in send-order. The `/context`
    /// debug command (`repl.rs`) writes this to a file so a human can inspect
    /// the grounding/harvest/transcript WITHOUT making an API call. This is a
    /// faithful flattening of the SAME `AgentRequest` `assemble_request` builds,
    /// so a reader can trust it as ground truth (it is the request, not a
    /// reconstruction — Principle 7).
    ///
    /// Sections, in the order the provider sees them (`request.rs`: primer +
    /// harvest form the system preamble, the transcript is the chat history, the
    /// last turn is the prompt the model answers):
    ///   `=== SYSTEM PRIMER ===`      — the always-on language primer (§7).
    ///   `=== HARVESTED CONTEXT ===`  — the push-context block (§5), or `(none)`.
    ///   `=== TOOLS (read-only) ===`  — the offered allowlist, name + description.
    ///   `=== TRANSCRIPT ===`         — every turn so far, oldest first; the
    ///                                  final turn is the prompt the model answers.
    pub fn render_for_debug(&self) -> String {
        let mut out = String::new();

        // A cheap, honest budget note: the approximate total system+transcript
        // character size (the model's wire payload is dominated by this).
        let char_total = self.primer.len()
            + self.harvest.len()
            + self
                .transcript
                .iter()
                .map(turn_debug_len)
                .sum::<usize>()
            + self.user.len();
        out.push_str(&format!(
            "=== BUDGET (approx) ===\n{char_total} chars (~{} tokens @4ch/tok)\n\n",
            char_total / 4
        ));

        out.push_str("=== SYSTEM PRIMER ===\n");
        out.push_str(&self.primer);
        if !self.primer.ends_with('\n') {
            out.push('\n');
        }
        out.push('\n');

        out.push_str("=== HARVESTED CONTEXT ===\n");
        if self.harvest.is_empty() {
            out.push_str("(none)\n");
        } else {
            out.push_str(&self.harvest);
            if !self.harvest.ends_with('\n') {
                out.push('\n');
            }
        }
        out.push('\n');

        out.push_str("=== TOOLS (read-only) ===\n");
        if self.tools.is_empty() {
            out.push_str("(none)\n");
        } else {
            for t in &self.tools {
                out.push_str(&format!("{} — {}\n", t.name, t.description));
            }
        }
        out.push('\n');

        out.push_str("=== TRANSCRIPT ===\n");
        if self.transcript.is_empty() {
            out.push_str("(empty — the current user turn is the prompt)\n");
        } else {
            for turn in &self.transcript {
                out.push_str(&render_turn_for_debug(turn));
            }
        }
        out.push('\n');

        out.push_str("=== CURRENT USER TURN ===\n");
        out.push_str(&self.user);
        if !self.user.ends_with('\n') {
            out.push('\n');
        }

        out
    }
}

/// The wire-validity invariant over a recorded transcript (the Anthropic
/// Messages API tool_use↔tool_result pairing rule, both directions). The S88/S89
/// 400 class lived in transcript paths that violated this — a `tool_result` with
/// no preceding matching `tool_use` (the give-up/decline corner), or a
/// `tool_use` with no following `tool_result` (the repair-feedback corner). The
/// deterministic stub sits ABOVE rig and never enforces this, so CI stayed green
/// while live 400'd. This is the central guard: called as a checked
/// `debug_assert!` at every `assemble_request` site so a malformed transcript
/// fails fast in tests instead of reaching the API.
///
/// The rules encoded (both directions):
///   1. **Forward** — every `AssistantToolCalls(ids)` turn is IMMEDIATELY followed
///      by `ToolResult` turn(s) that, taken together, cover EXACTLY those ids (in
///      any order; one tool_result per id; no extra, no missing). The Anthropic
///      API requires the next user message after a tool_use to carry the matching
///      tool_results.
///   2. **Backward** — every `ToolResult(id)` turn is IMMEDIATELY preceded (across
///      the run of contiguous tool_results, back to the assistant turn) by an
///      `AssistantToolCalls` turn carrying a matching `tool_use(id)`. A
///      `ToolResult` after a `User`/`Assistant`(prose) turn is the violation that
///      caused the current (give-up/decline) 400.
///
/// Note on id-correlation: the wire membrane (`request.rs::tool_call_id`) falls
/// back to the rendered command string when the provider supplied no id, so the
/// invariant here is checked on the SAME effective key (the `id` field, with an
/// empty-id ⇒ command fallback) the wire uses, to stay faithful to what the
/// provider actually receives.
pub fn assert_transcript_wire_valid(transcript: &[Turn]) -> Result<(), String> {
    // The effective correlation key for a tool_use id (empty ⇒ no fallback here:
    // the assistant tool_use carries the raw id; pairing is by raw id on BOTH
    // sides via `tool_result_key`, so empty ids on both sides still correlate by
    // the command string).
    let mut i = 0;
    while i < transcript.len() {
        match &transcript[i] {
            Turn::AssistantToolCalls(calls) => {
                if calls.is_empty() {
                    return Err(format!(
                        "turn {i}: AssistantToolCalls is empty (no tool_use blocks)"
                    ));
                }
                // The set of ids this assistant turn promised.
                let want: Vec<String> = calls.iter().map(|c| tool_use_key(c)).collect();
                // Collect the contiguous run of ToolResult turns that follow.
                let mut got: Vec<String> = Vec::new();
                let mut j = i + 1;
                while j < transcript.len() {
                    if let Turn::ToolResult(r) = &transcript[j] {
                        got.push(tool_result_key(r));
                        j += 1;
                    } else {
                        break;
                    }
                }
                // Forward: every promised id is covered exactly once, no extras.
                if got.is_empty() {
                    return Err(format!(
                        "turn {i}: AssistantToolCalls(ids={want:?}) is not followed by any \
                         tool_result — a tool_use with no matching tool_result (the \
                         repair-feedback / give-up unpaired-tool_use 400)"
                    ));
                }
                let mut remaining = want.clone();
                for g in &got {
                    match remaining.iter().position(|w| w == g) {
                        Some(pos) => {
                            remaining.remove(pos);
                        }
                        None => {
                            return Err(format!(
                                "turn {i}: tool_result id {g:?} has no matching tool_use in the \
                                 preceding AssistantToolCalls(ids={want:?}) (unexpected \
                                 tool_use_id in tool_result — the current 400)"
                            ));
                        }
                    }
                }
                if !remaining.is_empty() {
                    return Err(format!(
                        "turn {i}: AssistantToolCalls promised ids {want:?} but tool_results \
                         covered {got:?} — uncovered tool_use ids {remaining:?} (a tool_use \
                         with no matching tool_result)"
                    ));
                }
                i = j;
            }
            Turn::ToolResult(r) => {
                // A ToolResult NOT preceded by an AssistantToolCalls turn — the
                // exact backward violation behind the give-up/decline 400.
                return Err(format!(
                    "turn {i}: ToolResult(id={:?}) has no preceding AssistantToolCalls turn \
                     carrying a matching tool_use — a tool_result with no corresponding \
                     tool_use block in the previous message (the give-up/decline 400)",
                    tool_result_key(r)
                ));
            }
            Turn::User(_) | Turn::Assistant(_) => {
                i += 1;
            }
        }
    }
    Ok(())
}

/// The correlation key for an assistant tool_use — the raw provider id (the
/// real Anthropic pairing key). In every live flow the id is non-empty
/// (`toolu_…` from the provider, `stub-N` / `s1` from the test stub), so the
/// invariant correlates purely by id, as the API does.
fn tool_use_key(c: &ToolCallRequest) -> String {
    c.id.clone()
}

/// The correlation key for a tool_result — the raw id it echoes back (the same
/// key the matching tool_use carries). Matches the real Anthropic correlation
/// (id-to-id); the wire membrane's command-fallback is only for the never-live
/// empty-id case.
fn tool_result_key(r: &ToolCallResult) -> String {
    r.id.clone()
}

/// The approximate character length of a transcript turn, for the budget note.
fn turn_debug_len(turn: &Turn) -> usize {
    match turn {
        Turn::User(t) | Turn::Assistant(t) => t.len(),
        Turn::AssistantToolCalls(calls) => {
            calls.iter().map(|c| c.name.len() + c.argument.len()).sum()
        }
        Turn::ToolResult(r) => r.command.len() + r.output.len(),
    }
}

/// Render one transcript turn as a labeled block for `render_for_debug`.
fn render_turn_for_debug(turn: &Turn) -> String {
    match turn {
        Turn::User(text) => format!("[user] {text}\n"),
        Turn::Assistant(text) => format!("[assistant] {text}\n"),
        Turn::AssistantToolCalls(calls) => {
            let mut s = String::from("[assistant tool calls]\n");
            for c in calls {
                s.push_str(&format!("  - {} {} (id={})\n", c.name, c.argument, c.id));
            }
            s
        }
        Turn::ToolResult(r) => {
            format!("[tool result] {}\n{}\n", r.command, r.output)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tc(id: &str) -> ToolCallRequest {
        ToolCallRequest { id: id.to_string(), name: "submit".to_string(), argument: "x".to_string() }
    }
    fn tr(id: &str) -> ToolCallResult {
        ToolCallResult {
            id: id.to_string(),
            command: "submit x".to_string(),
            output: "ok".to_string(),
        }
    }

    // spec: repl/spec.md §17 — a well-formed transcript (user, prose, and a
    // paired tool_use→tool_result) is wire-valid in both directions.
    #[test]
    fn well_formed_transcript_is_valid() {
        let t = vec![
            Turn::User("hi".to_string()),
            Turn::AssistantToolCalls(vec![tc("toolu_1")]),
            Turn::ToolResult(tr("toolu_1")),
            Turn::Assistant("done".to_string()),
        ];
        assert!(assert_transcript_wire_valid(&t).is_ok());
    }

    // spec: repl/spec.md §17 — a prose-only transcript (no tool blocks) is valid.
    #[test]
    fn prose_only_is_valid() {
        let t = vec![Turn::User("hi".to_string()), Turn::Assistant("hello".to_string())];
        assert!(assert_transcript_wire_valid(&t).is_ok());
    }

    // spec: repl/spec.md §17 — multi-call: one assistant tool_use turn with two
    // calls, followed by two tool_results covering exactly those ids — valid.
    #[test]
    fn multi_call_paired_is_valid() {
        let t = vec![
            Turn::User("two".to_string()),
            Turn::AssistantToolCalls(vec![tc("a"), tc("b")]),
            Turn::ToolResult(tr("a")),
            Turn::ToolResult(tr("b")),
        ];
        assert!(assert_transcript_wire_valid(&t).is_ok());
    }

    // spec: repl/spec.md §17 (+neg) — THE CURRENT 400: a tool_result whose id does
    // not match the immediately-preceding tool_use (the give-up/decline corner:
    // `…AssistantToolCalls(repair-id), ToolResult(orig-id)`). Must be rejected.
    #[test]
    fn tool_result_with_mismatched_id_is_invalid() {
        let t = vec![
            Turn::AssistantToolCalls(vec![tc("repair-3")]),
            Turn::ToolResult(tr("orig")),
        ];
        let err = assert_transcript_wire_valid(&t).unwrap_err();
        assert!(err.contains("no matching tool_use"), "got: {err}");
    }

    // spec: repl/spec.md §17 (+neg) — a tool_result with NO preceding
    // AssistantToolCalls turn at all (after a User/prose turn) — the backward
    // violation behind the give-up/decline 400.
    #[test]
    fn tool_result_after_prose_is_invalid() {
        let t = vec![Turn::Assistant("here".to_string()), Turn::ToolResult(tr("x"))];
        let err = assert_transcript_wire_valid(&t).unwrap_err();
        assert!(err.contains("no preceding"), "got: {err}");
    }

    // spec: repl/spec.md §17 (+neg) — a tool_use with NO following tool_result
    // (the unpaired-tool_use forward violation — the S89 repair-feedback corner).
    #[test]
    fn tool_use_without_following_tool_result_is_invalid() {
        let t = vec![
            Turn::AssistantToolCalls(vec![tc("toolu_1")]),
            Turn::User("next".to_string()),
        ];
        let err = assert_transcript_wire_valid(&t).unwrap_err();
        assert!(err.contains("no matching tool_result"), "got: {err}");
    }

    // spec: repl/spec.md §17 (+neg) — a tool_use at the very end of the transcript
    // (no following turn at all) — also unpaired.
    #[test]
    fn trailing_tool_use_is_invalid() {
        let t = vec![Turn::AssistantToolCalls(vec![tc("toolu_1")])];
        assert!(assert_transcript_wire_valid(&t).is_err());
    }

    // spec: repl/spec.md §17 (+neg) — a multi-call tool_use only partially covered
    // by the following tool_results (one id uncovered) is invalid.
    #[test]
    fn partially_covered_multi_call_is_invalid() {
        let t = vec![
            Turn::AssistantToolCalls(vec![tc("a"), tc("b")]),
            Turn::ToolResult(tr("a")),
            Turn::User("oops".to_string()),
        ];
        let err = assert_transcript_wire_valid(&t).unwrap_err();
        assert!(err.contains("uncovered"), "got: {err}");
    }
}
