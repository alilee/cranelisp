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
}

impl AgentState {
    /// True when no provider is reachable (the dormant / "no key" state — §6.4).
    pub fn is_dormant(&self) -> bool {
        self.model.is_none()
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
