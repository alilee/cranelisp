// agent/provider.rs — runtime provider selection + the rig membrane impl
// (design/int/agent.md §3.1, §6.3, §6.4).
//
// Builds an `AgentModel` (the object-safe internal boundary, `types.rs`) for the
// runtime-configured provider, and reports dormancy. Selection is RUNTIME config
// (env vars), not a compile choice — Anthropic (default) / Ollama (local) / stub
// (tests). NO owned LLM-protocol code: rig owns the wire. This file is the one
// place that holds a concrete rig `CompletionModel`; everything above the
// `AgentModel` boundary is rig-free.
//
// Opt-in-twice (U6, §6.4): compiled-in (the `agent` feature) AND a runtime
// provider configured *and reachable*. Absent any provider the agent is DORMANT
// (`AgentState.model == None`) and `/ask` says so, naming the endpoint + that
// source excerpts are transmitted (the U6 disclosure — §2.3).
//
// Async bridge: rig's `completion()` is async; `agent_turn` is synchronous to
// the user's Enter. The rig-backed `AgentModel::complete` `block_on`s a
// current-thread tokio runtime around one completion call (no thread spawn).

#![cfg(feature = "agent")]

use rig_core::client::CompletionClient;
use rig_core::completion::CompletionModel;

use crate::agent::request as agent_request;
use crate::agent::types::{AgentModel, AgentRequest, AgentState, ModelResponse, Turn};

/// Environment surface for provider selection (§6.4 opt-in-twice). All read at
/// session construction; none baked from memory (the model-id is config, per the
/// `claude-api` discipline).
///
/// | Var | Effect |
/// |---|---|
/// | `CRANELISP_AGENT_PROVIDER` | `anthropic` (default) / `ollama` / `stub` |
/// | `CRANELISP_AGENT_MODEL` | model-id (provider-specific; required for a live provider) |
/// | `ANTHROPIC_API_KEY` / `CRANELISP_AGENT_KEY` | Anthropic key (its presence is the reachability gate) |
/// | `OLLAMA_API_BASE_URL` | Ollama endpoint (defaults to `http://localhost:11434`) |
/// | `CRANELISP_AGENT_STUB_SCRIPT` | (test) path to a scripted-response fixture for the stub provider |
const PROVIDER_VAR: &str = "CRANELISP_AGENT_PROVIDER";
const MODEL_VAR: &str = "CRANELISP_AGENT_MODEL";

/// The completion budget for every agent request (rig `CompletionRequest.max_tokens`).
/// Anthropic's Messages API makes `max_tokens` MANDATORY — a request that omits it is
/// rejected outright (`RequestError: max_tokens must be set for Anthropic`), which
/// broke every turn against the default provider (FIXME 0554). `build_request` is the
/// single shared assembly for `complete` and `complete_streaming` (Principle 7), so
/// setting it here repairs both transports at once. Sized for the STREAMING case — the
/// agent loop drives `stream` (S107): a low cap truncates a tool-call turn mid-thought,
/// so 64K is the sane streaming default (a per-model/configurable budget would thread a
/// field through `AgentRequest`; the constant is the minimal correct fix).
const AGENT_MAX_TOKENS: u64 = 65536;

/// Build the agent state for this session (§3.4). `enabled` is the resolved
/// `--agent` runtime toggle (§6.4 opt-in-twice — the FIRST opt-in is the `agent`
/// feature, the SECOND is this flag + a reachable provider). When `enabled` is
/// false, or no provider is reachable, the returned state is DORMANT (model
/// `None`) and `/ask`/the classifier route renders the dormant notice.
pub fn build_agent_state(enabled: bool) -> AgentState {
    build_agent_state_with(enabled, false)
}

/// Build the agent state, threading the resolved `--yes` autonomous-submit
/// toggle (§20.1) onto `AgentState.auto_accept`. `auto_accept` is meaningful
/// only with an active agent (it is already `&& agent_enabled` at the `main.rs`
/// seam, §20.1); a dormant / disabled agent carries it inertly. This is the
/// single construction site — every returned `AgentState` flows its
/// `auto_accept` from here (`new_state` seeds the two §20 bits).
pub fn build_agent_state_with(enabled: bool, auto_accept: bool) -> AgentState {
    if !enabled {
        return new_state(None, "disabled (--agent not set)", auto_accept);
    }

    let provider = std::env::var(PROVIDER_VAR).unwrap_or_else(|_| "anthropic".to_string());
    let state = match provider.as_str() {
        "stub" => build_stub_state(),
        "ollama" => build_ollama_state(),
        _ => build_anthropic_state(),
    };
    AgentState { auto_accept, ..state }
}

/// Construct an `AgentState`, seeding the §20 autonomy bits (`auto_accept` +
/// the once-only `auto_accept_notice_shown`, which always starts `false`). The
/// single literal site so the field set cannot drift across providers.
fn new_state(model: Option<Box<dyn AgentModel>>, label: &str, auto_accept: bool) -> AgentState {
    AgentState {
        transcript: Vec::new(),
        model,
        provider_label: label.to_string(),
        auto_accept,
        auto_accept_notice_shown: false,
        submit_gave_up: false,
        submit_committed: false,
        current_turn: 0,
        turn_ring: std::collections::VecDeque::new(),
    }
}

/// Anthropic (the default provider, §6.3). Reachable iff a key is present; the
/// model-id comes from runtime config (never hardcoded from memory).
fn build_anthropic_state() -> AgentState {
    let key = std::env::var("ANTHROPIC_API_KEY")
        .ok()
        .or_else(|| std::env::var("CRANELISP_AGENT_KEY").ok());
    let model_id = std::env::var(MODEL_VAR).ok();
    match (key, model_id) {
        (Some(key), Some(model_id)) if !key.is_empty() && !model_id.is_empty() => {
            match rig_core::providers::anthropic::Client::new(&key) {
                Ok(client) => {
                    let model = client.completion_model(model_id);
                    match RigModel::new(model) {
                        Ok(rig) => new_state(Some(Box::new(rig)), "anthropic", false),
                        Err(_) => dormant("anthropic (async runtime construction failed)"),
                    }
                }
                Err(_) => dormant("anthropic (client construction failed)"),
            }
        }
        _ => dormant(
            "anthropic (no API key or model-id; set ANTHROPIC_API_KEY + CRANELISP_AGENT_MODEL)",
        ),
    }
}

/// Ollama — the local / offline escape hatch (§6.3, the U6 privacy path). No key;
/// the endpoint defaults to localhost. Requires a configured model-id.
fn build_ollama_state() -> AgentState {
    let model_id = std::env::var(MODEL_VAR).ok();
    match model_id {
        Some(model_id) if !model_id.is_empty() => {
            match rig_core::providers::ollama::Client::new(rig_core::client::Nothing) {
                Ok(client) => {
                    let model = client.completion_model(model_id);
                    match RigModel::new(model) {
                        Ok(rig) => new_state(Some(Box::new(rig)), "ollama (local)", false),
                        Err(_) => dormant("ollama (async runtime construction failed)"),
                    }
                }
                Err(_) => dormant("ollama (client construction failed)"),
            }
        }
        _ => dormant("ollama (no model-id; set CRANELISP_AGENT_MODEL)"),
    }
}

/// The deterministic test stub provider, selected by `CRANELISP_AGENT_PROVIDER=stub`
/// (the §1.1(a) stub-provider-by-config mechanism — makes Lane A genuine e2e).
/// Loads a scripted-response fixture from `CRANELISP_AGENT_STUB_SCRIPT`.
fn build_stub_state() -> AgentState {
    match crate::agent::stub::StubModel::from_env() {
        Ok(stub) => new_state(Some(Box::new(stub)), "stub (test)", false),
        Err(reason) => dormant(&format!("stub ({reason})")),
    }
}

fn dormant(label: &str) -> AgentState {
    new_state(None, label, false)
}

/// The rig-backed `AgentModel` impl — the membrane's other half (§6.1). Holds a
/// concrete rig `CompletionModel` and a current-thread tokio runtime to bridge
/// rig's async `completion()` into the synchronous `AgentModel::complete`.
struct RigModel<M: CompletionModel> {
    model: M,
    runtime: tokio::runtime::Runtime,
}

impl<M: CompletionModel> RigModel<M> {
    /// Build the rig-backed model. Returns `Err` when the current-thread tokio
    /// runtime cannot be constructed — the provider-selection caller maps that to
    /// a DORMANT agent (no panic in pipeline code, per `src/CLAUDE.md` §Error
    /// Handling; the U6 dormancy fallback is the right degradation).
    fn new(model: M) -> Result<Self, std::io::Error> {
        // current-thread runtime: one blocking completion call per loop step, no
        // multi-thread executor needed (§6.4 — `rt` + `macros` features only).
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()?;
        Ok(Self { model, runtime })
    }
}

impl<M: CompletionModel> RigModel<M> {
    /// Build the rig `CompletionRequest` from the neutral `AgentRequest` via the
    /// membrane (`request.rs`) + the model's own builder — the SAME assembly for
    /// `complete` and `complete_streaming` (Principle 7, single source of truth).
    fn build_request(&self, request: &AgentRequest) -> rig_core::completion::CompletionRequest {
        let preamble = agent_request::preamble(request);
        let history = agent_request::history_messages(request);
        let prompt = agent_request::prompt_message(request);
        let tools = agent_request::tool_definitions(request);
        self.model
            .completion_request(prompt)
            .preamble(preamble)
            .messages(history)
            .tools(tools)
            // Anthropic REQUIRES max_tokens; omitting it 400s before a token streams
            // (FIXME 0554). Set on the shared builder so both transports carry it.
            .max_tokens(AGENT_MAX_TOKENS)
            .build()
    }
}

impl<M: CompletionModel> AgentModel for RigModel<M> {
    fn complete(&mut self, request: &AgentRequest) -> Result<ModelResponse, String> {
        // Trace mode (`CRANELISP_AGENT_TRACE=<path>`, §28.1): APPEND the assembled
        // message sequence (full content) to the trace file at the rig boundary so
        // wire-path bugs (the tool_use↔tool_result pairing 400 class) are directly
        // visible rather than inferred from a live 400. Off (no file) unless the
        // env path is set. The trace fires ONLY on this rig path, not the stub
        // (§28.2(2) — the persisted trace is a live-provider wire record). The
        // request's own `turn` id stamps the persisted block (the log↔trace join).
        crate::agent::trace::emit_request(request);

        let rig_req = self.build_request(request);

        let resp = self
            .runtime
            .block_on(self.model.completion(rig_req))
            .map_err(|e| format!("completion failed: {e}"))?;

        let lowered = agent_request::lower_response(resp.choice);
        // The response belongs to the request's turn — stamp the same `turn` id.
        crate::agent::trace::emit_response(&lowered, request.turn);
        Ok(lowered)
    }

    fn complete_streaming(
        &mut self,
        request: &AgentRequest,
        sink: &mut dyn FnMut(&str),
    ) -> Result<ModelResponse, String> {
        // Same trace + request assembly as `complete` (§14A.3 S2) — only the
        // transport differs: drive `stream` in ONE `block_on` and forward TEXT
        // deltas to `sink`, then lower the stream's aggregated `choice` with the
        // SAME `lower_response`. Trace/log fire on the accumulated final response
        // (the §17.21 record is byte-for-byte what `complete` produces, §14A.3 S4).
        crate::agent::trace::emit_request(request);

        let rig_req = self.build_request(request);
        // Bind a local reference so the async block borrows `self.model` only
        // (never `self` wholesale), keeping it disjoint from `self.runtime`.
        let model = &self.model;
        let choice = self.runtime.block_on(async move {
            use futures::StreamExt;
            use rig_core::streaming::StreamedAssistantContent;
            let mut stream = model
                .stream(rig_req)
                .await
                .map_err(|e| format!("stream failed: {e}"))?;
            while let Some(item) = stream.next().await {
                // Only TEXT deltas stream live. Tool-call / reasoning items are
                // accumulated into `stream.choice` (which `lower_response` turns
                // into `ToolCalls`/`Done`), so a tool-call turn streams NO prose
                // (§17.22 constraint) yet still returns the right `ModelResponse`.
                if let StreamedAssistantContent::Text(t) =
                    item.map_err(|e| format!("stream error: {e}"))?
                {
                    sink(&t.text);
                }
            }
            // The aggregated assistant content is set when the inner stream ends.
            Ok::<_, String>(stream.choice.clone())
        })?;

        let lowered = agent_request::lower_response(choice);
        crate::agent::trace::emit_response(&lowered, request.turn);
        Ok(lowered)
    }
}

impl AgentState {
    /// Push the user turn onto the transcript (§3.4).
    pub fn record_user(&mut self, text: &str) {
        self.transcript.push(Turn::User(text.to_string()));
    }
    /// Push an assistant prose turn onto the transcript.
    pub fn record_assistant(&mut self, text: &str) {
        self.transcript.push(Turn::Assistant(text.to_string()));
    }
    /// Push the assistant tool-call turn (the `tool_use` blocks the model just
    /// emitted) onto the transcript, BEFORE the matching tool results. This is
    /// the assistant turn the Anthropic API requires to precede each
    /// `tool_result` (matched by call id) — without it the continuation request
    /// 400s with "unexpected `tool_use_id` … must have a corresponding
    /// `tool_use` block in the previous message" (§4.1).
    pub fn record_assistant_tool_calls(
        &mut self,
        calls: Vec<crate::agent::types::ToolCallRequest>,
    ) {
        self.transcript.push(Turn::AssistantToolCalls(calls));
    }
    /// Push a tool-result turn (a pulled command + its output) onto the transcript.
    pub fn record_tool_result(&mut self, result: crate::agent::types::ToolCallResult) {
        self.transcript.push(Turn::ToolResult(result));
    }

    /// Record a pull/submit outcome onto the transcript, KEEPING the transcript
    /// wire-valid in BOTH directions (the Phase-6 give-up/decline 400 fix).
    ///
    /// The Anthropic API rule: a `tool_result` block is legal ONLY immediately
    /// after an assistant message carrying the matching `tool_use`. The repair
    /// loop (`pull.rs::validate_and_repair`) may have ALREADY paired the outer
    /// `submit` tool_use (its iter-1 error feedback is a `tool_result` against
    /// `call.id`) and then either left a TRAILING UNPAIRED repair tool_use
    /// (cap-exhausted give-up) or fully paired everything (prose/model-None
    /// give-up). The outer loop records exactly one result per submit — so blindly
    /// pushing a `ToolResult` either correctly closes the trailing unpaired
    /// tool_use OR adds a SPURIOUS second tool_result (the current 400).
    ///
    /// This method makes the choice structurally: it pushes a `ToolResult` ONLY
    /// when the GOVERNING `AssistantToolCalls` turn (the one that opened the
    /// batch these results are closing) promises the result's id AND no prior
    /// `ToolResult` in the batch has already covered it. Otherwise the outer
    /// submit is already paired, so the outcome is recorded as a benign `User`
    /// turn (the model still sees the give-up/decline prose, the pairing stays
    /// valid). The same rule serves clean-submit, 1-repair, cap-exhausted
    /// give-up, declined, and `--yes` uniformly.
    ///
    /// **Multi-call batches (FIXME 0541).** When one assistant turn issues N tool
    /// calls, `agent_turn` records the `AssistantToolCalls(batch)` turn ONCE, then
    /// loops this method once per call. After the first call's `ToolResult` is
    /// pushed, `transcript.last()` is that `ToolResult` — not the governing
    /// `AssistantToolCalls` — so a `.last()`-only check silently demoted calls
    /// 2..N to `User` turns, leaving their `tool_use` ids uncovered and tripping
    /// `assert_transcript_wire_valid` (a hard panic in a debug build). The fix
    /// walks back past the contiguous trailing run of already-recorded
    /// `ToolResult`s (the earlier calls of THIS same batch) to find the governing
    /// `AssistantToolCalls`, and skips an id a prior `ToolResult` already covered.
    pub fn record_pull_result(&mut self, result: crate::agent::types::ToolCallResult) {
        // Walk back over the contiguous run of trailing `ToolResult`s (calls
        // 1..k of this batch, already recorded) to reach the governing
        // `AssistantToolCalls` turn. Note if a prior result already covered this
        // id (idempotence guard). NOTE: correlation is by raw id; in every live
        // flow the id is non-empty (`toolu_…` / `stub-N`), so the empty-id case
        // (two empty-id results in one batch "colliding") is not reachable — the
        // wire membrane's command-fallback only ever applies to the never-live
        // empty-id path (see `types.rs::tool_result_key`).
        let mut i = self.transcript.len();
        let mut already_covered = false;
        while let Some(Turn::ToolResult(r)) =
            i.checked_sub(1).and_then(|k| self.transcript.get(k))
        {
            if r.id == result.id {
                already_covered = true;
            }
            i -= 1;
        }
        let closes_batch_tool_use = !already_covered
            && matches!(
                i.checked_sub(1).and_then(|k| self.transcript.get(k)),
                Some(Turn::AssistantToolCalls(calls)) if calls.iter().any(|c| c.id == result.id)
            );
        if closes_batch_tool_use {
            self.transcript.push(Turn::ToolResult(result));
        } else {
            // No governing tool_use for this id (or already covered) — recording a
            // tool_result would be the unpaired-tool_result 400. Carry the outcome
            // as a user turn instead (still visible to the model next turn).
            self.transcript.push(Turn::User(result.output));
        }
    }
}

#[cfg(test)]
mod tests {
    //! Rig-trait-level loop test (FIXME 0429 — pulled forward). This drives the
    //! REAL rig-request construction path (`RigModel` + `request.rs`) below the
    //! `AgentModel` membrane, against a mock that implements the genuine
    //! `rig_core::completion::CompletionModel` trait. It captures every
    //! `CompletionRequest` the model receives and asserts the continuation
    //! request (turn 2) is well-formed per the Anthropic pairing invariant — the
    //! coverage gap the stub (which sits ABOVE rig) cannot close.

    use super::*;
    use rig_core::completion::message::{AssistantContent, Message, ToolFunction, UserContent};
    use rig_core::completion::{
        CompletionError, CompletionModel, CompletionRequest, CompletionResponse, GetTokenUsage,
        Usage,
    };
    use rig_core::message::ToolCall;
    use rig_core::streaming::StreamingCompletionResponse;
    use rig_core::OneOrMany;
    use std::sync::{Arc, Mutex};

    /// Minimal raw-response type for the mock (the `Response`/`StreamingResponse`
    /// associated types). Carries nothing — the loop only reads `choice`.
    #[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
    struct MockRaw;

    impl GetTokenUsage for MockRaw {
        fn token_usage(&self) -> Usage {
            Usage::new()
        }
    }

    /// A mock `CompletionModel` (the real rig trait, below the membrane) that
    /// records every `CompletionRequest` it receives and replays a scripted set
    /// of assistant-content responses, one per `completion()` call.
    #[derive(Clone)]
    struct MockModel {
        script: Arc<Vec<Vec<AssistantContent>>>,
        cursor: Arc<Mutex<usize>>,
        requests: Arc<Mutex<Vec<CompletionRequest>>>,
    }

    impl MockModel {
        fn new(script: Vec<Vec<AssistantContent>>) -> Self {
            Self {
                script: Arc::new(script),
                cursor: Arc::new(Mutex::new(0)),
                requests: Arc::new(Mutex::new(Vec::new())),
            }
        }
    }

    impl CompletionModel for MockModel {
        type Response = MockRaw;
        type StreamingResponse = MockRaw;
        type Client = ();

        fn make(_: &Self::Client, _: impl Into<String>) -> Self {
            MockModel::new(Vec::new())
        }

        async fn completion(
            &self,
            request: CompletionRequest,
        ) -> Result<CompletionResponse<Self::Response>, CompletionError> {
            self.requests.lock().unwrap().push(request);
            let idx = {
                let mut c = self.cursor.lock().unwrap();
                let i = *c;
                *c += 1;
                i
            };
            let content = self
                .script
                .get(idx)
                .cloned()
                .unwrap_or_else(|| vec![AssistantContent::text(String::new())]);
            Ok(CompletionResponse {
                choice: OneOrMany::many(content).unwrap(),
                usage: Usage::new(),
                raw_response: MockRaw,
                message_id: None,
            })
        }

        async fn stream(
            &self,
            request: CompletionRequest,
        ) -> Result<StreamingCompletionResponse<Self::StreamingResponse>, CompletionError> {
            use rig_core::streaming::{RawStreamingChoice, RawStreamingToolCall, StreamingResult};
            // Mirror `completion`: record the request + advance the script cursor,
            // so the streaming loop test exercises the SAME capture/replay — the
            // agent loop now drives `stream` (S107), not `completion`.
            self.requests.lock().unwrap().push(request);
            let idx = {
                let mut c = self.cursor.lock().unwrap();
                let i = *c;
                *c += 1;
                i
            };
            let content = self
                .script
                .get(idx)
                .cloned()
                .unwrap_or_else(|| vec![AssistantContent::text(String::new())]);
            // Lower each scripted assistant-content item to a raw streaming choice
            // so the aggregated `stream.choice` matches what `completion` returns
            // (text → Message delta; tool call → ToolCall), then a FinalResponse
            // terminator so `stream.choice` is populated at stream-end.
            let mut raws: Vec<Result<RawStreamingChoice<MockRaw>, CompletionError>> = Vec::new();
            for c in content {
                match c {
                    AssistantContent::Text(t) => raws.push(Ok(RawStreamingChoice::Message(t.text))),
                    AssistantContent::ToolCall(tc) => {
                        raws.push(Ok(RawStreamingChoice::ToolCall(RawStreamingToolCall::new(
                            tc.id.clone(),
                            tc.function.name.clone(),
                            tc.function.arguments.clone(),
                        ))))
                    }
                    _ => {}
                }
            }
            raws.push(Ok(RawStreamingChoice::FinalResponse(MockRaw)));
            let inner: StreamingResult<MockRaw> = Box::pin(futures::stream::iter(raws));
            Ok(StreamingCompletionResponse::stream(inner))
        }
    }

    /// The assistant tool_use ids of a `Message`, in order.
    fn assistant_tool_use_ids(msg: &Message) -> Vec<String> {
        match msg {
            Message::Assistant { content, .. } => content
                .iter()
                .filter_map(|c| match c {
                    AssistantContent::ToolCall(tc) => Some(tc.id.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    /// The user tool_result ids of a `Message`, in order.
    fn user_tool_result_ids(msg: &Message) -> Vec<String> {
        match msg {
            Message::User { content } => content
                .iter()
                .filter_map(|c| match c {
                    UserContent::ToolResult(r) => Some(r.id.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    // spec: repl/spec.md §17 — drive the FULL model↔tool loop through the real
    // rig boundary: turn 1 returns a tool-call for `/source f`; turn 2 returns
    // Done text. Assert the CONTINUATION request (turn 2) the mock received is
    // well-formed per Anthropic's pairing invariant: each `tool_result` block is
    // preceded by an assistant `tool_use` block carrying the SAME id. Before the
    // fix this request 400'd ("unexpected tool_use_id … no corresponding
    // tool_use block"). Closes FIXME 0429's wire-path coverage gap.
    /// The tool_result content text of a user `Message`, concatenated, in order.
    fn user_tool_result_text(msg: &Message) -> String {
        use rig_core::completion::message::ToolResultContent;
        match msg {
            Message::User { content } => content
                .iter()
                .filter_map(|c| match c {
                    UserContent::ToolResult(r) => Some(
                        r.content
                            .iter()
                            .filter_map(|tc| match tc {
                                ToolResultContent::Text(t) => Some(t.text.clone()),
                                _ => None,
                            })
                            .collect::<Vec<_>>()
                            .join(""),
                    ),
                    _ => None,
                })
                .collect::<Vec<_>>()
                .join(""),
            _ => String::new(),
        }
    }

    #[test]
    fn continuation_request_pairs_tool_use_before_tool_result() {
        // Turn 1: the model asks to pull `/source f` (a read-only allowlist cmd).
        let turn1 = vec![AssistantContent::ToolCall(ToolCall::new(
            "toolu_42".to_string(),
            ToolFunction::new("source".to_string(), serde_json::json!({"argument": "f"})),
        ))];
        // Turn 2: the model answers.
        let turn2 = vec![AssistantContent::text("f is the identity")];
        let mock = MockModel::new(vec![turn1, turn2]);
        let captured = mock.requests.clone();

        let rig = RigModel::new(mock).expect("tokio current-thread runtime builds");

        // Wire the rig-backed model as the boxed AgentModel and drive a turn.
        // Define `f` with introspection source so the REAL `/source f` pull
        // (through process_commands) yields the source text fed back to the
        // model — this is what lets us assert the tool_result CONTENT, not just
        // its id pairing.
        let mut s = crate::agent::test_support::repl_session();
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
        s.agent = Some(AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(rig)),
            provider_label: "mock (test)".to_string(),
            auto_accept: false,
            auto_accept_notice_shown: false,
            submit_gave_up: false,
            submit_committed: false,
            current_turn: 0,
            turn_ring: std::collections::VecDeque::new(),
        });
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = crate::agent::types::NoConsent;
        s.agent_turn("show me the source of f", &mut sink, &mut consent);

        let reqs = captured.lock().unwrap();
        assert_eq!(reqs.len(), 2, "a tool-call turn drives two completion calls");

        // The CONTINUATION request (turn 2) carries the full history including the
        // assistant tool_use turn + the matching tool_result. Walk its
        // chat_history and assert every tool_result is preceded by a matching
        // tool_use (the exact invariant the Anthropic 400 enforced).
        let history: Vec<Message> = reqs[1].chat_history.clone().into_iter().collect();
        let mut last_use_ids: Vec<String> = Vec::new();
        let mut saw_tool_use = false;
        let mut saw_tool_result = false;
        for msg in &history {
            let uses = assistant_tool_use_ids(msg);
            if !uses.is_empty() {
                last_use_ids = uses;
                saw_tool_use = true;
            }
            for rid in user_tool_result_ids(msg) {
                saw_tool_result = true;
                assert!(
                    last_use_ids.contains(&rid),
                    "tool_result id {rid} has no preceding matching tool_use in the \
                     continuation request; preceding tool_use ids were {last_use_ids:?}"
                );
            }
        }
        assert!(saw_tool_use, "the continuation request must carry an assistant tool_use block");
        assert!(saw_tool_result, "the continuation request must carry the tool_result block");
        assert!(
            last_use_ids.contains(&"toolu_42".to_string()),
            "the tool_use id from turn 1 (toolu_42) must appear in the continuation history"
        );

        // S88 pull-loop fix — CONTENT assertion (this is what would have caught
        // the loop). The continuation request's tool_result must carry the actual
        // pulled command output (the source text), NON-EMPTY. The model loops
        // precisely when this content is empty.
        let tool_result_text: String = history.iter().map(user_tool_result_text).collect();
        assert!(
            !tool_result_text.is_empty(),
            "the continuation tool_result content must NOT be empty"
        );
        assert!(
            tool_result_text.contains("(defn f [x] x)"),
            "the continuation tool_result must carry the command output (the source), got: {tool_result_text:?}"
        );

        // The FINAL message of the continuation request is the tool_result
        // (the prompt), NOT a re-asked copy of the original question — the
        // duplicate-prompt-after-tool_result shape was the loop's root cause.
        let last = history.last().expect("a final message in the continuation request");
        assert!(
            !user_tool_result_ids(last).is_empty(),
            "the final continuation message must be the tool_result, not a re-asked question"
        );
        let restated = matches!(
            last,
            Message::User { content }
                if content.iter().any(|c| matches!(
                    c, UserContent::Text(t) if t.text.contains("show me the source")))
        );
        assert!(!restated, "the original question must not be re-appended after the tool_result");
    }

    // spec: repl/spec.md §17 — Phase-6 Build-mode repair-loop pairing. Drive a
    // BROKEN-then-FIXED `submit` through the validator-repair loop against the
    // REAL rig boundary: turn 1 = a `submit` tool_use carrying a BROKEN form
    // (fails the validator); turn 2 (the REPAIR completion) = a `submit` tool_use
    // carrying the FIXED form; turn 3 = Done. The REPAIR request (turn 2) is the
    // one the live agent sent malformed — the outer loop recorded the broken
    // submit as an assistant `tool_use`, and the inner repair loop assembled its
    // request mid-handling. Pre-fix it recorded the compiler-error feedback as a
    // bare USER turn, so the repair request ended `…tool_use(submit), user(feedback)`
    // — an unpaired tool_use → live Anthropic 400. This asserts the repair request
    // is well-formed: every `tool_result` block is immediately preceded by an
    // assistant `tool_use` block carrying the SAME id (the exact invariant the 400
    // enforced). The stub (which sits ABOVE rig) cannot catch this — only the real
    // `CompletionModel` request construction surfaces the pairing.
    #[test]
    fn repair_loop_request_pairs_submit_tool_use_before_error_tool_result() {
        use rig_core::completion::message::ToolResultContent;

        // Turn 1: the model submits a BROKEN form (missing close paren → parse err).
        let turn1 = vec![AssistantContent::ToolCall(ToolCall::new(
            "toolu_broken".to_string(),
            ToolFunction::new(
                "submit".to_string(),
                serde_json::json!({"argument": "(defn dbl [x] x"}),
            ),
        ))];
        // Turn 2: the REPAIR completion — a fresh `submit` tool_use with the FIXED
        // form (a bare identity, no unresolved primitive, so it validates clean).
        let turn2 = vec![AssistantContent::ToolCall(ToolCall::new(
            "toolu_fixed".to_string(),
            ToolFunction::new(
                "submit".to_string(),
                serde_json::json!({"argument": "(defn dbl [x] x)"}),
            ),
        ))];
        // Turn 3: the model answers.
        let turn3 = vec![AssistantContent::text("defined dbl")];
        let mock = MockModel::new(vec![turn1, turn2, turn3]);
        let captured = mock.requests.clone();

        let rig = RigModel::new(mock).expect("tokio current-thread runtime builds");

        let mut s = crate::agent::test_support::repl_session();
        s.agent = Some(AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(rig)),
            provider_label: "mock (test)".to_string(),
            // --yes so the confirm gate auto-accepts without a line-read; the
            // pairing defect is in the validator-repair loop, which runs BEFORE
            // (and independently of) the consent gate (§20.3).
            auto_accept: true,
            auto_accept_notice_shown: false,
            submit_gave_up: false,
            submit_committed: false,
            current_turn: 0,
            turn_ring: std::collections::VecDeque::new(),
        });
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = crate::agent::types::NoConsent;
        s.agent_turn("write me a dbl fn in this module", &mut sink, &mut consent);

        let reqs = captured.lock().unwrap();
        // Turn 1 (initial submit) + turn 2 (the repair completion) + turn 3 (the
        // post-submit continuation Done) — three completion calls.
        assert!(
            reqs.len() >= 2,
            "the broken-then-fixed repair drives at least the initial + repair calls, got {}",
            reqs.len()
        );

        // The REPAIR request (turn 2 = index 1) is the one that 400'd live. Walk
        // its chat_history and assert every tool_result is preceded by a matching
        // tool_use (the exact invariant the Anthropic 400 enforced).
        let history: Vec<Message> = reqs[1].chat_history.clone().into_iter().collect();
        let mut last_use_ids: Vec<String> = Vec::new();
        let mut saw_tool_use = false;
        let mut saw_tool_result = false;
        for msg in &history {
            let uses = assistant_tool_use_ids(msg);
            if !uses.is_empty() {
                last_use_ids = uses;
                saw_tool_use = true;
            }
            for rid in user_tool_result_ids(msg) {
                saw_tool_result = true;
                assert!(
                    last_use_ids.contains(&rid),
                    "tool_result id {rid} has no preceding matching tool_use in the \
                     REPAIR request; preceding tool_use ids were {last_use_ids:?} \
                     (this is the Phase-6 Anthropic 400 — unpaired tool_use)"
                );
            }
        }
        assert!(
            saw_tool_use,
            "the repair request must carry the (broken) submit's assistant tool_use block"
        );
        assert!(
            saw_tool_result,
            "the repair request must carry the compiler-error tool_result block \
             (paired, NOT a bare user turn)"
        );
        assert!(
            last_use_ids.contains(&"toolu_broken".to_string()),
            "the broken submit's tool_use id (toolu_broken) must appear in the repair history"
        );

        // The error feedback must be carried as the tool_result content (paired),
        // and it must be the FINAL message (the prompt the model answers) — not a
        // bare trailing user turn.
        let last = history.last().expect("a final message in the repair request");
        assert!(
            !user_tool_result_ids(last).is_empty(),
            "the final repair message must be the error tool_result (paired), not a bare user turn"
        );
        let last_text: String = match last {
            Message::User { content } => content
                .iter()
                .filter_map(|c| match c {
                    UserContent::ToolResult(r) => Some(
                        r.content
                            .iter()
                            .filter_map(|tc| match tc {
                                ToolResultContent::Text(t) => Some(t.text.clone()),
                                _ => None,
                            })
                            .collect::<Vec<_>>()
                            .join(""),
                    ),
                    _ => None,
                })
                .collect::<Vec<_>>()
                .join(""),
            _ => String::new(),
        };
        assert!(
            last_text.contains("does not compile"),
            "the paired tool_result must carry the compiler-error feedback, got: {last_text:?}"
        );

        // RESIDUAL-CORNER guard: the POST-SUBMIT continuation request (turn 3 =
        // index 2) must ALSO be well-formed. After the repair, the LAST recorded
        // tool_use is the REPAIR submit (toolu_fixed); the outer loop's success
        // tool_result must pair against THAT id, not the original toolu_broken —
        // else this request ends `…tool_use(toolu_fixed), tool_result(toolu_broken)`
        // and 400s. Walk its history and assert every tool_result is preceded by a
        // matching tool_use.
        assert!(
            reqs.len() >= 3,
            "the successful submit drives a post-submit continuation call, got {}",
            reqs.len()
        );
        let cont: Vec<Message> = reqs[2].chat_history.clone().into_iter().collect();
        let mut cont_use_ids: Vec<String> = Vec::new();
        for msg in &cont {
            let uses = assistant_tool_use_ids(msg);
            if !uses.is_empty() {
                cont_use_ids = uses;
            }
            for rid in user_tool_result_ids(msg) {
                assert!(
                    cont_use_ids.contains(&rid),
                    "POST-SUBMIT continuation: tool_result id {rid} has no preceding \
                     matching tool_use (residual Phase-6 corner); preceding tool_use \
                     ids were {cont_use_ids:?}"
                );
            }
        }
        // Specifically: the FINAL success tool_result must carry the REPAIR
        // tool_use id (toolu_fixed), and the history must contain the repair
        // tool_use — proving the outer result paired against the actual submit.
        let cont_last = cont.last().expect("a final message in the post-submit request");
        assert_eq!(
            user_tool_result_ids(cont_last),
            vec!["toolu_fixed".to_string()],
            "the success tool_result must pair against the REPAIR submit's id (toolu_fixed)"
        );

        // End-to-end: the FIXED form was submitted (the repair succeeded and the
        // clean form committed under --yes).
        assert!(
            s.lookup_with_prelude_fallback("dbl").is_some(),
            "the repaired clean form must commit the definition"
        );
    }

    /// Walk a captured `CompletionRequest`'s chat_history and assert the
    /// Anthropic tool_use↔tool_result pairing invariant holds in BOTH directions:
    ///   - every `tool_result` is preceded by an assistant `tool_use` carrying
    ///     the SAME id (the `messages.N: unexpected tool_use_id …` 400);
    ///   - every assistant `tool_use` whose id is later closed by a `tool_result`
    ///     pairs against the most recent preceding tool_use run.
    ///
    /// `label` names the request (which completion call) so a failure points at
    /// the exact offender. Returns whether the request carried ANY tool blocks.
    fn assert_request_wire_paired(req: &CompletionRequest, label: &str) -> (bool, bool) {
        let history: Vec<Message> = req.chat_history.clone().into_iter().collect();
        let mut last_use_ids: Vec<String> = Vec::new();
        let mut saw_tool_use = false;
        let mut saw_tool_result = false;
        for msg in &history {
            let uses = assistant_tool_use_ids(msg);
            if !uses.is_empty() {
                last_use_ids = uses;
                saw_tool_use = true;
            }
            for rid in user_tool_result_ids(msg) {
                saw_tool_result = true;
                assert!(
                    last_use_ids.contains(&rid),
                    "{label}: tool_result id {rid} has no preceding matching tool_use \
                     (the messages.N unexpected_tool_use_id 400); preceding tool_use \
                     ids were {last_use_ids:?}"
                );
            }
        }
        (saw_tool_use, saw_tool_result)
    }

    // spec: repl/spec.md §17 — Phase-6 CAP-EXHAUSTED GIVE-UP pairing. This is the
    // EXACT live 400 that triggered the Phase-6 work: the repair loop exhausts its
    // cap (3 consecutive broken `submit`s → "I couldn't produce a definition that
    // compiles cleanly…") and the give-up `tool_result` the OUTER loop records
    // must close the LAST (trailing-unpaired) repair tool_use — NOT the original
    // submit, and NOT be a spurious second tool_result. Get it wrong and the NEXT
    // request 400s `messages.4…: unexpected tool_use_id … each tool_result must
    // have a corresponding tool_use in the previous message`.
    //
    // Drive THREE consecutive broken `submit`s through the REAL rig boundary
    // (turn 1 = outer broken submit; turns 2,3,4 = the repair completions, each a
    // fresh broken submit → cap exhausted → give-up). Walk EVERY captured
    // `CompletionRequest` and assert each is wire-valid in BOTH directions — i.e.
    // it would have caught the live `messages.4` 400. The stub (above rig) cannot
    // catch this; only the real `CompletionModel` request construction surfaces it.
    #[test]
    fn cap_exhausted_give_up_keeps_every_request_wire_paired() {
        // A broken `submit` (missing close paren → parse Err → always re-prompts).
        let broken = |id: &str| {
            vec![AssistantContent::ToolCall(ToolCall::new(
                id.to_string(),
                ToolFunction::new(
                    "submit".to_string(),
                    serde_json::json!({"argument": "(defn never [x] x"}),
                ),
            ))]
        };
        // Turn 1 = the outer submit; turns 2..4 = the three repair completions the
        // loop requests (MAX_REPAIR_ITERATIONS = 3). All broken ⇒ cap exhausted ⇒
        // give-up. A trailing scripted Done is harmless (the give-up returns first).
        let mock = MockModel::new(vec![
            broken("toolu_b0"),
            broken("toolu_b1"),
            broken("toolu_b2"),
            broken("toolu_b3"),
            vec![AssistantContent::text("ok")],
        ]);
        let captured = mock.requests.clone();
        let rig = RigModel::new(mock).expect("tokio current-thread runtime builds");

        let mut s = crate::agent::test_support::repl_session();
        s.agent = Some(AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(rig)),
            provider_label: "mock (test)".to_string(),
            // --yes so the (never-reached) confirm gate would auto-accept; the
            // give-up happens in the validator-repair loop, BEFORE any gate.
            auto_accept: true,
            auto_accept_notice_shown: false,
            submit_gave_up: false,
            submit_committed: false,
            current_turn: 0,
            turn_ring: std::collections::VecDeque::new(),
        });
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = crate::agent::types::NoConsent;
        s.agent_turn("write me a never fn in this module", &mut sink, &mut consent);

        // Phase-6 (S89) give-up semantics: the per-submit cap exhaustion feeds the
        // MODEL an honest abort (so it can adapt), but the USER-facing
        // "couldn't produce a definition" line is decided ONLY at TRUE turn-end and
        // ONLY when the turn produced nothing. Here the loop continues after the
        // give-up and reaches the scripted `Done("ok")` answer — so the turn DID
        // produce an answer, and the give-up line must NOT appear (it would be
        // false). The agent still never submitted broken code (verified below).
        let rendered = String::from_utf8_lossy(&sink);
        assert!(
            !rendered.contains("couldn't produce a definition"),
            "a turn that ends on a Done answer must NOT show the give-up line, \
             stdout={rendered}"
        );

        // EVERY captured request must be wire-paired in BOTH directions — the
        // central assertion. The give-up's trailing request (and any post-give-up
        // turn the outer loop assembles) is exactly where the live `messages.4`
        // 400 lived: a trailing repair tool_use closed by a mis-id'd or spurious
        // tool_result. The repair loop drives ≥4 completion calls.
        let reqs = captured.lock().unwrap();
        assert!(
            reqs.len() >= 4,
            "three broken submits drive the outer + three repair completions, got {}",
            reqs.len()
        );
        let mut any_paired = false;
        for (i, req) in reqs.iter().enumerate() {
            let (saw_use, saw_result) = assert_request_wire_paired(req, &format!("request[{i}]"));
            any_paired |= saw_use && saw_result;
        }
        // The give-up path DID exercise the tool_use↔tool_result pairing (it is
        // not vacuously green on a transcript that never carried tool blocks).
        assert!(
            any_paired,
            "at least one request must carry a paired tool_use+tool_result \
             (the give-up path must actually exercise pairing, not pass vacuously)"
        );

        // The broken form was NEVER submitted — `never` stays unbound (give-up).
        assert!(
            s.lookup_with_prelude_fallback("never").is_none(),
            "the cap-exhausted give-up must commit NOTHING"
        );
    }

    // -----------------------------------------------------------------------
    // S90 §28 — the PERSISTENT TRACE sink, driven through the REAL rig boundary
    // (`RigModel::complete` → `emit_request`/`emit_response`). These are the
    // /dev-owned linchpin guards /qa CANNOT write: `emit_*` fires ONLY on the rig
    // path, never the deterministic stub (§28.2(2)), so only a rig-backed
    // `MockModel` populates the trace FILE. They assert: (a) the file is written
    // through the rig boundary; (b) FULL content — a >80-char form survives
    // VERBATIM (vs the old 80-char `compact()` cut); (c) the per-turn `turn=N`
    // marker matches `AgentRequest.turn`.
    // -----------------------------------------------------------------------

    /// A guard that sets `CRANELISP_AGENT_TRACE` for the test body and restores
    /// the prior value on drop. Env mutation is process-global; nextest runs each
    /// test in its OWN process (process-per-test), so a per-test set is isolated.
    struct TraceEnvGuard(Option<String>);
    impl TraceEnvGuard {
        fn set(path: &str) -> Self {
            let prior = std::env::var("CRANELISP_AGENT_TRACE").ok();
            // SAFETY: unit test, single-threaded within this process at this point.
            unsafe { std::env::set_var("CRANELISP_AGENT_TRACE", path) };
            TraceEnvGuard(prior)
        }
    }
    impl Drop for TraceEnvGuard {
        fn drop(&mut self) {
            match &self.0 {
                Some(v) => unsafe { std::env::set_var("CRANELISP_AGENT_TRACE", v) },
                None => unsafe { std::env::remove_var("CRANELISP_AGENT_TRACE") },
            }
        }
    }

    /// Install a session whose agent is a rig-backed `MockModel` running `script`,
    /// with a defined `f` carrying `f_source` as its introspection source (so a
    /// real `/source f` pull through `process_commands` yields that text back to
    /// the model). Returns the session ready to drive a turn.
    fn rig_session_with_source(
        script: Vec<Vec<AssistantContent>>,
        f_source: &str,
    ) -> crate::session_v4::CompilerSession {
        let mock = MockModel::new(script);
        let rig = RigModel::new(mock).expect("tokio current-thread runtime builds");
        let mut s = crate::agent::test_support::repl_session();
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
                    source: Some(f_source.to_string()),
                    sexp: None,
                    expanded: None,
                    ast: None,
                    clif_ir: None,
                    code_size: None,
                },
            );
        }
        s.agent = Some(AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(rig)),
            provider_label: "mock (test)".to_string(),
            auto_accept: false,
            auto_accept_notice_shown: false,
            submit_gave_up: false,
            submit_committed: false,
            current_turn: 0,
            turn_ring: std::collections::VecDeque::new(),
        });
        s
    }

    // spec: repl/spec.md §17.21.1 — `CRANELISP_AGENT_TRACE=<path>` causes the
    // trace to be WRITTEN to the file through the rig boundary. A single Done turn
    // drives one `RigModel::complete`, so `emit_request`/`emit_response` append a
    // `[agent-trace]`-marked request + response block to the file. The stub never
    // reaches `emit_*`, so this rig-`MockModel` test is the only path that can
    // observe the file population.
    #[test]
    fn trace_file_is_written_through_the_rig_boundary() {
        let tmp = tempfile::tempdir().unwrap();
        let trace_path = tmp.path().join("trace.txt");
        let _g = TraceEnvGuard::set(trace_path.to_str().unwrap());

        // A single Done turn — one completion, one request+response trace block.
        let script = vec![vec![AssistantContent::text("f is the identity")]];
        let mut s = rig_session_with_source(script, "(defn f [x] x)");
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = crate::agent::types::NoConsent;
        s.agent_turn("what is f", &mut sink, &mut consent);

        assert!(trace_path.exists(), "the trace file must be written through the rig boundary");
        let body = std::fs::read_to_string(&trace_path).expect("trace file readable");
        assert!(
            body.contains("[agent-trace]") && body.contains("→request"),
            "the trace must carry the request block: {body}"
        );
        assert!(
            body.contains("←response") && body.contains("Done[text]: f is the identity"),
            "the trace must carry the response block (the model's Done prose): {body}"
        );
    }

    // spec: repl/spec.md §17.21.1 — FULL, UNTRUNCATED content (§28.1 core
    // requirement). A >80-char form fed back as a tool_result must survive in the
    // persisted trace VERBATIM — no `…` cut, no `⏎` newline-collapse — vs the old
    // `TEXT_TRUNCATE = 80` `compact()` cut. The model pulls `/source f` on turn 1;
    // turn 2's request transcript carries the long source as a tool_result, which
    // the rig boundary traces at `Grain::Full`.
    #[test]
    fn trace_file_carries_full_untruncated_form() {
        let tmp = tempfile::tempdir().unwrap();
        let trace_path = tmp.path().join("trace.txt");
        let _g = TraceEnvGuard::set(trace_path.to_str().unwrap());

        // A >80-char, multi-line source form — exactly what the old compact cut
        // would have truncated to an 80-char head + `…`.
        let long_form = "(defn very-long-helper-fn [first-arg second-arg]\n  \
            (add-i64 (mul-i64 first-arg 1000000) second-arg))";
        assert!(long_form.len() > 80, "fixture must exceed the old compact cap");

        // Turn 1: pull `/source f`; turn 2: Done (so turn-2's request carries the
        // fed-back long source as a tool_result that the trace renders Full).
        let turn1 = vec![AssistantContent::ToolCall(ToolCall::new(
            "toolu_1".to_string(),
            ToolFunction::new("source".to_string(), serde_json::json!({"argument": "f"})),
        ))];
        let turn2 = vec![AssistantContent::text("that is the helper")];
        let mut s = rig_session_with_source(vec![turn1, turn2], long_form);
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = crate::agent::types::NoConsent;
        s.agent_turn("show me the source of f", &mut sink, &mut consent);

        let body = std::fs::read_to_string(&trace_path).expect("trace file readable");
        // VERBATIM: the whole long form is present, newline and all — NOT truncated.
        assert!(
            body.contains(long_form),
            "the persisted trace must carry the long form VERBATIM (Full grain, \
             §28.1), got: {body}"
        );
        // +neg: no compact-grain truncation glyphs leaked into the persisted file.
        assert!(
            !body.contains('…'),
            "the persisted (Full) trace must NOT carry the `…` truncation glyph: {body}"
        );
        assert!(
            !body.contains('⏎'),
            "the persisted (Full) trace must NOT collapse newlines to `⏎`: {body}"
        );
    }

    // spec: repl/spec.md §17.21.3 — the trace's per-turn `turn=N` marker carries
    // the SAME turn as `AgentRequest.turn` (the log↔trace join key, §28.2). The
    // first model exchange is turn 1; a pull then Done drives turns 1 and 2, so
    // the persisted trace must carry BOTH `turn=1` and `turn=2` markers, matching
    // the 1-based loop-step ids `assemble_request` stamps onto `AgentRequest.turn`.
    #[test]
    fn trace_marker_turn_matches_agent_request_turn() {
        let tmp = tempfile::tempdir().unwrap();
        let trace_path = tmp.path().join("trace.txt");
        let _g = TraceEnvGuard::set(trace_path.to_str().unwrap());

        // Turn 1: pull `/source f`; turn 2: Done — two completions ⇒ turns 1 and 2.
        let turn1 = vec![AssistantContent::ToolCall(ToolCall::new(
            "toolu_1".to_string(),
            ToolFunction::new("source".to_string(), serde_json::json!({"argument": "f"})),
        ))];
        let turn2 = vec![AssistantContent::text("done")];
        let mut s = rig_session_with_source(vec![turn1, turn2], "(defn f [x] x)");
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = crate::agent::types::NoConsent;
        s.agent_turn("show me the source of f", &mut sink, &mut consent);

        let body = std::fs::read_to_string(&trace_path).expect("trace file readable");
        // The 1-based per-turn markers — the SAME ids `AgentRequest.turn` carries.
        assert!(
            body.contains("turn=1"),
            "the trace must carry the turn=1 marker (the first exchange): {body}"
        );
        assert!(
            body.contains("turn=2"),
            "the trace must carry the turn=2 marker (the continuation exchange): {body}"
        );
        // The request AND response of one exchange share the turn id (the response
        // belongs to its request's turn) — both `→request` and `←response` lines
        // for turn 1 are present and stamped.
        assert!(
            body.lines().any(|l| l.contains("turn=1") && l.contains("→request")),
            "a turn=1 request marker must be present: {body}"
        );
        assert!(
            body.lines().any(|l| l.contains("turn=1") && l.contains("←response")),
            "a turn=1 response marker must be present (response shares request's turn): {body}"
        );
    }

    // -----------------------------------------------------------------------
    // FIXME 0541 — a single assistant turn issuing ≥2 tool calls must keep the
    // transcript wire-valid. `agent_turn` records the `AssistantToolCalls(batch)`
    // ONCE then loops `record_pull_result` per call; before the fix
    // `record_pull_result` inspected only `transcript.last()`, so after call 1's
    // `ToolResult` was pushed, calls 2..N were demoted to `User` turns — their
    // `tool_use` ids left uncovered → `assert_transcript_wire_valid` (a hard
    // panic on the continuation turn). These are the durable regression guard.
    // -----------------------------------------------------------------------

    /// The focused seam guard: drive `record_pull_result` directly over a 3-call
    /// batch (the exact `agent_turn` loop shape) and assert every call closes as a
    /// `ToolResult` and the transcript is wire-valid. Independent of the model
    /// loop, so it pins the seam even if `agent_turn` changes. FAILS before the
    /// fix (calls b/c demote to `User`, transcript wire-invalid).
    // spec: repl/spec.md §17 — Anthropic tool_use↔tool_result pairing over a
    // multi-tool-call batch (`types.rs::assert_transcript_wire_valid`).
    #[test]
    fn record_pull_result_closes_every_call_in_a_multi_call_batch() {
        use crate::agent::types::{
            assert_transcript_wire_valid, AgentState, ToolCallRequest, ToolCallResult, Turn,
        };
        let mut state = AgentState {
            transcript: Vec::new(),
            model: None,
            provider_label: "test".to_string(),
            auto_accept: false,
            auto_accept_notice_shown: false,
            submit_gave_up: false,
            submit_committed: false,
            current_turn: 1,
            turn_ring: std::collections::VecDeque::new(),
        };
        let calls = vec![
            ToolCallRequest { id: "toolu_a".into(), name: "source".into(), argument: "f".into() },
            ToolCallRequest { id: "toolu_b".into(), name: "info".into(), argument: "g".into() },
            ToolCallRequest { id: "toolu_c".into(), name: "sig".into(), argument: "h".into() },
        ];
        // One assistant turn opens the batch, then one result per call in order.
        state.record_assistant_tool_calls(calls.clone());
        for c in &calls {
            state.record_pull_result(ToolCallResult {
                id: c.id.clone(),
                command: format!("/{} {}", c.name, c.argument),
                output: format!("output for {}", c.id),
            });
        }
        // (a) all three close as ToolResult (none demoted to User).
        let result_ids: Vec<&str> = state
            .transcript
            .iter()
            .filter_map(|t| match t {
                Turn::ToolResult(r) => Some(r.id.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(
            result_ids,
            vec!["toolu_a", "toolu_b", "toolu_c"],
            "every call in a multi-call batch must close as a ToolResult, not \
             demote to User; transcript={:?}",
            state.transcript
        );
        // (b) the assembled transcript is wire-valid in both directions.
        assert!(
            assert_transcript_wire_valid(&state.transcript).is_ok(),
            "the multi-call batch transcript must be wire-valid: {:?}",
            assert_transcript_wire_valid(&state.transcript)
        );
    }

    // spec: repl/spec.md §17 — the full model↔tool loop through the REAL rig
    // boundary with a 3-tool-call turn 1. Before the fix, turn 2's
    // `assemble_request` `debug_assert!`-panicked on the wire-invalid transcript
    // (the exact FIXME 0541 crash); after the fix the turn completes and the
    // continuation request is wire-paired.
    #[test]
    fn multi_tool_call_turn_through_loop_stays_wire_valid() {
        let call = |id: &str| {
            AssistantContent::ToolCall(ToolCall::new(
                id.to_string(),
                ToolFunction::new("source".to_string(), serde_json::json!({"argument": "f"})),
            ))
        };
        // Turn 1: THREE tool calls in ONE ModelResponse::ToolCalls; turn 2: Done.
        let turn1 = vec![call("toolu_a"), call("toolu_b"), call("toolu_c")];
        let turn2 = vec![AssistantContent::text("here are the three")];
        let mut s = rig_session_with_source(vec![turn1, turn2], "(defn f [x] x)");
        let mut sink: Vec<u8> = Vec::new();
        let mut consent = crate::agent::types::NoConsent;
        // Pre-fix: this call panics inside agent_turn (assemble_request's
        // debug_assert). Post-fix: it returns cleanly.
        s.agent_turn("show me f three times", &mut sink, &mut consent);

        let transcript = &s.agent.as_ref().unwrap().transcript;
        let result_ids: Vec<&str> = transcript
            .iter()
            .filter_map(|t| match t {
                Turn::ToolResult(r) => Some(r.id.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(
            result_ids,
            vec!["toolu_a", "toolu_b", "toolu_c"],
            "every call in the 3-call batch must close as a ToolResult; \
             transcript={transcript:?}"
        );
        assert!(
            crate::agent::types::assert_transcript_wire_valid(transcript).is_ok(),
            "the multi-call batch transcript must be wire-valid: {:?}",
            crate::agent::types::assert_transcript_wire_valid(transcript)
        );
    }

    // spec: repl/spec.md §17 — FIXME 0541 DOCUMENTED RESIDUAL (out of scope,
    // /review IMPORTANT #2). 0541's scope is a batch of READ-ONLY pulls (the
    // observed crash: `/imports`, `/search`, `/search`) — plus a CLEAN `submit`
    // in a batch, which records nothing intervening and is handled (its result
    // closes contiguously). The residual is NARROWER: a batch that places a
    // `submit` NOT-last, where that submit needs REPAIR. `run_submit`'s
    // `validate_and_repair` records its OWN `AssistantToolCalls`/`ToolResult`
    // turns onto the MAIN transcript (pull.rs ~743/759), interposing them between
    // the batch `AssistantToolCalls` and the later call's result. Two consequences,
    // BOTH inherent to the interposition (not merely `record_pull_result`'s choice):
    //   1. `record_pull_result` for the later call walks back over the interposed
    //      repair pair, finds the repair `AssistantToolCalls` (which does not
    //      promise the later id), and demotes the later result to a `User` turn;
    //   2. even if it instead found the batch `AssistantToolCalls`, that turn is no
    //      longer IMMEDIATELY followed by its results (the repair pair sits between)
    //      — so `assert_transcript_wire_valid`'s forward rule fails REGARDLESS.
    // Fully closing this needs a batch/repair *contiguity* restructure (defer the
    // per-call results so a batch's results are recorded as one contiguous run),
    // which is beyond 0541's read-only/clean-submit scope. This guard PINS the
    // current behaviour (the later call demotes; the transcript is wire-invalid in
    // this interleaved corner) so a future contiguity fix flips it — and the author
    // then updates it to assert wire-VALID coverage of every batch id.
    #[test]
    fn submit_repair_interleaved_in_batch_is_known_wire_invalid_residual() {
        use crate::agent::types::{
            assert_transcript_wire_valid, AgentState, ToolCallRequest, ToolCallResult, Turn,
        };
        let mut state = AgentState {
            transcript: Vec::new(),
            model: None,
            provider_label: "test".to_string(),
            auto_accept: false,
            auto_accept_notice_shown: false,
            submit_gave_up: false,
            submit_committed: false,
            current_turn: 1,
            turn_ring: std::collections::VecDeque::new(),
        };
        // The batch: [a = submit (will repair), b = a read call]. submit NOT last.
        state.record_assistant_tool_calls(vec![
            ToolCallRequest { id: "a".into(), name: "submit".into(), argument: "(defn x [".into() },
            ToolCallRequest { id: "b".into(), name: "source".into(), argument: "f".into() },
        ]);
        // run_submit(a)'s repair loop records its OWN paired ATC/TR onto the main
        // transcript (the essence of the interposition) before the outer result.
        state.record_assistant_tool_calls(vec![ToolCallRequest {
            id: "a-repair".into(),
            name: "submit".into(),
            argument: "(defn x [] 0)".into(),
        }]);
        state.record_tool_result(ToolCallResult {
            id: "a-repair".into(),
            command: "submit".into(),
            output: "compiler feedback".into(),
        });
        // Now the OUTER loop records the later batch call `b`'s result. It walks
        // back over the interposed repair pair, hits the repair ATC (no `b`), and
        // demotes `b` to a User turn — the documented current behaviour.
        state.record_pull_result(ToolCallResult {
            id: "b".into(),
            command: "/source f".into(),
            output: "(defn f [x] x)".into(),
        });

        // (1) `b` was demoted — there is NO ToolResult carrying id "b".
        let has_b_result = state
            .transcript
            .iter()
            .any(|t| matches!(t, Turn::ToolResult(r) if r.id == "b"));
        assert!(
            !has_b_result,
            "documented residual: the later batch call demotes to User (no ToolResult \
             for `b`); transcript={:?}",
            state.transcript
        );
        // (2) The transcript is wire-INVALID in this interleaved corner (the batch
        // ATC's `b` is uncovered / the batch ATC is not immediately followed by its
        // results). Pinned as the accepted out-of-scope residual.
        assert!(
            assert_transcript_wire_valid(&state.transcript).is_err(),
            "documented residual: a submit-repair interleaved inside a NON-last batch \
             position is currently wire-invalid; a future contiguity fix flips this \
             guard. transcript={:?}",
            state.transcript
        );
    }

    // spec: design/int/agent.md §6 — every assembled rig `CompletionRequest` MUST
    // carry `max_tokens` (FIXME 0554). Anthropic's Messages API makes the field
    // MANDATORY; without it EVERY turn 400s before a token streams
    // (`RequestError: max_tokens must be set for Anthropic`). `build_request` is
    // the single shared assembly for `complete` and `complete_streaming`
    // (Principle 7), so this one assertion guards BOTH transports.
    //
    // This is a UNIT test, not an e2e, BECAUSE the defect is not e2e-reproducible:
    // the agent module is `#[cfg(feature = "agent")]` (the default suite never
    // compiles it), the e2e stub provider (`CRANELISP_AGENT_PROVIDER=stub`) bypasses
    // `RigModel`/`build_request` entirely, and CI cannot call the live Anthropic API.
    // Constructing `build_request` against the `MockModel` (the real rig
    // `CompletionModel` trait, below the membrane) is the only path that observes the
    // assembled `CompletionRequest.max_tokens`.
    #[test]
    fn build_request_sets_max_tokens_for_anthropic() {
        let rig = RigModel::new(MockModel::new(Vec::new()))
            .expect("tokio current-thread runtime builds");
        // A representative request — a plain user turn, no tools/transcript needed:
        // the missing field is on the shared builder, independent of request content.
        let req = AgentRequest { user: "what model are you?".to_string(), ..Default::default() };

        let rig_req = rig.build_request(&req);

        assert!(
            rig_req.max_tokens.is_some(),
            "build_request must set max_tokens — Anthropic rejects a request that omits it"
        );
        assert_eq!(
            rig_req.max_tokens,
            Some(AGENT_MAX_TOKENS),
            "build_request must set max_tokens to the AGENT_MAX_TOKENS budget"
        );
    }
}
