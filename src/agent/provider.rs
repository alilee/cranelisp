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

impl<M: CompletionModel> AgentModel for RigModel<M> {
    fn complete(&mut self, request: &AgentRequest) -> Result<ModelResponse, String> {
        // Build the rig request via the membrane (`request.rs`) + the model's
        // own builder (it carries the model handle rig needs).
        let preamble = agent_request::preamble(request);
        let history = agent_request::history_messages(request);
        let prompt = agent_request::prompt_message(request);
        let tools = agent_request::tool_definitions(request);

        let rig_req = self
            .model
            .completion_request(prompt)
            .preamble(preamble)
            .messages(history)
            .tools(tools)
            .build();

        let resp = self
            .runtime
            .block_on(self.model.completion(rig_req))
            .map_err(|e| format!("completion failed: {e}"))?;

        Ok(agent_request::lower_response(resp.choice))
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
            _request: CompletionRequest,
        ) -> Result<StreamingCompletionResponse<Self::StreamingResponse>, CompletionError> {
            unimplemented!("the agent loop never streams (block_on completion only)")
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
}
