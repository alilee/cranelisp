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
    if !enabled {
        return AgentState {
            transcript: Vec::new(),
            model: None,
            provider_label: "disabled (--agent not set)".to_string(),
        };
    }

    let provider = std::env::var(PROVIDER_VAR).unwrap_or_else(|_| "anthropic".to_string());
    match provider.as_str() {
        "stub" => build_stub_state(),
        "ollama" => build_ollama_state(),
        _ => build_anthropic_state(),
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
                        Ok(rig) => AgentState {
                            transcript: Vec::new(),
                            model: Some(Box::new(rig)),
                            provider_label: "anthropic".to_string(),
                        },
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
                        Ok(rig) => AgentState {
                            transcript: Vec::new(),
                            model: Some(Box::new(rig)),
                            provider_label: "ollama (local)".to_string(),
                        },
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
        Ok(stub) => AgentState {
            transcript: Vec::new(),
            model: Some(Box::new(stub)),
            provider_label: "stub (test)".to_string(),
        },
        Err(reason) => dormant(&format!("stub ({reason})")),
    }
}

fn dormant(label: &str) -> AgentState {
    AgentState {
        transcript: Vec::new(),
        model: None,
        provider_label: label.to_string(),
    }
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
    /// Push a tool-result turn (a pulled command + its output) onto the transcript.
    pub fn record_tool_result(&mut self, result: crate::agent::types::ToolCallResult) {
        self.transcript.push(Turn::ToolResult(result));
    }
}
