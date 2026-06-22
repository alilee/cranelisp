// agent/request.rs — the rig membrane (design/int/agent.md §6.1, the one
// place coupled to rig's request/response shapes).
//
// Translates the agent's provider-neutral turn vocabulary (`types.rs`) into rig
// `Message` / `ToolDefinition` / preamble strings, and lowers a rig
// `CompletionResponse`'s `AssistantContent` back into the neutral `ModelResponse`.
// The harvester, primer, pull, and transcript machinery never see a rig type —
// THIS is the membrane (§6.1). Dropping rig later touches this file + the loop +
// provider.rs, never a cross-crate edge (the accepted coupling tradeoff §6.5).

#![cfg(feature = "agent")]

use rig_core::completion::message::{AssistantContent, Message};
use rig_core::completion::request::ToolDefinition;

use crate::agent::types::{AgentRequest, ModelResponse, ToolCallRequest, Turn};

/// The preamble (system content) for a request: the always-on primer (§7) +
/// the harvested session context (§5), concatenated. rig puts the preamble into
/// the provider's system slot (the canonical place for instructions).
pub fn preamble(req: &AgentRequest) -> String {
    let mut p = String::with_capacity(req.primer.len() + req.harvest.len() + 64);
    p.push_str(&req.primer);
    if !req.harvest.is_empty() {
        p.push_str("\n\n== Session context (harvested) ==\n");
        p.push_str(&req.harvest);
    }
    p
}

/// The chat history (transcript turns) as rig `Message`s, in order (§3.4). The
/// caller appends the current user turn as the final message (rig requires the
/// last message to be the prompt).
pub fn history_messages(req: &AgentRequest) -> Vec<Message> {
    let mut msgs = Vec::with_capacity(req.transcript.len() + 1);
    for turn in &req.transcript {
        match turn {
            Turn::User(text) => msgs.push(Message::user(text.clone())),
            Turn::Assistant(text) => msgs.push(Message::assistant(text.clone())),
            Turn::ToolResult(r) => {
                // A pulled command + its output, fed back as a tool result so the
                // model sees what its pull returned (§4.1). Correlated by call id.
                let id = if r.id.is_empty() { r.command.clone() } else { r.id.clone() };
                msgs.push(Message::tool_result(id, r.output.clone()));
            }
        }
    }
    msgs
}

/// The current user turn as the final (prompt) message.
pub fn prompt_message(req: &AgentRequest) -> Message {
    Message::user(req.user.clone())
}

/// The read-only tool allowlist (§4.2) as rig `ToolDefinition`s. Each tool takes
/// a single string `argument` (a symbol name or expression). The JSON schema is
/// the minimal one-string-param shape every provider accepts.
pub fn tool_definitions(req: &AgentRequest) -> Vec<ToolDefinition> {
    req.tools
        .iter()
        .map(|t| ToolDefinition {
            name: t.name.clone(),
            description: t.description.clone(),
            parameters: serde_json::json!({
                "type": "object",
                "properties": {
                    "argument": {
                        "type": "string",
                        "description": "The symbol name or expression the command operates on."
                    }
                },
                "required": ["argument"]
            }),
        })
        .collect()
}

/// Lower a rig response's assistant content into the neutral `ModelResponse`
/// (§6.1, §3.2). Any tool call → `ToolCalls`; otherwise the accumulated text →
/// `Done(prose)`. (Reasoning / image content is ignored for the MVP.)
pub fn lower_response<I>(choices: I) -> ModelResponse
where
    I: IntoIterator<Item = AssistantContent>,
{
    let mut prose = String::new();
    let mut calls: Vec<ToolCallRequest> = Vec::new();
    for content in choices {
        match content {
            AssistantContent::Text(t) => {
                if !prose.is_empty() {
                    prose.push('\n');
                }
                prose.push_str(&t.text);
            }
            AssistantContent::ToolCall(tc) => {
                // Pull the single `argument` string out of the JSON args; if the
                // provider emitted a bare value or a differently-keyed object,
                // fall back to the whole arguments rendered compactly.
                let argument = tc
                    .function
                    .arguments
                    .get("argument")
                    .and_then(|v| v.as_str())
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| match &tc.function.arguments {
                        serde_json::Value::String(s) => s.clone(),
                        other => other.to_string(),
                    });
                calls.push(ToolCallRequest {
                    id: tc.id.clone(),
                    name: tc.function.name.clone(),
                    argument,
                });
            }
            _ => {}
        }
    }
    if calls.is_empty() {
        ModelResponse::Done(prose)
    } else {
        ModelResponse::ToolCalls(calls)
    }
}
