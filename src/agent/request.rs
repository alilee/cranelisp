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

use rig_core::OneOrMany;
use rig_core::completion::message::{
    AssistantContent, Message, ToolResultContent, UserContent,
};
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

/// Lower the whole transcript to rig `Message`s, in order, COALESCING each
/// contiguous run of `Turn::ToolResult` into ONE `Message::User` that carries all
/// N `tool_result` blocks (in order).
///
/// This is the WIRE half of the multi-tool-call fix (FIXME 0541; the recording
/// half is `provider.rs::record_pull_result`). The Anthropic Messages API
/// requires every `tool_result` for a single assistant `tool_use` turn to arrive
/// in ONE following user message, and forbids two consecutive same-role messages.
/// rig's Anthropic provider maps rig `Message`s **1:1** to API messages — it does
/// NOT coalesce (verified in rig-core 0.39 `providers/anthropic/completion.rs`:
/// `full_history.into_iter().map(Message::try_from).collect()`). So a batch of N
/// tool calls, lowered one-`Message`-per-result, would send N consecutive `user`
/// messages and 400 on the wire (the panic's live twin — symptom, not feature).
/// Coalescing here keeps the wire valid: `assistant(tool_use a,b,c)` is followed
/// by a single `user(tool_result a,b,c)`.
fn transcript_to_messages(transcript: &[Turn]) -> Vec<Message> {
    let mut msgs = Vec::with_capacity(transcript.len());
    let mut i = 0;
    while i < transcript.len() {
        if matches!(transcript[i], Turn::ToolResult(_)) {
            // Fold the whole contiguous run of ToolResults into ONE user message
            // carrying every tool_result block in order (the Anthropic grouping
            // rule). One user message per RUN, not per result.
            let mut blocks: Vec<UserContent> = Vec::new();
            while let Some(Turn::ToolResult(r)) = transcript.get(i) {
                let id = tool_call_id(&r.id, &r.command);
                blocks.push(UserContent::tool_result(
                    id,
                    OneOrMany::one(ToolResultContent::text(r.output.clone())),
                ));
                i += 1;
            }
            if let Ok(content) = OneOrMany::many(blocks) {
                msgs.push(Message::User { content });
            }
        } else {
            if let Some(msg) = turn_to_message(&transcript[i]) {
                msgs.push(msg);
            }
            i += 1;
        }
    }
    msgs
}

/// The chat history (transcript turns) as rig `Message`s, in order (§3.4).
///
/// CRITICAL — the history is every wire message EXCEPT the last: the LAST message
/// is the prompt (`prompt_message`), which rig appends as the final wire message
/// (`completion_request(prompt).build()` pushes the prompt last). The model
/// answers the LAST message, so the last message MUST be the most recent real
/// content — the just-fed-back `tool_result`(s) on a continuation step, the user
/// question on the opening step. Folding the whole transcript into history AND
/// re-appending the original user turn as the prompt (the pre-fix shape) left the
/// wire sequence ending `…, tool_result, user(original-question)` — so the model
/// never "saw" the result as the thing to act on and re-requested the same tool
/// forever (the S88 Lane-C pull-loop defect). Splitting head/last fixes it.
///
/// The split is over the COALESCED message sequence (`transcript_to_messages`),
/// NOT the raw turns — so a trailing multi-`tool_result` run is ONE prompt
/// message (all its blocks), never split across the history/prompt boundary into
/// two consecutive user messages (FIXME 0541 wire half).
pub fn history_messages(req: &AgentRequest) -> Vec<Message> {
    let mut msgs = transcript_to_messages(&req.transcript);
    msgs.pop(); // drop the last message — it is the prompt (`prompt_message`).
    msgs
}

/// Lower one transcript `Turn` to a rig `Message`. Returns `None` for a turn
/// that builds no meaningful message (an empty assistant tool-call set — the
/// loop never records one, but guard defensively). Contiguous `ToolResult` runs
/// are coalesced by `transcript_to_messages` (the Anthropic grouping rule), so
/// the single-result arm here builds the one-result user message used only when a
/// `ToolResult` stands alone.
fn turn_to_message(turn: &Turn) -> Option<Message> {
    match turn {
        Turn::User(text) => Some(Message::user(text.clone())),
        Turn::Assistant(text) => Some(Message::assistant(text.clone())),
        Turn::AssistantToolCalls(calls) => {
            // The assistant `tool_use` turn — emitted BEFORE the matching
            // `tool_result`(s) so the Anthropic API's pairing invariant holds
            // (every `tool_result` block must follow an assistant message
            // carrying the matching `tool_use` id — §4.1). An empty call set
            // would build an empty assistant message, which is meaningless;
            // skip it (the loop never records an empty tool-call turn).
            assistant_tool_calls_message(calls)
        }
        Turn::ToolResult(r) => {
            // A pulled command + its output, fed back as a tool result so the
            // model sees what its pull returned (§4.1). Correlated by call id —
            // the id MUST match the `tool_use` id in the preceding assistant
            // turn, or the provider rejects the request.
            let id = tool_call_id(&r.id, &r.command);
            Some(Message::tool_result(id, r.output.clone()))
        }
    }
}

/// The correlation id used to pair a `tool_result` with its `tool_use`. Falls
/// back to the rendered command when the provider supplied no id (the stub /
/// id-free path), so the two sides still agree on a key.
fn tool_call_id(id: &str, command: &str) -> String {
    if id.is_empty() {
        command.to_string()
    } else {
        id.to_string()
    }
}

/// Build the assistant `tool_use` message for one loop step's tool calls. Each
/// `ToolCallRequest` is lowered to a rig `tool_call` content block carrying the
/// SAME id the model emitted (and that the matching `tool_result` echoes), the
/// command name, and the `{ "argument": … }` JSON args matching the tool schema
/// (`tool_definitions`). Returns `None` for an empty call set.
fn assistant_tool_calls_message(calls: &[ToolCallRequest]) -> Option<Message> {
    let content: Vec<AssistantContent> = calls
        .iter()
        .map(|c| {
            AssistantContent::tool_call(
                c.id.clone(),
                c.name.clone(),
                serde_json::json!({ "argument": c.argument }),
            )
        })
        .collect();
    OneOrMany::many(content)
        .ok()
        .map(|content| Message::Assistant { id: None, content })
}

/// The final (prompt) message — the LAST transcript turn, which rig appends as
/// the final wire message and the model answers.
///
/// On the opening loop step the last message is the user's question (recorded by
/// `record_user` before the loop); on a continuation step it is the just-fed-back
/// `tool_result`(s) (a CONTIGUOUS run coalesced into one user message). Either way
/// the model is answering the most recent real content — NOT a stale re-statement
/// of the original question (the pull-loop defect). Falls back to `req.user` only
/// when the transcript is empty (a request assembled without `record_user`, e.g.
/// a direct unit test) so the prompt is never absent (rig requires one).
///
/// Derives from the COALESCED sequence (`transcript_to_messages`), so a trailing
/// multi-`tool_result` batch is ONE prompt message carrying all its blocks — the
/// wire half of FIXME 0541.
pub fn prompt_message(req: &AgentRequest) -> Message {
    transcript_to_messages(&req.transcript)
        .pop()
        .unwrap_or_else(|| Message::user(req.user.clone()))
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
                    },
                    // F1 (§17.20.3a/b) — REQUIRED on every probe/pull tool: the
                    // specific thing the agent wanted to learn by issuing this
                    // probe. Recorded verbatim (§17.20.3a F1) → the primer-gap
                    // worklist. Required, not optional (§17.20.3b).
                    "question": {
                        "type": "string",
                        "description": "The specific thing you want to learn by running this command \
                                        (e.g. \"does fn take a multi-arity clause form\"). Required."
                    }
                },
                "required": ["argument", "question"]
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
                // F1 (§17.20.3a/b) — the required `question` argument (what the
                // agent wanted to learn). Absent ⇒ `None` (graceful; a schema
                // non-conformance the harness does not crash on).
                let question = tc
                    .function
                    .arguments
                    .get("question")
                    .and_then(|v| v.as_str())
                    .map(|s| s.to_string());
                calls.push(ToolCallRequest {
                    id: tc.id.clone(),
                    name: tc.function.name.clone(),
                    argument,
                    question,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::types::{ToolCallResult, Turn};
    use rig_core::completion::message::UserContent;

    fn tool_call(id: &str, name: &str, arg: &str) -> ToolCallRequest {
        ToolCallRequest {
            id: id.to_string(),
            name: name.to_string(),
            argument: arg.to_string(),
            question: None,
        }
    }

    // OB-2 (§17.20.3b / repl/spec.md §17.2.1) — the ENUMERATED per-tool
    // question-required obligation. `question` is a REQUIRED argument on EVERY
    // probe/pull tool; a probe with no `question` is a tool-schema
    // non-conformance. This pins one assertion per probe tool the §17.2.1 set
    // names (fail-on-revert): each declares `question` in its schema `required`.
    // spec: repl/spec.md §17.20.3b — probe tools carry a required `question`.
    #[test]
    fn every_probe_tool_schema_requires_a_question_argument() {
        let req = AgentRequest {
            tools: crate::agent::pull::tool_defs(),
            ..Default::default()
        };
        let defs = tool_definitions(&req);
        // The §17.2.1 probe set — one enumerated obligation per tool.
        let probe_tools = [
            "type", "syntax", "sig", "info", "source", "doc", "exports", "list",
            "search", "refs",
        ];
        for probe in probe_tools {
            let def = defs
                .iter()
                .find(|d| d.name == probe)
                .unwrap_or_else(|| panic!("probe tool `{probe}` (§17.2.1) must be offered"));
            let required = def.parameters["required"]
                .as_array()
                .unwrap_or_else(|| panic!("`{probe}` schema must have a `required` array"));
            assert!(
                required.iter().any(|v| v == "question"),
                "OB-2: probe tool `{probe}` MUST declare `question` as a required \
                 argument (§17.20.3b); required={required:?}"
            );
            assert!(
                def.parameters["properties"].get("question").is_some(),
                "OB-2: probe tool `{probe}` MUST declare a `question` property; \
                 schema={:?}",
                def.parameters
            );
        }
    }

    fn tool_result(id: &str, command: &str, output: &str) -> ToolCallResult {
        ToolCallResult {
            id: id.to_string(),
            command: command.to_string(),
            output: output.to_string(),
        }
    }

    /// Extract the tool_use id(s) from an assistant `Message`, in order.
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

    /// Extract the tool_result id(s) from a user `Message`, in order.
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

    /// The full wire message sequence `RigModel::complete` builds: the history
    /// (all-but-last transcript turn) followed by the prompt (the last turn). The
    /// model answers the LAST element, so assertions about "what the model sees"
    /// must be made over THIS sequence, not over `history_messages` alone.
    fn wire_messages(req: &AgentRequest) -> Vec<Message> {
        let mut msgs = history_messages(req);
        msgs.push(prompt_message(req));
        msgs
    }

    /// The tool_result *content text* of a user `Message`, concatenated, in order.
    fn user_tool_result_text(msg: &Message) -> String {
        match msg {
            Message::User { content } => content
                .iter()
                .filter_map(|c| match c {
                    UserContent::ToolResult(r) => Some(
                        r.content
                            .iter()
                            .filter_map(|tc| match tc {
                                rig_core::completion::message::ToolResultContent::Text(t) => {
                                    Some(t.text.clone())
                                }
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

    // spec: repl/spec.md §17 — the Anthropic pairing invariant: a `tool_result`
    // block MUST be immediately preceded by an assistant message carrying the
    // matching `tool_use` block (same id). This is the exact seam where the
    // S88 Lane-C 400 lived — the assistant tool_use turn was omitted, so the
    // built rig request had a `tool_result` with no preceding `tool_use`. The
    // pure regression guard: build the FULL wire sequence (history + prompt) from
    // a transcript that includes the assistant tool-call turn + its result, and
    // assert the order + id match. (The tool_result is the LAST turn, so it lands
    // in the prompt slot — the model answers it, not a re-asked question.)
    #[test]
    fn tool_use_precedes_matching_tool_result_with_matching_id() {
        let req = AgentRequest {
            transcript: vec![
                Turn::User("show me the source of f".to_string()),
                Turn::AssistantToolCalls(vec![tool_call("toolu_01H", "source", "f")]),
                Turn::ToolResult(tool_result("toolu_01H", "/source f", "(defn f [x] x)")),
            ],
            ..Default::default()
        };

        let msgs = wire_messages(&req);
        // user, assistant(tool_use), user(tool_result) — three messages.
        assert_eq!(msgs.len(), 3, "expected user + assistant-tool_use + tool_result");

        let use_ids = assistant_tool_use_ids(&msgs[1]);
        let result_ids = user_tool_result_ids(&msgs[2]);
        assert_eq!(
            use_ids,
            vec!["toolu_01H".to_string()],
            "msg[1] must be the assistant tool_use carrying the call id"
        );
        assert_eq!(
            result_ids,
            vec!["toolu_01H".to_string()],
            "msg[2] must be the tool_result echoing the SAME id"
        );
        // The pairing invariant: the tool_result is immediately preceded by the
        // matching tool_use (same id, adjacent).
        assert_eq!(
            use_ids, result_ids,
            "tool_use id and the following tool_result id must match"
        );
        // The defect guard: the tool_result is the FINAL message (the prompt) and
        // CARRIES the command output — the model answers the result, not a stale
        // re-statement of the question (the pull-loop root cause).
        assert!(
            user_tool_result_text(&msgs[2]).contains("(defn f [x] x)"),
            "the final message must carry the command output, got: {:?}",
            user_tool_result_text(&msgs[2])
        );
    }

    // spec: repl/spec.md §17 — the pull-loop defect guard at the membrane: when
    // the transcript ends with a fed-back tool_result (a continuation step), the
    // FINAL wire message (the prompt the model answers) is that tool_result and
    // it CARRIES the command output — NOT a re-pushed copy of the original user
    // question. Pre-fix the prompt was always `req.user` (the original question)
    // appended after the tool_result, so the model never acted on the result and
    // re-requested the same tool forever.
    #[test]
    fn continuation_prompt_is_tool_result_carrying_output_not_restated_question() {
        let req = AgentRequest {
            user: "show me the source of f".to_string(),
            transcript: vec![
                Turn::User("show me the source of f".to_string()),
                Turn::AssistantToolCalls(vec![tool_call("toolu_01H", "source", "f")]),
                Turn::ToolResult(tool_result(
                    "toolu_01H",
                    "/source f",
                    "; source for f\n(defn f [x] x)",
                )),
            ],
            ..Default::default()
        };

        let msgs = wire_messages(&req);
        let last = msgs.last().expect("a prompt message");
        // +neg: the final message is NOT a re-asked user question.
        assert!(
            user_tool_result_ids(last) == vec!["toolu_01H".to_string()],
            "the final (prompt) message must be the tool_result, not the question"
        );
        // The final message carries the actual command output.
        assert!(
            user_tool_result_text(last).contains("(defn f [x] x)"),
            "the final tool_result prompt must carry the command output, got: {:?}",
            user_tool_result_text(last)
        );
        // +neg: the original question is NOT also re-appended as a trailing user
        // text message (the duplication that caused the loop).
        let trailing_question = matches!(
            last,
            Message::User { content }
                if content.iter().any(|c| matches!(
                    c, UserContent::Text(t) if t.text.contains("show me the source")))
        );
        assert!(!trailing_question, "the original question must not be re-appended as the prompt");
    }

    // spec: repl/spec.md §17 — the opening step (transcript = just the user turn)
    // sends the question EXACTLY ONCE: with the head/last split, history is empty
    // and the prompt is the lone user turn — no duplicate.
    #[test]
    fn opening_step_sends_user_question_once() {
        let req = AgentRequest {
            user: "what is f".to_string(),
            transcript: vec![Turn::User("what is f".to_string())],
            ..Default::default()
        };
        let msgs = wire_messages(&req);
        assert_eq!(msgs.len(), 1, "opening step is a single user message, not a duplicate");
        let user_texts = msgs
            .iter()
            .filter(|m| matches!(m, Message::User { .. }))
            .count();
        assert_eq!(user_texts, 1, "the question must appear exactly once");
    }

    // spec: repl/spec.md §17 (+neg) — a `tool_result` is NEVER emitted without a
    // preceding `tool_use` carrying its id. Every tool_result message's id set
    // must be a subset of the ids of the immediately-preceding assistant message.
    #[test]
    fn no_tool_result_without_preceding_matching_tool_use() {
        let req = AgentRequest {
            transcript: vec![
                Turn::User("two pulls".to_string()),
                Turn::AssistantToolCalls(vec![
                    tool_call("id-a", "source", "f"),
                    tool_call("id-b", "info", "g"),
                ]),
                Turn::ToolResult(tool_result("id-a", "/source f", "body-f")),
                Turn::ToolResult(tool_result("id-b", "/info g", "type-g")),
                Turn::Assistant("here is what I found".to_string()),
            ],
            ..Default::default()
        };

        let msgs = wire_messages(&req);
        // For each tool_result message, the most recent preceding assistant
        // tool_use message must carry its id.
        let mut last_use_ids: Vec<String> = Vec::new();
        for msg in &msgs {
            let uses = assistant_tool_use_ids(msg);
            if !uses.is_empty() {
                last_use_ids = uses;
            }
            for rid in user_tool_result_ids(msg) {
                assert!(
                    last_use_ids.contains(&rid),
                    "tool_result id {rid} has no preceding matching tool_use; \
                     preceding tool_use ids were {last_use_ids:?}"
                );
            }
        }
    }

    // spec: repl/spec.md §17 — a plain prose-only transcript (no tool calls)
    // builds no tool_use / tool_result messages (the common path is unchanged).
    #[test]
    fn prose_only_transcript_has_no_tool_blocks() {
        let req = AgentRequest {
            transcript: vec![
                Turn::User("hi".to_string()),
                Turn::Assistant("hello".to_string()),
            ],
            ..Default::default()
        };
        let msgs = wire_messages(&req);
        assert_eq!(msgs.len(), 2);
        assert!(assistant_tool_use_ids(&msgs[1]).is_empty());
        assert!(user_tool_result_ids(&msgs[0]).is_empty());
    }

    /// No two consecutive wire messages may share a role (the Anthropic
    /// role-alternation requirement) — the general guard the multi-call wire
    /// coalescing must satisfy.
    fn assert_role_alternation(msgs: &[Message]) {
        for w in msgs.windows(2) {
            let same = matches!(
                (&w[0], &w[1]),
                (Message::User { .. }, Message::User { .. })
                    | (Message::Assistant { .. }, Message::Assistant { .. })
            );
            assert!(!same, "two consecutive same-role messages on the wire: {msgs:?}");
        }
    }

    // spec: repl/spec.md §17 — FIXME 0541 WIRE HALF: a single assistant turn
    // issuing N tool calls whose results are the trailing turns must lower to
    // EXACTLY ONE trailing user message carrying all N `tool_result` blocks in
    // order (the Anthropic grouping rule), with role alternation. rig's Anthropic
    // provider maps rig Messages 1:1 (no coalescing), so WITHOUT the membrane
    // coalescing this lowered to N consecutive `user` messages → a live wire 400
    // (the panic's twin). Pre-fix: msgs.len()==5, two consecutive users; post-fix:
    // msgs.len()==3, one coalesced trailing user message.
    #[test]
    fn multi_tool_call_results_coalesce_into_one_trailing_user_message() {
        let req = AgentRequest {
            transcript: vec![
                Turn::User("show me f three times".to_string()),
                Turn::AssistantToolCalls(vec![
                    tool_call("toolu_a", "source", "f"),
                    tool_call("toolu_b", "source", "f"),
                    tool_call("toolu_c", "source", "f"),
                ]),
                Turn::ToolResult(tool_result("toolu_a", "/source f", "body-a")),
                Turn::ToolResult(tool_result("toolu_b", "/source f", "body-b")),
                Turn::ToolResult(tool_result("toolu_c", "/source f", "body-c")),
            ],
            ..Default::default()
        };

        let msgs = wire_messages(&req);
        // user(question), assistant(tool_use a,b,c), user(tool_result a,b,c) —
        // THREE messages, NOT five (one-user-per-result).
        assert_eq!(
            msgs.len(),
            3,
            "the 3 tool_results must coalesce into ONE user message (wire = user, \
             assistant, user), got {} messages: {msgs:?}",
            msgs.len()
        );
        assert!(matches!(msgs[0], Message::User { .. }), "msg[0] is the user question");
        assert!(matches!(msgs[1], Message::Assistant { .. }), "msg[1] is the assistant tool_use");
        assert!(
            matches!(msgs[2], Message::User { .. }),
            "msg[2] is the ONE coalesced tool_result user message"
        );
        // All THREE tool_result ids present, IN ORDER, in the single user message.
        assert_eq!(
            user_tool_result_ids(&msgs[2]),
            vec!["toolu_a".to_string(), "toolu_b".to_string(), "toolu_c".to_string()],
            "the coalesced user message must carry all 3 tool_result ids in order"
        );
        // Each block's output content is preserved.
        let text = user_tool_result_text(&msgs[2]);
        assert!(
            text.contains("body-a") && text.contains("body-b") && text.contains("body-c"),
            "all three tool_result outputs must be present in the coalesced message: {text}"
        );
        assert_role_alternation(&msgs);
    }

    // spec: repl/spec.md §17 — FIXME 0541 WIRE HALF, run-in-history variant: when
    // the multi-`tool_result` run is followed by a later turn (assistant prose),
    // it lands in HISTORY (not the prompt slot). It must STILL coalesce to one
    // user message and role-alternate — the boundary-split must not re-introduce
    // two consecutive users. Pre-fix: user, assistant, user(a), user(b),
    // assistant (5, two consecutive users); post-fix: user, assistant, user(a,b),
    // assistant (4).
    #[test]
    fn multi_tool_call_results_coalesce_when_run_is_in_history() {
        let req = AgentRequest {
            transcript: vec![
                Turn::User("two pulls".to_string()),
                Turn::AssistantToolCalls(vec![
                    tool_call("id-a", "source", "f"),
                    tool_call("id-b", "info", "g"),
                ]),
                Turn::ToolResult(tool_result("id-a", "/source f", "body-f")),
                Turn::ToolResult(tool_result("id-b", "/info g", "type-g")),
                Turn::Assistant("here is what I found".to_string()),
            ],
            ..Default::default()
        };
        let msgs = wire_messages(&req);
        assert_eq!(
            msgs.len(),
            4,
            "user, assistant(a,b), user(tr a,tr b coalesced), assistant — got {msgs:?}"
        );
        assert_eq!(
            user_tool_result_ids(&msgs[2]),
            vec!["id-a".to_string(), "id-b".to_string()],
            "the mid-history run must coalesce into one user message carrying both ids"
        );
        assert_role_alternation(&msgs);
    }
}
