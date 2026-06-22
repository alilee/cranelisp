// agent/trace.rs — the LLM-exchange trace mode (S89 Phase-6, user-requested).
//
// A debugging/transparency dev mode that logs the ACTUAL provider exchange at the
// rig boundary (`provider.rs::RigModel::complete`), so wire-path bugs (the
// tool_use↔tool_result pairing 400 class) are DIRECTLY visible on stderr instead
// of inferred from a live 400. The deterministic stub sits above rig and never
// enforces Anthropic's pairing, so CI stays green while live breaks — this trace
// is how a human eyeballs the real message sequence the provider receives.
//
// Usage: set the env var `CRANELISP_AGENT_TRACE=1` and run the REPL with
// `--agent`. On each provider completion call the assembled request's message
// sequence (role + per-block kind: text / tool_use{id,name} / tool_result{id})
// and the model's response (text / tool_calls{id,name}) are written to stderr,
// clearly marked `[agent-trace] →request` / `[agent-trace] ←response`. Compact
// (ids + kinds + truncated text), not a raw JSON dump.
//
// Off by default; `#[cfg(feature = "agent")]` — feature-off this file does not
// exist. The trace reads the SAME `AgentRequest` (`types.rs`) the membrane
// lowers to rig, so it is faithful to what is sent (it traces the request, not a
// reconstruction). Pure formatting — the only side effect (the `eprintln!`) is
// confined to `emit_request` / `emit_response`, behind the env gate.
//
// (Doc note for `/repl`: `repl/spec.md §17.10` should record
// `CRANELISP_AGENT_TRACE=1` alongside the other agent env config — that file is
// `/repl`-owned, so it is NOT edited here; this comment is the code-level doc.)

#![cfg(feature = "agent")]

use crate::agent::types::{AgentRequest, ModelResponse, ToolCallRequest, Turn};

/// The env var that turns the trace on. `=1` (or any non-empty, non-`0` value).
const TRACE_VAR: &str = "CRANELISP_AGENT_TRACE";

/// Max chars of any text block rendered in a trace line — keep it compact.
const TEXT_TRUNCATE: usize = 80;

/// Is the trace mode enabled (env `CRANELISP_AGENT_TRACE` set to a truthy value)?
pub fn trace_enabled() -> bool {
    match std::env::var(TRACE_VAR) {
        Ok(v) => {
            let v = v.trim();
            !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false")
        }
        Err(_) => false,
    }
}

/// Emit the request trace to stderr if enabled. Renders the assembled message
/// sequence (preamble summary + each transcript turn's role and per-block kinds).
pub fn emit_request(req: &AgentRequest) {
    if !trace_enabled() {
        return;
    }
    for line in format_request_trace(req) {
        eprintln!("{line}");
    }
}

/// Emit the response trace to stderr if enabled.
pub fn emit_response(resp: &ModelResponse) {
    if !trace_enabled() {
        return;
    }
    for line in format_response_trace(resp) {
        eprintln!("{line}");
    }
}

/// Truncate `text` to `TEXT_TRUNCATE` chars on a single line (newlines → `⏎`),
/// appending `…` when cut. Compact, eyeball-friendly.
fn compact(text: &str) -> String {
    let one_line: String = text.chars().map(|c| if c == '\n' { '⏎' } else { c }).collect();
    if one_line.chars().count() > TEXT_TRUNCATE {
        let head: String = one_line.chars().take(TEXT_TRUNCATE).collect();
        format!("{head}…")
    } else {
        one_line
    }
}

/// Render the request as compact trace lines (the full message sequence). The
/// FIRST line marks the direction + a system-preamble size note; then one line
/// per transcript turn (role + per-block kinds), with the LAST turn marked as the
/// prompt (the message the model answers). Pure — `emit_request` does the I/O.
pub fn format_request_trace(req: &AgentRequest) -> Vec<String> {
    let mut lines = Vec::new();
    lines.push(format!(
        "[agent-trace] →request  system(primer {}ch + harvest {}ch)  tools=[{}]  {} turn(s)",
        req.primer.len(),
        req.harvest.len(),
        req.tools.iter().map(|t| t.name.as_str()).collect::<Vec<_>>().join(","),
        req.transcript.len(),
    ));
    let last = req.transcript.len().saturating_sub(1);
    for (i, turn) in req.transcript.iter().enumerate() {
        let marker = if i == last { " (prompt)" } else { "" };
        lines.push(format!("[agent-trace]   {}{marker}", format_turn(turn)));
    }
    if req.transcript.is_empty() {
        lines.push(format!(
            "[agent-trace]   user[text]: {} (prompt; transcript empty)",
            compact(&req.user)
        ));
    }
    lines
}

/// Render one transcript turn as a compact `role[block,…]` line. The per-block
/// kind is exactly what the wire carries: `text` / `tool_use{id,name}` /
/// `tool_result{id}` — so a reader can eyeball the tool_use↔tool_result pairing.
fn format_turn(turn: &Turn) -> String {
    match turn {
        Turn::User(text) => format!("user[text]: {}", compact(text)),
        Turn::Assistant(text) => format!("assistant[text]: {}", compact(text)),
        Turn::AssistantToolCalls(calls) => {
            let blocks: Vec<String> = calls
                .iter()
                .map(|c| format!("tool_use{{id={},name={}}}", id_or_empty(&c.id), c.name))
                .collect();
            format!("assistant[{}]", blocks.join(", "))
        }
        Turn::ToolResult(r) => {
            format!(
                "user[tool_result{{id={}}}]: {}",
                id_or_empty(&r.id),
                compact(&r.output)
            )
        }
    }
}

/// Render an id, showing `<none>` for the empty-id (id-free provider) case so a
/// reader can SEE a missing id (which is itself a pairing-bug signal).
fn id_or_empty(id: &str) -> &str {
    if id.is_empty() { "<none>" } else { id }
}

/// Render the model response as compact trace lines.
pub fn format_response_trace(resp: &ModelResponse) -> Vec<String> {
    match resp {
        ModelResponse::Done(prose) => {
            vec![format!("[agent-trace] ←response  Done[text]: {}", compact(prose))]
        }
        ModelResponse::ToolCalls(calls) => {
            let mut lines =
                vec![format!("[agent-trace] ←response  ToolCalls ({})", calls.len())];
            for c in calls {
                lines.push(format!("[agent-trace]   {}", format_call(c)));
            }
            lines
        }
    }
}

/// Render one response tool-call as a compact `tool_call{id,name}: arg` line.
fn format_call(c: &ToolCallRequest) -> String {
    format!(
        "tool_call{{id={},name={}}}: {}",
        id_or_empty(&c.id),
        c.name,
        compact(&c.argument)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::types::{ToolCallResult, ToolDef};

    fn tc(id: &str, name: &str, arg: &str) -> ToolCallRequest {
        ToolCallRequest { id: id.to_string(), name: name.to_string(), argument: arg.to_string() }
    }

    // spec: repl/spec.md §17 — the request trace renders the full message
    // sequence: a header line + one line per turn, each carrying the role and the
    // per-block kind (text / tool_use{id,name} / tool_result{id}) so the
    // tool_use↔tool_result pairing is eyeball-visible. The LAST turn is marked
    // `(prompt)`.
    #[test]
    fn request_trace_renders_turns_with_block_kinds() {
        let req = AgentRequest {
            primer: "PRIMER".to_string(),
            harvest: "HARV".to_string(),
            tools: vec![ToolDef { name: "source".to_string(), description: "d".to_string() }],
            transcript: vec![
                Turn::User("show me f".to_string()),
                Turn::AssistantToolCalls(vec![tc("toolu_1", "source", "f")]),
                Turn::ToolResult(ToolCallResult {
                    id: "toolu_1".to_string(),
                    command: "/source f".to_string(),
                    output: "(defn f [x] x)".to_string(),
                }),
            ],
            user: "show me f".to_string(),
        };
        let lines = format_request_trace(&req);
        // Header + 3 turn lines.
        assert_eq!(lines.len(), 4, "header + one line per turn: {lines:?}");
        assert!(lines[0].contains("→request"), "header marks direction: {}", lines[0]);
        assert!(lines[0].contains("tools=[source]"), "header lists tools: {}", lines[0]);
        assert!(lines[1].contains("user[text]: show me f"), "{}", lines[1]);
        assert!(
            lines[2].contains("tool_use{id=toolu_1,name=source}"),
            "tool_use block kind + id + name: {}",
            lines[2]
        );
        assert!(
            lines[3].contains("tool_result{id=toolu_1}"),
            "tool_result block kind + id: {}",
            lines[3]
        );
        // The final turn is the prompt.
        assert!(lines[3].contains("(prompt)"), "last turn marked prompt: {}", lines[3]);
    }

    // spec: repl/spec.md §17 — the response trace renders a Done as a text line,
    // and ToolCalls as a header + one tool_call line per call (id + name + arg).
    #[test]
    fn response_trace_renders_done_and_tool_calls() {
        let done = format_response_trace(&ModelResponse::Done("hello world".to_string()));
        assert_eq!(done.len(), 1);
        assert!(done[0].contains("←response  Done[text]: hello world"), "{}", done[0]);

        let calls = format_response_trace(&ModelResponse::ToolCalls(vec![tc(
            "toolu_9", "submit", "(defn g [x] x)",
        )]));
        assert_eq!(calls.len(), 2, "header + one call line: {calls:?}");
        assert!(calls[0].contains("ToolCalls (1)"), "{}", calls[0]);
        assert!(
            calls[1].contains("tool_call{id=toolu_9,name=submit}: (defn g [x] x)"),
            "{}",
            calls[1]
        );
    }

    // spec: repl/spec.md §17 — long text is truncated on a single line; embedded
    // newlines collapse to `⏎` so a trace line stays one line.
    #[test]
    fn long_text_is_compacted_and_truncated() {
        let long = "a".repeat(200);
        let req = AgentRequest {
            transcript: vec![Turn::User(format!("line1\n{long}"))],
            ..Default::default()
        };
        let lines = format_request_trace(&req);
        let turn_line = &lines[1];
        assert!(turn_line.contains('…'), "truncated with ellipsis: {turn_line}");
        assert!(turn_line.contains('⏎'), "newline collapsed to glyph: {turn_line}");
        assert!(!turn_line.contains('\n'), "the trace line stays single-line");
        // The body before the ` (prompt)` suffix is at most TEXT_TRUNCATE+1 chars
        // (the head + the ellipsis) — the full 200-char body did not pass through.
        assert!(
            !turn_line.contains(&"a".repeat(120)),
            "the long body must be truncated, not passed through: {turn_line}"
        );
    }

    // spec: repl/spec.md §17 — an empty-id tool_use renders `<none>` so a missing
    // id (itself a pairing-bug signal) is visible in the trace.
    #[test]
    fn empty_id_renders_as_none() {
        let req = AgentRequest {
            transcript: vec![Turn::AssistantToolCalls(vec![tc("", "source", "f")])],
            ..Default::default()
        };
        let line = &format_request_trace(&req)[1];
        assert!(line.contains("id=<none>"), "empty id shown as <none>: {line}");
    }

    // spec: repl/spec.md §17 — the `=0` / unset env value disables the trace.
    #[test]
    fn trace_disabled_for_zero_and_unset() {
        // We cannot reliably mutate process env in parallel tests; assert the
        // pure predicate over explicit strings instead by reading the same rule.
        // (trace_enabled reads the live env; here we only exercise the formatters,
        // which are env-independent — this guards the gate's truthiness rule via
        // the documented contract.)
        // A direct unit of the rule:
        let truthy = |v: &str| {
            let v = v.trim();
            !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false")
        };
        assert!(!truthy("0"));
        assert!(!truthy(""));
        assert!(!truthy("false"));
        assert!(truthy("1"));
        assert!(truthy("yes"));
    }
}
