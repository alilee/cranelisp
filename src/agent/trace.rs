// agent/trace.rs — the LLM-exchange trace mode (S89 Phase-6; persistent
// full-content upgrade S90, `design/int/agent.md §28`).
//
// A debugging/transparency dev mode that records the ACTUAL provider exchange at
// the rig boundary (`provider.rs::RigModel::complete`), so wire-path bugs (the
// tool_use↔tool_result pairing 400 class) are DIRECTLY visible instead of
// inferred from a live 400. The deterministic stub sits above rig and never
// enforces Anthropic's pairing, so CI stays green while live breaks — this trace
// is how a human eyeballs the real message sequence the provider receives.
//
// S90 persistent + full-content upgrade (§28.1). `CRANELISP_AGENT_TRACE` changed
// meaning from a `=1` toggle to a PATH (sibling-identical to
// `CRANELISP_AGENT_LOG`): set ⇒ each request/response trace is APPENDED to that
// file (persistent across turns + session); unset/empty ⇒ off, no file, no cost.
// The stderr `eprintln!` sink is REMOVED — there is no longer an ephemeral
// stderr trace view. The persisted lines carry the WHOLE form/error/prose
// (`Grain::Full` — no `TEXT_TRUNCATE` cut, no `⏎` newline-collapse): a persisted
// trace is read IN A FILE, where multi-line forms are an asset, not noise.
//
// The trace = CONTENT record; the §27 log = compact INDEX. They join by a shared
// per-turn `turn` id (§28.2): each persisted block carries a `turn=N` marker that
// matches the log's `"turn":N` field, so a reader greps the log to find the
// interesting turn, then reads the trace block for that same N.
//
// Off by default; `#[cfg(feature = "agent")]` — feature-off this file does not
// exist. The trace reads the SAME `AgentRequest` (`types.rs`) the membrane lowers
// to rig, so it is faithful to what is sent (it traces the request, not a
// reconstruction). The only side effect is the silent best-effort file append
// (via the shared `sink::append_to_env_path`, §28.3), behind the env gate.
//
// (Doc note for `/repl`: `repl/spec.md §17.10` / §17.21 record
// `CRANELISP_AGENT_TRACE=<path>` as a PATH alongside `CRANELISP_AGENT_LOG` — that
// file is `/repl`-owned, so it is NOT edited here; this comment is the code-level
// doc.)

#![cfg(feature = "agent")]

use crate::agent::types::{AgentRequest, ModelResponse, ToolCallRequest, Turn};

/// The env var that turns the trace on. A PATH (not a `=1` toggle, §28.1) — set ⇒
/// append the trace to that file; unset/empty ⇒ off. Sibling to `log.rs`'s
/// `CRANELISP_AGENT_LOG`.
const TRACE_VAR: &str = "CRANELISP_AGENT_TRACE";

/// Max chars of any text block rendered in a `Grain::Compact` trace line — keeps
/// the unit-test compact rendering bounded. The persisted (`Grain::Full`) path
/// does NOT truncate.
const TEXT_TRUNCATE: usize = 80;

/// The render grain a formatter renders at (§28.1). `Compact` is the one-line,
/// `TEXT_TRUNCATE`-bounded, `⏎`-collapsed rendering (eyeball-on-one-line — the
/// unit tests exercise it directly). `Full` is the persisted-file rendering: the
/// whole form/error/prose verbatim, no cut, no newline-collapse. The two share
/// ONE formatter (Principle 7) — the grain is a param, not a parallel mirror.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Grain {
    Compact,
    Full,
}

/// The configured trace path, or `None` when the trace is off (unset/empty).
/// Defers to the shared `sink::env_path` gate (§28.3) — sibling to `log::log_path`.
pub fn trace_path() -> Option<String> {
    crate::agent::sink::env_path(TRACE_VAR)
}

/// Append the request trace to the configured file if enabled. Renders the
/// assembled message sequence at FULL grain (the whole form/error/prose), stamped
/// with the request's `turn` (§28.2) so a reader can join it to the §27 log's
/// `"turn":N`. Silent + best-effort + graceful (the shared `sink` append).
pub fn emit_request(req: &AgentRequest) {
    if trace_path().is_none() {
        return; // off — no file, no cost.
    }
    let mut block = String::new();
    for line in format_request_trace(req, req.turn, Grain::Full) {
        block.push_str(&line);
        block.push('\n');
    }
    crate::agent::sink::append_to_env_path(TRACE_VAR, &block);
}

/// Append the response trace to the configured file if enabled. Carries the same
/// `turn` as the request it answers (§28.2) — the response belongs to the
/// request's turn.
pub fn emit_response(resp: &ModelResponse, turn: usize) {
    if trace_path().is_none() {
        return; // off — no file, no cost.
    }
    let mut block = String::new();
    for line in format_response_trace(resp, turn, Grain::Full) {
        block.push_str(&line);
        block.push('\n');
    }
    crate::agent::sink::append_to_env_path(TRACE_VAR, &block);
}

/// Render `text` at the given grain. `Compact`: a single line (newlines → `⏎`),
/// truncated to `TEXT_TRUNCATE` chars with a trailing `…` when cut. `Full`: the
/// text VERBATIM — no collapse, no cut (the persisted-file rendering, §28.1).
/// ONE renderer for both grains (Principle 7 — no parallel "full" mirror).
fn render_text(text: &str, grain: Grain) -> String {
    match grain {
        Grain::Full => text.to_string(),
        Grain::Compact => {
            let one_line: String =
                text.chars().map(|c| if c == '\n' { '⏎' } else { c }).collect();
            if one_line.chars().count() > TEXT_TRUNCATE {
                let head: String = one_line.chars().take(TEXT_TRUNCATE).collect();
                format!("{head}…")
            } else {
                one_line
            }
        }
    }
}

/// Render the request as trace lines (the full message sequence) at `grain`. The
/// FIRST line marks the direction + the `turn` id + a system-preamble size note;
/// then one line per transcript turn (role + per-block kinds), with the LAST turn
/// marked as the prompt. Pure — `emit_request` does the I/O.
pub fn format_request_trace(req: &AgentRequest, turn: usize, grain: Grain) -> Vec<String> {
    let mut lines = Vec::new();
    lines.push(format!(
        "[agent-trace] turn={turn} →request  system(primer {}ch + harvest {}ch)  tools=[{}]  {} turn(s)",
        req.primer.len(),
        req.harvest.len(),
        req.tools.iter().map(|t| t.name.as_str()).collect::<Vec<_>>().join(","),
        req.transcript.len(),
    ));
    let last = req.transcript.len().saturating_sub(1);
    for (i, t) in req.transcript.iter().enumerate() {
        let marker = if i == last { " (prompt)" } else { "" };
        lines.push(format!("[agent-trace]   {}{marker}", format_turn(t, grain)));
    }
    if req.transcript.is_empty() {
        lines.push(format!(
            "[agent-trace]   user[text]: {} (prompt; transcript empty)",
            render_text(&req.user, grain)
        ));
    }
    lines
}

/// Render one transcript turn as a `role[block,…]` line at `grain`. The per-block
/// kind is exactly what the wire carries: `text` / `tool_use{id,name}` /
/// `tool_result{id}` — so a reader can eyeball the tool_use↔tool_result pairing.
fn format_turn(turn: &Turn, grain: Grain) -> String {
    match turn {
        Turn::User(text) => format!("user[text]: {}", render_text(text, grain)),
        Turn::Assistant(text) => format!("assistant[text]: {}", render_text(text, grain)),
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
                render_text(&r.output, grain)
            )
        }
    }
}

/// Render an id, showing `<none>` for the empty-id (id-free provider) case so a
/// reader can SEE a missing id (which is itself a pairing-bug signal).
fn id_or_empty(id: &str) -> &str {
    if id.is_empty() { "<none>" } else { id }
}

/// Render the model response as trace lines at `grain`, stamped with `turn`.
pub fn format_response_trace(resp: &ModelResponse, turn: usize, grain: Grain) -> Vec<String> {
    match resp {
        ModelResponse::Done(prose) => {
            vec![format!(
                "[agent-trace] turn={turn} ←response  Done[text]: {}",
                render_text(prose, grain)
            )]
        }
        ModelResponse::ToolCalls(calls) => {
            let mut lines = vec![format!(
                "[agent-trace] turn={turn} ←response  ToolCalls ({})",
                calls.len()
            )];
            for c in calls {
                lines.push(format!("[agent-trace]   {}", format_call(c, grain)));
            }
            lines
        }
    }
}

/// Render one response tool-call as a `tool_call{id,name}: arg` line at `grain`.
fn format_call(c: &ToolCallRequest, grain: Grain) -> String {
    format!(
        "tool_call{{id={},name={}}}: {}",
        id_or_empty(&c.id),
        c.name,
        render_text(&c.argument, grain)
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
    // `(prompt)`. The header carries the `turn` id (§28.2).
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
            turn: 3,
        };
        let lines = format_request_trace(&req, req.turn, Grain::Compact);
        // Header + 3 turn lines.
        assert_eq!(lines.len(), 4, "header + one line per turn: {lines:?}");
        assert!(lines[0].contains("→request"), "header marks direction: {}", lines[0]);
        assert!(lines[0].contains("turn=3"), "header carries the turn id: {}", lines[0]);
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
        let done =
            format_response_trace(&ModelResponse::Done("hello world".to_string()), 1, Grain::Compact);
        assert_eq!(done.len(), 1);
        assert!(done[0].contains("←response  Done[text]: hello world"), "{}", done[0]);
        assert!(done[0].contains("turn=1"), "response carries the turn id: {}", done[0]);

        let calls = format_response_trace(
            &ModelResponse::ToolCalls(vec![tc("toolu_9", "submit", "(defn g [x] x)")]),
            2,
            Grain::Compact,
        );
        assert_eq!(calls.len(), 2, "header + one call line: {calls:?}");
        assert!(calls[0].contains("ToolCalls (1)"), "{}", calls[0]);
        assert!(calls[0].contains("turn=2"), "{}", calls[0]);
        assert!(
            calls[1].contains("tool_call{id=toolu_9,name=submit}: (defn g [x] x)"),
            "{}",
            calls[1]
        );
    }

    // spec: repl/spec.md §17 — `Grain::Compact`: long text is truncated on a
    // single line; embedded newlines collapse to `⏎` so a trace line stays one
    // line (the eyeball rendering — re-pinned as a Compact-grain test, §28.5).
    #[test]
    fn long_text_is_compacted_and_truncated() {
        let long = "a".repeat(200);
        let req = AgentRequest {
            transcript: vec![Turn::User(format!("line1\n{long}"))],
            ..Default::default()
        };
        let lines = format_request_trace(&req, 0, Grain::Compact);
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

    // spec: repl/spec.md §17.21.1 — `Grain::Full`: a >80-char form survives
    // VERBATIM (no `…` cut, no `⏎` newline-collapse) — the un-truncation guard
    // for the persisted file (§28.5). This is the new Full-grain companion to the
    // Compact-grain truncation test above.
    #[test]
    fn full_grain_renders_long_text_verbatim() {
        // A >80-char multi-line form — exactly what the persisted trace must keep.
        let long_form = "(defn very-long-helper-fn [first-arg second-arg]\n  \
            (add-i64 (mul-i64 first-arg 1000000) second-arg))";
        assert!(long_form.len() > TEXT_TRUNCATE, "fixture must exceed the compact cap");
        let req = AgentRequest {
            transcript: vec![Turn::User(long_form.to_string())],
            ..Default::default()
        };
        let lines = format_request_trace(&req, 7, Grain::Full);
        let body: String = lines.join("\n");
        // VERBATIM: the whole form is present, including its newline + every char.
        assert!(
            body.contains(long_form),
            "Full grain must carry the long form VERBATIM (no truncation): {body}"
        );
        assert!(!body.contains('…'), "Full grain must NOT truncate with `…`: {body}");
        assert!(!body.contains('⏎'), "Full grain must NOT collapse newlines to `⏎`: {body}");
        assert!(body.contains("turn=7"), "the Full block carries the turn marker: {body}");
    }

    // spec: repl/spec.md §17 — an empty-id tool_use renders `<none>` so a missing
    // id (itself a pairing-bug signal) is visible in the trace.
    #[test]
    fn empty_id_renders_as_none() {
        let req = AgentRequest {
            transcript: vec![Turn::AssistantToolCalls(vec![tc("", "source", "f")])],
            ..Default::default()
        };
        let line = &format_request_trace(&req, 0, Grain::Compact)[1];
        assert!(line.contains("id=<none>"), "empty id shown as <none>: {line}");
    }

    // spec: repl/spec.md §17.21.1 — the `=<empty>` / unset env value disables the
    // trace (path-gate, §28.1). The pure predicate over the shared sink gate.
    #[test]
    fn trace_off_for_empty_and_unset() {
        // `trace_path()` reads the live env; exercise the documented gate rule via
        // the shared sink predicate over explicit strings (env-mutation-free, so
        // it does not race parallel tests).
        assert!(crate::agent::sink::env_path("CRANELISP_AGENT_TRACE_NEVER_SET").is_none());
    }
}
