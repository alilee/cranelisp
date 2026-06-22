// agent/stub.rs — the deterministic stub `AgentModel` (the testing linchpin,
// tests/plan/agent-testing-strategy.md §1; design/int/agent.md §11).
//
// Everything CI-testable about the agent rests on one structural fact: the agent
// loop drives an `AgentModel` (the object-safe membrane over rig's
// `CompletionModel`). The stub implements the SAME trait the rig-backed providers
// do, so the entire agent LOGIC — request assembly → harvest → pull → render →
// feed-back — runs with zero network, zero key, zero non-determinism.
//
// Two capabilities (strategy §1.1):
//   1. Scripted turn responses — an ordered script, one response consumed per
//      `complete()` call within a turn's model↔tool loop (`Done` / `ToolCalls`).
//   2. An assertable record of the requests received — every `AgentRequest` is
//      captured so a unit test can assert WHAT the agent sent (primer present,
//      harvest slice correct, transcript carried, tools = the allowlist, and
//      negatively that aged-out symbols are absent).
//
// Selected at runtime by `CRANELISP_AGENT_PROVIDER=stub` + a script-fixture path
// in `CRANELISP_AGENT_STUB_SCRIPT` (the §1.1(a) e2e mechanism). Unit tests build
// `StubModel` directly with an in-memory script + shared capture.

#![cfg(feature = "agent")]

use std::sync::{Arc, Mutex};

use crate::agent::types::{
    AgentModel, AgentRequest, ModelResponse, ToolCallRequest,
};

/// A deterministic stub model driven by an ordered script of responses.
///
/// `requests` is a shared, assertable log of every `AgentRequest` `complete()`
/// received (capability 2). `script` is consumed front-to-back; once exhausted,
/// `complete()` returns a terminal `Done` so the loop always ends.
pub struct StubModel {
    script: Vec<ModelResponse>,
    cursor: usize,
    /// Shared capture of received requests — a unit test holds the other `Arc`.
    pub requests: Arc<Mutex<Vec<AgentRequest>>>,
}

impl StubModel {
    /// Build a stub from an in-memory script (for `#[cfg(test)]` unit tests that
    /// assert request content). The returned `requests` handle is shared with the
    /// caller for assertion.
    pub fn new(script: Vec<ModelResponse>) -> Self {
        Self {
            script,
            cursor: 0,
            requests: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Build a stub from the `CRANELISP_AGENT_STUB_SCRIPT` fixture file (the e2e
    /// stub-provider-by-config path). The script format is a tiny line-based DSL:
    ///   - `done: <prose...>`           → a `Done(prose)` response (prose to EOL)
    ///   - `tool: <name> <argument>`    → a `ToolCalls([one])` response
    ///   - `prose: <text>`             → appended to the most recent `done:`/created `Done`
    ///
    /// Blank lines and `#`-comments are ignored. Each non-`prose:` line is one
    /// scripted turn response (consumed one per `complete()` call).
    pub fn from_env() -> Result<Self, String> {
        let path = std::env::var("CRANELISP_AGENT_STUB_SCRIPT")
            .map_err(|_| "no CRANELISP_AGENT_STUB_SCRIPT set".to_string())?;
        let text = std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read stub script '{path}': {e}"))?;
        Ok(Self::new(parse_script(&text)))
    }
}

/// Parse the line-based stub script DSL into an ordered list of responses.
pub fn parse_script(text: &str) -> Vec<ModelResponse> {
    let mut script: Vec<ModelResponse> = Vec::new();
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("done:") {
            script.push(ModelResponse::Done(rest.trim().to_string()));
        } else if let Some(rest) = line.strip_prefix("prose:") {
            // Append to the previous Done, or start one.
            match script.last_mut() {
                Some(ModelResponse::Done(p)) => {
                    if !p.is_empty() {
                        p.push('\n');
                    }
                    p.push_str(rest.trim());
                }
                _ => script.push(ModelResponse::Done(rest.trim().to_string())),
            }
        } else if let Some(rest) = line.strip_prefix("tool:") {
            let mut parts = rest.trim().splitn(2, char::is_whitespace);
            let name = parts.next().unwrap_or("").trim().to_string();
            let argument = parts.next().unwrap_or("").trim().to_string();
            script.push(ModelResponse::ToolCalls(vec![ToolCallRequest {
                id: format!("stub-{}", script.len()),
                name,
                argument,
            }]));
        }
        // unknown lines are ignored (forward-compatible)
    }
    script
}

impl AgentModel for StubModel {
    fn complete(&mut self, request: &AgentRequest) -> Result<ModelResponse, String> {
        // Capability 2: record the request for assertion.
        if let Ok(mut log) = self.requests.lock() {
            log.push(request.clone());
        }
        // Capability 1: return the next scripted response; terminal `Done` once
        // the script is exhausted (the loop always ends).
        let resp = self
            .script
            .get(self.cursor)
            .cloned()
            .unwrap_or_else(|| ModelResponse::Done(String::new()));
        self.cursor += 1;
        Ok(resp)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_done_and_tool_lines() {
        let script = parse_script(
            "# a comment\n\
             tool: source foo\n\
             done: here is the answer\n",
        );
        assert_eq!(script.len(), 2);
        match &script[0] {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "source");
                assert_eq!(calls[0].argument, "foo");
            }
            other => panic!("expected ToolCalls, got {other:?}"),
        }
        assert_eq!(script[1], ModelResponse::Done("here is the answer".to_string()));
    }

    // S89 Cluster B: `tool: submit <FORM>` parses with the WHOLE rest-of-line
    // (the form, verbatim, including its inner spaces) as the single argument —
    // the broken-then-fixed DSL contract (tests/agent.rs). Two consecutive
    // `tool: submit` lines parse as two ordered ToolCalls (the repair sequence).
    #[test]
    fn parses_submit_tool_with_form_argument() {
        let script = parse_script(
            "tool: submit (defn double [x] (add-i64 x x)\n\
             tool: submit (defn double [x] (add-i64 x x))\n\
             done: defined double for you\n",
        );
        assert_eq!(script.len(), 3);
        match &script[0] {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "submit");
                // The whole form (with its spaces) is the argument; line 1 is the
                // BROKEN form (missing its closing paren).
                assert_eq!(calls[0].argument, "(defn double [x] (add-i64 x x)");
            }
            other => panic!("expected ToolCalls(submit), got {other:?}"),
        }
        match &script[1] {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "submit");
                // Line 2 is the CLEAN repaired form.
                assert_eq!(calls[0].argument, "(defn double [x] (add-i64 x x))");
            }
            other => panic!("expected ToolCalls(submit), got {other:?}"),
        }
        assert_eq!(script[2], ModelResponse::Done("defined double for you".to_string()));
    }

    // S89 Cluster C: `tool: set-preamble <MODULE> <TEXT>` parses with the FIRST
    // token as the target and the REST of the line (verbatim, including inner
    // spaces) as the text — the same `tool:` grammar as `submit` (the argument is
    // `<TARGET> <TEXT>`, re-split in `run_document_edit`). No new keyword:
    // `set-preamble` is a tool NAME (the §17.2 discriminator). (`set-doc` descoped
    // — FIXME 0430.)
    #[test]
    fn parses_set_preamble_tool() {
        let script = parse_script(
            "tool: set-preamble user Solver core: constraint propagation over a grid.\n\
             done: recorded\n",
        );
        assert_eq!(script.len(), 2);
        match &script[0] {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "set-preamble");
                // The whole `<MODULE> <TEXT>` is the argument (split later).
                assert_eq!(
                    calls[0].argument,
                    "user Solver core: constraint propagation over a grid."
                );
            }
            other => panic!("expected ToolCalls(set-preamble), got {other:?}"),
        }
    }

    #[test]
    fn complete_consumes_script_then_terminates() {
        let mut stub = StubModel::new(vec![ModelResponse::Done("ok".to_string())]);
        let req = AgentRequest::default();
        assert_eq!(stub.complete(&req).unwrap(), ModelResponse::Done("ok".to_string()));
        // Exhausted → terminal empty Done.
        assert_eq!(stub.complete(&req).unwrap(), ModelResponse::Done(String::new()));
        // Two requests captured.
        assert_eq!(stub.requests.lock().unwrap().len(), 2);
    }
}
