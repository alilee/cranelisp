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

use crate::agent::types::{AgentModel, AgentRequest, ModelResponse, ToolCallRequest};

/// The streaming-delta split marker for the stub script DSL (S107, FIXME 0555 —
/// unblocks harness gap G-1 for `/qa`). A `done:`/`prose:` fixture may embed one
/// or more `<|delta|>` markers to script MULTIPLE streaming deltas within a single
/// terminal turn — including a boundary that falls INSIDE a ```lisp fence. The
/// markers are STRIPPED from the emitted `Done` prose (so the final answer text is
/// unchanged) and the segments between them become the ordered streaming deltas
/// (their concatenation == the marker-stripped prose). Absent any marker a `Done`
/// streams as a single delta (the default one-delta path). Example fixture:
///
/// ```text
/// done: Here is a definition:<|delta|>
/// prose: ```lisp<|delta|>
/// prose: (defn double [x]<|delta|> (add-i64 x x))
/// prose: ```
/// ```
///
/// scripts four deltas, one boundary landing mid-fence-body — exactly what the
/// streaming e2e needs to exercise buffer-within-fence + line-granular prose.
pub const DELTA_SPLIT: &str = "<|delta|>";

/// One scripted turn response + its optional streaming deltas (S107). `deltas` is
/// `Some(chunks)` only for a `Done` step whose fixture carried `<|delta|>` markers
/// (their concatenation == the `Done` prose); `None` ⇒ default one-delta streaming.
pub struct ScriptStep {
    pub response: ModelResponse,
    pub deltas: Option<Vec<String>>,
}

/// A deterministic stub model driven by an ordered script of responses.
///
/// `requests` is a shared, assertable log of every `AgentRequest` a `complete` /
/// `complete_streaming` call received (capability 2). `script` is consumed
/// front-to-back; once exhausted, a terminal `Done` is returned so the loop always
/// ends. `deltas` is parallel to `script`: for a `Done` step it optionally scripts
/// the streaming deltas (S107, the `<|delta|>` DSL).
pub struct StubModel {
    script: Vec<ModelResponse>,
    /// Parallel to `script`: `Some(chunks)` scripts a `Done` step's streaming
    /// deltas; `None` ⇒ that step streams as one delta (the whole prose).
    deltas: Vec<Option<Vec<String>>>,
    cursor: usize,
    /// Shared capture of received requests — a unit test holds the other `Arc`.
    pub requests: Arc<Mutex<Vec<AgentRequest>>>,
}

impl StubModel {
    /// Build a stub from an in-memory script (for `#[cfg(test)]` unit tests that
    /// assert request content). Each step streams as one delta (no scripted delta
    /// boundaries). The returned `requests` handle is shared with the caller.
    pub fn new(script: Vec<ModelResponse>) -> Self {
        let deltas = vec![None; script.len()];
        Self {
            script,
            deltas,
            cursor: 0,
            requests: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Build a stub from parsed `ScriptStep`s (the delta-aware path, used by
    /// `from_env`). Splits the steps into the parallel `script` + `deltas` arrays.
    pub fn from_steps(steps: Vec<ScriptStep>) -> Self {
        let mut script = Vec::with_capacity(steps.len());
        let mut deltas = Vec::with_capacity(steps.len());
        for s in steps {
            script.push(s.response);
            deltas.push(s.deltas);
        }
        Self {
            script,
            deltas,
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
    /// A `done:`/`prose:` line MAY embed `<|delta|>` (`DELTA_SPLIT`) markers to
    /// script multiple STREAMING deltas within the terminal turn (S107) — see
    /// `DELTA_SPLIT`. Blank lines and `#`-comments are ignored. Each non-`prose:`
    /// line is one scripted turn response (consumed one per model call).
    pub fn from_env() -> Result<Self, String> {
        let path = std::env::var("CRANELISP_AGENT_STUB_SCRIPT")
            .map_err(|_| "no CRANELISP_AGENT_STUB_SCRIPT set".to_string())?;
        let text = std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read stub script '{path}': {e}"))?;
        Ok(Self::from_steps(parse_script(&text)))
    }

    /// The next scripted step's response + its optional deltas, advancing the
    /// cursor. Shared by `complete` and `complete_streaming` so they consume the
    /// script identically (the terminal `Done` once exhausted).
    fn next_step(&mut self) -> (ModelResponse, Option<Vec<String>>) {
        let idx = self.cursor;
        let resp = self
            .script
            .get(idx)
            .cloned()
            .unwrap_or_else(|| ModelResponse::Done(String::new()));
        let deltas = self.deltas.get(idx).cloned().flatten();
        self.cursor += 1;
        (resp, deltas)
    }
}

/// Parse the line-based stub script DSL into an ordered list of `ScriptStep`s.
/// A `Done` step whose accumulated prose carries `<|delta|>` markers is split into
/// streaming deltas (the markers stripped from the emitted prose — S107).
pub fn parse_script(text: &str) -> Vec<ScriptStep> {
    let mut steps: Vec<ScriptStep> = Vec::new();
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("done:") {
            steps.push(ScriptStep {
                response: ModelResponse::Done(rest.trim().to_string()),
                deltas: None,
            });
        } else if let Some(rest) = line.strip_prefix("prose:") {
            // Append to the previous Done, or start one.
            match steps.last_mut() {
                Some(ScriptStep {
                    response: ModelResponse::Done(p),
                    ..
                }) => {
                    if !p.is_empty() {
                        p.push('\n');
                    }
                    p.push_str(rest.trim());
                }
                _ => steps.push(ScriptStep {
                    response: ModelResponse::Done(rest.trim().to_string()),
                    deltas: None,
                }),
            }
        } else if let Some(rest) = line.strip_prefix("tool:") {
            let mut parts = rest.trim().splitn(2, char::is_whitespace);
            let name = parts.next().unwrap_or("").trim().to_string();
            let arg_and_q = parts.next().unwrap_or("").trim();
            // F1 (§17.20.3b): a probe carries a model-supplied `question`. The stub
            // (the test "model") supplies one via an optional ` ?? <question>`
            // suffix; absent ⇒ a derived default so a probe always carries one (the
            // schema requires it). A `submit` form never contains ` ?? `, so its
            // whole form stays the argument (the question is unused for submits).
            let (argument, question) = match arg_and_q.split_once(" ?? ") {
                Some((a, q)) => (a.trim().to_string(), q.trim().to_string()),
                None => (arg_and_q.to_string(), format!("what is {arg_and_q}")),
            };
            steps.push(ScriptStep {
                response: ModelResponse::ToolCalls(vec![ToolCallRequest {
                    id: format!("stub-{}", steps.len()),
                    name,
                    argument,
                    question: Some(question),
                }]),
                deltas: None,
            });
        }
        // unknown lines are ignored (forward-compatible)
    }
    // Post-process: a `Done` whose prose carries `<|delta|>` markers scripts its
    // streaming deltas (the segments between markers); the emitted prose is the
    // marker-stripped concatenation, so the FINAL answer text is unchanged.
    for step in steps.iter_mut() {
        if let ModelResponse::Done(prose) = &step.response
            && prose.contains(DELTA_SPLIT)
        {
            let chunks: Vec<String> = prose.split(DELTA_SPLIT).map(|s| s.to_string()).collect();
            let full = chunks.concat();
            step.deltas = Some(chunks);
            step.response = ModelResponse::Done(full);
        }
    }
    steps
}

impl AgentModel for StubModel {
    fn complete(&mut self, request: &AgentRequest) -> Result<ModelResponse, String> {
        // Capability 2: record the request for assertion.
        if let Ok(mut log) = self.requests.lock() {
            log.push(request.clone());
        }
        // Capability 1: return the next scripted response; terminal `Done` once
        // the script is exhausted (the loop always ends).
        let (resp, _deltas) = self.next_step();
        Ok(resp)
    }

    fn complete_streaming(
        &mut self,
        request: &AgentRequest,
        sink: &mut dyn FnMut(&str),
    ) -> Result<ModelResponse, String> {
        // Same capture/replay as `complete` (S107) — the agent loop drives THIS
        // path. A `Done` step streams its scripted deltas (or the whole prose as
        // one delta absent markers); a `ToolCalls` step streams nothing (tool-call
        // turns are not streamed this sprint).
        if let Ok(mut log) = self.requests.lock() {
            log.push(request.clone());
        }
        let (resp, deltas) = self.next_step();
        if let ModelResponse::Done(prose) = &resp {
            match &deltas {
                Some(chunks) => {
                    for c in chunks {
                        sink(c);
                    }
                }
                None => sink(prose),
            }
        }
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
        match &script[0].response {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "source");
                assert_eq!(calls[0].argument, "foo");
            }
            other => panic!("expected ToolCalls, got {other:?}"),
        }
        assert_eq!(
            script[1].response,
            ModelResponse::Done("here is the answer".to_string())
        );
        // No `<|delta|>` markers ⇒ default one-delta streaming (deltas None).
        assert!(script.iter().all(|s| s.deltas.is_none()));
    }

    // S107 (FIXME 0555) — the `<|delta|>` DSL scripts MULTIPLE streaming deltas
    // within one terminal turn, INCLUDING a boundary inside a ```lisp fence. The
    // emitted `Done` prose is the marker-stripped concatenation (the final answer
    // text is unchanged); the deltas concatenate to it. This unblocks /qa's
    // streaming e2e (harness gap G-1).
    #[test]
    fn parses_delta_split_markers_into_streaming_chunks() {
        let steps = parse_script(
            "done: Here is a definition:<|delta|>\n\
             prose: ```lisp<|delta|>\n\
             prose: (defn double [x]<|delta|> (add-i64 x x))\n\
             prose: ```\n",
        );
        assert_eq!(steps.len(), 1);
        // The emitted Done prose is the marker-stripped full text.
        let full = "Here is a definition:\n```lisp\n(defn double [x] (add-i64 x x))\n```";
        assert_eq!(steps[0].response, ModelResponse::Done(full.to_string()));
        // The deltas concatenate to the full text, with a boundary INSIDE the fence.
        let chunks = steps[0].deltas.clone().expect("delta chunks scripted");
        assert_eq!(
            chunks.concat(),
            full,
            "deltas concatenate to the full answer"
        );
        assert!(chunks.len() >= 3, "multiple deltas scripted: {chunks:?}");
        assert!(
            chunks
                .iter()
                .any(|c| c.contains("(defn double [x]") && !c.contains("add-i64")),
            "a delta boundary falls INSIDE the ```lisp fence body: {chunks:?}"
        );
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
        match &script[0].response {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "submit");
                // The whole form (with its spaces) is the argument; line 1 is the
                // BROKEN form (missing its closing paren).
                assert_eq!(calls[0].argument, "(defn double [x] (add-i64 x x)");
            }
            other => panic!("expected ToolCalls(submit), got {other:?}"),
        }
        match &script[1].response {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "submit");
                // Line 2 is the CLEAN repaired form.
                assert_eq!(calls[0].argument, "(defn double [x] (add-i64 x x))");
            }
            other => panic!("expected ToolCalls(submit), got {other:?}"),
        }
        assert_eq!(
            script[2].response,
            ModelResponse::Done("defined double for you".to_string())
        );
    }

    // S89 Cluster C: `tool: set-preamble <MODULE> <TEXT>` / `tool: set-doc
    // <SYMBOL> <TEXT>` parse with the FIRST token as the target and the REST of
    // the line (verbatim, including inner spaces) as the text — the same `tool:`
    // grammar as `submit` (the argument is `<TARGET> <TEXT>`, re-split in
    // `run_document_edit`). No new keyword: `set-preamble`/`set-doc` are tool
    // NAMES (the §17.2 discriminator).
    #[test]
    fn parses_set_preamble_and_set_doc_tools() {
        let script = parse_script(
            "tool: set-preamble user Solver core: constraint propagation over a grid.\n\
             tool: set-doc solve Solve the grid by propagation.\n\
             done: recorded\n",
        );
        assert_eq!(script.len(), 3);
        match &script[0].response {
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
        match &script[1].response {
            ModelResponse::ToolCalls(calls) => {
                assert_eq!(calls[0].name, "set-doc");
                assert_eq!(calls[0].argument, "solve Solve the grid by propagation.");
            }
            other => panic!("expected ToolCalls(set-doc), got {other:?}"),
        }
    }

    #[test]
    fn complete_consumes_script_then_terminates() {
        let mut stub = StubModel::new(vec![ModelResponse::Done("ok".to_string())]);
        let req = AgentRequest::default();
        assert_eq!(
            stub.complete(&req).unwrap(),
            ModelResponse::Done("ok".to_string())
        );
        // Exhausted → terminal empty Done.
        assert_eq!(
            stub.complete(&req).unwrap(),
            ModelResponse::Done(String::new())
        );
        // Two requests captured.
        assert_eq!(stub.requests.lock().unwrap().len(), 2);
    }

    // S107 — `complete_streaming` emits the scripted deltas to the sink (in order,
    // concatenating to the Done prose), and records the request like `complete`.
    #[test]
    fn complete_streaming_emits_scripted_deltas() {
        let steps = parse_script("done: line one<|delta|>\nprose: line two\n");
        let mut stub = StubModel::from_steps(steps);
        let req = AgentRequest::default();
        let mut got: Vec<String> = Vec::new();
        let mut sink = |d: &str| got.push(d.to_string());
        let resp = stub.complete_streaming(&req, &mut sink).unwrap();
        // Two scripted deltas, concatenating to the (marker-stripped) Done prose.
        assert_eq!(got, vec!["line one".to_string(), "\nline two".to_string()]);
        assert_eq!(resp, ModelResponse::Done("line one\nline two".to_string()));
        assert_eq!(got.concat(), "line one\nline two");
        assert_eq!(stub.requests.lock().unwrap().len(), 1);
    }

    // S107 — absent any `<|delta|>` marker, `complete_streaming` emits the whole
    // Done prose as ONE delta (the default one-delta / §17.22 Fallback path).
    #[test]
    fn complete_streaming_default_is_one_delta() {
        let mut stub = StubModel::new(vec![ModelResponse::Done("whole answer".to_string())]);
        let req = AgentRequest::default();
        let mut got: Vec<String> = Vec::new();
        let mut sink = |d: &str| got.push(d.to_string());
        stub.complete_streaming(&req, &mut sink).unwrap();
        assert_eq!(
            got,
            vec!["whole answer".to_string()],
            "one delta = the whole answer"
        );
    }
}
