// agent.rs — embedded-agent dispatch foundations (Sprint 88 Phase 5, Wave 2).
//
// Tests the LLM-free dispatch / reverse-query foundations of the agentic-REPL
// track (design/int/agent.md, tests/plan/agent-testing-strategy.md):
//
//   - Lane B (feature-OFF guard, DEFAULT suite) — `/ask` → "agent not built
//     in", prose → today's parse-error display, `--agent` accepted-no-op, the
//     reverse-query commands run agent-free. These prove the feature-OFF binary
//     is byte-identical to today on every non-`/ask` input (agent.md §2.2).
//   - Lane A (feature-ON, `--features agent` lane) — the REFINED classifier
//     routing through the binary: compound form / literal / bare KNOWN symbol →
//     deterministic REPL; bare UNKNOWN symbol, multi-word prose, mixed
//     known+unknown, genuine parse error → agent; `/ask` forces the agent; plus
//     the §4 bare-known-symbol-self-doc negative guard. The classifier now
//     RESOLVES bare symbols (not just parses), closing the U1 gap where prose
//     parsed `Ok(N symbols)` and wrongly routed to the REPL.
//   - `/refs` / `/tests-for` — functional + neg, in BOTH builds (LLM-free).
//
// The tests that assert feature-OFF behaviour are gated `#[cfg(not(feature =
// "agent"))]`; the feature-ON classifier tests are gated `#[cfg(feature =
// "agent")]`. The `/refs`/`/tests-for` and `--agent`-accepted tests are
// unconditional (they hold in both builds). Run the agent lane with:
//   cargo nextest run --features agent --test agent

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// Bare REPL (no prelude) — pipe `lines`, capture stdout.
fn repl(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new().repl().stdin(lines).output()
}

// ---------------------------------------------------------------------------
// Lane B — feature-OFF byte-identical guard (DEFAULT suite)
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.1 — `/ask` on a feature-off build prints a single
// clear notice and does not crash or evaluate.
#[cfg(not(feature = "agent"))]
#[test]
fn ask_feature_off_prints_not_built_in() {
    let out = repl("/ask why does + not work on strings\n");
    assert!(
        out.stdout.contains("agent not built in"),
        "stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17 — `/context <path>` on a feature-off build prints the
// "agent not built in" notice and does not crash, write a file, or evaluate
// (the debug command's dispatch body is feature-split, mirroring `/ask`).
#[cfg(not(feature = "agent"))]
#[test]
fn context_feature_off_prints_not_built_in() {
    let out = repl("/context /tmp/should-not-be-written.txt\n");
    assert!(
        out.stdout.contains("agent not built in"),
        "stdout={}",
        out.stdout
    );
    assert!(
        !std::path::Path::new("/tmp/should-not-be-written.txt").exists(),
        "feature-off /context must NOT write the file"
    );
}

// spec: repl/spec.md §17.9 — with the feature off, input that the refined
// classifier's Agent arm WOULD divert (a non-bracket parse error) falls back to
// today's parse-error display (byte-identical fallback); the Agent arm does not
// exist. A stray `)` is a non-bracket parse error.
#[cfg(not(feature = "agent"))]
#[test]
fn parse_error_feature_off_falls_back_to_diagnostic() {
    let out = repl(")\n");
    assert!(
        !out.stdout.contains("\u{258c}"),
        "agent prose frame must be absent feature-off: {}",
        out.stdout
    );
    // It produces an error display, not silent success.
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "expected a parse-error display, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.9 — with the feature off, a bare UNBOUND symbol (which
// the REFINED feature-ON classifier would route to the agent) falls back to
// today's introspection / "unbound" behavior, byte-identical. The agent prose
// frame is absent; the symbol-resolution → Agent routing lives entirely under
// `#[cfg(feature = "agent")]`, so feature-off behavior is exactly today's.
#[cfg(not(feature = "agent"))]
#[test]
fn unbound_symbol_feature_off_falls_back_to_today() {
    let out = repl("lenght\n");
    assert!(
        !out.stdout.contains("\u{258c}"),
        "agent prose frame must be absent feature-off: {}",
        out.stdout
    );
    // Today's behavior for a bare unbound symbol is an unbound/undefined
    // diagnostic — not the agent, and not silent success.
    assert!(
        out.stdout.to_lowercase().contains("unbound")
            || out.stdout.to_lowercase().contains("undefined")
            || out.stdout.to_lowercase().contains("unknown"),
        "expected today's unbound-symbol display feature-off, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.9 — with the feature off, multi-word prose (which the
// refined classifier would route to the agent) falls back to today's behavior,
// byte-identical: no agent prose frame.
#[cfg(not(feature = "agent"))]
#[test]
fn prose_feature_off_falls_back_to_today() {
    let out = repl("how do I define a function\n");
    assert!(
        !out.stdout.contains("\u{258c}"),
        "agent prose frame must be absent feature-off: {}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// `--agent` accepted as no-op (both builds; default build is the load-bearing
// case — a script written for an agent build must not break on a default build)
// ---------------------------------------------------------------------------

// spec: repl/spec.md §0.6.1 — `--agent` is accepted (not "unknown flag") and is
// a no-op in REPL mode; the session behaves exactly as today.
#[test]
fn agent_flag_accepted_not_unknown() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(
        !out.stderr.contains("unknown flag"),
        "--agent must be accepted, stderr={}",
        out.stderr
    );
    assert!(out.stdout.contains("3"), "session must still eval, stdout={}", out.stdout);
}

// spec: repl/spec.md §0.6.1 — `--no-agent` is likewise accepted.
#[test]
fn no_agent_flag_accepted_not_unknown() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--no-agent")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(
        !out.stderr.contains("unknown flag"),
        "--no-agent must be accepted, stderr={}",
        out.stderr
    );
    assert!(out.stdout.contains("3"), "stdout={}", out.stdout);
}

// ---------------------------------------------------------------------------
// `/refs` — reverse-query (LLM-free, both builds)
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.6.1 — `/refs <sym>` lists definitions whose body
// references <sym>.
#[test]
fn refs_finds_referencing_definitions() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn target [x] (add-i64 x 1))\n\
             (defn caller [y] (target y))\n\
             /refs target\n",
        )
        .output();
    assert!(
        out.stdout.contains("references to target"),
        "stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("caller"),
        "caller must be listed as a referer, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.6.1 — `/refs` with no references prints a clear
// no-results line, distinct from an unknown-symbol error (+neg).
#[test]
fn refs_no_references_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn lonely [x] x)\n\
             /refs lonely\n",
        )
        .output();
    assert!(
        out.stdout.contains("no references to lonely"),
        "stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.6.1 — `/refs` on an unbound name reports unbound,
// distinguishing a typo from a genuinely-unreferenced symbol (+neg).
#[test]
fn refs_unbound_symbol_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("/refs no-such-symbol\n")
        .output();
    assert!(
        out.stdout.contains("unbound symbol 'no-such-symbol'"),
        "stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.6.1 — `/refs` with no argument prints a usage hint.
#[test]
fn refs_no_arg_usage_neg() {
    let out = repl("/refs\n");
    assert!(
        out.stdout.contains("Usage: /refs <symbol-name>"),
        "stdout={}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// `/tests-for` — reverse-query restricted to test functions (LLM-free)
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.6.2 — `/tests-for <sym>` lists test functions whose
// body references <sym>, and excludes non-test referers (+neg on the filter).
#[test]
fn tests_for_filters_to_test_functions() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn solve [x] (add-i64 x 1))\n\
             (defn caller [y] (solve y))\n\
             (defn test-solve [] (solve 1))\n\
             /tests-for solve\n",
        )
        .output();
    assert!(
        out.stdout.contains("tests referencing solve"),
        "stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("test-solve"),
        "the test fn must be listed, stdout={}",
        out.stdout
    );
    // +neg: the non-test referer `caller` must NOT appear in the /tests-for
    // command output (scope the check to the region after the header so the
    // earlier defn echo of `user/caller` is not counted).
    let after_header = out
        .stdout
        .split("tests referencing solve")
        .nth(1)
        .unwrap_or("");
    assert!(
        !after_header.contains("caller"),
        "non-test referer must be excluded from /tests-for output, region={after_header:?}"
    );
}

// spec: repl/spec.md §17.6.2 — `/tests-for` with no test referers prints a
// clear no-results line (+neg).
#[test]
fn tests_for_no_tests_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn untested [x] x)\n\
             /tests-for untested\n",
        )
        .output();
    assert!(
        out.stdout.contains("no tests reference untested"),
        "stdout={}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// Lane A — classifier routing through the binary (feature-ON)
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.1 — a complete form evals, NOT the agent (no prose
// frame).
#[cfg(feature = "agent")]
#[test]
fn agent_on_form_routes_to_repl() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(out.stdout.contains("3"), "stdout={}", out.stdout);
    assert!(
        !out.stdout.contains("\u{258c}"),
        "a form must NOT route to the agent, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17 — `/context <path>` (feature-ON) dumps the assembled
// agent request to a file even when the agent is DORMANT (no provider key set):
// `assemble_request` is pure, so the debug dump needs no API call. The file
// carries the labeled section headers + the always-on primer, and the
// confirmation line is printed. Writes a relative path into the per-test tmpdir
// (the binary's cwd), then reads it back.
#[cfg(feature = "agent")]
#[test]
fn agent_on_context_dumps_request_to_file_dormant() {
    let cr = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // No CRANELISP_AGENT_PROVIDER / key ⇒ dormant; /context still works.
        .stdin("(defn ctx-marker-fn [x] (add-i64 x 1))\n/context ctx-dump.txt\n");
    let out = cr.output();
    assert!(
        out.stdout.contains("wrote agent context to ctx-dump.txt"),
        "the confirmation line must print, stdout={}",
        out.stdout
    );
    let dumped = std::fs::read_to_string(out.tmpdir.join("ctx-dump.txt"))
        .expect("the /context file must exist");
    assert!(!dumped.is_empty(), "the dumped context must be non-empty");
    assert!(dumped.contains("=== SYSTEM PRIMER ==="), "primer header: {dumped}");
    assert!(dumped.contains("=== HARVESTED CONTEXT ==="), "harvest header");
    assert!(dumped.contains("=== TRANSCRIPT ==="), "transcript header");
    assert!(dumped.contains(":Type"), "the real language primer must be present");
    // The current-module pin in the harvest carries the just-defined fn's source.
    assert!(
        dumped.contains("ctx-marker-fn"),
        "the harvested current-module source must carry the defined fn: {dumped}"
    );
}

// spec: repl/spec.md §17.1 — a bare KNOWN symbol STILL self-documents; the agent
// does not intercept the §4 surface for a symbol that resolves, even with the
// feature on. `add-i64` resolves through the primitives-only prelude (the
// load-bearing negative guard preserving §4).
#[cfg(feature = "agent")]
#[test]
fn agent_on_bare_known_symbol_still_self_documents() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("add-i64\n")
        .output();
    assert!(
        !out.stdout.contains("\u{258c}"),
        "a bare KNOWN symbol must self-document, not route to the agent, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a bare KNOWN user-defined fn (defined this session)
// self-documents; resolution sees the live def, so the agent does not intercept.
#[cfg(feature = "agent")]
#[test]
fn agent_on_bare_defined_fn_self_documents() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn my-fn [x] (add-i64 x 1))\nmy-fn\n")
        .output();
    assert!(
        !out.stdout.contains("\u{258c}"),
        "a bare KNOWN defined fn must self-document, not route to the agent, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a literal routes to the deterministic REPL (the §4
// bare-value display), never the agent.
#[cfg(feature = "agent")]
#[test]
fn agent_on_literal_routes_to_repl() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("42\n")
        .output();
    assert!(out.stdout.contains("42"), "stdout={}", out.stdout);
    assert!(
        !out.stdout.contains("\u{258c}"),
        "a literal must NOT route to the agent, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a compound vector routes to the deterministic REPL
// (it is code), never the agent.
#[cfg(feature = "agent")]
#[test]
fn agent_on_compound_vector_routes_to_repl() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("[1 2 3]\n")
        .output();
    assert!(
        !out.stdout.contains("\u{258c}"),
        "a vector must NOT route to the agent, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a bare UNKNOWN symbol (a typo / bare word) routes to
// the agent (the refined classifier resolves the symbol and finds it unbound).
#[cfg(feature = "agent")]
#[test]
fn agent_on_bare_unknown_symbol_routes_to_agent() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("lenght\n")
        .output();
    assert!(
        out.stdout.contains("\u{258c}"),
        "a bare unknown symbol must route to the agent frame, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — multi-word prose parses as a run of bare symbols
// (Ok), but they do not resolve, so the refined classifier routes it to the
// agent. This is the U1 gap the refinement closes (was wrongly Repl before).
#[cfg(feature = "agent")]
#[test]
fn agent_on_prose_routes_to_agent() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("how do I define a function\n")
        .output();
    assert!(
        out.stdout.contains("\u{258c}"),
        "multi-word prose must route to the agent frame, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a buffer mixing a known bare symbol with an unknown
// one routes to the agent (any-unbound wins). `add-i64` resolves; `frobnicate`
// does not.
#[cfg(feature = "agent")]
#[test]
fn agent_on_mixed_known_unknown_routes_to_agent() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("add-i64 frobnicate\n")
        .output();
    assert!(
        out.stdout.contains("\u{258c}"),
        "mixed known+unknown must route to the agent frame, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a non-bracket parse error routes to the agent (the
// Wave-2 placeholder renders the framed notice). A stray `)` is a genuine parse
// error the classifier diverts.
#[cfg(feature = "agent")]
#[test]
fn agent_on_parse_error_routes_to_agent() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .stdin(")\n")
        .output();
    assert!(
        out.stdout.contains("\u{258c}"),
        "a non-bracket parse error must route to the agent frame, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — `/ask` forces the agent even for a bare word that
// would otherwise self-document.
#[cfg(feature = "agent")]
#[test]
fn agent_on_ask_forces_agent_for_bare_word() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .stdin("/ask why\n")
        .output();
    assert!(
        out.stdout.contains("\u{258c}"),
        "/ask must route to the agent frame, stdout={}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// Lane A — stub-driven e2e (the §1.1(a) stub-provider-by-config mechanism).
// CRANELISP_AGENT_PROVIDER=stub selects a deterministic `AgentModel` built from
// a scripted-response fixture; the test writes the script, drives the real
// binary via the REPL, and asserts the rendered transcript. This tests the REAL
// dispatch / request-assembly / pull wiring in the real binary, with zero
// network. Script DSL (one scripted turn-response per line):
//   tool: <name> <argument>   → a ToolCalls response (synthesized REPL command)
//   done: <prose>             → a terminal Done(prose) response
// ---------------------------------------------------------------------------

/// Build a stub-driven agent REPL: write `script` to a fixture in the tmpdir and
/// wire `CRANELISP_AGENT_PROVIDER=stub` + the script path. The model-id is unused
/// by the stub but a provider must be selected.
#[cfg(feature = "agent")]
fn stub_repl(script: &str, prelude: PreludeVariant, stdin: &str) -> helpers::e2e::CrOutput {
    let cl = Cranelisp::new().repl().with_prelude(prelude).cli_flag("--agent");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, script).unwrap();
    cl.env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .stdin(stdin)
        .output()
}

// spec: repl/spec.md §17.2 — pull-as-visible-command: the stub asks for a read
// command (`/source foo`); the agent synthesizes it, runs it through the SAME
// process_commands path a keystroke uses, renders it as-if-typed, feeds the
// result back, then answers. The transcript shows the command line + the answer.
#[cfg(feature = "agent")]
#[test]
fn stub_pull_renders_as_visible_command() {
    let out = stub_repl(
        "tool: source target\n\
         done: that is the source of target\n",
        PreludeVariant::PrimitivesOnly,
        "(defn target [x] (add-i64 x 1))\n\
         /ask show me target\n",
    );
    // The synthesized read command appears in the transcript as if typed.
    assert!(
        out.stdout.contains("/source target"),
        "the pulled command must render as-typed, stdout={}",
        out.stdout
    );
    // The agent's terminal prose is framed.
    assert!(
        out.stdout.contains("\u{258c}"),
        "the agent answer must be framed, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("that is the source of target"),
        "the agent prose must render, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.3 — +neg: a write/non-read tool-call is REFUSED by the
// read-only allowlist. The stub attempts `/sh`; the agent renders a refusal and
// nothing is executed (the consent boundary in read-only Advise mode).
#[cfg(feature = "agent")]
#[test]
fn stub_write_tool_call_is_refused() {
    let out = stub_repl(
        "tool: sh echo pwned\n\
         done: ok\n",
        PreludeVariant::PrimitivesOnly,
        "/ask run a shell command\n",
    );
    assert!(
        out.stdout.contains("refused"),
        "a write command must be refused, stdout={}",
        out.stdout
    );
    // The shell command must NOT have run (its output must be absent).
    assert!(
        !out.stdout.contains("pwned"),
        "the refused shell command must not execute, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17 — acceptance (with the stub): `/ask` returns a grounded
// answer + a proposed `(defn …)`. The proposal is SHOWN (framed), NOT submitted:
// the session symbol table is unchanged — a subsequent reference to the proposed
// name is still unbound. (Real-model grounding is Lane C, non-CI.)
#[cfg(feature = "agent")]
#[test]
fn stub_proposed_defn_is_shown_not_submitted() {
    let out = stub_repl(
        "done: Here is how to define a constrained function over Num:\\n(defn double [a] (+ a a))\n",
        PreludeVariant::PrimitivesOnly,
        // After the /ask, reference the proposed name via a COMPOUND form so it
        // routes to the deterministic REPL (a bare `double` would re-route to the
        // agent as an unknown symbol). `(double 2)` reaches eval → unbound, which
        // proves the proposed `(defn double …)` was never submitted.
        "/ask how do I define a constrained function over Num?\n\
         (double 2)\n",
    );
    // The proposal is shown in the agent frame.
    assert!(
        out.stdout.contains("\u{258c}"),
        "the proposal must be framed, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("constrained function over Num"),
        "the grounded answer must render, stdout={}",
        out.stdout
    );
    // +neg: the proposed `(defn double …)` was NOT submitted — `double` is still
    // unbound when referenced afterwards (the read-only Advise contract).
    assert!(
        out.stdout.to_lowercase().contains("unbound")
            || out.stdout.to_lowercase().contains("undefined")
            || out.stdout.to_lowercase().contains("unknown"),
        "the proposed defn must NOT be submitted (double stays unbound), stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — with the agent feature ON but NO provider
// configured/reachable, the agent is dormant and `/ask` says so (the U6
// opt-in-twice "no provider" path). The notice is framed; no crash.
#[cfg(feature = "agent")]
#[test]
fn agent_on_no_provider_is_dormant() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // Force the anthropic provider with no key → dormant.
        .env("CRANELISP_AGENT_PROVIDER", "anthropic")
        .stdin("/ask anything\n")
        .output();
    assert!(
        out.stdout.contains("\u{258c}"),
        "the dormant notice must be framed, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.to_lowercase().contains("provider"),
        "the dormant notice must mention the missing provider, stdout={}",
        out.stdout
    );
}
