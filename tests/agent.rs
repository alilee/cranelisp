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

// ===========================================================================
// Cluster A — agent output rendering (S89 Wave 1; design/int/agent.md §14,
// repl/spec.md §17.12–§17.13). RED-FIRST: these pin the new `render.rs`
// behaviour (the agent-input `agent>` prompt at echo sites, markdown formatted
// inside the `▌` frame, ```lisp fences pretty-printed) AND the §17.13.3 ANSI-
// leak defect (no literal escape codes; `--no-color` clean). They drive the
// real binary through the stub-provider-by-config mechanism (CRANELISP_AGENT_
// PROVIDER=stub) so the rendering is exercised end-to-end with zero network.
//
// A.1 (`agent_output_no_literal_ansi_escape_when_color_off_neg`) is the OWED
// failing-not-ignored DEFECT repro — RED on HEAD against today's leaking render,
// flips green when /dev lands the §14.6 style-once-at-the-leaf fix (step 1d) in
// the same change-set with its mandatory unit test. A.2 are RED until the §14
// `render.rs` work lands. None is `#[ignore]`d.
//
// ESC `[` (the literal `\x1b[` SGR introducer) is the leak signature: a literal
// escape character that reached the captured pipe as a *visible byte* rather
// than taking effect / being suppressed.
// ===========================================================================

/// The literal ANSI/SGR introducer (ESC followed by `[`). A conforming agent
/// render NEVER emits this as visible text under `--no-color` (§17.13.3).
#[cfg(feature = "agent")]
const ESC_SGR: &str = "\u{1b}[";

/// Stub-driven agent REPL with extra CLI flags (e.g. `--no-color`). Like
/// `stub_repl` but lets a test pass additional flags so the colour-off path can
/// be exercised. Writes `script` to the per-test tmpdir, wires the stub provider.
#[cfg(feature = "agent")]
fn stub_repl_flags(
    script: &str,
    prelude: PreludeVariant,
    flags: &[&str],
    stdin: &str,
) -> helpers::e2e::CrOutput {
    let mut cl = Cranelisp::new().repl().with_prelude(prelude).cli_flag("--agent");
    for f in flags {
        cl = cl.cli_flag(f);
    }
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, script).unwrap();
    cl.env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .stdin(stdin)
        .output()
}

// ---------------------------------------------------------------------------
// A.1 — the ANSI-escape-leak DEFECT (§14.6, §17.13.3) — RED-FIRST on HEAD
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.13.3 — an `/ask` answer whose scripted prose carries a
// ```lisp fence MUST, under `--no-color`, render as a **clean plain-text
// transcript**: the §17.13.3 normative acceptance is "gutter + plain prose +
// plain-indented Lisp" with NO literal ANSI escape sequence anywhere and NO raw
// fence markers surviving. This is the owed narrow failing-not-ignored DEFECT
// repro (CLAUDE.md §Testing) and is RED on HEAD: today the agent render path
// emits the ```lisp fence verbatim (raw fence markers survive — NOT "plain-
// indented Lisp"), violating the §17.13.3 `--no-color`-clean contract. It flips
// green when /dev lands the §14.6 style-once-at-the-leaf render fix (step 1d).
//
// TESTABILITY NOTE (flagged to /dev 1d / /int): the *literal-ANSI-escape* half
// of §17.13.3 (a visible `\x1b[` reaching the screen) is the candidate-(b)
// "styled-for-TTY text captured into a pipe" leak — which manifests only with
// COLOUR ON. The e2e harness pipes stdout, so `is_color_enabled()` is always
// false (style.rs detect_color: non-TTY ⇒ off) and there is no `--color=force`
// path (repl/spec.md §10.7). So the colour-ON escape leak CANNOT be reproduced
// end-to-end through the binary's I/O today — that residual is the /dev-owned
// unit-tier guard (`render_agent_prose` output over a ```lisp fence contains no
// literal `\x1b` when colour off / well-formed SGR when on, §14.6). This e2e
// repro therefore pins the colour-OFF `--no-color`-clean contract (no literal
// escape + plain-indented Lisp, not a raw fence), the half that IS observable.
#[cfg(feature = "agent")]
#[test]
fn agent_output_no_literal_ansi_escape_when_color_off_neg() {
    // One `/ask` turn; one scripted `done:` prose carrying one ```lisp fence.
    // The fence body is the form the render path routes through pretty_print.
    let out = stub_repl_flags(
        "done: Here is a definition:\n\
         prose: ```lisp\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // (a) NO literal `\x1b[` may appear anywhere under `--no-color` — agent
    // output must be completely free of SGR/escape sequences (§17.13.3). (This
    // half passes on HEAD because the harness forces colour off; it is the
    // load-bearing absence guard that must NOT regress when the fix lands.)
    assert!(
        !out.stdout.contains(ESC_SGR),
        "agent output must contain NO literal ANSI escape (\\x1b[) under --no-color; \
         found leaked SGR in stdout={:?}",
        out.stdout
    );
    // (b) §17.13.3 acceptance: the `--no-color` transcript is "plain-indented
    // Lisp" — the raw ```lisp fence markers must NOT survive (the fence is
    // pretty-printed, not echoed verbatim). RED on HEAD: today the raw fence is
    // emitted verbatim, so this fails until the §14.5 fence-routing lands.
    assert!(
        !out.stdout.contains("```"),
        "the `--no-color` transcript must be plain-indented Lisp, NOT a raw \
         ```fence — raw fence markers must not survive (§17.13.3), stdout={:?}",
        out.stdout
    );
    // Sanity: the agent turn actually rendered (so the absences above are real
    // coverage, not an empty transcript). The prose frame gutter is present.
    assert!(
        out.stdout.contains("\u{258c}"),
        "the agent answer must have rendered (framed), stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.13.2 — the fenced ```lisp form is routed through the
// deterministic S-expression pretty-printer (the same one /source and /sexp
// use), rendered as a correctly-styled, indented Lisp form INSIDE the `▌` prose
// frame — NOT emitted as a raw fence. Positive companion to A.1. RED until the
// §14.5 fence-routing lands; with colour ON the SGR is well-formed (no orphan
// literal escape bytes — every escape is part of a complete SGR sequence).
#[cfg(feature = "agent")]
#[test]
fn agent_output_lisp_fence_pretty_printed_styled() {
    let out = stub_repl_flags(
        "done: Here is a definition:\n\
         prose: ```lisp\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n",
        PreludeVariant::PrimitivesOnly,
        // colour ON (no --no-color) — exercises the styled leaf.
        &[],
        "/ask how do I double a number?\n",
    );
    // Positive: the form is pretty-printed — the symbols of the form appear
    // (round-tripped through the printer), NOT a raw ```lisp fence marker.
    assert!(
        out.stdout.contains("double") && out.stdout.contains("add-i64"),
        "the fenced lisp form must be pretty-printed into the answer, stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("```lisp") && !out.stdout.contains("```"),
        "the raw markdown fence markers must NOT survive into the rendered output, \
         stdout={:?}",
        out.stdout
    );
    // With colour on, any escape present must be a WELL-FORMED SGR sequence:
    // every ESC is immediately followed by `[` (the CSI introducer). An orphan
    // ESC not followed by `[` is the leak signature.
    for (i, _) in out.stdout.match_indices('\u{1b}') {
        let after = &out.stdout[i + 1..];
        assert!(
            after.starts_with('['),
            "every ESC must introduce a well-formed SGR (ESC '['); found an orphan \
             escape at byte {i} in stdout={:?}",
            out.stdout
        );
    }
}

// ---------------------------------------------------------------------------
// A.2 — rendering improvements (positive — RED until §14 render.rs lands)
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.12 — an agent-issued pull (a read command the agent
// "types") renders with the distinct agent-input prompt glyph `agent>` so the
// transcript reads honestly: who typed what. The result below it is the REPL's
// own normal output, unprefixed. RED until the §14.2 agent-input prefix lands.
#[cfg(feature = "agent")]
#[test]
fn agent_issued_pull_shows_agent_prompt() {
    let out = stub_repl_flags(
        "tool: source target\n\
         done: that is the source of target\n",
        PreludeVariant::PrimitivesOnly,
        // colour-independent assertion (the glyph degrades to plain `agent>`),
        // so run under --no-color to pin the plain-text token.
        &["--no-color"],
        "(defn target [x] (add-i64 x 1))\n\
         /ask show me target\n",
    );
    // The pulled command line carries the `agent>` agent-input prompt (§17.12).
    assert!(
        out.stdout.contains("agent>"),
        "the agent-issued pull must carry the `agent>` prompt glyph, stdout={}",
        out.stdout
    );
    // And the command itself is still echoed as-typed after the prompt.
    assert!(
        out.stdout.contains("/source target"),
        "the pulled command must still render as-typed, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.13.1 — the agent's markdown prose (heading / list /
// emphasis / inline-code) renders FORMATTED for the terminal within the §17.2
// `▌` agent-prose frame, NOT as raw markdown source. Under --no-color the
// markdown degrades to plain text (markers stripped) with the gutter present.
// RED until the §14.3 markdown_to_terminal formatter lands.
#[cfg(feature = "agent")]
#[test]
fn agent_prose_markdown_formatted_for_terminal() {
    let out = stub_repl_flags(
        "done: ## Defining functions\n\
         prose: Use **defn** to define a `function`.\n\
         prose: - first point\n\
         prose: - second point\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I define a function?\n",
    );
    // Framed (the prose frame gutter is present).
    assert!(
        out.stdout.contains("\u{258c}"),
        "the markdown prose must render inside the agent frame, stdout={}",
        out.stdout
    );
    // The heading text and the list/emphasis words survive (formatted), but the
    // raw markdown SOURCE markers must NOT (heading `##`, bold `**`, list `- `
    // as literal source, inline-code backticks).
    assert!(
        out.stdout.contains("Defining functions"),
        "the heading text must render, stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("##") && !out.stdout.contains("**") && !out.stdout.contains('`'),
        "raw markdown source markers (##, **, backticks) must NOT survive into \
         the formatted prose, stdout={:?}",
        out.stdout
    );
}

// spec: repl/spec.md §17.13.3 — the same markdown prose under `--no-color`
// degrades cleanly: formatted layout, gutter present, and NO literal escape
// codes. This ties A.1's absence guard to the markdown leaf (the `styled()`
// short-circuit). RED until the colour-gate-honouring markdown leaf lands.
#[cfg(feature = "agent")]
#[test]
fn agent_prose_markdown_no_color_clean_neg() {
    let out = stub_repl_flags(
        "done: ## Defining functions\n\
         prose: Use **defn** to define a `function`.\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I define a function?\n",
    );
    assert!(
        !out.stdout.contains(ESC_SGR),
        "markdown prose under --no-color must contain NO literal ANSI escape \
         (\\x1b[), stdout={:?}",
        out.stdout
    );
    // The gutter is still emitted as a plain-text prefix (frame degradation).
    assert!(
        out.stdout.contains("\u{258c}"),
        "the `▌` gutter must still mark the frame under --no-color, stdout={}",
        out.stdout
    );
    // §17.13.1: under --no-color the markdown DEGRADES to plain text — emphasis
    // markers stripped to their words, inline-code backticks gone, heading `##`
    // gone. RED on HEAD: today the raw markdown source passes through verbatim.
    assert!(
        !out.stdout.contains("##") && !out.stdout.contains("**") && !out.stdout.contains('`'),
        "markdown must degrade to plain text under --no-color (markers stripped: \
         ##, **, backticks), NOT pass through as raw source, stdout={:?}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// A.2 (iv) — Lane-D whole-session golden: a full `/ask` session (scripted prose
// + a ```lisp fence + an agent-issued pull) renders with the three visually-
// distinct origins honestly marked: agent prose framed in `▌`, the pull echoed
// unframed with the `agent>` prompt glyph, the fence pretty-printed (not raw),
// and NO literal escape codes under --no-color. Pins the whole rendered shape;
// a single drift in any of the three render rules flips it red. RED until §14.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.12 — whole-session render shape (Lane D): pull glyph +
// framed prose + pretty-printed fence + clean --no-color, all in one session.
#[cfg(feature = "agent")]
#[test]
fn agent_session_render_golden_transcript() {
    let out = stub_repl_flags(
        // Turn 1: a read pull. Turn 2: terminal prose carrying a ```lisp fence.
        "tool: source target\n\
         done: Here is the source, and a cleaner version:\n\
         prose: ```lisp\n\
         prose: (defn target [x] (add-i64 x 1))\n\
         prose: ```\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "(defn target [x] (add-i64 x 1))\n\
         /ask show me target and a cleaner version\n",
    );
    // (1) the agent-issued pull line carries the `agent>` prompt glyph (§17.12).
    assert!(
        out.stdout.contains("agent>"),
        "the agent-issued pull must carry the `agent>` prompt, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("/source target"),
        "the pulled command must render as-typed, stdout={}",
        out.stdout
    );
    // (2) the agent's terminal prose is framed in the `▌` gutter.
    assert!(
        out.stdout.contains("\u{258c}"),
        "the agent prose must be framed, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("cleaner version"),
        "the agent prose must render, stdout={}",
        out.stdout
    );
    // (3) the ```lisp fence is pretty-printed into the answer (no raw fence).
    assert!(
        !out.stdout.contains("```"),
        "the raw fence markers must NOT survive (the fence is pretty-printed), \
         stdout={:?}",
        out.stdout
    );
    // (4) the whole session is clean under --no-color — no literal escapes.
    assert!(
        !out.stdout.contains(ESC_SGR),
        "the whole agent session under --no-color must contain NO literal ANSI \
         escape (\\x1b[), stdout={:?}",
        out.stdout
    );
}
