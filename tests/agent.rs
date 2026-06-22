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

// spec: repl/spec.md §0.6.2 — B.5 (DEFAULT-lane half, NOT cfg(agent)): `--yes`
// on a DEFAULT (non-`agent`) build is an accepted no-op — never `unknown flag`,
// the session evals exactly as today. A script written for an agent build with
// `--yes` must run unchanged on a default build (the accepted-no-op discipline,
// §20.1, identical to `--agent`). RED today: the default build does not yet
// parse `--yes`, so it errors `unknown flag` — flips green when /dev 2d adds
// the accepted-no-op parse (`main.rs:413`, sibling to `--agent`).
#[test]
fn yes_flag_accepted_no_op_default_build() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--yes")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(
        !out.stderr.contains("unknown flag"),
        "`--yes` must be accepted on a default build (no-op), stderr={}",
        out.stderr
    );
    assert!(
        out.stdout.contains("3"),
        "the session must still eval, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §0.6.2 — `-y` (the short form of `--yes`) is likewise an
// accepted no-op on a default build. RED today for a SUBTLE reason: `-y` does
// not start with `--`, so today's parse loop (`main.rs:480`) swallows it as the
// REPL *target* (a module name) rather than recognising it as a flag — the
// session then runs in a `-y>` target context (a false-green if we only checked
// `unknown flag`/eval). The load-bearing guard is that `-y` must be parsed as a
// FLAG, NOT a target: the plain REPL prompt must NOT carry the `-y>` target
// marker. Flips green when /dev 2d adds `-y` to the recognised-flag arm.
#[test]
fn y_short_flag_accepted_no_op_default_build() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("-y")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(
        !out.stderr.contains("unknown flag"),
        "`-y` must be accepted on a default build (no-op), stderr={}",
        out.stderr
    );
    // The +neg guard: `-y` must NOT be swallowed as the REPL target — the
    // prompt must be the plain REPL prompt, never the `-y>` target context.
    assert!(
        !out.stdout.contains("-y>"),
        "`-y` must be parsed as a FLAG, not swallowed as the REPL target \
         (no `-y>` target prompt), stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("3"),
        "the session must still eval, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §0.6.2 — `--no-agent` is likewise accepted.
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
// The route fires only when the agent is ACTIVE (arch ruling e3f7d57, §5.3/§7.4:
// active ⇒ route; dormant ⇒ today's display) — so this drives an ACTIVE stub. The
// dormant complement (today's undefined-name diagnostic, NO frame) is the now-
// passing `repl_introspection::bare_primitive_unknown_name_produces_undefined_error_neg`.
#[cfg(feature = "agent")]
#[test]
fn agent_on_bare_unknown_symbol_routes_to_agent() {
    let out = stub_repl(
        "done: that is not a defined symbol\n",
        PreludeVariant::PrimitivesOnly,
        "lenght\n",
    );
    assert!(
        out.stdout.contains("\u{258c}"),
        "a bare unknown symbol must route to the ACTIVE agent frame, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — multi-word prose parses as a run of bare symbols
// (Ok), but they do not resolve, so the refined classifier routes it to the
// agent. This is the U1 gap the refinement closes (was wrongly Repl before).
// Active-agent route (arch ruling e3f7d57).
#[cfg(feature = "agent")]
#[test]
fn agent_on_prose_routes_to_agent() {
    let out = stub_repl(
        "done: to define a function use defn\n",
        PreludeVariant::PrimitivesOnly,
        "how do I define a function\n",
    );
    assert!(
        out.stdout.contains("\u{258c}"),
        "multi-word prose must route to the ACTIVE agent frame, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a buffer mixing a known bare symbol with an unknown
// one routes to the agent (any-unbound wins). `add-i64` resolves; `frobnicate`
// does not. Active-agent route (arch ruling e3f7d57).
#[cfg(feature = "agent")]
#[test]
fn agent_on_mixed_known_unknown_routes_to_agent() {
    let out = stub_repl(
        "done: frobnicate is not defined\n",
        PreludeVariant::PrimitivesOnly,
        "add-i64 frobnicate\n",
    );
    assert!(
        out.stdout.contains("\u{258c}"),
        "mixed known+unknown must route to the ACTIVE agent frame, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — a non-bracket parse error routes to the agent when
// ACTIVE (arch ruling e3f7d57). A stray `)` is a genuine parse error the
// classifier diverts to a live agent. The dormant complement (today's parse-error
// diagnostic, NO frame) is the now-passing `repl_negative::parse_error_stray_close`.
#[cfg(feature = "agent")]
#[test]
fn agent_on_parse_error_routes_to_agent() {
    let out = stub_repl(
        "done: that looks like a stray close paren\n",
        PreludeVariant::PrimitivesOnly,
        ")\n",
    );
    assert!(
        out.stdout.contains("\u{258c}"),
        "a non-bracket parse error must route to the ACTIVE agent frame, stdout={}",
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

// ===========================================================================
// Cluster B — Build mode + pre-flight validator + `--yes` (S89 Wave 2;
// design/int/agent.md §15/§16/§20, repl/spec.md §17.14 / §0.6.2 / §17.16).
// RED-FIRST: these pin the agent's FIRST WRITE PATH — the confirm-gated
// `submit` write arm (§15.2), the silent stage→check→discard repair loop
// (§16.5), the read-only structural floor (§15.4), and the `--yes` auto-accept
// policy knob that skips CONSENT but NEVER the validator (§20.3). They drive
// the real binary through the stub-provider-by-config mechanism
// (CRANELISP_AGENT_PROVIDER=stub) so the whole write path is exercised
// end-to-end with zero network. None is `#[ignore]`d — RED until /dev 2d lands
// the rung-5 write arm + validator + `--yes` threading.
//
// ---------------------------------------------------------------------------
// BROKEN-THEN-FIXED STUB-SCRIPT DSL — the contract /dev 2d MUST implement.
// ---------------------------------------------------------------------------
// The existing stub-script DSL (src/CLAUDE.md, agent-testing-strategy.md §1.1)
// is one scripted MODEL TURN-RESPONSE per line, consumed in order, one per
// `AgentModel::complete()` call within a turn's model↔tool loop:
//
//     tool: <name> <argument>   → a ToolCalls response (synthesized command)
//     done: <prose>             → a terminal Done(prose) response
//     prose: <line>             → a continuation line of the preceding done body
//
// Cluster B EXTENDS this with exactly ONE new tool name — `submit` — the Build
// write tool (§15.1). The stub line format is the SAME `tool:` form:
//
//     tool: submit <FORM>       → a `submit` ToolCalls response carrying <FORM>
//                                 (the rest of the line, verbatim) as the form
//                                 string to validate→confirm→submit (§15.2).
//
// A BROKEN-THEN-FIXED repair sequence is expressed as TWO consecutive
// `tool: submit` lines — NO new keyword. The repair loop (§16.2) consumes
// scripted responses in sequence exactly as the model↔tool loop does: the
// FIRST `tool: submit` line carries code that FAILS `validate_forms_dry_run`
// (parse OR type — U5, no error-classification); the validator stages → checks
// → DISCARDS it, feeds the compiler error back silently, and re-prompts; the
// stub's NEXT scripted response (the SECOND `tool: submit` line) carries the
// CLEAN code that passes. The Nth `tool: submit` in a script is the Nth repair
// attempt; the first one that validates clean reaches the confirm gate.
//
// Canonical broken-then-fixed two-line script (verbatim — /dev 2d's contract):
//
//     tool: submit (defn double [x] (add-i64 x x)
//     tool: submit (defn double [x] (add-i64 x x))
//     done: defined double for you
//
// Line 1 is broken (unbalanced paren → parse Err → repair). Line 2 is the
// clean repaired form (reaches the confirm gate → submits on accept / --yes).
// Line 3 is the terminal prose after the write. This is minimal and consistent
// with the existing `tool:`/`done:` DSL — `submit` is just a tool name; the
// broken-then-fixed sequence is just two scripted turn-responses in order.
// ---------------------------------------------------------------------------

/// The canonical broken-then-fixed Build script (the DSL above): line 1 is a
/// parse-broken `submit` (unbalanced paren), line 2 the clean repaired form,
/// line 3 the terminal prose. The clean form binds `double`.
#[cfg(feature = "agent")]
const BROKEN_THEN_FIXED_SUBMIT: &str = "tool: submit (defn double [x] (add-i64 x x)\n\
     tool: submit (defn double [x] (add-i64 x x))\n\
     done: defined double for you\n";

// ---------------------------------------------------------------------------
// B.1 — the validator repair loop (the killer test): broken-then-fixed.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.14.3 — the pre-flight validator silently repairs a
// broken generation: the user NEVER sees an agent compile error. Turn 1
// proposes a `submit` of code that does NOT compile (unbalanced paren); the
// validator stages → checks → DISCARDS it and re-prompts SILENTLY; turn 2
// proposes code that DOES compile; only the clean form reaches the confirm
// gate and (on `y`) binds. RED-FIRST: the §15/§16 write arm + validator do not
// exist yet — won't-compile / wrong-result is a valid loud signal — flips green
// when /dev 2d lands the rung-5 write arm with the broken-then-fixed stub DSL.
#[cfg(feature = "agent")]
#[test]
fn agent_build_broken_then_fixed_repaired_silently() {
    // `y\n` answers the confirm-gate prompt that the clean form reaches. The
    // broken form must never produce a prompt (it is discarded silently before
    // the echo/gate). After the agent turn, reference `double` via a COMPOUND
    // form `(double 5)` so it routes to the deterministic REPL (a bare `double`
    // would re-route to the agent); a successful eval proves the CLEAN form was
    // the one submitted + bound.
    let out = stub_repl(
        BROKEN_THEN_FIXED_SUBMIT,
        PreludeVariant::PrimitivesOnly,
        "/ask define double\n\
         y\n\
         (double 5)\n",
    );
    // (i) the broken text NEVER appears — neither the broken form nor a
    // compiler error reaches the transcript (the U5 silent contract, §16.2).
    // The broken form is missing its closing paren; the clean form has it. We
    // assert the broken intermediate's compiler-error chatter is absent and
    // that no parse/compile error surfaced for the agent's write.
    assert!(
        !out.stdout.to_lowercase().contains("error"),
        "the broken intermediate must be silently repaired — NO compiler error \
         may reach the transcript (U5 §17.14.3), stdout={}",
        out.stdout
    );
    // (ii) the FIXED form submits + binds: `(double 5)` evals to 10 (5+5), so
    // the clean `(defn double [x] (add-i64 x x))` is now real session state.
    assert!(
        out.stdout.contains("10"),
        "the fixed form must submit + bind — `(double 5)` must eval to 10, \
         proving the clean defn is live, stdout={}",
        out.stdout
    );
    // (iii) `double` is NOT reported unbound afterward (the write committed).
    let after_submit = out.stdout.rsplit("double for you").next().unwrap_or(&out.stdout);
    assert!(
        !after_submit.to_lowercase().contains("unbound")
            && !after_submit.to_lowercase().contains("undefined"),
        "after the silent repair, `double` must be bound (clean form committed), \
         region={after_submit:?}"
    );
}

// spec: repl/spec.md §17.14.3 — +neg (U5 silent contract): the broken
// intermediate form text is structurally ABSENT from the rendered transcript.
// The broken form `(defn double [x] (add-i64 x x)` (unbalanced) must never be
// echoed; only the clean form `(...x x))` reaches the confirm-gate echo. We
// assert the transcript never carries the broken-arity signature — there is
// exactly ONE submitted/echoed form (the clean one), not a stack of attempts.
#[cfg(feature = "agent")]
#[test]
fn agent_build_broken_intermediate_never_shown_neg() {
    let out = stub_repl(
        BROKEN_THEN_FIXED_SUBMIT,
        PreludeVariant::PrimitivesOnly,
        "/ask define double\n\
         y\n",
    );
    // The broken form differs from the clean form only by the missing closing
    // paren. The render path runs ONLY after validate_and_repair returns
    // Ok(clean_form), so the broken form is never echoed. Negative guard: the
    // transcript MUST NOT carry the validator's internal retry chatter — no
    // "repair", "retry", "attempt", or compiler-diagnostic text leaks (§16.2).
    let lc = out.stdout.to_lowercase();
    assert!(
        !lc.contains("parse error")
            && !lc.contains("unbalanced")
            && !lc.contains("unexpected"),
        "the broken intermediate's compiler diagnostic must be ABSENT — the user \
         structurally cannot see an agent compile failure (§17.14.3), stdout={}",
        out.stdout
    );
    // The agent's terminal prose still renders (so the absence above is real
    // coverage, not an empty transcript): the clean form was submitted.
    assert!(
        out.stdout.contains("\u{258c}"),
        "the agent answer must have rendered (framed), stdout={}",
        out.stdout
    );
}

/// The cap-exhausted give-up script: FOUR consecutive broken `submit`s (each an
/// unbalanced paren → parse Err → re-prompt). The repair loop (MAX_REPAIR_
/// ITERATIONS = 3) validates the outer submit + drives 3 repair completions, all
/// broken ⇒ cap exhausted ⇒ give-up. A trailing `done:` is harmless (the give-up
/// returns first). This is the EXACT shape that 400'd live (`messages.4 …
/// unexpected tool_use_id`): the trailing repair tool_use's give-up tool_result.
#[cfg(feature = "agent")]
const CAP_EXHAUSTED_GIVE_UP: &str = "tool: submit (defn never [x] x\n\
     tool: submit (defn never [x] x\n\
     tool: submit (defn never [x] x\n\
     tool: submit (defn never [x] x\n\
     done: I tried but could not\n";

// spec: repl/spec.md §17.14.4 — the CAP-EXHAUSTED GIVE-UP path, e2e: this is the
// live 400 that triggered the Phase-6 work. Three consecutive broken `submit`s
// exhaust the silent-repair cap (§16.3); the agent gives up gracefully ("I
// couldn't produce a definition that compiles cleanly…", §16.4) — it NEVER
// submits broken code and never surfaces a raw compiler error. CRITICAL: the
// give-up transcript must stay wire-valid (the `mod.rs` assemble_request
// `debug_assert!(assert_transcript_wire_valid)` guard executes on THIS path in
// the debug binary) — a malformed give-up transcript would panic the subprocess
// (non-zero exit), so a clean exit proves the guard fired green at the seam,
// catching the `messages.4` 400 in CI instead of at the live API.
#[cfg(feature = "agent")]
#[test]
fn agent_build_cap_exhausted_give_up_stays_wire_valid() {
    // `--yes` so the (never-reached) confirm gate would auto-accept; the give-up
    // is in the validator-repair loop, BEFORE any gate. No `y` line is piped.
    let out = stub_repl_flags(
        CAP_EXHAUSTED_GIVE_UP,
        PreludeVariant::PrimitivesOnly,
        &["--yes"],
        "/ask define never\n\
         (never 1)\n",
    );
    // (i) THE WIRE-VALIDITY GUARD (the primary signal): the subprocess exited
    // cleanly with NO wire-validity panic. A malformed give-up transcript would
    // trip the `assert_transcript_wire_valid` debug_assert at assemble_request
    // (the give-up path assembles a follow-up request) and panic the debug binary
    // — a non-zero exit + a `not wire-valid` stderr. A clean exit proves the guard
    // fired green: the give-up transcript is wire-paired, so the live `messages.4`
    // `unexpected tool_use_id` 400 is unreachable from this path.
    assert!(
        !out.stderr.contains("not wire-valid"),
        "the wire-validity guard must NOT fire on the give-up path — a `messages.4` \
         400 is a debug-binary panic here; stderr={}",
        out.stderr
    );
    assert!(
        out.status.success(),
        "the give-up path must keep the transcript wire-valid — a malformed \
         transcript would panic the debug binary's assemble_request guard; \
         exit={:?}, stderr={}",
        out.status,
        out.stderr
    );
    // (ii) Phase-6 (S89) corrected give-up semantics: the per-submit cap
    // exhaustion feeds the MODEL an honest abort (so it can adapt), but the
    // USER-facing "couldn't produce a definition" line is decided ONLY at TRUE
    // turn-end and ONLY when the turn produced nothing. Here the loop continues
    // after the give-up and reaches the scripted `done: I tried but could not`
    // ANSWER — so the turn DID produce an answer, and the give-up line must NOT
    // appear (it would be false, the live-trace defect this work fixed). The
    // model's answer is what renders instead. (FIXME 0431 → /qa: this test
    // previously asserted the false mid-turn give-up line; corrected with the fix.)
    assert!(
        !out.stdout.contains("couldn't produce a definition"),
        "a turn that ends on a Done answer must NOT show the give-up line, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("I tried but could not"),
        "the model's terminal answer must render in the frame, stdout={}",
        out.stdout
    );
    // (iii) NO raw compiler error leaked across the three broken attempts (§16.2).
    assert!(
        !out.stdout.to_lowercase().contains("parse error")
            && !out.stdout.to_lowercase().contains("unbalanced")
            && !out.stdout.to_lowercase().contains("unexpected"),
        "the broken attempts must be silently discarded — NO compiler diagnostic \
         may leak on the give-up path (§16.2), stdout={}",
        out.stdout
    );
    // (iv) the give-up committed NOTHING — `never` stays unbound (`(never 1)`
    // routes to the deterministic REPL via the compound form and is unbound).
    assert!(
        out.stdout.to_lowercase().contains("unbound")
            || out.stdout.to_lowercase().contains("undefined")
            || out.stdout.to_lowercase().contains("unknown"),
        "a cap-exhausted give-up must write NOTHING — `never` must stay unbound, \
         stdout={}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// B.2 — read-only floor +neg: declined submit makes no change; non-read tool
// never reaches `eval` (§15.4).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.14.2 — On decline, NOTHING is written: a `submit`
// whose `[y/N]` confirm-gate is DECLINED mutates nothing — the proposed name
// stays unbound, structurally identical to the S88 "proposed, not submitted"
// floor (§17.3.1). RED-FIRST until the confirm-gated write arm lands.
#[cfg(feature = "agent")]
#[test]
fn agent_build_declined_submit_no_change_neg() {
    // The clean form reaches the confirm gate; the user declines with `n`.
    // Then `(declinee 1)` is referenced via a COMPOUND form (so it routes to
    // the deterministic REPL) — it must be unbound (the decline wrote nothing).
    let out = stub_repl(
        "tool: submit (defn declinee [x] (add-i64 x 1))\n\
         done: proposed declinee\n",
        PreludeVariant::PrimitivesOnly,
        "/ask define declinee\n\
         n\n\
         (declinee 1)\n",
    );
    // The proposed name MUST still be unbound after the decline (no write).
    assert!(
        out.stdout.to_lowercase().contains("unbound")
            || out.stdout.to_lowercase().contains("undefined")
            || out.stdout.to_lowercase().contains("unknown"),
        "a declined submit must write NOTHING — `declinee` must stay unbound \
         (§17.14.2 decline path), stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.14 — +neg (the structural floor §15.4): a non-read,
// non-`submit` tool (e.g. `/sh`) is REFUSED at `synthesize_command` exactly as
// in the S88 read-only MVP — the read ALLOWLIST floor is UNCHANGED; the only
// new write path is the confirm-gated `submit`, everything else still hits the
// read-only refusal WITHOUT any confirm gate. This proves the floor was
// EXTENDED, not loosened. (This holds on HEAD — the S88 floor — so it is the
// standing structural guard the rung-5 write arm must NOT regress.)
#[cfg(feature = "agent")]
#[test]
fn agent_build_non_read_tool_still_refused_neg() {
    let out = stub_repl(
        "tool: sh echo pwned\n\
         done: ok\n",
        PreludeVariant::PrimitivesOnly,
        "/ask run a shell command\n",
    );
    // The shell command is refused at synthesize (no confirm gate offered) and
    // its output never appears — the read-only floor holds for non-`submit`.
    assert!(
        out.stdout.contains("refused"),
        "a non-read, non-submit tool must be refused at synthesize_command, \
         stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("pwned"),
        "the refused shell command must NOT execute (never reaches eval), \
         stdout={}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// B.4 — `--yes` validation-floor (CRITICAL, /arch §7.4 / §20.3): with `--yes`
// ON, a deliberately-broken generation is STILL silently repaired (never
// submitted raw), only the clean form commits, AND no `[y/N]` prompt fires.
// Proves `--yes` skips CONSENT, NOT VALIDATION.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.14.6 — `--yes` auto-answers consent, NOT validation:
// with `--yes` ON, the broken-then-fixed sequence (§17.14.3) STILL repairs
// silently — only the clean form reaches the session — but WITHOUT a `[y/N]`
// prompt (auto-accepted, §17.14.5). RED-FIRST: the `--yes` threading + the
// validation-floor placement (§20.3) do not exist yet. Note: NO `y\n` is piped
// — under `--yes` the gate auto-accepts, so a stray `y` is not consumed by the
// prompt; the binding is asserted instead via `(double 5)`.
#[cfg(feature = "agent")]
#[test]
fn agent_build_yes_validation_floor_still_repairs() {
    let out = stub_repl_flags(
        BROKEN_THEN_FIXED_SUBMIT,
        PreludeVariant::PrimitivesOnly,
        &["--yes"],
        // No `y` line — `--yes` auto-accepts the confirm gate. After the turn,
        // `(double 5)` proves the CLEAN form (not the broken one) was committed.
        "/ask define double\n\
         (double 5)\n",
    );
    // (a) the broken intermediate is STILL silently repaired — no compiler
    // error reaches the transcript even with `--yes` ON (§17.14.6 / §20.3:
    // `--yes` skips consent, never the validator).
    assert!(
        !out.stdout.to_lowercase().contains("error"),
        "with `--yes` ON the broken generation must STILL be silently repaired \
         — NO compiler error may surface (the validation floor holds, §17.14.6), \
         stdout={}",
        out.stdout
    );
    // (b) only the CLEAN form commits — `(double 5)` evals to 10. A `--yes`
    // that skipped validation would submit the raw broken form and `double`
    // would never bind (the conflation defect §20.3 names).
    assert!(
        out.stdout.contains("10"),
        "with `--yes` ON only the CLEAN repaired form may commit — `(double 5)` \
         must eval to 10; a raw-broken submit would leave `double` unbound \
         (§17.14.6 — never submit raw), stdout={}",
        out.stdout
    );
    // (c) NO `[y/N]` prompt fires — the consent gate is auto-accepted (§17.14.5).
    assert!(
        !out.stdout.contains("[y/N]") && !out.stdout.to_lowercase().contains("[y/n]"),
        "under `--yes` the `[y/N]` confirm prompt must NOT appear — consent is \
         auto-accepted (§17.14.5), stdout={}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// B.5 (agent-lane half) — `--yes` accepted-no-op under `--no-agent` (agent
// build, but the agent is disabled): `--yes` is inert, accepted, never an
// error; the session evals as today. The DEFAULT-build half is in the default
// lane below (NOT `#[cfg(feature="agent")]`).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §0.6.2 — `--yes` with `--no-agent` (no active agent) is an
// accepted no-op: never `unknown flag`, the session behaves exactly as today.
#[cfg(feature = "agent")]
#[test]
fn agent_yes_with_no_agent_is_accepted_no_op() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--no-agent")
        .cli_flag("--yes")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(
        !out.stderr.contains("unknown flag"),
        "`--yes` with `--no-agent` must be accepted (no active agent to \
         escalate), stderr={}",
        out.stderr
    );
    assert!(
        out.stdout.contains("3"),
        "the session must still eval as today, stdout={}",
        out.stdout
    );
}

// ===========================================================================
// Cluster C — Document mode: durable preamble/docstring edits (S89 Wave 3;
// design/int/agent.md §17, repl/spec.md §17.15, spec/08-modules.md §8.16).
// RED-FIRST: these pin the agent's SECOND write class — the **consultative**
// Document edit (set/replace a module preamble, §17.15.1) that records the
// agent's durable understanding into the code itself ("memory is the code",
// §17.15.3). Document mode does NOT exist yet (no `set-preamble`/`set-doc`
// tool, no `run_document_edit` arm, no `apply_preamble_edit` — verified absent
// on HEAD), so these are RED until /dev 3d lands rung 6. None is `#[ignore]`d.
//
// They drive the real binary through the stub-provider-by-config mechanism
// (CRANELISP_AGENT_PROVIDER=stub) so the whole Document write path is exercised
// end-to-end with zero network. The keystone (C.1) closes the memory loop:
// write → save → reload → harvester-reads-it-back, using `run_again()` (a
// fresh session over the same tmpdir) as the cross-session seam.
//
// ---------------------------------------------------------------------------
// THE set-preamble / set-doc STUB-SCRIPT DSL — the contract /dev 3d MUST
// implement (verbatim). This EXTENDS the existing one-scripted-turn-per-line
// DSL (src/CLAUDE.md, agent-testing-strategy.md §1.1) with the TWO Document
// write tools, in the SAME `tool:` form. As with `submit` (Cluster B), the
// tool NAME is the discriminator (§17.2): `submit` is code (confirm gate);
// `set-preamble`/`set-doc` are documentation (consultative gate).
//
//     tool: set-preamble <MODULE> <TEXT>
//         → a `set-preamble` ToolCalls response. The argument is split on the
//           FIRST run of whitespace: the FIRST token is <MODULE> (the module
//           whose preamble to record, e.g. `user`); the REST of the line,
//           verbatim, is <TEXT> — the STRIPPED preamble prose (NO leading `;;`,
//           NO comment markers). The agent renders the proposed canonical
//           leading `;;` block (via `generate_preamble`, §17.5.2), asks the
//           CONSULTATIVE question ("record this as <MODULE>'s preamble?"), and
//           on confirm calls `apply_preamble_edit(MODULE, TEXT)` (§17.1) +
//           regenerates the module's backing file (byte-stable §8.16.5).
//
//     tool: set-doc <SYMBOL> <TEXT>
//         → a `set-doc` ToolCalls response. The argument is split on the FIRST
//           whitespace: the FIRST token is <SYMBOL> (the definition whose
//           docstring to record); the REST is <TEXT> — the docstring prose.
//           Same consultative gate ("record this as <SYMBOL>'s docstring?").
//           (C.1/C.2/C.3 exercise `set-preamble`; the `set-doc` shape is
//           defined here for /dev 3d completeness — same line grammar, same
//           consultative gate, same tool-name discrimination.)
//
// A multi-line TEXT preamble is NOT expressed within one line; a single
// `set-preamble` records a single-line-or-`\n`-joined preamble text. The
// canonical C.1 script records a one-line preamble:
//
//     tool: set-preamble user Solver core: constraint propagation over a grid.
//     done: recorded the module preamble for you
//
// Line 1 is the Document write (consultative gate → on confirm, writes the
// `;; Solver core: constraint propagation over a grid.` leading block into
// `user.cl` + regenerates byte-stably). Line 2 is the terminal prose after the
// edit. Minimal + consistent with the existing `tool:`/`done:` DSL — the new
// tools are just two tool names whose argument splits MODULE/SYMBOL ⊕ TEXT.
// **/dev 3d must implement EXACTLY this format** (the stub parses
// `tool: set-preamble <MODULE> <TEXT>` / `tool: set-doc <SYMBOL> <TEXT>` into
// the respective ToolCalls; `run_pull`'s head routes both to the consultative
// `run_document_edit` arm by tool name — §17.2).
// ---------------------------------------------------------------------------

/// The canonical C.1 Document-edit script (the DSL above): a single
/// `set-preamble` recording a one-line preamble on the `user` module, then the
/// terminal prose. The recorded prose is STRIPPED (no `;;`); the regen emits
/// the canonical `;; <prose>` leading block.
#[cfg(feature = "agent")]
const SET_PREAMBLE_USER: &str =
    "tool: set-preamble user Solver core: constraint propagation over a grid.\n\
     done: recorded the module preamble for you\n";

/// The stripped preamble prose the script records (no `;;`), and its canonical
/// regenerated leading-comment-block form (`;; ` + prose, §8.16.2/§8.16.5).
#[cfg(feature = "agent")]
const PREAMBLE_PROSE: &str = "Solver core: constraint propagation over a grid.";
#[cfg(feature = "agent")]
const PREAMBLE_BLOCK: &str = ";; Solver core: constraint propagation over a grid.";

// ---------------------------------------------------------------------------
// C.1 — the keystone: durable round-trip + harvester read-back.
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.16.5 — a Document-mode preamble edit (i) WRITES
// the preamble into the module source as the leading `;;` comment block, and
// (ii) ROUND-TRIPS byte-stably through save→reload: the regenerated `user.cl`
// carries the exact canonical block, and re-reading it (the inverse capture)
// recovers the same prose. RED-FIRST: the `set-preamble` Document tool +
// `apply_preamble_edit` + the section-0 regen wiring do not exist yet (rung 6),
// so the consultative gate is never reached and `user.cl` carries no preamble —
// flips green when /dev 3d lands the Document edit arm.
#[cfg(feature = "agent")]
#[test]
fn agent_document_preamble_edit_round_trips_byte_stable() {
    // A defn is submitted first so the module has a backing file to regenerate;
    // then the agent records the preamble; `y` confirms the consultative gate.
    let out = stub_repl(
        SET_PREAMBLE_USER,
        PreludeVariant::PrimitivesOnly,
        "(defn solve [g] g)\n\
         /ask record what this module does\n\
         y\n",
    );
    // (i) the edit is written into the module SOURCE — the regenerated backing
    // file `user.cl` (in the binary's cwd = the per-test tmpdir) carries the
    // canonical leading `;;` block at the head of the file (§8.16.1/§8.16.5).
    let user_cl = std::fs::read_to_string(out.tmpdir.join("user.cl"))
        .expect("the module backing file `user.cl` must exist after the edit");
    assert!(
        user_cl.contains(PREAMBLE_BLOCK),
        "the preamble edit must write the canonical leading `;;` block into the \
         module source (§8.16.5), user.cl={user_cl:?}"
    );
    // The preamble is the LEADING block (section 0, above the first form) — it
    // precedes the `solve` definition in the regenerated file (§8.16.1).
    let block_at = user_cl.find(PREAMBLE_BLOCK);
    let solve_at = user_cl.find("solve");
    assert!(
        matches!((block_at, solve_at), (Some(b), Some(s)) if b < s),
        "the preamble block must be the LEADING section-0 block, above the first \
         form (§8.16.1), user.cl={user_cl:?}"
    );
    // (ii) byte-stable round-trip: the consultative gate echoes the EXACT block
    // it proposes (§17.15.1 "show exactly what it proposes to record"), and the
    // written block re-reads to the same prose. We assert the proposed block is
    // shown verbatim in the transcript (the inverse-pair `;; <prose>` form).
    assert!(
        out.stdout.contains(PREAMBLE_BLOCK),
        "the consultative gate must show the EXACT canonical `;;` block it \
         proposes to record (§17.15.1), stdout={}",
        out.stdout
    );
    // The regenerated source has NOT reflowed the preamble — exactly ONE
    // canonical block line, not a re-wrapped / re-marked variant (§8.16.5
    // no-reflow). The prose appears once, behind exactly one `;; `.
    assert_eq!(
        user_cl.matches(PREAMBLE_BLOCK).count(),
        1,
        "the preamble must be emitted ONCE as the canonical block — no reflow / \
         duplication (§8.16.5), user.cl={user_cl:?}"
    );
}

// spec: repl/spec.md §17.15.3 — the durable-memory promise ("next session it
// remembers"): after the Document edit + regen, a FRESH session loads the
// regenerated `user.cl`, `apply_module_preamble` captures the section-0 block
// back into `SymbolTable.module_preamble` on load, and the next turn's harvest
// carries the recorded preamble text into the assembled request (rung 6 write →
// rung 3 read, no new harvest code). The observable seam is the `/context`
// dump's `=== HARVESTED CONTEXT ===` section in the fresh session: with the
// edited module MENTIONED, its preamble surfaces (harvest.rs reads
// `module_preamble` for mentioned modules, §5.2 #2). RED-FIRST: the write side
// (rung 6) does not exist, so the fresh session finds no preamble to read back.
#[cfg(feature = "agent")]
#[test]
fn agent_document_harvester_reads_edited_preamble_back() {
    // Session 1: define + record the preamble (confirm the consultative gate).
    let first = stub_repl(
        SET_PREAMBLE_USER,
        PreludeVariant::PrimitivesOnly,
        "(defn solve [g] g)\n\
         /ask record what this module does\n\
         y\n",
    );
    // Sanity: session 1 actually wrote the backing file with the preamble (so
    // the read-back below is a genuine cross-session test, not an empty start).
    let user_cl = std::fs::read_to_string(first.tmpdir.join("user.cl"))
        .expect("session 1 must leave a `user.cl` backing file");
    assert!(
        user_cl.contains(PREAMBLE_BLOCK),
        "session 1 must have recorded the preamble into `user.cl`, user.cl={user_cl:?}"
    );

    // Session 2 (run_again — a FRESH binary over the SAME tmpdir, so `user.cl`
    // is loaded from disk): mention the `user` module in the conversation, then
    // dump the assembled context. The harvest must carry the preamble read back
    // from the regenerated file (§17.15.3 / §8.16.4).
    let second = first
        .run_again()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent")
        .env("CRANELISP_AGENT_PROVIDER", "stub");
    // No script tool-calls needed for the read-back; an empty script keeps the
    // stub well-formed (the /context dump is pure — no completion is issued).
    let script_path = second.tmpdir_path().join("agent_script2.txt");
    std::fs::write(&script_path, "done: ok\n").unwrap();
    let out = second
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        // Mention `user` (the edited module) so the harvest includes its
        // mentioned-module preamble block (§5.2 #2), then dump the context.
        .stdin("/ask tell me about the user module\n/context ctx2.txt\n")
        .output();
    assert!(
        out.stdout.contains("wrote agent context to ctx2.txt"),
        "the /context dump must succeed in the fresh session, stdout={}",
        out.stdout
    );
    let dumped = std::fs::read_to_string(out.tmpdir.join("ctx2.txt"))
        .expect("the fresh-session /context file must exist");
    // The harvested context of the FRESH session carries the preamble text that
    // session 1 recorded — the durable-memory loop is closed (§17.15.3).
    assert!(
        dumped.contains(PREAMBLE_PROSE),
        "the fresh session's harvester must read the recorded preamble back into \
         the assembled context (durable memory, §17.15.3), dumped={dumped}"
    );
}

// ---------------------------------------------------------------------------
// C.2 — consent decline +neg (Document consultative gate).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.15.2 — On decline, NOTHING is written: a
// `set-preamble` whose CONSULTATIVE gate is declined (`n` to "record this as
// <module>'s preamble?") leaves the module source unmodified — no preamble
// block is written and no regen fires. The Document twin of B.2's declined
// Build `submit` (`agent_build_declined_submit_no_change_neg`, Cluster B) — the
// confirm and consultative gates are discriminated by tool NAME (§17.2), but
// both decline paths are no-ops on session/source state. RED-FIRST until the
// Document edit arm + its decline path land.
#[cfg(feature = "agent")]
#[test]
fn agent_document_declined_preamble_edit_no_change_neg() {
    // The consultative gate is reached; the user declines with `n`. The module
    // source must remain free of the proposed preamble block.
    let out = stub_repl(
        SET_PREAMBLE_USER,
        PreludeVariant::PrimitivesOnly,
        "(defn solve [g] g)\n\
         /ask record what this module does\n\
         n\n",
    );
    // If a backing file exists at all (the `solve` defn regen may write one), it
    // MUST NOT carry the declined preamble block — the decline wrote nothing
    // (§17.15.2). Read it leniently: absence-of-file is also "no preamble".
    let user_cl = std::fs::read_to_string(out.tmpdir.join("user.cl")).unwrap_or_default();
    assert!(
        !user_cl.contains(PREAMBLE_BLOCK),
        "a DECLINED preamble edit must write NOTHING — the module source must not \
         carry the proposed `;;` block (§17.15.2 decline path), user.cl={user_cl:?}"
    );
    // And the proposed prose must not appear as a recorded preamble anywhere in
    // the regenerated source (no partial/uncommented write either).
    assert!(
        !user_cl.contains(PREAMBLE_PROSE),
        "a declined preamble edit must leave the module source byte-identical to \
         the pre-edit state (no preamble recorded), user.cl={user_cl:?}"
    );
}

// ---------------------------------------------------------------------------
// C.3 — `--yes` covers Document (blanket auto-accept).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.15.2a — `--yes` is BLANKET: it auto-accepts the
// Document consultative gate exactly as it auto-accepts the Build confirm gate
// (§17.14.5). With `--yes` ON, the `set-preamble` is applied WITHOUT the
// "record this as <module>'s preamble?" consultation firing — proving the
// blanket flag covers Document writes, not just Build. The proposed block is
// STILL shown (§17.15.2a render-always); only the consultative question is
// suppressed. RED-FIRST: the `--yes` threading into the Document gate (§20.2)
// does not exist yet. Note: NO `y` line is piped — `--yes` auto-accepts.
#[cfg(feature = "agent")]
#[test]
fn agent_document_yes_auto_accepts_preamble_edit() {
    let out = stub_repl_flags(
        SET_PREAMBLE_USER,
        PreludeVariant::PrimitivesOnly,
        &["--yes"],
        // No `y` line — `--yes` auto-accepts the consultative gate.
        "(defn solve [g] g)\n\
         /ask record what this module does\n",
    );
    // (a) the edit was applied WITHOUT a consultative prompt — the
    // "record this as ...'s preamble?" question must NOT appear (auto-accepted,
    // §17.15.2a). It is suppressed, not asked-then-auto-answered.
    let lc = out.stdout.to_lowercase();
    assert!(
        !lc.contains("record this as"),
        "under `--yes` the Document consultative question must NOT fire — the \
         gate is auto-accepted (§17.15.2a), stdout={}",
        out.stdout
    );
    // (b) the edit was nonetheless APPLIED — the regenerated `user.cl` carries
    // the canonical preamble block (proving `--yes` covers Document writes, not
    // just Build; the blanket flag, §17.15.2a).
    let user_cl = std::fs::read_to_string(out.tmpdir.join("user.cl"))
        .expect("the module backing file must exist after the auto-accepted edit");
    assert!(
        user_cl.contains(PREAMBLE_BLOCK),
        "under `--yes` the preamble edit must STILL be applied (blanket auto-accept \
         covers Document, §17.15.2a), user.cl={user_cl:?}"
    );
    // (c) the proposed block is STILL shown (§17.15.2a render-always: `--yes` is
    // trust, not silence — the user always sees the documentation recorded).
    assert!(
        out.stdout.contains(PREAMBLE_BLOCK),
        "under `--yes` the proposed `;;` block must STILL be shown before the \
         auto-accepted write (§17.15.2a render-always), stdout={}",
        out.stdout
    );
}
