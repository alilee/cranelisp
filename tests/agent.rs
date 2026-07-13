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

// spec: repl/spec.md §0.6.1 — S106 user ruling: `--agent` on a binary built
// WITHOUT the agent feature MUST be a HARD ERROR (usage hint to stderr, exit 1),
// NOT an accepted no-op — the flag names a capability the binary does not have.
// It MUST NOT print `unknown flag` (a recognised flag rejected for a specific
// reason). RED on HEAD (FIXME 0539): the default build currently accepts `--agent`
// as a no-op. (Flipped from the pre-S106 `agent_flag_accepted_not_unknown`.)
#[cfg(not(feature = "agent"))]
#[test]
fn agent_flag_errors_on_non_agent_build() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert_eq!(
        out.status.code(),
        Some(1),
        "--agent on a non-agent build MUST exit 1 (§0.6.1, FIXME 0539); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr.contains("--agent"),
        "--agent rejection MUST print a usage hint naming the flag to stderr; stderr={}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("unknown flag"),
        "--agent is a RECOGNISED flag rejected for a reason, NOT `unknown flag`; stderr={}",
        out.stderr
    );
    // +neg: the session MUST NOT start — the flag is rejected before eval.
    assert!(
        !out.stdout.contains(":primitives/Int 3"),
        "--agent on a non-agent build MUST NOT start the session; stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §0.6.1 — on an agent-CAPABLE build `--agent` stays accepted
// (a request to enable the agent), a no-op in the byte-identical sense here. The
// feature-not-compiled-in reversal (FIXME 0539) is scoped to the non-agent build.
#[cfg(feature = "agent")]
#[test]
fn agent_flag_accepted_on_agent_build() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(
        !out.stderr.contains("unknown flag"),
        "--agent must be accepted on an agent build, stderr={}",
        out.stderr
    );
    assert!(out.stdout.contains("3"), "session must still eval, stdout={}", out.stdout);
}

// spec: repl/spec.md §0.6.2 — S106 user ruling: `--yes` on a binary built WITHOUT
// the agent feature MUST be a HARD ERROR (usage hint to stderr, exit 1) — there is
// no write-consent gate for it to auto-answer. NOT `unknown flag`. RED on HEAD
// (FIXME 0539): the default build accepts `--yes` as a no-op. (Flipped from the
// pre-S106 `yes_flag_accepted_no_op_default_build`.)
#[cfg(not(feature = "agent"))]
#[test]
fn yes_flag_errors_on_non_agent_build() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--yes")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert_eq!(
        out.status.code(),
        Some(1),
        "`--yes` on a non-agent build MUST exit 1 (§0.6.2, FIXME 0539); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr.contains("--yes") || out.stderr.contains("agent"),
        "`--yes` rejection MUST print a usage hint naming the flag/reason to stderr; stderr={}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("unknown flag"),
        "`--yes` is a RECOGNISED flag rejected for a reason, NOT `unknown flag`; stderr={}",
        out.stderr
    );
}

// spec: repl/spec.md §0.6.2 — `-y` (the short form of `--yes`) MUST likewise be a
// HARD ERROR on a non-agent build (exit 1, usage hint) — same reversal as `--yes`.
// RED on HEAD (FIXME 0539): the default build accepts `-y` today. NOT `unknown
// flag`, and NOT swallowed as the REPL target. (Flipped from the pre-S106
// `y_short_flag_accepted_no_op_default_build`.)
#[cfg(not(feature = "agent"))]
#[test]
fn y_short_flag_errors_on_non_agent_build() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("-y")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert_eq!(
        out.status.code(),
        Some(1),
        "`-y` on a non-agent build MUST exit 1 (§0.6.2, FIXME 0539); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stderr.contains("unknown flag"),
        "`-y` is a RECOGNISED flag rejected for a reason, NOT `unknown flag`; stderr={}",
        out.stderr
    );
    // +neg: `-y` must be parsed as a FLAG, never swallowed as the REPL target.
    assert!(
        !out.stdout.contains("-y>"),
        "`-y` MUST be parsed as a flag, not swallowed as the REPL target; stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §0.6.1 — `--no-agent` is UNAFFECTED by the S106 reversal:
// asking for the agent to be OFF is trivially true on a non-agent build, so it
// stays an accepted no-op (never `unknown flag`, never an error).
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

// spec: repl/spec.md §0.6.1 — NEG anchor of the S106 ruling (FIXME 0539): the
// `--agent`/`--yes` error reversal is SCOPED and MUST NOT over-reach to
// `--no-agent`. On a non-agent build `--no-agent` MUST NOT error (exit 0), MUST NOT
// print `unknown flag`, and the session evals normally. GREEN-expected guard.
#[test]
fn no_agent_flag_still_accepted_no_op_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--no-agent")
        .stdin("(add-i64 1 2)\n")
        .output();
    assert_eq!(
        out.status.code(),
        Some(0),
        "--no-agent MUST NOT error — the reversal is scoped to --agent/--yes \
         (§0.6.1, FIXME 0539); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stderr.contains("unknown flag") && !out.stderr.contains("--no-agent requires"),
        "--no-agent MUST NOT be rejected; stderr={}",
        out.stderr
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "--no-agent session MUST eval normally; stdout={}",
        out.stdout
    );
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
        // `without_agent_provider` strips any ambient key/model so the default
        // anthropic provider cannot go live under the runner's env (S106 hermeticity).
        .without_agent_provider()
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

// spec: repl/spec.md §17.1 — a REPL buffer of EXACTLY ONE form (bare, FQ, or a
// single compound) is code for the deterministic REPL; only ≥2 forms or
// unparseable prose divert to an ACTIVE agent (user ruling 2026-07-12). A single
// bare UNKNOWN symbol (`lenght`) is ONE form, so it MUST reach the deterministic
// REPL and produce its unbound display (`undefined variable: lenght`, §4.1) — it
// MUST NOT route to the agent, even when the agent is ACTIVE. This is the exact
// inverse of the retired "refined classifier resolves the symbol and finds it
// unbound ⇒ route" design (arch ruling e3f7d57), which the §17.1 one-form ruling
// reverses. The stub is ACTIVE to prove it is NOT consulted for one form.
//
// context: §17.1-ruling reconciliation (Sprint 108 Inc3 Wave A) — was
// `agent_on_bare_unknown_symbol_routes_to_agent` asserting the `▌` frame.
#[cfg(feature = "agent")]
#[test]
fn agent_on_bare_unknown_symbol_stays_in_repl_not_routed() {
    let out = stub_repl(
        "done: that is not a defined symbol\n",
        PreludeVariant::PrimitivesOnly,
        "lenght\n",
    );
    // The deterministic REPL unbound display is produced …
    assert!(
        out.stdout.contains("undefined variable: lenght"),
        "a single bare unknown symbol MUST reach the deterministic REPL and \
         produce its unbound display (§17.1 one-form rule; §4.1), stdout={}",
        out.stdout
    );
    // … and the ACTIVE stub agent MUST NOT have been consulted (no frame) …
    assert!(
        !out.stdout.contains("\u{258c}"),
        "a single bare unknown symbol MUST NOT route to the agent frame (§17.1 \
         one-form rule reverses the retired refined-classifier route), stdout={}",
        out.stdout
    );
    // … nor its scripted reply rendered.
    assert!(
        !out.stdout.contains("that is not a defined symbol"),
        "the agent (stub) MUST NOT be consulted for a single bare unknown symbol, \
         stdout={}",
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

// ---------------------------------------------------------------------------
// S108 (Increment 3) — E6 + candidate B: the §17.1 one-form routing rule.
// The deterministic `classify_for_agent` unit pins are /dev's Wave A; these are
// the two e2e ROUTING guards through the real binary with an ACTIVE stub agent —
// ONE pair, not the whole matrix (SPRINT.md §E6 e2e companion).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.1 — E6: a natural-language sentence containing an
// apostrophe (`why doesn't that typecheck?`) parses to ≥2 forms (the `'` in
// `doesn't` is the quote reader-macro → `doesn` + `(quote t)`), so under the §17.1
// user ruling (>1 form → the agent if active) it MUST route to the ACTIVE agent —
// rendered in the `▌` prose frame — and MUST NOT be evaluated to a silent
// `:primitives/Int 0`. RED on HEAD: the `any_compound → Repl` heuristic misroutes
// the sentence to eval, printing `:primitives/Int 0`; the stub is never consulted.
//
// defect: class=routing-misclassify locus=src/agent/mod.rs::classify_for_agent (any_compound arm) found=S108 owner=/dev
#[cfg(feature = "agent")]
#[test]
fn agent_on_nl_prose_with_contraction_routes_to_agent() {
    let out = stub_repl(
        "done: to fix that add a type annotation\n",
        PreludeVariant::PrimitivesOnly,
        "why doesn't that typecheck?\n",
    );
    // Routes to the ACTIVE agent — framed prose, and the stub WAS consulted.
    assert!(
        out.stdout.contains("\u{258c}"),
        "a multi-form NL sentence (`'` splits `doesn't` into ≥2 forms) MUST route \
         to the ACTIVE agent frame (§17.1 >1-form rule), stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("to fix that add a type annotation"),
        "the agent (stub) MUST be consulted and its reply rendered, stdout={}",
        out.stdout
    );
    // The load-bearing negative: NOT misrouted to eval as a silent `:Int 0`.
    assert!(
        !out.stdout.contains(":primitives/Int 0"),
        "the sentence MUST NOT be evaluated to a silent `:primitives/Int 0` (the E6 \
         misroute); stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.1 — candidate B: a single FULLY-QUALIFIED symbol
// (`primitives/vec-len`) parses to EXACTLY one form, so it routes to the
// deterministic REPL and INTROSPECTS (§4) — independent of `symbol_is_known` — and
// MUST NOT route to the agent. The stub agent is ACTIVE but MUST NOT be consulted.
// RED on HEAD: a single FQ symbol routes to the agent (its `symbol_is_known` bare
// lookup misses the FQ name → the `all_known` gate diverts it), so the stub reply
// renders in the `▌` frame instead of the introspection line.
//
// defect: class=routing-misclassify locus=src/agent/mod.rs::classify_for_agent (single-FQ-form arm) found=S108 owner=/dev
#[cfg(feature = "agent")]
#[test]
fn agent_on_single_fq_symbol_introspects_not_routed_to_agent() {
    let out = stub_repl(
        "done: STUB-WAS-CONSULTED\n",
        PreludeVariant::None,
        "primitives/vec-len\n",
    );
    // The deterministic §4 introspection/value line is produced …
    assert!(
        out.stdout.contains(":(Fn") && out.stdout.contains("primitives/Int"),
        "a single FQ symbol MUST route to the deterministic REPL and introspect \
         (§17.1 one-form rule; §4), not the agent; stdout={}",
        out.stdout
    );
    // … and the ACTIVE stub agent MUST NOT have been consulted.
    assert!(
        !out.stdout.contains("\u{258c}"),
        "a single FQ symbol MUST NOT route to the agent frame (candidate B); \
         stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("STUB-WAS-CONSULTED"),
        "the agent (stub) MUST NOT be consulted for a single FQ symbol — it \
         introspects deterministically; stdout={}",
        out.stdout
    );
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
        // Force the anthropic provider with no key → dormant. `without_agent_provider`
        // strips any ambient ANTHROPIC_API_KEY / CRANELISP_AGENT_MODEL so the runner's
        // env cannot make the forced provider go live (harness hermeticity, S106).
        .without_agent_provider()
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
    // (c) S107 re-baseline (§17.2 item 3, FIXME 0556): the ```lisp code lines
    // MUST be copy-clean — NO per-line `▌` gutter on any code line. Identify the
    // code lines by the code-only token `add-i64` (never in the prose) and assert
    // none carries the gutter. RED on HEAD: today the fence line renders as
    // `▌ (defn double …)`; GREEN when the item-3 render split lands.
    let guttered_code: Vec<&str> = out
        .stdout
        .lines()
        .filter(|l| l.contains("add-i64") && l.contains('\u{258c}'))
        .collect();
    assert!(
        guttered_code.is_empty(),
        "agent ```lisp code lines MUST be un-guttered (`▌`-free) so they copy \
         clean (§17.2 item 3, FIXME 0556); found guttered code line(s): {:?}\n\
         stdout={}",
        guttered_code,
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
    // S107 re-baseline (§17.2 item 3, FIXME 0556): the pretty-printed code lines
    // MUST carry NO `▌` gutter (copy-clean). The gutter glyph `▌` is a raw byte
    // regardless of colour, so the check holds in both colour modes. RED on HEAD
    // (the fence line renders `▌ (defn double …)`); GREEN with the render split.
    let guttered_code: Vec<&str> = out
        .stdout
        .lines()
        .filter(|l| l.contains("add-i64") && l.contains('\u{258c}'))
        .collect();
    assert!(
        guttered_code.is_empty(),
        "the pretty-printed ```lisp code lines MUST be un-guttered (`▌`-free) \
         (§17.2 item 3, FIXME 0556); found guttered code line(s): {:?}\nstdout={}",
        guttered_code,
        out.stdout
    );
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
    // (5) S107 re-baseline (§17.13.3 whole-session golden; §17.2 item 3, FIXME
    // 0556): the ```lisp code lines are gutter-free (copy-clean) while the prose
    // lines keep their `▌` gutter — the render split is code-only. RED on HEAD
    // (the fence line renders `▌ (defn target …)`); GREEN with the render split.
    let guttered_code: Vec<&str> = out
        .stdout
        .lines()
        .filter(|l| l.contains("add-i64") && l.contains('\u{258c}'))
        .collect();
    assert!(
        guttered_code.is_empty(),
        "the ```lisp code lines MUST be un-guttered (`▌`-free) (§17.2 item 3); \
         found guttered code line(s): {:?}\nstdout={}",
        guttered_code,
        out.stdout
    );
    // The surrounding PROSE keeps its gutter (the split is code-only): the prose
    // sentence carrying "cleaner version" MUST be guttered.
    assert!(
        out.stdout
            .lines()
            .any(|l| l.contains("cleaner version") && l.contains('\u{258c}')),
        "agent prose lines MUST keep the `▌` gutter (code-only split, §17.2 item \
         3); the prose line carrying \"cleaner version\" must be guttered.\n\
         stdout={}",
        out.stdout
    );
}

// ===========================================================================
// S107 item 3 — FIXME 0556: agent gutter copy shape (repl/spec.md §17.2 item 3,
// §17.13.2 "Copy-clean, un-guttered [S107]", §10.3). Normative MUST: agent-
// emitted ```lisp / ```cranelisp code fences render with NO per-line `▌` gutter
// on any code line, and the code block's bytes are byte-identical (colour-off)
// to `/sexp` / `pretty_print_str` for the same form — nothing prepended.
// Surrounding PROSE lines keep their `▌` gutter (the split is code-only).
//
// RED on HEAD: `src/style.rs::agent_prose` gutters EVERY line via `text.lines()`,
// so today the ```lisp fence line renders `▌ (defn double …)`. Flips GREEN when
// the render-side structural split lands in `src/agent/render.rs` (gutter prose,
// frame code fences un-guttered). Drives the real binary via the stub provider.
// ===========================================================================

/// Extract the `/sexp <name>` pretty-print block from a captured session: the
/// non-empty lines strictly between the `; sexp for <name>` marker line and the
/// next REPL prompt. These lines are emitted clean (no prompt prefix) by the
/// pretty-printer, so they are the byte-exact deterministic reference for the
/// agent-fence parity check.
#[cfg(feature = "agent")]
fn sexp_block(stdout: &str, name: &str) -> Vec<String> {
    let marker = format!("; sexp for {name}");
    let mut lines = stdout.lines();
    for l in lines.by_ref() {
        if l.contains(&marker) {
            break;
        }
    }
    let mut block = Vec::new();
    for l in lines {
        // A prompt line ends the pretty-print block.
        if l.contains("ms; user>") {
            break;
        }
        if l.trim().is_empty() {
            continue;
        }
        block.push(l.to_string());
    }
    block
}

// spec: repl/spec.md §17.2 — the core 0556 MUST: an agent ```lisp fence renders
// with NO `▌` gutter on any code line. Identify the code lines by the code-only
// token `add-i64` (never in the prose) and assert none carries the gutter. RED
// on HEAD (all lines guttered via `text.lines()`); GREEN with the render split.
#[cfg(feature = "agent")]
#[test]
fn agent_lisp_fence_code_lines_ungutter_neg() {
    let out = stub_repl_flags(
        "done: Here is a definition:\n\
         prose: ```lisp\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // The turn rendered (framed prose present) — so the absence check is real.
    assert!(
        out.stdout.contains('\u{258c}'),
        "the agent answer must have rendered (framed), stdout={}",
        out.stdout
    );
    // Every CODE line MUST be gutter-free (the core 0556 MUST).
    let guttered_code: Vec<&str> = out
        .stdout
        .lines()
        .filter(|l| l.contains("add-i64") && l.contains('\u{258c}'))
        .collect();
    assert!(
        guttered_code.is_empty(),
        "agent ```lisp code lines MUST carry NO `▌` gutter so they copy clean \
         (§17.2 item 3, FIXME 0556); found guttered code line(s): {:?}\nstdout={}",
        guttered_code,
        out.stdout
    );
}

// spec: repl/spec.md §17.13.2 — byte parity: the rendered agent code block is
// byte-identical (colour-off) to `/sexp` output for the same form (nothing
// prepended). In one session define `double`, capture `/sexp double`, then show
// the same form via an `/ask` ```lisp fence; assert each `/sexp` block line
// appears VERBATIM (gutter-free, full-line-equal) in the agent region. RED on
// HEAD: the agent line is `▌ (defn double …)` — not byte-equal to the un-guttered
// `/sexp` line; GREEN when the fence renders un-guttered through the same printer.
#[cfg(feature = "agent")]
#[test]
fn agent_lisp_fence_bytes_equal_sexp_output() {
    let out = stub_repl_flags(
        "done: Here is a definition:\n\
         prose: ```lisp\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "(defn double [x] (add-i64 x x))\n\
         /sexp double\n\
         /ask how do I double a number?\n",
    );
    let block = sexp_block(&out.stdout, "double");
    assert!(
        !block.is_empty(),
        "the /sexp double pretty-print block must be captured; stdout={}",
        out.stdout
    );
    // The agent region is everything from the terminal prose onward (excludes the
    // earlier /sexp echo so the parity check targets the agent-rendered fence).
    let agent_start = out
        .stdout
        .find("Here is a definition")
        .expect("the agent prose must render");
    let agent_region = &out.stdout[agent_start..];
    for bl in &block {
        assert!(
            agent_region.lines().any(|al| al == bl),
            "the agent ```lisp code block MUST be byte-identical (colour-off) to \
             `/sexp` output — nothing prepended (§17.2 item 3, §17.13.2): the \
             /sexp line {bl:?} MUST appear VERBATIM (gutter-free, full line) in \
             the agent region.\n--- /sexp block ---\n{block:#?}\n\
             --- agent region ---\n{agent_region}"
        );
    }
}

// spec: repl/spec.md §17.2 — the split is CODE-ONLY: the surrounding prose lines
// (before AND after the fence) MUST still carry the `▌` gutter. GREEN today
// (prose is guttered) and MUST stay GREEN across the fix (the un-guttering is
// scoped to code lines, never the prose framing).
#[cfg(feature = "agent")]
#[test]
fn agent_prose_lines_keep_gutter() {
    let out = stub_repl_flags(
        "done: Here is a definition:\n\
         prose: ```lisp\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n\
         prose: That defines double.\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // The prose line BEFORE the fence keeps its gutter.
    assert!(
        out.stdout
            .lines()
            .any(|l| l.contains("Here is a definition") && l.contains('\u{258c}')),
        "the prose line before the fence MUST keep its `▌` gutter (code-only \
         split, §17.2 item 3); stdout={}",
        out.stdout
    );
    // The prose line AFTER the fence keeps its gutter too.
    assert!(
        out.stdout
            .lines()
            .any(|l| l.contains("That defines double") && l.contains('\u{258c}')),
        "the prose line after the fence MUST keep its `▌` gutter (code-only \
         split, §17.2 item 3); stdout={}",
        out.stdout
    );
}

// ===========================================================================
// S107 item 4 — FIXME 0555: streaming the agent's terminal answer
// (`--features agent`; repl/spec.md §17.22). The terminal `Done` prose streams
// line-by-line as deltas arrive; a ```lisp fence is BUFFERED while open and
// emitted formatted + un-guttered at fence-close; tool-call turns are NOT
// streamed (explicit seam). The load-bearing MUST is the DIFFERENTIAL INVARIANT:
// streamed-then-concatenated output is byte-identical (colour-off) to the
// single-shot render of the same answer — streaming changes only WHEN bytes
// reach the screen, never WHICH bytes.
//
// The streaming impl (arch S1–S5) is landed and the stub `<|delta|>` DSL
// (`src/agent/stub.rs::DELTA_SPLIT`, FIXME 0555 — G-1 unblocked) scripts MULTIPLE
// deltas within one terminal turn, including a boundary INSIDE a ```lisp fence.
// These five e2e are GREEN against the landed impl (integration confirmation);
// the load-bearing pure `== render_agent_prose` differential test is the
// by-construction unit test in `src/agent/render.rs` (per G-1 the test infra was
// impl, so these e2e are not failing-first — documented in `tests/plan/ledger.md`).
// They drive the real binary through CRANELISP_AGENT_PROVIDER=stub, zero network.
// ===========================================================================

/// Extract the framed agent-answer region from a captured non-TTY session: from
/// the first `▌` gutter glyph (start of the framed answer) up to — but excluding —
/// the newline before the following REPL prompt. This drops the surrounding
/// `N+Nms; user> ` prompt lines (whose timing varies run-to-run) so the agent
/// region can be compared byte-for-byte across delta chunkings (G-3 — the non-TTY
/// prompt interleaves the capture).
#[cfg(feature = "agent")]
fn agent_answer_region(stdout: &str) -> &str {
    let start = stdout
        .find('\u{258c}')
        .expect("agent answer must render (gutter glyph present)");
    let rest = &stdout[start..];
    // The answer ends at the next REPL prompt (`…; user> `). Trim back to the
    // newline that precedes that prompt line (excludes its variable timing).
    match rest.find("; user>") {
        Some(i) => &rest[..rest[..i].rfind('\n').unwrap_or(0)],
        None => rest,
    }
}

// spec: repl/spec.md §17.22 — the DIFFERENTIAL INVARIANT (the load-bearing MUST,
// e2e proxy): a terminal answer scripted with `<|delta|>` splits (INCLUDING one
// boundary INSIDE the ```lisp fence body) produces final rendered bytes
// byte-identical (colour-off) to the SAME answer scripted as a SINGLE delta.
// Delta chunking changes only WHEN bytes reach the screen, never WHICH bytes:
// same gutter on prose lines, same un-guttered pretty-printed fence. G-3: the
// non-TTY `user> ` prompt interleaves, so assert the framed answer BLOCK as a
// byte-exact SUBSTRING + the extracted agent regions equal each other.
#[cfg(feature = "agent")]
#[test]
fn agent_streaming_bytes_equal_single_shot() {
    // (a) the whole answer as ONE delta (no `<|delta|>` markers — the one-delta /
    // §17.22 Fallback case).
    let single = stub_repl_flags(
        "done: Here is a definition:\n\
         prose: ```lisp\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n\
         prose: That defines double.\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // (b) the SAME answer scripted as MANY deltas — one boundary lands INSIDE the
    // ```lisp fence body (mid-form), one after the leading prose line, one after
    // the opening fence. The marker-stripped full text is identical to (a).
    let multi = stub_repl_flags(
        "done: Here is a definition:<|delta|>\n\
         prose: ```lisp<|delta|>\n\
         prose: (defn double [x]<|delta|> (add-i64 x x))\n\
         prose: ```\n\
         prose: That defines double.\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // The exact framed answer BLOCK: prose lines guttered `▌ `, the pretty-printed
    // ```lisp form on its OWN line UN-guttered, then the trailing prose guttered.
    // (Byte-exact substring per G-3 — the surrounding prompt/timing is excluded.)
    const BLOCK: &str = "\u{258c} Here is a definition:\n\
                         (defn double [x] (add-i64 x x))\n\
                         \u{258c} That defines double.";
    assert!(
        single.stdout.contains(BLOCK),
        "single-delta render must contain the exact framed answer block; stdout={:?}",
        single.stdout
    );
    assert!(
        multi.stdout.contains(BLOCK),
        "multi-delta render must contain the exact framed answer block; stdout={:?}",
        multi.stdout
    );
    // The differential invariant end-to-end: the extracted agent regions are
    // byte-identical across the two chunkings (only WHEN differs, never WHICH). A
    // mismatch here is a REAL streaming defect — not something to paper over.
    let a = agent_answer_region(&single.stdout);
    let b = agent_answer_region(&multi.stdout);
    assert_eq!(
        a, b,
        "streamed (multi-delta) and single-shot agent regions MUST be byte-identical \
         (§17.22 differential invariant)"
    );
    // colour-off cleanliness: no literal escape leaked in either capture.
    assert!(
        !single.stdout.contains(ESC_SGR) && !multi.stdout.contains(ESC_SGR),
        "no literal ANSI escape may leak under --no-color; single={:?} multi={:?}",
        single.stdout,
        multi.stdout
    );
}

// spec: repl/spec.md §17.22 — a ```lisp fence split ACROSS delta boundaries is
// BUFFERED while open and emitted as ONE whole formatted, un-guttered block at
// fence-close: no raw fence markers survive, no half-formatted mid-fence fragment
// appears, and no code line carries the `▌` gutter.
#[cfg(feature = "agent")]
#[test]
fn agent_streaming_fence_emitted_whole_at_close_neg() {
    let out = stub_repl_flags(
        "done: Here is a definition:<|delta|>\n\
         prose: ```lisp<|delta|>\n\
         prose: (defn double [x]<|delta|> (add-i64 x x))\n\
         prose: ```<|delta|>\n\
         prose: That defines double.\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // (a) NO raw fence markers survive — the fence is buffered while open and
    // emitted formatted at fence-close (§17.22 "renders formatted at fence-close").
    assert!(
        !out.stdout.contains("```"),
        "a delta-split ```lisp fence must NOT leak raw fence markers — it is \
         buffered then emitted whole at close (§17.22); stdout={:?}",
        out.stdout
    );
    // (b) the pretty-printed form appears as ONE whole line despite the mid-fence
    // delta boundary (buffer-within-fence: the boundary does not split the form).
    assert!(
        out.stdout
            .lines()
            .any(|l| l == "(defn double [x] (add-i64 x x))"),
        "the fence must render as ONE whole pretty-printed form line despite the \
         mid-fence delta boundary; stdout={:?}",
        out.stdout
    );
    // (c) no code line carries the `▌` gutter (identify code lines by `add-i64`,
    // never in the prose) — the streamed fence is copy-clean.
    let guttered_code: Vec<&str> = out
        .stdout
        .lines()
        .filter(|l| l.contains("add-i64") && l.contains('\u{258c}'))
        .collect();
    assert!(
        guttered_code.is_empty(),
        "the streamed fence code line MUST be un-guttered (`▌`-free); found: {:?}\n\
         stdout={}",
        guttered_code,
        out.stdout
    );
    // (d) +neg: no half-formed mid-fence fragment line surfaces (the mid-fence
    // delta boundary must NOT surface `(defn double [x]` as its own line).
    assert!(
        !out.stdout.lines().any(|l| l.trim() == "(defn double [x]"),
        "no half-formed mid-fence fragment line may surface mid-stream; stdout={:?}",
        out.stdout
    );
    // Sanity: the turn rendered (framed prose present) so the absences are real.
    assert!(
        out.stdout.contains('\u{258c}'),
        "the agent answer must have rendered (framed); stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.22 — a multi-delta terminal answer renders the correct
// final result (the observable proxy; per G-2 true incrementality/timing is not
// observable through the post-exit captured pipe). Assert the rendered result:
// each prose line framed (guttered), IN ORDER, and the fenced code un-guttered +
// whole.
#[cfg(feature = "agent")]
#[test]
fn agent_terminal_answer_streams_incrementally() {
    let out = stub_repl_flags(
        "done: First line.<|delta|>\n\
         prose: Second line.<|delta|>\n\
         prose: ```lisp<|delta|>\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n\
         prose: Third line.\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // Each prose line renders framed (guttered) — the correct final result of the
    // multi-delta streaming path.
    for line in ["First line.", "Second line.", "Third line."] {
        assert!(
            out.stdout
                .lines()
                .any(|l| l.contains(line) && l.contains('\u{258c}')),
            "prose line {line:?} must render guttered (framed); stdout={}",
            out.stdout
        );
    }
    // The fenced form renders whole + un-guttered (copy-clean).
    assert!(
        out.stdout
            .lines()
            .any(|l| l == "(defn double [x] (add-i64 x x))"),
        "the fenced form must render whole + un-guttered; stdout={:?}",
        out.stdout
    );
    let guttered_code: Vec<&str> = out
        .stdout
        .lines()
        .filter(|l| l.contains("add-i64") && l.contains('\u{258c}'))
        .collect();
    assert!(
        guttered_code.is_empty(),
        "code lines MUST be un-guttered; found {:?}\nstdout={}",
        guttered_code,
        out.stdout
    );
    // The streamed prose lines appear IN ORDER in the capture.
    let p1 = out.stdout.find("First line").expect("First line renders");
    let p2 = out.stdout.find("Second line").expect("Second line renders");
    let p3 = out.stdout.find("Third line").expect("Third line renders");
    assert!(
        p1 < p2 && p2 < p3,
        "the streamed prose lines must appear in order; stdout={}",
        out.stdout
    );
    // colour-off clean.
    assert!(
        !out.stdout.contains(ESC_SGR),
        "no literal ANSI escape under --no-color; stdout={:?}",
        out.stdout
    );
}

// spec: repl/spec.md §17.22 — the streaming path applies ONLY to the terminal
// `Done` prose (explicit S107 seam): a turn that issues a TOOL CALL is NOT
// streamed — its pull command + result render as today (unframed pull with the
// `agent>` prompt, after the tool runs); only the terminal `Done` prose that
// follows streams framed. Pins the seam boundary.
#[cfg(feature = "agent")]
#[test]
fn agent_tool_call_turn_not_streamed() {
    let out = stub_repl_flags(
        "tool: source target\n\
         done: that is the source of target\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "(defn target [x] (add-i64 x 1))\n\
         /ask show me target\n",
    );
    // The tool-call turn is NOT streamed: the pull renders as-today — the `agent>`
    // command echo, UNFRAMED (no `▌` gutter on the pull line).
    let pull_line = out
        .stdout
        .lines()
        .find(|l| l.contains("/source target"))
        .unwrap_or_else(|| panic!("the pulled command must render; stdout={}", out.stdout));
    assert!(
        pull_line.contains("agent>"),
        "the pull renders as-today with the `agent>` prompt; line={pull_line:?}"
    );
    assert!(
        !pull_line.contains('\u{258c}'),
        "the tool-call pull is NOT framed (not streamed — §17.22 seam); line={pull_line:?}"
    );
    // The pull RESULT (the source of target) renders UNFRAMED too (tool-call turn).
    assert!(
        out.stdout
            .lines()
            .any(|l| l.contains("(defn target [x] (add-i64 x 1))") && !l.contains('\u{258c}')),
        "the pull result renders unframed (the tool-call turn is not streamed); stdout={}",
        out.stdout
    );
    // Only the terminal `Done` prose is streamed → framed.
    assert!(
        out.stdout
            .lines()
            .any(|l| l.contains("that is the source of target") && l.contains('\u{258c}')),
        "the terminal Done prose must render framed (streamed); stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.22 — Fallback: a provider relying on the DEFAULT
// `AgentModel::complete_streaming` (whole `Done` prose as ONE delta) degrades to
// today's behaviour — the one-delta answer renders EXACTLY as the all-at-once
// render (framed prose + un-guttered pretty-printed fence, `--no-color`-clean).
// A stub script with no `<|delta|>` markers exercises the one-delta path (the
// same bytes the trait default emits).
#[cfg(feature = "agent")]
#[test]
fn agent_non_streaming_provider_degrades() {
    let out = stub_repl_flags(
        "done: Here is a definition:\n\
         prose: ```lisp\n\
         prose: (defn double [x] (add-i64 x x))\n\
         prose: ```\n\
         prose: That defines double.\n",
        PreludeVariant::PrimitivesOnly,
        &["--no-color"],
        "/ask how do I double a number?\n",
    );
    // Renders exactly as the all-at-once render: the framed answer BLOCK appears
    // byte-exact (prose guttered, fence un-guttered on its own line).
    const BLOCK: &str = "\u{258c} Here is a definition:\n\
                         (defn double [x] (add-i64 x x))\n\
                         \u{258c} That defines double.";
    assert!(
        out.stdout.contains(BLOCK),
        "the one-delta (non-streaming) answer must render exactly as all-at-once \
         (§17.22 Fallback): the framed block appears byte-exact; stdout={:?}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("```"),
        "no raw fence markers may survive (fence is pretty-printed); stdout={:?}",
        out.stdout
    );
    assert!(
        !out.stdout.contains(ESC_SGR),
        "no literal ANSI escape under --no-color; stdout={:?}",
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

/// The turn-produces-nothing give-up script (S91 FIXME 0431 new fixture): a long
/// run of consecutive broken `submit`s with NO terminal `done:` answer — so every
/// outer turn-step gives up on its submit and the turn exhausts its iteration
/// budget (`MAX_TURN_ITERATIONS`, each step's repair loop also consuming scripted
/// completions) with no commit and no answer. This is the EXACT shape the impl's
/// own unit guard `give_up_line_shown_once_when_turn_produces_nothing` uses (64
/// repeated broken submits) — provisioned generously so the script never runs dry
/// before the turn budget is reached. Contrast `CAP_EXHAUSTED_GIVE_UP` above,
/// which ends on a `done:` (so the give-up line is ABSENT there — the corrected
/// Phase-6 semantics). A four-submit script (the prior shape) under-provisions the
/// turn loop and the give-up path never fires — the fixture, not the impl, was the
/// fault (FIXME 0431; the impl is correct, proven by the unit guard).
#[cfg(feature = "agent")]
const TURN_PRODUCES_NOTHING_LINE: &str = "tool: submit (defn never [x] x\n";

// spec: repl/spec.md §17.14.4 — the give-up notice is decided at TRUE turn-end and
// ONLY when the turn produced nothing. NEW (S91, FIXME 0431): the complement of
// the corrected `agent_build_cap_exhausted_give_up_stays_wire_valid` — a turn that
// ends WITHOUT a terminal `done:` answer (the repair cap exhausts with no answer)
// MUST render the give-up notice EXACTLY ONCE, and MUST commit nothing. This pins
// the "exactly once at turn-end" arm that the corrected semantics introduced (the
// other test pins the "absent when the turn ends on an answer" arm). RED-first
// until /dev's §16/§17.14.4 turn-end give-up decision lands.
#[cfg(feature = "agent")]
#[test]
fn agent_turn_produces_nothing_shows_give_up_once() {
    // 64 consecutive broken submits, no terminal `done:` — enough to exhaust the
    // turn iteration budget with no answer (mirrors the impl's unit guard).
    let script = TURN_PRODUCES_NOTHING_LINE.repeat(64);
    let out = stub_repl_flags(
        &script,
        PreludeVariant::PrimitivesOnly,
        &["--yes"],
        "/ask define never\n\
         (never 1)\n",
    );
    // (i) the give-up notice renders — the turn produced no answer, so the
    // turn-end decision is "could not produce" (the substring /dev's wording uses,
    // matching the sibling test's negative assertion).
    let lc = out.stdout.to_lowercase();
    assert!(
        lc.contains("couldn't produce a definition"),
        "a turn that ends with NO answer (cap exhausted) MUST render the give-up \
         notice at turn-end (§17.14.4), stdout={}",
        out.stdout
    );
    // (ii) EXACTLY ONCE — the notice must not print per-failed-submit mid-turn
    // (the live defect FIXME 0431 fixed). Count occurrences of the give-up phrase.
    let occurrences = lc.matches("couldn't produce a definition").count();
    assert_eq!(
        occurrences, 1,
        "the give-up notice MUST render EXACTLY ONCE at turn-end, not per-failed \
         submit (FIXME 0431); found {occurrences} occurrences, stdout={}",
        out.stdout
    );
    // (iii) committed NOTHING — `never` stays unbound.
    assert!(
        lc.contains("unbound") || lc.contains("undefined") || lc.contains("unknown"),
        "a give-up must write NOTHING — `never` must stay unbound, stdout={}",
        out.stdout
    );
    // (iv) the subprocess stayed wire-valid (clean exit; debug-binary
    // assemble_request guard fired green on the give-up follow-up).
    assert!(
        !out.stderr.contains("not wire-valid") && out.status.success(),
        "the give-up path must keep the transcript wire-valid; exit={:?} stderr={}",
        out.status,
        out.stderr
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

// ===========================================================================
// Pillar 1 (S90) — `/syntax` as an AGENT PULL-TOOL (tests/plan/s90-test-plan.md
// §P1 row P1.6). The default-build `/syntax` command rows (P1.1–P1.5, P1.7,
// P1.8) live in `tests/repl_introspection.rs` (the deterministic-command home,
// not feature-gated). This row is the Lane-A agent-pull face: the agent
// synthesizes `/syntax <topic>` via the stub `tool: syntax <topic>` line, the
// command renders with the `agent>` glyph, the topic content renders beneath
// (unframed), and the terminal `done:` prose is framed (§17.17.3 dual-use).
//
// TESTABILITY SEAM owed by /dev 1d: `syntax` must be a recognised read-only
// pull-tool name in the stub-DSL allowlist (the new `tool: syntax <topic>` form,
// §17.17.3 / §11.7). RED on HEAD: `/syntax` is unimplemented AND `syntax` is not
// an allowlisted pull tool, so the stub's `tool: syntax hkt` cannot synthesize a
// rendered `/syntax hkt`. Flips green when /dev 1d wires the command + adds the
// allowlist row.
// ===========================================================================

// spec: repl/spec.md §17.17.3 — the agent pulls `/syntax`: a stub `tool: syntax
// hkt` makes the agent synthesize `/syntax hkt` (the `agent>` glyph), the topic
// content renders beneath it unframed, then a `done:` answer is framed (`▌`).
// Same who-typed-what honesty as every other agent pull (§17.12).
#[cfg(feature = "agent")]
#[test]
fn agent_pulls_syntax_renders_as_command() {
    let out = stub_repl_flags(
        "tool: syntax hkt\n\
         done: so a higher-kinded type is written with (f a)\n",
        PreludeVariant::PrimitivesOnly,
        // --no-color so the `agent>` glyph degrades to the plain token.
        &["--no-color"],
        "/ask how do I write a higher-kinded type?\n",
    );
    // The synthesized pull command renders as-typed with the agent-input prompt.
    assert!(
        out.stdout.contains("agent>"),
        "the agent-issued /syntax pull must carry the `agent>` prompt, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("/syntax hkt"),
        "the pulled command must render as-typed, stdout={}",
        out.stdout
    );
    // The topic content rendered beneath the pull (the `hkt` block's content).
    assert!(
        out.stdout.contains("hkt") || out.stdout.contains("SPEC") || out.stdout.contains("TOPIC"),
        "the /syntax topic content must render beneath the pull, stdout={}",
        out.stdout
    );
    // The terminal prose answer is framed.
    assert!(
        out.stdout.contains('\u{258c}'),
        "the agent's terminal answer must be framed, stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("higher-kinded type"),
        "the agent prose must render, stdout={}",
        out.stdout
    );
}

// ===========================================================================
// Primer-shape repros (S90 Wave 1 primer-defect fold-in — SPRINT.md Notes
// 2026-06-23 finding #3). The always-on primer (`src/agent/primer.txt`) today
// documents TWO Cranelisp shapes that DO NOT compile — verified live against
// the binary at authoring time:
//
//   1. `match` arms paren-grouped — primer lines 44 + 123–125 show
//      `(match s ((Circle r) …) ((Rect w h) …))`. Live result: PARSE ERROR
//      ("match requires scrutinee and arms" / "unknown constructor in pattern").
//      The spec (spec/06-pattern-matching.md §6.1) is flat bracket pairs in ONE
//      `[ ]`: `(match s [(Circle r) … (Rect w h) …])` — which compiles
//      (`(match (Some 7) [None 0 (Some x) x])` → `:primitives/Int 7`).
//
//   2. `deftrait` outer-bracket — primer lines 46 + 128 show
//      `(deftrait Show [(show [a] String)])`. Live result: PARSE ERROR
//      ("expected list"). The spec (spec/07-traits.md §7.1) form
//      `(deftrait Show (show [a] String))` — method sigs as DIRECT children, no
//      outer `[ ]` — parses (the trait + `show` method are declared).
//
// These are primer-content guards that read `primer.txt` straight off disk
// (the asset exists regardless of the `agent` feature, so the guards are
// unconditional) and assert the SPEC-CORRECT shapes are present + the WRONG
// shapes absent. RED on HEAD (the primer carries the wrong shapes); /dev 1d
// corrects `primer.txt` to flip them green. A companion e2e confirms the
// spec-correct shapes the primer SHOULD teach actually compile.
// ===========================================================================

/// The always-on primer asset, read-only on project_root (per `tests/CLAUDE.md`
/// — locating a checked-in asset). The SAME source `include_str!`'d into
/// `src/agent/primer.rs`; the content guards assert its shapes match the spec.
// read-only on project_root
fn primer_asset() -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/agent/primer.txt");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the primer asset must exist at {path:?}: {e}"))
}

// spec: spec/06-pattern-matching.md §6.1 — the primer's `match` examples MUST use
// the spec-correct FLAT-bracket arm shape (`[(Ctor a) body …]`), NOT the
// paren-grouped shape (`((Ctor a) body) …`) which fails to parse. RED on HEAD:
// primer.txt lines 124–125 carry `((Circle r) …)` / `((Rect w h) …)`. Flips
// green when /dev 1d rewrites the primer's match example to the bracket shape.
#[test]
fn primer_match_uses_flat_bracket_arms_not_paren_grouped() {
    let primer = primer_asset();
    // +neg: the paren-grouped match arms (the WRONG shape, verified non-compiling)
    // must NOT appear in the primer's worked example.
    assert!(
        !primer.contains("((Circle r)"),
        "primer must NOT use the paren-grouped `((Circle r) …)` match arm — it \
         fails to parse; use the spec flat-bracket shape (spec/06 §6.1)"
    );
    assert!(
        !primer.contains("((Rect w h)"),
        "primer must NOT use the paren-grouped `((Rect w h) …)` match arm — it \
         fails to parse; use the spec flat-bracket shape (spec/06 §6.1)"
    );
    // The spec-correct flat-bracket arms (the COMPILING shape) must be present:
    // the worked example's arms live inside ONE `[ ]`.
    assert!(
        primer.contains("[(Circle r)") || primer.contains("(match s\n      [(Circle r)"),
        "primer must use the spec flat-bracket match arm `[(Circle r) …]` \
         (spec/06 §6.1) so the documented example compiles"
    );
    // The special-forms summary (primer line ~44) must likewise show the bracket
    // form, NOT the paren-grouped `(pattern result)` clause-list shape.
    assert!(
        !primer.contains("(match scrutinee (pattern result)"),
        "primer's special-forms summary must NOT show the paren-grouped \
         `(match scrutinee (pattern result) …)` shape — it does not parse \
         (spec/06 §6.1)"
    );
}

// spec: spec/07-traits.md §7.1 — the primer's `deftrait` examples MUST use the
// spec-correct shape with method sigs as DIRECT children
// (`(deftrait Describe (describe [a] String))`), NOT the outer-bracket shape
// (`(deftrait Describe [(describe [a] String)])`) which fails to parse ("expected
// list"). The primer's worked example uses the trait name `Describe` (NOT `Show`):
// reusing the prelude method name `show` makes the prelude's `str` — which calls
// `show` — recurse into the user's own impl → stack overflow; the primer's
// adjacent guidance (primer.txt ~L154) now warns against reusing a prelude method
// name. The test's INTENT is unchanged — the `deftrait` example uses method sigs
// as DIRECT children, not the outer-bracket `[(...)]` shape. Current primer.txt:
// L50 (special-forms summary) + L157 (worked example) both carry the direct-child
// shape. GREEN. Guards against a regression to the non-compiling outer-bracket.
#[test]
fn primer_deftrait_uses_direct_children_not_outer_bracket() {
    let primer = primer_asset();
    // +neg: the outer-bracket deftrait (the WRONG shape, verified non-compiling)
    // must NOT appear — neither in the worked example nor the summary.
    assert!(
        !primer.contains("(deftrait Describe [(describe"),
        "primer must NOT use the outer-bracket `(deftrait Describe [(describe …)])` \
         — it fails to parse (\"expected list\"); method sigs are direct children \
         (spec/07 §7.1)"
    );
    assert!(
        !primer.contains("(deftrait Name [method-sigs"),
        "primer's special-forms summary must NOT show the outer-bracket \
         `(deftrait Name [method-sigs...])` — method sigs are direct children, \
         no outer `[ ]` (spec/07 §7.1)"
    );
    // The spec-correct shape (method sig as a direct child) must be present.
    // `Describe`, not `Show`: the method name must not collide with a prelude
    // method (`show`), which would recurse the prelude's `str` into the impl.
    assert!(
        primer.contains("(deftrait Describe (describe [a] String))"),
        "primer must use the spec-correct `(deftrait Describe (describe [a] String))` \
         shape (method sigs as direct children, spec/07 §7.1) so the documented \
         example compiles"
    );
}

// spec: spec/06-pattern-matching.md §6.1 — companion e2e: the spec-correct
// flat-bracket `match` shape the primer SHOULD teach actually COMPILES live
// (guards the shape the primer guards above pin). `Some` is bare-available
// through the prelude, so this needs no import. Green on HEAD (the spec shape
// already compiles) — it pins the convergence target the corrected primer must
// match. Paired with the RED primer-content guard above (the match-shape
// verification step in tests/CLAUDE.md).
#[test]
fn primer_match_flat_bracket_shape_compiles_e2e() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(match (Some 7) [None 0 (Some x) x])\n")
        .output();
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "the spec flat-bracket match shape `[None 0 (Some x) x]` must compile and \
         eval to :primitives/Int 7 (spec/06 §6.1), stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.to_lowercase().contains("error"),
        "the spec flat-bracket match shape must NOT produce a parse/type error, \
         stdout={}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// Pillar 2 — harvest at signature grain (S90 Phase 5 Wave 2; §P2 rows P2.1–P2.4)
//
// The harvester surfaces in-scope symbols — the current module's own defns +
// explicit imports + implicit prelude — at name + `:Type` signature + docstring
// grain, ambiently every turn, WITHOUT the agent first spending a turn on
// `/list`/`/imports`/`/exports`. This is ambient (no command, nothing extra in
// the human REPL); it is observable via the `/context <path>` harvest dump
// (§17.11, the `=== HARVESTED CONTEXT ===` section) — the established read-back
// seam (mirrors `agent_on_context_dumps_request_to_file_dormant` above and the
// S89 `agent_document_harvester_reads_edited_preamble_back` read-back).
//
// RED on HEAD: harvest is name-only today (no sig grain). `/dev` step 2d
// enriches `harvest_context` (`src/agent/harvest.rs`) to reuse
// `repl::format_entry_sig` → `display::format_type_qualified`, flipping these
// green (design/int/agent.md §23).
//
// `/context` is pure (no model call) and works DORMANT, so these run with the
// agent built-in but unconfigured — no stub, no provider.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.18 — P2.1: a fresh session defines a docstring'd fn
// over the PrimitivesOnly prelude (which re-exports `primitives` as bare implicit
// prelude names — e.g. `add-i64` carries an §A.5 Description docstring). The
// `/context` dump's in-scope block MUST carry, per symbol, name + its `:Type`
// signature (FQ type names) + its docstring — for an OWN defn (`inc-doc`), and
// for an implicit-prelude symbol (`add-i64`). RED on HEAD (harvest is name-only:
// no signature, no docstring for the export/prelude surface).
#[cfg(feature = "agent")]
#[test]
fn harvest_in_scope_shows_name_sig_docstring() {
    let cr = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // Dormant: no provider key ⇒ `/context` still dumps (pure assembly).
        // Strip any ambient key/model so the default provider stays unreachable (S106).
        .without_agent_provider()
        .stdin(
            "(defn inc-doc \"adds one to its argument\" [x] (add-i64 x 1))\n\
             /context p2-grain.txt\n",
        );
    let out = cr.output();
    assert!(
        out.stdout.contains("wrote agent context to p2-grain.txt"),
        "the /context dump must succeed, stdout={}",
        out.stdout
    );
    let dumped = std::fs::read_to_string(out.tmpdir.join("p2-grain.txt"))
        .expect("the /context file must exist");
    // Scope to the NEW `== in scope ==` block (§17.18.2 / design §23.1 header) —
    // NOT the current-module full-source pin (which always carries `inc-doc`'s
    // source inline and would satisfy the assertions trivially). The in-scope
    // block is the read-enrichment Pillar 2 adds. RED on HEAD: the block does not
    // exist (harvest is name-only), so `nth(1)` yields nothing.
    let in_scope = dumped
        .split("== in scope ==")
        .nth(1)
        .unwrap_or("")
        .split("=== TOOLS")
        .next()
        .unwrap_or("");

    // --- own defn: name + FQ `:Type` signature + docstring (§17.18.1, 3 facets) ---
    assert!(
        in_scope.contains("inc-doc"),
        "the `== in scope ==` block must name the own defn `inc-doc`, in_scope={in_scope}"
    );
    assert!(
        in_scope.contains("(Fn [primitives/Int] primitives/Int)"),
        "the `== in scope ==` block must carry `inc-doc`'s FQ `:Type` signature \
         (the same shape `/sig` renders), in_scope={in_scope}"
    );
    assert!(
        in_scope.contains("adds one to its argument"),
        "the `== in scope ==` block must carry `inc-doc`'s docstring (§17.18.1 \
         facet 3), in_scope={in_scope}"
    );

    // --- implicit-prelude symbol: name + FQ signature (§A.5 description) ---
    // `add-i64` is NOT in the current module's source, so its signature appearing
    // proves the in-scope / export-surface arm is enriched (not the source pin).
    assert!(
        in_scope.contains("add-i64"),
        "the `== in scope ==` block must name the implicit-prelude symbol \
         `add-i64`, in_scope={in_scope}"
    );
    assert!(
        in_scope.contains("(Fn [primitives/Int primitives/Int] primitives/Int)"),
        "the `== in scope ==` block must carry `add-i64`'s FQ `:Type` signature at \
         sig grain (not name-only) — the harvest-sourced prelude awareness, \
         in_scope={in_scope}"
    );
    // --- implicit-prelude symbol DOCSTRING (§17.18.1 facet 3, ALL feeders) ---
    // At roomy budget (no budget constraint here) the §23.2 ladder is at full
    // grain, so the implicit-prelude feeder MUST also carry its §A.5 Description
    // docstring — not just OWN defns. `add-i64`'s Description is "Add"; it renders
    // as the `; <classification> - <docstring>` comment tail (the SAME shape a
    // bare-symbol display / `/doc` produces). Guarding the exact `; primitive - Add`
    // suffix (not the bare word "Add") pins the docstring to the prelude symbol's
    // own line and closes the gap that let docstrings-dropped-from-imports pass
    // green. RED on HEAD: the import/prelude arm renders at sig grain (docstring
    // dropped) per `render_in_scope_entry`'s `with_docstring=false` for non-own
    // defns — the Pillar-2 deviation `/review` (2R) ruled must be reverted.
    assert!(
        in_scope.contains("primitives/add-i64 ; primitive - Add"),
        "the `== in scope ==` block must carry the implicit-prelude symbol \
         `add-i64`'s §A.5 docstring at full grain (all feeders carry docstrings, \
         not just OWN defns) — the `; primitive - Add` comment tail, \
         in_scope={in_scope}"
    );
}

// spec: repl/spec.md §17.18 — P2.2 (+neg, fully-qualified): the harvested
// signatures render with the qualified `:Type` form (the `/sig`-grain formatter,
// `display::format_type_qualified`), NOT bare/unqualified. Assert the qualified
// shape appears AND that a bare-only `Int` token does not appear in a type
// position in the in-scope block. RED on HEAD (name-only harvest carries no type
// at all — neither qualified nor bare).
#[cfg(feature = "agent")]
#[test]
fn harvest_sig_is_fully_qualified_neg() {
    let cr = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // Dormant /context (pure): strip any ambient key/model (S106 hermeticity).
        .without_agent_provider()
        .stdin(
            "(defn inc-doc \"adds one\" [x] (add-i64 x 1))\n\
             /context p2-fq.txt\n",
        );
    let out = cr.output();
    let dumped = std::fs::read_to_string(out.tmpdir.join("p2-fq.txt"))
        .expect("the /context file must exist");
    // Scope to the NEW `== in scope ==` block — the signature-grain rendering
    // Pillar 2 adds (RED on HEAD: the block does not exist).
    let in_scope = dumped
        .split("== in scope ==")
        .nth(1)
        .unwrap_or("")
        .split("=== TOOLS")
        .next()
        .unwrap_or("");

    // Positive: the FQ form appears (the §4.1 FQ-display discipline, same as `/sig`).
    assert!(
        in_scope.contains("primitives/Int"),
        "the `== in scope ==` signature must use FQ type names (`primitives/Int`), \
         in_scope={in_scope}"
    );
    // +neg: no bare `Int` type token leaks into a TYPE position. Each in-scope
    // line is `:<sig> <module>/<name> ; <classification> - <docstring>` — the
    // type position is the segment BEFORE the `;` comment tail; the docstring
    // PROSE after the `;` legitimately contains "Int" inside words like
    // "**Int**eger division" and must NOT trigger this +neg (that false trigger
    // is exactly what drove the wrong docstring-drop; the check is now scoped to
    // type position only). For each line, take the pre-`;` segment, strip the FQ
    // `primitives/Int` occurrences, and assert no free-standing `Int` remains.
    for line in in_scope.lines() {
        let type_position = line.split(';').next().unwrap_or("");
        let stripped = type_position.replace("primitives/Int", "");
        assert!(
            !stripped.contains("Int"),
            "the `== in scope ==` block must NOT carry a bare unqualified `Int` in a \
             type position — only the FQ `primitives/Int` form (the `/sig`-grain +neg). \
             Offending line (pre-comment segment)=`{type_position}`, in_scope={in_scope}"
        );
    }
}

// spec: repl/spec.md §17.18 — P2.3 (+neg, budget degrades GRAIN not membership):
// under a constrained harvest budget the in-scope block drops signature DETAIL
// (docstring first, then sig — toward names-only) rather than silently DROPPING
// a symbol. Assert every in-scope symbol's NAME still appears under the tight
// budget (the agent must never believe a symbol is absent), while the heavier
// detail (the docstring) is elided.
//
// This row depends on a HARVEST-BUDGET TEST LEVER that does not exist on HEAD:
// `CRANELISP_AGENT_HARVEST_BUDGET` (an env knob to force a small `char_budget`
// in-process). 2d OWES this testability seam (flagged in the test plan §
// "Testability seams" #2 / design/int/agent.md §23.2). RED on HEAD for TWO
// reasons: (a) harvest is name-only (no grain to degrade), and (b) the budget
// lever is absent so the constrained budget is not honored. Both resolve when
// 2d lands the sig-grain enrichment AND the budget env lever.
#[cfg(feature = "agent")]
#[test]
fn harvest_budget_degrades_grain_not_truncates_neg() {
    let cr = Cranelisp::new()
        .repl()
        .cli_flag("--agent")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // Force a tiny harvest budget so degradation (not truncation) is exercised.
        // 2d testability-seam obligation: this env lever does not exist on HEAD.
        .env("CRANELISP_AGENT_HARVEST_BUDGET", "200")
        // Dormant /context (pure): strip any ambient key/model (S106 hermeticity).
        .without_agent_provider()
        .stdin(
            "(defn inc-doc \"a long descriptive docstring that costs many characters \
             and should be the first grain dropped under budget pressure\" [x] \
             (add-i64 x 1))\n\
             /context p2-budget.txt\n",
        );
    let out = cr.output();
    let dumped = std::fs::read_to_string(out.tmpdir.join("p2-budget.txt"))
        .expect("the /context file must exist");
    // Scope to the NEW `== in scope ==` block (§17.18.2 / design §23.1 header) —
    // NOT the whole harvest. The current-module full-source pin (§5.4 floor) is
    // unchanged and always carries the inline docstring; the budget degrades the
    // grain of the in-scope block, not the pinned source. RED on HEAD: the
    // `== in scope ==` block does not exist (harvest is name-only), so `nth(1)`
    // yields nothing and the name-membership assertions below fail.
    let in_scope = dumped
        .split("== in scope ==")
        .nth(1)
        .unwrap_or("")
        .split("=== TOOLS")
        .next()
        .unwrap_or("");

    // +neg (membership): the symbol's NAME is still present in the in-scope block
    // under the tight budget — the in-scope LIST is never silently truncated.
    assert!(
        in_scope.contains("inc-doc"),
        "under a tight harvest budget the in-scope symbol's NAME must still appear \
         in the `== in scope ==` block — budget degrades GRAIN, not membership \
         (§17.18.2), in_scope={in_scope}"
    );
    assert!(
        in_scope.contains("add-i64"),
        "under a tight harvest budget the implicit-prelude symbol's NAME must still \
         appear in the `== in scope ==` block — no symbol is silently dropped, \
         in_scope={in_scope}"
    );
    // Grain degraded: the heavy docstring detail is elided first (sig→names) in
    // the in-scope block under the tight budget.
    assert!(
        !in_scope.contains("a long descriptive docstring that costs many characters"),
        "under a tight harvest budget the docstring DETAIL must be dropped from the \
         `== in scope ==` block (grain degrades sig→names; docstrings go first), \
         in_scope={in_scope}"
    );
}

// spec: repl/spec.md §17.18 — P2.4 (no-relist acceptance): the sig-grain content
// appears in the AMBIENT harvest without the agent having to issue
// `/list`/`/exports`/`/imports`. A stub session whose only scripted action is a
// terminal `done:` (no read-pull) still gets the in-scope signature ambiently:
// the `/context` dump carries the own-defn's signature even though the
// transcript contains NO `/list`/`/exports`/`/imports` pull. RED on HEAD (the
// ambient harvest is name-only, so the agent WOULD have to pull `/list` to learn
// the signature — the very pre-flight Pillar 2 removes).
#[cfg(feature = "agent")]
#[test]
fn harvest_references_actual_sig_no_relist_needed() {
    let out = stub_repl(
        // The model answers directly — no `tool: list` / `tool: exports` pull.
        "done: inc-doc takes an Int and returns an Int\n",
        PreludeVariant::PrimitivesOnly,
        "(defn inc-doc \"adds one\" [x] (add-i64 x 1))\n\
         /ask what is the signature of inc-doc\n\
         /context p2-noflight.txt\n",
    );
    // The transcript must contain NO pre-flight list/exports/imports pull: the
    // ambient sig-grain harvest made it unnecessary (the acceptance).
    assert!(
        !out.stdout.contains("/list")
            && !out.stdout.contains("/exports")
            && !out.stdout.contains("/imports"),
        "the agent must answer from the AMBIENT harvest grain — no `/list`/\
         `/exports`/`/imports` pre-flight pull in the transcript (§17.18.2 \
         acceptance), stdout={}",
        out.stdout
    );
    // And the ambient harvest actually carried the signature (so the no-pull
    // answer was grounded, not guessed): the /context dump shows the sig grain.
    let dumped = std::fs::read_to_string(out.tmpdir.join("p2-noflight.txt"))
        .expect("the /context file must exist");
    let in_scope = dumped
        .split("== in scope ==")
        .nth(1)
        .unwrap_or("")
        .split("=== TOOLS")
        .next()
        .unwrap_or("");
    assert!(
        in_scope.contains("inc-doc")
            && in_scope.contains("(Fn [primitives/Int] primitives/Int)"),
        "the ambient `== in scope ==` harvest must carry `inc-doc`'s actual \
         signature so the agent never needs to relist (§17.18.2), in_scope={in_scope}"
    );
}

// ===========================================================================
// Pillar 4 (S90) — silent greppable agent log (tests/plan/s90-test-plan.md §P4
// rows P4.1–P4.5; repl/spec.md §17.20; design/int/agent.md §27).
//
// With `CRANELISP_AGENT_LOG=<path>` set, an `--features agent` session appends
// one structured JSONL record per agent event to that file — SILENTLY (nothing
// extra in the REPL), with STABLE GREPPABLE KEYS (event type, symbol, error
// class, repair-iteration count, module). The log is `#[cfg(feature="agent")]`,
// off the default build, and feature-OFF stays byte-identical (§17.20.2/§17.9).
//
// RED on HEAD: no log sink exists (`src/agent/log.rs` is unbuilt — verified
// absent), `CRANELISP_AGENT_LOG` is inert, so NO file is ever written and the
// stable-key assertions fail. Flips green when /dev 3d lands the §27 sibling
// sink (one-line appends at the existing record sites, env-gated like
// `trace.rs`, JSONL via `serde_json`, best-effort-discarded write).
//
// The Lane-A log-content rows (P4.1/P4.2/P4.4) drive the real binary through
// the stub-provider-by-config mechanism with `CRANELISP_AGENT_LOG` set on the
// spawned subprocess (the builder's `.env(...)`). The default-build absence
// row (P4.3) and the feature-OFF re-verify (P4.5) are default-lane rows
// (`#[cfg(not(feature = "agent"))]`).
//
// We assert the JSONL shape with a `grep`-style structural check (each line is
// `{...}` carrying the expected key substrings) rather than a `serde_json`
// parse — the §17.20.3 acceptance is OPERATIONAL ("a one-line `grep`/`jq`
// extracts every repair event with its triggering symbol/error"), and the test
// crate has no `serde_json` dep. The grep check IS the spec acceptance.
//
// TESTABILITY SEAM owed by /dev 3d: `CRANELISP_AGENT_LOG` honored on the
// spawned binary (already provided by the `Cranelisp` builder's `.env(...)` —
// no new seam; noted in the test plan §"Testability seams" #4). Each test uses
// a FRESH per-test tmpdir path for the log file (fresh-tmp discipline).
// ===========================================================================

/// A stub-driven agent REPL with `CRANELISP_AGENT_LOG` pointed at `log_path`
/// (a per-test tmpdir file). Like `stub_repl` but also wires the log env var so
/// the agent's silent activity log is captured to an observable file. Returns
/// the captured output; the caller reads `log_path` back.
#[cfg(feature = "agent")]
fn stub_repl_logged(
    script: &str,
    prelude: PreludeVariant,
    log_path: &std::path::Path,
    stdin: &str,
) -> helpers::e2e::CrOutput {
    let cl = Cranelisp::new().repl().with_prelude(prelude).cli_flag("--agent");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, script).unwrap();
    cl.env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .env("CRANELISP_AGENT_LOG", log_path.to_str().unwrap())
        .stdin(stdin)
        .output()
}

/// A Build script that exercises a PULL, a REPAIR (broken-then-fixed submit),
/// and a SUBMIT/commit — so the log carries multiple event types including the
/// keystone `repair` record (the user's primary struggle signal, §17.20.3).
/// Line 1: a read pull (`/source target`). Lines 2–3: broken-then-fixed submit
/// (the first fails the validator → a repair iteration; the second is clean →
/// commit). Line 4: terminal prose.
#[cfg(feature = "agent")]
const PULL_REPAIR_SUBMIT_SCRIPT: &str = "tool: source target\n\
     tool: submit (defn helper [x] (add-i64 x x)\n\
     tool: submit (defn helper [x] (add-i64 x x))\n\
     done: defined helper for you\n";

// ---------------------------------------------------------------------------
// P4.1 — writes JSONL with stable greppable keys (positive).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.20.3 — with `CRANELISP_AGENT_LOG=<tmp path>` set, a
// stub session that PULLS + REPAIRS + SUBMITS writes a JSONL file: every line
// parses as a JSON object (`{...}`) and carries the stable greppable keys — an
// `event` type on every record, plus `symbol`/`module`/`error_class`/
// `iteration` on the records that have them (a `grep`/`jq` one-liner extracts
// the repair events + their triggering symbol/error). RED on HEAD: no log sink
// exists, so NO file is written.
#[cfg(feature = "agent")]
#[test]
fn agent_log_writes_jsonl_with_stable_keys() {
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    // Fresh per-test tmpdir path for the log file (NOT a fixed location).
    let log_path = cl.tmpdir_path().join("agent-activity.jsonl");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, PULL_REPAIR_SUBMIT_SCRIPT).unwrap();
    let out = cl
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .env("CRANELISP_AGENT_LOG", log_path.to_str().unwrap())
        .stdin(
            "(defn target [x] (add-i64 x 1))\n\
             /ask define a helper\n\
             y\n",
        )
        .output();

    // The log FILE must exist (the env var was honored, the sink wrote to it).
    assert!(
        log_path.exists(),
        "`CRANELISP_AGENT_LOG` set ⇒ the agent must write the JSONL log file; \
         it does not exist at {log_path:?} (stdout={})",
        out.stdout
    );
    let log = std::fs::read_to_string(&log_path).expect("the log file must be readable");
    let lines: Vec<&str> = log.lines().filter(|l| !l.trim().is_empty()).collect();
    assert!(
        !lines.is_empty(),
        "the agent log must carry at least one event line, log={log:?}"
    );
    // Every line is a JSON OBJECT — JSONL shape (one object per line). The grep
    // contract: each record is `{...}` and carries an `event` key.
    for line in &lines {
        let t = line.trim();
        assert!(
            t.starts_with('{') && t.ends_with('}'),
            "each agent-log line must be a JSON object (`{{...}}`) — JSONL shape; \
             offending line={t:?}, log={log:?}"
        );
        assert!(
            t.contains("\"event\""),
            "every agent-log record must carry the stable `event` key (§17.20.3), \
             offending line={t:?}, log={log:?}"
        );
    }
    // The KEYSTONE: the broken-then-fixed submit produced a REPAIR record
    // carrying the stable struggle-signal keys — `event=repair`, its triggering
    // `symbol`, the `module`, an `error_class`, and an `iteration` count. A
    // one-line `grep '"event":"repair"'` extracts it (§17.20.3 acceptance).
    let repair_line = lines
        .iter()
        .find(|l| l.contains("\"event\":\"repair\"") || l.contains("\"event\": \"repair\""))
        .unwrap_or_else(|| {
            panic!(
                "the broken-then-fixed submit must produce a `repair` event record \
                 (the keystone struggle signal, §17.20.3) — none found, log={log:?}"
            )
        });
    for key in ["\"symbol\"", "\"module\"", "\"error_class\"", "\"iteration\""] {
        assert!(
            repair_line.contains(key),
            "the `repair` record must carry the stable greppable key {key} (the \
             triggering symbol/error/module + repair-iteration count, §17.20.3); \
             repair_line={repair_line:?}"
        );
    }
    // The repair's triggering symbol is the one the agent struggled to define.
    assert!(
        repair_line.contains("helper"),
        "the `repair` record's `symbol` must name the struggled-over definition \
         (`helper`), so `grep helper` surfaces it (§17.20.3), repair_line={repair_line:?}"
    );
}

// ---------------------------------------------------------------------------
// P4.2 — silent: transcript byte-identical with the log ON vs OFF (+neg).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.20.1 — the log is SILENT: the REPL/agent transcript
// with `CRANELISP_AGENT_LOG` SET is BYTE-IDENTICAL to the same stub session
// with it UNSET. Turning on the log adds NOTHING to stdout — no "logging to …"
// banner, no per-event echo, no transcript change. The +neg is the zero-byte
// perturbation: two real stub transcripts (log-on / log-off) diff to nothing.
// RED on HEAD: no log sink exists, so today both runs are trivially identical
// (the var is inert) — but this row is the standing guard that when the sink
// lands it perturbs the transcript by ZERO bytes (it must NOT regress).
#[cfg(feature = "agent")]
#[test]
fn agent_log_is_silent_transcript_unchanged_neg() {
    // Log OFF: the baseline stub transcript (no `CRANELISP_AGENT_LOG`).
    let off = stub_repl(
        PULL_REPAIR_SUBMIT_SCRIPT,
        PreludeVariant::PrimitivesOnly,
        "(defn target [x] (add-i64 x 1))\n\
         /ask define a helper\n\
         y\n",
    );
    // Log ON: the SAME session with `CRANELISP_AGENT_LOG` pointed at a tmp file.
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    let log_path = cl.tmpdir_path().join("silent.jsonl");
    let on = stub_repl_logged(
        PULL_REPAIR_SUBMIT_SCRIPT,
        PreludeVariant::PrimitivesOnly,
        &log_path,
        "(defn target [x] (add-i64 x 1))\n\
         /ask define a helper\n\
         y\n",
    );
    // The keystone silent guard: stdout is BYTE-IDENTICAL log-on vs log-off,
    // AFTER masking the per-prompt elapsed-ms counter (`N+Mms; <mod>> `) — that
    // counter is independent wall-clock jitter every REPL run differs on, NOT a
    // log perturbation. The §17.20.1 contract is that the LOG adds nothing; the
    // mask isolates that from the timing chrome both runs carry regardless.
    let mask = regex::Regex::new(r"\d+\+\d+ms; (\w+)> ").unwrap();
    let on_masked = mask.replace_all(&on.stdout, "T+Tms; $1> ");
    let off_masked = mask.replace_all(&off.stdout, "T+Tms; $1> ");
    assert_eq!(
        on_masked, off_masked,
        "`CRANELISP_AGENT_LOG` must be SILENT — the REPL transcript with the log \
         ON must be BYTE-IDENTICAL to the log OFF, modulo the wall-clock prompt \
         counter (§17.20.1: no banner, no per-event echo, nothing extra in stdout)"
    );
    // +neg: no "logging" banner ever appears in the log-on transcript.
    assert!(
        !on.stdout.to_lowercase().contains("logging to")
            && !on.stdout.to_lowercase().contains("writing log"),
        "the silent log must NOT print a `logging to …` banner (§17.20.1), \
         stdout={}",
        on.stdout
    );
}

// ---------------------------------------------------------------------------
// P4.4 — graceful on an unwritable path (+neg).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.20.2 — graceful on an unwritable path: with
// `CRANELISP_AGENT_LOG` set to a path that cannot be written (here a file under
// a NONEXISTENT parent directory), the session does NOT crash and spews NO
// error into the REPL — the log degrades SILENTLY (its write is a best-effort
// `let _ = ...`). The agent runs normally; the failure is swallowed. RED on
// HEAD: no log sink exists (the path is inert) — this is the standing guard
// that when the sink lands, an unwritable path can never disturb the session.
#[cfg(feature = "agent")]
#[test]
fn agent_log_graceful_on_unwritable_path_neg() {
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    // A path under a nonexistent parent directory — opening it for append fails.
    let unwritable = cl
        .tmpdir_path()
        .join("no-such-dir")
        .join("agent.jsonl");
    let out = stub_repl_logged(
        PULL_REPAIR_SUBMIT_SCRIPT,
        PreludeVariant::PrimitivesOnly,
        &unwritable,
        "(defn target [x] (add-i64 x 1))\n\
         /ask define a helper\n\
         y\n",
    );
    // (i) the session runs to completion — a clean exit, NO crash/panic. A
    // failed log write must never unwind the session (logging is a side channel).
    assert!(
        out.status.success(),
        "an unwritable `CRANELISP_AGENT_LOG` path must NOT crash the session — \
         logging degrades silently (§17.20.2); exit={:?}, stderr={}",
        out.status,
        out.stderr
    );
    // (ii) the agent still ran normally: the fixed form committed + the prose
    // rendered (so the swallowed log failure perturbed nothing observable).
    assert!(
        out.stdout.contains('\u{258c}'),
        "the agent turn must still render — the failed log write must not disturb \
         the session (§17.20.2), stdout={}",
        out.stdout
    );
    // (iii) +neg: the unwritable-path failure spews NO error into the REPL — no
    // "could not open", "permission denied", "no such file" log-error chatter.
    let lc = out.stdout.to_lowercase();
    assert!(
        !lc.contains("could not open")
            && !lc.contains("permission denied")
            && !lc.contains("failed to write log")
            && !lc.contains("no such file or directory"),
        "an unwritable log path must degrade SILENTLY — NO log-error chatter may \
         reach the REPL (§17.20.2), stdout={}",
        out.stdout
    );
    // (iv) the parent dir is genuinely absent — no file was forced into being.
    assert!(
        !unwritable.exists(),
        "the unwritable log path must not have been written, path={unwritable:?}"
    );
}

// ---------------------------------------------------------------------------
// P4.3 — absent on the default build (+neg). DEFAULT-LANE (not feature-gated).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.20.2 — on a DEFAULT (non-`agent`) build, setting
// `CRANELISP_AGENT_LOG` writes NOTHING: the var is inert and the sink does not
// exist (the log lives ONLY in an `--features agent` build, §17.9). The +neg
// absence guard: a default-build session with the env set + an `--agent`-style
// flow produces NO log file. RED-context: this is the standing Lane-B floor
// re-confirmed with the log code added — the default build must stay agent-free.
#[cfg(not(feature = "agent"))]
#[test]
fn agent_log_absent_on_default_build_neg() {
    // NB: no `--agent` precondition — since S106 (FIXME 0539) `--agent` HARD-ERRORS
    // on a non-agent build, so the log-absence guard stands on a plain default-build
    // session (the log sink is agent-feature-gated regardless of any flag).
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly);
    let log_path = cl.tmpdir_path().join("default-build.jsonl");
    let out = cl
        .env("CRANELISP_AGENT_LOG", log_path.to_str().unwrap())
        .stdin("(add-i64 1 2)\n")
        .output();
    // The session evals as today (the agent surface is absent feature-off).
    assert!(
        out.stdout.contains("3"),
        "the default-build session must still eval, stdout={}",
        out.stdout
    );
    // +neg: NO log file was written — the var is inert on the default build.
    assert!(
        !log_path.exists(),
        "`CRANELISP_AGENT_LOG` must be INERT on the default (non-`agent`) build — \
         NO log file may be written (§17.20.2: the log exists only in an \
         `--features agent` build), but a file appeared at {log_path:?}"
    );
}

// ---------------------------------------------------------------------------
// P4.5 — feature-OFF byte-identical re-verify. DEFAULT-LANE (Lane B floor).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.9 — the standing Lane-B floor re-confirmed for Pillar
// 4: the default build is UNCHANGED by the log code. A non-agent input on a
// default build with `CRANELISP_AGENT_LOG` set is byte-identical to the same
// input with it UNSET — the log code (agent-gated) cannot perturb the default
// build. This is the test-plan Feature-OFF floor for Pillar 4 (the log adds no surface
// to the default suite). Green-on-HEAD context (the var is inert today); the
// standing guard that adding `src/agent/log.rs` must keep the default build
// byte-identical.
#[cfg(not(feature = "agent"))]
#[test]
fn agent_log_feature_off_byte_identical_reverify() {
    // The SAME non-agent input, once with the log env set, once without.
    let with_log = {
        let cl = Cranelisp::new()
            .repl()
            .with_prelude(PreludeVariant::PrimitivesOnly);
        let log_path = cl.tmpdir_path().join("reverify.jsonl");
        cl.env("CRANELISP_AGENT_LOG", log_path.to_str().unwrap())
            .stdin("(add-i64 40 2)\nhow do I define a function\n")
            .output()
    };
    let without_log = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(add-i64 40 2)\nhow do I define a function\n")
        .output();
    // Byte-identical: the agent-gated log code adds NOTHING to the default build
    // (masking the per-prompt wall-clock counter, as in P4.2 — independent jitter,
    // not a log perturbation).
    let mask = regex::Regex::new(r"\d+\+\d+ms; (\w+)> ").unwrap();
    let with_masked = mask.replace_all(&with_log.stdout, "T+Tms; $1> ");
    let without_masked = mask.replace_all(&without_log.stdout, "T+Tms; $1> ");
    assert_eq!(
        with_masked, without_masked,
        "the default build must stay BYTE-IDENTICAL with `CRANELISP_AGENT_LOG` set \
         vs unset — the agent-gated log code cannot perturb the default suite (§17.9)"
    );
}

// ===========================================================================
// S90 ADDENDUM (step 5q) — persistent full-content TRACE sink + log↔trace `turn`
// correlation (repl/spec.md §17.20 reframed + §17.21 NEW; design/int/agent.md
// §28; tests/plan/s90-test-plan.md §"S90 addendum — persistent trace + turn").
//
// The §17.20 LOG is the compact greppable INDEX (metadata-only, gains a `turn`
// field). Its companion §17.21 TRACE is the persistent FULL-CONTENT sink:
// `CRANELISP_AGENT_TRACE` becomes a PATH (re-purposed from S89's ephemeral
// stderr view), appending the full, untruncated request/response transcript;
// the stderr `eprintln!` sink is REMOVED. The two sinks are joined by a shared
// per-turn `turn` index, stamped identically in both.
//
// ───────────────────────────────────────────────────────────────────────────
// THE RIG-BOUNDARY TESTABILITY CONSTRAINT (design/int/agent.md §28.2(2)).
// ───────────────────────────────────────────────────────────────────────────
// The TRACE fires at the rig boundary (`provider.rs` `RigModel::complete` →
// `emit_request`/`emit_response`), ABOVE the deterministic stub. The stub
// (`stub.rs`) NEVER reaches the emit sites. VERIFIED on HEAD: a stub session
// with `CRANELISP_AGENT_TRACE=<path>` set writes NO trace file (the stub path
// never calls `emit_*`). Therefore a stub-driven e2e CANNOT populate the trace
// file — and it stays empty even after the §28.1 file-sink fix lands.
//
// Consequently the trace tests split by reachability:
//
//   * The TRACE FILE POPULATION + FULL untruncated CONTENT + the trace-side
//     `turn=N` marker + the `Grain::Full` formatter + `append_to_env_path` are
//     exercised by the RIG-trait `MockModel` path, which lives in
//     `src/agent/provider.rs` `#[cfg(test)] mod tests` (the S88/S89
//     continuation_request_* / repair_loop_request_* pattern that drives a real
//     `CompletionModel`/`CompletionRequest` below the membrane). Those are
//     `/dev`-owned UNIT tests in the binary crate's `src/` — NOT authored here
//     (`/qa` owns `tests/`, not `crates/*/src/`; qa.md §"Testing ownership").
//     They are flagged below as the 5d testability seam owed.
//
//   * The LOG side (incl. the `turn` field) IS stub-reachable — it fires inside
//     `agent_turn`/`pull.rs`, provider-independent. So the `turn` field, the
//     log↔trace `turn` correlation (LOG side), and the log-stays-compact guard
//     ARE authored here as stub e2e.
//
//   * The TRACE var's silent / graceful / feature-off contract that IS
//     observable e2e (no stderr leak, no crash on an unwritable path, inert on
//     the default build) is authored here — these hold REGARDLESS of whether the
//     stub reaches emit (they assert ABSENCE of perturbation).
//
// RED-FIRST on HEAD (`--features agent`):
//   - T1 (turn field present): RED — the `exchange` record carries `iteration`,
//     not `turn`; the pull/submit/repair records carry NO turn at all. VERIFIED
//     live: `grep -c '"turn"' log.jsonl` == 0 on HEAD.
//   - T2 (log↔trace turn correlation, LOG side): RED — same reason (no `turn`).
//   - T3 (log stays compact): a GUARD (passes on HEAD) that pins the index/
//     content split — the §28.1 trace-content work must NOT thicken the log.
//   - T4/T5 (trace var silent / no-stderr-leak / graceful / feature-off): on
//     HEAD the var is the legacy stderr toggle; these pin the §17.21 path-only
//     contract — RED where HEAD still emits to stderr on a truthy value, GUARD
//     where they assert absence the fix must preserve.
//
// 5d TESTABILITY SEAMS OWED (design/int/agent.md §28.2 / §28.6, flagged to /dev):
//   (a) the §28.1 `Grain { Compact, Full }` formatter param on
//       `format_request_trace`/`format_response_trace` — UNIT-testable directly
//       (a >80-char form survives verbatim under `Full`), `src/agent/trace.rs`.
//   (b) `AgentRequest.turn: usize` (`types.rs`) set by `assemble_request` from
//       `AgentState.current_turn` — so the rig `MockModel` test can read
//       `request.turn` and assert the trace-side `turn=N` marker matches the
//       log's `turn`. The new `usize` defaults to 0 (`AgentRequest: Default`).
//   (c) the §28.3 `append_to_env_path(var, content)` shared helper — one UNIT
//       test for gate-off / append / unwritable-swallow.
//   (d) the trace-file-population + trace-side-`turn` rig `MockModel` UNIT tests
//       in `src/agent/provider.rs` — the ONLY place the trace file is populated
//       deterministically (the stub cannot). `/dev` authors these alongside the
//       §28.1/§28.2 implementation, per the unit-test-per-fix discipline.
//
// (A Lane-C LIVE check against a real provider — where the trace file actually
// fills end-to-end through the binary — is the user's manual confirmation, not
// CI; the stub path's emptiness above is exactly why CI cannot cover it.)
// ===========================================================================

/// A Build script that drives THREE model exchanges in one turn — a PULL
/// (turn 1), a broken-then-fixed SUBMIT spanning a REPAIR (turns 2 & 3), and a
/// terminal Done — so the log carries multiple event types across DISTINCT
/// `turn` indices. Reused by the `turn`-correlation e2e below.
#[cfg(feature = "agent")]
const TRACE_TURN_SCRIPT: &str = "tool: source target\n\
     tool: submit (defn helper [x] (add-i64 x x)\n\
     tool: submit (defn helper [x] (add-i64 x x))\n\
     done: defined helper for you\n";

// ---------------------------------------------------------------------------
// T1 — the LOG JSONL carries a `turn` field (positive). STUB-reachable e2e.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.21.3 — the §17.20 log JSONL gains a `turn` field on
// every line: the per-turn/exchange correlation index, monotonic within the
// session, that joins each compact log line to the full-content trace exchange
// that produced it. RED on HEAD: the `exchange` record carries `iteration`
// (overloaded) and the pull/submit/repair records carry NO turn — `grep -c
// '"turn"'` over the log is 0. Flips green when /dev 5d adds the `LogEvent.turn`
// field (§28.2) and switches the `exchange` record from `.iteration(turn_step+1)`
// to `.turn(turn_step+1)` + threads `.turn(current)` onto the in-loop records.
#[cfg(feature = "agent")]
#[test]
fn agent_log_carries_turn_correlation_field() {
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    let log_path = cl.tmpdir_path().join("turn-field.jsonl");
    let out = stub_repl_logged(
        TRACE_TURN_SCRIPT,
        PreludeVariant::PrimitivesOnly,
        &log_path,
        "(defn target [x] (add-i64 x 1))\n\
         /ask define a helper\n\
         y\n",
    );
    assert!(
        log_path.exists(),
        "the log file must exist (the sink wrote it), stdout={}",
        out.stdout
    );
    let log = std::fs::read_to_string(&log_path).expect("the log file must be readable");
    let lines: Vec<&str> = log.lines().filter(|l| !l.trim().is_empty()).collect();
    assert!(!lines.is_empty(), "the log must carry event lines, log={log:?}");

    // EVERY agent-log line must carry the stable `turn` correlation key
    // (§17.21.3 — "the §17.20 log JSONL gains a `turn` field on every line").
    for line in &lines {
        assert!(
            line.contains("\"turn\""),
            "every agent-log record must carry the `turn` correlation key \
             (§17.21.3) — offending line={line:?}, log={log:?}"
        );
    }
    // The first model exchange carries turn 1 (1-based, monotonic): the `turn`
    // index is the per-exchange key, NOT the overloaded `iteration`.
    let first_exchange = lines
        .iter()
        .find(|l| l.contains("\"event\":\"exchange\"") || l.contains("\"event\": \"exchange\""))
        .expect("the loop must record an `exchange` event");
    assert!(
        first_exchange.contains("\"turn\":1") || first_exchange.contains("\"turn\": 1"),
        "the first model exchange must carry `turn`:1 (1-based monotonic index, \
         §17.21.3) — first_exchange={first_exchange:?}"
    );
}

// ---------------------------------------------------------------------------
// T2 — log↔trace `turn` correlation (LOG side): the SAME `turn` joins a
// non-exchange record to the model exchange it belongs to. STUB-reachable e2e.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.21.3 — the shared `turn` key joins an index record
// (log) to its content record (trace). On the LOG side this means: a pull /
// repair / submit record carries the SAME `turn` as the `exchange` record for
// the loop iteration that produced it (they fire inside one `agent_turn` loop
// step, after that step's `exchange` record). RED on HEAD: no `turn` field at
// all, so no join is possible. The trace-SIDE `turn=N` marker that completes the
// join is the rig-`MockModel` UNIT test owed by /dev 5d (the stub cannot
// populate the trace — §28.2(2)); this e2e pins the LOG half of the join.
#[cfg(feature = "agent")]
#[test]
fn agent_log_turn_joins_record_to_its_exchange() {
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    let log_path = cl.tmpdir_path().join("turn-join.jsonl");
    stub_repl_logged(
        TRACE_TURN_SCRIPT,
        PreludeVariant::PrimitivesOnly,
        &log_path,
        "(defn target [x] (add-i64 x 1))\n\
         /ask define a helper\n\
         y\n",
    );
    let log = std::fs::read_to_string(&log_path).expect("the log file must be readable");
    let lines: Vec<&str> = log.lines().filter(|l| !l.trim().is_empty()).collect();

    /// Extract the integer value of the `turn` key from a JSONL line (tolerant
    /// of `"turn":N` and `"turn": N`). `None` ⇒ the key is absent (RED today).
    fn turn_of(line: &str) -> Option<u64> {
        let i = line.find("\"turn\"")?;
        let rest = &line[i + "\"turn\"".len()..];
        let rest = rest.trim_start_matches([':', ' ']);
        let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        rest[..end].parse::<u64>().ok()
    }

    // Walk the JSONL: each `exchange` line sets the "current turn"; every
    // following NON-exchange record (pull/repair/submit) until the next exchange
    // must carry that SAME turn — the join key (§17.21.3). At least one
    // non-exchange record must be checked (the pull) so the assertion is real.
    let mut current_turn: Option<u64> = None;
    let mut joined_a_non_exchange = false;
    for line in &lines {
        let is_exchange =
            line.contains("\"event\":\"exchange\"") || line.contains("\"event\": \"exchange\"");
        let t = turn_of(line);
        assert!(
            t.is_some(),
            "every record must carry a parseable `turn` (§17.21.3); line={line:?}"
        );
        if is_exchange {
            current_turn = t;
        } else {
            joined_a_non_exchange = true;
            assert_eq!(
                t, current_turn,
                "a non-exchange record must carry the SAME `turn` as the \
                 `exchange` it belongs to (the log↔trace join key, §17.21.3); \
                 line={line:?}, current exchange turn={current_turn:?}"
            );
        }
    }
    assert!(
        joined_a_non_exchange,
        "the script must produce at least one non-exchange record (a pull) so \
         the turn-join is actually exercised, lines={lines:?}"
    );
}

// ---------------------------------------------------------------------------
// T3 — the LOG stays COMPACT: NO content fields (the index/content split).
// STUB-reachable GUARD. Pins §28.4 "the log stays compact — `turn` is the ONLY
// field added; no content fields migrate into the log."
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.20.3 — the log "stays the compact index — it carries
// metadata-only keys (event/symbol/error_class/iteration/module/`turn`) and NO
// content (no form text, no error message, no model prose)." The §17.21 trace
// is where the full content lives. This GUARD pins the split: even with the
// trace-content work landed, the log must NOT gain content fields. It asserts
// the log carries the metadata keys but NONE of the content keys the trace
// owns (`form`/`prose`/`request`/`response`/`error_message`/`content`/`text`),
// and that no log VALUE smuggles the verbatim submitted form text.
#[cfg(feature = "agent")]
#[test]
fn agent_log_stays_compact_no_content_fields_neg() {
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    let log_path = cl.tmpdir_path().join("compact.jsonl");
    stub_repl_logged(
        TRACE_TURN_SCRIPT,
        PreludeVariant::PrimitivesOnly,
        &log_path,
        "(defn target [x] (add-i64 x 1))\n\
         /ask define a helper\n\
         y\n",
    );
    let log = std::fs::read_to_string(&log_path).expect("the log file must be readable");

    // +neg: NONE of the content-grain keys the trace owns may appear in the log.
    for content_key in [
        "\"form\"",
        "\"prose\"",
        "\"request\"",
        "\"response\"",
        "\"error_message\"",
        "\"content\"",
        "\"text\"",
        "\"transcript\"",
    ] {
        assert!(
            !log.contains(content_key),
            "the LOG must stay the compact index — content key {content_key} must \
             NOT appear (it belongs to the §17.21 trace, §17.20.3 / §28.4); log={log:?}"
        );
    }
    // +neg: the verbatim submitted FORM body must NOT leak into the log as a
    // value — the log records that a submit/repair happened + its `symbol`, never
    // the form's content (which the trace carries). The body `(add-i64 x x)` is
    // the form content; the log carries only `helper` (the symbol).
    assert!(
        !log.contains("(add-i64 x x)") && !log.contains("(defn helper"),
        "the LOG must NOT carry the verbatim form content (that is the trace's \
         job, §28.4) — found form text in log={log:?}"
    );
    // Positive sanity: the metadata index keys ARE present (the log still works).
    assert!(
        log.contains("\"event\"") && log.contains("\"symbol\""),
        "the log must still carry its metadata index keys, log={log:?}"
    );
}

// ---------------------------------------------------------------------------
// T4 — `CRANELISP_AGENT_TRACE=<path>` is SILENT + does NOT leak to stderr, and
// the stub session does not crash with the trace var set. Observable-e2e half
// of §17.21.1 (the trace-FILE-population half is the rig-MockModel UNIT test
// owed by /dev 5d — the stub never reaches `emit_*`, §28.2(2)).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.21.1 — `CRANELISP_AGENT_TRACE` set to a PATH is SILENT
// (nothing extra in the REPL — no banner, no per-exchange echo, no transcript
// change) and PATH-ONLY (the stderr sink is REMOVED — "there is no longer any
// `eprintln!` trace view"). This pins the observable half: with the var set to a
// file PATH, the stub session's transcript is byte-identical to the trace-off
// session AND nothing `[agent-trace]`-shaped leaks to stderr. RED on HEAD for a
// SUBTLE reason: HEAD treats `CRANELISP_AGENT_TRACE=<path>` as a TRUTHY value and
// (on the rig path) would `eprintln!` to stderr — the path-only swap (§28.1)
// removes the stderr sink. On the stub path no `emit_*` fires either way, so the
// no-stderr-leak holds; the load-bearing guard is the SILENT-transcript + the
// absence of the legacy `[agent-trace]` stderr marker the §28.1 swap deletes.
#[cfg(feature = "agent")]
#[test]
fn agent_trace_path_is_silent_no_stderr_leak() {
    // Trace OFF baseline.
    let off = stub_repl(
        TRACE_TURN_SCRIPT,
        PreludeVariant::PrimitivesOnly,
        "(defn target [x] (add-i64 x 1))\n\
         /ask define a helper\n\
         y\n",
    );
    // Trace ON: `CRANELISP_AGENT_TRACE` pointed at a per-test tmp file PATH.
    let cl = Cranelisp::new().repl().with_prelude(PreludeVariant::PrimitivesOnly).cli_flag("--agent");
    let trace_path = cl.tmpdir_path().join("trace.txt");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, TRACE_TURN_SCRIPT).unwrap();
    let on = cl
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .env("CRANELISP_AGENT_TRACE", trace_path.to_str().unwrap())
        .stdin(
            "(defn target [x] (add-i64 x 1))\n\
             /ask define a helper\n\
             y\n",
        )
        .output();

    // (i) SILENT: stdout byte-identical trace-on vs trace-off (modulo the
    // wall-clock prompt counter both runs carry regardless — masked as in P4.2).
    let mask = regex::Regex::new(r"\d+\+\d+ms; (\w+)> ").unwrap();
    let on_masked = mask.replace_all(&on.stdout, "T+Tms; $1> ");
    let off_masked = mask.replace_all(&off.stdout, "T+Tms; $1> ");
    assert_eq!(
        on_masked, off_masked,
        "`CRANELISP_AGENT_TRACE=<path>` must be SILENT — the transcript with the \
         trace ON must be BYTE-IDENTICAL to trace OFF (§17.21.1: no banner, no \
         per-exchange echo, nothing extra in stdout)"
    );
    // (ii) PATH-ONLY: the legacy `[agent-trace]` stderr view is REMOVED (§28.1).
    // No `[agent-trace]`-marked line may reach stderr with the var set to a path.
    assert!(
        !on.stderr.contains("[agent-trace]"),
        "the stderr trace sink is REMOVED (§17.21.1 / §28.1) — no `[agent-trace]` \
         line may reach stderr when `CRANELISP_AGENT_TRACE` is a PATH; stderr={}",
        on.stderr
    );
    // (iii) the session ran to completion cleanly with the trace var set.
    assert!(
        on.status.success(),
        "setting `CRANELISP_AGENT_TRACE` must not crash the session, exit={:?}, stderr={}",
        on.status,
        on.stderr
    );
}

// ---------------------------------------------------------------------------
// T5 — graceful on an UNWRITABLE trace path (+neg). Observable e2e.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.21.1 — graceful on an unwritable path: with
// `CRANELISP_AGENT_TRACE` set to a path that cannot be written (a file under a
// NONEXISTENT parent directory), the session MUST degrade silently — never crash,
// never spew errors into the REPL (the trace is a side channel; its failure never
// disturbs the session — identical to the §17.20.2 log contract). The agent turn
// still renders. GUARD (the stub never reaches `emit_*`, so the unwritable open
// is not even attempted on the stub path) — but it pins the contract the §28.1
// best-effort `let _ = …` append must honour when the rig path DOES write.
#[cfg(feature = "agent")]
#[test]
fn agent_trace_graceful_on_unwritable_path_neg() {
    let cl = Cranelisp::new().repl().with_prelude(PreludeVariant::PrimitivesOnly).cli_flag("--agent");
    // A path under a nonexistent parent directory — opening it for append fails.
    let unwritable = cl.tmpdir_path().join("no-such-dir").join("trace.txt");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, TRACE_TURN_SCRIPT).unwrap();
    let out = cl
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .env("CRANELISP_AGENT_TRACE", unwritable.to_str().unwrap())
        .stdin(
            "(defn target [x] (add-i64 x 1))\n\
             /ask define a helper\n\
             y\n",
        )
        .output();
    // (i) the session runs to completion — no crash/panic from a failed trace write.
    assert!(
        out.status.success(),
        "an unwritable `CRANELISP_AGENT_TRACE` path must NOT crash the session \
         (§17.21.1); exit={:?}, stderr={}",
        out.status,
        out.stderr
    );
    // (ii) the agent turn still rendered (the swallowed failure perturbed nothing).
    assert!(
        out.stdout.contains('\u{258c}'),
        "the agent turn must still render — a failed trace write must not disturb \
         the session (§17.21.1), stdout={}",
        out.stdout
    );
    // (iii) +neg: no trace-error chatter reached the REPL.
    let lc = out.stdout.to_lowercase();
    assert!(
        !lc.contains("could not open")
            && !lc.contains("permission denied")
            && !lc.contains("failed to write trace")
            && !lc.contains("no such file or directory"),
        "an unwritable trace path must degrade SILENTLY — NO trace-error chatter \
         may reach the REPL (§17.21.1), stdout={}",
        out.stdout
    );
    // (iv) the parent dir is genuinely absent — no file was forced into being.
    assert!(
        !unwritable.exists(),
        "the unwritable trace path must not have been written, path={unwritable:?}"
    );
}

// ---------------------------------------------------------------------------
// T6 — `CRANELISP_AGENT_TRACE` is INERT on the DEFAULT (non-`agent`) build
// (+neg). DEFAULT-LANE (not feature-gated). Mirrors P4.3 for the trace sink.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.21.1 — on a DEFAULT (non-`agent`) build, setting
// `CRANELISP_AGENT_TRACE` writes NOTHING: the trace exists ONLY in an
// `--features agent` build (feature-OFF stays byte-identical, §17.9). The +neg
// absence guard: a default-build session with the env set to a PATH produces NO
// trace file. Standing Lane-B floor for the §17.21 trace sink.
#[cfg(not(feature = "agent"))]
#[test]
fn agent_trace_absent_on_default_build_neg() {
    // NB: no `--agent` precondition — since S106 (FIXME 0539) `--agent` HARD-ERRORS
    // on a non-agent build; the trace-absence guard stands on a plain default-build
    // session (the trace sink is agent-feature-gated regardless of any flag).
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly);
    let trace_path = cl.tmpdir_path().join("default-build-trace.txt");
    let out = cl
        .env("CRANELISP_AGENT_TRACE", trace_path.to_str().unwrap())
        .stdin("(add-i64 1 2)\n")
        .output();
    assert!(
        out.stdout.contains("3"),
        "the default-build session must still eval, stdout={}",
        out.stdout
    );
    // +neg: NO trace file was written — the var is inert on the default build.
    assert!(
        !trace_path.exists(),
        "`CRANELISP_AGENT_TRACE` must be INERT on the default (non-`agent`) build \
         — NO trace file may be written (§17.21.1: the trace exists only in an \
         `--features agent` build), but a file appeared at {trace_path:?}"
    );
}

// ===========================================================================
// CF.1 — the validator containment floor (R2 layer b)
//
// `design/arch/repl-embedded-agent.md §11.3` layer (b): the agent's eval-thread
// typechecks (the S89 Build validator `validate_forms_dry_run`) call
// `check_forms` DIRECTLY on the eval thread with NO `catch_unwind` today
// (`src/worker.rs` `validate_forms_dry_run` → `check_forms`). ANY typechecker
// panic over uncontrolled (model-proposed) input unwinds the eval thread and
// CRASHES the REPL. Layer (b) wraps that eval-thread typecheck in
// `catch_unwind` — converting a caught unwind into a clean "could not validate"
// outcome so the session stays alive.
//
// DURABILITY HAZARD (the subtle one, flagged by /sprint): a CF.1 keyed on the
// 0432 Face-B form would be VACUOUS. On HEAD the 0432 form does NOT panic
// through the validator — the §4 ambiguity backstop catches it cleanly (the
// session already survives, verified live). And once 4d-tc's §9 root fix lands,
// the 0432 form panics even less. So a 0432-keyed CF.1 passes with NO
// `catch_unwind` present — it would guard nothing.
//
// To durably guard the `catch_unwind` FLOOR independent of the 0432 fix, CF.1
// must exercise the catch with a panic the root fix does NOT remove. It uses a
// TEST-ONLY PANIC-INJECTION SEAM (the 4d-int testability obligation, mirroring
// the S89 `#[cfg(test)]` colour-force seam): an env lever recognized only in
// test/feature builds that forces the eval-thread validator's `check_forms`
// path to panic. CF.1 then asserts the injected panic is CAUGHT, converted to a
// clean outcome, the REPL stays alive, and nothing crashes.
//
// 4d-int OBLIGATION (testability seam owed): provide
// `CRANELISP_AGENT_FORCE_VALIDATOR_PANIC=1` (a `#[cfg(any(test, feature =
// "agent"))]`-gated hook at the top of `validate_forms_dry_run`, or an
// equivalent magic-form mechanism) that makes the eval-thread validator
// `check_forms` panic. Without this seam CF.1 cannot durably guard the catch —
// it would be a vacuous-after-root-fix guard keyed on a non-panicking form.
// The §11.3(b) `catch_unwind` is the substantive fix that flips CF.1 green.
// ===========================================================================

/// The injection env lever (4d-int testability obligation). When set, the
/// eval-thread validator (`validate_forms_dry_run` → `check_forms`) is forced to
/// panic on a model-proposed `submit`, so the `catch_unwind` floor is exercised
/// independent of whether any real form (0432 or otherwise) currently panics.
#[cfg(feature = "agent")]
const FORCE_VALIDATOR_PANIC_ENV: &str = "CRANELISP_AGENT_FORCE_VALIDATOR_PANIC";

/// Stub-driven agent REPL with EXTRA env wired (here: the validator
/// panic-injection lever). Mirrors `stub_repl` but threads additional env vars
/// onto the spawned binary.
#[cfg(feature = "agent")]
fn stub_repl_with_env(
    script: &str,
    prelude: PreludeVariant,
    stdin: &str,
    extra_env: &[(&str, &str)],
) -> helpers::e2e::CrOutput {
    let mut cl = Cranelisp::new().repl().with_prelude(prelude).cli_flag("--agent");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, script).unwrap();
    cl = cl
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap());
    for (k, v) in extra_env {
        cl = cl.env(k, v);
    }
    cl.stdin(stdin).output()
}

// spec: repl/spec.md §17.14.3 — CF.1: a model-proposed `submit` whose
// eval-thread validation PANICS does NOT crash the REPL. The §11.3(b)
// `catch_unwind` floor converts the caught unwind into a clean "could not
// validate" outcome; the session stays alive (a FOLLOWING input still evals).
//
// RED on HEAD: the eval-thread `check_forms` in `validate_forms_dry_run` has no
// `catch_unwind`, so the injected panic unwinds the eval thread and crashes the
// REPL (the following input never evals). Green on the §11.3(b) floor.
//
// CF.1 uses the panic-INJECTION seam (not the 0432 form) so the guard is NOT
// vacuous-after-root-fix: the injected validator panic is one the 0432 §9 root
// fix does NOT remove (defence-in-depth for the NEXT uncontrolled-input panic —
// a Face-A shape or a future construct).
#[cfg(feature = "agent")]
#[test]
fn agent_validator_malformed_form_does_not_crash_repl() {
    // A well-formed `submit` that WOULD validate cleanly — but the injection
    // lever forces the eval-thread validator's `check_forms` to panic, standing
    // in for any uncontrolled-input typechecker panic. The `done:` is the
    // terminal turn; `(add-i64 7 8)` after the agent turn is the survival probe.
    let script = "tool: submit (defn helper [x] (add-i64 x x))\n\
                  done: I defined helper for you\n";
    let out = stub_repl_with_env(
        script,
        PreludeVariant::PrimitivesOnly,
        "/ask define helper\n\
         (add-i64 7 8)\n",
        &[(FORCE_VALIDATOR_PANIC_ENV, "1")],
    );

    // (i) the REPL stayed ALIVE: the following independent form still evals.
    // If the injected validator panic unwound the eval thread (no catch), the
    // process dies before this form runs and `:primitives/Int 15` is absent.
    assert!(
        out.stdout.contains(":primitives/Int 15"),
        "CF.1: an injected eval-thread validator panic MUST be caught by the \
         §11.3(b) `catch_unwind` floor — the REPL stays alive and the following \
         `(add-i64 7 8)` evals to `:primitives/Int 15`. RED on HEAD (no catch → \
         eval thread unwinds → process dies). stdout={} stderr={}",
        out.stdout,
        out.stderr
    );

    // (ii) +neg: no Rust panic banner / abnormal-termination chatter reached the
    // transcript. The catch converts the unwind into a clean validator outcome;
    // the user never sees an internal panic (the §16.2 silent contract holds —
    // a panicking validation is treated like a failed validation, not a crash).
    let lc = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        !lc.contains("panicked")
            && !lc.contains("note: run with `rust_backtrace")
            && !lc.contains("stack backtrace"),
        "CF.1 +neg: no Rust panic banner may reach the transcript — the caught \
         validator panic surfaces as a clean outcome, never an internal crash \
         (§11.3(b) / §16.2). stdout={} stderr={}",
        out.stdout,
        out.stderr
    );

    // (iii) the process did not die by signal (it exited cleanly via EOF).
    assert!(
        out.status.code().is_some(),
        "CF.1: the REPL MUST exit cleanly (an exit code, not a signal) — a \
         caught validator panic does not abort the process. status={:?} \
         stdout={} stderr={}",
        out.status,
        out.stdout,
        out.stderr
    );
}

// ===========================================================================
// Sprint 94 — FIXME 0430: docstring-into-source regen (the S89-W3-descoped
// `set-doc`). Plan: tests/plan/sprint-94.md §3. Candidate-1 ratified by /design:
// docstring-aware `render_decl_sexp` + the reconciliation rule (live
// `Def.docstring` authoritative when `Some`; the sexp's own docstring emitted
// only when the live field is `None`; never double-emit). /dev (src/) re-lands
// the `set-doc` Document-write surface against that contract.
//
// This is a DEFECT-grade persistence repro (the §17.15.3 durable-memory promise
// the S89 half-feature failed to deliver): the e2e rows owe a failing-not-ignored
// guard. The `set-doc` write tool is `#[cfg(feature = "agent")]` (descoped from
// `src/agent/{pull,stub}.rs` in S89 W3), so these run in the `agent` lane beside
// the existing Document-mode coverage, driven through the stub-provider-by-config
// mechanism.
//
// THE set-doc STUB-SCRIPT DSL (the /dev contract, also documented at the
// Cluster-C header above): `tool: set-doc <SYMBOL> <TEXT>` → a `set-doc`
// ToolCalls response. The argument is split on the FIRST whitespace: the first
// token is <SYMBOL> (the definition whose docstring to record); the REST of the
// line, verbatim, is <TEXT> — the docstring prose. The Document consultative gate
// fires ("record this as <symbol>'s docstring?"); on confirm the agent calls
// `apply_doc_edit(SYMBOL, TEXT)` + regenerates the backing `.cl` byte-stably so
// the live `Def.docstring` is rendered after the param vector (candidate 1).
// ---------------------------------------------------------------------------

/// The docstring prose the agent records via `set-doc` (must equal the TEXT in
/// `SET_DOC_DOUBLE`'s `tool:` line).
#[cfg(feature = "agent")]
const SET_DOC_DOCSTRING: &str = "doubles its argument by adding it to itself";

/// A stub script that records a docstring on `double`, then finishes.
#[cfg(feature = "agent")]
const SET_DOC_DOUBLE: &str =
    "tool: set-doc double doubles its argument by adding it to itself\n\
     done: recorded the docstring for you\n";

// spec: repl/spec.md §17.15.3 — the durable-memory promise ("next session it
// remembers") for a `set-doc` docstring edit. Session 1: the user defines
// `double` (no docstring), the agent records a docstring via `set-doc` (the
// consultative gate is confirmed with `y`), and the backing `user.cl` is
// regenerated with the docstring (docstring-aware `render_decl_sexp`, candidate
// 1). Session 2 (run_again — a FRESH binary over the SAME tmpdir, so `user.cl`
// is loaded from disk): `/doc double` shows the recorded docstring. RED-FIRST:
// the `set-doc` Document write surface + `apply_doc_edit` + docstring-aware
// renderer do not exist on HEAD (descoped S89 W3), so the docstring is never
// recorded and the fresh session's `/doc double` reports "no docstring".
#[cfg(feature = "agent")]
#[test]
fn set_doc_docstring_survives_session_restart() {
    // Session 1: define `double` (no docstring), then the agent records one.
    let first = stub_repl(
        SET_DOC_DOUBLE,
        PreludeVariant::PrimitivesOnly,
        "(defn double [x] (add-i64 x x))\n\
         /ask add a docstring to double\n\
         y\n",
    );
    // Sanity: session 1 left a backing file (the defn persists via regen) so the
    // read-back below is a genuine cross-session test, not an empty start.
    let user_cl = std::fs::read_to_string(first.tmpdir.join("user.cl"))
        .expect("session 1 must leave a `user.cl` backing file");
    assert!(
        user_cl.contains("double"),
        "session 1 must persist `double` to user.cl, user.cl={user_cl:?}"
    );

    // Session 2: a FRESH binary over the same tmpdir loads the regenerated
    // `user.cl`; `/doc double` must surface the recorded docstring (§17.15.3).
    let out = first
        .run_again()
        .repl()
        .stdin("/doc double\n/quit\n")
        .output();
    assert!(
        out.stdout.contains(SET_DOC_DOCSTRING),
        "the fresh session's `/doc double` must show the docstring recorded by \
         `set-doc` in the prior session (durable memory, §17.15.3); stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.15.3 + FIXME 0430 reconciliation rule (the negative
// face): a symbol whose original `(defn …)` source ALREADY carried a docstring,
// after `set-doc` OVERWRITES it then the session restarts, shows the NEW
// docstring EXACTLY ONCE — the live `Def.docstring` is authoritative and the
// stored sexp's docstring is dropped (never double-emitted). RED-FIRST: the
// `set-doc` write surface is descoped on HEAD, so the overwrite never applies —
// the fresh session shows the OLD docstring, not the new one.
#[cfg(feature = "agent")]
#[test]
fn set_doc_does_not_duplicate_docstring_on_restart_neg() {
    let old_doc = "old docstring before the agent edit";
    let new_doc = "new docstring after the agent edit";
    let set_doc_new = format!("tool: set-doc double {new_doc}\ndone: updated the docstring\n");

    // Session 1: define `double` WITH an original docstring, then overwrite it.
    let first = stub_repl(
        &set_doc_new,
        PreludeVariant::PrimitivesOnly,
        &format!(
            "(defn double \"{old_doc}\" [x] (add-i64 x x))\n\
             /ask change the docstring on double\n\
             y\n"
        ),
    );
    let _ = std::fs::read_to_string(first.tmpdir.join("user.cl"))
        .expect("session 1 must leave a `user.cl` backing file");

    // Session 2: the fresh session shows the NEW docstring exactly once.
    let out = first
        .run_again()
        .repl()
        .stdin("/doc double\n/quit\n")
        .output();
    // (i) the live (new) docstring won the reconciliation.
    assert!(
        out.stdout.contains(new_doc),
        "after `set-doc` overwrites the original docstring, the fresh session's \
         `/doc double` must show the NEW docstring (live `Def.docstring` wins, \
         §17.15.3 reconciliation); stdout={}",
        out.stdout
    );
    // (ii) +neg: the regenerated source carries the docstring EXACTLY ONCE — the
    // stored sexp's docstring is not double-emitted alongside the live one.
    let regen = std::fs::read_to_string(out.tmpdir.join("user.cl")).unwrap_or_default();
    assert_eq!(
        regen.matches(new_doc).count(),
        1,
        "the regenerated `user.cl` must carry the new docstring exactly ONCE — no \
         double-emit (reconciliation rule); user.cl={regen:?}"
    );
    // (iii) +neg: the superseded original docstring is gone (the live field, not
    // the stored sexp, is authoritative).
    assert!(
        !regen.contains(old_doc),
        "the superseded original docstring must NOT survive the overwrite — the \
         live `Def.docstring` is authoritative (§17.15.3); user.cl={regen:?}"
    );
}

// ---------------------------------------------------------------------------
// FIXME 0460 drain (S101 Wave 5) — §17.15.4 honest-failure e2e lane. The
// contract is unit-covered in `src/agent/pull.rs` (S94); these are the e2e
// complements so the honest-failure UX is guarded at the binary's outside
// surface (agent prose, not a raw compiler error — U5, §16.4) and §17.15.4
// gains its `[Tested+Neg …]` citations. GREEN at draft (coverage gap, not a
// defect — per the FIXME).
// ---------------------------------------------------------------------------

// spec: repl/spec.md §17.15.4 — honest failure, face 1: a `set-doc` on a
// target with NO LOCAL Def is refused with the not-found error (`no such
// definition`) — pinned for BOTH spec-named shapes: a never-defined name
// (`ghost`) AND a name that is only a re-exported prelude IMPORT (`add-i64`
// under PrimitivesOnly resolves as an Import entry, not a local `Def` —
// probed 2026-07-03). The consultative success line MUST NOT appear, and the
// live state is unchanged — the follow-up `/doc ghost` shows no
// spuriously-recorded docstring.
#[cfg(feature = "agent")]
#[test]
fn set_doc_missing_target_e2e_refused_no_false_recorded_neg() {
    let doc_text = "a ghost docstring that must never persist";
    let script = format!(
        "tool: set-doc ghost {doc_text}\n\
         done: tried to document ghost\n\
         tool: set-doc add-i64 an import docstring that must never persist\n\
         done: tried to document add-i64\n"
    );
    let out = stub_repl(
        &script,
        PreludeVariant::PrimitivesOnly,
        "/ask add a docstring to ghost\n\
         y\n\
         /ask add a docstring to add-i64\n\
         y\n\
         /doc ghost\n",
    );
    assert!(
        out.stdout.matches("no such definition").count() >= 2,
        "both the never-defined and import-only targets must surface `no such \
         definition` at the REPL (§17.15.4); stdout={}",
        out.stdout
    );
    // The consultative success line has the exact shape `recorded {target}'s
    // {noun}` (src/agent/pull.rs) — pin its absence precisely, since the
    // consultative QUESTION legitimately contains "record".
    assert!(
        !out.stdout.contains("recorded ghost's docstring")
            && !out.stdout.contains("recorded add-i64's docstring"),
        "a missing-target set-doc must NOT print the success line (§17.15.4); \
         stdout={}",
        out.stdout
    );
    // The live state is unchanged: after the refusals, /doc shows no recorded
    // text. Scoped to the tail AFTER the last refusal because the consultative
    // gate legitimately echoes the proposed text (§17.15.2a render-always).
    let tail = out.stdout.rsplit("no such definition").next().unwrap_or("");
    assert!(
        !tail.contains(doc_text),
        "/doc after the refusal must show no spuriously-recorded docstring \
         (§17.15.4); tail={tail} full stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.15.4 — honest failure, face 2: a `set-doc` on a
// target that DOES resolve locally but is NOT a user-defined function (here
// an ADT constructor, spec-named; a bare primitive under the prelude is an
// Import and takes face 1) is refused with a message naming that only a
// FUNCTION definition's docstring persists; no success line; the live
// docstring field stays unset (`/doc Red` after the refusal shows no
// recorded text).
#[cfg(feature = "agent")]
#[test]
fn set_doc_non_function_target_e2e_refused_not_recorded_neg() {
    let doc_text = "the colour of stop signs and sunsets";
    let script = format!("tool: set-doc Red {doc_text}\ndone: tried to document Red\n");
    let out = stub_repl(
        &script,
        PreludeVariant::PrimitivesOnly,
        "(deftype Color (Red))\n\
         /ask add a docstring to Red\n\
         y\n\
         /doc Red\n",
    );
    assert!(
        out.stdout.contains("only function definitions persist a docstring"),
        "the non-function refusal must name the function-only contract \
         (§17.15.4); stdout={}",
        out.stdout
    );
    // Exact success-line shape (see the missing-target sibling's note).
    assert!(
        !out.stdout.contains("recorded Red's docstring"),
        "a non-function set-doc must NOT print the success line (§17.15.4); \
         stdout={}",
        out.stdout
    );
    // Live field unset: /doc after the refusal carries no recorded text
    // (scoped past the gate's legitimate render-always echo of the proposal).
    let tail = out
        .stdout
        .rsplit("only function definitions persist a docstring")
        .next()
        .unwrap_or("");
    assert!(
        !tail.contains(doc_text),
        "/doc Red after the refusal must show no docstring (§17.15.4); \
         tail={tail} full stdout={}",
        out.stdout
    );
}

// ===========================================================================
// Sprint 109 — Observability (§17.20.3a field→metric acceptance) + §17.2.1
// probe channel. Plan: tests/plan/PLAN.md §S109 §F. Agent-feature build only
// (feature-off there is no agent and no log). Stub-driven, zero network; the
// activity log (`CRANELISP_AGENT_LOG`) is read back and asserted on raw JSONL
// text (the greppable-keys contract, §17.20.3). The six §17.20.3a fields
// (`question`, `error_class` on pull, `cause`, `primer_hash`/`harvest_len`,
// `scenario`, step accounting) are new this sprint, so the pos rows are RED
// (field absent) until /dev lands them; the metadata-only and probe-channel
// guards frame the contract they must preserve.
// ===========================================================================

/// Drive the stub agent with `CRANELISP_AGENT_LOG` enabled; return the session
/// output and the raw JSONL log text (empty string if no log was written).
#[cfg(feature = "agent")]
fn stub_log_session(
    script: &str,
    stdin: &str,
    extra_env: &[(&str, &str)],
) -> (helpers::e2e::CrOutput, String) {
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, script).unwrap();
    let mut cl = cl
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .env("CRANELISP_AGENT_LOG", "agent-activity.jsonl");
    for (k, v) in extra_env {
        cl = cl.env(k, v);
    }
    let out = cl.stdin(stdin).output();
    let log = if out.tmp_exists("agent-activity.jsonl") {
        out.read_tmp("agent-activity.jsonl")
    } else {
        String::new()
    };
    (out, log)
}

// spec: repl/spec.md §17.20.3a F1 — a `pull` record carries a `question` field
// (the specific thing the probe wanted to learn). RED until F1 lands.
#[cfg(feature = "agent")]
#[test]
fn agent_log_pull_records_question() {
    let (_, log) = stub_log_session(
        "tool: source foo\ndone: that is the source\n",
        "(defn foo [] (add-i64 1 2))\n/ask show me foo\n",
        &[],
    );
    assert!(
        log.contains("\"event\":\"pull\""),
        "the probe pull MUST be logged; log={log}"
    );
    assert!(
        log.contains("\"question\""),
        "F1: a `pull` record MUST carry a `question` field (§17.20.3a); log={log}"
    );
}

// spec: repl/spec.md §17.20.3b F1 (enumerated /dev-unit deferral — NOT authored
// here). `question` is a REQUIRED argument on every probe/pull tool in the
// §17.2.1 set; a probe with no `question` is a tool-schema non-conformance. The
// e2e cannot enumerate per-tool schema conformance — that is a /dev unit
// obligation in `src/agent`. ENUMERATED cases (one assertion per probe tool,
// fail-on-revert): each of `/type`, `/syntax`, `/sig`, `/info`, `/source`,
// `/doc`, `/exports`, `/list`, `/search`, `/refs` declares a required
// `question` argument, and the harness records it. Owner: /dev (src/agent).

// spec: repl/spec.md §17.20.3a F2 — a FAILED `pull` result carries an
// `error_class` (the classifier the repair path already runs). RED until F2
// lands.
#[cfg(feature = "agent")]
#[test]
fn agent_log_failed_pull_carries_error_class() {
    let (_, log) = stub_log_session(
        "tool: source no-such-symbol-xyz\ndone: could not find it\n",
        "/ask show me no-such-symbol-xyz\n",
        &[],
    );
    assert!(
        log.contains("\"event\":\"pull\""),
        "the failed probe pull MUST be logged; log={log}"
    );
    assert!(
        log.contains("\"error_class\""),
        "F2: a failed `pull` MUST carry an `error_class` field (§17.20.3a); log={log}"
    );
}

// spec: repl/spec.md §17.20.3a F3 — a `give_up` record carries a `cause`
// (`step_budget`/`model_declined`) and the dominant `error_class`. Verify-first:
// forcing a give_up e2e requires validator exhaustion (a persistently-broken
// submit). If the give_up cannot be forced through the stub, /dev pins the
// ENUMERATED unit cases at the give_up emission seam (fail-on-revert):
// (i) `step_budget` cause; (ii) `model_declined` cause; (iii) dominant-class
// computation from the run-up. RED until F3 lands (the `cause` field is absent
// even when a give_up fires).
#[cfg(feature = "agent")]
#[test]
fn agent_log_give_up_records_cause_and_dominant_class() {
    let broken = "tool: submit (defn broken [] (undefined-xyz 1))\n";
    let script = format!("{broken}{broken}{broken}{broken}{broken}done: I give up\n");
    let (_, log) = stub_log_session(&script, "/ask define broken\n", &[]);
    assert!(
        log.contains("\"event\":\"give_up\""),
        "a give_up MUST be logged when the agent abandons a broken submit \
         (verify-first — if unattainable e2e, /dev pins the enumerated unit \
         cases); log={log}"
    );
    assert!(
        log.contains("\"cause\""),
        "F3: a `give_up` record MUST carry a `cause` field (§17.20.3a); log={log}"
    );
}

// spec: repl/spec.md §17.20.3a F4 — the session-start (or first exchange) record
// stamps the context version: `primer_hash` + `harvest_len`. RED until F4 lands.
#[cfg(feature = "agent")]
#[test]
fn agent_log_session_start_stamps_context_version() {
    let (_, log) = stub_log_session("done: hello\n", "/ask hello\n", &[]);
    assert!(
        !log.is_empty(),
        "an /ask MUST produce at least one log record; log={log}"
    );
    assert!(
        log.contains("\"primer_hash\"") && log.contains("\"harvest_len\""),
        "F4: the context-version stamp (`primer_hash` + `harvest_len`) MUST be \
         recorded (§17.20.3a); log={log}"
    );
}

// spec: repl/spec.md §17.20.3a F5 + §17.20.3b — `CRANELISP_AGENT_SCENARIO` is
// stamped as a `scenario` field on EVERY log record. RED until F5 lands.
#[cfg(feature = "agent")]
#[test]
fn agent_log_scenario_env_stamped_on_every_record() {
    let (_, log) = stub_log_session(
        "tool: source foo\ndone: ok\n",
        "(defn foo [] (add-i64 1 2))\n/ask show foo\n",
        &[("CRANELISP_AGENT_SCENARIO", "safe-dial")],
    );
    assert!(!log.is_empty(), "records MUST be written; log={log}");
    for line in log.lines().filter(|l| !l.trim().is_empty()) {
        assert!(
            line.contains("\"scenario\":\"safe-dial\""),
            "F5: EVERY log record MUST carry the `scenario` tag (§17.20.3a); \
             line={line}"
        );
    }
}

// spec: repl/spec.md §17.20.3a F5 (NEG) — with `CRANELISP_AGENT_SCENARIO` unset,
// the `scenario` field is absent (or neutral), never a spurious value. GREEN
// today (no scenario field) — a fail-on-revert guard once F5 lands.
#[cfg(feature = "agent")]
#[test]
fn agent_log_neg_no_scenario_field_when_env_unset() {
    let (_, log) = stub_log_session("done: hello\n", "/ask hello\n", &[]);
    assert!(
        !log.contains("\"scenario\":\"safe-dial\""),
        "with the scenario env UNSET, no scenario value may be stamped; log={log}"
    );
}

// spec: repl/spec.md §17.20.3a F6 — a `submit` record carries step accounting
// (`step` / `steps_at_submit`). RED until F6 lands.
#[cfg(feature = "agent")]
#[test]
fn agent_log_submit_carries_step_accounting() {
    // `--yes` auto-accepts the confirm gate so the submit COMMITS and records.
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent")
        .cli_flag("--yes");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(
        &script_path,
        "tool: submit (defn bar [] (add-i64 20 22))\ndone: defined bar\n",
    )
    .unwrap();
    let out = cl
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .env("CRANELISP_AGENT_LOG", "agent-activity.jsonl")
        .stdin("/ask define bar\n")
        .output();
    let log = if out.tmp_exists("agent-activity.jsonl") {
        out.read_tmp("agent-activity.jsonl")
    } else {
        String::new()
    };
    assert!(
        log.contains("\"event\":\"submit\""),
        "a submit MUST be logged (committed under --yes); log={log}"
    );
    assert!(
        log.contains("\"steps_at_submit\"") || log.contains("\"step\""),
        "F6: a `submit` record MUST carry step accounting (§17.20.3a); log={log}"
    );
}

// spec: repl/spec.md §17.20.3 (NEG) — the log is metadata-only: it carries NO
// content (no form text, no error message, no model prose). GREEN — the contract
// every metric's substrate preserves.
#[cfg(feature = "agent")]
#[test]
fn agent_log_neg_carries_no_content_fields() {
    let (_, log) = stub_log_session(
        "tool: source foo\ndone: the private conclusion prose\n",
        "(defn foo [] (add-i64 1 2))\n/ask show foo\n",
        &[],
    );
    assert!(!log.is_empty(), "records MUST be written; log={log}");
    for key in ["\"form\"", "\"prose\"", "\"content\"", "\"message\"", "\"error_message\""] {
        assert!(
            !log.contains(key),
            "§17.20.3: the log MUST NOT carry a content field ({key}); log={log}"
        );
    }
    // Nor the model prose body itself.
    assert!(
        !log.contains("the private conclusion prose"),
        "§17.20.3: the log MUST NOT carry the model prose content; log={log}"
    );
}

// spec: repl/spec.md §17.2.1 (NEG) — probe traffic MUST NOT echo `agent> {cmd}`
// + its result into the user session; it routes to the private working channel
// (log/trace). RED today: §17.2 item 2 still echoes the probe command inline.
// defect: class=routing-misclassify locus=src/agent/pull.rs (probe pull echoed to the user session instead of the private channel) found=S108 owner=/dev
#[cfg(feature = "agent")]
#[test]
fn agent_probe_traffic_not_echoed_to_session_neg() {
    let (out, _) = stub_log_session(
        "tool: source foo\ndone: foo returns three\n",
        "(defn foo [] (add-i64 1 2))\n/ask show me foo\n",
        &[],
    );
    assert!(
        !out.stdout.contains("/source foo"),
        "§17.2.1: a probe's command MUST NOT be echoed into the user session; \
         stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.2.1 — the user DOES see the agent's conclusions (framed
// `▌` gutter prose) and the finished definition, even when probe traffic is
// hidden. GREEN.
#[cfg(feature = "agent")]
#[test]
fn agent_probe_conclusions_and_definition_still_shown() {
    let (out, _) = stub_log_session(
        "tool: source foo\ndone: foo returns three\n",
        "(defn foo [] (add-i64 1 2))\n/ask show me foo\n",
        &[],
    );
    assert!(
        out.stdout.contains("\u{258c}"),
        "the agent conclusions MUST be framed (§17.2.1); stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("foo returns three"),
        "the conclusion prose MUST render to the user (§17.2.1); stdout={}",
        out.stdout
    );
}
