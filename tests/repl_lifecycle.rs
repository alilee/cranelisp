// repl_lifecycle.rs — REPL session lifecycle (Sprint 64 Wave 3 Batch 7 sub-batch 2).
//
// Carries forward the session-mechanism assertions from the integration-tier
// `repl_experience.rs` (lifecycle slice), `ring3_repl.rs` (macro persistence),
// `v4_repl_eval.rs` (eval-cycle persistence + error recovery). Per
// the [current mode-canonicalisation guidance](plan/PLAN.md#mode-canonicalisation--repl-is-the-canonical-surface-for-language-conformance), canonical mode is REPL.
//
// Coverage (per `repl/spec.md §0.1, §1.2, §1.3, §2.3, §3.1, §5.2, §6.2, §11.4, §15.2,
// §15.6` and `spec/05-definitions.md §5.1, §5.2`, `spec/09-macros.md §9.2, §9.13`):
//   - REPL boot / banner / clean exit on EOF
//   - Multi-form sessions with definition persistence
//   - Recursive function definition inside REPL
//   - ADT define-then-match / define-then-use
//   - Type errors / parse errors / runtime errors do NOT corrupt the session
//   - Redefinition cycles (defn replaces defn; callers see new value)
//   - Macro persistence across evals
//
// What this file does NOT cover (lives elsewhere):
//   - Slash-command introspection — `repl_introspection.rs`
//   - Negative paths (errors from bad input shapes) — `repl_negative.rs`

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// Test-authoring shortcuts: see `tests/helpers/e2e.rs`
// `Cranelisp::repl_capture` / `repl_prims_capture`.
fn repl(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::repl_capture(lines)
}
fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::repl_prims_capture(lines)
}

// =============================================================================
// REPL boot — repl/spec.md §6.2 (Startup Banner) + §0.1 (REPL Mode)
// =============================================================================

// spec: repl/spec.md §6.2 — Startup Banner displays language name
#[test]
fn boot_shows_banner() {
    repl("").assert_stdout_contains("cranelisp REPL");
}

// spec: repl/spec.md §0.1 — REPL Mode exits on EOF
#[test]
fn boot_exits_clean_on_eof() {
    repl("").assert_ok();
}

// spec: repl/spec.md §6.2 — Startup Banner mentions /help
#[test]
fn boot_banner_mentions_help() {
    repl("").assert_stdout_contains("/help");
}

// =============================================================================
// §6.1 / §6.3 — First Five Minutes / First Session Journey
// =============================================================================

// spec: repl/spec.md §6.1 — First Five Minutes / §6.3 First Session Journey:
// a single END-TO-END journey driving the narrative arc a new user follows
// from launch to confidence, in ONE session so state carries between phases.
// The sub-steps are covered piecemeal elsewhere; this is the missing single
// journey test the §6.1/§6.3 gap calls for. Each numbered §6.1 capability is
// asserted in order:
//   1. banner advertises /help               (§6.1 step 1, §6.3 Phase 1)
//   2. evaluate an expression → typed result  (§6.1 step 2, §6.3 Phase 2)
//   3. define a fn → inferred type displayed   (§6.1 step 3, §6.3 Phase 3)
//   4. /list surfaces the user's definitions    (§6.1 step 4, §6.3 Phase 4)
//   5. /sig + /info explain a symbol             (§6.1 step 5, §6.3 Phase 4)
// Free-standing: uses the `add-i64` primitive (PrimitivesOnly prelude) rather
// than the `+` operator from §6.1's example, which would require the trait
// prelude (stdlib). The typed-result + inferred-type contract is identical.
#[test]
fn first_session_journey_launch_to_confidence() {
    let out = repl_prims(
        "(add-i64 1 2)\n\
         (defn id [x] x)\n\
         /list\n\
         /sig id\n\
         /info id\n",
    );
    let s = &out.stdout;
    // Phase 1 — Orientation: banner names the language and the /help hint.
    assert!(
        s.contains("cranelisp REPL") && s.contains("/help"),
        "Phase 1: banner MUST name the REPL and advertise /help \
         (repl/spec.md §6.1 step 1 / §6.3 Phase 1); got:\n{s}"
    );
    // Phase 2 — First evaluation: typed result in `:Type value` form.
    assert!(
        s.contains(":primitives/Int 3"),
        "Phase 2: a simple expression MUST yield a typed `:Type value` result \
         (repl/spec.md §6.1 step 2 / §6.3 Phase 2); got:\n{s}"
    );
    // Phase 3 — Defining things: defn shows the inferred type scheme + FQ name.
    assert!(
        s.contains(":(Fn [a] a) user/id"),
        "Phase 3: a defn MUST display its inferred type scheme + qualified name \
         (repl/spec.md §6.1 step 3 / §6.3 Phase 3); got:\n{s}"
    );
    // Phase 4 — Introspection: /list surfaces the user's own definition.
    assert!(
        s.contains("id"),
        "Phase 4: /list MUST surface the user's definitions \
         (repl/spec.md §6.1 step 4 / §6.3 Phase 4); got:\n{s}"
    );
    // Phase 5 — Help on a symbol: /sig + /info explain `id`.
    assert!(
        s.matches("user/id").count() >= 2,
        "Phase 5: /sig and /info MUST both explain the symbol `id` \
         (repl/spec.md §6.1 step 5 / §6.3 Phase 4); got:\n{s}"
    );
}

// =============================================================================
// Single-form evals — repl/spec.md §1.2 (Expression Results) / §1.3 (Definition Results)
// =============================================================================

// spec: repl/spec.md §1.2 — single bare expression evaluates and displays
#[test]
fn single_expr_evaluates() {
    repl_prims("(add-i64 2 3)\n").assert_stdout_contains(":primitives/Int 5");
}

// spec: repl/spec.md §1.3 — single defn registers and displays type
#[test]
fn single_defn_registers() {
    repl_prims("(defn square [x] (mul-i64 x x))\n").assert_stdout_contains("user/square ; defn");
}

// =============================================================================
// Definition persistence — repl/spec.md §15.2 (Session Restore) + §1.3
// =============================================================================

// spec: repl/spec.md §15.2 — defns persist across eval rounds in a session
#[test]
fn defn_then_call_in_next_form() {
    repl_prims(
        "(defn double [x] (mul-i64 x 2))
(double 21)
",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: repl/spec.md §15.2 — multiple defns coexist across eval rounds
#[test]
fn multiple_defns_coexist() {
    repl_prims(
        "(defn one [] 1)
(defn two [] 2)
(add-i64 (one) (two))
",
    )
    .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/05-definitions.md §5.1 — self-recursive defn at REPL (factorial)
#[test]
fn recursive_factorial() {
    repl_prims(
        "(defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
(fact 5)
",
    )
    .assert_stdout_contains(":primitives/Int 120");
}

// spec: spec/05-definitions.md §5.1 — self-recursive defn at REPL (fibonacci)
#[test]
fn recursive_fibonacci() {
    repl_prims(
        "(defn fib [n] (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))
(fib 7)
",
    )
    .assert_stdout_contains(":primitives/Int 13");
}

// =============================================================================
// ADT lifecycle — spec/05-definitions.md §5.2 + spec/06-pattern-matching.md §6.1
// =============================================================================

// spec: spec/05-definitions.md §5.2 — define ADT, then match in next form
#[test]
fn deftype_then_match() {
    repl_prims(
        "(deftype Color Red Green Blue)
(defn pick [c] (match c [Red 1 Green 2 Blue 3]))
(pick Green)
",
    )
    .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/05-definitions.md §5.2 — multiple ADTs coexist in REPL session
#[test]
fn multiple_adts_coexist() {
    repl_prims(
        "(deftype Color Red Green Blue)
(deftype Size Small Medium Large)
(defn size-rank [s] (match s [Small 1 Medium 2 Large 3]))
(size-rank Medium)
",
    )
    .assert_stdout_contains(":primitives/Int 2");
}

// =============================================================================
// Redefinition — repl/spec.md §15.6
// =============================================================================

// spec: repl/spec.md §15.6 — redefinition replaces previous defn
#[test]
fn redefinition_replaces_value() {
    repl_prims(
        "(defn foo [] 1)
(defn foo [] 2)
(foo)
",
    )
    .assert_stdout_contains(":primitives/Int 2");
}

// spec: repl/spec.md §15.6 — redefinition with different body shape
#[test]
fn redefinition_different_body() {
    repl_prims(
        "(defn calc [x] (add-i64 x 1))
(defn calc [x] (mul-i64 x 2))
(calc 5)
",
    )
    .assert_stdout_contains(":primitives/Int 10");
}

// spec: repl/spec.md §15.6 — redefinition propagates through caller chain
#[test]
fn redefinition_propagates_through_callers() {
    // First call: 10*2=20; after redef inner→5: 5*2=10. Both must appear.
    repl_prims(
        "(defn inner [] 10)
(defn outer [] (mul-i64 (inner) 2))
(outer)
(defn inner [] 5)
(outer)
",
    )
    .assert_stdout_contains_all(&[":primitives/Int 20", ":primitives/Int 10"]);
}

// spec: repl/spec.md §15.6 — redefinition propagates transitively through a
// 3-defn pipeline (caller -> mid-helper -> leaf-helper). The redefined helper
// is mid-pipeline; its new value must flow through both the caller and the
// original first-call observation. Distinct from the 1-caller / 1-helper
// `redefinition_propagates_through_callers` shape: this exercises transitive
// propagation through one extra layer of indirection.
// (carry: legacy/sketch_port.rs::sketch_repl_redefinition_updates_callers)
#[test]
fn redefinition_propagates_transitively_through_pipeline() {
    // First (pipeline 5): add1 -> 6, double -> 12. After redef add1 to +10:
    // (pipeline 5): add1 -> 15, double -> 30. Both observations required.
    repl_prims(
        "(defn add1 [x] (add-i64 x 1))
(defn double [x] (mul-i64 x 2))
(defn pipeline [x] (double (add1 x)))
(pipeline 5)
(defn add1 [x] (add-i64 x 10))
(pipeline 5)
",
    )
    .assert_stdout_contains_all(&[":primitives/Int 12", ":primitives/Int 30"]);
}

// =============================================================================
// Error recovery — repl/spec.md §5.2
// =============================================================================

// spec: repl/spec.md §5.2 — type error does not corrupt prior definitions
#[test]
fn type_error_preserves_prior_defs() {
    let out = repl_prims(
        "(defn good [] 42)
(add-i64 1 \"oops\")
(good)
",
    );
    // The error is reported; `good` still works.
    assert!(
        out.stdout.contains(":primitives/Int 42"),
        "after type error, good() must still return 42; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.2 — parse error does not corrupt prior definitions
#[test]
fn parse_error_preserves_prior_defs() {
    // Use a stray closing paren as the parse error — `((((` triggers
    // multi-line continuation and consumes subsequent lines.
    let out = repl_prims(
        "(defn good [] 99)
)bad
(good)
",
    );
    assert!(
        out.stdout.contains(":primitives/Int 99"),
        "after parse error, good() must still return 99; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.2 — multiple consecutive errors then success
#[test]
fn multiple_errors_then_success() {
    let out = repl_prims(
        "(undefined-symbol)
(another-undefined)
(add-i64 1 2)
",
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "session must continue after multiple errors; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.2 — failed defn does NOT pollute namespace
#[test]
fn failed_defn_does_not_pollute() {
    // A defn whose body has a type error should NOT register the symbol.
    // `broken` should be undefined; the bare reference produces an error
    // and the symbol must not appear in REPL output as a registered defn.
    repl_prims(
        "(defn broken [x] (add-i64 x \"nope\"))
broken
",
    )
    .assert_stdout_does_not_contain("user/broken ; defn");
}

// spec: repl/spec.md §5.2 — failed redefn preserves original
#[test]
fn failed_redefn_preserves_original() {
    let out = repl_prims(
        "(defn good [x] (add-i64 x 1))
(defn good [x] (add-i64 x \"nope\"))
(good 5)
",
    );
    // After the failed redef, `good 5` should still produce 6 from the original.
    assert!(
        out.stdout.contains(":primitives/Int 6"),
        "failed redefn must preserve original; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Macro persistence — spec/09-macros.md §9.13 (REPL Integration) + repl/spec.md §11.4
// =============================================================================

// spec: repl/spec.md §11.4 — defmacro persists across evals (Bare Macro Lookup)
#[test]
fn defmacro_persists_across_evals() {
    repl_prims(
        "(defmacro double [x] `(mul-i64 ~x 2))
(double 21)
",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/09-macros.md §9.2 — multi-clause defmacro dispatch (REPL persistence)
#[test]
fn multi_clause_defmacro_dispatches() {
    // 1-arg clause returns x → :Int 1; 2-arg clause returns y → :Int 2.
    repl_prims(
        "(defmacro pick ([x] x) ([x y] y))
(pick 1)
(pick 1 2)
",
    )
    .assert_stdout_contains_all(&[":primitives/Int 1", ":primitives/Int 2"]);
}

// =============================================================================
// Builds — sanity that the REPL handles longer transcripts
// =============================================================================

// spec: repl/spec.md §15.2 — many sequential evals don't degrade
#[test]
fn many_sequential_evals() {
    let mut input = String::new();
    for i in 0..20 {
        input.push_str(&format!("(add-i64 {} 1)\n", i));
    }
    let out = repl_prims(&input).assert_ok();
    // Should see at least the last value (`(+ 19 1) = 20`).
    assert!(
        out.stdout.contains(":primitives/Int 20"),
        "20 sequential evals must complete; got tail:\n{}",
        out.stdout
            .lines()
            .rev()
            .take(5)
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// spec: repl/spec.md §15.6 — redefining the same fn many times in a session
#[test]
fn many_redefinitions_same_name() {
    let mut input = String::new();
    for i in 0..10 {
        input.push_str(&format!("(defn x [] {})\n", i));
    }
    input.push_str("(x)\n");
    repl_prims(&input).assert_stdout_contains(":primitives/Int 9");
}

// =============================================================================
// Multi-form composition — repl/spec.md §1.6
// =============================================================================

// spec: repl/spec.md §15.2 — incremental program build-up
#[test]
fn incremental_build_up() {
    repl_prims(
        "(defn pair-add [a b] (add-i64 a b))
(defn triple-add [a b c] (pair-add a (pair-add b c)))
(triple-add 1 2 3)
",
    )
    .assert_stdout_contains(":primitives/Int 6");
}

// spec: repl/spec.md §15.2 — interleaved defns and bare expressions
#[test]
fn interleaved_defns_and_exprs() {
    repl_prims(
        "(defn x [] 5)
(x)
(defn y [] 10)
(add-i64 (x) (y))
",
    )
    .assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 15"]);
}

// =============================================================================
// /mod — module switching — repl/spec.md §3
// =============================================================================

// spec: repl/spec.md §3.1 — /mod command (no-arg variant shows current module)
#[test]
fn mod_shows_current() {
    let out = repl("/mod\n").assert_ok();
    // Default module is `user`.
    assert!(
        out.stdout.contains("user"),
        "/mod must mention 'user' default module; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Empty / blank input handling — repl/spec.md §1.5
// =============================================================================

// spec: repl/spec.md §2.3 — blank line is silent (no error, no result line)
#[test]
fn blank_line_silent() {
    let out = repl("\n\n\n");
    assert!(
        !out.stdout.to_lowercase().contains("error"),
        "blank lines must not error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Redefinition GOT propagation — Wave 5.6 dedupe-recovery supplement
// =============================================================================

// spec: repl/spec.md §15.6 — redefinition propagates to a live caller via
// the GOT. This is the "caller defined first, helper redefined while the
// caller is still alive in the session, caller re-evaluated" angle: the
// existing `redefinition_propagates_through_callers` covers the same shape
// but the GOT propagation timing is load-bearing enough that the
// originating ring0 angle is preserved as a discrete REGRESSION-GUARD.
// (carry: legacy/ring0.rs::repl_redefinition_updates_callers)
#[test]
fn redefinition_updates_live_callers() {
    // Define helper, define caller (which closes over helper via GOT),
    // call caller -> 11; redefine helper to add 2 instead of 1; call
    // caller again -> 12. Both result lines must appear in stdout.
    repl_prims(
        "(defn helper [x] (add-i64 x 1))
(defn caller [] (helper 10))
(caller)
(defn helper [x] (add-i64 x 2))
(caller)
",
    )
    .assert_stdout_contains_all(&[":primitives/Int 11", ":primitives/Int 12"]);
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-1 GAP-COVER carry-forwards.
// =============================================================================

// spec: repl/spec.md §2.1 — Primary Prompt format `{N}+{N}ms; user>`. The
// startup output must contain the timing-prefix `ms;` separator and the
// module-name `user>` suffix. Distinct from `boot_shows_banner` (which
// asserts the header text only).
// (carry: legacy/e2e.rs::e2e_s2_1_prompt_format)
#[test]
fn boot_prompt_format_timing_and_module() {
    let out = repl("");
    assert!(
        out.stdout.contains("ms;"),
        "prompt MUST contain the timing separator 'ms;' per repl/spec.md §2.1; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("user>"),
        "prompt MUST end with the module suffix 'user>' per repl/spec.md §2.1; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §2.2 — Continuation Prompt: when input is incomplete
// (e.g. an unclosed `(`), subsequent lines are prefixed with `...` until
// the form is closed. After closure the form evaluates to its result.
// (carry: legacy/e2e.rs::e2e_s2_2_continuation_prompt)
#[test]
fn continuation_prompt_for_unclosed_paren() {
    let out = repl_prims(
        "(add-i64
  2 3)
",
    );
    assert!(
        out.stdout.contains("..."),
        "incomplete input MUST emit `...` continuation marker per §2.2; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "after closure, the multi-line form MUST evaluate to `:primitives/Int 5`; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-2 GAP-COVER carry-forward.
// =============================================================================

// spec: (none — regression-only)
// REGRESSION-GUARD: cross-session cache isolation. Two independent
// REPL subprocess invocations MUST NOT share definitions through any
// shared on-disk cache or state. The first session defines `secret`;
// the second session, started fresh in its own TempDir, MUST report
// `secret` as undefined. Defends against accidental cache leakage
// across `cranelisp` invocations.
// (carry: legacy/e2e.rs::e2e_isolation_no_shared_state)
#[test]
fn two_independent_sessions_isolation_neg_no_state_leak() {
    // Session A: define `secret`.
    let out_a = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::PrimitivesOnly)
        .stdin("(defn secret [x] (mul-i64 x 99))\n")
        .output()
        .assert_ok();
    // Sanity: A actually compiled the defn.
    assert!(
        out_a.stdout.contains("user/secret") || out_a.stdout.contains("secret"),
        "session A MUST register 'secret' (got:\n{}\n)",
        out_a.stdout
    );

    // Session B: independent TempDir; tries to call A's `secret`. MUST
    // see an undefined-name error (no state leak from session A).
    let out_b = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::PrimitivesOnly)
        .stdin("(secret 1)\n")
        .output();
    let combined = format!("{}{}", out_b.stdout, out_b.stderr);
    assert!(
        combined.contains("Error:"),
        "session B MUST NOT see 'secret' from session A — cross-session state leak detected; \
         combined stdout+stderr:\n{}",
        combined
    );
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-3 GAP-COVER carry-forwards.
// =============================================================================

/// A REPL whose project root holds the module `name` (`name.cl`), loaded by a
/// qualified reference before `stdin` runs, so `/mod name` targets an
/// existing module (repl/spec/03-slash-commands.md §3.9).
fn repl_with_loaded_module(name: &str, stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .file(&format!("{name}.cl"), "(defn seed [] 0)\n")
        .stdin(&format!("({name}/seed)\n{stdin}"))
        .output()
}

// spec: repl/spec.md §8 — Scenario 1: `/mod math` switches the prompt
// to `math>`. Distinct from `mod_shows_current` which exercises the
// no-arg form (current module display).
// (carry: legacy/e2e.rs::e2e_s8_mod_switch_namespace)
#[test]
fn mod_switch_to_named_module_changes_prompt() {
    let out = repl_with_loaded_module("math", "/mod math\n");
    assert!(
        out.stdout.contains("math>"),
        "/mod math MUST switch the prompt to 'math>' per repl/spec.md §8 Scenario 1; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §8 — Scenario 2: `/mod math` then `/mod user`
// performs a round-trip — both `math>` and `user>` prompts MUST appear.
// Distinct from `mod_switch_to_named_module_changes_prompt` (single
// switch): this asserts the round-trip path.
// (carry: legacy/e2e.rs::e2e_s8_mod_switch_back)
#[test]
fn mod_switch_round_trip_math_to_user() {
    let out = repl_with_loaded_module("math", "/mod math\n/mod user\n");
    assert!(
        out.stdout.contains("math>") && out.stdout.contains("user>"),
        "/mod round-trip MUST surface both 'math>' and 'user>' prompts per §8 Scenario 2; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// S78 §1 — Entry module is first-class; the REPL targets the ENTRY module,
// not a hardcoded `"user"`. design/int/int.md §6.5.
//
// A REPL launched with a positional target (`cranelisp myapp`) registers
// `myapp` as the entry module (`main.rs` resolve_target → register_module).
// The REPL cursor (`current_repl_module`) and the `/mod` no-arg "home"
// target are the ENTRY module — `"user"` is ONLY the default name when no
// target is given. These tests run the binary with a positional entry name
// via `cli_flag` (REPL mode, no `--run`).
//
// RED-BY-DESIGN until §1 lands: `current_repl_module` is hardcoded to
// `"user"` at `session_v4.rs:1154`, and `handle_mod("")` hardcodes `"user"`
// at `session_v4.rs:2682`. So today the prompt shows `user>` and defns land
// in `user/` even when the entry is `myapp`. The §1 fix threads the entry
// name through, making these GREEN.
// =============================================================================

// spec: design/int/int.md §6.5 — the REPL prompt reflects the
//   ENTRY module. Launched as `cranelisp myapp`, the prompt MUST be `myapp>`,
//   not the hardcoded `user>`. RED until `current_repl_module` is seeded with
//   the entry name.
#[test]
fn repl_prompt_targets_entry_module_not_hardcoded_user() {
    let out = Cranelisp::new()
        .repl()
        .file("myapp.cl", "(defn main [] 0)")
        .cli_flag("myapp")
        .stdin("\n")
        .output()
        .assert_ok();
    assert!(
        out.stdout.contains("myapp>"),
        "REPL with entry 'myapp' MUST show prompt 'myapp>' (the entry module), \
         not a hardcoded 'user>' (design/int/int.md §6.5); got:\n{}",
        out.stdout
    );
}

// spec: design/int/int.md §6.5 (negative) — when the entry
//   module is `myapp`, the REPL MUST NOT operate in a `user` module. A bare
//   `(defn ...)` lands in the entry module, so its display is `myapp/...`,
//   NOT `user/...`. Verifies the wrong module does not leak in.
#[test]
fn repl_defn_lands_in_entry_module_neg_not_user() {
    let out = Cranelisp::new()
        .repl()
        .file("myapp.cl", "(defn main [] 0)")
        .cli_flag("myapp")
        .stdin("(defn foo [] 1)\n")
        .output()
        .assert_ok();
    assert!(
        out.stdout.contains("myapp/foo"),
        "a defn in a REPL with entry 'myapp' MUST register as 'myapp/foo' \
         (the entry module), got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("user/foo"),
        "a defn in a REPL with entry 'myapp' MUST NOT land in a 'user' module \
         (design/int/int.md §6.5 — `\"user\"` is not privileged); got:\n{}",
        out.stdout
    );
}

// spec: repl/spec/03-slash-commands.md §3.9 — `/mod` with NO argument returns
//   to the ENTRY module ("home"), not a literal `"user"`. With entry `myapp`,
//   after `/mod scratch` a bare `/mod` MUST return the prompt to `myapp>`.
//   RED until `handle_mod("")` resolves to the entry module.
#[test]
fn mod_no_arg_returns_to_entry_module_not_user() {
    let out = Cranelisp::new()
        .repl()
        .file("myapp.cl", "(defn main [] 0)")
        .file("scratch.cl", "(defn seed [] 0)\n")
        .cli_flag("myapp")
        .stdin("(scratch/seed)\n/mod scratch\n/mod\n")
        .output()
        .assert_ok();
    // After the no-arg `/mod` the prompt must return to the entry module.
    // We assert the final prompt is `myapp>` (the entry), not `user>`.
    let returned_to_entry = out
        .stdout
        .rsplit("scratch>")
        .next()
        .map(|tail| tail.contains("myapp>"))
        .unwrap_or(false);
    assert!(
        returned_to_entry,
        "`/mod` no-arg MUST return to the entry module 'myapp', not a hardcoded \
         'user' (design/int/int.md §6.5); got:\n{}",
        out.stdout
    );
}

// spec: repl/spec/03-slash-commands.md §3.9 — regression (GREEN): when NO
//   target is given, the entry module defaults to `"user"`, so `/mod` no-arg
//   "home" IS `user>`. This pins that `"user"` survives as the legitimate
//   default name (not as a privileged identity).
#[test]
fn mod_no_arg_default_entry_is_user() {
    let out = repl_with_loaded_module("scratch", "/mod scratch\n/mod\n").assert_ok();
    let returned_to_user = out
        .stdout
        .rsplit("scratch>")
        .next()
        .map(|tail| tail.contains("user>"))
        .unwrap_or(false);
    assert!(
        returned_to_user,
        "with no CLI target, `/mod` no-arg MUST return to the default entry \
         'user' (design/int/int.md §6.5); got:\n{}",
        out.stdout
    );
}

// =============================================================================
// §3.9 Target module — `/mod <name>` switches to the module the language's
// module-name resolution finds, loading it if needed, and never creates one
// =============================================================================

/// Each input line of a piped REPL session as (prompt module, output):
/// element `k` is the prompt the `k+1`th line was entered at, with that
/// line's output. A prompt reads `<elapsed>ms; <module>> `.
fn prompted_turns(stdout: &str) -> Vec<(&str, &str)> {
    stdout
        .split("ms; ")
        .skip(1)
        .filter_map(|chunk| chunk.split_once("> "))
        .collect()
}

/// Whether `/mod`'s output reports an unknown module named `name`.
fn reports_unknown_module(output: &str, name: &str) -> bool {
    let lower = output.to_lowercase();
    output.contains(name) && (lower.contains("not found") || lower.contains("unknown"))
}

fn assert_legs(violated: &[&str], out: &helpers::e2e::CrOutput, context: &str) {
    assert!(
        violated.is_empty(),
        "violated:\n- {}\nstdout:\n{}\nstderr:\n{}\n{context}",
        violated.join("\n- "),
        out.stdout,
        out.stderr
    );
}

// spec: repl/spec/03-slash-commands.md §3.9 — Target module: `nonexistent`
// names no module, so `/mod nonexistent` reports an unknown-module error naming
// it and leaves `user` active: the following definition lands in `user`. No
// module is created: `/exports nonexistent` still finds none, and no
// `nonexistent.cl` is written. repl/spec/08-module-demos.md §8 Scenario 7. NAV-1.
// DEFECT (open): `/mod nonexistent` switches to a new blank module.
// defect: class=silent-accept locus=src/repl/commands.rs::handle_mod found=S122 owner=/dev — provisional until design places the fix: ensure_module_exists creates a blank table for any name that is not loaded
#[test]
fn mod_unknown_module_neg_not_created_and_active_module_unchanged() {
    let out = repl("/mod nonexistent\n(defn z [] 1)\n/exports nonexistent\n/quit\n");
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or(("", ""));
    let mut violated = Vec::new();
    let mut check = |holds: bool, leg: &'static str| {
        if !holds {
            violated.push(leg);
        }
    };
    check(
        reports_unknown_module(turn(0).1, "nonexistent"),
        "`/mod nonexistent` reports an unknown-module error naming `nonexistent`",
    );
    check(
        t.iter().all(|(module, _)| *module == "user"),
        "every prompt stays `user>`",
    );
    check(
        turn(1).1.contains("user/z") && !turn(1).1.contains("nonexistent/z"),
        "`(defn z [] 1)` lands in `user`",
    );
    check(
        reports_unknown_module(turn(2).1, "nonexistent"),
        "`/exports nonexistent` still reports the module unknown",
    );
    check(
        !out.tmp_exists("nonexistent.cl"),
        "no `nonexistent.cl` is written",
    );
    assert_legs(&violated, &out, "");
}

// spec: repl/spec/03-slash-commands.md §3.9 — Target module: nothing has loaded
// `lib.cl`, so `/mod lib` loads it and switches to it. `(keep-me)` gives 42
// there, and the preceding definition keeps `(defn keep-me [] 42)` in
// `lib.cl`. repl/spec/14-file-watching.md §14.1. ACT-1010 M2; NAV-2.
// DEFECT (open): `/mod lib` switches to a new blank `lib`, so `(keep-me)` is
// undefined and `(defn z [] 1)` regenerates `lib.cl` without `keep-me`.
// defect: class=silent-accept locus=src/repl/commands.rs::handle_mod found=S122 owner=/dev — provisional until design places the fix: ensure_module_exists creates a blank table for any name that is not loaded
#[test]
fn mod_unloaded_module_is_loaded_and_its_file_kept() {
    let out = Cranelisp::new()
        .repl()
        .file("lib.cl", "(defn keep-me [] 42)\n")
        .stdin("/mod lib\n(defn z [] 1)\n(keep-me)\n/quit\n")
        .output();
    let t = prompted_turns(&out.stdout);
    let lib = out.read_tmp("lib.cl");
    let mut violated = Vec::new();
    let mut check = |holds: bool, leg: &'static str| {
        if !holds {
            violated.push(leg);
        }
    };
    check(
        t.get(2).is_some_and(|(module, output)| {
            *module == "lib" && output.contains(":primitives/Int 42")
        }),
        "`(keep-me)` in `lib` gives 42",
    );
    check(
        lib.contains("(defn keep-me [] 42)"),
        "lib.cl still holds `(defn keep-me [] 42)`",
    );
    assert_legs(&violated, &out, &format!("lib.cl at exit:\n{lib}"));
}

const ROOT_Y: &str = "(defn which [] 2)\n";

/// The root module `y` (`y.cl`) and `user/y.cl` both provide `which`; `user`
/// declares the submodule `user.y` only when `declares_child`. `other/o`
/// loads the root `y` through `other`'s import. Turns: 1 `(other/o)`,
/// 2 `/mod y`, 3 `(defn z [] 3)`, 4 `(which)`.
fn dual_name_session(declares_child: bool) -> helpers::e2e::CrOutput {
    let user = if declares_child {
        "(mod y)\n(defn g [] 0)\n"
    } else {
        "(defn g [] 0)\n"
    };
    Cranelisp::new()
        .repl()
        .file("y.cl", ROOT_Y)
        .file("user/y.cl", "(defn which [] 1)\n")
        .file("other.cl", "(import [y [which]])\n(defn o [] (which))\n")
        .user(user)
        .stdin("(other/o)\n/mod y\n(defn z [] 3)\n(which)\n/quit\n")
        .output()
}

// spec: repl/spec/03-slash-commands.md §3.9 — Target module: `/mod <name>`
// resolves `<name>` from the active module by the language's module-name
// resolution. `user` declares `(mod y)` and a root `y.cl` exists (the root `y`
// is also loaded), so under spec/08-modules.md §8.11.2.1 `/mod y` switches to
// the submodule `user.y`: the prompt is `user.y>`, `(defn z [] 3)` lands in
// `user.y`, `(which)` gives `user.y`'s 1, and the root `y.cl` is untouched.
// The control
// `mod_bare_name_resolves_root_module_without_declared_submodule_control`
// differs only in the `(mod y)` declaration.
// DEFECT (open): `/mod` reads `y` as an absolute module path and switches to
// the root `y`.
// defect: class=wrong-scope-lookup locus=src/repl/commands.rs::handle_mod found=S122 owner=/dev — provisional: the target is read as an absolute path, not by the language's module-name resolution
#[test]
fn mod_bare_name_resolves_declared_submodule_over_root_module() {
    let out = dual_name_session(true);
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or(("", ""));
    let mut violated = Vec::new();
    let mut check = |holds: bool, leg: &'static str| {
        if !holds {
            violated.push(leg);
        }
    };
    check(
        turn(0).1.contains(":primitives/Int 2"),
        "precondition: `(other/o)` loads the root `y` and gives 2",
    );
    check(
        turn(2).0 == "user.y",
        "after `/mod y` the prompt is `user.y>`",
    );
    check(
        turn(2).1.contains("user.y/z"),
        "`(defn z [] 3)` lands in `user.y`",
    );
    check(
        turn(3).1.contains(":primitives/Int 1"),
        "`(which)` gives the submodule's 1",
    );
    check(
        out.read_tmp("y.cl") == ROOT_Y,
        "the root `y.cl` is unchanged",
    );
    assert_legs(&violated, &out, "");
}

// spec: repl/spec/03-slash-commands.md §3.9 — Target module: `user` declares
// no submodule `y`, so `/mod y` resolves to the root module `y`
// (spec/08-modules.md §8.11.2): the prompt is `y>`, `(defn z [] 3)` lands in
// `y`, and `(which)` gives the root's 2. The control for
// `mod_bare_name_resolves_declared_submodule_over_root_module`.
#[test]
fn mod_bare_name_resolves_root_module_without_declared_submodule_control() {
    let out = dual_name_session(false);
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or(("", ""));
    let mut violated = Vec::new();
    let mut check = |holds: bool, leg: &'static str| {
        if !holds {
            violated.push(leg);
        }
    };
    check(
        turn(0).1.contains(":primitives/Int 2"),
        "precondition: `(other/o)` loads the root `y` and gives 2",
    );
    check(turn(2).0 == "y", "after `/mod y` the prompt is `y>`");
    check(
        turn(2).1.contains(" y/z") && !turn(2).1.contains("user.y/z"),
        "`(defn z [] 3)` lands in the root `y`",
    );
    check(
        turn(3).1.contains(":primitives/Int 2"),
        "`(which)` gives the root's 2",
    );
    assert_legs(&violated, &out, "");
}

/// `user` imports `f` from `lib` under the module alias `lib-alias`
/// (spec/08-modules.md §8.3.4). Turns: 1 `/mod <target>`, 2 `(defn z [] 1)`.
fn aliased_lib_session(target: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .file("lib.cl", "(defn f [] 1)\n")
        .user("(import [(lib lib-alias) [f]])\n")
        .stdin(&format!("/mod {target}\n(defn z [] 1)\n/quit\n"))
        .output()
}

// spec: repl/spec/03-slash-commands.md §3.9 — Target module: module-name
// resolution (spec/08-modules.md §8.11.2) does not read import aliases, which
// only qualified names substitute (§8.6.6 step 1). So `lib-alias`, an alias of
// the loaded `lib`, names no module: `/mod lib-alias` reports an unknown-module
// error naming it, `user` stays active and receives `(defn z [] 1)`, `lib.cl` is
// unchanged, and no `lib-alias.cl` is written. The control
// `mod_module_name_of_aliased_import_switches_to_it_control` differs only in
// naming `lib`.
// DEFECT (open): `/mod lib-alias` switches to a new blank module `lib-alias`.
// defect: class=silent-accept locus=src/repl/commands.rs::handle_mod found=S122 owner=/dev — provisional until design places the fix: ensure_module_exists creates a blank table for any name that is not loaded; the cell also refuses a fix that resolves through the qualified-name alias step
#[test]
fn mod_import_alias_neg_not_a_module_name() {
    let out = aliased_lib_session("lib-alias");
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or(("", ""));
    let mut violated = Vec::new();
    let mut check = |holds: bool, leg: &'static str| {
        if !holds {
            violated.push(leg);
        }
    };
    check(
        reports_unknown_module(turn(0).1, "lib-alias"),
        "`/mod lib-alias` reports an unknown-module error naming `lib-alias`",
    );
    check(
        t.iter().all(|(module, _)| *module == "user"),
        "every prompt stays `user>`",
    );
    check(
        turn(1).1.contains("user/z"),
        "`(defn z [] 1)` lands in `user`",
    );
    check(
        out.read_tmp("lib.cl") == "(defn f [] 1)\n",
        "lib.cl is unchanged",
    );
    check(
        !out.tmp_exists("lib-alias.cl"),
        "no `lib-alias.cl` is written",
    );
    assert_legs(&violated, &out, "");
}

// spec: repl/spec/03-slash-commands.md §3.9 — Target module: `/mod lib` names
// the loaded module `lib`, imported by `user` under an alias, and switches to
// it: the prompt is `lib>` and `(defn z [] 1)` lands in `lib`. The control for
// `mod_import_alias_neg_not_a_module_name`.
#[test]
fn mod_module_name_of_aliased_import_switches_to_it_control() {
    let out = aliased_lib_session("lib");
    let t = prompted_turns(&out.stdout);
    let switched = t
        .get(1)
        .is_some_and(|(module, output)| *module == "lib" && output.contains("lib/z"));
    assert!(
        switched,
        "`/mod lib` switches to `lib`, where `(defn z [] 1)` lands\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// S106 — FIXME 0551: piped `read-line` MUST NOT leak the next input line, and the
// REPL session MUST continue after a read-line turn. The interactive-TTY exit
// (fd-0 O_NONBLOCK leak → REPL exits) is TTY-only and NOT reachable through the
// piped-stdin harness (no PTY — harness gap G-1); the fd-flag-restore and
// WouldBlock-≠-EOF seams get named /dev UNIT tests (platforms/stdio + src/main.rs).
// These e2e guards pin the REACHABLE piped-mode behaviour (the piped-vs-interactive
// divergence noted in the FIXME).
// =============================================================================

/// A REPL session with the workspace `stdio` platform available and a `main` that
/// reads a line then prints it.
const READ_LINE_MAIN: &str = "(platform stdio)\n\
     (import [platform.stdio [print read-line]])\n\
     (defn m [] (bind (read-line) (fn [l] (print l))))\n";

// spec: repl/spec.md §10.1 — [+neg] a piped `read-line` turn MUST consume its
// input line, NOT leak it to the REPL reader as an `undefined variable`. RED on
// HEAD (FIXME 0551): the piped read-line returns immediately without consuming the
// next line (`zzleak`), which then leaks to the reader as a type/undefined error.
#[test]
fn piped_read_line_does_not_leak_next_line_as_undefined_var_neg() {
    let out = Cranelisp::new()
        .repl()
        .use_workspace_platforms()
        .with_prelude(helpers::e2e::PreludeVariant::PrimitivesOnly)
        .stdin(&format!("{READ_LINE_MAIN}(m)\nzzleak\n(add-i64 4 5)\n",))
        .output();
    // Neg: the read-line input line MUST NOT leak to the REPL reader.
    assert!(
        !out.stdout.contains("undefined variable: zzleak"),
        "a piped `read-line` MUST consume its input line, not leak `zzleak` to the \
         REPL reader as an undefined variable (FIXME 0551); stdout:\n{}",
        out.stdout
    );
    // Pos: the subsequent expression still evaluates.
    assert!(
        out.stdout.contains(":primitives/Int 9"),
        "the form following the read-line turn MUST still evaluate; stdout:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §10.1 — the REPL session MUST continue after a `read-line`
// turn: a plain form issued after it still evaluates (the session did not
// terminate early). In piped mode the session already continues (the TTY-only
// early-exit is not e2e-reachable — harness gap G-1); this is the reachable
// robustness guard that a read-line turn does not silently kill the session.
#[test]
fn piped_read_line_session_continues_after_eval() {
    let out = Cranelisp::new()
        .repl()
        .use_workspace_platforms()
        .with_prelude(helpers::e2e::PreludeVariant::PrimitivesOnly)
        .stdin(&format!("{READ_LINE_MAIN}(m)\n\n(add-i64 20 22)\n"))
        .output();
    assert!(
        out.stdout.contains(":primitives/Int 42"),
        "the session MUST continue after a read-line turn — a following `(add-i64 \
         20 22)` MUST evaluate to 42 (FIXME 0551); stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// S106 — FIXME 0544: interactive line editor (rustyline, TTY-gated). The line
// editor is constructed ONLY on the interactive-TTY branch; the non-TTY (piped)
// path MUST stay byte-for-byte identical (§10.8 BLOCKING invariant). Arrow-key /
// history behaviour is TTY-only and NOT e2e-reachable (harness gap G-1) — the
// durable /qa guard is this non-TTY byte-identical golden. The agent consent-line
// read (§15.2 write gate) is agent-feature-gated and NOT reachable on the default
// build, so its non-TTY invariant is a named coverage gap, not authored here.
// =============================================================================

// spec: repl/spec.md §10.8 — a fixed piped-stdin session's stdout is captured as a
// golden (timing masked). rustyline is TTY-gated, so this non-TTY output MUST stay
// byte-identical after the 0544 change lands. Captured on S106 HEAD (pre-change
// baseline); the guard is that adding rustyline never perturbs a single byte of the
// non-TTY path. GREEN-expected (byte-identical pre/post).
#[test]
fn non_tty_repl_output_byte_identical_line_editor_off() {
    let out = repl_prims(
        "(add-i64 1 2)\n\
         (defn id [x] x)\n\
         /list\n\
         /sig id\n",
    );
    // Mask only the non-deterministic prompt timing (`N+Mms; <module>> `); every
    // other byte of the non-TTY session output MUST match the committed golden.
    let prompt_re = regex::Regex::new(r"\d+\+\d+ms; \w+> ").unwrap();
    out.assert_golden_masked("non_tty_repl_line_editor_off", &[&prompt_re]);
}

// =============================================================================
// Sprint 109 — 0573: deftype-shape × persistence matrix ("coverage by
// definition variants" made flesh). See the [historical QA allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md), S109 E.
// A SUM deftype persists to the backing `user.cl`; a PRODUCT deftype does NOT
// (silent data loss — the 0573 defect). Both are pinned here + a no-double-emit
// negative for the post-fix `type_def_info()`-keyed change.
// =============================================================================

// spec: repl/spec.md §15.2 — a SUM deftype is persisted to the backing `user.cl`.
#[test]
fn sum_deftype_persisted_to_backing_file() {
    let out = Cranelisp::new()
        .repl()
        .stdin("(deftype Shape (Circle [:primitives/Int r]) (Sq [:primitives/Int s]))\n/quit\n")
        .output();
    assert!(
        out.tmp_exists("user.cl") && out.read_tmp("user.cl").contains("deftype Shape"),
        "a sum deftype MUST persist to backing user.cl; got user.cl exists={}, \
         stdout={}",
        out.tmp_exists("user.cl"),
        out.stdout
    );
}

// spec: repl/spec.md §15.2 — a persisted SUM deftype's type + constructors
// survive a restart (reload from user.cl).
#[test]
fn sum_deftype_reload_retains_type_and_ctors() {
    let first = Cranelisp::new()
        .repl()
        .stdin("(deftype Shape (Circle [:primitives/Int r]) (Sq [:primitives/Int s]))\n/quit\n")
        .output();
    first
        .run_again()
        .repl()
        .stdin("(match (Circle 5) [(Circle r) r (Sq s) s])\n")
        .output()
        .assert_stdout_contains(":primitives/Int 5");
}

// spec: repl/spec.md §15.2 — a PRODUCT deftype MUST persist to the backing
// `user.cl`, exactly as a sum deftype does. RED today: the product type is not
// written (silent data loss).
// defect: class=enumeration-miss locus=src/session_v4/save.rs::generate_types (matches ModuleEntry::TypeDef only; product facet is Def{Constructor{type_def:Some}}) found=S108 owner=/dev
#[test]
fn product_deftype_persisted_to_backing_file() {
    let out = Cranelisp::new()
        .repl()
        .stdin("(deftype Point [:primitives/Int x :primitives/Int y])\n/quit\n")
        .output();
    assert!(
        out.tmp_exists("user.cl") && out.read_tmp("user.cl").contains("deftype Point"),
        "a product deftype MUST persist to backing user.cl (0573 — silent data \
         loss); got user.cl exists={}, stdout={}",
        out.tmp_exists("user.cl"),
        out.stdout
    );
}

// spec: repl/spec.md §15.2 — a persisted PRODUCT deftype's type + generated
// accessor survive a restart. RED today (the product is not persisted, so the
// reloaded session does not know `Point`).
// defect: class=enumeration-miss locus=src/session_v4/save.rs::generate_types found=S108 owner=/dev
#[test]
fn product_deftype_reload_retains_type_and_accessor() {
    let first = Cranelisp::new()
        .repl()
        .stdin("(deftype Point [:primitives/Int x :primitives/Int y])\n/quit\n")
        .output();
    first
        .run_again()
        .repl()
        .stdin("(Point.x (Point 3 4))\n")
        .output()
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: repl/spec.md §15.2 (NEG) — the post-fix `type_def_info()`-keyed emit MUST
// NOT emit a SUM deftype twice (sum ctor `Def`s carry `type_def: None`). Guard:
// the sum deftype appears exactly once in the backing file.
#[test]
fn sum_deftype_not_double_emitted_neg() {
    let out = Cranelisp::new()
        .repl()
        .stdin("(deftype Shape (Circle [:primitives/Int r]) (Sq [:primitives/Int s]))\n/quit\n")
        .output();
    let user_cl = if out.tmp_exists("user.cl") {
        out.read_tmp("user.cl")
    } else {
        String::new()
    };
    assert_eq!(
        user_cl.matches("deftype Shape").count(),
        1,
        "a sum deftype MUST be emitted ONCE, not doubled (0573 fix guard); \
         got user.cl:\n{user_cl}"
    );
}
