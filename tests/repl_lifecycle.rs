// repl_lifecycle.rs — REPL session lifecycle (Sprint 64 Wave 3 Batch 7 sub-batch 2).
//
// Carries forward the session-mechanism assertions from the integration-tier
// `repl_experience.rs` (lifecycle slice), `ring3_repl.rs` (macro persistence),
// `v4_repl_eval.rs` (eval-cycle persistence + error recovery). Per
// `tests/plan/PLAN.md §"Mode canonicalisation"`, canonical mode is REPL.
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
fn repl(lines: &str) -> helpers::e2e::CrOutput { Cranelisp::repl_capture(lines) }
fn repl_prims(lines: &str) -> helpers::e2e::CrOutput { Cranelisp::repl_prims_capture(lines) }

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
    repl_prims("(defn square [x] (mul-i64 x x))\n")
        .assert_stdout_contains("user/square ; defn");
}

// =============================================================================
// Definition persistence — repl/spec.md §15.2 (Session Restore) + §1.3
// =============================================================================

// spec: repl/spec.md §15.2 — defns persist across eval rounds in a session
#[test]
fn defn_then_call_in_next_form() {
    repl_prims("(defn double [x] (mul-i64 x 2))
(double 21)
")
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: repl/spec.md §15.2 — multiple defns coexist across eval rounds
#[test]
fn multiple_defns_coexist() {
    repl_prims("(defn one [] 1)
(defn two [] 2)
(add-i64 (one) (two))
")
    .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/05-definitions.md §5.1 — self-recursive defn at REPL (factorial)
#[test]
fn recursive_factorial() {
    repl_prims("(defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
(fact 5)
")
    .assert_stdout_contains(":primitives/Int 120");
}

// spec: spec/05-definitions.md §5.1 — self-recursive defn at REPL (fibonacci)
#[test]
fn recursive_fibonacci() {
    repl_prims("(defn fib [n] (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))
(fib 7)
")
    .assert_stdout_contains(":primitives/Int 13");
}

// =============================================================================
// ADT lifecycle — spec/05-definitions.md §5.2 + spec/06-pattern-matching.md §6.1
// =============================================================================

// spec: spec/05-definitions.md §5.2 — define ADT, then match in next form
#[test]
fn deftype_then_match() {
    repl_prims("(deftype Color Red Green Blue)
(defn pick [c] (match c [Red 1 Green 2 Blue 3]))
(pick Green)
")
    .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/05-definitions.md §5.2 — multiple ADTs coexist in REPL session
#[test]
fn multiple_adts_coexist() {
    repl_prims("(deftype Color Red Green Blue)
(deftype Size Small Medium Large)
(defn size-rank [s] (match s [Small 1 Medium 2 Large 3]))
(size-rank Medium)
")
    .assert_stdout_contains(":primitives/Int 2");
}

// =============================================================================
// Redefinition — repl/spec.md §15.6
// =============================================================================

// spec: repl/spec.md §15.6 — redefinition replaces previous defn
#[test]
fn redefinition_replaces_value() {
    repl_prims("(defn foo [] 1)
(defn foo [] 2)
(foo)
")
    .assert_stdout_contains(":primitives/Int 2");
}

// spec: repl/spec.md §15.6 — redefinition with different body shape
#[test]
fn redefinition_different_body() {
    repl_prims("(defn calc [x] (add-i64 x 1))
(defn calc [x] (mul-i64 x 2))
(calc 5)
")
    .assert_stdout_contains(":primitives/Int 10");
}

// spec: repl/spec.md §15.6 — redefinition propagates through caller chain
#[test]
fn redefinition_propagates_through_callers() {
    // First call: 10*2=20; after redef inner→5: 5*2=10. Both must appear.
    repl_prims("(defn inner [] 10)
(defn outer [] (mul-i64 (inner) 2))
(outer)
(defn inner [] 5)
(outer)
")
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
    repl_prims("(defn add1 [x] (add-i64 x 1))
(defn double [x] (mul-i64 x 2))
(defn pipeline [x] (double (add1 x)))
(pipeline 5)
(defn add1 [x] (add-i64 x 10))
(pipeline 5)
")
    .assert_stdout_contains_all(&[":primitives/Int 12", ":primitives/Int 30"]);
}

// =============================================================================
// Error recovery — repl/spec.md §5.2
// =============================================================================

// spec: repl/spec.md §5.2 — type error does not corrupt prior definitions
#[test]
fn type_error_preserves_prior_defs() {
    let out = repl_prims("(defn good [] 42)
(add-i64 1 \"oops\")
(good)
");
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
    let out = repl_prims("(defn good [] 99)
)bad
(good)
");
    assert!(
        out.stdout.contains(":primitives/Int 99"),
        "after parse error, good() must still return 99; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.2 — multiple consecutive errors then success
#[test]
fn multiple_errors_then_success() {
    let out = repl_prims("(undefined-symbol)
(another-undefined)
(add-i64 1 2)
");
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
    repl_prims("(defn broken [x] (add-i64 x \"nope\"))
broken
")
    .assert_stdout_does_not_contain("user/broken ; defn");
}

// spec: repl/spec.md §5.2 — failed redefn preserves original
#[test]
fn failed_redefn_preserves_original() {
    let out = repl_prims("(defn good [x] (add-i64 x 1))
(defn good [x] (add-i64 x \"nope\"))
(good 5)
");
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
    repl_prims("(defmacro double [x] `(mul-i64 ~x 2))
(double 21)
")
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/09-macros.md §9.2 — multi-clause defmacro dispatch (REPL persistence)
#[test]
fn multi_clause_defmacro_dispatches() {
    // 1-arg clause returns x → :Int 1; 2-arg clause returns y → :Int 2.
    repl_prims("(defmacro pick ([x] x) ([x y] y))
(pick 1)
(pick 1 2)
")
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
    repl_prims("(defn pair-add [a b] (add-i64 a b))
(defn triple-add [a b c] (pair-add a (pair-add b c)))
(triple-add 1 2 3)
")
    .assert_stdout_contains(":primitives/Int 6");
}

// spec: repl/spec.md §15.2 — interleaved defns and bare expressions
#[test]
fn interleaved_defns_and_exprs() {
    repl_prims("(defn x [] 5)
(x)
(defn y [] 10)
(add-i64 (x) (y))
")
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
// Wave 5.6 file 6 e2e.rs chunk-1 GAP-COVER carry-forwards
// (per tests/plan/wave-5.6-e2e-reaudit.md).
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
    let out = repl_prims("(add-i64
  2 3)
");
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
