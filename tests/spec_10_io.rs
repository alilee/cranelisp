// spec_10_io.rs — IO surface (Sprint 64 Wave 3 Batch 4).
//
// Covers `spec/10-io.md`. Carries forward language-behaviour assertions
// from the legacy integration-tier `tests/io.rs`, `tests/io_minimal.rs`,
// `tests/sprint61_io_closure_regression.rs`. Per
// `tests/plan/PLAN.md §"Mode canonicalisation"`, default canonical mode is
// REPL — Pure / bind / IO trampoline observable behaviour is asserted via
// stdout substring against the REPL.
//
// Mode-specific exceptions (cited per-test):
//   - Tests asserting on `--run` IO sequencing (file output from
//     `(print ...)`, exit code from `(defn main [] (Pure N))`) use `--run`
//     because the IO sequencing semantics ARE what's under test.
//
// What this file covers:
//   - Pure constructor wraps Int/Bool/String (§10.2)
//   - bind primitive forms IO chains (§10.3)
//   - bind with identity continuation, with computation, polymorphic
//   - Internal Bind constructor / pattern rejection (§10.1 — Bind is internal,
//     not user-invocable per the runtime representation)
//   - IO type inference / propagation (§10.7)
//   - REPL eval unwraps Pure inline (§10.6.2 — REPL Mode entry point)
//   - --run mode: main returns IO, exit code from Pure / from bind chain (§10.6.1)
//   - Closure-capture inc regression (Sprint 61 Wave 4 — `emit_capture_return_inc`)
//   - bind! desugaring (§10.5 macro form)
//
// Quarantined to `tests/legacy/observability_io.rs`:
//   - cranelisp_runtime::io_trace::* internal-API trace event assertions
//   - Direct ring-buffer capacity inspection
//   - `cache .meta.json` JSON-file inspection for trace-event leakage

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// Helpers
// =============================================================================

/// Pipe `lines` to a fresh REPL with PrimitivesOnly prelude.
fn repl(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// =============================================================================
// Pure constructor — spec/10-io.md §10.2
// =============================================================================

// spec: spec/10-io.md §10.2 — Pure wraps Int; REPL trampolines inline
#[test]
fn pure_int_unwraps_inline() {
    repl("(Pure 42)\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/10-io.md §10.2.3 — Pure wraps Bool
#[test]
fn pure_bool_unwraps_inline() {
    repl("(Pure true)\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/10-io.md §10.2.3 — Pure wraps String
#[test]
fn pure_string_unwraps_inline() {
    repl("(Pure \"hello\")\n").assert_stdout_contains(":primitives/String");
}

// =============================================================================
// bind primitive — spec/10-io.md §10.3
// =============================================================================

// spec: spec/10-io.md §10.3.1 — bind chains Pure(42) into +1
#[test]
fn bind_pure_to_pure_plus_one() {
    repl("(bind (Pure 42) (fn [x] (Pure (add-i64 x 1))))\n")
        .assert_stdout_contains(":primitives/Int 43");
}

// spec: spec/10-io.md §10.3.1 — bind with identity continuation
#[test]
fn bind_identity_continuation() {
    repl("(bind (Pure 77) (fn [x] (Pure x)))\n")
        .assert_stdout_contains(":primitives/Int 77");
}

// spec: spec/10-io.md §10.3.3 — nested bind chains
#[test]
fn bind_nested_chain() {
    // (bind (bind (Pure 10) (fn [x] (Pure (+ x 20)))) (fn [y] (Pure (+ y 100))))
    repl("(bind (bind (Pure 10) (fn [x] (Pure (add-i64 x 20)))) (fn [y] (Pure (add-i64 y 100))))\n")
        .assert_stdout_contains(":primitives/Int 130");
}

// spec: spec/10-io.md §10.3 — triple bind chain
#[test]
fn bind_triple_chain() {
    repl("(bind (Pure 1) (fn [a] (bind (Pure 2) (fn [b] (bind (Pure 3) (fn [c] (Pure (add-i64 a (add-i64 b c)))))))))\n")
        .assert_stdout_contains(":primitives/Int 6");
}

// spec: spec/10-io.md §10.3 — bind with named defn as continuation
#[test]
fn bind_named_defn_continuation() {
    repl("(defn my-pure [x] (Pure x))
(bind (Pure 99) my-pure)
")
    .assert_stdout_contains(":primitives/Int 99");
}

// =============================================================================
// Internal Bind constructor / pattern rejection — spec/10-io.md §10.1 (Bind is internal, not user-invocable)
// =============================================================================

// spec: spec/10-io.md §10.1 (Bind is internal, not user-invocable) — Bind cannot be constructed directly
#[test]
fn bind_constructor_rejected() {
    let out = repl("(Bind (Pure 1) (fn [x] (Pure x)))\n");
    // The internal Bind constructor MUST NOT be invocable from user code.
    assert!(
        out.stdout.to_lowercase().contains("error") || out.stdout.contains("undefined"),
        "Bind constructor must NOT be user-invocable; got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.1 (Bind is internal, not user-invocable) — Bind cannot be matched
#[test]
fn bind_pattern_rejected() {
    let out = repl("(match (Pure 1) [(Bind a b) 0 _ 99])\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "Bind pattern must NOT be matchable; got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.2 (positive) — Pure CAN be matched (it's a public ctor)
#[test]
fn pure_pattern_accepted() {
    // Match on IO type must cover both Pure and Effect (Bind is private).
    repl("(match (Pure 5) [(Pure x) x (Effect e) 0])\n")
        .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// IO type inference — spec/10-io.md §10.7 (Effect Tracking)
// =============================================================================

// spec: spec/10-io.md §10.7.1 — defn returning Pure has type with IO marker (propagation)
#[test]
fn defn_returning_pure_displays_fn_type() {
    let out = repl("(defn pure-int [] (Pure 42))\n");
    // Display should show `(Fn [] ... Int)` — the IO wrapper unwraps to Int.
    assert!(
        out.stdout.contains("user/pure-int ; defn"),
        "defn returning Pure must show defn classification; got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.3 — bind result inferred as polymorphic
#[test]
fn bind_polymorphic_inference() {
    repl("(bind (Pure 99) (fn [x] (Pure x)))\n")
        .assert_stdout_contains(":primitives/Int 99");
}

// =============================================================================
// REPL eval inline trampoline — spec/10-io.md §10.6.2
// =============================================================================
//
// Sprint 57 Wave 6 + Sprint 61 Wave 4 fixes: REPL eval trampolines IO inline
// before returning, so `(Pure 42)` produces `:primitives/Int 42` at the REPL,
// not a raw IO heap pointer with type `(IO Int)`. The closure-capture-inc
// (§5.6 "Capture-return inc") fix landed in S61 Wave 4 prevents the
// double-free that surfaced as SIGBUS pre-fix.

// spec: spec/10-io.md §10.6.2 — Pure(42) evaluates to Int 42 at REPL (regression
// guard for Sprint 57 Wave 6 SIGBUS cluster).
#[test]
fn repl_pure_int_unwraps() {
    repl("(Pure 42)\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/10-io.md §10.6.2 — bind+Pure regression guard
// (Sprint 61 Wave 4 capture-return-inc: `emit_capture_return_inc` rule.)
#[test]
fn repl_bind_pure_lambda_no_double_free() {
    repl("(bind (Pure 42) (fn [x] (Pure x)))\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// --run mode: IO sequencing (mode-specific exception)
// =============================================================================
//
// Per `tests/plan/PLAN.md §"Mode canonicalisation"`, --run mode is the
// canonical home for "main returns Pure(N), exit code = N" semantics. The
// REPL form would observe Int N as well, but the spec says batch mode
// returns IO via the trampoline before exiting. These tests exercise that
// path explicitly.

// spec: spec/10-io.md §10.6.1 (Exit Code) — main returning Pure: exit code = inner Int
#[test]
fn run_mode_main_returns_pure_exit_code() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (Pure 42))")
        .output()
        .assert_exit(42);
}

// spec: spec/10-io.md §10.6.1 (Exit Code) — main returning Pure with non-zero exit code
#[test]
fn run_mode_main_returns_pure_nonzero() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (Pure 99))")
        .output()
        .assert_exit(99);
}

// spec: spec/10-io.md §10.6.1 (Exit Code) — main returning bind chain: exit code from final value
#[test]
fn run_mode_main_returns_bind_exit_code() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (bind (Pure 10) (fn [x] (Pure (add-i64 x 32)))))")
        .output()
        .assert_exit(42);
}

// spec: spec/10-io.md §10.6.1 (Exit Code) — a batch `main` returning `(IO Int)`
// exits with the inner Int. A bare-`Int` main is REJECTED (see
// `batch_main_pure_int_return_is_rejected`); the conformant shape wraps the
// exit code in `(Pure …)`, and the inner Int (7) is the process exit code.
#[test]
fn run_mode_main_returns_int_exit_code() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user("(defn main [] (Pure 7))")
        .output()
        .assert_exit(7);
}

// =============================================================================
// Entry-point return type enforcement — batch `main` MUST return `IO _`
// =============================================================================
//
// FAILING-FIRST forcing function (S79). The spec REQUIRES a batch-mode
// (`--run` / `--link`) `main` to return `IO _`:
//   - spec/02-grammar.md §2.1 "Batch Mode" (~line 25): main "returns a value
//     of type `IO _`".
//   - spec/10-io.md §10.6 "Entry Point" (~line 244–247): "The return type of
//     `main` MUST be `IO _`" → `main :: (Fn [] (IO _))`.
//   - spec/12-runtime.md §12.6 "Entry Point" (~line 173): same MUST; exit code
//     is the inner Int of the resulting `IO Int`.
// REPL mode is EXEMPT (spec/10-io.md §10.6.2 — no `main` requirement).
//
// The compiler currently accepts a bare-`Int` `main` as an unenforced
// leniency (e.g. `run_mode_main_returns_int_exit_code` above, and the
// `(defn main [] 42)` corpus in tests/link.rs + tests/build_confidence.rs).
// This test is RED today: a pure (non-`IO`) batch `main` is NOT yet rejected.
// It is the forcing function — the suite cannot go green until `main : IO _`
// is enforced. Un-ignored on purpose (memory/feedback_failing_not_ignored.md).
//
// spec: spec/10-io.md §10.6 (Entry Point) + spec/02-grammar.md §2.1 (Batch Mode)
// + spec/12-runtime.md §12.6 (Entry Point) — a batch `main` returning a bare
// `Int` (not `IO _`) MUST be rejected with a spec-grounded error.
#[test]
fn batch_main_pure_int_return_is_rejected() {
    // A pure (bare-`Int`) main: `(defn main [] 0)` has type `(Fn [] Int)`,
    // which violates `main :: (Fn [] (IO _))`. Both batch entry modes
    // (`--run` and `--link`) MUST refuse it.
    let pure_main = "(defn main [] 0)";

    // --- `--run` half ---
    let run_out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(pure_main)
        .output();
    assert!(
        !run_out.status.success(),
        "--run: a pure (bare-Int) main MUST be rejected — `main :: (Fn [] (IO _))` \
         (spec/10-io.md §10.6); compiler accepted it.\nstdout:\n{}\nstderr:\n{}",
        run_out.stdout, run_out.stderr
    );
    let run_combined = format!("{}{}", run_out.stdout, run_out.stderr);
    assert!(
        run_combined.contains("main") && run_combined.contains("IO"),
        "--run: rejection MUST name `main` and the `IO _` requirement \
         (spec/10-io.md §10.6, spec/12-runtime.md §12.6).\ncombined:\n{}",
        run_combined
    );

    // --- `--link` half ---
    let link_out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link("user.cl")
        .user(pure_main)
        .output();
    assert!(
        !link_out.status.success(),
        "--link: a pure (bare-Int) main MUST be rejected — `main :: (Fn [] (IO _))` \
         (spec/02-grammar.md §2.1, spec/10-io.md §10.6); compiler accepted it.\n\
         stdout:\n{}\nstderr:\n{}",
        link_out.stdout, link_out.stderr
    );
    let link_combined = format!("{}{}", link_out.stdout, link_out.stderr);
    assert!(
        link_combined.contains("main") && link_combined.contains("IO"),
        "--link: rejection MUST name `main` and the `IO _` requirement \
         (spec/10-io.md §10.6, spec/12-runtime.md §12.6).\ncombined:\n{}",
        link_combined
    );
}

// spec: spec/10-io.md §10.6 (Entry Point) + spec/02-grammar.md §2.1 (Batch Mode)
// + spec/12-runtime.md §12.6 (Entry Point) — a batch `main` returning a bare
// `Bool` (not `IO _`) MUST be rejected with the same `(Fn [] (IO _))`
// diagnostic as the bare-`Int` case.
//
// FAILING-FIRST (RED until the Wave-1 int enforcement lands — the
// `classify_main_return_type` one-arm deletion in `src/exe.rs`). This is the
// `Bool`-main rejection subject from the Phase-3 "Mains that STAY non-IO" list:
// `(defn main [] true)` has type `(Fn [] Bool)`, which violates
// `main :: (Fn [] (IO _))`. Today the compiler leniently accepts a non-IO main
// (e.g. `spec_12_runtime::main_returning_non_int_produces_zero_exit_code`
// certifies the `true` main exits 0). Once enforcement lands, BOTH batch entry
// modes MUST refuse it with the `(Fn [] (IO _))` error.
#[test]
fn batch_main_bool_return_is_rejected() {
    // A pure (bare-`Bool`) main: `(defn main [] true)` has type `(Fn [] Bool)`.
    let bool_main = "(defn main [] true)";

    // --- `--run` half ---
    let run_out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(bool_main)
        .output();
    assert!(
        !run_out.status.success(),
        "--run: a pure (bare-Bool) main MUST be rejected — `main :: (Fn [] (IO _))` \
         (spec/10-io.md §10.6); compiler accepted it.\nstdout:\n{}\nstderr:\n{}",
        run_out.stdout, run_out.stderr
    );
    let run_combined = format!("{}{}", run_out.stdout, run_out.stderr);
    assert!(
        run_combined.contains("main") && run_combined.contains("IO"),
        "--run: rejection MUST name `main` and the `IO _` requirement \
         (spec/10-io.md §10.6, spec/12-runtime.md §12.6).\ncombined:\n{}",
        run_combined
    );

    // --- `--link` half ---
    let link_out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link("user.cl")
        .user(bool_main)
        .output();
    assert!(
        !link_out.status.success(),
        "--link: a pure (bare-Bool) main MUST be rejected — `main :: (Fn [] (IO _))` \
         (spec/02-grammar.md §2.1, spec/10-io.md §10.6); compiler accepted it.\n\
         stdout:\n{}\nstderr:\n{}",
        link_out.stdout, link_out.stderr
    );
    let link_combined = format!("{}{}", link_out.stdout, link_out.stderr);
    assert!(
        link_combined.contains("main") && link_combined.contains("IO"),
        "--link: rejection MUST name `main` and the `IO _` requirement \
         (spec/10-io.md §10.6, spec/12-runtime.md §12.6).\ncombined:\n{}",
        link_combined
    );
}

// =============================================================================
// IO branch consistency — spec/10-io.md §10.7.2
// =============================================================================

// spec: spec/10-io.md §10.7.2 — both branches IO (branch consistency)
#[test]
fn if_both_branches_io() {
    repl("(if (eq-i64 1 1) (Pure 10) (Pure 20))\n")
        .assert_stdout_contains(":primitives/Int 10");
}

// spec: spec/10-io.md §10.7.2 — branch consistency (mixed Pure / non-Pure errors)
#[test]
fn if_branch_consistency_neg_mixed() {
    let out = repl("(if (eq-i64 1 1) (Pure 10) 20)\n");
    // Mixing Pure(Int) with bare Int in branches is a type error.
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "mixing Pure(Int) with Int in if branches must error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// match on IO values — spec/10-io.md §10.7.2 + spec/06-pattern-matching.md §6.1
// =============================================================================

// spec: spec/10-io.md §10.7.2 — match arms all IO (branch consistency)
#[test]
fn match_arms_all_io_pure() {
    repl("(match (Pure 1) [(Pure x) (Pure (add-i64 x 100)) (Effect e) (Pure 0)])\n")
        .assert_stdout_contains(":primitives/Int 101");
}

// =============================================================================
// IO let-binding — spec/10-io.md §10.7.1 (effect propagation)
// =============================================================================

// spec: spec/10-io.md §10.7.1 — let with IO body inherits IO type (effect propagation)
#[test]
fn let_io_body() {
    repl("(let [x 5] (Pure x))\n").assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// Closure-capture-inc regression guard — Sprint 61 Wave 4 (FIXME 0030 surface)
// =============================================================================
//
// Per `design/backend/ring2-rc.md §5.6 Capture-return inc`. The bug pre-fix:
// a lambda body whose return value was a captured heap reference would be
// dec'd by the closure drop-glue *after* the return, causing a double-free.
// Fix: `emit_capture_return_inc` in
// `crates/cranelisp-backend/src/compiler/control_flow.rs` increments the
// captured value before return, balancing the subsequent dec.

// spec: design/backend/ring2-rc.md §5.6 — capture-return inc regression guard
// (carry-forward from `tests/sprint61_io_closure_regression.rs`).
#[test]
fn capture_return_inc_does_not_double_free() {
    // The 7-line minimum repro from the Sprint 61 investigation:
    // a string captured by a lambda, returned via the lambda, no double-free.
    repl(r#"(defn make-bind [s] (bind (Pure s) (fn [x] (Pure x))))
(make-bind "hello")
"#)
    .assert_stdout_contains(":primitives/String");
}

// =============================================================================
// bind! macro desugaring — spec/10-io.md §10.5 (Monadic Bind Sugar)
// =============================================================================
//
// `bind!` and `do` are stdlib macros (`stdlib/io.monad`). Tests MUST NOT
// depend on stdlib (root CLAUDE.md §"Design Principles" — Stdlib separation),
// so the `bind!` / `do` desugaring assertions live in `tests/spec_11_stdlib.rs`
// (the named exception that uses the workspace stdlib). This file covers
// the underlying primitive `bind` shape that `bind!` desugars to.

// =============================================================================
// IO Effect isolation — spec/10-io.md §10.8.3 (Effect Isolation)
// =============================================================================

// spec: spec/10-io.md §10.8 — IO values are deferred data (not eager)
#[test]
fn io_values_deferred() {
    // Defining a fn that returns Pure does not run any side effects.
    repl("(defn deferred [] (Pure 99))
(deferred)
")
    .assert_stdout_contains(":primitives/Int 99");
}

// =============================================================================
// IO + auto-curry — spec/04-expressions.md §4.7 (Multi-Signature Dispatch)
// =============================================================================

// spec: spec/04-expressions.md §4.7 — partial application (auto-curry) of IO-returning fn
#[test]
fn auto_curry_io_returning_fn() {
    let out = repl("(defn add-pure [x y] (Pure (add-i64 x y)))
(add-pure 5)
");
    // Partial application returns a closure with Fn type — not an error.
    assert!(
        out.stdout.contains("Fn"),
        "auto-curry of IO-returning fn must return a closure; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// IO type errors — spec/10-io.md §10.3 (bind shape) + §10.1.2 (Purity Guarantee)
// (harvest: legacy/io.rs::io_neg_* — bind arg/continuation typing + purity)
// =============================================================================

// spec: spec/10-io.md §10.3 — bind's first argument MUST be `(IO a)`; a bare
// Int is a type error.
#[test]
fn bind_first_arg_must_be_io_neg() {
    let out = repl("(bind 42 (fn [x] (Pure x)))\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "bind with non-IO first arg MUST be a type error; got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.3 — bind's second argument MUST be a function
// `(Fn [a] (IO b))`; a bare Int is a type error.
#[test]
fn bind_second_arg_must_be_function_neg() {
    let out = repl("(bind (Pure 42) 99)\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "bind with non-function second arg MUST be a type error; got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.3 — bind's continuation MUST return `(IO b)`; a
// continuation returning a bare value (here `x`, an Int) is a type error.
#[test]
fn bind_continuation_must_return_io_neg() {
    let out = repl("(bind (Pure 42) (fn [x] x))\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "bind continuation returning non-IO MUST be a type error; got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.1 — IO is parametric: `IO Int` and `IO Bool` do not
// unify, so an `if` with one Pure-Int branch and one Pure-Bool branch errors.
#[test]
fn io_int_vs_io_bool_mismatch_neg() {
    let out = repl("(if (eq-i64 1 1) (Pure 1) (Pure true))\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "IO Int vs IO Bool branches MUST be a type error; got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.7.2 — match arm consistency: mixing an `(IO Int)` arm
// with a bare-`Int` arm is a type error (all arms must share the IO shape).
#[test]
fn match_arms_mixed_io_and_bare_neg() {
    let out = repl(
        "(deftype Color Red Green Blue)\n\
         (match Red [Red (Pure 1) Green 2 Blue (Pure 3)])\n",
    );
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "match arms mixing (IO Int) and bare Int MUST be a type error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// then-combinator / discard-pattern RC — spec/10-io.md §10.3 + §10.8.1
// (harvest: legacy/io.rs::io_then_combinator_* + io_bind_unused_heap_param)
//
// `(bind a (fn [_] b))` is the `then` combinator: the first action's result
// is discarded. The discarded value's RC must be balanced (dec'd) so a heap
// value is not leaked or double-freed. These run through the REPL and assert
// the final value survives — an RC mis-count would crash or corrupt the result.
// =============================================================================

// spec: spec/10-io.md §10.3 — discard a NeverHeap Int result, keep the next.
#[test]
fn then_discard_int_result() {
    repl("(bind (Pure 999) (fn [_] (Pure 42)))\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/10-io.md §10.3 — discard an AlwaysHeap String result, keep an Int.
// Regression guard: the `_` parameter must be dec'd to avoid leaking the String.
#[test]
fn then_discard_string_result() {
    repl(r#"(bind (Pure "discarded") (fn [_] (Pure 42)))
"#)
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/10-io.md §10.3 — discard a Mixed-heap ADT result, keep an Int.
#[test]
fn then_discard_adt_result() {
    repl(
        "(deftype (Option a) None (Some [:a val]))\n\
         (bind (Pure (Some 99)) (fn [_] (Pure 42)))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/10-io.md §10.3 — two discards chained: both heap results dec'd.
#[test]
fn then_chained_discards() {
    repl(r#"(bind (Pure "first") (fn [_] (bind (Pure "second") (fn [_] (Pure 0)))))
"#)
    .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/10-io.md §10.3 — a named (non-`_`) parameter that is unused must
// still be dec'd, same RC obligation as the `_` discard.
#[test]
fn then_unused_named_heap_param() {
    repl(r#"(bind (Pure "unused") (fn [x] (Pure 77)))
"#)
    .assert_stdout_contains(":primitives/Int 77");
}

// =============================================================================
// IO wrapping ADT values — spec/10-io.md §10.2.3 (Examples)
// (harvest: legacy/io.rs::io_pure_option_none / io_pure_option_some)
// =============================================================================

// spec: spec/10-io.md §10.2.3 — Pure wraps an Option None; eval unwraps the IO
// inline and the Option ADT is the displayed value.
#[test]
fn pure_wraps_option_none() {
    repl(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn mk [] (Pure None))\n\
         (mk)\n",
    )
    .assert_stdout_contains("Option");
}

// spec: spec/10-io.md §10.2.3 — Pure wraps an Option (Some 42).
#[test]
fn pure_wraps_option_some() {
    repl(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn mk [] (Pure (Some 42)))\n\
         (mk)\n",
    )
    .assert_stdout_contains("Some");
}

// =============================================================================
// pure as an ordinary value (higher-order) — spec/10-io.md §10.2.2 (Purpose)
// (harvest: legacy/io.rs::io_pure_as_higher_order)
// =============================================================================

// spec: spec/10-io.md §10.2 — a user `pure` (defn wrapping Pure) is an ordinary
// function: it can be passed as a higher-order argument and applied.
#[test]
fn pure_as_higher_order_function() {
    repl(
        "(defn my-pure [x] (Pure x))\n\
         (defn apply-to-42 [f] (f 42))\n\
         (apply-to-42 my-pure)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// Deep bind chain + batch exit code — spec/10-io.md §10.8.2 (Trampoline) + §10.6.1
// (harvest: legacy/io.rs::io_trampoline_deep_bind_chain + io_batch_exit_code_from_bind)
// =============================================================================

// spec: spec/10-io.md §10.8.2 — the trampoline interprets a deeply-nested bind
// chain iteratively (O(1) stack). A named-defn continuation threaded through 9
// binds returns the accumulated count via the process exit code under `--run`.
#[test]
fn run_mode_deep_bind_chain_named_continuation() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn add-one [x] (Pure (add-i64 x 1)))\n\
             (defn main []\n\
               (bind (Pure 0)\n\
                 (fn [a] (bind (add-one a)\n\
                 (fn [b] (bind (add-one b)\n\
                 (fn [c] (bind (add-one c)\n\
                 (fn [d] (bind (add-one d)\n\
                 (fn [e] (bind (add-one e)\n\
                 (fn [f] (bind (add-one f)\n\
                 (fn [g] (bind (add-one g)\n\
                 (fn [h] (bind (add-one h)\n\
                 (fn [i] (Pure i))))))))))))))))))))",
        )
        .output()
        // 0, then add-one applied 8 times = 8.
        .assert_exit(8);
}

// =============================================================================
// FIXME 0103 — IoObserver in cranelisp-intrinsics; trace.rs/io_trace.rs in int
// =============================================================================
//
// Authored failing-not-ignored at Sprint 66 Phase-5 Stage-1 open per /qa
// Phase-5 obligation. Pinning the canonical trace dump shape catches silent
// reshape during the FIXME-0103 + FIXME-0150 Phase-2 migration where:
//   - IoObserver registration moves from `cranelisp-runtime` to
//     `cranelisp-intrinsics` (per /arch Phase-2 revision #3).
//   - trace.rs + io_trace.rs ring-buffer + flush guard move from runtime
//     into `src/io_trace/`.
//
// Per `tests/plan/implementation-slice-s66.md §5.4`. The snapshot fixture
// `tests/fixtures/io_trace_snapshot.txt` pins event presence (not line
// ordering — line ordering may shift slightly across the relocation). The
// second test verifies the public-API home of `register_io_observer` is
// `cranelisp-intrinsics`, not `cranelisp-runtime`, post-relocation.
//
// Off-path (`CRANELISP_IO_TRACE` unset) overhead — design
// `design/backend/archive/io-trampoline-trace.md` §9 AC 2's "< 1%" bound — is
// NOT asserted here. The former S61 placeholder `..._subprocess_completes_
// within_generous_ceiling` (a 5-second subprocess wall-clock ceiling) proved a
// weak structural property only; it did not survive the port to this file. Per
// FIXME 0021 (user-ratified S81 W-H) the authoritative off-path measure is the
// in-process criterion microbench `benches/io_trace_off_path.rs`
// (`cargo bench --features bench --bench io_trace_off_path`), which measures the
// filter-OFF `record_event` per-call cost at nanosecond resolution: a fixed
// ~0.29 ns guard (one relaxed OnceLock load + null-check + branch). A
// subprocess / suite-wall-clock test cannot reach that resolution (process-spawn
// + I/O jitter swamps the signal), so no integration-tier ceiling is added — the
// criterion bench is the single authoritative AC-2 measurement.

// spec: spec/10-io.md §"IO observation contract" + spec/12-runtime.md
// §"Diagnostic logging".
// FIXME(/dev intrinsics FIXME 0103 Phase 1 + /dev int FIXME 0103 Phase 2)
// — fails until the relocated machinery emits trace lines whose shape
// matches the snapshot fixture (event tags present at minimum).
#[test]
fn io_trace_snapshot_pre_post_relocation_byte_equivalent() {
    // The program MUST dispatch a real platform effect for `PlatformEffect`
    // to fire (a pure value returns without any effect dispatch). `main`
    // calls `print` from the stdio platform — an effectful IO action that
    // routes through the IO trampoline and the platform-effect dispatch path.
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .use_workspace_platforms()
        .run("user.cl")
        .user(
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"io-trace probe\"))\n",
        )
        .env("CRANELISP_IO_TRACE", "1")
        .output();

    // Read the snapshot fixture — list of event tags that MUST appear.
    let fixture = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/io_trace_snapshot.txt"
    ))
    .expect("read tests/fixtures/io_trace_snapshot.txt");

    // Each non-empty, non-comment line is a required substring in stderr.
    let mut missing: Vec<&str> = Vec::new();
    for line in fixture.lines() {
        let needle = line.trim();
        if needle.is_empty() || needle.starts_with('#') {
            continue;
        }
        if !out.stderr.contains(needle) {
            missing.push(needle);
        }
    }
    assert!(
        missing.is_empty(),
        "io_trace snapshot drift — these required substrings are MISSING from stderr:\n  {}\n\
         full stderr was:\n{}",
        missing.join("\n  "),
        out.stderr
    );
}

// spec: structural — IoObserver registration site post-FIXME-0103 is in
// `cranelisp-intrinsics`, NOT `cranelisp-runtime` (per /arch Phase-2
// revision #3). Verifiable through `cargo public-api` baselines: a) the
// intrinsics baseline must list `register_io_observer`; b) the runtime
// baseline (transit) must NOT list it (after the relocation).
//
// FIXME(/dev intrinsics FIXME 0103 Phase 1 + /dev runtime retire under
// FIXME 0150 Phase 5).
#[test]
fn io_observer_registration_lives_in_intrinsics() {
    use std::path::PathBuf;
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let intrinsics_baseline = root.join("crates/cranelisp-intrinsics/public-api.txt");
    let runtime_baseline = root.join("crates/cranelisp-runtime/public-api.txt");

    let intrinsics_present = intrinsics_baseline.exists();
    assert!(
        intrinsics_present,
        "FIXME 0103: cranelisp-intrinsics crate / baseline must exist post-Wave-2 \
         (D43 Phase 1+2). Path: {}",
        intrinsics_baseline.display()
    );

    let intrinsics_pub = std::fs::read_to_string(&intrinsics_baseline)
        .unwrap_or_else(|e| panic!("read {}: {e}", intrinsics_baseline.display()));
    assert!(
        intrinsics_pub.contains("register_io_observer"),
        "cranelisp-intrinsics MUST expose `register_io_observer` per FIXME 0103 + /arch Phase-2 revision #3; \
         baseline at {}:\n{}",
        intrinsics_baseline.display(),
        intrinsics_pub
    );

    if runtime_baseline.exists() {
        let runtime_pub = std::fs::read_to_string(&runtime_baseline)
            .unwrap_or_else(|e| panic!("read {}: {e}", runtime_baseline.display()));
        assert!(
            !runtime_pub.contains("register_io_observer"),
            "cranelisp-runtime MUST NOT expose `register_io_observer` post-relocation \
             per FIXME 0103; baseline at {}:\n{}",
            runtime_baseline.display(),
            runtime_pub
        );
    }
}
