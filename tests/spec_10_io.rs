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

// spec: spec/10-io.md §10.1.1 — Type System Integration: IO propagates upward
// through the call graph automatically via HM inference, with no special rules.
// A fn that produces an IO value (here `(Pure 5)`) has `IO` in its inferred
// return type WITHOUT any annotation. The REPL display shows
// `(Fn [] (primitives/IO primitives/Int))` — the IO marker is present, proving
// propagation is type-inferred, not annotated.
#[test]
fn io_propagates_into_inferred_return_type() {
    let out = repl("(defn mk [] (Pure 5))\nmk\n");
    assert!(
        out.stdout.contains("(Fn [] (primitives/IO primitives/Int))"),
        "a fn producing an IO value MUST inherit `IO` in its inferred return \
         type with no annotation (spec/10-io.md §10.1.1 propagation); got:\n{}",
        out.stdout
    );
}

// spec: spec/10-io.md §10.1.2 — Purity Guarantee: a function whose type does
// NOT contain `IO` cannot have performed side effects — enforced by the type
// system. Using an `IO`-typed value where a pure value is expected MUST produce
// a type mismatch. Here `(mk)` has type `(IO Int)`; passing it to `add-i64`
// (which expects `Int`) MUST be rejected as a type error naming the IO type.
// This is the negative enforcing the purity boundary.
#[test]
fn io_value_in_pure_position_is_type_error_neg() {
    let out = repl("(defn mk [] (Pure 5))\n(add-i64 1 (mk))\n");
    assert!(
        out.stdout.contains("type error") || out.stdout.contains("type mismatch"),
        "using an IO-typed value where a pure value is expected MUST be a type \
         error (spec/10-io.md §10.1.2 purity guarantee); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("IO"),
        "the purity-violation type error MUST name the offending `IO` type; \
         got:\n{}",
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
    // Reuse the prelude-seeded `primitives/Option` (§8.6.4: a local Option
    // deftype under the Option-providing prelude is a define-over-prelude
    // collision). Discarding a Mixed-heap ADT result is unaffected.
    repl(
        "(bind (Pure (Some 99)) (fn [_] (Pure 42)))\n",
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
    // Reuse the prelude-seeded `primitives/Option` (see §8.6.4 note above).
    repl(
        "(defn mk [] (Pure None))\n\
         (mk)\n",
    )
    .assert_stdout_contains("Option");
}

// spec: spec/10-io.md §10.2.3 — Pure wraps an Option (Some 42).
#[test]
fn pure_wraps_option_some() {
    // Reuse the prelude-seeded `primitives/Option` (see §8.6.4 note above).
    repl(
        "(defn mk [] (Pure (Some 42)))\n\
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

// =============================================================================
// §10.12.4 — Runtime Resource Tokens: ResourceSerial token serialization
// (FIXME 0353 — the end-to-end witness the two legacy GAP stubs always owed:
//  `test_io_schedule_resource_serial_same_token_sequential` /
//  `..._diff_token_parallel`, harvested from `tests/legacy/lenient.rs` at S82
//  close. The `cranelisp-test-capture` `resource-serial-sleep-ms (token, ms)`
//  fixture — `SchedulingClass::ResourceSerial`, places `token` on the Effect
//  node via `CLIO::effect_on_resource`, sleeps `ms` — landed first half.)
//
// Spec §10.12.4: within a `Par` group the trampoline groups Effect nodes by
// resource token; branches with the SAME non-zero token are serialised
// regardless of data independence; branches with DIFFERENT tokens run
// concurrently. This is observable by timing two data-independent ResourceSerial
// calls (each sleeping `D` ms) in one program:
//   - same token  -> serialised -> wall-clock ~= 2*D (> 1.5*D)
//   - diff tokens -> concurrent -> wall-clock ~= 1*D (< 1.5*D)
//
// Both programs are TWO data-independent bindings in a `bind` chain (`a` not
// free in the second effect, `b` not free in the first) so the independence
// analysis can Par-group them (spec §10.12.1; ResourceSerial groups identically
// to the Commutative pair whose Par emission is pinned by
// `control_flow.rs::par_codegen_tests`). The terminal `Pure (add-i64 a b)`
// makes `main : IO Int`, and the summed sleep durations become the exit code
// (§10.6.1) — `2*200 = 400 -> 400 mod 256 = 144` (Unix exit byte).
//
// TIMING DISCIPLINE (robust margins, NOT tight ratios — timing-flakiness is
// banned as a disposition): D = 200 ms per call so OS jitter is swamped, and the
// structural inequality is asserted at the 1.5*D midpoint (300 ms), giving 50%
// slack each side. Measured around the program run only:
//   - `--run`: `out.elapsed` is compile(~21ms) + program — clean separation
//     against the 300 ms midpoint (serial ~= 421 ms; parallel ~= 221 ms).
//   - `--link`: the link COMPILE (~225 ms) must NOT be timed. We link with
//     `.link()` (produce only), then exec the produced standalone binary
//     ourselves and time THAT (binary startup ~= 5 ms; serial ~= 409 ms;
//     parallel ~= 205 ms). `link_then_run` folds link+run into one `elapsed`
//     and is therefore unusable for timing.
//
// KNOWN-DEFECT GUARD (failing-not-ignored): as of S83, automatic IO scheduling
// (spec §10.12) is NOT wired into the live source->AST pipeline — the int-side
// `apply_bind_chain_analysis` / `auto_schedule_defn` pass that inserts
// `Expr::ParBind` from `bind` chains is dead code (`#[allow(dead_code)]`, zero
// live callers), so NO `Par` node is ever emitted and BOTH same- and diff-token
// chains run sequentially (~2*D). The backend can codegen + dispatch `Par`
// nodes (`par_codegen_tests`, `dispatch_par_branches`) but nothing constructs
// them from user source. The `..._diff_token_parallelizes` assertion therefore
// FAILS today (diff-token measures ~2*D, not <1.5*D) — it is the spec-correct
// regression guard that flips green when scheduling is wired in. See FIXME
// 0367-int-resource-serial-scheduling-not-wired (target: /int; the
// runtime-dispatch remainder of FIXME 0353, surfaced by this witness). The
// `..._same_token_serializes` companion passes in both states (sequential
// satisfies "> 1.5*D"); it is the positive serialization witness.

/// Per-call sleep duration. >=100 ms swamps OS jitter; 200 ms gives a wide
/// margin against the 1.5x midpoint in both directions.
const RS_SLEEP_MS: u64 = 200;

/// Best-of-N attempts for a POSITIVE wall-clock parallelism witness.
///
/// A "parallelism makes this faster" assertion (`run_ms < RS_MIDPOINT_MS`) is
/// fragile under a saturated full-workspace `cargo nextest run` (16 processes):
/// when the parallel sparks are starved of cores the wall-clock balloons past
/// the midpoint even though the scheduling is correct. CPU contention can only
/// ever make a measurement SLOWER than the true parallel wall-clock, never
/// faster, so taking the MINIMUM over N attempts filters contention noise and
/// reflects the genuine parallelization capability. The threshold is unchanged
/// — if parallelism is actually broken, ALL N runs measure ~2*D (~400 ms) and
/// the assertion still fails.
///
/// Only POSITIVE (`< RS_MIDPOINT_MS`) witnesses use this. NEGATIVE / serial
/// guards (`> RS_MIDPOINT_MS`) stay single-shot: contention only makes those
/// MORE serial, so they are already robust, and `min` could weaken them.
///
/// Hardened S86 (the S85 map-reduce best-of-N precedent applied to the auto-IO
/// timing witnesses; see tests/plan/ledger.md S86 entry).
const RS_BEST_OF_N: usize = 5;

/// Run `attempt` `RS_BEST_OF_N` times and return the minimum elapsed-ms.
fn best_of_n_ms(mut attempt: impl FnMut() -> u128) -> u128 {
    (0..RS_BEST_OF_N)
        .map(|_| attempt())
        .min()
        .expect("RS_BEST_OF_N >= 1")
}

/// Structural inequality boundary: 1.5 x single-call duration.
const RS_MIDPOINT_MS: u128 = (RS_SLEEP_MS as u128 * 3) / 2; // 300 ms

/// Source for a two-binding ResourceSerial `bind` chain. `(t1, t2)` are the
/// resource tokens on the two data-independent 200 ms calls.
fn rs_program(t1: i64, t2: i64) -> String {
    format!(
        "(platform test-capture)\n\
         (import [platform.test-capture [resource-serial-sleep-ms]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main []\n\
           (bind (resource-serial-sleep-ms {t1} {RS_SLEEP_MS}) (fn [a]\n\
             (bind (resource-serial-sleep-ms {t2} {RS_SLEEP_MS}) (fn [b]\n\
               (Pure (primitives/add-i64 a b)))))))\n"
    )
}

/// Wall-clock the program under `--run` (compile + JIT-run; compile overhead is
/// ~21 ms, negligible against the 300 ms midpoint). Asserts the value-bearing
/// exit code so a silent mis-run can't masquerade as a timing pass.
fn rs_run_elapsed_ms(t1: i64, t2: i64) -> u128 {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", &rs_program(t1, t2))
        .run("main.cl")
        .output();
    // 2*200 = 400 -> 400 mod 256 = 144 (Unix exit byte). Proves both effects ran.
    let code = out.status.code();
    assert_eq!(
        code,
        Some(144),
        "--run: expected exit 144 (both 200ms sleeps ran, summed=400 mod 256)\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    out.elapsed.as_millis()
}

/// Wall-clock the program under `--link`: link (produce the binary, NOT timed),
/// then exec the produced standalone binary and time only that run. The produced
/// binary resolves the test-capture platform DLL at runtime via dlopen, so it
/// needs `CRANELISP_PLATFORM_PATH` in its env.
fn rs_link_elapsed_ms(t1: i64, t2: i64) -> u128 {
    use std::process::Command;
    use std::time::Instant;

    let platform_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug");

    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", &rs_program(t1, t2))
        .link("main.cl")
        .output();
    assert!(
        out.status.success(),
        "--link: link step failed\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );

    // The linker emits the produced binary as `<stem>` next to the source.
    let produced = out.tmpdir.join("main");
    assert!(
        produced.exists(),
        "--link: produced binary missing at {}\nstdout:\n{}\nstderr:\n{}",
        produced.display(),
        out.stdout,
        out.stderr
    );

    let start = Instant::now();
    let run = Command::new(&produced)
        .current_dir(&out.tmpdir)
        .env("CRANELISP_PLATFORM_PATH", &platform_path)
        .output()
        .expect("exec produced --link binary");
    let elapsed = start.elapsed();

    assert_eq!(
        run.status.code(),
        Some(144),
        "--link produced binary: expected exit 144 (both 200ms sleeps ran)\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    elapsed.as_millis()
}

// spec: spec/10-io.md §10.12.4 — two data-independent ResourceSerial calls with
// the SAME non-zero resource token are SERIALISED (run one after the other)
// regardless of data independence. Wall-clock witness: each call sleeps 200 ms,
// so the serialised total exceeds the 1.5x midpoint (300 ms). Positive
// serialization witness — passes whether or not Par-grouping is wired (a
// sequential run also exceeds 1.5x a single call). Asserted in BOTH `--run`
// (JIT trampoline) and `--link` (static-relocation trampoline) — serialization
// is mode-independent.
#[test]
fn resource_serial_same_token_serializes() {
    // Same token = 1 on both calls.
    let run_ms = rs_run_elapsed_ms(1, 1);
    assert!(
        run_ms > RS_MIDPOINT_MS,
        "--run same-token: expected serialised wall-clock > {RS_MIDPOINT_MS}ms \
         (~= 2*{RS_SLEEP_MS}ms), got {run_ms}ms — the two same-token \
         ResourceSerial calls did not serialise (spec §10.12.4)"
    );

    let link_ms = rs_link_elapsed_ms(1, 1);
    assert!(
        link_ms > RS_MIDPOINT_MS,
        "--link same-token: expected serialised wall-clock > {RS_MIDPOINT_MS}ms \
         (~= 2*{RS_SLEEP_MS}ms), got {link_ms}ms — the two same-token \
         ResourceSerial calls did not serialise in the linked binary (spec §10.12.4)"
    );
}

// spec: spec/10-io.md §10.12.4 — two data-independent ResourceSerial calls with
// DIFFERENT resource tokens run CONCURRENTLY (different token groups dispatch in
// parallel on the thread pool). Wall-clock witness: each call sleeps 200 ms, so
// the concurrent total stays below the 1.5x midpoint (300 ms). Asserted in BOTH
// `--run` and `--link`.
//
// FAILING-NOT-IGNORED DEFECT GUARD (S83): this currently FAILS — automatic IO
// scheduling (spec §10.12) is not wired into the live pipeline
// (`apply_bind_chain_analysis` is dead code), so no `Par` node is emitted and
// the diff-token calls run SEQUENTIALLY (~2*200 = ~400 ms, not <300 ms). It is
// the spec-correct regression guard for FIXME
// 0367-int-resource-serial-scheduling-not-wired (target: /int; the
// runtime-dispatch remainder of FIXME 0353); it flips green
// when the ParBind-insertion pass is reactivated on the hot path. Do NOT relax
// this to a tight ratio or weaken the inequality to make it pass — the failure
// IS the defect signal.
#[test]
fn resource_serial_diff_token_parallelizes() {
    // Different tokens: 1 and 2. Best-of-N min (positive witness; see
    // best_of_n_ms) so full-workspace CPU saturation can't masquerade as a
    // scheduling regression.
    let run_ms = best_of_n_ms(|| rs_run_elapsed_ms(1, 2));
    assert!(
        run_ms < RS_MIDPOINT_MS,
        "--run diff-token: expected concurrent wall-clock < {RS_MIDPOINT_MS}ms \
         (~= 1*{RS_SLEEP_MS}ms), got {run_ms}ms — the two different-token \
         ResourceSerial calls did not run concurrently (spec §10.12.4). \
         If grouping is genuinely not happening, this is the FIXME-0353 \
         scheduling-not-wired defect, not a margin to relax."
    );

    let link_ms = best_of_n_ms(|| rs_link_elapsed_ms(1, 2));
    assert!(
        link_ms < RS_MIDPOINT_MS,
        "--link diff-token: expected concurrent wall-clock < {RS_MIDPOINT_MS}ms \
         (~= 1*{RS_SLEEP_MS}ms), got {link_ms}ms — the two different-token \
         ResourceSerial calls did not run concurrently in the linked binary \
         (spec §10.12.4)."
    );
}

// =============================================================================
// Sprint 84 Cluster B — AUTOMATIC IO PARALLELISATION (PO-0367 checklist).
//
// Plan: tests/plan/sprint84-test-plan.md §B (FIXMEs 0367 / 0353). The
// independence-analysis pass that inserts `Par` nodes from `bind` chains is
// dead code today (`apply_bind_chain_analysis`, zero live callers), so NO `Par`
// node is emitted and every chain runs sequentially. These e2e proxies are the
// Wave-0 failing-first guards /qa owns for PO-0367.1 / .2 (the deterministic
// AST-property contract is pinned by /dev unit tests in the wiring change-set;
// these e2e proxies CAN be RED at Wave-0 and ARE the failing-first signal).
//
// TIMING DISCIPLINE: identical to the §10.12.4 ResourceSerial pair above —
// D = 200 ms per call, structural inequality at the 1.5*D = 300 ms midpoint
// (50% slack each side), the link COMPILE excluded from the timing window
// (produce-only `.link()` then exec + time the produced binary). Robust margins,
// NOT tight ratios — timing-flakiness is a banned disposition.
//
// SCHEDULING-CLASS COVERAGE (per spec §10.12.2):
//   - Commutative  (`commutative-sleep-ms`)        → MUST parallelise when
//     data-independent (the POSITIVE proxy, RED today).
//   - ResourceSerial (`resource-serial-sleep-ms`)  → MUST stay serial when
//     data-DEPENDENT regardless of token (the NEGATIVE proxy, GREEN-stay).
//   - Sequential   (`print`)                       → MUST stay ordered/serial
//     always (the NEGATIVE proxy, GREEN-stay).
// =============================================================================

/// A two-binding Commutative `bind` chain. Both `commutative-sleep-ms` calls
/// are data-independent (`a` not free in the second, `b` not free in the first)
/// and Commutative → spec §10.12.1 REQUIRES a `Par` node. The terminal
/// `Pure (add-i64 a b)` makes `main : IO Int`; summed sleeps = exit code.
/// `2*200 = 400 -> 400 mod 256 = 144`.
fn commutative_indep_program() -> String {
    format!(
        "(platform test-capture)\n\
         (import [platform.test-capture [commutative-sleep-ms]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main []\n\
           (bind (commutative-sleep-ms {RS_SLEEP_MS}) (fn [a]\n\
             (bind (commutative-sleep-ms {RS_SLEEP_MS}) (fn [b]\n\
               (Pure (primitives/add-i64 a b)))))))\n"
    )
}

/// A two-binding ResourceSerial `bind` chain that is DATA-DEPENDENT: the second
/// call's token derives from the first call's result (`a`), so `a` IS free in
/// the second effect → independence analysis MUST NOT Par-group it (spec
/// §10.12.1). Even after wiring this stays serial (~2*D). Both calls use token
/// derived so they sleep `RS_SLEEP_MS`; summed = 400 -> exit 144.
fn resource_dependent_program() -> String {
    // The second token is `(add-i64 a 1)` — derived from the first result `a`,
    // making the second effect data-dependent on the first. Independence
    // analysis sees `a` free in the second binding and must keep it serial.
    format!(
        "(platform test-capture)\n\
         (import [platform.test-capture [resource-serial-sleep-ms]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main []\n\
           (bind (resource-serial-sleep-ms 1 {RS_SLEEP_MS}) (fn [a]\n\
             (bind (resource-serial-sleep-ms (primitives/add-i64 a 1) {RS_SLEEP_MS}) (fn [b]\n\
               (Pure (primitives/add-i64 a b)))))))\n"
    )
}

/// A two-binding Sequential `bind` chain (`stdio`'s `print`,
/// SchedulingClass::Sequential — which writes to REAL stdout, so ordering is
/// observable in the captured process stdout; the `test-capture` `print` routes
/// into an internal FFI buffer and is NOT visible in process stdout). Sequential
/// effects MUST execute in source order and MUST NOT be Par-grouped (spec
/// §10.12.1 / §10.12.2). Terminal `Pure 0` → exit 0; the witness is ORDERED
/// stdout ("first" before "second").
fn sequential_class_program() -> String {
    "(platform stdio)\n\
     (import [platform.stdio [print]])\n\
     (import [primitives [bind Pure]])\n\
     (defn main []\n\
       (bind (print \"first\") (fn [a]\n\
         (bind (print \"second\") (fn [b]\n\
           (Pure 0))))))\n"
        .to_string()
}

/// Wall-clock an arbitrary IO program under `--run`, asserting `expected_exit`
/// so a silent mis-run can't masquerade as a timing pass. Mirrors
/// `rs_run_elapsed_ms` but parameterised on source + expected exit.
fn prog_run_elapsed_ms(source: &str, expected_exit: i32) -> u128 {
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", source)
        .run("main.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(expected_exit),
        "--run: expected exit {expected_exit} (both effects ran)\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    out.elapsed.as_millis()
}

/// Wall-clock an arbitrary IO program under `--link`: link (produce only, NOT
/// timed), then exec the produced standalone binary and time only that run.
/// Mirrors `rs_link_elapsed_ms` but parameterised on source + expected exit.
fn prog_link_elapsed_ms(source: &str, expected_exit: i32) -> u128 {
    use std::process::Command;
    use std::time::Instant;

    let platform_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug");

    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", source)
        .link("main.cl")
        .output();
    assert!(
        out.status.success(),
        "--link: link step failed\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );

    let produced = out.tmpdir.join("main");
    assert!(
        produced.exists(),
        "--link: produced binary missing at {}\nstdout:\n{}\nstderr:\n{}",
        produced.display(),
        out.stdout,
        out.stderr
    );

    let start = Instant::now();
    let run = Command::new(&produced)
        .current_dir(&out.tmpdir)
        .env("CRANELISP_PLATFORM_PATH", &platform_path)
        .output()
        .expect("exec produced --link binary");
    let elapsed = start.elapsed();
    assert_eq!(
        run.status.code(),
        Some(expected_exit),
        "--link produced binary: expected exit {expected_exit} (both effects ran)\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    elapsed.as_millis()
}

// spec: spec/10-io.md §10.12.1 — Automatic IO Scheduling: a data-independent,
// Commutative pair MUST be parallelised (the compiler MUST insert a `Par`
// node). Wall-clock witness: two data-independent 200ms Commutative calls run
// concurrently → < 1.5*D midpoint in BOTH `--run` and `--link`.
//
// FAILING-NOT-IGNORED DEFECT GUARD (S84, PO-0367.1 positive proxy): RED today —
// the independence-analysis pass is not wired into the live pipeline, so no
// `Par` node is emitted and the two Commutative calls run SEQUENTIALLY
// (~2*200 = ~400 ms, not < 300 ms). It is the spec-correct guard for FIXME 0367
// (target: /int); it flips GREEN when the ParBind-insertion pass is reactivated.
// Distinct from `resource_serial_diff_token_parallelizes` (which proxies the
// ResourceSerial token path); this one proxies the Commutative independence
// path. Do NOT relax the inequality to make it pass — the failure IS the defect.
#[test]
fn auto_io_independent_diff_token_parallelizes_e2e() {
    let src = commutative_indep_program();
    // Best-of-N min (positive witness; see best_of_n_ms) so full-workspace CPU
    // saturation can't masquerade as a scheduling regression.
    let run_ms = best_of_n_ms(|| prog_run_elapsed_ms(&src, 144));
    assert!(
        run_ms < RS_MIDPOINT_MS,
        "--run independent-Commutative: expected concurrent wall-clock < \
         {RS_MIDPOINT_MS}ms (~= 1*{RS_SLEEP_MS}ms), got {run_ms}ms — the two \
         data-independent Commutative calls did not run concurrently (spec \
         §10.12.1). If grouping is genuinely not happening, this is the FIXME-0367 \
         scheduling-not-wired defect, not a margin to relax."
    );

    let link_ms = best_of_n_ms(|| prog_link_elapsed_ms(&src, 144));
    assert!(
        link_ms < RS_MIDPOINT_MS,
        "--link independent-Commutative: expected concurrent wall-clock < \
         {RS_MIDPOINT_MS}ms (~= 1*{RS_SLEEP_MS}ms), got {link_ms}ms — the two \
         data-independent Commutative calls did not run concurrently in the \
         linked binary (spec §10.12.1)."
    );
}

// spec: spec/10-io.md §10.12.1 — Automatic IO Scheduling: independence analysis.
// A DATA-DEPENDENT pair (the second binding references an earlier-bound name)
// MUST NOT be Par-grouped — it MUST stay serial. Wall-clock witness: two 200ms
// calls where the second's token derives from the first's result run
// SEQUENTIALLY → > 1.5*D midpoint in BOTH `--run` and `--link`.
//
// NEGATIVE / GREEN-STAY GUARD (S84, PO-0367.1 data-dependent proxy): serial
// today (nothing parallelises) AND must STAY serial after wiring — it proves the
// independence analysis is REAL ("not parallelise all diff-token pairs"). Catches
// a wiring that over-parallelises a data-dependent chain (a correctness bug).
#[test]
fn auto_io_data_dependent_stays_serial_e2e() {
    let src = resource_dependent_program();
    let run_ms = prog_run_elapsed_ms(&src, 144);
    assert!(
        run_ms > RS_MIDPOINT_MS,
        "--run data-dependent: expected serial wall-clock > {RS_MIDPOINT_MS}ms \
         (~= 2*{RS_SLEEP_MS}ms), got {run_ms}ms — a data-dependent chain was \
         wrongly parallelised (the second effect's token derives from the first \
         result; spec §10.12.1 forbids Par-grouping it)."
    );

    let link_ms = prog_link_elapsed_ms(&src, 144);
    assert!(
        link_ms > RS_MIDPOINT_MS,
        "--link data-dependent: expected serial wall-clock > {RS_MIDPOINT_MS}ms \
         (~= 2*{RS_SLEEP_MS}ms), got {link_ms}ms — a data-dependent chain was \
         wrongly parallelised in the linked binary (spec §10.12.1)."
    );
}

// spec: spec/10-io.md §10.12.1 — Automatic IO Scheduling: Sequential-class
// effects are always executed in source order and MUST NOT be Par-grouped (spec
// §10.12.1 / §10.12.2 — `print` is SchedulingClass::Sequential). Observable
// witness: two `print` effects emit in source order ("first" before "second").
//
// NEGATIVE / GREEN-STAY GUARD (S84, PO-0367.1 Sequential-class proxy): ordered
// today AND must STAY ordered after wiring. Catches a wiring that parallelises a
// Sequential pair (an ordering bug). Asserted in `--run` and `--link` (where the
// produced binary's stdout is the program's print output directly).
#[test]
fn auto_io_sequential_class_stays_serial_e2e() {
    let src = sequential_class_program();

    // --run: the two prints must appear in source order.
    let run_out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", &src)
        .run("main.cl")
        .output();
    assert_eq!(
        run_out.status.code(),
        Some(0),
        "--run Sequential: expected exit 0\nstdout:\n{}\nstderr:\n{}",
        run_out.stdout, run_out.stderr
    );
    let first_idx = run_out.stdout.find("first");
    let second_idx = run_out.stdout.find("second");
    assert!(
        first_idx.is_some()
            && second_idx.is_some()
            && first_idx < second_idx,
        "--run Sequential: expected 'first' to precede 'second' (source order; \
         spec §10.12.1) — Sequential effects must NOT be reordered.\nstdout:\n{}",
        run_out.stdout
    );

    // --link: same ordering in the produced standalone binary.
    let link_out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", &src)
        .link_then_run("main.cl")
        .output();
    assert_eq!(
        link_out.status.code(),
        Some(0),
        "--link Sequential: expected exit 0\nstdout:\n{}\nstderr:\n{}",
        link_out.stdout, link_out.stderr
    );
    let lfirst = link_out.stdout.find("first");
    let lsecond = link_out.stdout.find("second");
    assert!(
        lfirst.is_some() && lsecond.is_some() && lfirst < lsecond,
        "--link Sequential: expected 'first' to precede 'second' (source order; \
         spec §10.12.1) in the linked binary.\nstdout:\n{}",
        link_out.stdout
    );
}

// spec: spec/10-io.md §10.12 — Automatic IO Scheduling MODE-UNIFORMITY
// (PO-0367.2): the same source MUST yield the same Par-grouping decision in
// `--run`, `--link`, AND the REPL — no mode silently skips the pass. The current
// dormant state IS a mode-uniformity hole (the REPL-eval path "does not invoke
// auto-scheduling"). Witnessed by the timing decision in each mode: a
// data-independent Commutative program parallelises (< 1.5*D) in every mode.
//
// FAILING-NOT-IGNORED DEFECT GUARD (S84, PO-0367.2): RED in ALL modes today (the
// pass is dormant everywhere → all serial). Flips GREEN when 0367 wires the
// grouping decision mode-uniformly (including the REPL-eval seam). Asserts the
// grouping DECISION is identical across `--run` and `--link` via the timing
// witness in each. (The REPL timing witness is intentionally folded into the
// per-mode `--run`/`--link` assertions here; a REPL-specific eval-path proxy is
// the companion B.2.b, deferred to /dev's wiring change-set.)
#[test]
fn auto_io_par_grouping_uniform_across_modes() {
    let src = commutative_indep_program();

    // The grouping decision must be the SAME (parallelise) in --run and --link.
    // Both timing windows must fall below the 1.5*D midpoint — if any mode skips
    // the pass, that mode measures ~2*D and this fails for that mode.
    // Best-of-N min per leg (positive witness; see best_of_n_ms) so
    // full-workspace CPU saturation can't masquerade as a mode-uniformity hole.
    let run_ms = best_of_n_ms(|| prog_run_elapsed_ms(&src, 144));
    assert!(
        run_ms < RS_MIDPOINT_MS,
        "--run mode: data-independent Commutative program did not parallelise \
         (wall-clock {run_ms}ms >= {RS_MIDPOINT_MS}ms) — the auto-scheduling pass \
         is dormant in --run (mode-uniformity hole; spec §10.12)."
    );

    let link_ms = best_of_n_ms(|| prog_link_elapsed_ms(&src, 144));
    assert!(
        link_ms < RS_MIDPOINT_MS,
        "--link mode: data-independent Commutative program did not parallelise \
         (wall-clock {link_ms}ms >= {RS_MIDPOINT_MS}ms) — the auto-scheduling pass \
         is dormant in --link (mode-uniformity hole; spec §10.12)."
    );
}

// =============================================================================
// Sprint 85 Item 4 — 0398 Par-boundary FORK-JOIN ERROR FERRY (NEW e2e guards).
//
// Plan: tests/plan/sprint85-test-plan.md §Item 4 (FIXME 0398). The Par/IO
// analogue of `tests/spec_12_runtime.rs::lenient_binding_panic_not_swallowed_neg`
// (the IVar/lenient boundary), extending the witness to the Par boundary that
// 0367's wiring newly activates on user effects.
//
// CONSTRUCTION (mechanism 1 from the plan — no new fixture): a data-independent
// two-effect `bind` chain over `commutative-sleep-ms`, where ONE branch's
// argument raises a runtime panic via `(div-i64 N 0)`. The div-by-zero fires
// inside the branch's argument-computation dynamic extent. Pre-0367 the chain
// runs sequentially; post-0367 the same chain is Par-grouped and the panic
// fires inside a spark — the ferry (already landed S76, io.rs:527-564) must
// re-raise it on the joining thread.
//
// EMPIRICAL W0-STATE (verified 2026-06-17, PRE-0367-wiring): both guards are
// GREEN now (the bind chain still runs sequentially, so the panic surfaces
// trivially on the own thread). They are therefore MUST-STAY-GREEN regression
// guards — analogous to `resource_serial_same_token_serializes` — that prove
// the ferry keeps surfacing the first error once Par grouping activates. They
// MUST NOT regress to a swallowed panic (exit 0 / spurious slot pollution) when
// 0367 wires Par emission. (Were the panic ever swallowed across the Par fork,
// these flip RED — exactly the 0398 defect signal.)
//
// LINK-MODE NOTE: a div-by-zero panic in a `--link` produced binary currently
// terminates by SIGSEGV (exit 139), not a clean "division by zero" message —
// a PRE-EXISTING `--link` panic-surfacing gap independent of Par and of 0367
// (reproduces with a plain non-bind div-by-zero `--run`/`--link` program). To
// avoid entangling 0398's ferry guard with that separate gap, the `--link` leg
// asserts only the spec-load-bearing property — the panic is NOT silently
// swallowed (exit non-zero, never a clean exit 0) — while the `--run` leg
// asserts the full "division by zero" surfacing. The message-in-`--link` gap is
// a separate concern, not this guard's subject.

/// A two-binding Commutative `bind` chain where the FIRST branch's argument
/// raises a div-by-zero runtime panic: `(commutative-sleep-ms (div-i64 200 0))`.
/// The other branch is a clean 200ms sleep. Data-independent (`a` not free in
/// the second binding) → 0367 Par-groups it; the panic fires inside the first
/// branch's spark. The terminal `Pure (add-i64 a b)` would make `main : IO Int`
/// were both branches to complete — but the panic must abort first.
fn par_branch_panic_program() -> String {
    format!(
        "(platform test-capture)\n\
         (import [platform.test-capture [commutative-sleep-ms]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main []\n\
           (bind (commutative-sleep-ms (primitives/div-i64 {RS_SLEEP_MS} 0)) (fn [a]\n\
             (bind (commutative-sleep-ms {RS_SLEEP_MS}) (fn [b]\n\
               (Pure (primitives/add-i64 a b)))))))\n"
    )
}

// spec: spec/12-runtime.md §12.4.3 — a runtime panic inside one branch of a
// fork-join (the §10.12 automatic-IO scheduling case) MUST surface on the
// joining thread; it MUST NOT be silently discarded. The Par/IO analogue of
// `lenient_binding_panic_not_swallowed_neg`.
//
// MUST-STAY-GREEN regression guard (S85, 0398; gated-on-0367 by construction):
// GREEN today (sequential — panic surfaces on own thread) AND must STAY green
// after 0367 wires Par emission (the landed ferry re-raises the first error on
// join). A regression to a swallowed panic flips this RED — the 0398 signal.
#[test]
fn auto_io_par_branch_panic_surfaces_on_join_neg() {
    let src = par_branch_panic_program();

    // --run: the panic MUST surface with the "division by zero" message and a
    // non-zero exit — NOT a swallowed sentinel that lets main exit 0.
    let run_out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", &src)
        .run("main.cl")
        .output();
    assert_ne!(
        run_out.status.code(),
        Some(0),
        "--run Par-branch panic: expected non-zero exit (panic surfaced), got \
         exit 0 — the div-by-zero in a Par branch was silently swallowed \
         (spec §12.4.3 fork-join error propagation).\nstdout:\n{}\nstderr:\n{}",
        run_out.stdout, run_out.stderr
    );
    assert!(
        run_out.stderr.contains("division by zero")
            || run_out.stdout.contains("division by zero"),
        "--run Par-branch panic: expected the 'division by zero' panic message to \
         surface on the joining thread (spec §12.4.3) — it MUST NOT be silently \
         discarded.\nstdout:\n{}\nstderr:\n{}",
        run_out.stdout, run_out.stderr
    );

    // --link: the produced binary MUST also not silently swallow the panic
    // (exit non-zero). The full message-surfacing in --link is gated on a
    // separate pre-existing --link panic gap (see the LINK-MODE NOTE above), so
    // this leg asserts only the spec-load-bearing non-swallow property.
    let link_out = Cranelisp::new()
        .use_workspace_platforms()
        .file("main.cl", &src)
        .link_then_run("main.cl")
        .output();
    assert_ne!(
        link_out.status.code(),
        Some(0),
        "--link Par-branch panic: produced binary exited 0 — the div-by-zero in \
         a Par branch was silently swallowed in the linked binary (spec §12.4.3 \
         fork-join error propagation MUST NOT discard a branch panic).\n\
         stdout:\n{}\nstderr:\n{}",
        link_out.stdout, link_out.stderr
    );
}

// spec: spec/12-runtime.md §12.4.3 — after a fork-join branch panic surfaces,
// the runtime-error slot MUST be clean for a subsequent read in the same
// process — the first-error-wins + slot-clear half of the ferry. Witnessed at
// the REPL: a Par-grouped bind chain whose first branch panics, then a clean
// independent expression in the SAME session, which MUST evaluate correctly
// (not spuriously inherit the prior error).
//
// MUST-STAY-GREEN regression guard (S85, 0398 companion; gated-on-0367 by
// construction): GREEN today (sequential — the slot is cleared on read, the
// next expression is clean) AND must STAY green after 0367 wires Par emission.
// A slot left polluted across the Par fork flips this RED.
#[test]
fn auto_io_par_branch_panic_no_slot_pollution_neg() {
    // Line 1-3: load the platform + primitives. Line 4: a Par-eligible
    // (data-independent) two-effect bind chain whose first branch panics
    // (div-by-zero). Line 5: a clean independent expression — MUST yield 42,
    // proving the error slot was not left polluted by the prior panic.
    let session = "(platform test-capture)\n\
                   (import [platform.test-capture [commutative-sleep-ms]])\n\
                   (import [primitives [bind Pure add-i64 div-i64]])\n\
                   (bind (commutative-sleep-ms (div-i64 200 0)) (fn [a]\n\
                     (bind (commutative-sleep-ms 200) (fn [b]\n\
                       (Pure (add-i64 a b))))))\n\
                   (add-i64 40 2)\n";

    Cranelisp::new()
        .use_workspace_platforms()
        .repl()
        .stdin(session)
        .output()
        // The panic from the first (Par) branch must surface, AND the
        // subsequent clean expression must NOT inherit the error slot — it
        // evaluates to 42 (no spurious error attached to it).
        .assert_stdout_contains_all(&["division by zero", ":primitives/Int 42"]);
}
