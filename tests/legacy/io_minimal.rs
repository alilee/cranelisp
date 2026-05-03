// Minimal reduction of the Sprint 57 Wave 6 IO-path SIGBUS cluster.
//
// =============================================================================
// REGRESSION GUARD (Sprint 57 Wave 6 — CLOSED)
// =============================================================================
//
// These tests were written to expose a cluster of ~25 SIGBUS failures in
// tests/io.rs, tests/stdlib.rs (macro_do_*) and v4_repl_discover_and_run_test_via_bind.
// All involved IO bind-chains built inside a REPL-session eval, then forced by
// `run_io_trampoline` AFTER the session-level eval had already returned. By
// that point Sprint 57 Wave 4's `impl Drop for Jit` had freed the executable
// page the continuation pointer pointed into, so invoking the continuation
// jumped to unmapped memory.
//
// **The bug is fixed**: `src/pipeline.rs::compile_and_execute_expr` now calls
// `unwrap_io_inline` before the per-eval `Jit` drops, trampolining the IO
// tree while the JIT's executable pages are still live. The returned
// `EvalResult::Val { value, ty }` is the fully-reduced inner value —
// never a raw IO pointer that outlives the JIT.
//
// These tests are kept as regression guards. If a future change reintroduces
// the old "return raw IO pointer, trampoline later" pattern, these tests
// will SIGBUS again and catch the regression.
//
// CONTRACT UNDER TEST:
//   compile_and_run_typed("(defn main [] (Pure 42))") returns (42, Int) —
//   the IO type has been unwrapped inline and the caller sees the final
//   value directly. No manual `run_io_trampoline` call is required, and
//   the raw IO pointer never escapes into test-land.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;

// =============================================================================
// LEVEL 0 — control: no IO at all
// =============================================================================

// Plain integer eval through the REPL session path. Proves the harness
// and the per-eval JIT drop are fine for non-IO return types.
#[test]
fn minimal_0_plain_int_via_repl() {
    let (value, ty) = compile_and_run_typed("(defn main [] 42)");
    assert_eq!(value, 42);
    assert_eq!(ty, cranelisp_types::Type::Int);
}

// =============================================================================
// LEVEL 1 — Pure node, unwrapped inline by the eval contract
// =============================================================================

// Pure by itself: IO tree has no closure. After the Wave-6 fix, the eval
// path trampolines the IO tree inline and returns the unwrapped Int.
// Regression guard: if the fix regresses, `ty` will come back as `IO Int`
// and/or the raw IO heap pointer will leak out as `value`.
//
// spec: 10-io §10.2 — Pure through the eval contract
#[test]
fn minimal_1_pure_trampoline_after_eval() {
    let (value, ty) = compile_and_run_typed("(defn main [] (Pure 42))");
    assert_eq!(ty, cranelisp_types::Type::Int, "eval must unwrap IO inline; got {ty:?}");
    assert_eq!(value, 42, "eval must return the unwrapped Pure inner value");
}

// =============================================================================
// LEVEL 2 — bind(Pure, lambda) via batch_run (was already correct pre-fix)
// =============================================================================

// batch_run has always trampolined IO before returning (trampoline fires
// inside `CompilerSession::trampoline`, before the per-eval JIT drops).
// This test stays unchanged as a "control group" to prove the fix doesn't
// regress the batch path.
//
// spec: 10-io §10.3 — bind of Pure(42) with identity continuation, batch path
#[test]
fn minimal_2_bind_pure_lambda_via_batch_run() {
    let src = "(defn main [] (bind (Pure 42) (fn [x] (Pure x))))";
    let (value, _ty) = batch_run(src).expect("batch_run of identity bind failed");
    assert_eq!(value, 42);
}

// =============================================================================
// LEVEL 3 — bind(Pure, lambda), trampolined inline by the eval contract
// =============================================================================

// Exact same bind source as Level 2, but evaluated through compile_and_run_typed.
// Pre-fix this SIGBUSed because the IO tree's Bind node held a closure code
// pointer into the per-eval JIT, which was dropped before the test called
// run_io_trampoline. Post-fix the trampoline runs inline while the JIT is
// still alive, and the test sees the unwrapped final value.
//
// spec: 10-io §10.3 — bind of Pure with lambda continuation through eval contract
#[test]
fn minimal_3_bind_pure_lambda_trampolines_inline() {
    let (value, ty) = compile_and_run_typed(
        "(defn main [] (bind (Pure 42) (fn [x] (Pure x))))",
    );
    assert_eq!(ty, cranelisp_types::Type::Int, "eval must unwrap IO inline; got {ty:?}");
    assert_eq!(value, 42, "bind/identity-continuation must reduce to 42 inline");
}

// =============================================================================
// LEVEL 4 — bind with a named defn as continuation, trampolined inline
// =============================================================================

// If Level 3 passes but Level 4 had regressed, the JIT-drop issue would be
// narrowed to top-level defn fn references rather than anonymous lambdas.
// Both live in the same per-eval JIT, so both must trampoline inline.
//
// spec: 10-io §10.3 — named defn as bind continuation through eval contract
#[test]
fn minimal_4_bind_named_defn_trampolines_inline() {
    // `my-pure` is a user-defined fn; bind references it as a function value.
    let (value, ty) = compile_and_run_typed(
        "(defn my-pure [x] (Pure x))\n(defn main [] (bind (Pure 77) my-pure))",
    );
    assert_eq!(ty, cranelisp_types::Type::Int, "eval must unwrap IO inline; got {ty:?}");
    assert_eq!(value, 77, "bind/named-defn continuation must reduce to 77 inline");
}
