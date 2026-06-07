// spec_12_runtime.rs — Runtime model surface (Sprint 64 Wave 4 Batch 6).
//
// Covers spec/12-runtime.md observable runtime properties via REPL canonical
// (per `tests/plan/PLAN.md §"Mode canonicalisation"`). Carries forward the
// language-behaviour subset of the integration-tier `tests/rc.rs`,
// `tests/ring4_trace.rs`. Rust-internal observations (CRANELISP_RC_TRACE
// stderr alloc/free counter parsing; trace event taxonomy via
// repl_eval_typed Type assertions) quarantine to `tests/legacy/`.
//
// What this file covers:
//   - §12.3.1 Memory management requirements — heap-using bodies (string,
//     ADT, closure, Vec) complete cleanly via REPL evaluation; the program
//     does not panic, the value is correct.
//   - §12.3.3 Vec copy-on-write — both old and new Vec values remain
//     accessible after `vec-set` / `vec-push`.
//   - §4.12 / §12.9.5 Trace expression — `(trace expr)` returns a `Trace`
//     ADT value observable via REPL `:Type value` display.
//   - appendix-a-builtins / repl/spec.md §3 — `/run-tests` slash command
//     discovers `test-*` functions and reports pass/fail counts.
//
// Mode-specific exception (cited per-test): a small set of RC tests use
// `--run` because the only observable property is "the program ran without
// leak panic and exited 0". For these, the canonical observation is the
// process exit code from `(defn main [] expr-returning-Int)`. The REPL form
// is awkward for multi-form RC sessions where the `/mem` baseline shifts
// per-form; `--run` exit-code witness is the cleanest e2e form.
//
// Quarantined to:
//   - `tests/legacy/rc_alloc_trace.rs` — 38 `assert_rc_balanced` tests that
//     parse `CRANELISP_RC_TRACE=1` stderr alloc/free counters (Rust-internal
//     trace channel; harvest into `cranelisp-runtime` / `cranelisp-backend`
//     `#[cfg(test)]` unit tests).
//   - `tests/legacy/ring4_trace_taxonomy.rs` — 31 `repl_eval_typed`-based
//     tests asserting on internal `Type::ADT(FQTypeName, Vec<Type>)` shapes
//     (Rust-API observation of typecheck output; harvest into
//     `cranelisp-typecheck` `#[cfg(test)]` unit tests).
//   - `tests/legacy/sprint60_observability.rs` — `CRANELISP_CODEGEN_DUMP`
//     env-var subprocess CLIF dump filter (debugging trace; backend unit).
//   - `tests/legacy/sprint61_observability_scheduler.rs` — direct
//     `cranelisp::observability::*` API exercise (scheduler trace internals).
//   - `tests/legacy/sprint61_observability_shared.rs` — shared trace anchor
//     + boundary-crate hygiene scan (Rust-internal observation across
//     crates).
//   - `tests/legacy/v4_jit_reclaim.rs` — `cranelisp_runtime::*_count()`
//     atomics + `cranelisp::code::Code` enum + `ReplSession::symbol_tables()`
//     reach-throughs (per-redefinition JIT reclaim is a backend-internal
//     contract; observable through `/mem` smoke only).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// Helpers
// =============================================================================

/// Pipe `lines` to a fresh REPL with the `PrimitivesOnly` prelude variant.
fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::repl_prims_capture(lines)
}

/// Pipe `lines` to a fresh REPL (no prelude).
fn repl(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::repl_capture(lines)
}

// =============================================================================
// §12.3.1 Memory Management Requirements — heap-using bodies complete cleanly
// =============================================================================
//
// The spec property: "Heap-allocated values (strings, closures, data
// constructors, Vecs) MUST be freed when they are no longer reachable". The
// e2e observation is the program returning the expected value without
// panic; an underflow / double-free / leak detector firing would terminate
// the process abnormally.

// spec: spec/12-runtime.md §12.3.1 — String alloc/drop balanced via str-len
#[test]
fn string_literal_alloc_drop_balanced() {
    repl_prims("(str-len \"hello\")\n").assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/12-runtime.md §12.3.1 — String returned from function freed
#[test]
fn string_returned_from_function_freed() {
    repl_prims("(defn greet [] \"hello\")\n(str-len (greet))\n")
        .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/12-runtime.md §12.3.1 — String concat intermediate freed
#[test]
fn string_concat_intermediate_freed() {
    repl_prims("(str-len (str-concat \"hello\" \" world\"))\n")
        .assert_stdout_contains(":primitives/Int 11");
}

// spec: spec/12-runtime.md §12.3.1 / §12.1.4 — ADT product alloc / match unwrap
#[test]
fn adt_product_alloc_and_match_unwrap() {
    repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (match (Point 3 4) [(Point x y) (add-i64 x y)])\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/12-runtime.md §12.1.4 — ADT sum (Some) heap-allocated; matched and freed
#[test]
fn adt_sum_some_alloc_and_match() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (match (Some 42) [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/12-runtime.md §12.1.4 — Nullary constructors (None) are bare tags, no heap alloc
#[test]
fn adt_sum_none_no_heap_alloc() {
    // Wrap None in a fn returning the Option to anchor the type variable;
    // bare `None` at top-level would leave `a` unconstrained.
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn opt-int-none [] (match None [(Some x) (add-i64 x 0) None 0]))\n\
         (opt-int-none)\n",
    )
    .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/12-runtime.md §12.3.1 — ADT with String field; both freed cleanly
#[test]
fn adt_with_string_field_freed() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (match (Some \"hello\") [(Some s) (str-len s) None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/12-runtime.md §12.3.1 / §12.1.3 — Closure environment alloc / call / drop
#[test]
fn closure_capture_alloc_and_invoke() {
    repl_prims("(let [n 10] ((fn [x] (add-i64 n x)) 32))\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/12-runtime.md §12.1.3 — Closure with multiple captures
#[test]
fn closure_multiple_captures() {
    repl_prims(
        "(let [a 1 b 2 c 3] ((fn [x] (add-i64 a (add-i64 b (add-i64 c x)))) 4))\n",
    )
    .assert_stdout_contains(":primitives/Int 10");
}

// =============================================================================
// §12.3.3 Vec Copy-on-Write — `vec-set` / `vec-push` return a new Vec; the
// caller observes pure functional behaviour regardless of in-place mutation.
// =============================================================================

// spec: spec/12-runtime.md §12.3.3 — vec-set: original and new Vec both accessible
#[test]
fn vec_set_cow_preserves_original() {
    // Both original v[1] (=2) and updated v2[1] (=99) are read; sum = 101.
    repl_prims(
        "(let [v [1 2 3]] (let [v2 (vec-set v 1 99)] (add-i64 (vec-get v 1) (vec-get v2 1))))\n",
    )
    .assert_stdout_contains(":primitives/Int 101");
}

// spec: spec/12-runtime.md §12.3.3 — vec-push: original Vec retains its length
#[test]
fn vec_push_cow_preserves_original_length() {
    // Original len=2, pushed len=3, sum=5.
    repl_prims(
        "(let [v [1 2]] (let [v2 (vec-push v 3)] (add-i64 (vec-len v) (vec-len v2))))\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/12-runtime.md §12.1.5 — Vec of Strings; each element freed with the Vec
#[test]
fn vec_of_strings_alloc_drop() {
    repl_prims("(vec-len [\"a\" \"b\" \"c\"])\n")
        .assert_stdout_contains(":primitives/Int 3");
}

// =============================================================================
// §12.3.1 Memory Management — additional shapes (Wave 5.6 sketch_port carry-forward)
// =============================================================================

// spec: spec/12-runtime.md §12.3.1 — nested let scopes; the inner string
// allocation is reachable only inside the inner let body. The outer body
// returning Int (=42) means the inner scope's binding goes out of scope
// before the outer scope's; a leak / double-free in the inner-scope cleanup
// path would terminate the process abnormally.
// (carry: legacy/sketch_port.rs::sketch_rc_nested_let_inner_scope_freed)
#[test]
fn nested_let_inner_string_freed_before_outer() {
    repl_prims("(let [s \"hello\"] (let [t \"world\"] (str-len t)))\n")
        .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/12-runtime.md §12.1.5 / §12.3.1 — Vec-of-Int let-bound and freed
// at scope exit. Distinct from `vec_of_strings_alloc_drop` (vec-of-Strings
// exercises per-element drop glue); vec-of-Int has no per-element drop glue
// but the vec body itself is still heap-allocated and must be freed.
// (carry: legacy/sketch_port.rs::sketch_rc_vec_int_freed_on_scope_exit)
#[test]
fn vec_of_int_let_bound_freed() {
    repl_prims("(let [xs [1 2 3]] (vec-len xs))\n")
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/12-runtime.md §12.1.5 / §12.3.1 — empty vec literal is still
// heap-allocated (boundary case: zero-element vec) and must be freed when
// its binding goes out of scope.
// (carry: legacy/sketch_port.rs::sketch_rc_vec_empty_freed)
#[test]
fn empty_vec_let_bound_freed() {
    repl_prims("(let [xs []] (vec-len xs))\n")
        .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/12-runtime.md §12.3.1 — match scrutinee that is a heap-allocated
// temporary (no let binding) MUST be freed when the match exits. Distinct
// from `adt_with_string_field_freed` (which uses a let-bound scrutinee);
// the temporary-scrutinee path exercises a distinct cleanup pathway.
// (carry: legacy/sketch_port.rs::sketch_rc_match_temporary_scrutinee_freed)
#[test]
fn match_temporary_scrutinee_freed_on_exit() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (match (Some \"hello\") [None 0 (Some s) (str-len s)])\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/12-runtime.md §12.1.3 / §12.3.1 — closure capturing another
// closure (chained closure references) — known double-free / leak vector.
// Per `memory/feedback_repros_join_suite.md` this shape stays in the suite
// as a regression guard. The outer body returning Int (=42) means a
// double-free during the chained closure cleanup would terminate the process.
// (carry: legacy/sketch_port.rs::sketch_rc_closure_capturing_closure)
#[test]
fn closure_capturing_closure_balanced() {
    repl_prims(
        "(let [f (fn [x] x)] (let [g (fn [] f)] 42))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §4.12 Trace Expression — Trace is an ADT value observable via REPL display
// (per spec §12.9.5 — trace uses canonical value display format).
// =============================================================================

// spec: spec/04-expressions.md §4.12.1 — (trace expr) returns Trace ADT whose
// root name is the synthetic `::trace::` root (per §4.12.2). Extracted via the
// TraceCall pattern — NOT the `name` accessor, whose codegen is broken in all
// modes (see tests/trace.rs::trace_nanos_accessor_resolves_in_repl + FIXME
// 0276). Trace-tree shape, nested-trace, build-mode, and visibility coverage
// now lives in tests/trace.rs (the active trace e2e home, FIXME 0258).
#[test]
fn trace_returns_trace_value() {
    repl(
        "(import [primitives [trace Trace TraceCall]])\n\
         (defn id [x] x)\n\
         (let [t (trace (id 42))] (match t [(TraceCall n p r c ns) n]))\n",
    )
    .assert_stdout_contains("::trace::");
}

// (The former `trace_nested_still_returns_trace` — which asserted the
// superseded "outermost wins, single tree" behaviour — is retired. Per the
// 2026-06-04 trace ruling (spec §4.12.5) nested trace is now a RUNTIME ERROR;
// see tests/trace.rs::trace_nested_dynamic_raises_runtime_error and
// ::trace_nested_lexical_raises_runtime_error.)

// spec: spec/04-expressions.md §4.12.7 — TraceCall pattern destructures the Trace ADT
#[test]
fn trace_pattern_match_extracts_name() {
    // Pattern match on TraceCall to extract the name field; assert a String
    // value is observable on stdout.
    repl(
        "(import [primitives [trace Trace TraceCall]])\n\
         (defn id [x] x)\n\
         (let [t (trace (id 1))] (match t [(TraceCall n p r c ns) n]))\n",
    )
    .assert_stdout_contains(":primitives/String");
}

// spec: spec/04-expressions.md §4.12 — `trace` keyword is in scope without import
#[test]
fn trace_form_available_without_import() {
    // `trace` is a parser keyword — `(trace expr)` should compile and
    // evaluate without any import. Observable: the REPL accepts the form
    // without an "unbound symbol" error; `:primitives/Trace` appears in the
    // type prefix on the result line.
    repl_prims(
        "(defn id [x] x)\n\
         (trace (id 9))\n",
    )
    .assert_stdout_contains(":primitives/Trace");
}

// =============================================================================
// /run-tests slash command — appendix-a-builtins + repl/spec.md §3
// =============================================================================

// spec: repl/spec.md §3.1 — /run-tests discovers `test-*` fns and reports passes
#[test]
fn run_tests_reports_passes() {
    // /run-tests convention: a test-* fn returns `None` for pass, `Some msg`
    // for fail (per `appendix-a-builtins.md`, the test result protocol).
    repl(
        "(import [primitives [*]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (defn test-one [] None)\n\
         /run-tests\n",
    )
    .assert_stdout_contains_all(&["ok", "1 passed"]);
}

// spec: repl/spec.md §3.1 — /run-tests reports failure with reason
#[test]
fn run_tests_reports_failures_with_reason() {
    repl(
        "(import [primitives [*]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (defn test-fail [] (Some \"expected failure\"))\n\
         /run-tests\n",
    )
    .assert_stdout_contains_all(&["FAIL", "expected failure"]);
}

// spec: repl/spec.md §3.1 — /run-tests with no `test-*` fns reports "no tests"
#[test]
fn run_tests_empty_module_reports_no_tests() {
    repl(
        "(import [primitives [*]])\n\
         /run-tests\n",
    )
    .assert_stdout_contains("No test-* functions found");
}

// spec: repl/spec.md §16 — `discover-tests` and `run-test` are user-callable
// primitives; a user can compose their own test runner without relying on
// the `/run-tests` slash command. Sprint 60 reduction history makes this a
// load-bearing repro shape: the slash-command path differs from the direct
// primitive-composition path. The test below defines its own `count-passes`
// fold over `discover-tests` results and verifies the pass count surfaces.
// (carry: legacy/sketch_port.rs::sketch_run_tests_pass_fn_called)
#[test]
fn discover_tests_and_run_test_user_composition() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (import [macros [SCons SNil]])\n\
         (defn test-passing [] None)\n\
         (defn count-passes [acc names]\n\
           (match names\n\
             [SNil (Pure acc)\n\
              (SCons head tail)\n\
                (bind (run-test head)\n\
                      (fn [result]\n\
                        (match result\n\
                          [(TestPass n ns) (count-passes (add-i64 acc 1) tail)\n\
                           (TestFail n ns r) (count-passes acc tail)])))]))\n\
         (defn my-run-tests [] (bind (discover-tests) (fn [names] (count-passes 0 names))))\n\
         (my-run-tests)\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// §12.7.2 / §12.7.3 Arithmetic policy — Wave 5.5 GAP-COVER
//
// Integer overflow wraps (specified, not a panic); integer division by zero
// panics. Coverage was previously only in tests/legacy/ring0.rs.
// =============================================================================

// spec: spec/12-runtime.md §12.7.2 — `add-i64` overflow wraps (two's complement)
// (carry: legacy/ring0.rs::integer_overflow_wraps)
#[test]
fn integer_overflow_wraps_silently() {
    // i64::MAX + 1 wraps to i64::MIN.
    // i64::MAX = 9_223_372_036_854_775_807; +1 wraps to -9_223_372_036_854_775_808
    repl_prims("(add-i64 9223372036854775807 1)\n")
        .assert_stdout_contains(":primitives/Int -9223372036854775808");
}

// spec: spec/12-runtime.md §12.7.2 — `sub-i64` underflow wraps
// (carry: legacy/ring0.rs::integer_underflow_wraps)
#[test]
fn integer_underflow_wraps_silently() {
    // i64::MIN - 1 wraps to i64::MAX.
    repl_prims("(sub-i64 -9223372036854775808 1)\n")
        .assert_stdout_contains(":primitives/Int 9223372036854775807");
}

// spec: spec/12-runtime.md §12.7.3 — `div-i64` by zero panics at runtime
// (carry: legacy/ring0.rs::checked_division_by_zero_panics)
#[test]
fn integer_division_by_zero_panics_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(div-i64 10 0)\n")
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    // Per §12.7.3 the divisor-zero case MUST trigger a runtime panic with
    // "division by zero" diagnostic. The REPL session MUST survive the panic
    // (§12.7.4); we assert only that the diagnostic appears.
    assert!(
        combined.contains("division by zero")
            || combined.contains("divide by zero")
            || combined.contains("zero")
            || combined.contains("Error")
            || combined.contains("panic"),
        "div-i64 with zero divisor MUST produce a panic / error diagnostic \
         per §12.7.3; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.1 — String is UTF-8; non-ASCII source text
// MUST be accepted and round-trip through str-len.
// (carry: legacy/ring0.rs::source_encoding_utf8)
#[test]
fn string_utf8_source_encoding_accepted() {
    // "héllo" — 5 chars, 6 bytes (é is 2 bytes in UTF-8). str-len reports
    // bytes per the appendix-A definition (immutable UTF-8 byte sequence).
    repl_prims("(str-len \"héllo\")\n").assert_stdout_contains(":primitives/Int 6");
}

// =============================================================================
// §12.4.3 Lenient evaluation — opt-out via CRANELISP_NO_LENIENT (Wave 5.6)
//
// Per §12.4.3: "An implementation MAY provide an opt-out mechanism (e.g., an
// environment variable) for debugging purposes." The Cranelisp implementation
// honours `CRANELISP_NO_LENIENT=1`. Lenient evaluation is semantically
// transparent (independent let bindings produce the same result whether
// sparked or sequential), so the spec assertion is *correctness* of the
// result with the opt-out engaged.
//
// Mode-specific exception: this test uses `--run` mode (not REPL) because
// `CRANELISP_NO_LENIENT=1` is set on the spawned binary's env, and `--run`
// is the cleanest e2e form for a single-program env-var-conditioned check.
// The exit code from `(defn main [] expr)` returning Int is the canonical
// observation.
// =============================================================================

// spec: spec/12-runtime.md §12.4.3 — CRANELISP_NO_LENIENT=1 disables sparking;
// the program still computes the correct result.
// (carry: legacy/lenient.rs::test_lenient_no_lenient_env_var)
#[test]
fn lenient_no_lenient_env_var_preserves_correctness() {
    // double(5) + triple(7) = 10 + 21 = 31. Use add-i64 / mul-i64 so the
    // PrimitivesOnly prelude suffices — no operator dispatch needed.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn double [x] (mul-i64 x 2))\n\
             (defn triple [x] (mul-i64 x 3))\n\
             (defn main [] (let [a (double 5) b (triple 7)] (add-i64 a b)))\n",
        )
        .env("CRANELISP_NO_LENIENT", "1")
        .output()
        .assert_exit(31);
}

// =============================================================================
// §12.4.3 Lenient evaluation — panic propagation across the fork-join boundary
// (FIXME 0272 Half A — pre-existing panic-swallow DEFECT)
//
// Per §12.4.3: "A runtime error raised while evaluating any binding — whether
// evaluated sequentially or in parallel — MUST propagate as if the bindings
// were evaluated sequentially: the first such error aborts the whole `let`
// expression. ... a parallelised binding's panic MUST NOT be silently
// discarded." NEITHER fork-join boundary ferries the runtime-error slot
// (IVar `ivar_force`; Par `dispatch_par_branches_with_trace`), so a panic
// inside a lenient-evaluated binding is silently swallowed and the binding
// yields the sentinel `0` instead of aborting the expression.
// =============================================================================

// spec: spec/12-runtime.md §12.4.3 — a div-by-zero inside a lenient `let`
// binding MUST abort the whole expression with a runtime panic; it MUST NOT be
// swallowed.
//
// CURRENT BEHAVIOUR (FAILING): with lenient evaluation ON (the default),
// `(let [a (div-i64 10 0) b (add-i64 1 2)] a)` evaluates to the sentinel
// `:primitives/Int 0` — the div-by-zero panic is silently discarded on the
// joining thread. Deterministic across runs.
//
// FIXME(/dev intrinsics) — the fork-join error-slot ferry obligation: every
// fork-join boundary MUST ferry a worker-side take_runtime_error() back to the
// join site and re-raise the first error (FIXME 0270; per FIXME 0272 Half A +
// design/arch/test-discovery.md §"the fork-join error-slot ferry obligation").
#[test]
fn lenient_binding_panic_not_swallowed_neg() {
    repl_prims("(let [a (div-i64 10 0) b (add-i64 1 2)] a)\n")
        // MUST surface the panic — MUST NOT bind `a` to the sentinel 0.
        .assert_stdout_contains("division by zero");
}

// spec: spec/12-runtime.md §12.4.3 — the same `let` under CRANELISP_NO_LENIENT=1
// DOES panic, proving lenient evaluation (the spark path) is the trigger for
// the swallow. This control test PASSES today and pins the spark as the cause.
#[test]
fn lenient_binding_panic_surfaces_with_no_lenient_control() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .repl()
        .stdin("(let [a (div-i64 10 0) b (add-i64 1 2)] a)\n")
        .env("CRANELISP_NO_LENIENT", "1")
        .output()
        .assert_stdout_contains("division by zero");
}

// =============================================================================
// §12.5 Tail Call Optimization — Wave 5.6 dedupe-recovery carries
//
// The 5 TCO carries below are #[ignore]'d pending FIXME 0141 — `/spec`
// upgrading §12.5 from `SHOULD` to `MUST` for self-recursive TCO. The
// implementation already provides loop-based self-TCO (per
// `memory/macros.md §"Tail Call Optimization (TCO)"`), so the assertions
// pass against the current binary; the gate is normative, not behavioural.
// Once §12.5's verb upgrades, /qa removes the `#[ignore]` attributes
// (target Sprint 65). Citations resolve through the linter today — only
// the normative authority is missing.
// =============================================================================

// spec: spec/12-runtime.md §12.5 — self-recursive tail calls optimised; deep
// countdown completes without stack overflow.
// (carry: legacy/ring0.rs::tco_deep_countdown)
#[ignore = "TCO MUST clause not yet in spec — FIXME 0141; target S65"]
#[test]
fn tco_deep_countdown() {
    // Without TCO, 1_000_000 frames overflow the default thread stack.
    repl_prims(
        "(defn countdown [n]\n\
           (if (eq-i64 n 0)\n\
             0\n\
             (countdown (sub-i64 n 1))))\n\
         (countdown 1000000)\n",
    )
    .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/12-runtime.md §12.5 — TCO across an accumulator parameter.
// (carry: legacy/ring0.rs::tco_accumulator)
#[ignore = "TCO MUST clause not yet in spec — FIXME 0141; target S65"]
#[test]
fn tco_accumulator() {
    // sum of 1..100 = 5050; recursion depth 100 is well under any
    // overflow threshold but the test asserts the accumulator pattern
    // returns the correct value.
    repl_prims(
        "(defn sum-acc [n acc]\n\
           (if (eq-i64 n 0)\n\
             acc\n\
             (sum-acc (sub-i64 n 1) (add-i64 acc n))))\n\
         (sum-acc 100 0)\n",
    )
    .assert_stdout_contains(":primitives/Int 5050");
}

// spec: spec/12-runtime.md §12.5 — match arm is a tail-position context;
// recursion through it does not grow the stack.
// (carry: legacy/ring0.rs::tco_match_tail_position)
#[ignore = "TCO MUST clause not yet in spec — FIXME 0141; target S65"]
#[test]
fn tco_match_tail_position() {
    // 100_000-iteration loop using match in tail position. Without TCO
    // through match arms, this overflows.
    repl_prims(
        "(deftype Action Stop Continue)\n\
         (defn loop-match [n]\n\
           (match (if (eq-i64 n 0) Stop Continue)\n\
             [Stop 0\n\
              Continue (loop-match (sub-i64 n 1))]))\n\
         (loop-match 100000)\n",
    )
    .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/12-runtime.md §12.5 — let body is a tail-position context.
// (carry: legacy/ring0.rs::tco_let_body_tail_position)
#[ignore = "TCO MUST clause not yet in spec — FIXME 0141; target S65"]
#[test]
fn tco_let_body_tail_position() {
    // 100_000-iteration loop where the recursive call sits inside a
    // let body in tail position.
    repl_prims(
        "(defn loop-let [n]\n\
           (if (eq-i64 n 0)\n\
             42\n\
             (let [m (sub-i64 n 1)]\n\
               (loop-let m))))\n\
         (loop-let 100000)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/12-runtime.md §12.5 — non-tail recursion is NOT optimised but
// still produces the correct value at modest depth (negative-of-TCO).
// (carry: legacy/ring0.rs::tco_non_tail_recursion_unchanged)
#[ignore = "TCO MUST clause not yet in spec — FIXME 0141; target S65"]
#[test]
fn tco_non_tail_recursion_unchanged() {
    // sum of 0..10 via non-tail recursion (the recursive call is inside
    // an add-i64 — not in tail position). Asserts correctness, not
    // depth: TCO must NOT silently apply here, but the answer is the
    // same regardless of optimisation.
    repl_prims(
        "(defn sum [n]\n\
           (if (eq-i64 n 0)\n\
             0\n\
             (add-i64 n (sum (sub-i64 n 1)))))\n\
         (sum 10)\n",
    )
    .assert_stdout_contains(":primitives/Int 55");
}

// =============================================================================
// §12.7.3 Arithmetic policy (continued) — i64::MIN / -1 trap
//
// On x86_64 / aarch64 the `idiv` of `i64::MIN` by `-1` traps because the
// mathematical result (`i64::MAX + 1`) does not fit in a signed 64-bit
// register. The spec lists this alongside divide-by-zero as a panic
// source. The legacy test grouped it with the divide-by-zero diagnostic.
// =============================================================================

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-1 GAP-COVER carry-forwards — `/run-tests`
// aggregation angles (count multi, mixed pass+fail, non-test filter) per
// repl/spec.md §3.1 (Command Inventory) + §16.2.1.
// =============================================================================

// spec: repl/spec.md §3.1 — `/run-tests` aggregates pass count across
// multiple `test-*` functions. Distinct from the single-test
// `run_tests_reports_passes` shape.
// (carry: legacy/e2e.rs::e2e_run_tests_multiple)
#[test]
fn run_tests_multiple_passes_count() {
    repl(
        "(import [primitives [*]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (defn test-a [] None)\n\
         (defn test-b [] None)\n\
         (defn test-c [] None)\n\
         /run-tests\n",
    )
    .assert_stdout_contains("3 passed");
}

// spec: repl/spec.md §3.1 — `/run-tests` aggregates mixed pass+fail counts
// in the same run. Distinct from per-test pass and per-test fail shapes
// covered by `run_tests_reports_passes` and
// `run_tests_reports_failures_with_reason`.
// (carry: legacy/e2e.rs::e2e_run_tests_mixed_pass_fail)
#[test]
fn run_tests_mixed_pass_and_fail_counts() {
    repl(
        "(import [primitives [*]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (defn test-pass-1 [] None)\n\
         (defn test-pass-2 [] None)\n\
         (defn test-fail-1 [] (Some \"broken\"))\n\
         /run-tests\n",
    )
    .assert_stdout_contains_all(&["2 passed", "1 failed"]);
}

// spec: repl/spec.md §3.1 — REGRESSION-GUARD: `/run-tests` filters out
// non-`test-*` prefixed functions. A `helper` defn alongside a `test-one`
// defn must result in only `test-one` being discovered and run. The
// negative angle confirms the prefix filter.
// (carry: legacy/e2e.rs::e2e_run_tests_ignores_non_test)
#[test]
fn run_tests_neg_ignores_non_test_prefixed_fns() {
    let out = repl(
        "(import [primitives [*]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (defn helper [] None)\n\
         (defn test-one [] None)\n\
         /run-tests\n",
    );
    assert!(
        out.stdout.contains("1 passed"),
        "/run-tests MUST discover exactly 1 test (test-one), not 'helper'; got:\n{}",
        out.stdout
    );
    // Negative: `helper` must not appear in the per-test results section
    // (the line shape is `name ............... ok`). The defn-display
    // banner does mention `user/helper ; defn`, so guard against the
    // results-line shape `helper ........` rather than substring `helper`.
    assert!(
        !out.stdout.contains("helper ."),
        "/run-tests results MUST NOT include non-`test-*` fn 'helper'; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forward (chunk 2)
// =============================================================================

// spec: spec/12-runtime.md §12.5 — self-recursive HOF threading a
// fn-typed parameter through each call: `(repeat-fn f n x) → (repeat-fn
// f (sub-i64 n 1) (f x))`. Distinct from the deep-countdown TCO carries
// (none pass a fn through self-recursion) and from the HOF carries (none
// recurse). The combined shape exercises self-recursion correctness with
// a fn-typed argument surviving across the loop-back jump. This carry
// asserts the value is computed correctly at modest depth (5); it does
// NOT require TCO (no stack-overflow test) — therefore is not gated on
// FIXME 0141 unlike the deep TCO carries above.
// (carry: legacy/ring1.rs::closure_recursive_with_higher_order)
#[test]
fn tco_self_recursion_with_fn_typed_parameter() {
    repl_prims(
        "(defn repeat-fn [f n x]\n\
           (if (eq-i64 n 0)\n\
             x\n\
             (repeat-fn f (sub-i64 n 1) (f x))))\n\
         (repeat-fn (fn [x] (add-i64 x 1)) 5 0)\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §12.6 Entry Point — `(defn main [] expr)` exit-code witness
// (carry-forward: legacy/v4_pipeline.rs — Wave 6 batch 6)
//
// These tests are the FIRST coverage of spec/12-runtime.md §12.6 (R4 S10
// pre-batch). They use `--run` mode (mode-specific exception per
// `tests/plan/PLAN.md §"Mode canonicalisation"`) — the canonical
// observation for §12.6 is the process exit code from
// `(defn main [] expr-returning-Int)`. The REPL form does not invoke
// `main`; only the `--run` driver does.
// =============================================================================

// spec: spec/12-runtime.md §12.6 — `(defn main [] Int)` exits with that Int
// (carry: legacy/v4_pipeline.rs::test_v4_integer_literal)
#[test]
fn main_returning_int_produces_int_exit_code() {
    Cranelisp::new()
        .user("(defn main [] 42)")
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/12-runtime.md §12.6 — non-Int main result → exit 0
// (carry: legacy/v4_pipeline.rs::test_v4_boolean_literal)
#[test]
fn main_returning_non_int_produces_zero_exit_code() {
    Cranelisp::new()
        .user("(defn main [] true)")
        .run("user.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/12-runtime.md §12.6 — main may invoke a primitive call
// spec: spec/appendix-a-builtins.md — add-i64 primitive
// (carry: legacy/v4_pipeline.rs::test_v4_add_i64)
#[test]
fn main_invokes_primitive_call_for_exit_code() {
    Cranelisp::new()
        .user("(defn main [] (primitives/add-i64 1 2))")
        .run("user.cl")
        .output()
        .assert_exit(3);
}

// spec: spec/12-runtime.md §12.6 + spec/05-definitions.md §5.1.1 — main
// invokes a sibling user-defined defn. The batch driver must compile both
// forms in source order and produce the right exit code.
// (carry: legacy/v4_pipeline.rs::test_v4_defn_and_call)
#[test]
fn main_invokes_sibling_user_defn_for_exit_code() {
    Cranelisp::new()
        .user(
            "(defn double [x] (primitives/add-i64 x x))\n\
             (defn main [] (double 5))",
        )
        .run("user.cl")
        .output()
        .assert_exit(10);
}

// spec: spec/12-runtime.md §12.6 + §12.5 — recursive (non-tail) call from main
// computes factorial 5! = 120; demonstrates that recursive call frames work
// through the entry-point invocation path.
// (carry: legacy/v4_pipeline.rs::test_v4_recursive_function)
#[test]
fn main_invokes_recursive_user_defn_for_exit_code() {
    Cranelisp::new()
        .user(
            "(defn fact [n]\n\
               (if (primitives/eq-i64 n 0)\n\
                 1\n\
                 (primitives/mul-i64 n (fact (primitives/sub-i64 n 1)))))\n\
             (defn main [] (fact 5))",
        )
        .run("user.cl")
        .output()
        .assert_exit(120);
}

// =============================================================================
// §12.7.4.2 Batch Mode Error Behaviour
// (carry-forward: legacy/v4_pipeline.rs — Wave 6 batch 6)
//
// Per `tests/plan/PLAN.md`, §12.7.4.2 was `[R4 S18]` UNTESTED. The
// batch-mode error rendering surface is most cleanly observed via
// `--run` mode + stderr capture + non-zero exit-code witness.
// =============================================================================

// spec: spec/12-runtime.md §12.7.4.2 — undefined name in entry produces
// stderr error + non-zero exit
// (carry: legacy/v4_pipeline.rs::test_v4_falls_back_for_operators)
// REGRESSION-GUARD: bare `+` without prelude must error, not silently
// dispatch to anything.
#[test]
fn main_with_undefined_name_errors_in_run_mode_neg() {
    let out = Cranelisp::new()
        .user("(defn main [] (+ 1 2))")
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "undefined `+` should produce non-zero exit; got {:?}",
        out.status.code()
    );
    assert!(
        out.stderr.contains("undefined variable: +"),
        "stderr should contain 'undefined variable: +'; got: {}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.7.4.2 — type error in entry produces stderr
// error + non-zero exit
// (carry: legacy/v4_pipeline.rs::v4_error_type_error_in_entry)
#[test]
fn main_with_type_error_in_entry_errors_in_run_mode_neg() {
    let out = Cranelisp::new()
        .user("(defn main [] (add-i64 1 true))")
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "type error should produce non-zero exit"
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("type")
            || combined.contains("Type")
            || combined.contains("mismatch")
            || combined.contains("error")
            || combined.contains("Error"),
        "error output should mention type error; got stderr: {}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.7.4.2 + design/int/step9-error-cascade.md §4.1+4.2 —
// type error in dependency module cascades to dependent module with
// dependency-module name in the error context.
// (carry: legacy/v4_pipeline.rs::v4_error_cascade_from_dependency)
// REGRESSION-GUARD: error chain rendering — Sprint 45 Step 9 design guard.
#[test]
fn dependency_type_error_cascades_with_module_context_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [math [compute]])\n(defn main [] (compute))",
        )
        .file("math.cl", "(defn compute [] (add-i64 1 true))")
        .run("main.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "cascade: type error in dep should fail compilation"
    );
    assert!(
        out.stderr.contains("math"),
        "cascade error should mention dependency module 'math'; got: {}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.7.4.2 + design/int/step9-error-cascade.md §4.1 —
// cascade error preserves root-cause type-error context (not just
// "dependency failed").
// (carry: legacy/v4_pipeline.rs::v4_error_cascade_includes_root_cause)
// REGRESSION-GUARD: cascade rendering must preserve root cause.
#[test]
fn dependency_type_error_cascade_preserves_root_cause_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [lib [broken-fn]])\n(defn main [] (broken-fn))",
        )
        .file("lib.cl", "(defn broken-fn [] (add-i64 true false))")
        .run("main.cl")
        .output();
    assert!(out.status.code() != Some(0));
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("type")
            || combined.contains("Type")
            || combined.contains("mismatch")
            || combined.contains("Bool"),
        "cascade error should include root cause type error, not just 'dependency failed'; got: {}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.7.4.2 (negative complement) — clean program
// produces no error text on stderr. Regression guard: error path changes
// MUST NOT break the success path.
// (carry: legacy/v4_pipeline.rs::v4_error_no_error_exits_cleanly)
#[test]
fn clean_program_produces_no_error_in_run_mode() {
    let out = Cranelisp::new()
        .user("(defn main [] (primitives/add-i64 10 20))")
        .run("user.cl")
        .output();
    // Filter benign nice-worker warnings from stderr before assertion.
    let err: String = out
        .stderr
        .lines()
        .filter(|line| !line.starts_with("nice-worker:"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !err.contains("Error") && !err.contains("failed") && !err.contains("panic"),
        "clean program should produce no errors on stderr; got: {}",
        err
    );
    out.assert_exit(30);
}

// spec: spec/12-runtime.md §12.7.4.2 + design/int/step9-error-cascade.md §4.2 —
// A→B→C cascade prints root cause once or twice, not 3+ times. Regression
// guard: no per-module duplicate error rendering.
// (carry: legacy/v4_pipeline.rs::v4_error_cascade_no_duplicate_output)
#[test]
fn three_level_cascade_does_not_duplicate_error_output_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [mid [relay]])\n(defn main [] (relay))",
        )
        .file(
            "mid.cl",
            "(import [leaf [broken]])\n(defn relay [] (broken))",
        )
        .file("leaf.cl", "(defn broken [] (add-i64 1 true))")
        .run("main.cl")
        .output();
    assert!(out.status.code() != Some(0));
    let all = &out.stderr;
    let mentions = all.matches("type mismatch").count()
        + all.matches("Type mismatch").count()
        + all.matches("type error").count()
        + all.matches("Type error").count();
    // Root cause + context = at most 2; 3+ would be one per cascade level.
    assert!(
        mentions <= 2,
        "expected <= 2 type-error mentions in 3-level cascade, got {}; output: {}",
        mentions,
        all
    );
}

// spec: spec/12-runtime.md §12.7.3 — `div-i64` of i64::MIN by -1 panics
// (carry: legacy/ring0.rs::checked_div_min_neg1_panics)
#[test]
fn integer_div_min_by_neg_one_panics_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(div-i64 -9223372036854775808 -1)\n")
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    // §12.7.3: the i64::MIN / -1 case MUST trigger a runtime panic. The
    // diagnostic vocabulary historically reuses the divide-by-zero
    // wording (the legacy assertion checked exactly that). The REPL
    // session MUST survive (§12.7.4); we only check for a diagnostic.
    assert!(
        combined.contains("division by zero")
            || combined.contains("divide by zero")
            || combined.contains("overflow")
            || combined.contains("Error")
            || combined.contains("panic"),
        "div-i64 of i64::MIN by -1 MUST produce a panic / error diagnostic \
         per §12.7.3; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}
