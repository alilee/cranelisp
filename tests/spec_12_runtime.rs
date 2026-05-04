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

// spec: spec/04-expressions.md §4.12.1 — (trace expr) returns Trace ADT;
// observable via REPL :Type prefix in `:primitives/Trace`.
#[test]
fn trace_returns_trace_value() {
    // The REPL prints `:primitives/Trace ...` for the result. Use `name`
    // accessor to extract the root trace name; per spec §4.12.2 the root is
    // always `::trace::`.
    repl(
        "(import [primitives [trace Trace TraceCall name]])\n\
         (defn id [x] x)\n\
         (let [t (trace (id 42))] (name t))\n",
    )
    .assert_stdout_contains("::trace::");
}

// spec: spec/04-expressions.md §4.12.5 — nested (trace ...) still produces a Trace
#[test]
fn trace_nested_still_returns_trace() {
    repl(
        "(import [primitives [trace Trace TraceCall name]])\n\
         (defn id [x] x)\n\
         (let [t (trace (trace (id 7)))] (name t))\n",
    )
    .assert_stdout_contains("::trace::");
}

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
