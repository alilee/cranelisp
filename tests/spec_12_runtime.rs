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
// spec: spec/03-types.md §3.11.1 — the let-bound `[]` is `(Vec a)` at a
// codegen-reaching position; under the tightened full-concreteness verdict the
// unpinned element type is a type error, pinned with `:(Vec Int) []` (the
// directed remedy). The RC-balance property under test is unchanged — the
// binding is still heap-allocated and freed at scope exit.
// (carry: legacy/sketch_port.rs::sketch_rc_vec_empty_freed)
#[test]
fn empty_vec_let_bound_freed() {
    repl_prims("(let [xs :(Vec Int) []] (vec-len xs))\n")
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
// spec: spec/03-types.md §3.11.1 — the captured `f` is `(Fn [a] a)`, a
// polymorphic function value at an unresolved type reaching codegen; under the
// tightened full-concreteness verdict the unpinned `a` is a type error, pinned
// with `:(Fn [Int] Int) (fn [x] x)`. The chained-closure RC-balance property
// under test is unchanged.
// (carry: legacy/sketch_port.rs::sketch_rc_closure_capturing_closure)
#[test]
fn closure_capturing_closure_balanced() {
    repl_prims(
        "(let [f :(Fn [Int] Int) (fn [x] x)] (let [g (fn [] f)] 42))\n",
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
        "(import [primitives [Trace TraceCall]])\n\
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
        "(import [primitives [Trace TraceCall]])\n\
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

// spec: design/arch/test-discovery.md §4.3 — `discover-tests` and
// `catch-runtime-error` are user-callable `primitives`; a user composes
// their own test runner over the discovered name+callable pairs without the
// `/run-tests` slash command. This is the load-bearing composability shape
// (ruling 1): the runner folds over the `(Vec (Pair String (Fn [] (Option
// String))))` discovery result, brackets each late-bound callable with
// `catch-runtime-error`, and counts passes. The retired `run-test` /
// `TestResult` (TestPass/TestFail) surface and the SList-of-names return are
// gone (src/CLAUDE.md §"Test discovery"; test-discovery.md fourth
// convergence) — this test asserts the current fn-value-pairs surface.
//
// Two properties this exercises beyond construction:
//   - explicit `(Vec String)` module argument — the no-arg `(discover-tests)`
//     form is STDLIB-MACRO sugar (test-discovery.md §150), and tests are
//     stdlib-free (CLAUDE.md), so the bare extern is called with `["user"]`.
//   - q-eligibility (test-discovery.md §162): a `test-*` fn is discovered only
//     if its type is EXACTLY `(Fn [] (Option String))`. A bare `(defn test-x
//     [] None)` infers the polymorphic `(Fn [] (Option a))` and is correctly
//     excluded; `(if true None (Some "..."))` forces `(Option String)`.
#[test]
fn discover_tests_and_catch_runtime_error_user_composition() {
    repl_prims(
        // test-passing returns None typed (Option String) (the (Some ..) arm
        // forces the element type); test-failing returns (Some msg). Only the
        // passing one is counted → expect 1.
        "(defn test-passing [] (if true None (Some \"never\")))\n\
         (defn test-failing [] (Some \"boom\"))\n\
         (defn count-passes [acc i pairs]\n\
           (if (eq-i64 i (vec-len pairs))\n\
               acc\n\
               (match (vec-get pairs i)\n\
                 [(Pair name run)\n\
                  (match (catch-runtime-error run)\n\
                    [(Ok inner)\n\
                       (match inner\n\
                         [None      (count-passes (add-i64 acc 1) (add-i64 i 1) pairs)\n\
                          (Some why) (count-passes acc (add-i64 i 1) pairs)])\n\
                     (Err msg)  (count-passes acc (add-i64 i 1) pairs)])])))\n\
         (defn my-run-tests [] (count-passes 0 0 (discover-tests [\"user\"])))\n\
         (my-run-tests)\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// FIXME 0289 Half B — `catch-runtime-error` arm coverage across modes +
// `discover-tests` eligibility-exclusion negative.
//
// The composition test above exercises the Ok/None pass-counting path in REPL.
// Half B adds the two coverage gaps the design calls out:
//   - `catch-runtime-error` over a *panicking* thunk → `(Err …)` and over a
//     clean thunk → `(Ok …)`, demonstrated end-to-end in `--run` AND `--link`
//     (the combinator is a self-contained intrinsic — appendix-A "works in all
//     modes including --link"). The Err vs Ok arm selects the program's exit
//     code, so the e2e observation is the exit code, not stdout.
//   - `discover-tests` excludes a mis-typed `test-*` (negative) — discovery
//     requires BOTH the `test-` prefix AND the exact signature
//     `(Fn [] (Option String))`.
//
// `--run`/`--link` programs do not get the implicit primitives re-export the
// REPL `repl_prims` helper provides, so each entry program imports the names it
// uses from `primitives` explicitly. `main` returns `(IO _)` via `Pure`
// (S80 main:IO enforcement); the inner Int becomes the process exit code.
// =============================================================================

// The `--run`/`--link` entry program: `catch-runtime-error` over a thunk that
// divides by zero (a `runtime/panic` source per §12.7.2.1). The Err arm is
// selected → `main` yields `(Pure 0)` → exit 0. The Ok arm (had the thunk not
// panicked) would yield 1 — so exit 0 proves the Err arm fired.
const CATCH_ERR_PROGRAM: &str = "(import [primitives [catch-runtime-error div-i64 Result Ok Err Pure]])\n\
     (defn main []\n\
       (Pure (match (catch-runtime-error (fn [] (div-i64 10 0)))\n\
               [(Ok v)   1\n\
                (Err m)  0])))\n";

// Clean-thunk counterpart: the thunk computes 42 without panicking, so the Ok
// arm fires and `main` yields `(Pure 42)` → exit 42.
const CATCH_OK_PROGRAM: &str = "(import [primitives [catch-runtime-error add-i64 Result Ok Err Pure]])\n\
     (defn main []\n\
       (Pure (match (catch-runtime-error (fn [] (add-i64 40 2)))\n\
               [(Ok v)   v\n\
                (Err m)  -1])))\n";

// spec: spec/appendix-a-builtins.md §"Test discovery and error capture" —
// `catch-runtime-error` returns `(Err message)` when the thunk raises a
// language-level runtime error; self-contained intrinsic, works in `--run`.
#[test]
fn catch_runtime_error_err_arm_run() {
    Cranelisp::new()
        .file("user.cl", CATCH_ERR_PROGRAM)
        .run("user.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/appendix-a-builtins.md §"Test discovery and error capture" —
// `catch-runtime-error` "works in all modes including --link". The Err arm
// must fire identically in a linked standalone binary.
#[test]
fn catch_runtime_error_err_arm_link() {
    Cranelisp::new()
        .file("user.cl", CATCH_ERR_PROGRAM)
        .link_then_run("user.cl")
        .output()
        .assert_exit(0);
}

// =============================================================================
// FIXME 0399 — `--link` runtime-panic surfacing parity with `--run`.
//
// An UNCAUGHT runtime panic (div-by-zero, §12.7.2.1) in a `main : IO Int`:
//   - under `--run`  surfaces cleanly: non-zero exit + "division by zero" on
//     stderr (§12.7.4.2 batch-mode requirement). GREEN today (the control).
//   - under `--link` (produced standalone binary) the SAME program SIGSEGVs
//     (exit 139) with NO message — the linked startup stub forces the
//     panic-path sentinel through `cranelisp_run_io` → null-deref.
//
// The `--link` produced binary IS a batch-mode process (§12.7.4.2): "a runtime
// panic terminates the process with a non-zero exit code … MUST print the panic
// message to stderr". A SIGSEGV (139) is NOT a clean non-zero batch exit, and
// no message is printed — so the linked binary violates §12.7.4.2 / §12.7.8.3.
//
// This is the failing-not-ignored 0399 guard: RED today (exit 139, no message);
// it flips GREEN when the `--link` panic boundary is wired to mirror `--run`.
// =============================================================================

// The minimal free-standing div-by-zero entry (per FIXME 0399). Zero stdlib;
// explicit `primitives` imports. An uncaught `(div-i64 1 0)` inside `main`.
const UNCAUGHT_PANIC_PROGRAM: &str =
    "(import [primitives [Pure div-i64]])\n\
     (defn main [] (Pure (div-i64 1 0)))\n";

// spec: spec/12-runtime.md §12.7.4.2 — batch-mode CONTROL (the `--run` leg).
// An uncaught div-by-zero panic in `main` under `--run` MUST terminate the
// process with a non-zero exit code AND print "division by zero" to stderr.
// GREEN today — proves the cross-mode divergence is the `--link` defect, not the
// program (companion to the FIXME 0399 `--link` guard below).
#[test]
fn uncaught_runtime_panic_surfaces_message_and_clean_exit_run() {
    let out = Cranelisp::new()
        .file("user.cl", UNCAUGHT_PANIC_PROGRAM)
        .run("user.cl")
        .output();
    assert_ne!(
        out.status.code(),
        Some(0),
        "--run uncaught div-by-zero: expected non-zero exit (§12.7.4.2); \
         got exit 0.\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    // Clean batch exit, not a signal-kill: code() is Some(_), not a SIGSEGV.
    assert!(
        out.status.code().is_some(),
        "--run uncaught div-by-zero: expected a clean process exit code \
         (§12.7.4.2), not a signal kill.\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("division by zero") || out.stdout.contains("division by zero"),
        "--run uncaught div-by-zero: expected the 'division by zero' panic \
         message to surface (§12.7.4.2 — MUST print to stderr before exiting).\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// spec: spec/12-runtime.md §12.7.4.2 — the `--link` produced binary is a
// batch-mode process and MUST surface a runtime panic the same way `--run`
// does: a clean non-zero exit code AND "division by zero" on stderr. Today the
// linked binary SIGSEGVs (exit 139) with NO message — the §12.7.4.2 / §12.7.8.3
// batch-exit requirement is not wired into the `--link` panic boundary.
//
// FAILING-NOT-IGNORED guard for FIXME 0399 — RED today (exit 139, no message);
// flips GREEN when /dev wires the linked-binary panic boundary to mirror `--run`.
#[test]
fn uncaught_runtime_panic_surfaces_message_and_clean_exit_link() {
    let out = Cranelisp::new()
        .file("user.cl", UNCAUGHT_PANIC_PROGRAM)
        .link_then_run("user.cl")
        .output();
    // (1) Clean batch exit, NOT a SIGSEGV. status.code() is None when the
    // process was killed by a signal (exit 139 == SIGSEGV) — the bug.
    assert!(
        out.status.code().is_some(),
        "--link uncaught div-by-zero: produced binary was killed by a signal \
         (SIGSEGV / exit 139) instead of exiting cleanly — §12.7.4.2 requires a \
         clean non-zero batch exit code, and the panic boundary must not \
         null-deref.\nstatus={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    // (2) Non-zero exit (the panic was not swallowed).
    assert_ne!(
        out.status.code(),
        Some(0),
        "--link uncaught div-by-zero: produced binary exited 0 — the panic was \
         swallowed (§12.7.4.2 requires non-zero exit on a runtime panic).\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    // (3) The message surfaces, mirroring `--run` (§12.7.4.2 MUST print to stderr).
    assert!(
        out.stderr.contains("division by zero") || out.stdout.contains("division by zero"),
        "--link uncaught div-by-zero: expected the 'division by zero' panic \
         message to surface in the produced binary, matching `--run` \
         (§12.7.4.2). Got no message.\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// FIXME 0401 — runtime error raised INSIDE an IO `bind` continuation SIGSEGVs
// in BOTH `--run` AND `--link` (exit 139). The general case of FIXME 0399.
//
// 0399 (fixed this sprint) covered a panic in `main`'s body BEFORE any IO — see
// `uncaught_runtime_panic_surfaces_message_and_clean_exit_{run,link}` above,
// which now surface "division by zero" + a clean exit.
//
// THIS pair covers the DURING-IO case those guards do not reach: the panic is
// raised by the continuation passed to `bind`, while the IO trampoline is
// running. The continuation returns the panic-path sentinel `0`; the IO
// trampoline reads that `0` back and dereferences it (`read_node_tag(0)`),
// producing a null-deref SIGSEGV. Neither the `--run` host nor the `--link`
// startup stub checks the panic slot after the trampoline returns, so the
// sentinel is forced through `cranelisp_run_io` → segfault in BOTH modes.
//
// The `--run` process and the `--link` produced binary are both batch-mode
// processes (§12.7.4.2): "a runtime panic terminates the process with a
// non-zero exit code … MUST print the panic message to stderr". A SIGSEGV
// (139) is NOT a clean non-zero batch exit, and no message is printed.
//
// FAILING-NOT-IGNORED guards for FIXME 0401 — RED today (exit 139, no message
// in either mode); both flip GREEN when /dev wires the IO trampoline panic
// boundary to surface the error and exit cleanly (mirroring the 0399 fix).
// =============================================================================

// Minimal free-standing div-by-zero raised INSIDE an IO `bind` continuation
// (per FIXME 0401). Zero stdlib; explicit `primitives` imports. The `div-i64`
// runs in the `(fn [x] ...)` passed to `bind` — i.e. during the IO trampoline,
// not in `main`'s body before IO.
const UNCAUGHT_PANIC_IN_IO_PROGRAM: &str =
    "(import [primitives [Pure bind div-i64 Int]])\n\
     (defn main [] (bind (Pure 1) (fn [x] (Pure (div-i64 x 0)))))\n";

// spec: spec/12-runtime.md §12.7.4.2 — a runtime panic raised inside an IO
// `bind` continuation under `--run` MUST terminate the process with a clean
// non-zero exit code AND print "division by zero" to stderr — the same as a
// panic in `main`'s body (the 0399 control above). Today the IO trampoline
// dereferences the panic-path sentinel and the process SIGSEGVs (exit 139)
// with NO message.
//
// FAILING-NOT-IGNORED guard for FIXME 0401 — RED today (exit 139, no message);
// flips GREEN when /dev wires the IO trampoline panic boundary to mirror `--run`.
#[test]
fn runtime_panic_in_io_continuation_surfaces_run() {
    let out = Cranelisp::new()
        .file("user.cl", UNCAUGHT_PANIC_IN_IO_PROGRAM)
        .run("user.cl")
        .output();
    // (1) Clean batch exit, NOT a SIGSEGV. status.code() is None when the
    // process was killed by a signal (exit 139 == SIGSEGV) — the bug.
    assert!(
        out.status.code().is_some(),
        "--run panic-in-IO-continuation: process was killed by a signal \
         (SIGSEGV / exit 139) instead of exiting cleanly — §12.7.4.2 requires a \
         clean non-zero batch exit code, and the IO trampoline panic boundary \
         must not null-deref.\nstatus={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    // (2) Non-zero exit (the panic was not swallowed).
    assert_ne!(
        out.status.code(),
        Some(0),
        "--run panic-in-IO-continuation: process exited 0 — the panic was \
         swallowed (§12.7.4.2 requires non-zero exit on a runtime panic).\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    // (3) The message surfaces (§12.7.4.2 MUST print to stderr before exiting).
    assert!(
        out.stderr.contains("division by zero") || out.stdout.contains("division by zero"),
        "--run panic-in-IO-continuation: expected the 'division by zero' panic \
         message to surface (§12.7.4.2 — MUST print to stderr before exiting).\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// spec: spec/12-runtime.md §12.7.4.2 — the `--link` produced binary is a
// batch-mode process and MUST surface a runtime panic raised inside an IO
// `bind` continuation the same way `--run` does: a clean non-zero exit code AND
// "division by zero" on stderr. Today the linked binary SIGSEGVs (exit 139)
// with NO message — the IO trampoline panic boundary is not wired in either
// host.
//
// FAILING-NOT-IGNORED guard for FIXME 0401 — RED today (exit 139, no message);
// flips GREEN when /dev wires the IO trampoline panic boundary to mirror `--run`.
#[test]
fn runtime_panic_in_io_continuation_surfaces_link() {
    let out = Cranelisp::new()
        .file("user.cl", UNCAUGHT_PANIC_IN_IO_PROGRAM)
        .link_then_run("user.cl")
        .output();
    // (1) Clean batch exit, NOT a SIGSEGV.
    assert!(
        out.status.code().is_some(),
        "--link panic-in-IO-continuation: produced binary was killed by a signal \
         (SIGSEGV / exit 139) instead of exiting cleanly — §12.7.4.2 requires a \
         clean non-zero batch exit code, and the IO trampoline panic boundary \
         must not null-deref.\nstatus={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    // (2) Non-zero exit (the panic was not swallowed).
    assert_ne!(
        out.status.code(),
        Some(0),
        "--link panic-in-IO-continuation: produced binary exited 0 — the panic \
         was swallowed (§12.7.4.2 requires non-zero exit on a runtime panic).\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    // (3) The message surfaces, mirroring `--run` (§12.7.4.2 MUST print to stderr).
    assert!(
        out.stderr.contains("division by zero") || out.stdout.contains("division by zero"),
        "--link panic-in-IO-continuation: expected the 'division by zero' panic \
         message to surface in the produced binary, matching `--run` \
         (§12.7.4.2). Got no message.\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// spec: spec/appendix-a-builtins.md §"Test discovery and error capture" —
// `catch-runtime-error` returns `(Ok result)` when the thunk completes
// cleanly; the inner value (42) propagates as the exit code in `--run`.
#[test]
fn catch_runtime_error_ok_arm_run() {
    Cranelisp::new()
        .file("user.cl", CATCH_OK_PROGRAM)
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/appendix-a-builtins.md §"Test discovery and error capture" —
// `discover-tests` eligibility: a `test-*` fn is discovered only if its type is
// EXACTLY `(Fn [] (Option String))`. NEGATIVE: a wrong-arity `test-*` and a
// wrong-return-type `test-*` are both excluded — only the one well-typed test
// is discovered (vec-len = 1, not 3).
#[test]
fn discover_tests_excludes_mistyped_test_neg() {
    repl_prims(
        // test-good: exact (Fn [] (Option String)) — the (Some ..) arm forces
        // the element type to String. test-bad-arity: takes an argument.
        // test-bad-ret: returns Int. Only test-good is eligible.
        "(defn test-good [] (if true None (Some \"x\")))\n\
         (defn test-bad-arity [n] (if true None (Some \"x\")))\n\
         (defn test-bad-ret [] (add-i64 1 2))\n\
         (vec-len (discover-tests [\"user\"]))\n",
    )
    // Positive: exactly one eligible test is discovered.
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
             (defn main [] (Pure (let [a (double 5) b (triple 7)] (add-i64 a b))))\n",
        )
        .env("CRANELISP_NO_LENIENT", "1")
        .output()
        .assert_exit(31);
}

// =============================================================================
// §12.4.3 Lenient evaluation — panic propagation across the fork-join boundary
// (FIXME 0272 Half A — fork-join error-slot ferry, NOW SATISFIED)
//
// Per §12.4.3: "A runtime error raised while evaluating any binding — whether
// evaluated sequentially or in parallel — MUST propagate as if the bindings
// were evaluated sequentially: the first such error aborts the whole `let`
// expression. ... a parallelised binding's panic MUST NOT be silently
// discarded." The fork-join boundary now ferries the runtime-error slot: the
// IVar force path (`ivar_force`, `crates/cranelisp-intrinsics/src/ivar.rs`)
// stashes a worker-side `take_runtime_error()` into the IVar's error field and
// re-raises it on the joining thread via `set_runtime_error`, so a panic inside
// a lenient-evaluated binding aborts the whole expression instead of yielding a
// sentinel. The ferry infrastructure landed in S76 Wave 4 (commits 9491ccc +
// e53ef13); the test became durably green no later than the S80 close (verified
// by checkout-and-run at 48dcea3 and at the S81 funnel-1/4 commit aeff79d).
// =============================================================================

// spec: spec/12-runtime.md §12.4.3 — a div-by-zero inside a lenient `let`
// binding MUST abort the whole expression with a runtime panic; it MUST NOT be
// swallowed.
//
// AS-LANDED BEHAVIOUR (PASSING regression guard): with lenient evaluation ON
// (the default), `(let [a (div-i64 10 0) b (add-i64 1 2)] a)` correctly surfaces
// the "division by zero" runtime panic rather than binding `a` to the sentinel
// `0`. The fork-join error-slot ferry obligation (worker-side
// `take_runtime_error()` -> join-side re-raise) is satisfied as of the IVar
// ferry landing (S76 Wave 4 — commits 9491ccc + e53ef13). Deterministic across
// runs.
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
// §12.4.3 Lenient evaluation — wall-clock WITNESS that independent same-block
// `let` bindings are sparked and actually run in parallel (Sprint 85 Phase 6b).
//
// Per §12.4.3: "Lenient evaluation is semantically transparent — programs MUST
// NOT depend on whether any particular binding is parallelized." The spark
// mechanism is an *observable* performance property (a speedup), so the witness
// is a WALL-CLOCK RATIO between lenient-ON (default) and lenient-OFF
// (CRANELISP_NO_LENIENT=1) over the SAME program — the same pattern the auto-IO
// timing tests in tests/spec_10_io.rs use (`prog_run_elapsed_ms`-style helper:
// run in a subprocess, time `out.elapsed`, set/clear the env per run).
//
// The program is a Vec map-reduce expressed via index-range divide-and-conquer:
// `pmr` recurses over a Vec slice [lo,hi); at a leaf it computes `fib` of the
// element; at an internal node it binds the two recursive halves to two SAME-
// BLOCK `let` bindings (`left`, `right`) whose free vars reference NO earlier
// binding in that block, so BOTH are sparkable (Apply to a non-cheap,
// non-constructor callee). Two sparkable independent bindings => the two halves
// run in parallel, and a balanced D&C tree parallelises across the whole Vec.
//
// TIMING DISCIPLINE (mirrors spec_10_io.rs §10.12.4): conservative ONE-SIDED
// margin, NOT a tight ratio — timing-flakiness is a banned disposition. Measured
// on this 10-core machine in ISOLATION: ON ~= 0.09 s, OFF ~= 0.28 s (ratio
// ~2.8-3.1x). The assertion is the slack `ON < 0.7 * OFF` (a >=1.43x speedup),
// which clears the worst observed ~2.8x by a wide margin.
//
// BEST-OF-N HARDENING (Sprint 85 flake fix). Unlike the auto-IO timing tests
// (spec_10_io.rs), which are SLEEP-based and therefore immune to CPU contention,
// this witness is CPU-BOUND (recursive `fib`). Under `cargo nextest run
// --workspace`, every core is saturated by sibling test processes, so a single
// lenient-ON run can be starved of spare cores and show ~no speedup — a false
// failure (observed once at ON=246ms vs a 240ms threshold). A CPU-bound
// wall-clock parallelism assertion measured ONCE under a saturated harness is
// fundamentally noisy.
//
// The fix is BEST-OF-N: run the ON-vs-OFF comparison up to N times and judge the
// speedup against the BEST attempt (the attempt where the parallel run got the
// most spare cores). This is sound as a parallelism proof: a purely-SEQUENTIAL
// implementation would NEVER show `ON < 0.7*OFF` in ANY attempt (its ON ~= OFF
// regardless of contention), so a single qualifying attempt still genuinely
// proves the two same-block bindings were sparked and ran in parallel. The
// SEMANTIC-TRANSPARENCY check (ON exit == OFF exit) is asserted on EVERY attempt
// — it is contention-immune and never relaxed. We early-exit as soon as the
// positive margin is met, so the common (fast) case runs once.
//
// The NEGATIVE CONTROL (prior-binding-stays-serial) gets the inverse treatment:
// a genuinely serial case shows ON ~= OFF on every attempt, so we require the
// MAJORITY of N attempts to show NO speedup (ON >= 0.7*OFF). This tolerates a
// single contention blip (an OFF-slow reading that spuriously looks like a
// speedup) while still failing loudly if the prior-binding case were wrongly
// sparked (which would show the speedup in all/most attempts).
//
// The leaf cost is `fib(35)` (Vec of 8 elements): big enough that real parallel
// work dominates spark overhead, small enough that even the worst case
// (best-of-N exhausting all N attempts for the positive test, plus the
// majority-N negative control) stays within the 30 s suite budget. With N=4 and
// early-exit, the common case is ~2 runs (positive) + 4 runs (negative) ~= 1.4s.
// =============================================================================

/// Vec leaf cost: `fib(35)` per element. Tuned so parallel work dominates spark
/// overhead (>=2.4x at >=fib(33)/Vec>=8 in the S85 probe) while keeping each run
/// short (~0.28 s lenient-OFF). Shared by the positive witness and the negative
/// control so they compute the identical value (exit code 73) and differ ONLY in
/// `let`-block structure.
const PMR_LEAF: i64 = 35;
/// Vec width — 8 elements give a balanced 3-level D&C tree (full parallel fan-out
/// across the thread pool).
const PMR_VEC: &str = "35 35 35 35 35 35 35 35";
/// Conservative speedup factor: lenient-ON wall-clock MUST be below this fraction
/// of lenient-OFF. 0.7 => a >=1.43x speedup is required; the observed ~2.8-3.1x
/// clears it by a wide margin, leaving headroom for slow/low-core CI.
const PMR_SPEEDUP_NUM: u128 = 7;
const PMR_SPEEDUP_DEN: u128 = 10;
/// Best-of-N attempt budget for the CPU-bound timing witnesses. The positive
/// test early-exits the moment the speedup is observed, so N is the WORST-case
/// attempt count, not the typical one. N=4 tolerates up to 3 contention-starved
/// attempts before the parallel run gets enough spare cores once. See the
/// BEST-OF-N HARDENING note in the section banner above for the rationale.
const PMR_ATTEMPTS: u32 = 4;

/// Wall-clock the divide-and-conquer Vec map-reduce under `--run`, with lenient
/// evaluation either ON (default) or OFF (`CRANELISP_NO_LENIENT=1`). Returns
/// (elapsed_ms, exit_code). Asserts a clean run (no panic / nonzero-from-error)
/// so a silent mis-run can't masquerade as a timing pass; the value-bearing exit
/// code is returned for the caller's same-result cross-check.
///
/// `src` is the full program text; `lenient_off` toggles the opt-out env var.
fn pmr_run_elapsed_ms(src: &str, lenient_off: bool) -> (u128, Option<i32>) {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src);
    if lenient_off {
        b = b.env("CRANELISP_NO_LENIENT", "1");
    }
    let out = b.output();
    // A clean run terminates via the exit code from `(defn main [] (Pure n))`;
    // a panic / compile failure would surface on stderr. Guard against the
    // latter so a crash can't read as a fast (and therefore "parallel") run.
    assert!(
        !out.stderr.to_lowercase().contains("panic")
            && !out.stderr.to_lowercase().contains("error"),
        "lenient_off={lenient_off}: expected a clean run, got stderr:\n{}\nstdout:\n{}",
        out.stderr,
        out.stdout
    );
    (out.elapsed.as_millis(), out.status.code())
}

// spec: spec/12-runtime.md §12.4.3 — independent same-block `let` bindings ARE
// sparked and run in parallel: a divide-and-conquer Vec map-reduce (`pmr` binds
// its two recursive halves to two sparkable same-block bindings `left`/`right`)
// runs MEANINGFULLY faster with lenient evaluation ON than with
// CRANELISP_NO_LENIENT=1, AND produces the SAME result (semantic transparency).
#[test]
fn lenient_vec_map_reduce_parallelizes() {
    // Divide-and-conquer: at an internal node, `left` and `right` are two
    // SAME-BLOCK `let` bindings, each an Apply to `pmr` (non-cheap, non-ctor)
    // whose free vars reference NO earlier binding in that block => both
    // sparkable => the halves run in parallel.
    let src = format!(
        "(import [primitives [Int add-i64 sub-i64 div-i64 le-i64 lt-i64 vec-get vec-len Pure]])\n\
         (defn fib [:Int n]\n\
           (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))\n\
         (defn pmr [v :Int lo :Int hi]\n\
           (if (le-i64 (sub-i64 hi lo) 1)\n\
               (fib (vec-get v lo))\n\
               (let [left  (pmr v lo (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))\n\
                     right (pmr v (add-i64 lo (div-i64 (sub-i64 hi lo) 2)) hi)]\n\
                 (add-i64 left right))))\n\
         (defn main []\n\
           (let [v [{PMR_VEC}]]\n\
             (Pure (div-i64 (pmr v 0 (vec-len v)) 1000000))))\n",
        PMR_VEC = PMR_VEC,
    );
    let _ = PMR_LEAF; // documents the per-leaf cost baked into PMR_VEC.

    // BEST-OF-N: the speedup must appear in AT LEAST ONE of N attempts. A
    // sequential impl would never qualify in ANY attempt (ON ~= OFF regardless of
    // contention), so one qualifying attempt genuinely proves parallelism. We
    // early-exit on the first qualifying attempt, so the common case runs once.
    // The semantic-transparency check runs on EVERY attempt and is never relaxed.
    let mut observed: Vec<(u128, u128, u128)> = Vec::new(); // (on_ms, off_ms, threshold)
    let mut parallel_witnessed = false;
    for attempt in 0..PMR_ATTEMPTS {
        let (on_ms, on_exit) = pmr_run_elapsed_ms(&src, false);
        let (off_ms, off_exit) = pmr_run_elapsed_ms(&src, true);

        // Semantic transparency: ON and OFF MUST compute the identical value.
        // Contention-immune — asserted on every attempt.
        assert_eq!(
            on_exit, off_exit,
            "attempt {attempt}: lenient ON vs OFF produced different results \
             (exit {on_exit:?} vs {off_exit:?}) — §12.4.3 requires lenient \
             evaluation to be semantically transparent"
        );

        let threshold = off_ms * PMR_SPEEDUP_NUM / PMR_SPEEDUP_DEN;
        observed.push((on_ms, off_ms, threshold));
        if on_ms < threshold {
            parallel_witnessed = true;
            break; // best-of-N satisfied — no need for further attempts.
        }
    }

    // Witness: the parallel (ON) run beat the serial (OFF) run by the conservative
    // margin (ON < 0.7 * OFF) in the BEST attempt. The probe measured ~2.8-3.1x in
    // isolation; the required >=1.43x leaves wide headroom. A failure here (across
    // ALL N attempts) means the two independent same-block bindings were NOT
    // sparked / not run in parallel — a sequential impl can never qualify.
    assert!(
        parallel_witnessed,
        "expected lenient-ON wall-clock < 0.7 * lenient-OFF in at least one of \
         {PMR_ATTEMPTS} attempts; none qualified — the divide-and-conquer Vec \
         map-reduce did not parallelise its two independent same-block `let` \
         bindings (§12.4.3). Attempts (on_ms, off_ms, threshold_ms): {observed:?}"
    );
}

// spec: spec/12-runtime.md §12.4.3 — NEGATIVE CONTROL pinning the sparkability
// rule. The SAME computation, but `mid` is bound FIRST in the SAME `let` block
// and BOTH halves reference it (an earlier same-block binding). A binding whose
// free vars reference an earlier same-block binding is NOT sparkable, so neither
// `left` nor `right` is sparked (<2 sparkable bindings) and the two halves run
// SERIALLY. Witness: lenient ON ~= OFF (no meaningful speedup) AND the same
// result. This proves the parallelism in `lenient_vec_map_reduce_parallelizes`
// comes from the sparkability rule, not incidentally.
#[test]
fn lenient_vec_map_reduce_prior_binding_stays_serial() {
    // `mid`, `left`, `right` share ONE `let` block; `left`/`right` both
    // reference the earlier same-block `mid` => not sparkable => serial.
    let src = format!(
        "(import [primitives [Int add-i64 sub-i64 div-i64 le-i64 lt-i64 vec-get vec-len Pure]])\n\
         (defn fib [:Int n]\n\
           (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))\n\
         (defn pmr [v :Int lo :Int hi]\n\
           (if (le-i64 (sub-i64 hi lo) 1)\n\
               (fib (vec-get v lo))\n\
               (let [mid   (add-i64 lo (div-i64 (sub-i64 hi lo) 2))\n\
                     left  (pmr v lo mid)\n\
                     right (pmr v mid hi)]\n\
                 (add-i64 left right))))\n\
         (defn main []\n\
           (let [v [{PMR_VEC}]]\n\
             (Pure (div-i64 (pmr v 0 (vec-len v)) 1000000))))\n",
        PMR_VEC = PMR_VEC,
    );

    // MAJORITY-OF-N: a genuinely serial case shows ON ~= OFF on every attempt, so
    // we require the MAJORITY of attempts to show NO speedup (ON >= 0.7*OFF). This
    // tolerates a single contention blip — an OFF-slow reading that spuriously
    // looks like a speedup — while still failing loudly if the prior-binding case
    // were wrongly sparked (which would show the speedup in all/most attempts).
    // Semantic transparency is asserted on EVERY attempt and never relaxed.
    let majority = PMR_ATTEMPTS / 2 + 1;
    let mut no_speedup_count = 0u32;
    let mut observed: Vec<(u128, u128, u128)> = Vec::new(); // (on_ms, off_ms, threshold)
    for attempt in 0..PMR_ATTEMPTS {
        let (on_ms, on_exit) = pmr_run_elapsed_ms(&src, false);
        let (off_ms, off_exit) = pmr_run_elapsed_ms(&src, true);

        // Same value with and without the opt-out (and the SAME value the positive
        // test computes — identical leaf cost / Vec, only the block shape differs).
        assert_eq!(
            on_exit, off_exit,
            "negative control attempt {attempt}: lenient ON vs OFF produced \
             different results (exit {on_exit:?} vs {off_exit:?}) — §12.4.3 \
             semantic transparency"
        );

        let parallel_threshold = off_ms * PMR_SPEEDUP_NUM / PMR_SPEEDUP_DEN;
        observed.push((on_ms, off_ms, parallel_threshold));
        if on_ms >= parallel_threshold {
            no_speedup_count += 1;
            // Early-exit: once a strict majority shows no speedup, the pass
            // outcome is locked in — no remaining attempt can change it. This
            // shaves the common-case runtime (the serial case reaches the
            // majority in the first `majority` attempts).
            if no_speedup_count >= majority {
                break;
            }
        }
    }

    // NO meaningful speedup in the MAJORITY of attempts: the inverse of the
    // positive assertion. If the prior-binding case were wrongly sparked, the
    // speedup (ON < 0.7*OFF) would appear in all/most attempts and the
    // no-speedup count would fall to the minority — failing this guard. Requiring
    // a strict majority (> N/2) tolerates one contention-induced false-speedup
    // reading without weakening the sparkability-rule proof.
    assert!(
        no_speedup_count >= majority,
        "negative control: expected NO meaningful speedup (lenient-ON \
         wall-clock >= 0.7 * lenient-OFF) in the majority ({majority} of \
         {PMR_ATTEMPTS}) of attempts; only {no_speedup_count} showed no speedup \
         — the prior-same-block-binding case is being wrongly parallelised; the \
         sparkability rule (free vars must not reference an earlier same-block \
         binding) is being violated (§12.4.3). Attempts (on_ms, off_ms, \
         threshold_ms): {observed:?}"
    );
}

// =============================================================================
// §12.5 Tail Call Optimization — Wave 5.6 dedupe-recovery carries
//
// FIXME 0141 (§12.5 SHOULD→MUST for self-recursive TCO) ratified by /spec
// and landed in the tree (Sprint 81). The implementation has shipped
// structural loop-based self-TCO since S22 (per `memory/macros.md
// §"Tail Call Optimization (TCO)"`), so these assertions pass against the
// current binary, and §12.5 is now normatively MUST — so they are
// un-ignored. Citations resolve through the linter.
// =============================================================================

// spec: spec/12-runtime.md §12.5 — self-recursive tail calls optimised; deep
// countdown completes without stack overflow.
// (carry: legacy/ring0.rs::tco_deep_countdown)
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

// spec: spec/12-runtime.md §12.6 — `(defn main [] (Pure Int))` exits with the
// inner Int. A batch main returns `IO _`; the exit code is the inner Int.
// (carry: legacy/v4_pipeline.rs::test_v4_integer_literal)
#[test]
fn main_returning_int_produces_int_exit_code() {
    Cranelisp::new()
        .user("(import [primitives [Pure]])\n(defn main [] (Pure 42))")
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/12-runtime.md §12.6 — non-Int IO main result → exit 0. The main
// returns `IO Bool` (`(Pure true)`); a non-Int inner value maps to exit 0.
// (carry: legacy/v4_pipeline.rs::test_v4_boolean_literal)
#[test]
fn main_returning_non_int_produces_zero_exit_code() {
    Cranelisp::new()
        .user("(import [primitives [Pure]])\n(defn main [] (Pure true))")
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
        .user("(import [primitives [Pure]])\n(defn main [] (Pure (primitives/add-i64 1 2)))")
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
            "(import [primitives [Pure]])\n\
             (defn double [x] (primitives/add-i64 x x))\n\
             (defn main [] (Pure (double 5)))",
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
            "(import [primitives [Pure]])\n\
             (defn fact [n]\n\
               (if (primitives/eq-i64 n 0)\n\
                 1\n\
                 (primitives/mul-i64 n (fact (primitives/sub-i64 n 1)))))\n\
             (defn main [] (Pure (fact 5)))",
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
        .user("(import [primitives [Pure]])\n(defn main [] (Pure (primitives/add-i64 10 20)))")
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

// =============================================================================
// §12.3.3 Vec copy-on-write — heap-ADT element RC corrupted through a
//         user-defined `vec-push` wrapper — DEFECT DEF-2 (S86)
// =============================================================================
//
// DEF-2 — a user-defined wrapper `(defn push2 [v x] (vec-push v x))` corrupts
// the refcount of a HEAP-ADT element when accumulated in a loop. Calling the
// primitive `vec-push` DIRECTLY does not. The corruption is observable as a
// WRONG derived value: summing the unboxed elements of the wrapper-built
// `(Vec Box)` over-counts versus the direct-built vec (and versus the true sum).
//
// §12.3.3 promises Vec COW is "semantically invisible — the caller observes
// pure functional behavior regardless." DEF-2 violates that: routing `vec-push`
// through a one-line wrapper makes COW NOT semantically invisible for heap-ADT
// elements.
//
// ISOLATION (this session, /qa S86 step 1.5a):
//   - Divergence appears at N=2 already: wrapper-built sum = 2, direct-built
//     sum = 1 (true sum 0+1 = 1). The wrapper path consistently OVER-counts.
//   - Int (scalar) elements are UNAFFECTED: the same wrapper over a `(Vec Int)`
//     yields the correct sum (the Int-control test below). Only heap-allocated
//     ADT elements corrupt — pinning the defect to RC handling of a heap arg
//     passed through the wrapper call boundary, not to the wrapper or COW per se.
//   - CRANELISP_RC_TRACE=1 on the N=2 wrapper path shows an asymmetric
//     alloc/free sequence vs the direct path: the direct path allocs 5 / frees
//     cleanly with a COW reuse at refcount=1; the wrapper path frees-then-
//     re-allocs a backing store and leaves one Box object without the matching
//     RC bookkeeping — i.e. the wrapper call boundary drops an RC inc (or makes
//     the COW single-owner decision against a stale refcount). The over-count
//     is the corrupted vec reading a stale/aliased element.
//
// TRUE OWNER: /backend (RC mis-count at the wrapper call boundary — the heap
// arg passed into the user-defined wrapper is not inc'd the way the direct
// primitive-call codegen inc's it, so the COW single-owner test fires
// incorrectly). FIXME(/backend). Inspect the arg-passing RC inc/dec symmetry
// at a `defn` call that forwards a heap ADT to a vec primitive.
//
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md: asserts the
// CORRECT behaviour (the wrapper-built sum equals the true sum, exit 1 at N=2),
// RED today (wrapper over-counts to exit 2), GREEN when the RC asymmetry closes.

// Builds a `(Vec Box)` of N boxed indices via `bw` (which forwards each `(Box i)`
// through the given push function), then sums the unboxed elements. `$BUILDER` is
// either `push2` (the wrapper) or `vec-push` (direct). True sum for N=2 is 1.
const DEF2_BOX_VEC_TEMPLATE: &str = "\
(import [primitives [*]])
(deftype Box [:Int v])
(defn unbox [b] (match b [(Box v) v]))
(defn push2 [v x] (vec-push v x))
(defn bw [v i n] (if (lt-i64 i n) (bw ($BUILDER v (Box i)) (add-i64 i 1) n) v))
(defn sv [v i n acc] (if (lt-i64 i n) (sv v (add-i64 i 1) n (add-i64 acc (unbox (vec-get v i)))) acc))
(defn main [] (Pure (sv (bw [] 0 2) 0 2 0)))
";

// spec: spec/12-runtime.md §12.3.3 — Vec COW is semantically invisible; routing
// `vec-push` through a user-defined wrapper MUST yield the same result as the
// direct primitive. DEF-2: the wrapper over-counts heap-ADT elements (exit 2,
// should be 1) — the heap element's RC is corrupted at the wrapper call boundary.
#[test]
fn def2_vec_push_wrapper_preserves_heap_adt_element_rc() {
    // WRAPPER path: each `(Box i)` is appended via `push2` (wraps `vec-push`).
    // True sum 0+1 = 1 ⇒ exit 1 when GREEN; today over-counts to exit 2.
    let src = DEF2_BOX_VEC_TEMPLATE.replace("$BUILDER", "push2");
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .user(&src)
        .run("user.cl")
        .output()
        .assert_exit(1);
}

// spec: spec/12-runtime.md §12.3.3 — CONTROL: the DIRECT `vec-push` path yields
// the correct sum (exit 1). Pins that the user-defined wrapper — not the loop,
// the ADT, or COW itself — is the DEF-2 trigger. GREEN today.
#[test]
fn def2_vec_push_direct_heap_adt_element_correct_control() {
    let src = DEF2_BOX_VEC_TEMPLATE.replace("$BUILDER", "vec-push");
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .user(&src)
        .run("user.cl")
        .output()
        .assert_exit(1);
}

// spec: spec/12-runtime.md §12.3.3 — CONTROL: the SAME wrapper over `(Vec Int)`
// (scalar elements) yields the correct sum (exit 1). Pins that only HEAP-ADT
// elements corrupt through the wrapper — scalars are unaffected. GREEN today.
#[test]
fn def2_vec_push_wrapper_scalar_element_unaffected_control() {
    // Int elements, wrapper path, N=2. True sum 0+1 = 1 ⇒ exit 1.
    let src = "\
(import [primitives [*]])
(defn push2 [v x] (vec-push v x))
(defn bw [v i n] (if (lt-i64 i n) (bw (push2 v i) (add-i64 i 1) n) v))
(defn sv [v i n acc] (if (lt-i64 i n) (sv v (add-i64 i 1) n (add-i64 acc (vec-get v i))) acc))
(defn main [] (Pure (sv (bw [] 0 2) 0 2 0)))
";
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .user(src)
        .run("user.cl")
        .output()
        .assert_exit(1);
}

// =============================================================================
// §12.3.3 Vec copy-on-write — TEMPORARY heap-ADT element RC LEAK through
//         `vec-set` — DEFECT DEF-3 (S86), the opposite-direction mirror of DEF-2
// =============================================================================
//
// DEF-3 — `vec-set`'s inline copy-on-write path (and the `vec_set_copy` runtime
// helper) inc the NEW element UNCONDITIONALLY. That is correct only for a Var
// element that stays live (two owners ⇒ inc needed). For a TEMPORARY heap
// element — `(vec-set v i (Box 7))` — the temporary arrives at rc=1 and its sole
// reference must TRANSFER into the Vec (no inc), per the uniform consuming
// convention (Decision 24). The unconditional inc gives the element a permanent
// extra reference the Vec never drops, so the heap object LEAKS.
//
// This is the OPPOSITE-DIRECTION mirror of DEF-2: DEF-2 UNDER-counted a Var
// forwarded through a `vec-push` wrapper; DEF-3 OVER-counts a temporary handed
// straight to `vec-set`. The fix (next step, /backend) aligns `vec-set` to the
// same consuming-Var rule that DEF-2 aligns `vec-push` to — Var→inc,
// temp→transfer (ring2-rc.md §"Decision 24" / "Algorithm" steps 1–2).
//
// ISOLATION (this session, /qa S86):
//   - A single `vec-set` with a TEMPORARY heap element allocs 5, frees 4 —
//     one heap object leaks. The leaked object is the temporary new element
//     (rc bumped to 2 by the unconditional inc, only ever dec'd once).
//   - SCALAR (Int) elements are UNAFFECTED: `vec-set` over a `(Vec Int)` is
//     alloc/free balanced (no heap element to inc) — the scalar control below.
//   - The leak scales with repeated vec-sets (an N=3 loop leaks 9), confirming
//     the per-call extra reference, but a single call is the minimal pin.
//
// OBSERVABILITY LIMITATION (why this parses RC_TRACE rather than asserting exit
// code, unlike DEF-2): a pure leak does NOT corrupt the read-back value — the
// element is still the correct `(Box 7)`, the program exits 0 with the right
// answer. There is no value-level or exit-code witness; the ONLY observable is
// the allocation imbalance. So — as the S86 brief anticipated for the
// allocation-imbalance case, and exceptionally vs. the file-header note that
// counter-parsing migrates to legacy — this repro parses the
// `CRANELISP_RC_TRACE=1` stderr alloc/free counters directly. The scalar
// control pins that the imbalance is specific to a TEMPORARY HEAP element.
//
// TRUE OWNER: /backend (RC inc on the new `vec-set` element — inline COW codegen
// + the `vec_set_copy` runtime helper — must follow the Var/temp distinction,
// not inc unconditionally). FIXME(/backend). Mirror the DEF-2 vec-push fix.
//
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md: asserts the
// CORRECT behaviour (alloc count == free count for the temporary-element case),
// RED today (5 allocs / 4 frees ⇒ leak), GREEN when the unconditional inc is
// gated to the live-Var case.

// Count `[RC] alloc` / `[RC]  free` lines in the RC trace stderr. The trace
// formats these as `[RC] alloc 0x…` and `[RC]  free 0x…` (note the alignment
// space before `free`), so match on the bare `alloc`/`free` event token, scoped
// to RC lines, and exclude `dec`/`inc` events.
fn rc_alloc_free_counts(stderr: &str) -> (usize, usize) {
    let allocs = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" alloc "))
        .count();
    let frees = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" free "))
        .count();
    (allocs, frees)
}

// spec: spec/12-runtime.md §12.3.3 — Vec COW is semantically invisible; a
// `vec-set` with a TEMPORARY heap element must transfer the temporary's sole
// reference into the Vec (consuming convention, ring2-rc.md Decision 24), NOT
// inc it. DEF-3: the unconditional inc leaks the temporary heap element
// (5 allocs / 4 frees today; must be balanced when GREEN).
#[test]
fn def3_vec_set_temporary_heap_element_rc_balanced() {
    let src = "\
(import [primitives [*]])
(deftype Box [:Int v])
(defn unbox [b] (match b [(Box v) v]))
(defn main [] (Pure (unbox (vec-get (vec-set [(Box 0) (Box 0)] 1 (Box 7)) 1))))
";
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .env("CRANELISP_RC_TRACE", "1")
        .user(src)
        .run("user.cl")
        .output();
    // Value/exit are correct even under the leak (the observability limitation):
    // the read-back element is the right `(Box 7)`, exit 0. The only witness is
    // the allocation balance.
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert_eq!(
        allocs, frees,
        "vec-set of a TEMPORARY heap element must be alloc/free balanced \
         (consuming-temp transfer, no unconditional inc); got {allocs} allocs / \
         {frees} frees — DEF-3 leak.\nstderr:\n{}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.3.3 — CONTROL: `vec-set` over a `(Vec Int)`
// (scalar element, no heap object to inc) is alloc/free balanced. Pins that the
// DEF-3 leak is specific to a TEMPORARY HEAP element, not to `vec-set` per se.
// GREEN today.
#[test]
fn def3_vec_set_scalar_element_rc_balanced_control() {
    let src = "\
(import [primitives [*]])
(defn main [] (Pure (vec-get (vec-set [10 20] 1 99) 1)))
";
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .env("CRANELISP_RC_TRACE", "1")
        .user(src)
        .run("user.cl")
        .output();
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert_eq!(
        allocs, frees,
        "vec-set of a SCALAR element must be alloc/free balanced; \
         got {allocs} allocs / {frees} frees.\nstderr:\n{}",
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.3.3 — CONTROL: a literal `(Vec Box)` read WITHOUT
// any `vec-set` is alloc/free balanced (4/4). Pins that the heap-element machinery
// itself is sound — the leak is introduced specifically by `vec-set`'s
// unconditional new-element inc, not by constructing or reading a heap-element
// Vec. GREEN today.
#[test]
fn def3_heap_element_vec_no_vecset_rc_balanced_control() {
    let src = "\
(import [primitives [*]])
(deftype Box [:Int v])
(defn unbox [b] (match b [(Box v) v]))
(defn main [] (Pure (unbox (vec-get [(Box 5) (Box 7)] 1))))
";
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .env("CRANELISP_RC_TRACE", "1")
        .user(src)
        .run("user.cl")
        .output();
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert_eq!(
        allocs, frees,
        "literal (Vec Box) read with no vec-set must be alloc/free balanced; \
         got {allocs} allocs / {frees} frees.\nstderr:\n{}",
        out.stderr
    );
}

// =============================================================================
// §12.4.2 — Lazy Sequences (thunks / zero-arg closures)
// =============================================================================
//
// `Seq` is NOT a compiler-seeded type — §12.4.2 specifies that laziness is
// "explicit and user-controlled … through thunks (zero-argument closures)",
// NOT a property of the evaluation model. So these tests build a lazy stream
// free-standing: an ADT cell `(SCons head tail-thunk)` whose tail is a
// `(Fn [] Stream)` thunk that is only invoked (`(tf)`) on demand. The exit
// code carries the witnessed Int (per `(defn main [] (Pure N))` → exit N).

// A free-standing lazy stream over Int: SCons holds a head and a tail THUNK
// (zero-arg closure). `from` is infinite — each `(tf)` lazily produces the next
// cell. `take-nth k` forces exactly k tail thunks.
const LAZY_STREAM_PROGRAM: &str = "\
(import [primitives [*]])
(deftype Stream (SNil) (SCons [:Int h :(Fn [] Stream) tailf]))
(defn from [n] (SCons n (fn [] (from (add-i64 n 1)))))
(defn take-nth [k s]
  (match s [(SNil) 0
            (SCons h tf) (if (eq-i64 k 0) h (take-nth (sub-i64 k 1) (tf)))]))
(defn main [] (Pure (take-nth 5 (from 37))))
";

// spec: spec/12-runtime.md §12.4.2 — take-from-infinite: a lazy stream `(from
// 37)` is conceptually infinite, yet `(take-nth 5 …)` forces exactly five tail
// thunks and terminates with the 5th element (37+5 = 42). If the tail were eager
// rather than a thunk, constructing `(from 37)` would loop forever and the
// program would never reach `main`. Exit 42 witnesses both: laziness works AND
// the demanded element is correct.
#[test]
fn lazy_stream_take_from_infinite_terminates_with_demanded_element() {
    Cranelisp::new()
        .file("user.cl", LAZY_STREAM_PROGRAM)
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/12-runtime.md §12.4.2 — construction-does-not-force-tail: merely
// CONSTRUCTING an infinite lazy stream and reading ONLY its head (never forcing
// the tail thunk) must terminate. `(SCons n tail-thunk)` does not evaluate
// `tail-thunk`; pattern-matching the head out without calling `(tf)` leaves the
// infinite tail unforced. Exit 37 (the head of `(from 37)`) witnesses that
// construction is non-strict in the tail.
#[test]
fn lazy_stream_construction_does_not_force_tail() {
    let src = "\
(import [primitives [*]])
(deftype Stream (SNil) (SCons [:Int h :(Fn [] Stream) tailf]))
(defn from [n] (SCons n (fn [] (from (add-i64 n 1)))))
(defn head [s] (match s [(SNil) 0 (SCons h tf) h]))
(defn main [] (Pure (head (from 37))))
";
    Cranelisp::new()
        .file("user.cl", src)
        .run("user.cl")
        .output()
        .assert_exit(37);
}

// =============================================================================
// §12.3.3 Vec Copy-on-Write — heap-element Vec RC under borrowed-source copy
// (DEF-2 / T2 family: vec-push/vec-set consuming-inc on heap elements)
// =============================================================================

// spec: spec/12-runtime.md §12.3.3 — `vec-push` returns a NEW Vec; the original
// Vec and its heap (String) elements remain valid and re-readable. spec §12.1.5
// — each heap element is reference-counted and freed with the Vec, not before.
//
// DEFECT (DEF-2 / T2 family — heap-element-vec RC; surfaced verifying the S87
// `conj` curated verb and the audit's B2/B17 claims). When a Vec with HEAP
// (String) elements is a BORROWED recursive parameter, re-passed unchanged to
// the recursive call, and each iteration `vec-push`-copies it AND reads back
// from the copy, the per-element consuming-inc on the heap element is
// mismatched: the original String's refcount is decremented by the copy path
// without a compensating inc, so by the SECOND iteration the still-live
// original element is freed → use-after-free → SIGSEGV (exit 139).
//
// ISOLATION (this session):
//   - Crashes deterministically 10/10 at recursion DEPTH 2 (n=2) in BOTH REPL
//     and `--run`. Depth 0/1 pass.
//   - The SAME loop with INT elements (no per-element heap RC) does NOT
//     use-after-free — the trigger is the HEAP element, not the loop shape.
//   - A single non-recursive `vec-push` reading both original and copy passes;
//     the corruption needs the borrowed-source re-read on a SUBSEQUENT
//     iteration after a prior copy decremented the element.
//   - The simple threaded-accumulator `conj`/`vec-push` stress (build a vec by
//     threading the result) does NOT crash — so plain `conj` is NOT corrupt;
//     this borrowed-recursive shape is the live face of the DEF-2/B17 family.
//
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md — RED today
// (SIGSEGV), GREEN when the heap-element consuming-inc balances on the
// vec-push/vec-set copy path. When GREEN: 2 iterations × str-len "aaa" = 6.
// → /backend (vec heap-element consuming-inc symmetry; audit B2/T2,
// `vec_codegen.rs` / `vec_runtime.rs` `vec_set_copy`/`vec_push_copy`).
#[test]
fn vec_push_heap_element_borrowed_recursive_source_no_uaf() {
    repl_prims(
        "(defn loop [v n acc] \
           (if (le-i64 n 0) acc \
             (loop v (sub-i64 n 1) \
               (add-i64 acc (str-len (vec-get (vec-push v \"z\") 0))))))\n\
         (loop [\"aaa\"] 2 0)\n",
    )
    .assert_stdout_contains(":primitives/Int 6");
}

// spec: spec/12-runtime.md §12.3.3 / §12.1.5 — same DEF-2/T2 heap-element-vec
// RC defect, observed END-TO-END through `--run` (the unit-tier face above is
// REPL). A mode-crossing guard: the use-after-free aborts the process, so the
// `--run` exit code is the witness — exit 6 when GREEN, SIGSEGV (139) today.
// Mode parity matters because `--run` (JIT) and the REPL share the codegen but
// the e2e path proves the corruption is not a REPL-session artifact.
// → /backend (same fix as the unit-tier repro above).
#[test]
fn vec_push_heap_element_borrowed_recursive_source_no_uaf_run() {
    Cranelisp::new()
        .file(
            "user.cl",
            "(import [primitives [vec-push vec-get str-len add-i64 sub-i64 le-i64 Pure]])\n\
             (defn loop [v n acc] \
               (if (le-i64 n 0) acc \
                 (loop v (sub-i64 n 1) \
                   (add-i64 acc (str-len (vec-get (vec-push v \"z\") 0))))))\n\
             (defn main [] (Pure (loop [\"aaa\"] 2 0)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(6);
}
