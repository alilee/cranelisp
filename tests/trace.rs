// trace.rs — `(trace ...)` execution-trace surface (Sprint 76 Wave 3).
//
// The active e2e home for the `(trace ...)` feature. Supersedes the
// quarantined `tests/legacy/ring4_trace.rs` (Rust-API observations) and
// the scattered trace cases formerly in `tests/spec_12_runtime.rs`.
//
// Covers, per FIXME 0258 (+ gate addenda NOTE-1/NOTE-2/NOTE-4) and
// FIXME 0276:
//   - §4.12.5 Nested trace runtime error (lexical + dynamic).
//   - §4.12.9 Build-mode availability — linked-binary trace runs.
//   - §4.12.3 What-is-traced — swap-all visibility (+Neg: inline
//     arithmetic + anonymous lambdas absent).
//   - NOTE-1 — polymorphic-ADT param/result rendering round-trip.
//   - NOTE-2 — panic-unwind stuck-guard (FAILING; resolver S77 / FIXME 0270).
//   - FIXME 0276 — `--link` accessor unresolved + session park.
//
// Several tests here land FAILING against current behaviour and serve as
// the durable target + regression guard (per
// `memory/feedback_failing_not_ignored.md` +
// `memory/feedback_repros_join_suite.md`). Each such test names its
// resolver via `// FIXME(/skill)`.
//
// Mode note (FIXME 0280 RESOLVED, FIXME 0286): the primitives-GOT
// static-backing fix landed in Sprint 76 Wave 3 — the primitives group is now
// swapped in object mode, so extern primitives appear as trace-tree children in
// `--link` binaries exactly as they do in REPL / `--run`. The linked-binary
// tests here assert WITH extern-primitive children (flipped from the 0280
// interim WITHOUT-children disposition). The link-mode mirror of the
// extern-primitive child assertion lives in
// tests/link.rs::link_traced_extern_primitives_appear_as_children_exit_42.

#[path = "helpers/mod.rs"]
mod helpers;

use std::time::Duration;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// Helpers
// =============================================================================

/// Pipe `lines` to a fresh REPL with the `PrimitivesOnly` prelude variant.
fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::repl_prims_capture(lines)
}

/// A prelude that re-exports primitives and adds ONE plain helper fn. Used to
/// witness that a prelude-defined (stdlib-fixture-style) function appears as a
/// child in a trace tree, WITHOUT pulling in the trait-heavy `TestStandard`
/// prelude (which currently overflows the trace formatter — see
/// `trace_neg_trait_heavy_prelude_overflows_DEFECT`).
const PRELUDE_ONE_HELPER: &str = "(export [primitives [*]])\n\
     (defn helper [x] (add-i64 x 100))\n";

// =============================================================================
// §4.12.5 — Nested trace is a runtime error
// =============================================================================

// spec: spec/04-expressions.md §4.12.5 — dynamic nested trace raises a runtime
// error. `(trace (g ...))` where g's body reaches an inner `(trace ...)` after
// an instrumented call has fired must raise "nested trace is not supported".
// This is the case the Wave-1.5 guard handles: the outer trace's first wrapper
// raises TRACE_BODY_RUNNING before the inner form's swap_got runs. PASSES.
#[test]
fn trace_nested_dynamic_raises_runtime_error() {
    repl_prims(
        "(defn id [x] x)\n\
         (defn h [x] (id x))\n\
         (defn g [x] (let [a (h x)] (trace (id a))))\n\
         (trace (g 5))\n",
    )
    .assert_stdout_contains("nested trace is not supported");
}

// spec: spec/04-expressions.md §4.12.5 — lexical `(trace (trace expr))` MUST
// raise a runtime error. The spec is explicit: the inner `(trace ...)` raises
// "rather than producing a nested or merged trace tree", whether lexical OR
// dynamic. The nested-trace guard now catches the pure-lexical case (resolved
// S81; the prior lexical re-entrancy escape was fixed).
#[test]
fn trace_nested_lexical_raises_runtime_error() {
    repl_prims(
        "(defn id [x] x)\n\
         (trace (trace (id 7)))\n",
    )
    .assert_stdout_contains("nested trace is not supported");
}

// spec: spec/04-expressions.md §4.12.5 — (same anchor) NOTE-2 panic-unwind
// stuck guard. The gate review (0258 NOTE-2) flagged a worry: if a JIT body
// panics mid-trace while TRACE_BODY_RUNNING is set (after an instrumented inner
// call has raised the flag), the thread-local flag + trace role could stay
// stuck with no RAII cleanup, so a later same-thread `(trace (ok-fn))` would
// spuriously raise "nested trace".
//
// VERDICT (S76 W3 /qa probe): the worry does NOT reproduce at the e2e level in
// REPL mode. Probed BOTH the simple shape (`(trace (boom))` where boom panics
// directly) AND the precise NOTE-2 shape (`g` calls an instrumented `inner`,
// raising the flag, then panics mid-trace): in every case the subsequent
// `(trace (ok 1))` runs cleanly and produces a Trace value — the REPL's
// per-form panic recovery resets the thread-local state. This test therefore
// PASSES and is a positive regression guard that the flag/role do not stick
// across a panicking trace. (If a future change reintroduces the stuck guard
// it will fail here, naming /dev intrinsics + FIXME 0270.)
#[test]
fn trace_panic_unwind_does_not_stick_guard() {
    // Precise NOTE-2 shape: g calls an instrumented inner fn (raising
    // TRACE_BODY_RUNNING) and THEN panics mid-trace.
    let out = repl_prims(
        "(defn inner [x] (add-i64 x 1))\n\
         (defn g [x] (let [a (inner x)] (div-i64 a 0)))\n\
         (defn ok [x] x)\n\
         (trace (g 1))\n\
         (trace (ok 1))\n",
    );
    // The second trace must run cleanly: a Trace value, not a nested-trace
    // error left over from the panicked first trace.
    assert!(
        out.stdout.contains(":primitives/Trace")
            && !out.stdout.contains("nested trace is not supported"),
        "second trace after a panicking trace should run cleanly; \
         stdout=\n{}",
        out.stdout
    );
}

// =============================================================================
// §4.12.9 — Build-mode availability: linked-binary trace runs
// =============================================================================

// spec: spec/04-expressions.md §4.12.9 — a `(trace ...)` form in a `--link`
// standalone binary resolves and runs (no "undefined symbol
// cranelisp_collect_trace" link failure, no SIGBUS from baked compiling-process
// addresses — FIXME 0275 object-mode relocations landed Wave 3). The
// match-consumption shape (0275 acceptance) consumes the Trace ADT to an Int
// and the produced binary exits 42.
//
// FIXME 0286 FLIP: with FIXME 0280 (primitives-GOT static-backing) landed, the
// primitives group is now swapped in object mode, so extern primitives appear
// as children in `--link` trace trees — the same as REPL / `--run`. This test
// now asserts WITH extern-primitive children (flipped from the 0280 interim
// WITHOUT-children disposition): the traced `work` body calls `str-len` over a
// `str-concat`, both extern primitives, so the `user/work` node has exactly TWO
// children. main descends to work (the root's only child) and counts work's
// extern-primitive children (2), returning count+40 == 42.
#[test]
fn trace_linked_binary_match_consumption_runs() {
    let src = "(import [primitives [trace Trace TraceCall str-concat str-len Pure]])\n\
         (import [macros [SCons SNil]])\n\
         (defn work [s] (str-len (str-concat \"x\" s)))\n\
         (defn slen [acc xs]\n\
           (match xs [SNil acc (SCons h t) (slen (add-i64 acc 1) t)]))\n\
         (defn main []\n\
           (Pure (match (trace (work \"ab\"))\n\
             [(TraceCall n p r c ns)\n\
               (match c [SNil 0\n\
                         (SCons h t)\n\
                           (match h [(TraceCall n2 p2 r2 c2 ns2)\n\
                                     (add-i64 (slen 0 c2) 40)])])])))\n";
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("prog.cl", src)
        .link_then_run("prog.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// §4.12.3 — What is traced: swap-all visibility
// =============================================================================

// spec: spec/04-expressions.md §4.12.3 — extern primitives in the synthetic
// `primitives` module appear as trace-tree nodes when called from a traced
// body (discovery swaps ALL symbol tables, incl. primitives, in REPL/`--run`).
// `(trace (greet "bob"))` → root `::trace::` with child `user/greet`, whose own
// first child is `primitives/str-concat`. PASSES (REPL mode).
#[test]
fn trace_extern_primitive_appears_as_child() {
    repl_prims(
        "(import [primitives [trace Trace TraceCall str-concat]])\n\
         (import [macros [SCons SNil]])\n\
         (defn greet [s] (str-concat \"hi \" s))\n\
         (defn fst-grandchild [c]\n\
           (match c [SNil \"<none>\"\n\
                     (SCons h t)\n\
                       (match h [(TraceCall n p r cc ns)\n\
                                 (match cc [SNil \"<none>\"\n\
                                            (SCons h2 t2)\n\
                                              (match h2 [(TraceCall n2 p2 r2 cc2 ns2) n2])])])]))\n\
         (match (trace (greet \"bob\")) [(TraceCall n p r c ns) (fst-grandchild c)])\n",
    )
    .assert_stdout_contains("primitives/str-concat");
}

// spec: spec/04-expressions.md §4.12.3 — a prelude-defined (stdlib-fixture
// style) function appears as a trace-tree node when called from a traced body.
// `(trace (f 5))` where `f` calls `prelude/helper` → root child `user/f` whose
// own child is `prelude/helper`. PASSES.
#[test]
fn trace_stdlib_fixture_fn_appears_as_child() {
    Cranelisp::new()
        .prelude(PRELUDE_ONE_HELPER)
        .repl()
        .stdin(
            "(import [primitives [trace Trace TraceCall]])\n\
             (import [macros [SCons SNil]])\n\
             (defn f [x] (helper x))\n\
             (defn fst-grandchild [c]\n\
               (match c [SNil \"<none>\"\n\
                         (SCons h t)\n\
                           (match h [(TraceCall n p r cc ns)\n\
                                     (match cc [SNil \"<none>\"\n\
                                                (SCons h2 t2)\n\
                                                  (match h2 [(TraceCall n2 p2 r2 cc2 ns2) n2])])])]))\n\
             (match (trace (f 5)) [(TraceCall n p r c ns) (fst-grandchild c)])\n",
        )
        .output()
        .assert_stdout_contains("prelude/helper");
}

// spec: spec/04-expressions.md §4.12.3 — NEGATIVE: inline-CLIF arithmetic
// (add-i64) has no callable entry point and is structurally invisible. The
// traced body `(add3 x)` (which uses inline `add-i64`) appears as a child of
// the root, but `add3` itself has ZERO children — `add-i64` does not appear.
#[test]
fn trace_neg_inline_arithmetic_not_traced() {
    repl_prims(
        "(import [primitives [trace Trace TraceCall]])\n\
         (import [macros [SCons SNil]])\n\
         (defn cnt [acc xs]\n\
           (match xs [SNil acc (SCons h t) (cnt (add-i64 acc 1) t)]))\n\
         (defn gcnt [c]\n\
           (match c [SNil 99\n\
                     (SCons h t) (match h [(TraceCall n p r cc ns) (cnt 0 cc)])]))\n\
         (defn add3 [x] (add-i64 x 3))\n\
         (match (trace (add3 5)) [(TraceCall n p r c ns) (gcnt c)])\n",
    )
    // add3 is a child of root (so gcnt descends into it); add3's own child
    // count is 0 — inline add-i64 produced no node.
    .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/04-expressions.md §4.12.3 — NEGATIVE: anonymous lambdas have no
// named indirection-table entry and are not individually traced. A traced body
// `(useslam x)` that applies a local `(fn [y] ...)` has ZERO children — the
// lambda does not appear as a named node.
#[test]
fn trace_neg_anonymous_lambda_not_traced() {
    repl_prims(
        "(import [primitives [trace Trace TraceCall]])\n\
         (import [macros [SCons SNil]])\n\
         (defn cnt [acc xs]\n\
           (match xs [SNil acc (SCons h t) (cnt (add-i64 acc 1) t)]))\n\
         (defn gcnt [c]\n\
           (match c [SNil 99\n\
                     (SCons h t) (match h [(TraceCall n p r cc ns) (cnt 0 cc)])]))\n\
         (defn useslam [x] (let [f (fn [y] (add-i64 y 1))] (f x)))\n\
         (match (trace (useslam 5)) [(TraceCall n p r c ns) (gcnt c)])\n",
    )
    .assert_stdout_contains(":primitives/Int 0");
}

// =============================================================================
// NOTE-1 — polymorphic-ADT param/result rendering round-trip
// =============================================================================

// spec: spec/04-expressions.md §4.12.3 — (same anchor) NOTE-1: a traced fn
// returning a polymorphic ADT at a concrete instantiation ((Option Int)) must
// render its result string via the production codegen-baked DisplayDescriptor.
// This closes the production-baker round-trip gap (the descriptor round-trip
// unit tests hand-mirror bake_adt; this is the only e2e exercise of the real
// bake_descriptor/bake_adt ctor-table assembly + concrete-type substitution).
// The prior ADT-render stack-overflow in the descriptor formatter was resolved
// S81 (FIXME 0258); tracing a fn returning a user ADT value now renders cleanly.
#[test]
fn trace_polymorphic_adt_result_renders() {
    let out = repl_prims(
        "(import [primitives [trace Trace TraceCall]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (defn wrap [x] (Some x))\n\
         (match (trace (wrap 7)) [(TraceCall n p r c ns) r])\n",
    );
    // The matched `r` is the rendered result string for the traced `(wrap 7)`
    // call. On success the REPL prints a `:primitives/String "...Some..."`
    // result line. The match-arm HINT line (`; None Some`) also contains
    // "Some", so we must require BOTH the String result type prefix AND a
    // "Some" rendering — and assert the process did NOT abort.
    assert!(
        !out.stderr.contains("overflowed its stack"),
        "tracing a fn returning (Option Int) overflowed the descriptor \
         formatter; stderr=\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains(":primitives/String") && out.stdout.contains("Some"),
        "the (Some 7) result should render as a String trace-result value; \
         stdout=\n{}",
        out.stdout
    );
}

// spec: spec/04-expressions.md §4.12.3 — (same anchor) the minimal witness for
// the ADT-render overflow: tracing a fn that returns a NULLARY constructor
// (None). This is the 1-constructor reduction of
// `trace_polymorphic_adt_result_renders`. Resolved S81 (FIXME 0258); the nullary
// value now renders without overflowing the descriptor formatter.
#[test]
fn trace_adt_value_render_overflows_defect() {
    repl_prims(
        "(import [primitives [trace Trace TraceCall]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (defn mk [] None)\n\
         (match (trace (mk)) [(TraceCall n p r c ns) r])\n",
    )
    // Once the overflow is fixed, the result renders the nullary value. The
    // assertion is "ran to a result without aborting" — a stack overflow leaves
    // stdout without the matched result line.
    .assert_stdout_contains(":primitives/String");
}

// spec: spec/04-expressions.md §4.12.3 — (same anchor) trait-heavy prelude
// overflow witness. With the trait-bearing `TestStandard` prelude loaded,
// `(trace (f 5))` — even for an `f` that uses only inline `add-i64` — formerly
// stack-overflowed on a worker thread with the full trait-bearing prelude
// loaded (4 traits, ~14 impls); a single trait+impl or Num+Eq+Ord without
// Display did not. The overflow fired on a `nice-worker` rayon thread, in the
// interaction of trace swap-all discovery with lenient-eval sparks over a large
// multi-module symbol set. Resolved S81 (FIXME 0258); trace swap-all over the
// trait-heavy prelude now scales without overflowing.
#[test]
fn trace_trait_heavy_prelude_overflows_defect() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .repl()
        .stdin(
            "(import [primitives [trace Trace TraceCall]])\n\
             (defn f [x] (add-i64 x 1))\n\
             (trace (f 5))\n",
        )
        .output()
        // A clean run prints the Trace result; an overflow aborts before it.
        .assert_stdout_contains(":primitives/Trace");
}

// =============================================================================
// §4.12.4 / NOTE-1 lineage — generated field accessors (FIXME 0276 defect 1)
// =============================================================================

// spec: spec/04-expressions.md §4.12.4 — the TraceCall field accessors
// (name, params, result, children, nanos) are generated per §5.2.6 and
// resolve in ALL JIT modes. `(nanos (trace (work 41)))` returns an Int.
//
// POSITIVE regression guard (FIXME 0292 backend half DONE + verified): the
// bare accessor name `nanos` resolves to the `cranelisp_trace_nanos` intrinsic
// at the call site and consumes the Trace tree, yielding the wall-clock Int.
//
// Def order: `id` is defined BEFORE `work` (which calls it). Each REPL input is
// a single top-level form (spec/05-definitions.md §5.13.2), and forward
// references across separate REPL inputs are NOT supported — a name must be
// defined before the input that references it. The earlier failing form of this
// test defined `work` before `id`, which is the §5.13.2 forward-reference error
// (`undefined variable: id`), NOT an accessor-resolution failure. Reordering is
// the correct fix (spec-mandated REPL incremental no-forward-reference).
#[test]
fn trace_nanos_accessor_resolves_in_repl() {
    let out = repl_prims(
        "(import [primitives [trace Trace TraceCall nanos]])\n\
         (defn id [x] x)\n\
         (defn work [x] (id x))\n\
         (nanos (trace (work 41)))\n",
    );
    assert!(
        out.stdout.contains(":primitives/Int") && !out.stdout.contains("can't resolve symbol"),
        "nanos accessor should resolve and return an Int; stdout=\n{}\nstderr=\n{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/04-expressions.md §4.12.9 — (same anchor) POSITIVE regression
// guard: a `--link`'d program consuming a trace via the `nanos` accessor builds
// and runs cleanly. The original `..._parks_defect` form asserted the COMPILE
// parked forever (worker panic → main thread waits); that park is fixed (the
// accessor resolves at link, the worker-panic→park robustness fix surfaces a
// clean error instead of hanging) and the consume path is sound.
//
// Why deterministic-return main: `--link`/`--run` use `main`'s return value as
// the process EXIT CODE. `nanos` is a wall-clock nanosecond Int, so returning it
// directly makes the exit code `nanos mod 256` — non-deterministic non-zero,
// which is NOT a crash but conflates "consume crashed" with "valid nanos used as
// exit code". Returning a deterministic `0` keeps the accessor
// consume path exercised (the trace is still collected + consumed by `nanos`)
// while making `status.success()` a clean signal: a real double-consume would
// still crash this shape.
//
// The 15s timeout guard is retained as cheap park-regression insurance; we now
// expect Ok + success.
#[test]
fn trace_linked_accessor_consume_runs_clean() {
    let src = "(import [primitives [trace Trace TraceCall nanos Pure]])\n\
         (defn id [x] x)\n\
         (defn work [x] (id x))\n\
         (defn use-it [n] 0)\n\
         (defn main [] (Pure (use-it (nanos (trace (work 41))))))\n";
    let result = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("prog.cl", src)
        .link_then_run("prog.cl")
        .timeout(Duration::from_secs(15))
        .try_output();
    match result {
        Err(helpers::e2e::CrError::Timeout(_)) => {
            panic!(
                "--link accessor consumption PARKED (compile never completed \
                 within 15s). A park regression would resurface here."
            );
        }
        Ok(out) => {
            // The build completes and the produced binary runs cleanly: the
            // accessor resolved at link, consumed the Trace tree, and `main`
            // returned the deterministic 0.
            assert!(
                out.status.success(),
                "expected the linked accessor binary to exit 0; \
                 stdout=\n{}\nstderr=\n{}",
                out.stdout,
                out.stderr
            );
        }
        Err(e) => panic!("unexpected harness error: {e}"),
    }
}

// spec: spec/04-expressions.md §4.12.4 — (same anchor) POSITIVE regression
// guard: the trace field-accessor consume path is SOUND in `--run` mode. The
// Phase-2 /arch "mode-independent RC double-consume" framing was disproved by
// the W-Trace backend investigation (FIXME 0292): there is no heap
// corruption and no RC double-consume. The earlier failing form returned
// `nanos` from `main`, but `--run`/`--link` use `main`'s return value as the
// process EXIT CODE; `nanos` is a wall-clock nanosecond Int, so the exit code
// was `nanos mod 256` — a non-deterministic non-zero value mistaken for a crash.
//
// This guard returns a deterministic `0` from `main` (via `use-it`), so the
// accessor still collects + consumes the Trace tree but the exit code is fixed.
// A real double-consume / use-after-free would still crash this shape; a sound
// consume path exits 0 every iteration.
#[test]
fn trace_run_mode_accessor_consume_runs_clean() {
    let src = "(import [primitives [trace Trace TraceCall nanos Pure]])\n\
         (defn id [x] x)\n\
         (defn work [x] (id x))\n\
         (defn use-it [n] 0)\n\
         (defn main [] (Pure (use-it (nanos (trace (work 41))))))\n";
    // Run a few times so a non-deterministic regression (a re-introduced
    // double-free racing the allocator) reliably surfaces; kept at 4 to bound
    // per-test wall-clock. A sound consume path exits 0 on every iteration.
    let mut clean = 0usize;
    let mut crashed = 0usize;
    let mut sample_exit: Option<i32> = None;
    let mut sample_stderr = String::new();
    for _ in 0..4 {
        let out = Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .file("prog.cl", src)
            .run("prog.cl")
            .timeout(Duration::from_secs(15))
            .output();
        if out.status.success() {
            clean += 1;
        } else {
            crashed += 1;
            if sample_exit.is_none() {
                sample_exit = out.status.code();
                sample_stderr = out.stderr.clone();
            }
        }
    }
    assert_eq!(
        crashed, 0,
        "`--run` of the deterministic-return accessor-consume program crashed \
         {crashed}/4 iterations (clean={clean}); sample exit={sample_exit:?}, \
         stderr=\n{sample_stderr}\n\
         A non-zero exit here is a real consume-path regression (double-free / \
         use-after-free of the Trace tree), not the nanos-as-exit-code artifact \
         (the deterministic 0 return rules that out)."
    );
}
