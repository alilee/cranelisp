// output_equivalence.rs — Mode-Output Equivalence floor (S80 Pillar B, item 4).
//
// spec/10-io.md §10.6.3 (Mode-Output Equivalence) promises a program's
// observable output (its stream of `print` effects) is byte-for-byte identical
// across `--run` (JIT), a `--link`-produced standalone binary, and the REPL.
// This file is the OUTPUT FLOOR: ~10-12 feature-class representatives plus a
// few existing-IO representatives, each driven through all six
// mode×cache permutations and asserted byte-equivalent on program stdout (REPL
// chrome stripped), via the `run_through_all_modes_output` harness.
//
// This is the output-coverage counterpart to the value-equivalence subset in
// `tests/build_confidence.rs` (which compares only the canonical Int). Where
// that asks "do all modes agree on the value?", this asks "do all modes emit
// the same observable bytes?". Full-corpus conversion is S81; this file seeds
// the floor with one representative per major feature class that performs IO.
//
// Each program prints through the workspace `stdio` platform (the harness sets
// `CRANELISP_PLATFORM_PATH` to `target/debug/`); mains return `IO _` and are
// therefore spec-conformant per §10.6 / FIXME 0318 (EXCLUDED from the Pillar B
// bare-Int sweep).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{run_through_all_modes_output, PreludeVariant};

/// Common header: declare `stdio`, import `print` + the IO constructors.
const HDR: &str = "(platform stdio)\n\
     (import [platform.stdio [print]])\n\
     (import [primitives [Pure bind]])\n";

/// Build a full program from the header + the given body.
fn prog(body: &str) -> String {
    format!("{HDR}{body}")
}

// =============================================================================
// Feature-class representatives — one printing program per class.
// =============================================================================

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (single print effect)
#[test]
fn output_equiv_single_print() {
    let program = prog("(defn main [] (print \"hello\"))\n");
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("hello");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (sequenced print effects)
#[test]
fn output_equiv_sequenced_prints() {
    // Two prints bound in order: the effect stream is `a\nb` in every mode.
    let program = prog(
        "(defn main [] (bind (print \"a\") (fn [_] (print \"b\"))))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("a\nb");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (let binding feeds print)
#[test]
fn output_equiv_let_binding() {
    let program = prog("(defn main [] (let [x \"bound\"] (print x)))\n");
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("bound");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (if branch selects output)
#[test]
fn output_equiv_if_branch() {
    let program = prog(
        "(defn main [] (if (eq-i64 1 1) (print \"yes\") (print \"no\")))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("yes");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (user fn returns the string)
#[test]
fn output_equiv_user_function_call() {
    let program = prog(
        "(defn label [] \"fn-output\")\n\
         (defn main [] (print (label)))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("fn-output");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (recursion drives N prints)
#[test]
fn output_equiv_recursion() {
    // Print "x" three times via tail recursion over a counter.
    let program = prog(
        "(defn loop-print [n] \
            (if (eq-i64 n 0) \
                (Pure 0) \
                (bind (print \"x\") (fn [_] (loop-print (sub-i64 n 1))))))\n\
         (defn main [] (loop-print 3))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("x\nx\nx");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (closure captures the string)
#[test]
fn output_equiv_closure_capture() {
    let program = prog(
        "(defn main [] \
            (let [msg \"captured\"] \
                (bind (Pure 0) (fn [_] (print msg)))))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("captured");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (bind threads a computed value)
#[test]
fn output_equiv_bind_threads_value() {
    // print returns IO Int (0); bind threads it into a continuation that prints
    // a second fixed string. The observable stream is `first\nsecond`.
    let program = prog(
        "(defn main [] \
            (bind (print \"first\") (fn [r] (print \"second\"))))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("first\nsecond");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (Pure then print)
#[test]
fn output_equiv_pure_then_print() {
    let program = prog(
        "(defn main [] (bind (Pure 7) (fn [_] (print \"after-pure\"))))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("after-pure");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (nested bind chain)
#[test]
fn output_equiv_nested_bind_chain() {
    let program = prog(
        "(defn main [] \
            (bind (print \"1\") (fn [_] \
            (bind (print \"2\") (fn [_] \
                  (print \"3\"))))))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("1\n2\n3");
}

// =============================================================================
// Existing-IO representatives — re-asserted as all-modes-output (was single-mode).
// =============================================================================

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (the canonical hello-world)
#[test]
fn output_equiv_hello_world() {
    let program = prog("(defn main [] (print \"hello, world\"))\n");
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_eq("hello, world");
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence (mode-agnostic, no expected literal)
#[test]
fn output_equiv_all_modes_agree() {
    // Cross-check without pinning a literal: every mode must agree with itself,
    // catching any mode-specific drift the literal-pinned tests above might miss.
    let program = prog(
        "(defn main [] (bind (print \"p\") (fn [_] (print \"q\"))))\n",
    );
    run_through_all_modes_output(&program, PreludeVariant::PrimitivesOnly)
        .assert_output_equivalent();
}
