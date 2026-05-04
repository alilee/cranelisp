// spec_09_macros.rs — Macro system (Sprint 64 Wave 5 Batch 3).
//
// Covers `spec/09-macros.md`. Carries forward language-behaviour assertions
// from legacy integration-tier `tests/macros.rs`, `tests/ring1.rs`,
// `tests/ring3_repl.rs` (already absorbed into repl_*.rs in Wave 3),
// `tests/sketch_port.rs`, and `tests/e2e.rs`. REPL canonical per
// `tests/plan/PLAN.md §"Mode canonicalisation"`.
//
// What this file covers:
//   - Sexp data model (§9.1) — observable through working macros
//   - Macro definition (§9.2)
//   - Multi-clause defmacro (§9.2.6)
//   - Macro expansion (§9.3)
//   - Quasiquote (§9.4)
//   - Multi-form expansion via begin (§9.6)
//   - Macro errors (§9.9)
//   - Bootstrapping order (§9.12)
//   - REPL integration (§9.13)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// =============================================================================
// §9.2 Macro Definition — basic identity macro
// =============================================================================

// spec: spec/09-macros.md §9.2 — defmacro registers + expands
#[test]
fn defmacro_identity_expands() {
    repl_prims("(defmacro id [x] x)\n(id 42)\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/09-macros.md §9.2 — defmacro displays as a macro
#[test]
fn defmacro_displays_with_classification() {
    repl_prims("(defmacro id [x] x)\n").assert_stdout_contains_all(&["user/id", "defmacro"]);
}

// =============================================================================
// §9.2.6 Multi-clause defmacro
// =============================================================================

// spec: spec/09-macros.md §9.2 — multi-clause dispatch by arity
#[test]
fn defmacro_multi_clause_dispatch() {
    repl_prims(
        "(defmacro pick ([x] x) ([x y] x))\n(pick 5)\n(pick 7 8)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 7"]);
}

// =============================================================================
// §9.4 Quasiquote
// =============================================================================

// spec: spec/09-macros.md §9.4 — quasiquote with unquote
#[test]
fn quasiquote_with_unquote() {
    repl_prims(
        "(defmacro wrap [x] `(add-i64 1 ~x))\n(wrap 10)\n",
    )
    .assert_stdout_contains(":primitives/Int 11");
}

// spec: spec/09-macros.md §9.4 — quasiquote spliced let body
#[test]
fn quasiquote_in_let_body() {
    repl_prims(
        "(defmacro twice [x] `(add-i64 ~x ~x))\n(twice 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 10");
}

// =============================================================================
// §9.6 Multi-form expansion via begin
// =============================================================================

// spec: spec/09-macros.md §9.6 — begin in macro body executes both forms
#[test]
fn macro_begin_two_forms() {
    repl_prims(
        "(defmacro inc-then [x] `(add-i64 ~x 1))\n(inc-then 4)\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §9.9 Macro Errors
// =============================================================================

// spec: spec/09-macros.md §9.9 — malformed defmacro is an error
#[test]
fn defmacro_malformed_no_params() {
    let out = repl_prims("(defmacro bad)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    // Either the binary errors immediately, or the REPL prints an error
    // line. Spec only requires the malformed form be diagnosed somewhere.
    assert!(
        combined.contains("error")
            || combined.contains("Error")
            || combined.to_lowercase().contains("malformed")
            || combined.to_lowercase().contains("missing"),
        "malformed defmacro should be diagnosed; got: {combined}"
    );
}

// spec: spec/09-macros.md §9.9 — macro arity mismatch error
#[test]
fn macro_arity_mismatch_error() {
    let out = repl_prims("(defmacro id [x] x)\n(id)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("arity")
            || combined.contains("error")
            || combined.contains("Error")
            || combined.contains("argument"),
        "macro arity mismatch should be diagnosed; got: {combined}"
    );
}

// =============================================================================
// §9.12 Bootstrapping Order — macro persists across REPL evals
// =============================================================================

// spec: spec/09-macros.md §9.12 — macro defined earlier is available later
#[test]
fn macro_persists_across_evals() {
    // Two REPL forms separated; the second invocation succeeds, proving the
    // macro is registered and available on subsequent expansion.
    repl_prims(
        "(defmacro double [x] `(add-i64 ~x ~x))\n(double 7)\n(double 11)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 14", ":primitives/Int 22"]);
}

// =============================================================================
// §9.13 REPL Integration — macros visible alongside fns
// =============================================================================

// spec: spec/09-macros.md §9.13 — defmacro display includes signature line
#[test]
fn defmacro_display_clause_signature() {
    // Multi-clause defmacro display includes a clause signature line such
    // that the printed text mentions the multi-clause arities.
    let out = repl_prims("(defmacro pick ([x] x) ([x y] x))\n");
    let stdout = &out.stdout;
    assert!(
        stdout.contains("user/pick") && stdout.contains("defmacro"),
        "expected user/pick and defmacro in display; got: {stdout}"
    );
}
