// s76_macro_availability.rs — the LOCKED macro-availability model (S76 W-Macro).
//
// Authored at S76 Phase 5 Stage 1 (QA-first) per `sprints/SPRINT.md` W-Macro
// + `design/arch/macro-availability-model.md §0` (DECISION LOCKED 2026-06-03).
// These are FAILING-NOT-IGNORED until the three-pass implementation lands in
// `/dev (typecheck + int + frontend)`. Per
// `memory/feedback_failing_not_ignored.md` they are NOT `#[ignore]`'d — a
// failing/compile-failing test is the loud signal that scopes the impl.
//
// The LOCKED model (macro-availability-model.md §0.1–§0.4):
//   1. A macro's EXPANSION may reference only (a) DEPENDENCY-module definitions
//      (typechecked before the defining module) and (b) MACROS (same-module
//      macros included — the compile-time layer).
//   2. A same-module NON-MACRO definition (defn/def/const/deftype-ctor/trait
//      method) is NOT available at expansion → a clause that calls one is a
//      REJECTED PROGRAM (clear diagnostic), not a defect to fix (§0.8).
//   3. defmacro-before-use is NORMATIVE: a use textually before its `defmacro`
//      is a plain unresolved reference, not a macro call (§0.2).
//   4. FQ macro references (`mod/macro`) work, lazy-loading the dependency
//      (§9.3.6, folded into Pass 1).
//   5. REPL ≡ batch by construction (round-trip safety, §0.3).
//
// Spec anchors (the `[R4 S76 — tested-by /qa S76]` tags /spec placed):
//   spec/09-macros.md §9.3.4 (availability + def order), §9.3.6 (FQ refs),
//                     §9.12 (three-pass), §9.2.5 (body capabilities)
//   spec/05-definitions.md §5.13.2 (REPL/batch cluster unification)

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
// §9.3.4 — defmacro-before-use is NORMATIVE
// A use before the `defmacro` is a plain unresolved reference (NOT a macro
// call), and fails name resolution. This INVERTS the retired
// `spec_09_macros.rs::macro_used_before_defmacro_form_is_hoisted` test.
// =============================================================================

// spec: spec/09-macros.md §9.3.4 — defmacro-before-use; a forward use is a
// plain unresolved reference and MUST fail name resolution (not be hoisted).
#[test]
fn macro_used_before_defmacro_is_unresolved_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .user(
            "(defn main [] (nope 42))\n\
             (defmacro nope [x] x)",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(42) && out.status.code() != Some(0),
        "forward macro use MUST NOT be hoisted/expanded; it is a plain \
         unresolved reference per §9.3.4. stdout={} stderr={}",
        out.stdout,
        out.stderr,
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("nope")
            && (combined.contains("error") || combined.contains("Error")),
        "expected an unresolved-reference diagnostic naming `nope`; \
         stderr={} stdout={}",
        out.stderr,
        out.stdout,
    );
}

// spec: spec/09-macros.md §9.3.4 — a macro defined BEFORE its use expands
// normally (the positive companion; the always-reliable subset).
#[test]
fn macro_defined_before_use_expands() {
    repl_prims("(defmacro nope [x] x)\n(nope 42)\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §9.3.4 / §9.12 — SAME-MODULE NON-MACRO HELPER AT EXPANSION IS REJECTED
// This is the `stdlib/defs.cl` real-world instance + the §4.4 trace scenario.
// Under the LOCKED decision it is a REJECTED PROGRAM with a clear diagnostic
// (NOT a defect to fix). INVERTS the retired
// `spec_09_macros.rs::macro_body_drives_three_level_call_graph`.
// =============================================================================

// spec: spec/09-macros.md §9.3.4 — a macro clause that calls a SAME-MODULE
// `defn` helper at expansion time MUST be rejected with a clear diagnostic
// naming the helper, directing it to a dependency module.
#[test]
fn macro_clause_calls_same_module_defn_helper_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .user(
            "(import [primitives [add-i64]])\n\
             (defn helper [x] (add-i64 x 1))\n\
             (defmacro m [a] (helper a))\n\
             (defn f [y] (m y))\n\
             (defn main [] (f 41))",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "same-module non-macro helper at expansion MUST be rejected per \
         §9.3.4; got exit 0. stdout={} stderr={}",
        out.stdout,
        out.stderr,
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("helper")
            && (combined.contains("dependency") || combined.contains("same-module")),
        "expected a clear diagnostic naming `helper` and pointing at the \
         dependency-module / same-module rule per §0.8; stderr={} stdout={}",
        out.stderr,
        out.stdout,
    );
}

// spec: spec/09-macros.md §9.3.4 — reading a SAME-MODULE `def`/`const` value
// at expansion time is equally rejected (def/const are non-macro defs).
#[test]
fn macro_clause_reads_same_module_def_value_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .user(
            "(import [primitives [add-i64]])\n\
             (def base 10)\n\
             (defmacro m [a] (add-i64 a base))\n\
             (defn main [] (m 5))",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "same-module `def` value at expansion MUST be rejected per §9.3.4; \
         got exit 0. stdout={} stderr={}",
        out.stdout,
        out.stderr,
    );
}

// =============================================================================
// §9.3.4 / §9.2.5 — a macro calling an IMPORTED (dependency-module) helper at
// expansion WORKS. This is the correct authoring pattern the rejection above
// directs toward, and the canonical cross-module case (already green in
// spec_09_macros.rs::cross_module_macro_calls_helper_in_other_module — this is
// the s76-locked-model assertion that it MUST keep working).
// =============================================================================

// spec: spec/09-macros.md §9.2.5 — a macro clause calling a helper from a
// DEPENDENCY module at expansion time works (helper typechecked-before).
// Per §9.2.2 every macro parameter is `Sexp` and per §9.2.3 the body MUST
// return `Sexp`, so the dependency helper takes/returns `Sexp`: `bump` ignores
// its `Sexp` arg and returns the literal `(SexpInt 42)`, which is the macro's
// expansion. `wrap 41` therefore expands to `42`. (FIXME 0267 retype.)
#[test]
fn macro_clause_calls_imported_helper_at_expansion_works() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(
            "main.cl",
            "(import [mac [wrap]])\n(defn main [] (wrap 41))",
        )
        // `mac` depends on `helper`; `helper` is typechecked-and-compiled
        // just-in-time when `wrap`'s expansion first needs `bump`.
        .file(
            "mac.cl",
            "(import [helper [bump]])\n\
             (defmacro wrap [a] (bump a))",
        )
        .file(
            "helper.cl",
            "(import [macros [*]])\n\
             (defn bump [s] (SexpInt 42))",
        )
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/09-macros.md §9.2.3 — a dependency-module helper called unquoted
// in a macro clause body MUST satisfy the macro-body contract: parameters are
// `Sexp` (§9.2.2) and the body returns `Sexp` (§9.2.3). An ill-typed helper
// with the `Int -> Int` shape (the old fixture) is REJECTED with a type error
// (the body yields `Int` where `Sexp` is required). This is the deliberate
// negative companion to the positive case above (FIXME 0267 _neg sibling).
#[test]
fn macro_clause_calls_imported_helper_ill_typed_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(
            "main.cl",
            "(import [mac [wrap]])\n(defn main [] (wrap 41))",
        )
        .file(
            "mac.cl",
            "(import [helper [bump]])\n\
             (defmacro wrap [a] (bump a))",
        )
        // Ill-typed helper: `Int -> Int`. Calling it unquoted in `wrap`'s body
        // violates §9.2.2/§9.2.3 (macro params/result are `Sexp`).
        .file(
            "helper.cl",
            "(import [primitives [add-i64]])\n\
             (defn bump [x] (add-i64 x 1))",
        )
        .run("main.cl")
        .output();
    assert!(
        out.status.code() != Some(0) && out.status.code() != Some(42),
        "an `Int -> Int` helper called unquoted in a macro body MUST be \
         rejected per §9.2.2/§9.2.3; got exit {:?}. stdout={} stderr={}",
        out.status.code(),
        out.stdout,
        out.stderr,
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("error") || combined.contains("Error"),
        "expected a type-error diagnostic (Sexp expected) per §9.2.3; \
         stdout={} stderr={}",
        out.stdout,
        out.stderr,
    );
}

// =============================================================================
// §9.3.6 — FQ macro references (`mod/macro`) work without explicit import,
// lazy-loading the dependency. NEW capability (folded into Pass 1).
// =============================================================================

// spec: spec/09-macros.md §9.3.6 — a qualified macro reference `mod/macro`
// resolves to a macro and expands, lazy-loading the defining module; no
// explicit `import` of the macro is required.
#[test]
fn fq_macro_reference_expands_without_import() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(
            "main.cl",
            // No `(import [mac [twice]])` — referenced fully-qualified.
            "(import [primitives [add-i64]])\n\
             (defn main [] (mac/twice 21))",
        )
        .file(
            "mac.cl",
            "(import [primitives [add-i64]])\n\
             (defmacro twice [x] `(add-i64 ~x ~x))",
        )
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// §9.12 — a macro that GENERATES top-level defns / defmacros (structural-form
// re-entry, macro-availability-model.md §0.4 "recursively"). The expansion
// result re-enters classification in the same cluster.
// =============================================================================

// spec: spec/09-macros.md §9.12 — a macro expanding into a structural form
// `(begin (defn ...) ...)` registers the generated defn in the same cluster.
#[test]
fn macro_generates_toplevel_defn() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .user(
            "(import [primitives [add-i64]])\n\
             (defmacro make-adder [] `(defn add5 [x] (add-i64 x 5)))\n\
             (make-adder)\n\
             (defn main [] (add5 37))",
        )
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/09-macros.md §9.12 — a macro-generated `defmacro` is itself
// typechecked/compiled in Pass 1 and becomes available to a subsequent use
// (expansion runs to fixpoint).
#[test]
fn macro_generates_defmacro_available_to_later_use() {
    repl_prims(
        "(defmacro make-id [] `(defmacro gen-id [x] x))\n\
         (make-id)\n\
         (gen-id 42)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.13.2 — REPL ≡ batch macro availability (round-trip safety, §0.3).
// The SAME program produces the SAME macro-availability outcome in REPL and
// `--run`. defmacro-before-use holds identically; the rejected same-module
// helper is rejected identically.
// =============================================================================

// spec: spec/05-definitions.md §5.13.2 — defmacro-before-use within a REPL
// `(begin ...)` cluster mirrors batch: a forward macro use inside the cluster
// is a plain unresolved reference.
#[test]
fn repl_begin_cluster_forward_macro_use_is_unresolved_neg() {
    let out = repl_prims(
        "(begin (defn main [] (nope 42)) (defmacro nope [x] x))\n",
    );
    // Cluster must not silently expand the forward macro reference.
    assert!(
        !out.stdout.contains(":primitives/Int 42"),
        "forward macro use in a begin cluster MUST NOT expand per §5.13.2; \
         stdout={}",
        out.stdout,
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("error") || combined.contains("Error"),
        "forward macro use in a begin cluster MUST fail per §5.13.2; \
         stdout={} stderr={}",
        out.stdout,
        out.stderr,
    );
}

// spec: spec/05-definitions.md §5.13.2 — a macro using an EARLIER same-module
// macro (compile-time layer) works in the REPL — macros may reference
// same-module macros (§0.1 (b)). Positive parity companion.
#[test]
fn repl_macro_uses_earlier_macro_works() {
    repl_prims(
        "(import [primitives [add-i64]])\n\
         (defmacro inc [x] `(add-i64 ~x 1))\n\
         (defmacro inc2 [x] `(inc (inc ~x)))\n\
         (inc2 40)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}
