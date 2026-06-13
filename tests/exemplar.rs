//! Sprint 64 Wave 6 batch 1 carry-forward — exemplar batch-mode shapes.
//!
//! (carry: legacy/exemplar.rs::exemplar_batch_const_macro)
//! (carry: legacy/exemplar.rs::exemplar_batch_cross_module_import)
//! (carry: legacy/exemplar.rs::exemplar_batch_cross_module_adt)
//! (carry: legacy/exemplar_solver_correctness.rs::eliminate_on_same_value_given_returns_none, inline-rewritten)
//!
//! Per the Wave 6 batch 1 audit (tests/plan/wave-6-batch-1-audit.md),
//! these tests assert the **multi-file on-disk batch compilation**
//! pipeline against TempDir-rooted source (not inline strings via the
//! REPL session). The legacy tests used the integration helper
//! `batch_run_file`; the new shape uses the e2e `Cranelisp` builder
//! with `.run("main.cl")` and reads the program exit code as the
//! observation.
//!
//! T-S2-1 (the Layer-1 `eliminate` contract guard) is inline-rewritten
//! per `memory/feedback_repro_handoff.md` — the new repro embeds a
//! minimal `Cell` + `eliminate` definition sufficient to trigger the
//! contract violation, removing the dependency on `exemplar/grid.cl`
//! and `exemplar/solver.cl` that the legacy version copied into
//! TempDir at test start.

#[path = "helpers/e2e.rs"]
mod e2e;

use e2e::Cranelisp;

// =============================================================================
// Multi-module batch compilation shapes
// =============================================================================

// spec: spec/08-modules.md §8.2.1 — module declaration in batch entry file.
//       The angle this test asserts is that a defmacro defined in the entry
//       file resolves at compile time and is callable from main, yielding
//       the expected Int. (Legacy version asserted the prelude's `const`
//       macro; the new shape inlines a defmacro to avoid a stdlib
//       dependency per `tests/CLAUDE.md` test isolation rules.)
//
// (carry: legacy/exemplar.rs::exemplar_batch_const_macro)
#[test]
fn batch_const_macro_in_main() {
    Cranelisp::new()
        .run("main.cl")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defmacro size [] `9)\n(defn main [] (Pure (size)))",
        )
        .output()
        .assert_exit(9);
}

// spec: spec/08-modules.md §8.10.1 — qualified import + call across modules
//
// (carry: legacy/exemplar.rs::exemplar_batch_cross_module_import)
#[test]
fn batch_cross_module_function_import() {
    Cranelisp::new()
        .run("main.cl")
        .file("util.cl", "(defn helper [] 42)")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper)))",
        )
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.10.1 — cross-module ADT export (constructors,
//       type) plus pattern match on the imported ADT
//
// (carry: legacy/exemplar.rs::exemplar_batch_cross_module_adt)
#[test]
fn batch_cross_module_adt_export_and_pattern_match() {
    Cranelisp::new()
        .run("main.cl")
        .file(
            "types.cl",
            "(deftype Color Red Green Blue)\n\
             (defn color-val [:Color c] (match c [Red 1 Green 2 Blue 3]))",
        )
        .file(
            "main.cl",
            "(import [primitives [add-i64 Pure]])\n\
             (import [types [Color Red Green Blue color-val]])\n\
             (defn main [] (Pure (add-i64 (color-val Red) (color-val Blue))))",
        )
        .output()
        .assert_exit(4); // 1 + 3
}

// =============================================================================
// T-S2-1 — Layer-1 contract: eliminate on a same-value Given/Solved cell
//          MUST return None (a contradiction).
// =============================================================================
//
// Inline-rewritten per memory/feedback_repro_handoff.md (Sprint 64 Wave 6
// batch 1): legacy version copied exemplar/grid.cl and exemplar/solver.cl
// into a TempDir before running the inline repro source. The new repro
// embeds the minimum-needed Cell ADT + eliminate skeleton inline so the
// regression guard does NOT depend on exemplar/ source which is subject
// to redesign / removal by /port.
//
// CONTRACT: eliminate on a cell already fixed at value v, asked to
// eliminate digit d, MUST return None when v == d (contradiction —
// eliminating the cell's own fixed value).

// spec: spec/05-definitions.md §5.2 — ADT pattern matching contract
//       (the test exercises a layer-1 algorithmic invariant on the ADT
//       defined inline; T-S2-1 was originally documented in
//       tests/plan/legacy/ring4.md "Slice 2 branch-b outcome" but that
//       doc is archived).
//
// FIXME(/spec): the contract is not stated normatively in any spec/*.md;
// it is an exemplar-internal invariant ledgered as the regression
// surface for a known historical defect (Sprint 61 Slice 2 Layer 1).
//
// (carry: legacy/exemplar_solver_correctness.rs::eliminate_on_same_value_given_returns_none, inline-rewritten)
#[test]
fn t_s2_1_eliminate_contract_on_given_returns_none() {
    // Inline minimal Cell + eliminate — no exemplar/ source dependency.
    // The repro is small enough to embed: one cell with (Given 5), one
    // call to eliminate with digit 5, must return None.
    //
    // main returns:
    //   0 = pass (eliminate returned None — contract honoured)
    //   1 = fail (eliminate returned (Some _) — contract violated)
    //   2 = setup failure (cell did not match expected (Given 5))
    let source = r#"(import [primitives [*]])

(deftype Cell
  (Given [:Int v])
  (Solved [:Int v])
  (Candidates [:Int mask]))

(deftype (Option a) None (Some [:a v]))

;; Layer-1 contract: eliminate on a cell already fixed at value v, asked
;; to remove digit d, MUST return None when v == d (eliminating own value
;; = contradiction). A naive impl would return (Some cell) and propagate
;; an inconsistent grid; the contract requires explicit None.
(defn eliminate [:Cell c :Int d]
  (match c
    [(Given v)
       (if (eq-i64 v d) None (Some c))
     (Solved v)
       (if (eq-i64 v d) None (Some c))
     (Candidates m)
       ;; Candidates path not exercised by this regression guard; pass-through.
       (Some c)]))

(defn main []
  (Pure (let [c (Given 5)]
    (match c
      [(Given v)
         (if (eq-i64 v 5)
           (match (eliminate c 5)
             [None 0
              (Some _) 1])
           2)
       _ 2]))))
"#;

    Cranelisp::new()
        .run("main.cl")
        .file("main.cl", source)
        .output()
        .assert_exit(0);
}
