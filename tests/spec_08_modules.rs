// spec_08_modules.rs — Module system (Sprint 64 Wave 5 Batch 3).
//
// Covers `spec/08-modules.md`. Carries forward language-behaviour assertions
// from legacy integration-tier `tests/modules.rs`, `tests/ring1.rs`,
// `tests/ring2.rs`, `tests/sprint59_neg.rs`, and `tests/e2e.rs`.
// Module tests use on-disk fixtures via the `Cranelisp::file()` builder
// and `--run` mode (mode-specific exception per
// `tests/plan/PLAN.md §"Mode canonicalisation"` — module discovery is
// most cleanly tested through the batch-driver's project-root resolution).
//
// What this file covers:
//   - Module declaration (§8.2)
//   - Imports — specific names, glob (§8.3)
//   - Qualified names (§8.5)
//   - Name resolution (§8.6)
//   - Visibility — defn-, deftype- (§8.7)
//   - Prelude (§8.8)
//   - Synthetic modules — primitives (§8.9)
//   - Module compilation order (§8.10)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// =============================================================================
// §8.3 Import — specific names + cross-module call
// =============================================================================

// spec: spec/08-modules.md §8.3 — import a specific name from a sibling module
#[test]
fn import_specific_name_compiles_and_runs() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper))",
        )
        .file("util.cl", "(defn helper [] 42)")
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// §8.3 Import — glob
// =============================================================================

// spec: spec/08-modules.md §8.3 — `[*]` glob import
#[test]
fn import_glob_brings_in_all_exports() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [util [*]])\n(defn main [] (helper))",
        )
        .file("util.cl", "(defn helper [] 17)")
        .run("main.cl")
        .output()
        .assert_exit(17);
}

// =============================================================================
// §8.5 Qualified Names
// =============================================================================

// spec: spec/08-modules.md §8.5 — call via fully-qualified `module/name`
#[test]
fn qualified_name_resolution() {
    // Qualified access does not require a names list: importing the module
    // (here triggered transitively by referencing `util/helper`) makes the
    // qualified name resolvable. We use a glob import to bring helper into
    // scope plus reference via qualified name to assert resolution works.
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [util [helper]])\n(defn main [] (util/helper))",
        )
        .file("util.cl", "(defn helper [] 99)")
        .run("main.cl")
        .output()
        .assert_exit(99);
}

// =============================================================================
// §8.7 Visibility — defn- private
// =============================================================================

// spec: spec/08-modules.md §8.7 — defn- private MUST NOT be importable
#[test]
fn private_defn_not_importable_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [util [secret]])\n(defn main [] (secret))",
        )
        .file("util.cl", "(defn- secret [] 0)")
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "importing a defn- private name MUST be rejected (spec §8.7)"
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("secret")
            || combined.contains("private")
            || combined.contains("not found")
            || combined.contains("not exported"),
        "error should diagnose missing/private 'secret'; got: {combined}"
    );
}

// =============================================================================
// §8.7 Visibility — deftype- private
// =============================================================================

// spec: spec/08-modules.md §8.7 — deftype- private MUST NOT be importable
#[test]
fn private_deftype_not_importable_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [util [Hidden]])\n(defn main [] 0)",
        )
        .file("util.cl", "(deftype- Hidden [:Int x])")
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "importing a deftype- private type MUST be rejected (spec §8.7)"
    );
}

// =============================================================================
// §8.6 Name Resolution — local shadows imported
// =============================================================================

// spec: spec/08-modules.md §8.6 — local binding shadows module-scope name
#[test]
fn local_let_shadows_imported_name() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [util [helper]])\n(defn main [] (let [helper 7] helper))",
        )
        .file("util.cl", "(defn helper [] 100)")
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// =============================================================================
// §8.9 Synthetic primitives module — always available
// =============================================================================

// spec: spec/08-modules.md §8.9 — primitives synthetic module is available
#[test]
fn synthetic_primitives_module_available() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [*]])\n(defn main [] (add-i64 1 2))",
        )
        .run("main.cl")
        .output()
        .assert_exit(3);
}

// =============================================================================
// §8.3.1 — import of a non-existent name MUST error
// =============================================================================

// spec: spec/08-modules.md §8.3 — non-existent imported name fails compilation
#[test]
fn import_of_non_existent_name_errors_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [util [does-not-exist]])\n(defn main [] (does-not-exist))",
        )
        .file("util.cl", "(defn exists [] 42)")
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "importing a non-existent name MUST be a compile-time error (spec §8.3)"
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("does-not-exist")
            || combined.contains("not found")
            || combined.contains("unknown"),
        "error should name the missing import; got: {combined}"
    );
}

// =============================================================================
// §8.10 Module Compilation Order — cycle detection
// =============================================================================

// spec: spec/08-modules.md §8.10 — circular module imports MUST be rejected
#[test]
fn module_cycle_detection_neg() {
    // Spec §8.10.2: "Circular dependencies MUST be detected and reported as
    // a compile-time error." The implementation rejects cycles via cascading
    // dependency-failure diagnostics. The diagnostic text does not currently
    // say "cycle" (FIXME(/int) potentially — UX gap, not a spec violation),
    // so the test asserts only that the program is rejected.
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [a [f]])\n(defn main [] (f))",
        )
        .file("a.cl", "(import [b [g]])\n(defn f [] (g))")
        .file("b.cl", "(import [a [f]])\n(defn g [] (f))")
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "import cycles MUST be rejected at compile time (spec §8.10.2); \
         stdout={} stderr={}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// §8.3.7 — super at top-level MUST error (REPL surface)
// =============================================================================

// spec: spec/08-modules.md §8.3 — `super` at the top-level rejected
#[test]
fn super_import_at_top_level_neg() {
    // The REPL is inherently in the top-level user module; `super` there
    // has no parent to resolve to, MUST be rejected.
    let out = Cranelisp::new()
        .repl()
        .stdin("(import [super [*]])\n")
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("super")
            || combined.to_lowercase().contains("top-level")
            || combined.contains("parent")
            || combined.contains("error")
            || combined.contains("Error"),
        "REPL super-import should produce a diagnostic (spec §8.3); got: {combined}"
    );
}

// =============================================================================
// §8.3.9 — import placement and ordering (Wave 5.5 GAP-COVER)
//
// These two tests carry forward sprint59_neg.rs assertions that were missed
// by the Wave 5 dedupe.
// =============================================================================

// spec: spec/08-modules.md §8.3 — (import …) placed inside a let body MUST be
// rejected: imports are top-level forms, extracted before macro expansion.
// (carry: legacy/sprint59_neg.rs::import_inside_let_rejected_neg)
#[test]
fn import_inside_let_rejected_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(defn main []\n  (let [x 1]\n    (import [util [helper]])\n    (helper)))",
        )
        .file("util.cl", "(defn helper [] 42)")
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "(import …) inside a let body MUST be rejected — spec §8.3 requires \
         imports as top-level forms; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/08-modules.md §8.3.9 — multiple `import` forms accumulate; effects
// MUST be visible to all definitions regardless of source position.
// Per §8.3.9: "An implementation MUST process `import` before compiling
// definitions in the same module, so that imported names are available
// during type checking and code generation."
// (carry: legacy/sprint59_neg.rs::import_below_use_still_available_before_definitions)
//
// FIXME(/int): the integration-tier helper `batch_run_file` accepts this
// program; the binary `--run` path rejects it with "entry module has no
// `main` function". Spec parity gap between integration helper and binary
// surface; defect is in `/int` orchestration. Failing-not-ignored per
// `memory/feedback_failing_not_ignored.md`. Ledger entry added under
// Wave 5.5.
#[test]
fn import_below_use_still_available_before_definitions() {
    // The defn references `helper` BEFORE the import line — but per §8.3.9
    // imports are extracted en bloc before compilation, so `main` MUST see
    // `helper` at typecheck time.
    Cranelisp::new()
        .file(
            "main.cl",
            "(defn main [] (helper))\n(import [util [helper]])",
        )
        .file("util.cl", "(defn helper [] 42)")
        .run("main.cl")
        .output()
        .assert_exit(42);
}
