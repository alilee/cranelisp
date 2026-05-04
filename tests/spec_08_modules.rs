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

// =============================================================================
// §8.10.3 Whole-Module Compilation — explicit (mod ...) declaration
//
// Wave 5.6 carry-forwards from legacy/modules.rs. All 13 use the
// tempdir-fixture + --run pattern (mode-specific exception per
// PLAN.md §"Mode canonicalisation" — module discovery is most cleanly
// tested through the batch-driver's project-root resolution).
// =============================================================================

// spec: spec/08-modules.md §8.10.3 — explicit `(mod util)` parent declaration
// before sibling import. The child file lives at `main/util.cl` because the
// parent declares (mod util), making the child a proper submodule of `main`.
// (carry: legacy/modules.rs::import_dependency_compiles_correctly)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — the binary's `--run`
// orchestration does not discover `(mod ...)` declarations in the entry
// module, so `main.cl`'s `(defn main ...)` becomes invisible after the
// `(mod util)` line is processed. Failing-not-ignored per
// `memory/feedback_failing_not_ignored.md`. Ledger entry added at
// `tests/plan/ledger.md` Wave 5.6 cluster.
#[test]
fn import_dependency_compiles_correctly() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))",
        )
        .file("main/util.cl", "(defn helper [] 99)")
        .run("main.cl")
        .output()
        .assert_exit(99);
}

// =============================================================================
// §8.11.2 Module Resolution Search Order — project root precedence
// =============================================================================

// spec: spec/08-modules.md §8.11.2 — project root MUST shadow stdlib for
// modules with the same name. REGRESSION-GUARD: Slice 1 boundary; the
// stdlib copy returns a different value, so a value mismatch would
// indicate stdlib precedence (a regression).
// (carry: legacy/modules.rs::project_root_shadows_stdlib)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod helper)` and the `--run` orchestration loses sight of `(defn main)`
// after the mod declaration. Failing-not-ignored. Ledger entry added.
#[test]
fn project_root_shadows_stdlib() {
    let cr = Cranelisp::new()
        .file(
            "main.cl",
            "(mod helper)\n(defn main [] (helper/val))",
        )
        .file("main/helper.cl", "(defn val [] 100)")
        // Stdlib copy with a DIFFERENT value — if the resolver picked
        // stdlib over project root, the exit would be 200.
        .file("stdlib/main/helper.cl", "(defn val [] 200)")
        .lib_dir("stdlib")
        .run("main.cl");
    cr.output().assert_exit(100);
}

// spec: spec/08-modules.md §8.11.2 — module file present ONLY in stdlib_dir
// MUST resolve. Demonstrates that stdlib search-path participation works
// when the module is absent from project root.
// (carry: legacy/modules.rs::stdlib_module_compiles_and_runs)
#[test]
fn stdlib_module_compiles_and_runs() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(mod helper)\n(defn main [] (helper/compute))",
        )
        // Note: NO `main/helper.cl` at project root — only in stdlib.
        .file("stdlib/main/helper.cl", "(defn compute [] 55)")
        .lib_dir("stdlib")
        .run("main.cl")
        .output()
        .assert_exit(55);
}

// =============================================================================
// §8.4 Export — re-export shell module patterns
// =============================================================================

// spec: spec/08-modules.md §8.4 — a shell module that imports + re-exports
// (the prelude-like pattern) compiles. Here `main.shell` defines a function
// directly; main imports from the shell.
// (carry: legacy/modules.rs::prelude_like_reexport_compiles)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod shell)` and the orchestration loses `(defn main)`. Failing-not-ignored.
#[test]
fn prelude_like_reexport_compiles() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(mod shell)\n(import [main.shell [get-val]])\n(defn main [] (get-val))",
        )
        .file("main/shell.cl", "(defn get-val [] 88)")
        .run("main.cl")
        .output()
        .assert_exit(88);
}

// =============================================================================
// §8.3 Import — multi-segment module path
// =============================================================================

// spec: spec/08-modules.md §8.3 — a 3-segment module path
// (`main.shell.inner`) MUST resolve. The intermediate module has its
// own `(mod inner)` declaration before importing from the leaf.
// (carry: legacy/modules.rs::multi_dot_module_path_in_import)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod shell)` and the orchestration loses `(defn main)`. Failing-not-ignored.
#[test]
fn multi_dot_module_path_in_import() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(mod shell)\n(import [main.shell [relay]])\n(defn main [] (relay))",
        )
        .file(
            "main/shell.cl",
            "(mod inner)\n(import [main.shell.inner [get-val]])\n(defn relay [] (get-val))",
        )
        .file("main/shell/inner.cl", "(defn get-val [] 88)")
        .run("main.cl")
        .output()
        .assert_exit(88);
}

// =============================================================================
// §8.5.1 Module-Qualified Names — three-level dependency chain
// =============================================================================

// spec: spec/08-modules.md §8.5.1 — A → B → C dependency chain via
// qualified ref into a leaf module. Mid declares `(mod leaf)` and refers
// to `main.mid.leaf/value` directly without an explicit import.
// (carry: legacy/modules.rs::nested_dependency_chain_compiles)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod mid)` and the orchestration loses `(defn main)`. Failing-not-ignored.
#[test]
fn nested_dependency_chain_compiles() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(mod mid)\n(import [main.mid [relay]])\n(defn main [] (relay))",
        )
        .file(
            "main/mid.cl",
            "(mod leaf)\n(defn relay [] (main.mid.leaf/value))",
        )
        .file("main/mid/leaf.cl", "(defn value [] 7)")
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// =============================================================================
// §8.5.4 Auto-Loading — qualified ref into nonexistent module
// =============================================================================

// spec: spec/08-modules.md §8.5.4 — qualified reference to a non-existent
// module MUST be a compile-time error. The auto-loader cannot find a file
// for `nonexistent`.
// (carry: legacy/modules.rs::qualified_ref_to_missing_module_errors)
#[test]
fn qualified_ref_to_missing_module_errors_neg() {
    let out = Cranelisp::new()
        .file("main.cl", "(defn main [] (nonexistent/foo))")
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "qualified ref to non-existent module MUST be rejected (spec §8.5.4); \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// §8.7.3 Private Name Semantics — glob excludes private
// =============================================================================

// spec: spec/08-modules.md §8.7.3 — `[*]` glob import MUST NOT bring in
// names defined with `(defn-)`. REGRESSION-GUARD: a regression in glob
// import that pulled in private names would break the visibility boundary.
// (carry: legacy/modules.rs::glob_import_excludes_private)
#[test]
fn glob_import_excludes_private_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(mod util)\n(import [main.util [*]])\n(defn main [] (secret))",
        )
        .file(
            "main/util.cl",
            "(defn- secret [] 42)\n(defn public-fn [] 1)",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "glob import MUST NOT include private (defn-) names — calling 'secret' \
         from main MUST fail (spec §8.7.3); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// §8.4 Export — re-export chains
// =============================================================================

// spec: spec/08-modules.md §8.4.1 — a named re-export makes the source
// module's binding visible to the importer through the shell module.
// (carry: legacy/modules.rs::export_specific_reexport)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod shell)` and the orchestration loses `(defn main)`. Failing-not-ignored.
#[test]
fn export_specific_reexport() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(mod shell)\n(import [main.shell [val]])\n(defn main [] (val))",
        )
        .file(
            "main/shell.cl",
            "(mod inner)\n(import [main.shell.inner [val]])\n(export [main.shell.inner [val]])",
        )
        .file("main/shell/inner.cl", "(defn val [] 42)")
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.4.2 — a glob re-export `[*]` re-exports all
// public names from the source module through the shell.
// (carry: legacy/modules.rs::export_glob_reexport)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod shell)` and the orchestration loses `(defn main)`. Failing-not-ignored.
#[test]
fn export_glob_reexport() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [add-i64]])\n\
             (mod shell)\n\
             (import [main.shell [a b]])\n\
             (defn main [] (add-i64 (a) (b)))",
        )
        .file(
            "main/shell.cl",
            "(mod inner)\n\
             (import [main.shell.inner [*]])\n\
             (export [main.shell.inner [*]])",
        )
        .file(
            "main/shell/inner.cl",
            "(defn a [] 10)\n(defn b [] 20)",
        )
        .run("main.cl")
        .output()
        .assert_exit(30);
}

// spec: spec/08-modules.md §8.4.4 — re-export semantics MUST compose
// across a 3-level chain: leaf → mid → shell → main.
// (carry: legacy/modules.rs::export_transitive_reexport_chain)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod shell)` and the orchestration loses `(defn main)`. Failing-not-ignored.
#[test]
fn export_transitive_reexport_chain() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(mod shell)\n\
             (import [main.shell [deep-val]])\n\
             (defn main [] (deep-val))",
        )
        .file(
            "main/shell.cl",
            "(mod mid)\n\
             (import [main.shell.mid [deep-val]])\n\
             (export [main.shell.mid [deep-val]])",
        )
        .file(
            "main/shell/mid.cl",
            "(mod leaf)\n\
             (import [main.shell.mid.leaf [deep-val]])\n\
             (export [main.shell.mid.leaf [deep-val]])",
        )
        .file(
            "main/shell/mid/leaf.cl",
            "(defn deep-val [] 77)",
        )
        .run("main.cl")
        .output()
        .assert_exit(77);
}

// spec: spec/08-modules.md §8.4.3 — a single shell module MAY re-export
// names from multiple distinct source modules.
// (carry: legacy/modules.rs::export_multiple_modules)
//
// FIXME(/int): same `--run`-mode defect as FIXME 0121 — `main.cl` declares
// `(mod shell)` and the orchestration loses `(defn main)`. Failing-not-ignored.
#[test]
fn export_multiple_modules() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [add-i64]])\n\
             (mod shell)\n\
             (import [main.shell [alpha beta]])\n\
             (defn main [] (add-i64 (alpha) (beta)))",
        )
        .file(
            "main/shell.cl",
            "(mod a)\n\
             (mod b)\n\
             (import [main.shell.a [alpha]])\n\
             (import [main.shell.b [beta]])\n\
             (export [main.shell.a [alpha]\n         main.shell.b [beta]])",
        )
        .file("main/shell/a.cl", "(defn alpha [] 3)")
        .file("main/shell/b.cl", "(defn beta [] 7)")
        .run("main.cl")
        .output()
        .assert_exit(10);
}

// spec: spec/08-modules.md §8.4.4 — a re-export of a private name MUST
// fail. Re-export semantics cannot bypass the visibility boundary set by
// `(defn-)`.
// (carry: legacy/modules.rs::export_private_name_not_reexported)
#[test]
fn export_private_name_not_reexported_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(mod shell)\n\
             (import [main.shell [secret]])\n\
             (defn main [] (secret))",
        )
        .file(
            "main/shell.cl",
            "(mod inner)\n\
             (import [main.shell.inner [*]])\n\
             (export [main.shell.inner [secret]])",
        )
        .file(
            "main/shell/inner.cl",
            "(defn- secret [] 42)\n(defn public-fn [] 1)",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "re-exporting a (defn-) private name MUST be rejected (spec §8.4.4); \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}
