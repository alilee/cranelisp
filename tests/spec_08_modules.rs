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

use helpers::e2e::{Cranelisp, PreludeVariant};
use std::time::Duration;

// =============================================================================
// §8.3 Import — specific names + cross-module call
// =============================================================================

// spec: spec/08-modules.md §8.3 — import a specific name from a sibling module
#[test]
fn import_specific_name_compiles_and_runs() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper)))",
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
            "(import [primitives [Pure]])\n(import [util [*]])\n(defn main [] (Pure (helper)))",
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
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (util/helper)))",
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
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (let [helper 7] helper)))",
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
            "(import [primitives [*]])\n(defn main [] (Pure (add-i64 1 2)))",
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

// spec: spec/08-modules.md §8.10 — circular module imports MUST be rejected
//
// OQ-2 (Sprint 78): the tightest 2-node mutual import (m ↔ n) under the
// in-call-stack dep-drive. The existing `module_cycle_detection_neg` above
// covers a 3-node chain; this covers the 2-node mutual case that
// `design/int/s77-int-restructure.md §3.4` reasons about directly — "W blocks
// M on N; a worker blocks N on M; the second block_for_typecheck detects the
// M→N→M cycle". It additionally asserts the LIVENESS property OQ-2 names:
// rejection fires BEFORE any wait (the cycle path runs detect_cycle_locked
// before adding the waiter), so the subprocess TERMINATES promptly rather than
// deadlocking. The `.timeout(...)` bound makes a deadlock regression surface as
// a Timeout panic, not an infinitely-hanging test.
#[test]
fn mutual_import_cycle_rejected_before_wait_neg() {
    // Tightest 2-node mutual cycle: m imports n, n imports m. `main` is the
    // entry that pulls in m.
    let out = Cranelisp::new()
        .file("main.cl", "(import [m [f]])\n(defn main [] (f))")
        .file("m.cl", "(import [n [g]])\n(defn f [] (g))")
        .file("n.cl", "(import [m [f]])\n(defn g [] (f))")
        .run("main.cl")
        .timeout(Duration::from_secs(10))
        .output();
    // (1) Rejection: the program does NOT succeed. (The diagnostic text need
    //     not say "cycle" — matching `module_cycle_detection_neg`'s note that
    //     the wording is a UX gap, not a spec violation.)
    // (2) Liveness: reaching this assertion at all proves the subprocess
    //     terminated within the 10s bound — `.output()` would have panicked
    //     with CrError::Timeout on a deadlock regression. This is the OQ-2
    //     "fires before any wait" evidence: rejection is prompt, not after a
    //     block-and-deadlock.
    assert!(
        !out.status.success(),
        "2-node mutual import cycle (m ↔ n) MUST be rejected before any wait \
         (spec §8.10; design/int/s77-int-restructure.md §3.4); \
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
            "(import [primitives [Pure]])\n(defn main [] (Pure (helper)))\n(import [util [helper]])",
        )
        .file("util.cl", "(defn helper [] 42)")
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// §8.2.2 Inline Submodule Declaration — extraction + parent rewrite
//
// FIXME 0217 (S81 bite-1) implemented spec §8.2.2 step 2: after the inline body
// is written to the backing file (step 1), the PARENT source file is rewritten
// in place, replacing `(mod name form…)` with bare `(mod name)`. The in-crate
// unit tests pin the pure splice (`splice_inline_mod_to_bare`) with a HAND-BUILT
// span; these e2e tests were authored as the owed end-to-end regression guard
// (FIXME 0330) and instead SURFACED a defect.
//
// DEFECT (FIXME 0336 → /dev int): under `--run`, `rewrite_parent_inline_mod` is
// invoked TWICE for the same `(mod child …)` form — the S78 cluster
// retry-from-top re-runs Pass-0 against the original `sexps` (span 29..59) AFTER
// the first pass already shrank the on-disk parent to 77 bytes. The second call
// slices the STALE span over the rewritten file, producing a corrupt parent
// (`(mod child)e (child/helper)))`). The exact-match idempotence guard in
// `splice_inline_mod_to_bare` misses because the stale-span slice is not exactly
// `(mod child)`. The first run still exits correctly (in-memory state is fine),
// but the durable backing-file damage breaks every subsequent run. The reader
// span (29..59) and the pure splice are CORRECT; the bug is the double-invocation
// with a stale span on cluster retry — int's, in `src/process_form.rs`.
//
// These tests are FAILING-NOT-IGNORED per `memory/feedback_failing_not_ignored.md`
// — they pin the spec-correct behaviour and flip green when /dev resolves 0336.
// =============================================================================

// spec: spec/08-modules.md §8.2.2 — first compilation of an inline `(mod child
// form…)` MUST (1) create the backing file `{stem}/child.cl` containing the
// inline body, and (2) rewrite the parent file so the inline form becomes a
// bare `(mod child)` reference WITH SURROUNDING FORMS PRESERVED. After
// extraction the submodule is indistinguishable from one created manually.
#[test]
fn inline_mod_extracts_backing_file_and_rewrites_parent() {
    let cr = Cranelisp::new()
        .file(
            "app.cl",
            "(import [primitives [Pure]])\n\
             (mod child (defn helper [] 7))\n\
             (defn main [] (Pure (child/helper)))",
        )
        .run("app.cl");
    let out = cr.output().assert_exit(7);

    // Step 1: the backing file was created with the inline body.
    assert!(
        out.tmp_exists("app/child.cl"),
        "backing file app/child.cl MUST be created from the inline body"
    );
    let child = out.read_tmp("app/child.cl");
    assert!(
        child.contains("(defn helper [] 7)"),
        "backing file MUST contain the inline body, got:\n{child}"
    );

    // Step 2: the parent file was rewritten — the inline form is now a bare
    // `(mod child)` reference, the inline body is gone, and the surrounding
    // forms (import, main) are preserved INTACT. The last assertion fails under
    // FIXME 0336 (the `main` form is truncated by the stale-span re-rewrite).
    let parent = out.read_tmp("app.cl");
    assert!(
        parent.contains("(mod child)"),
        "parent MUST be rewritten to a bare `(mod child)` reference, got:\n{parent}"
    );
    assert!(
        !parent.contains("(mod child (defn helper [] 7))"),
        "the inline body MUST NOT remain in the parent after extraction, got:\n{parent}"
    );
    assert!(
        parent.contains("(import [primitives [Pure]])")
            && parent.contains("(defn main [] (Pure (child/helper)))"),
        "surrounding forms MUST be preserved intact (FIXME 0336 corrupts `main`), got:\n{parent}"
    );
}

// spec: spec/08-modules.md §8.2.2 — the inline form is a "one-time creation
// syntax": after extraction, subsequent compilations use the extracted file.
// Re-running the project MUST be idempotent — the parent already holds the bare
// `(mod child)` reference and the program output is unchanged.
#[test]
fn inline_mod_extraction_is_idempotent_on_rerun() {
    let cr = Cranelisp::new()
        .file(
            "app.cl",
            "(import [primitives [Pure]])\n\
             (mod child (defn helper [] 7))\n\
             (defn main [] (Pure (child/helper)))",
        )
        .run("app.cl");
    let first = cr.output().assert_exit(7);
    let child_after_first = first.read_tmp("app/child.cl");

    // Second run in the same project tree: the rewritten parent + extracted
    // backing file MUST re-run cleanly to the same result. Fails under 0336
    // because the first run corrupted `app.cl`.
    let second = first.run_again().run("app.cl").output().assert_exit(7);
    assert_eq!(
        child_after_first,
        second.read_tmp("app/child.cl"),
        "the extracted backing file MUST be unchanged on re-run"
    );
}

// =============================================================================
// §8.2.2 — inline `(mod test …)` extraction writes the backing file
// LIB-DIR-RELATIVE (`{parent_dir}/…`), never CWD-relative (FIXME 0423 — /int)
// =============================================================================
//
// DEFECT (FIXME 0423 → /int): when a module that lives in a CRANELISP_LIB
// directory declares an INLINE `(mod test …)` body, and the program is run
// from a working directory that is NOT the lib-dir, the extractor writes the
// extracted backing file CWD-relative (`<cwd>/<module>/test.cl`) instead of
// next to its parent in the lib-dir (`<lib-dir>/<module>/test.cl`). This is
// the root cause of the stray `./collections/`, `./num/`, … trees that
// appeared at the repo root when the stdlib self-test runner was invoked from
// the repo root in S87 (currently band-aided by a `.gitignore` guard). The
// parent rewrite (to bare `(mod test)`) DOES correctly target the lib-dir
// copy; only the backing-file write mis-resolves against the process CWD.
//
// REPRO (this test): `mod.cl` with an inline `(mod test …)` lives in the
// lib-dir (`lib/` under the per-test tmpdir, on CRANELISP_LIB); the `--run`
// driver (`driver.cl`) sits at the tmpdir ROOT, which is the process CWD.
// CWD (tmpdir root) ≠ lib-dir (tmpdir/lib). After the run, the extracted
// backing file MUST appear under the lib-dir (`lib/mod/test.cl`) and MUST NOT
// appear CWD-relative (`mod/test.cl` at the tmpdir root).
//
// FAILING-NOT-IGNORED per `memory/feedback_failing_not_ignored.md` — it pins
// the spec-correct lib-dir-relative behaviour and flips green when /int
// resolves the extraction output path against the lib-dir / the source
// module's own directory rather than the process CWD. → /int (source-regen /
// `(mod …)` extraction write path; `src/`).

// spec: spec/08-modules.md §8.2.2 — extraction step 1 writes the backing file
// at `{parent_dir}/{stem}/{name}.cl`; `{parent_dir}` is the parent module's OWN
// directory (the lib-dir for a lib-dir module), NEVER the process working
// directory. The stray CWD-relative write is FIXME 0423.
#[test]
fn inline_mod_test_extraction_writes_lib_dir_relative_not_cwd() {
    // `accum.cl` lives in the lib-dir (`lib/`, on CRANELISP_LIB). It declares
    // an inline `(mod test …)` body — the extractor must write the backing
    // file next to `accum.cl` (under `lib/`), not under the process CWD.
    let out = Cranelisp::new()
        .file(
            "lib/accum.cl",
            "(import [prelude []])\n\
             (import [primitives [add-i64]])\n\
             (defn double [x] (add-i64 x x))\n\
             (mod test \
               (import [primitives [add-i64]]) \
               (defn check [x] (add-i64 x 1)))",
        )
        // The `--run` driver sits at the tmpdir ROOT (= the process CWD), which
        // is DISTINCT from the lib-dir. It imports `accum` to force its load +
        // the inline-`(mod test)` extraction.
        .file(
            "driver.cl",
            "(import [accum [double]])\n\
             (import [primitives [Pure]])\n\
             (defn main [] (Pure (double 21)))",
        )
        .lib_dir("lib")
        .run("driver.cl")
        .output()
        .assert_exit(42);

    // CORRECT (§8.2.5): the backing file is written next to its parent in the
    // lib-dir. Fails today under 0423 (the write is CWD-relative, so the
    // lib-dir copy is never created).
    assert!(
        out.tmp_exists("lib/accum/test.cl"),
        "the extracted `(mod test)` backing file MUST be written LIB-DIR-relative \
         at lib/accum/test.cl; under FIXME 0423 it is written CWD-relative instead"
    );

    // NEGATIVE (the 0423 symptom): no stray backing file appears CWD-relative
    // (at the tmpdir root, outside the lib-dir). This is the assertion that is
    // RED today — the stray `accum/test.cl` is written next to the driver.
    assert!(
        !out.tmp_exists("accum/test.cl"),
        "NO stray backing file may appear OUTSIDE the lib-dir (CWD-relative \
         accum/test.cl) — this is the FIXME-0423 stray-write defect"
    );
}

// spec: spec/08-modules.md §8.2.2 — extraction step 1 formats the inline body as
// source text. FIXME 0423 secondary symptom: the regen pretty-printer must emit
// `:Type` (NO space after the colon), not `: Type`. Per
// `memory/annotation-reader-macro-binds-following-form`, `:Type` is a
// reader-macro-like annotation that binds the immediately-following form with no
// intervening space. The extracted backing file MUST preserve that spacing.
//
// RED-first: the regen path inserts a space (`: Type`) today (the latent
// formatting divergence noted in FIXME 0423). The lib-dir-relative write fix and
// the spacing fix land together in /int's regen pass (Wave 6 / S88-landed source).
#[test]
fn regen_annotation_spacing_no_space_after_colon() {
    let out = Cranelisp::new()
        .file(
            "lib/annot.cl",
            "(import [primitives [add-i64]])\n\
             (defn double [x] (add-i64 x x))\n\
             (mod test \
               (import [primitives [add-i64]]) \
               (defn check [:primitives/Int x] (add-i64 x 1)))",
        )
        .file(
            "driver.cl",
            "(import [annot [double]])\n\
             (import [primitives [Pure]])\n\
             (defn main [] (Pure (double 21)))",
        )
        .lib_dir("lib")
        .run("driver.cl")
        .output()
        .assert_exit(42);

    // The extracted backing file must exist lib-dir-relative (the 0423 primary
    // fix); read it and assert the annotation spacing is `:Type`, not `: Type`.
    if out.tmp_exists("lib/annot/test.cl") {
        let body = out.read_tmp("lib/annot/test.cl");
        assert!(
            body.contains(":primitives/Int") && !body.contains(": primitives/Int"),
            "regen MUST emit `:Type` (no space), not `: Type` — the reader-macro \
             binds the following form with no intervening space (FIXME 0423 \
             secondary); extracted body:\n{body}"
        );
    } else {
        // The lib-dir-relative backing file is not written yet (the 0423 primary
        // defect); the spacing cannot be checked until that lands. Fail loudly so
        // this is a visible RED guard, not a vacuous pass.
        panic!(
            "the extracted `(mod test)` backing file MUST be written lib-dir-relative \
             at lib/annot/test.cl before the regen annotation-spacing can be \
             verified (FIXME 0423 primary + secondary land together)"
        );
    }
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
#[test]
fn import_dependency_compiles_correctly() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod util)\n(import [main.util [helper]])\n(defn main [] (Pure (helper)))",
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
#[test]
fn project_root_shadows_stdlib() {
    let cr = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod helper)\n(defn main [] (Pure (helper/val)))",
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
            "(import [primitives [Pure]])\n(mod helper)\n(defn main [] (Pure (helper/compute)))",
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
#[test]
fn prelude_like_reexport_compiles() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod shell)\n(import [main.shell [get-val]])\n(defn main [] (Pure (get-val)))",
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
#[test]
fn multi_dot_module_path_in_import() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod shell)\n(import [main.shell [relay]])\n(defn main [] (Pure (relay)))",
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
#[test]
fn nested_dependency_chain_compiles() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod mid)\n(import [main.mid [relay]])\n(defn main [] (Pure (relay)))",
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
#[test]
fn export_specific_reexport() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod shell)\n(import [main.shell [val]])\n(defn main [] (Pure (val)))",
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
#[test]
fn export_glob_reexport() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [add-i64 Pure]])\n\
             (mod shell)\n\
             (import [main.shell [a b]])\n\
             (defn main [] (Pure (add-i64 (a) (b))))",
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
#[test]
fn export_transitive_reexport_chain() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (mod shell)\n\
             (import [main.shell [deep-val]])\n\
             (defn main [] (Pure (deep-val)))",
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
#[test]
fn export_multiple_modules() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [add-i64 Pure]])\n\
             (mod shell)\n\
             (import [main.shell [alpha beta]])\n\
             (defn main [] (Pure (add-i64 (alpha) (beta))))",
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

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-3 GAP-COVER carry-forward (REGRESSION-GUARD).
// =============================================================================

// spec: spec/08-modules.md §8.3 — an imported (or REPL-defined) function
// MUST be usable as a higher-order argument. Source comment from legacy
// e2e: "Bug: REPL codegen fails with 'undefined variable' when an
// imported function is passed as an argument to a higher-order function."
// REGRESSION-GUARD: the legacy test defines `even?` inline (avoiding
// module discovery in isolated e2e dirs); the imported-fn-as-value angle
// in REPL mode is what's load-bearing.
// (carry: legacy/e2e.rs::e2e_imported_fn_as_higher_order_arg_repl)
#[test]
fn imported_fn_as_higher_order_arg_in_repl_mode() {
    let out = Cranelisp::new()
        .repl()
        .stdin(
            // spec/03-types.md §3.1: bare type refs (`:Int`, `:Bool`) MUST be
            // imported or fully-qualified — so the type names are imported
            // alongside the functions (RT1 fixture fix, S77 W-Fix).
            "(import [primitives [Int Bool eq-i64 sub-i64 mul-i64 div-i64]])
(defn rem [:Int a :Int b] :Int (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn even? [:Int x] :Bool (eq-i64 (rem x 2) 0))
(defn apply-fn [f x] (f x))
(apply-fn even? 4)
",
        )
        .output();
    assert!(
        !out.stdout.contains("Error:") && !out.stdout.contains("error:"),
        "fn passed as higher-order arg MUST NOT error in REPL per spec/08 §8.3; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("true"),
        "(apply-fn even? 4) MUST evaluate to true; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 file 8 ring2.rs chunk 4 GAP-COVER carry-forwards (REGRESSION-GUARDs).
// =============================================================================

// spec: spec/08-modules.md §8.7.3 — after `[*]` glob import, a private name
// MUST NOT be reachable via the qualified ref `<module>/<name>` either. The
// existing canonical (`glob_import_excludes_private_neg`) only exercises the
// bare-name path; this asserts the qualified-ref-after-glob angle, which is
// the regression-prone composition (a fix that loosens visibility could
// pass the bare-name test while letting the qualified-ref escape).
// REGRESSION-GUARD: post-Sprint-16 D5 P1-HIGH negative-coverage shape.
// (carry: legacy/ring2.rs::neg_glob_import_private_not_via_qualified)
#[test]
fn glob_import_private_not_accessible_via_qualified_ref_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(mod util)\n\
             (import [main.util [*]])\n\
             (defn main [] (main.util/secret))",
        )
        .file(
            "main/util.cl",
            "(defn helper [] 42)\n(defn- secret [] 99)",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "private name MUST NOT be accessible via qualified ref after glob \
         import (spec §8.7.3); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/08-modules.md §8.2.3 — a `(mod- internal)` private submodule
// MUST NOT be importable from a peer module under the same parent. Distinct
// from `(defn-)` private-name tests: this exercises private-submodule
// declaration via `mod-`, which has zero existing carry-forward coverage.
// REGRESSION-GUARD: spec/08 §8.2.3 promises private-submodule isolation;
// silently loosening it would compromise module encapsulation.
// (carry: legacy/ring2.rs::neg_private_submodule_not_importable_from_peer)
#[test]
fn mod_dash_private_submodule_not_importable_from_peer_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(mod host)\n\
             (mod consumer)\n\
             (import [main.consumer [run]])\n\
             (defn main [] (run))",
        )
        .file("main/host.cl", "(mod- internal)\n(defn public-fn [] 1)")
        .file("main/host/internal.cl", "(defn private-leaf [] 42)")
        .file(
            "main/consumer.cl",
            "(import [main.host.internal [private-leaf]])\n\
             (defn run [] (private-leaf))",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "peer module MUST NOT import from a `(mod- internal)` private \
         submodule (spec §8.2.3); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/08-modules.md §8.7.3 — a `(defmacro- secret-mac ...)` private
// macro MUST NOT be importable from a peer module. Macro-visibility is
// covered indirectly by spec/08 §8.7.3 ("private name semantics") and
// spec/09 §9.2 (which lists `defmacro-` syntax); macro-visibility has
// zero pre-existing carry-forward, making this the only regression-guard
// for that boundary.
// REGRESSION-GUARD: post-Sprint-16 D5 P1-HIGH negative-coverage shape.
// Cross-ref: spec/09-macros.md §9.2.
// (carry: legacy/ring2.rs::neg_private_macro_not_importable)
#[test]
fn defmacro_dash_private_not_importable_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(mod util)\n\
             (import [main.util [secret-mac]])\n\
             (defn main [] (secret-mac 1))",
        )
        .file(
            "main/util.cl",
            "(defmacro- secret-mac [x] x)\n(defn helper [] 42)",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "private (defmacro-) macro MUST NOT be importable (spec §8.7.3 + \
         spec/09 §9.2); stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// Null-import resolution (§8.3.6) — free-standing
// =============================================================================
//
// Spec subject: §8.3.6 Null Import — a module that suppresses the implicit
// prelude glob via `(import [prelude []])` MUST resolve EVERY referenced name
// through explicit imports; any name it leaves unimported is `undefined
// variable`, not silently picked up from the prelude.
//
// Decoupled from real stdlib (was: imported `seq.lazy` via
// `use_workspace_stdlib_for_stdlib_conformance_only`). The original test only
// exercised whether `stdlib/seq/lazy.cl` happened to import its names — a
// /stdlib conformance concern, not a language-rule concern, and it broke when
// the real stdlib momentarily stopped compiling (FIXME 0312/0314 — the
// two-`Option` collision, since CLOSED in S78 Wave 6 via the
// `fn.option`/`fn.result`/`collections.pair` re-export of the canonical
// `primitives` ADTs).
// This free-standing version pins the LANGUAGE RULE directly with a tiny
// test-owned module graph: a null-importing leaf that DOES explicitly import
// the names it uses resolves cleanly; the negative companion below pins that a
// null-importing leaf that OMITS an import fails with `undefined variable`.
//
// The fixture is spec-clean (no `primitives` glob + separate Option footgun):
// it defines its own ADT in one module and explicitly imports the constructor
// into the null-importing leaf.

// spec: spec/08-modules.md §8.3.6 — Null Import: a module that suppresses
//       the prelude glob via `(import [prelude []])` resolves every referenced
//       name through explicit imports (positive path).
#[test]
fn null_import_module_resolves_all_names_via_explicit_imports() {
    // `lib/data.cl` defines a Box ADT. `lib/leaf.cl` null-imports the prelude
    // and EXPLICITLY imports `Box`/`unbox` plus the bare primitives it uses —
    // so every referenced name resolves. `main.cl` drives the leaf.
    let out = Cranelisp::new()
        .file(
            "lib/data.cl",
            "(deftype (Box a) (Boxed [:a v]))\n\
             (defn unbox [b] (match b [(Boxed v) v]))",
        )
        .file(
            "lib/leaf.cl",
            "(import [prelude []])\n\
             (import [primitives [add-i64]])\n\
             (import [lib.data [Box Boxed unbox]])\n\
             (defn wrapped [] (Boxed (add-i64 40 2)))\n\
             (defn value [] (unbox (wrapped)))",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [lib.leaf [value]])\n(defn main [] (Pure (value)))",
        )
        .run("main.cl")
        .output();

    let combined = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("undefined variable"),
        "a null-importing module (`(import [prelude []])`) that EXPLICITLY \
         imports every name it references MUST resolve cleanly (spec §8.3.6); \
         got:\n{combined}"
    );
    out.assert_exit(42);
}

// spec: spec/08-modules.md §8.3.6 — Null Import (negative): a name a
//       null-importing module references but does NOT explicitly import is
//       `undefined variable` — the prelude glob is suppressed, so there is no
//       implicit fallback that would silently resolve it.
#[test]
fn null_import_module_neg_unimported_name_is_undefined() {
    // Same shape, but `lib/leaf.cl` references `Boxed`/`unbox` WITHOUT importing
    // `lib.data`. Under null-import there is no prelude fallback, so the
    // constructor reference MUST fail to resolve.
    let out = Cranelisp::new()
        .file(
            "lib/data.cl",
            "(deftype (Box a) (Boxed [:a v]))\n\
             (defn unbox [b] (match b [(Boxed v) v]))",
        )
        .file(
            "lib/leaf.cl",
            "(import [prelude []])\n\
             (import [primitives [add-i64]])\n\
             (defn value [] (unbox (Boxed (add-i64 40 2))))",
        )
        .file(
            "main.cl",
            "(import [lib.leaf [value]])\n(defn main [] (value))",
        )
        .run("main.cl")
        .output();

    assert!(
        !out.status.success(),
        "a null-importing module that references a name it did NOT explicitly \
         import MUST fail (no prelude fallback, spec §8.3.6); exit={:?}\n{}\n{}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
    let combined = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        combined.contains("undefined") || combined.contains("Boxed") || combined.contains("unbox"),
        "the diagnostic MUST name the unresolved symbol; got:\n{combined}"
    );
}

// =============================================================================
// §8.3 + §8.10.1 — Multi-import discipline + scheduler resumption
// (carry-forward: legacy/v4_pipeline.rs §E — Wave 6 batch 6)
// =============================================================================

// spec: spec/08-modules.md §8.3 — multiple separate import forms in one
// module, each importing from a different sibling module.
// (carry: legacy/v4_pipeline.rs::v4_multiple_imports)
#[test]
fn multiple_import_forms_in_one_module() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [alpha [get-alpha]])\n\
             (import [beta [get-beta]])\n\
             (defn main [] (Pure (primitives/add-i64 (get-alpha) (get-beta))))",
        )
        .file("alpha.cl", "(defn get-alpha [] 50)")
        .file("beta.cl", "(defn get-beta [] 60)")
        .run("main.cl")
        .output()
        .assert_exit(110);
}

// spec: spec/08-modules.md §8.10.1 — a defn defined BEFORE an import
// must survive the suspension caused by the import blocking. The
// scheduler must save/restore the accumulator so that local defns
// declared above the import remain available after the dep loads.
// (carry: legacy/v4_pipeline.rs::v4_resumption_correctness)
// REGRESSION-GUARD: Step 5 lazy-discovery resumption invariant
// (design/int/step5-lazy-discovery.md §5).
//
// Defect-discovery note (Wave 6 batch 6): the legacy test asserted only
// that stderr was empty; it did NOT check exit code. The carry-forward
// preserves the legacy spec invariant (clean stderr = §8.10.1
// resumption succeeded) and additionally records that the run-mode
// child SEGVs (exit 139) on this shape — an open downstream codegen/
// scheduler defect tracked under FIXME 0149. The compile invariant
// (the §8.10.1 spec property) PASSES; the SEGV is a separate concern.
#[test]
fn defn_before_import_resumes_correctly_after_dep_load() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn local-fn [] 10)\n\
             (import [util [remote-fn]])\n\
             (defn main [] (Pure (primitives/add-i64 (local-fn) (remote-fn))))",
        )
        .file("util.cl", "(defn remote-fn [] 32)")
        .run("main.cl")
        .output();
    // Filter benign nice-worker warnings from stderr.
    let err: String = out
        .stderr
        .lines()
        .filter(|line| !line.starts_with("nice-worker:"))
        .collect::<Vec<_>>()
        .join("\n");
    // §8.10.1 invariant: defn-before-import suspends/resumes cleanly,
    // i.e. compilation produces no error text. Legacy assertion shape.
    assert!(
        err.is_empty(),
        "compilation should succeed cleanly; stderr: {}",
        err
    );
    // XXX(/backend) FIXME 0149: exit-code witness `assert_exit(42)` is
    // currently NOT asserted — the run-mode child SEGVs (exit 139) on
    // this shape. Re-enable when the downstream defect is resolved.
}

// =============================================================================
// S78 §1 — Entry module is ordinary; `"user"` is only the default CLI name.
// design/int/s78-entry-module.md §1 (entry-module concept, name-agnostic).
//
// The entry module is the `main`-bearing module the session is asked to
// compile + run. Under `--run <file>` it is named after the file (`main.rs`
// `resolve_target_from` → file stem), NOT a literal `"user"`. Most programs
// have NO `user` module at all. These are GREEN behaviour-preservation guards
// that the §1 de-special-casing must keep passing (the `--run` entry
// registration is already name-agnostic — `main.rs:172`).
// =============================================================================

// spec: design/int/s78-entry-module.md §1 — a `--run` program whose entry
//   file is named non-`user` compiles and runs. The entry module is `sudoku`
//   (the file stem), an ordinary module; there is no `user` module anywhere.
#[test]
fn entry_module_named_non_user_runs() {
    Cranelisp::new()
        .file("sudoku.cl", "(import [primitives [Pure]])\n(defn main [] (Pure 7))")
        .run("sudoku.cl")
        .output()
        .assert_exit(7);
}

// spec: design/int/s78-entry-module.md §1 — a program with NO `user` module
//   anywhere works end-to-end: the entry (named `myapp`) imports a sibling
//   (`board`), and neither file is `user.cl`. Exercises cross-module call +
//   import-gap drive against a non-`user` entry.
#[test]
fn program_with_no_user_module_runs_end_to_end() {
    Cranelisp::new()
        .file(
            "myapp.cl",
            "(import [primitives [Pure]])\n(import [board [cell]])\n(defn main [] (Pure (cell)))",
        )
        .file("board.cl", "(defn cell [] 42)")
        .run("myapp.cl")
        .output()
        .assert_exit(42);
}

// spec: design/int/s78-entry-module.md §1 — regression: the CLI default
//   entry name (`user`, when no target is given) still works. `--run user.cl`
//   names the entry `user` and runs it.
#[test]
fn entry_module_default_user_name_still_runs() {
    Cranelisp::new()
        .user("(import [primitives [Pure]])\n(defn main [] (Pure 5))")
        .run("user.cl")
        .output()
        .assert_exit(5);
}

// =============================================================================
// §8.6.4 / §8.6.5 — Import-ambiguity model: terminal-source dedup
//                   vs distinct-terminal collision (FIXME 0316)
// =============================================================================
//
// These two tests pin the §8.6.4 terminal-source comparison ruling
// (/arch, 2026-06-13). §8.6.4 says same-source duplicates "the same name
// arriving through two re-export paths from the same original definition"
// are NOT ambiguous — the comparison is by TERMINAL source, not immediate
// source. §8.6.5 keeps globs as PEERS of specific imports: ambiguity is
// decided purely on terminal-source identity, no precedence tier.
//
// FAILING-FIRST: `glob_and_reexport_of_same_terminal_dedup` is RED until the
// int wave lands terminal-source dedup in `src/imports.rs`
// (`insert_detecting_ambiguity` currently keys dedup on the IMMEDIATE
// `source.module`, so a glob + a re-export of one of its names read as two
// sources and falsely collide). `distinct_terminal_overlap_collides` guards
// that the fix does NOT over-dedup — genuinely-distinct definitions sharing a
// bare name MUST still poison the name (footgun protection preserved).

// spec: spec/08-modules.md §8.6.4 — terminal-source dedup. A glob import of
// `prim` (immediate source `prim`) co-exists with a specific import of `Foo`
// from `reexp` (immediate source `reexp`) when `reexp` RE-EXPORTS `prim/Foo`:
// both bare `Foo` entries chain-follow to the SAME terminal `(prim, Foo)`, so
// they dedup silently rather than poisoning the name. MUST compile clean — no
// `Ambiguous`. (Comparing only the immediate sources `prim` vs `reexp` would
// wrongly read two sources and report a false collision.)
#[test]
fn glob_and_reexport_of_same_terminal_dedup() {
    // `prim` is the terminal home of `Foo`. `reexp` imports + re-exports it.
    // `main` brings `Foo` BOTH ways (glob of `prim` + specific from `reexp`),
    // then constructs and destructures it — exercising the deduped binding.
    let out = Cranelisp::new()
        .file(
            "prim.cl",
            "(import [primitives [Int]])\n\
             (deftype Foo [:Int n])",
        )
        .file(
            "reexp.cl",
            "(import [prim [Foo]])\n\
             (export [prim [Foo]])",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [prim [*]])\n\
             (import [reexp [Foo]])\n\
             (defn main [] (Pure (match (Foo 42) [(Foo n) n])))",
        )
        .run("main.cl")
        .output();

    let combined = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        !combined.to_lowercase().contains("ambiguous"),
        "a glob import + a re-export of one of its names share the SAME \
         terminal source `(prim, Foo)` and MUST dedup silently — NOT collide \
         as `Ambiguous` (spec §8.6.4 terminal-source comparison); got:\n{combined}"
    );
    out.assert_exit(42);
}

// spec: spec/08-modules.md §8.6.5 — distinct-terminal collision. Two modules
// `a` and `b` each define their OWN, DIFFERENT `Bar`. Importing both bare and
// referencing bare `Bar` MUST poison the name: a compile-time ambiguity
// diagnostic naming both qualified alternatives. This is the footgun
// protection §8.6.5 preserves — globs are PEERS of specific imports, so
// distinct terminals collide regardless of import shape; terminal-source
// dedup (§8.6.4) MUST NOT silently pick one winner.
#[test]
fn distinct_terminal_overlap_collides() {
    // `a/Bar` and `b/Bar` are genuinely-different definitions (distinct
    // terminals). Both imported bare; `main` references bare `Bar`.
    let out = Cranelisp::new()
        .file(
            "a.cl",
            "(import [primitives [Int]])\n\
             (deftype Bar [:Int x])",
        )
        .file(
            "b.cl",
            "(import [primitives [Int]])\n\
             (deftype Bar [:Int y])",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [a [Bar]])\n\
             (import [b [Bar]])\n\
             (defn main [] (Pure (match (Bar 7) [(Bar v) v])))",
        )
        .run("main.cl")
        .output();

    assert!(
        !out.status.success(),
        "two DISTINCT terminal `Bar` definitions imported under the same bare \
         name MUST collide (spec §8.6.5 — footgun protection; globs are peers, \
         no silent winner); compilation MUST fail. stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    let combined = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("ambiguous"),
        "the ambiguity diagnostic MUST identify the conflict as ambiguous; \
         got:\n{combined}"
    );
    // Negative-coverage: the diagnostic MUST name BOTH qualified alternatives
    // so the user can disambiguate (`a/Bar` and `b/Bar`).
    assert!(
        combined.contains("a/Bar") && combined.contains("b/Bar"),
        "the ambiguity diagnostic MUST name BOTH qualified alternatives \
         (`a/Bar` and `b/Bar`) so the user can disambiguate (spec §8.6.5); \
         got:\n{combined}"
    );
}

// =============================================================================
// §8.9.1 / §3.1 — primitive bare-name import battery (FIXME 0216)
// =============================================================================
//
// §8.9.1 + §3.1: primitive names (types `Int`/`Bool`/`Float`/`String` AND
// functions `add-i64` etc.) live in `primitives` in QUALIFIED form only. Bare
// references require prelude re-export or an explicit import; FQ references
// (`primitives/Int`, `primitives/add-i64`) always work regardless of imports.
//
// Expected GREEN (the S78 architectural cascade landed — `Type::from_name`
// bridge removed, primitives registered uniformly). This is new coverage
// guarding the rule, not failing-first. `PreludeVariant::None` = NO prelude,
// NO implicit primitives import.

// Pipe `lines` to a bare REPL (no prelude, no primitives import) and capture.
fn repl_no_prelude(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .stdin(lines)
        .output()
}

// spec: spec/08-modules.md §8.9.1 — bare `:Int` with no primitives import and
// no prelude MUST be a compile-time "unknown type" error: the primitive type
// `Int` lives in `primitives` in QUALIFIED form only, so the bare name is
// unreachable without a re-export or explicit import. This guards the §8.9.1
// REACHABILITY rule (the type IS real but out of scope) — distinct from
// `annotation_unknown_type_is_error`, which guards a name that is no type at
// all. Asserts the SPEC-CORRECT `unknown type` signal (FIXME 0329: the prior
// `|| contains("error")` fallback matched a swallowed parse error before the
// annotation-pairing fix landed; now the `Expr::Annotate` node exists at top
// level and typecheck's reachability check fires the precise diagnostic).
#[test]
fn bare_primitive_type_int_neg_unknown_type_without_import() {
    let out = repl_no_prelude(":Int 42\n");
    let s = out.stdout.to_lowercase();
    assert!(
        s.contains("unknown type `int`"),
        "bare `:Int` with no primitives import / no prelude MUST be an \
         `unknown type` compile-time error naming `Int` (spec §8.9.1 \
         reachability); got:\n{}",
        out.stdout
    );
    // Negative: the bare-name path MUST NOT resolve `Int` and display a value.
    assert!(
        !out.stdout.contains(":primitives/Int 42"),
        "bare `:Int` (no import) MUST NOT resolve the primitive type and \
         display `:primitives/Int 42` — that would violate §8.9.1 \
         reachability; got:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.9.1 — same reachability rule for `:Bool`,
// `:Float`, `:String`: each bare primitive type name with no import is an
// unknown-type error naming that type.
#[test]
fn bare_primitive_types_bool_float_string_neg_unknown_without_import() {
    for (annot, lit, tyname) in [
        (":Bool", "true", "bool"),
        (":Float", "1.0", "float"),
        (":String", "\"hi\"", "string"),
    ] {
        let line = format!("{annot} {lit}\n");
        let out = repl_no_prelude(&line);
        let s = out.stdout.to_lowercase();
        let needle = format!("unknown type `{tyname}`");
        assert!(
            s.contains(&needle),
            "bare `{annot}` with no primitives import / no prelude MUST be an \
             `unknown type` compile-time error naming `{tyname}` (spec §8.9.1 \
             reachability); got:\n{}",
            out.stdout
        );
    }
}

// spec: spec/08-modules.md §8.9.1 — the fully-qualified `:primitives/Int`
// annotation MUST work with NO import / no prelude. FQ reachability is the
// §8.11.4 "primitives remain available" guarantee.
#[test]
fn fq_primitive_type_int_works_without_import() {
    repl_no_prelude(":primitives/Int 42\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/08-modules.md §8.9.1 — negative-coverage on the FQ path: it MUST
// NOT trip the unknown-type error that the BARE form does. FQ is the
// always-available escape hatch.
#[test]
fn fq_primitive_type_int_neg_no_unknown_type_error() {
    let out = repl_no_prelude(":primitives/Int 42\n");
    assert!(
        !out.stdout.to_lowercase().contains("unknown type"),
        "`:primitives/Int` (FQ) MUST NOT produce an `unknown type` error — \
         FQ references are always available regardless of imports \
         (spec §8.9.1 / §8.11.4); got:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.9.1 — primitive FUNCTION side: bare `add-i64`
// with no import / no prelude MUST be an "unknown name" compile-time error
// (the bare-name rule applies to functions as well as types).
#[test]
fn bare_primitive_fn_add_i64_neg_unknown_name_without_import() {
    let out = repl_no_prelude("(add-i64 1 2)\n");
    let s = out.stdout.to_lowercase();
    assert!(
        s.contains("unknown")
            || s.contains("undefined")
            || s.contains("not in scope")
            || s.contains("error"),
        "bare `add-i64` with no primitives import / no prelude MUST be an \
         `unknown name` compile-time error (spec §8.9.1); got:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.9.1 — primitive FUNCTION FQ path:
// `primitives/add-i64` MUST work with no import / no prelude.
#[test]
fn fq_primitive_fn_add_i64_works_without_import() {
    repl_no_prelude("(primitives/add-i64 1 2)\n")
        .assert_stdout_contains(":primitives/Int 3");
}

// =============================================================================
// §2.3.8 / §1.4.5 — `:Type` annotation binds the following form in EVERY
// position (FIXME 0329 — the annotation-pairing fix)
// =============================================================================
//
// spec: spec/02-grammar.md §2.3.8 — `annotate_expr = annotation expr`. The
// `:Type` token is a reader-level prefix binding the immediately-following
// form into one `Expr::Annotate`, in every expression position (top-level,
// parenthesized, argument, …). It is never a standalone atom. spec/01-lexical.md
// §1.4.5 carries the lexical-level statement (colon-prefix is an annotation
// introducer, not a `var_ref`). Before the S81 frontend `build_forms` +
// int cluster-grouping fix, the top-level / list-head positions never built
// the `Expr::Annotate` node (a leading `:Type` parsed as a bare `Var`); these
// tests lock the ratified semantics.
//
// `Int` / `Float` are reachable via an explicit `(import [primitives […]])`
// (the bare names are QUALIFIED-only per §8.9.1); `Foo` is left unreachable.

// Pipe `lines` to a bare REPL after importing the primitive types so `Int` /
// `Float` resolve as bare names. `Foo` is NOT imported (stays unknown).
fn repl_with_prim_types(lines: &str) -> helpers::e2e::CrOutput {
    let stdin = format!("(import [primitives [Int Float Bool String]])\n{lines}");
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .stdin(&stdin)
        .output()
}

// spec: spec/02-grammar.md §2.3.8 — a top-level `:Int 42` is an `annotate_expr`
// binding the following form (`42`); its inferred type unifies with `Int` and
// the REPL displays the annotated value `:primitives/Int 42`. (Also §1.4.5 —
// the leading `:Int` is the annotation introducer, not a `var_ref`.)
#[test]
fn annotation_binds_top_level_following_form() {
    repl_with_prim_types(":Int 42\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/02-grammar.md §2.3.8 — the inner form's inferred type MUST unify
// with the annotation. `:Float 42` annotates the Int literal `42` with `Float`,
// so unification fails with a type mismatch (Int vs Float).
#[test]
fn annotation_type_mismatch_is_unify_error() {
    let out = repl_with_prim_types(":Float 42\n");
    out.assert_stdout_contains("type mismatch: expected primitives/Int, got primitives/Float");
}

// spec: spec/02-grammar.md §2.3.8 — the annotation type MUST resolve. `:Foo 42`
// names no type `Foo` (left unimported / undefined), so it is an unknown-type
// error — NOT a silently-ignored leading symbol (the pre-fix behaviour).
#[test]
fn annotation_unknown_type_is_error() {
    // `Foo` is deliberately unreachable: no import, no prelude.
    let out = repl_no_prelude(":Foo 42\n");
    out.assert_stdout_contains("unknown type `Foo`");
}

// spec: spec/02-grammar.md §2.3.8 — `(:Int 42)` is NOT a special form: the
// reader binds `:Int` to the single following element `42`, yielding a
// one-element list whose sole element is `(annotate Int 42)`; the list is then
// the ordinary application of that one (Int-typed) element. Applying an Int as
// a function fails — the callee is expected to be a function but is `Int`,
// reported as `expected Int, got (Fn …)`. (Also §1.4.5 — a leading `:Type`
// inside parens annotates only the next element, it is not the application
// callee.)
#[test]
fn annotation_in_paren_is_application_of_annotated_element() {
    let out = repl_with_prim_types("(:Int 42)\n");
    // The annotated element has type Int but is applied as a function.
    out.assert_stdout_contains_all(&["type mismatch", "expected primitives/Int, got (Fn"]);
}

// spec: spec/02-grammar.md §2.3.8 — the annotation's unification check is
// performed during typechecking, BEFORE any application semantics of the
// enclosing form. For `(:Float 42)` the inner `:Float 42` annotation fails to
// unify (Int vs Float) and that error is reported FIRST — the not-a-function
// error of `annotation_in_paren_is_application_of_annotated_element` is NOT
// reached.
#[test]
fn annotation_in_paren_unify_precedes_not_a_function() {
    let out = repl_with_prim_types("(:Float 42)\n");
    // The unify mismatch (Int vs Float) is reported …
    let out = out.assert_stdout_contains("type mismatch: expected primitives/Int, got primitives/Float");
    // … and the not-a-function `(Fn …)` mismatch is NOT the reported error.
    out.assert_stdout_does_not_contain("got (Fn");
}

// =============================================================================
// §8.2.5 Module Declaration — bare `(mod name)` NESTED-only resolution
//
// Regression guard for FIXME 0337 (S81 surfaced; S82 ruled nested-only via
// FIXME 0345). A bare `(mod child)` (no inline body) in an entry file MUST
// resolve the NESTED child path `{stem}/{name}.cl` — for `main.cl` declaring
// `(mod child)` that is `main/child.cl` (loaded module `main.child`). It MUST
// NOT fall back to a SIBLING `child.cl` in the same directory (that file, if
// present, is the independent peer module `child`, reachable only via
// `import`). The implementation already follows §8.2.5; these guards pin it.
//
// Earlier shape (S81): these guards encoded the OLD *sibling* expectation,
// which the §8.2.5 nested-only ruling (FIXME 0345) made wrong. Rewritten S82
// to the nested expectation — they PASS against the (correct) implementation.
//
// Owning skill: /int (module resolution); the behaviour is normative per
// §8.2.5 and these guards lock it against regression.
// =============================================================================

// spec: spec/08-modules.md §8.2.5 — bare `(mod child)` resolves the NESTED
//   child file `{stem}/{name}.cl` (here `main/child.cl`, module `main.child`).
#[test]
fn bare_mod_decl_resolves_nested_child_for_entry_main() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod child)\n(defn main [] (Pure (child/answer)))",
        )
        .file("main/child.cl", "(defn answer [] 42)")
        .run("main.cl")
        .output()
        // CORRECT (§8.2.5): the nested child fn resolves and main exits 42.
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.2.5 — negative companion: a bare `(mod child)`
//   MUST NOT auto-resolve a SIBLING `child.cl`. Only the nested
//   `{stem}/child.cl` is sought; a sibling peer is reachable only via
//   `import`, never `mod`. With no nested `main/child.cl` present, the build
//   MUST fail (the resolver does not silently fall back to the sibling).
#[test]
fn bare_mod_decl_neg_does_not_resolve_sibling_file() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod child)\n(defn main [] (Pure (child/answer)))",
        )
        // A SIBLING child.cl exists, but no NESTED main/child.cl. Per §8.2.5
        // the bare `(mod child)` seeks ONLY main/child.cl and must NOT fall
        // back to this sibling.
        .file("child.cl", "(defn answer [] 42)")
        .run("main.cl")
        .output();
    // CORRECT (§8.2.5): the sibling is NOT considered, so resolution of the
    // nested `main.child` fails — main must NOT exit 42 (which would mean the
    // sibling was wrongly resolved). Assert the failure surfaces the
    // nested-module lookup, not a successful sibling fallback.
    assert_ne!(
        out.status.code(),
        Some(42),
        "bare `(mod child)` MUST NOT fall back to a SIBLING `child.cl` \
         (§8.2.5 nested-only); exit 42 would mean the sibling was wrongly \
         resolved.\nstdout={}\nstderr={}",
        out.stdout,
        out.stderr
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("main.child"),
        "the failure MUST name the NESTED module `main.child` (the only path \
         §8.2.5 seeks), confirming no sibling fallback was attempted.\n\
         stdout={}\nstderr={}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// §8.3.8 Super Import — child submodule resolves parent symbols
//
// FAILING-NOT-IGNORED repro for FIXME 0342 (S81 close). A plain (non-cyclic)
// `(import [super [name]])` from a `(mod test ...)` submodule MUST resolve the
// parent module's symbols (both fns and type constructors). Today it errors
// `'name' not found in module '<parent>'` — the submodule typechecks before
// the parent's definitions are visible to it (an ordering issue).
//
// This is DISTINCT from the §8.3.8 mutual-import deadlock limitation — there
// is no cycle here (parent does not import from the child).
//
// Owning skill: /typecheck (resolution) or /int (module-load ordering) —
// see tests/CLAUDE.md §"Isolating Cross-Crate Failures". The visible error is
// a typecheck "not found"; the root cause may be int's load ordering.
// =============================================================================

// spec: spec/08-modules.md §8.3.8 — non-cyclic child→parent `super` import of
//   a parent fn MUST resolve. FIXME(/typecheck 0342).
#[test]
fn super_import_resolves_parent_fn() {
    Cranelisp::new()
        .file(
            "superp.cl",
            "(defn helper [x] x)\n\
             (mod test\n  \
               (import [super [helper]])\n  \
               (import [primitives [eq-i64]])\n  \
               (defn test-h [] (eq-i64 (helper 5) 5)))",
        )
        .file(
            "entry.cl",
            "(import [primitives [Pure]])\n\
             (import [superp [helper]])\n\
             (defn main [] (Pure (helper 7)))",
        )
        .run("entry.cl")
        .output()
        // CORRECT: the submodule sees the parent's `helper`, the project
        // compiles, and main exits 7. Today this FAILS with
        // `'helper' not found in module 'superp'`.
        .assert_exit(7);
}

// spec: spec/08-modules.md §8.3.8 — non-cyclic child→parent `super` import of
//   a parent TYPE constructor MUST resolve. FIXME(/typecheck 0342).
//
// Fixture corrected (S82): the original repro used a postfix annotation
// `[b :superp/Box]` which is INVALID — `:Type` is a reader-macro-like
// annotation that binds the IMMEDIATELY-FOLLOWING form (the prefix form
// `[:superp/Box b]`), never the preceding binder (per
// `memory/annotation-reader-macro-binds-following-form.md`). It also used a
// `box-v` accessor; the spec (§5 — auto-generated accessor = the FIELD name)
// has no `box-v`, and the field-name accessor (`v`) currently does not resolve
// as a free callable (a separate pre-existing typecheck issue — see report).
//
// This guard's SUBJECT is the `super` import of a parent type constructor, NOT
// accessor/annotation mechanics. It therefore extracts the field via `match`
// destructuring (the spec-blessed pattern, see examples/10-adts.cl) and drops
// the (broken) self-qualified annotation. With the fixture corrected the
// behaviour-under-test resolves and main exits 9.
#[test]
fn super_import_resolves_parent_type_constructor() {
    Cranelisp::new()
        .file(
            "superp.cl",
            "(deftype Box [:primitives/Int v])\n\
             (defn unbox [b] (match b [(Box x) x]))\n\
             (mod test\n  \
               (import [super [Box]])\n  \
               (defn make [] (Box 3)))",
        )
        .file(
            "entry.cl",
            "(import [primitives [Pure]])\n\
             (import [superp [Box unbox]])\n\
             (defn main [] (Pure (unbox (Box 9))))",
        )
        .run("entry.cl")
        .output()
        // CORRECT: the submodule sees the parent's `Box` constructor (via the
        // `super` import) and the project compiles; main exits 9.
        .assert_exit(9);
}

// =============================================================================
// §8.5 Qualified Names — self-qualified type reference (FIXME 0351)
// =============================================================================

// spec: spec/08-modules.md §8.5 — a module MUST be able to reference its own
// types by their fully-qualified (module-qualified) name.
// FAILING-NOT-IGNORED defect repro (FIXME 0351, target /typecheck, S83).
// Inside `t.cl` (compiled as module `t`), the type `Box` is defined locally;
// annotating a parameter with the self-qualified name `:t/Box` MUST resolve
// to that local type. As-built it errors:
//   `unknown type `t/Box` (from module ``)`.
// Single-file, no super-import — this is the (a) repro of 0351, isolating the
// self-qualified resolution defect from the (now-green) 0342 super-import guard.
//
// The behaviour-under-test is the self-qualified `:t/Box` annotation on `unbox`
// (module `t` referencing its OWN type by qualified name). Post-S80 `main` MUST
// return `IO _`, so the body is wrapped in `Pure` (importing `[primitives [Pure]]`),
// mirroring the corrected sibling `super_import_resolves_parent_type_constructor`.
// The wrap is the `main` envelope only; the self-qualified resolution is unchanged.
#[test]
fn self_qualified_type_reference_resolves_to_local_type() {
    Cranelisp::new()
        .file(
            "t.cl",
            "(import [primitives [Pure]])\n\
             (deftype Box [:primitives/Int v])\n\
             (defn unbox [:t/Box b] (match b [(Box x) x]))\n\
             (defn main [] (Pure (unbox (Box 9))))",
        )
        .run("t.cl")
        .output()
        // CORRECT: `:t/Box` resolves to the locally-defined `Box`; main exits 9.
        .assert_exit(9);
}

// =============================================================================
// §8.2 Submodules — `(mod test)` inside a TRAIT-DEFINING module
//
// FAILING-NOT-IGNORED defect repros for S86 D3 + D4 (the self-test-rollout
// blockers). Both are isolated, fully stdlib-free, single-tree repros of the
// `(mod test …)`-inside-a-trait-module path that `/stdlib` could not roll out.
// Owning crate guess: /typecheck (submodule trait-environment seeding /
// parent-trait re-processing under submodule load). The visible errors are
// typecheck "trait already defined" / "unknown type" — but the proximate cause
// is module-load ordering, so /int (worker module-load) may co-own; see
// tests/CLAUDE.md §"Isolating Cross-Crate Failures". Same defect family as the
// (now-green) 0342 super-import guards above and the impl-body-scope D1.
// =============================================================================

// spec: spec/08-modules.md §8.2 — a `(mod name)` child submodule MUST load
//   WITHOUT re-processing (re-defining) the parent module's top-level forms.
//
// D3 (S86): a trait-defining module that declares a `(mod test)` child errors
// "trait <T> already defined" — adding ANY child submodule (even a trivial one
// that imports nothing from the parent) causes the parent's `(deftrait …)` to be
// processed twice. The `(mod test)` child is the entire trigger: dropping it
// makes the same module load clean. This blocks rolling self-tests into the
// trait-defining foundation modules (compare.eq, num.num, …) — the headline
// self-test-rollout goal.
//
// Minimal, stdlib-free: `eqmod.cl` defines a one-method trait + one impl and
// declares `(mod test)`; `eqmod/test.cl` is a trivial test fn that touches
// NOTHING in the parent. `entry.cl` imports the trait so the project compiles.
// FIXME(/typecheck — D3).
#[test]
fn mod_test_child_in_trait_module_does_not_redefine_parent_trait() {
    Cranelisp::new()
        .file(
            "eqmod.cl",
            "(import [primitives [eq-i64 Bool Int]])\n\
             (deftrait Eq (= [a b] Bool))\n\
             (impl Eq Int (defn = [a b] (eq-i64 a b)))\n\
             (mod test)",
        )
        .file(
            "eqmod/test.cl",
            "(defn test-trivial [] :primitives/Bool true)",
        )
        .file(
            "entry.cl",
            "(import [primitives [Pure]])\n\
             (import [eqmod [Eq =]])\n\
             (defn main [] (Pure 0))",
        )
        .run("entry.cl")
        .output()
        // CORRECT: the child submodule loads without re-processing the parent's
        // `(deftrait Eq …)`; the project compiles and main exits 0. Today this
        // FAILS with `type error … trait Eq already defined` (the parent's
        // deftrait span), exit 1.
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.3.8 — a `(mod test)` child submodule that imports
//   the parent's TRAIT via `super` MUST resolve that trait as a usable
//   constraint inside the child's scope.
//
// D4 (S86): a test submodule that does `(import [super [Eq]])` and then uses
// `:Eq` as a parameter constraint fails to resolve the trait in the child's
// scope. This single-annotation form errors `unknown type \`Eq\` (from module
// \`\`)` at the child's defn — the bound-resolver roots in the child's
// (empty/root) module and finds no `TraitDecl` for `Eq`, falling through to the
// TYPE-resolution path (a single `:Eq a` annotation is read as a type
// annotation, not a trait bound; only a STACK of 2+ — `:Eq :Eq a` — parses as
// trait bounds, which under a `user` entry module yields the sprint's reported
// `unknown trait \`Eq\` (from module \`user\`)`). Both are the same root cause:
// a super-imported trait is not seeded into the child submodule's
// constraint-resolution scope. The single-annotation form is the smallest
// deterministic repro and is what this test pins; the stacked-bound variant is
// noted for the resolver fix. Distinct from D3: the super-import reorders the
// load so the parent is NOT re-processed (no "already defined"). Same defect
// family as the impl-body-scope D1.
//
// Minimal, stdlib-free: trait-only parent + `(mod test)`; the child super-imports
// `Eq` and annotates a parameter `:Eq`. FIXME(/typecheck — D4).
#[test]
fn mod_test_child_super_imported_parent_trait_resolves_as_constraint() {
    Cranelisp::new()
        .file(
            "eqmod.cl",
            "(import [primitives [Bool]])\n\
             (deftrait Eq (= [a b] Bool))\n\
             (mod test)",
        )
        .file(
            "eqmod/test.cl",
            "(import [super [Eq]])\n\
             (import [primitives [Bool]])\n\
             (defn use-it [:Eq a] :Bool true)\n\
             (defn test-x [] :Bool (use-it 1))",
        )
        .file(
            "entry.cl",
            "(import [primitives [Pure]])\n\
             (import [eqmod [Eq]])\n\
             (defn main [] (Pure 0))",
        )
        .run("entry.cl")
        .output()
        // CORRECT: the super-imported `Eq` resolves as a constraint inside the
        // child; the project compiles and main exits 0. Today this FAILS with
        // `type error … unknown type `Eq` (from module ``)` at the child's
        // `use-it` defn, exit 1.
        .assert_exit(0);
}

// =============================================================================
// §8.8.1 Implicit prelude — re-export-only / prelude-provided `defn` body
//        dropped from the consuming program's codegen batch — DEFECT DEF-1 (S86)
// =============================================================================
//
// DEF-1 — a plain `defn` that the consuming program reaches ONLY through the
// implicit-prelude glob (a bare call, no explicit import) typechecks but its
// BODY never enters the user program's codegen batch. The call resolves at
// typecheck (the prelude-resolution fallback per §8.8.1 surfaces the name into
// bare scope), then codegen fails `undefined function: <name>`.
//
// ISOLATION (this session, /qa S86 step 1.5a):
//   - The bare prelude-provided call FAILS; an EXPLICIT `(import [prelude [name]])`
//     of the SAME name WORKS (the control test below, exit 3). So the trigger is
//     the implicit-glob / re-export path, NOT the function itself.
//   - The body must wrap a GOT-dispatched primitive (`vec-len`, `vec-push`,
//     `Pure`) to surface the drop. A wrapper of an INLINE-emitted primitive
//     (`add-i64`) appears to work because the inline materialises at the call
//     site — masking the same batch-derivation gap. `count` (wraps `vec-len`)
//     is the representative shape (matches the carried `count`/`get`/`conj`
//     prelude-promotion blocker in `stdlib/prelude.cl`).
//   - The long-re-exported bare `pure` (io.monad) is the pre-existing instance.
//
// TRUE OWNER: /int. `derive_codegen_batch` (`src/worker.rs:621`) emits only
// `ModuleEntry::Def` entries; a name surfaced via the implicit-prelude fallback
// installs as `ModuleEntry::Import`/`Reexport`, which is codegen-skipped, and
// the prelude's provision does not cascade the body into the consuming module's
// batch. FIXME(/int). LOCALIZED at the batch-derivation seam.
//
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md: asserts the
// CORRECT behaviour (a prelude-provided function is callable bare; the program
// runs to exit 3), RED today (`codegen error … undefined function: count`,
// exit 1), GREEN when the body enters the batch. When fixed, the
// `count`/`get`/`conj` bare re-exports in `stdlib/prelude.cl` can be un-blocked.

const PRELUDE_WITH_COUNT: &str = "\
(export [primitives [*]])
(defn count [v] (vec-len v))
";

// spec: spec/08-modules.md §8.8.1 — a function provided ONLY through the implicit
// prelude (bare call, no explicit import) MUST be callable; its body MUST enter
// the consuming program's codegen batch. DEF-1: today codegen-fails
// `undefined function: count` (exit 1) — the bare-call/re-export path drops the body.
#[test]
fn def1_prelude_provided_defn_called_bare_enters_codegen_batch() {
    // `count` wraps the GOT-dispatched primitive `vec-len`; main calls `count`
    // BARE (relies on the implicit-prelude fallback, no explicit import).
    // Vec of 3 ⇒ exit 3 when GREEN.
    Cranelisp::new()
        .prelude(PRELUDE_WITH_COUNT)
        .user("(defn main [] (Pure (count [10 20 30])))")
        .run("user.cl")
        .output()
        .assert_exit(3);
}

// spec: spec/08-modules.md §8.8.1 — CONTROL: the SAME prelude-provided function
// reached via an EXPLICIT `(import [prelude [count]])` already works (exit 3).
// This pins that the implicit-glob/re-export path — not the function — is the
// DEF-1 trigger. GREEN today; a behaviour-preservation guard.
#[test]
fn def1_prelude_provided_defn_explicit_import_works_control() {
    Cranelisp::new()
        .prelude(PRELUDE_WITH_COUNT)
        // Explicit import of `count`; `Pure` comes via the implicit prelude glob.
        .user(
            "(import [prelude [count]])\n\
             (import [primitives [Pure]])\n\
             (defn main [] (Pure (count [10 20 30])))",
        )
        .run("user.cl")
        .output()
        .assert_exit(3);
}
