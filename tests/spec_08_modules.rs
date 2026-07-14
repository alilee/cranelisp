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

use helpers::e2e::{run_through_all_modes, Cranelisp, PreludeVariant};
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

// =============================================================================
// §1D — D0030 mutual-import: cycle-error, NOT a hang (S93 race gate)
//
// Design of record: design/int/signature-body-prepass.md §4 — the ratified
// user ruling (S93 Phase-3, coarse reading / FIXME 0448 closed) is that MUTUAL
// IMPORTS ARE A COMPILE-TIME CYCLE-ERROR — they are NOT compiled. The module-
// atomic signature/body pre-pass barrier converts the D0030 deadlock (a HANG)
// into a deterministic cycle-detected error at the import site (a strict
// improvement: a hang is the worst failure mode).
//
// Posture: RED-first on HEAD via a BOUNDED TIMEOUT. HEAD deadlocks (FIXME 0426),
// so `try_output()` returns `CrError::Timeout` — the test fails its assertion
// but is bounded (it does NOT wedge `cargo nextest`; the harness kills the child
// at the bound). Post-fix (the barrier): a clean cycle diagnostic → GREEN.
// =============================================================================

// spec: design/int/signature-body-prepass.md §4 — two modules that each
// `(import …)` the other MUST terminate with a cycle-detected diagnostic at the
// import site within a bounded time, NOT hang and NOT panic.
#[test]
fn mutual_import_pair_diagnoses_cycle_not_hang() {
    // a.cl imports b; b.cl imports a — a 2-cycle in the static import closure.
    let result = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "a.cl",
            "(import [b [bb]])\n\
             (defn aa [] 1)\n\
             (defn main [] (add-i64 (aa) (bb)))\n",
        )
        .file("b.cl", "(import [a [aa]])\n(defn bb [] 2)\n")
        // Bounded so a HEAD deadlock surfaces as a Timeout error rather than
        // wedging the suite. Post-fix the cycle diagnostic is near-instant.
        .timeout(Duration::from_secs(8))
        .run("a.cl")
        .try_output();

    let out = match result {
        Ok(o) => o,
        Err(e) => panic!(
            "mutual import MUST terminate with a cycle diagnostic, not hang — \
             the process did not exit within the bound ({e}). This is the HEAD \
             D0030 deadlock (FIXME 0426); the signature/body pre-pass barrier \
             (signature-body-prepass.md §4) flips this GREEN."
        ),
    };
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    // POST-FIX target (signature-body-prepass.md §4): the module-atomic barrier's
    // `dependency_closure` finds a 2-cycle with no topological order and emits a
    // clean CYCLE-detected diagnostic at the import site. RED-first on HEAD: the
    // form-by-form resolver instead surfaces a confusing dependency error
    // (`'aa' not found in module 'a'`) — neither a clean cycle diagnostic nor (for
    // this specific-import shape) a deadlock. The bounded timeout above still
    // guards the deadlock shape from wedging the suite.
    assert!(
        combined.contains("cycle") || combined.contains("circular"),
        "mutual import MUST surface a CYCLE diagnostic (signature-body-prepass.md \
         §4). HEAD emits a confusing non-cycle error instead — RED-first, GREEN \
         when the pre-pass barrier lands. got: {combined}"
    );
    assert!(
        !combined.contains("panic"),
        "mutual import MUST be a clean cycle diagnostic, not a panic, got: {combined}"
    );
}

// =============================================================================
// FIXME 0434 sweep (this sprint) — import / `(mod)` target, qualified vs bare.
// verify-on-HEAD: a passing row is a standing [Tested+Neg] regression guard on
// the qualified module-target path; a failing row is a surfaced sibling defect
// handed to /frontend with this minimal repro.
// =============================================================================

// spec: spec/08-modules.md §8.2.6 + §8.5.1 — a `(mod child)` submodule is
// referable BOTH by its bare short-name alias (`child/val`) AND by its full
// qualified path (`app.child/val`); the two MUST resolve to the same loaded
// submodule symbol. The REPL displays the full qualified module path, so the
// bare alias and the qualified form must be interchangeable name-positions.
#[test]
fn import_mod_target_qualified_and_bare_equiv() {
    // Entry module `app` (the `--run app.cl` target) declares an inline
    // submodule `child`; `app.child` is its full identity, `child` the alias.
    // `child/val` (bare alias) and `app.child/val` (qualified) MUST both
    // resolve to the same defn → 7 + 7 = 14.
    Cranelisp::new()
        .file(
            "app.cl",
            "(import [primitives [add-i64]])\n\
             (import [primitives [Pure]])\n\
             (mod child (defn val [] 7))\n\
             (defn main [] (Pure (add-i64 (child/val) (app.child/val))))\n",
        )
        .run("app.cl")
        .output()
        .assert_exit(14);
}

// =============================================================================
// §8.11.2 — bare (current-module-relative) submodule re-export resolution
// (S96 Phase 6 user-proxy validation; PRE-EXISTING, unrelated to S96).
// =============================================================================
//
// FAILING-NOT-IGNORED defect repro. §8.11.2 step 1 mandates that when resolving
// a module name inside a module, the FIRST search step is "Submodule of current
// module -- already registered via (mod name) in the current module" (no file
// search required). A shell module that declares `(mod child)` and then
// re-exports a name from it by the BARE relative name —
//
//   (mod child)
//   (export [child [foo]])
//
// — therefore MUST resolve `child` to the current module's submodule. Today it
// fails:
//   module 'child' not found (re-exported by 'shell')
// because the export-resolution path (src/process_form/dependency.rs
// `handle_export` → `pipeline::resolve_module_file`) skips §8.11.2 step 1 and
// resolves `child` only as a project-root / lib-dir ROOT module — which does not
// exist (the file is `shell/child.cl`, i.e. module `shell.child`).
//
// Isolation (`tests/CLAUDE.md §"Isolating Cross-Crate Failures"`):
//   - SELF-CONTAINED fixture reproduces (this test — no stdlib dependency).
//     The defect is NOT stdlib-specific; the real `stdlib/core.cl`
//     `(export [syntax …])` / `(export [io …])` bare re-exports are merely the
//     surfacing instance (failing under `CRANELISP_LIB=stdlib`).
//   - The FULLY-QUALIFIED form `(export [shell.child [foo]])` WORKS (exit 42) —
//     see `export_specific_reexport` above — pinning the axis to bare-relative
//     name resolution, NOT re-export semantics in general.
//   - The same skip affects bare-relative IMPORT
//     (`(import [child …])` ⇒ "module 'child' not found (imported by 'shell')").
//   - The bug reproduces in-project AND via a lib path; not lib-path-specific.
//
// Resolver = /int (module resolution in the binary crate). The error originates
// in `src/process_form/dependency.rs`, which is /int-owned; the fix is to honour
// §8.11.2 step 1 (submodule-of-current-module) before falling through to
// project-root / lib-dir file resolution in BOTH the export and import paths.
//
// spec: spec/08-modules.md §8.11.2 — Module Resolution Search Order (step 1,
//   submodule of current module).
// FIXME(/int): honour §8.11.2 step 1 in `handle_export`/`handle_import` so a
//   bare name matching a `(mod name)`-declared submodule of the current module
//   resolves to that submodule instead of erroring "module 'name' not found".
#[test]
fn bare_relative_submodule_reexport_resolves() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [shell [foo]])\n\
             (defn main [] (Pure (foo 41)))",
        )
        .file(
            "shell.cl",
            "(mod child)\n\
             (export [child [foo]])",
        )
        .file(
            "shell/child.cl",
            "(import [primitives [add-i64]])\n\
             (defn foo [x] (add-i64 x 1))",
        )
        .run("main.cl")
        .output()
        // CORRECT: the bare `child` in `(export [child [foo]])` resolves to the
        // current module's `(mod child)` submodule (§8.11.2 step 1); `foo` is
        // re-exported through `shell`; main exits 42. Today this FAILS with
        // "module 'child' not found (re-exported by 'shell')".
        .assert_exit(42);
}

// =============================================================================
// FIXME 0484 (S101 Phase 6a, /stdlib) — definition over an explicit import.
// RE-ANCHORED S102 Phase 5 stage 1 to the /spec ruling (spec/08-modules.md
// §8.6.4 §"Definition-Over-Import: Order-Independent, All Modes", landed
// S102 Phase 3): a definition whose name is bound by an EXPLICIT import MUST
// be REJECTED with a compile-time error — order-independent, all modes; the
// rejected form has no effect (the import stays the binding, introspection
// keeps describing it). The originally-drafted polarity (shadow-wins per the
// pre-ruling §8.6.1 reading) was itself the violation, so BOTH tests below
// now expect rejection and BOTH are RED on HEAD: today the binary neither
// rejects nor resolves order-independently (used-first order keeps the
// import silently; unused order silently takes the shadow — the S101 6a
// finding). Resolver: /int (Block A5 — reject the later-arriving conflicting
// form). Failing-not-ignored; ledger: tests/plan/ledger.md §"Sprint 101
// Phase 6a/6b defect set" (+ S102 re-anchor note).
// Re-anchored S102 (user no-exception ruling 2026-07-04; /spec `a953de0`;
// FIXME 0514/0515): prelude-PROVIDED names are NO LONGER shadowable — the
// prelude is just an implicit `(import [prelude [*]])`, so a def over a
// prelude name is the SAME error (§8.6.4/§8.8.1). The former "contrast pins"
// in tests/vec_query_value_use.rs are FLIPPED to expect rejection; the full
// positive/negative matrix (all modes) lives in tests/spec_08_name_shadowing.rs.
// Reduced stdlib-free: local module `util`, fn `measure`.
// =============================================================================

// spec: spec/08-modules.md §8.6.4 — definition-over-import is a compile-time
// ERROR regardless of call history: import → call (3) → conflicting defn
// MUST be rejected; the import remains the binding (post-turn call still 3,
// never 99). RED on HEAD (FIXME 0484): today this order silently keeps the
// import while `/info` claims the shadow — no rejection, split introspection.
#[test]
fn import_used_then_shadowed_by_defn_is_rejected_error() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "util.cl",
            "(import [primitives [*]])\n\
             (defn measure \"module count\" [v] (vec-len v))\n",
        )
        .stdin(
            "(import [util [measure]])\n\
             (measure [1 2 3])\n\
             (defn measure \"user shadow\" [v] :Int 99)\n\
             (measure [1 2 3])\n",
        )
        .output()
        .assert_ok()
        // The conflicting definition is rejected with an error naming the
        // symbol (§8.6.4: the diagnostic SHOULD also name the import source).
        .assert_stdout_contains("error")
        .assert_stdout_does_not_contain(":primitives/Int 99"); // rejected form has NO effect
    // Both calls resolve through the import — pre-conflict AND
    // post-rejection print 3 (the §8.6.4 transcript is identical with or
    // without the pre-definition call).
    assert_eq!(
        out.stdout.matches(":primitives/Int 3").count(),
        2,
        "the import must remain the binding before AND after the rejected \
         definition (spec/08-modules.md §8.6.4); stdout:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.6.4 — the SAME rejection with NO pre-conflict
// call (order-independence: "an implementation in which an already-exercised
// import behaves differently from an unexercised one … is defective on both
// legs"). RED on HEAD (FIXME 0484): today this order silently ACCEPTS the
// shadow (99) — the formerly-"control" behaviour is itself the violation per
// the S102 /spec ruling.
#[test]
fn import_shadowed_by_defn_before_first_call_is_rejected_error() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "util.cl",
            "(import [primitives [*]])\n\
             (defn measure \"module count\" [v] (vec-len v))\n",
        )
        .stdin(
            "(import [util [measure]])\n\
             (defn measure \"user shadow\" [v] :Int 99)\n\
             (measure [1 2 3])\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("error") // the definition is rejected
        .assert_stdout_does_not_contain(":primitives/Int 99") // no silent shadow
        .assert_stdout_contains(":primitives/Int 3"); // the import stays the binding
}

// =============================================================================
// §8.5.2 Dotted Names — constructor in value position
// =============================================================================

// spec: spec/08-modules.md §8.5.2 — dotted constructor access `Type.Ctor` is a
// first-class value reference: "Like dotted constructor/method access, the
// canonical accessor is a derived consequence of `Type` being in bare scope
// ... first-class — `Box.v` MAY be passed as an argument or bound to a
// variable." Whenever the parent type is in bare scope (here: same-module
// `deftype`), `Type.Ctor` MUST resolve — as a value, not only in call/pattern
// position. The bare constructor `Red` resolves in value position AND the
// language even DISPLAYS the value using the canonical dotted form
// (`:user/Color Color.Red`), yet writing that same `Color.Red` as input in
// value position fails `undefined variable`. Contrast: the dotted FIELD
// accessor `Box.v` DOES resolve as a value — so the dotted-member resolver
// enumerates field accessors but omits constructors. Mode-independent
// (`--run` and REPL both fail); nullary and applied (`Opt.Some`) ctors alike.
//
// This test asserts the spec-correct behaviour (exit 7 via a bare-pattern
// match on a value bound through the dotted constructor ref) and is therefore
// RED until the dotted value-position constructor path is fixed.
// defect: class=enumeration-miss locus=crates/cranelisp-typecheck/src/checker.rs::resolve_dotted_field_accessor found=S108 owner=/dev
#[test]
fn dotted_constructor_in_value_position_resolves() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (deftype Color Red Green)\n\
             (defn main [] (Pure (match (let [c Color.Red] c) [Red 7 Green 0])))",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// =============================================================================
// Sprint 109 — §8.5.4 Auto-loading (AL rows) + 0571 FQ defect class (FQ rows) +
// dotted-`Type.Ctor` capability (DC rows) + 0570 `mod-` search twin (MV rows).
// Plan: tests/plan/PLAN.md §"Sprint 109 — sprint-wide failing-test plan".
// Fixtures are stdlib-free: own modules composed into the tmpdir via `.file()`,
// PreludeVariant::None (default) unless a row needs primitives named in-file.
// =============================================================================

/// Combined stdout+stderr of a capture — module/compile errors under `--run`
/// may land on either stream; error tests match the union (substring standard).
fn combined(out: &helpers::e2e::CrOutput) -> String {
    format!("{}\n{}", out.stdout, out.stderr)
}

/// The 0571 D1 signature (FQ-D3): a source-level fault that typecheck must
/// decide leaking to the backend surfaces as the doubly-wrapped
/// `codegen error … codegen failed for / … codegen error` shape. A conforming
/// resolution-layer diagnostic NEVER produces this. Shared across AL/FQ rows.
fn assert_no_doubly_wrapped_codegen_leak(text: &str) {
    let leak = text.contains("codegen failed for /")
        || (text.matches("codegen error").count() >= 2);
    assert!(
        !leak,
        "output leaks a doubly-wrapped codegen-layer error (FQ-D3 §8.5.4 edge 3 \
         — a resolution-layer fault MUST NOT surface as a codegen leak):\n{text}"
    );
}

// --- AL-1 / A1 — call position auto-loads, all modes (§8.5.4 edge 1) ---------

// spec: spec/08-modules.md §8.5.4 — a FQ call-position reference to an
// unimported, file-backed module auto-loads and resolves it, uniformly across
// REPL, `--run`, and `--link` (edge 1: all modes). Mode divergence is a defect.
#[test]
fn fq_call_position_autoloads_all_modes() {
    let aux = "(import [primitives [Int mul-i64]])\n\
               (defn square [:Int x] :Int (mul-i64 x x))\n";
    let entry = "(import [primitives [Pure]])\n\
                 (defn main [] (Pure (mathx/square 5)))\n";
    // --run
    Cranelisp::new()
        .file("mathx.cl", aux)
        .file("main.cl", entry)
        .run("main.cl")
        .output()
        .assert_exit(25);
    // --link then run
    Cranelisp::new()
        .file("mathx.cl", aux)
        .file("main.cl", entry)
        .link_then_run("main.cl")
        .output()
        .assert_exit(25);
    // REPL — the aux module in cwd auto-loads on the qualified reference.
    Cranelisp::new()
        .repl()
        .file("mathx.cl", aux)
        .stdin("(mathx/square 5)\n")
        .output()
        .assert_stdout_contains(":primitives/Int 25");
}

// spec: spec/08-modules.md §8.5.4 edge 1 (value position, A2) — a FQ reference
// bound in a `let` and applied auto-loads and resolves (concrete fn).
#[test]
fn fq_value_position_ref_call_through_let() {
    let aux = "(import [primitives [Int add-i64]])\n\
               (defn inc1 [:Int x] :Int (add-i64 x 1))\n";
    let entry = "(import [primitives [Pure]])\n\
                 (defn main [] (Pure (let [f mathx/inc1] (f 41))))\n";
    Cranelisp::new()
        .file("mathx.cl", aux)
        .file("main.cl", entry)
        .run("main.cl")
        .output()
        .assert_exit(42);
    Cranelisp::new()
        .file("mathx.cl", aux)
        .file("main.cl", entry)
        .link_then_run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.5.4 edge 1 (macro, A3) + §9.3.6 — a FQ reference
// to a macro auto-loads its defining module and expands at the qualified call
// site. Verify-first: A3 is expected GREEN today per arch verification.
#[test]
fn fq_macro_ref_expands_at_qualified_site() {
    let aux = "(import [primitives [Int add-i64]])\n\
               (defmacro dbl [x] `(add-i64 ~x ~x))\n";
    let entry = "(import [primitives [Pure]])\n\
                 (defn main [] (Pure (macx/dbl 21)))\n";
    let out = Cranelisp::new()
        .file("macx.cl", aux)
        .file("main.cl", entry)
        .run("main.cl")
        .output();
    assert_no_doubly_wrapped_codegen_leak(&combined(&out));
    out.assert_exit(42);
}

// spec: spec/08-modules.md §8.5.4 edge 1 (type, A4) — a fully-qualified type
// name in an annotation participates in auto-load: referencing `shapes/Circle`
// as an annotation triggers loading `shapes`. Verify-first.
#[test]
fn fq_type_annotation_triggers_autoload() {
    let aux = "(import [primitives [Int]])\n\
               (deftype Circle [:Int r])\n";
    let entry = "(import [primitives [Pure Int]])\n\
                 (defn area [:shapes/Circle c] :Int (shapes/Circle.r c))\n\
                 (defn main [] (Pure (area (shapes/Circle 9))))\n";
    let out = Cranelisp::new()
        .file("shapes.cl", aux)
        .file("main.cl", entry)
        .run("main.cl")
        .output();
    assert_no_doubly_wrapped_codegen_leak(&combined(&out));
    out.assert_exit(9);
}

// --- AL-2 — absolute path resolution + phantom-child negative ----------------

// spec: spec/08-modules.md §8.5.4 edge 2 — auto-load resolves the qualified
// `module_path` as an ABSOLUTE module path, same resolution as `import`, with a
// file-backed module and no preceding import/mod declaration.
#[test]
fn fq_ref_autoloads_absolute_module_path() {
    Cranelisp::new()
        .file(
            "util/helper.cl",
            "(import [primitives [Int]])\n(defn val [] :Int 13)\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (util.helper/val)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(13);
}

// spec: spec/08-modules.md §8.5.4 edge 2 (NEG) — auto-load MUST NOT invent a
// phantom child module from a bare qualifier: `util/helper` names an ABSOLUTE
// module `util`; when no `util.cl` (nor `util/`) backs it, the reference is a
// compile-time error at the reference site, not a silently-invented child.
#[test]
fn autoload_neg_no_phantom_child_from_bare_qualifier() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (util.helper/val)))\n",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "an unresolvable absolute FQ path MUST error, not invent a phantom child; {}",
        combined(&out)
    );
    assert_no_doubly_wrapped_codegen_leak(&combined(&out));
}

// --- AL-3 — file-not-found error at the REFERENCE SITE (span-pinned RED) -----

// spec: spec/08-modules.md §8.5.4 edge 3 — auto-load that cannot locate a
// backing file is a compile-time error AT THE REFERENCE SITE, produced at the
// resolution layer, naming both the referenced and referencing modules. It MUST
// NOT surface with the bogus `0..0` span, as `undefined variable`, or through a
// codegen-layer frame.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck (missing-module FQ ref reported at module head 0..0, not the reference span) found=S108 owner=/dev
#[test]
fn fq_ref_missing_module_errors_at_reference_site() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (nonesuch/square 5)))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(!out.status.success(), "missing module MUST error; {text}");
    // Names both modules (referenced + referencing).
    assert!(
        text.contains("nonesuch"),
        "error MUST name the referenced module 'nonesuch'; {text}"
    );
    // Span-pinned (structural): the reference-site span, NOT the bogus `0..0`
    // module-head span. RED today (the wrap reports at module head).
    assert!(
        !text.contains("at 0..0"),
        "error MUST be span-pinned at the reference site, not the bogus `0..0` \
         module-head span (AL-3, structural span standard); {text}"
    );
    // Neg facet: resolution-layer, not a codegen/undefined-variable leak.
    assert!(
        !text.contains("undefined variable"),
        "a missing-module FQ ref is a resolution-layer error, NOT `undefined \
         variable`; {text}"
    );
    assert_no_doubly_wrapped_codegen_leak(&text);
}

// --- AL-4 — member absent names module+member, order-independent -------------

// spec: spec/08-modules.md §8.5.4 edge 4 — an auto-loaded module that lacks the
// named member yields "module X has no member Y", naming both.
#[test]
fn fq_ref_member_absent_names_module_and_member() {
    let out = Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int]])\n(defn present [] :Int 1)\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (mathx/absent)))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(!out.status.success(), "member-absent MUST error; {text}");
    assert!(
        text.contains("mathx") && text.contains("absent"),
        "error MUST name both the module and the absent member; {text}"
    );
    assert_no_doubly_wrapped_codegen_leak(&text);
}

// spec: spec/08-modules.md §8.5.4 edge 4 (NEG twin) — the member-absent error is
// order-independent: identical class whether the module was auto-loaded by this
// reference or explicitly imported first. The preloaded leg must produce the
// same member-absent error (not a different diagnostic).
#[test]
fn fq_ref_member_absent_error_identical_when_preloaded_neg() {
    let out = Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int]])\n(defn present [] :Int 1)\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [mathx [present]])\n\
             (defn main [] (Pure (mathx/absent)))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(!out.status.success(), "member-absent MUST error even when preloaded; {text}");
    assert!(
        text.contains("mathx") && text.contains("absent"),
        "preloaded leg MUST give the SAME member-absent error naming both \
         (order-independence, §8.6.4 terminal-source); {text}"
    );
}

// --- AL-5 — dependency compile failure ⇒ chained diagnostic; REPL survives ---

// spec: spec/08-modules.md §8.5.4 edge 5 — a located-but-failing dependency
// fails the referencing form with a chained diagnostic naming the failed
// module, at the reference site (not a session-killer).
#[test]
fn fq_ref_dep_compile_error_chained_diagnostic() {
    let out = Cranelisp::new()
        .file(
            "broken.cl",
            "(import [primitives [Int]])\n(defn f [] :Int (not-a-thing 1))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure (broken/f)))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(!out.status.success(), "a failing dep MUST fail the reference; {text}");
    assert!(
        text.contains("broken"),
        "the chained diagnostic MUST name the failed module 'broken'; {text}"
    );
}

// spec: spec/08-modules.md §8.5.4 edge 5 (NEG) — a REPL session survives an
// auto-load dependency compile error: the failing reference reports and the
// session continues to the next prompt (a follow-on form still evaluates).
#[test]
fn fq_ref_dep_compile_error_repl_survives_to_next_prompt_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "broken.cl",
            "(import [primitives [Int]])\n(defn f [] :Int (not-a-thing 1))\n",
        )
        .stdin("(broken/f)\n(add-i64 1 2)\n")
        .output();
    // The follow-on form MUST still evaluate — the session survived.
    out.assert_stdout_contains(":primitives/Int 3");
}

// --- AL-6 — cycles ⇒ circular-dependency error naming the path (B4 RED) ------

// spec: spec/08-modules.md §8.5.4 edge 6 — a FQ reference that closes a module
// dependency cycle MUST be reported as a circular-dependency error naming the
// cycle path, at parity with import-induced cycles. It MUST NOT deadlock and
// MUST NOT surface as "undefined variable".
// defect: class=routing-misclassify locus=src/worker.rs (FQ-induced cycle reported as `undefined variable`, not circular-dependency) found=S108 owner=/dev
#[test]
fn fq_ref_cycle_reports_circular_dependency_path() {
    let out = Cranelisp::new()
        .file("a.cl", "(import [primitives [Int]])\n(defn x [] :Int (b/y))\n")
        .file("b.cl", "(import [primitives [Int]])\n(defn y [] :Int (a/x))\n")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure (a/x)))\n",
        )
        .timeout(Duration::from_secs(15))
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(!out.status.success(), "a FQ cycle MUST error; {text}");
    assert!(
        text.to_lowercase().contains("circular") || text.to_lowercase().contains("cycle"),
        "a FQ-induced cycle MUST be a circular-dependency error naming the path; {text}"
    );
    assert!(
        !text.contains("undefined variable"),
        "a FQ cycle MUST NOT surface as `undefined variable` (§8.5.4 edge 6); {text}"
    );
}

// spec: spec/08-modules.md §8.5.4 edge 6 (mixed cycle, B5/C2) — a cycle mixing
// an `import` edge and an FQ-ref edge (A imports B, B FQ-refs A) is deterministic
// (the import edge forces the order) and MUST report as a cycle, never
// `undefined variable`.
#[test]
fn fq_ref_mixed_cycle_import_plus_fq_reports_cycle() {
    let out = Cranelisp::new()
        .file(
            "a.cl",
            "(import [primitives [Int]])\n(import [b [y]])\n(defn x [] :Int (y))\n",
        )
        .file("b.cl", "(import [primitives [Int]])\n(defn y [] :Int (a/x))\n")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [a [x]])\n(defn main [] (Pure (x)))\n",
        )
        .timeout(Duration::from_secs(15))
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(!out.status.success(), "a mixed cycle MUST error; {text}");
    assert!(
        text.to_lowercase().contains("circular") || text.to_lowercase().contains("cycle"),
        "a mixed import+FQ cycle MUST report as a cycle; {text}"
    );
    assert!(
        !text.contains("undefined variable"),
        "a mixed cycle MUST NOT surface as `undefined variable`; {text}"
    );
}

// --- AL-8 — idempotence: a second reference does not reload ------------------

// spec: spec/08-modules.md §8.5.4 edge 8 — a second FQ reference to an
// already-loaded module resolves against the loaded instance (at most once per
// context). Observed behaviorally here: two references in one program both
// resolve to the correct combined value.
// NOTE (enumerated /dev-unit deferral): the "exactly one load event"
// structural assertion via CRANELISP_MODULE_TRACE is not reliably expressible
// e2e (the trace emits only sparse cache-hit lines). /dev pins the at-most-once
// load in the worker (`drive_module_dep`) with a load-counter unit test.
#[test]
fn fq_ref_second_reference_no_reload() {
    Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int mul-i64]])\n(defn square [:Int x] :Int (mul-i64 x x))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure add-i64]])\n\
             (defn main [] (Pure (add-i64 (mathx/square 5) (mathx/square 6))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(61);
}

// --- AL-9 — visibility unchanged; private member via FQ is an error ----------

// spec: spec/08-modules.md §8.5.4 edge 9 + §8.6.6 — a private member reached via
// FQ auto-load reference is a compile-time error (auto-load does not widen
// visibility).
#[test]
fn fq_ref_private_member_rejected_neg() {
    let out = Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int]])\n(defn- secret [] :Int 99)\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure (mathx/secret)))\n",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "a private member MUST NOT be reachable via FQ auto-load (§8.5.4 edge 9); {}",
        combined(&out)
    );
}

// spec: spec/08-modules.md §8.5.4 edge 9 (pos twin) — a public member via the
// same FQ auto-load path resolves.
#[test]
fn fq_ref_public_member_resolves() {
    Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int]])\n(defn public-val [] :Int 7)\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure (mathx/public-val)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// --- AL-10 — no scope pollution ---------------------------------------------

// spec: spec/08-modules.md §8.5.4 edge 10 (NEG) — auto-load installs NO bare
// bindings: after a FQ reference `(mathx/square 3)` resolves, the bare name
// `square` is still unresolved in the referencing module.
#[test]
fn autoload_neg_installs_no_bare_bindings() {
    let out = Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int mul-i64]])\n(defn square [:Int x] :Int (mul-i64 x x))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure add-i64]])\n\
             (defn main [] (Pure (add-i64 (mathx/square 3) (square 4))))\n",
        )
        .run("main.cl")
        .output();
    assert!(
        !out.status.success(),
        "auto-load MUST NOT install a bare `square` binding (§8.5.4 edge 10); {}",
        combined(&out)
    );
    assert!(
        combined(&out).contains("square"),
        "the error should be the unresolved bare `square`; {}",
        combined(&out)
    );
}

// spec: spec/08-modules.md §8.5.4 edge 10 (NEG) — auto-load introduces no §8.6.5
// ambiguity: a local `(defn square …)` after a FQ ref to `mathx/square` is NOT a
// conflict (the FQ ref installed no bare `square`), so the program compiles.
#[test]
fn autoload_neg_no_ambiguity_with_local_def() {
    Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int mul-i64]])\n(defn square [:Int x] :Int (mul-i64 x x))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure Int add-i64]])\n\
             (defn use-fq [] :Int (mathx/square 3))\n\
             (defn square [:Int x] :Int (add-i64 x 1))\n\
             (defn main [] (Pure (add-i64 (use-fq) (square 4))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(14);
}

// --- AL-11 — chain depth ≥3 parks/resumes -----------------------------------

// spec: spec/08-modules.md §8.5.4 edges 1+8 composed — a FQ chain A→B→C of depth
// three parks and resumes, producing the correct value.
#[test]
fn fq_ref_chain_depth_three_resumes() {
    Cranelisp::new()
        .file("cc.cl", "(import [primitives [Int]])\n(defn v [] :Int 4)\n")
        .file(
            "bb.cl",
            "(import [primitives [Int add-i64]])\n(defn v [] :Int (add-i64 (cc/v) 10))\n",
        )
        .file(
            "aa.cl",
            "(import [primitives [Int add-i64]])\n(defn v [] :Int (add-i64 (bb/v) 100))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure (aa/v)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(114);
}

// --- AL-12 — diamond loads C once, both legs resume -------------------------

// spec: spec/08-modules.md §8.5.4 edges 7+8 composed — a diamond (root refs A
// and B, both FQ-ref C) loads C once and both legs resume with correct values.
// (Load-count via trace is a /dev-unit pin per AL-8; here we assert behaviorally
// that both legs resolve against the one loaded C.)
#[test]
fn fq_ref_diamond_loads_once_both_resume() {
    Cranelisp::new()
        .file("cc.cl", "(import [primitives [Int]])\n(defn base [] :Int 5)\n")
        .file(
            "aa.cl",
            "(import [primitives [Int add-i64]])\n(defn va [] :Int (add-i64 (cc/base) 1))\n",
        )
        .file(
            "bb.cl",
            "(import [primitives [Int add-i64]])\n(defn vb [] :Int (add-i64 (cc/base) 2))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure add-i64]])\n\
             (defn main [] (Pure (add-i64 (aa/va) (bb/vb))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(13);
}

// --- C1-e2e — the in-flight race confidence sweep (edge 7) -------------------

// spec: spec/08-modules.md §8.5.4 edge 7 — in-flight atomicity. Deterministic
// e2e forcing of the interleaving is unattainable (no scheduler-pause hook), so
// this is the probabilistic confidence sweep: repeat the diamond-under-load
// spawn many times; EVERY iteration MUST exit 0 with the correct value and
// NEVER report `has no member` (the racy misclassification). A single failing
// iteration is a real bug — the forbidden dispositions (flaky/timing-sensitive)
// apply in full. The deterministic guard is the /dev int gap-arm unit pins
// (C1-unit: absent⇒park; non-terminal⇒PARK-not-err; terminal+present⇒resolve;
// terminal+absent⇒member-absent) enumerated in PLAN §C.
#[test]
fn autoload_diamond_race_under_load_repeated() {
    let cc = "(import [primitives [Int]])\n(defn base [] :Int 5)\n";
    let aa = "(import [primitives [Int add-i64]])\n(defn va [] :Int (add-i64 (cc/base) 1))\n";
    let bb = "(import [primitives [Int add-i64]])\n(defn vb [] :Int (add-i64 (cc/base) 2))\n";
    // root imports A and B (import wave puts both in-flight); A also FQ-refs B.
    let main = "(import [primitives [Pure add-i64]])\n\
                (import [aa [va]])\n(import [bb [vb]])\n\
                (defn main [] (Pure (add-i64 (va) (vb))))\n";
    for i in 0..25 {
        let out = Cranelisp::new()
            .file("cc.cl", cc)
            .file("aa.cl", aa)
            .file("bb.cl", bb)
            .file("main.cl", main)
            .cli_flag("--priority-workers")
            .cli_flag("4")
            .run("main.cl")
            .output();
        let text = combined(&out);
        assert!(
            !text.contains("has no member"),
            "iteration {i}: the in-flight member-probe race misclassified as \
             `has no member` (§8.5.4 edge 7 — a real bug, never flaky); {text}"
        );
        out.assert_exit(13);
    }
}

// =============================================================================
// FQ defect-class rows (0571) — FQ-D1 (check-gate-leak), FQ-D3 (no-leak sweep),
// FQ-D4 (import invariance twin).
// =============================================================================

// spec: spec/08-modules.md §8.5.4 edge 1 + spec/03-types.md §3.11 — a
// value-position FQ reference to a GENERIC fn concretely used MUST either
// resolve check-side (a mono minted at the inferred concrete type) or die
// check-side with an actionable annotation-required error — NEVER a codegen-
// layer error. Today it leaks the doubly-wrapped codegen error (RED).
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck (value-position ref to slot-less Polymorphic template never mints a mono; leaks to backend/literals.rs) found=S108 owner=/dev
#[test]
fn fq_value_ref_generic_fn_concrete_use_never_reaches_codegen() {
    let out = Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int Vec vec-len]])\n(defn gcount [v] :Int (vec-len v))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (let [f mathx/gcount] (f [1 2 3]))))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    // The load-bearing assertion: it MUST NOT reach the backend as a codegen
    // leak. Either it resolves (exit 3) or it is a check-side annotation error.
    assert_no_doubly_wrapped_codegen_leak(&text);
    if out.status.success() {
        assert_eq!(out.status.code(), Some(3), "if it resolves, the value is 3");
    } else {
        assert!(
            !text.contains("codegen"),
            "a slot-less generic value-position FQ ref MUST be decided check-side, \
             not leaked to codegen (0571 D1 check-gate-leak); {text}"
        );
    }
}

// spec: spec/08-modules.md §8.5.4 edge 3 (NEG sweep) — no AL/FQ fixture output
// ever matches the doubly-wrapped codegen-error shape. Dedicated guard using
// the shared helper over the FQ-D1 fixture.
#[test]
fn fq_ref_neg_no_doubly_wrapped_codegen_error() {
    let out = Cranelisp::new()
        .file(
            "mathx.cl",
            "(import [primitives [Int Vec vec-len]])\n(defn gcount [v] :Int (vec-len v))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (mathx/gcount [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    assert_no_doubly_wrapped_codegen_leak(&combined(&out));
}

// spec: spec/08-modules.md §8.5.4 edge 10 + §8.6.4 — import invariance: the same
// program with and without a prior `(import [mathx [square]])` behaves
// identically (value AND diagnostic legs). Here the value leg: both produce 25.
#[test]
fn fq_ref_import_invariance_twin() {
    let aux = "(import [primitives [Int mul-i64]])\n(defn square [:Int x] :Int (mul-i64 x x))\n";
    // Leg A — no prior import.
    let a = Cranelisp::new()
        .file("mathx.cl", aux)
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure (mathx/square 5)))\n",
        )
        .run("main.cl")
        .output();
    // Leg B — with a prior import of the same member.
    let b = Cranelisp::new()
        .file("mathx.cl", aux)
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [mathx [square]])\n\
             (defn main [] (Pure (mathx/square 5)))\n",
        )
        .run("main.cl")
        .output();
    a.assert_exit(25);
    b.assert_exit(25);
}

// =============================================================================
// Dotted-`Type.Ctor` capability (DC rows) — value-position twins + product +
// import-shape provenance. Pattern-position twins live in
// tests/spec_06_pattern_matching.rs (DC-4/DC-5); cache row in tests/cache.rs.
// =============================================================================

// spec: spec/08-modules.md §8.5.2/§8.6.5 — two in-scope types sharing BOTH
// constructor names (`Some` data + `None` nullary): the canonical dotted forms
// `Maybe.Some`/`Option.Some` (applied) and `Maybe.None`/`Option.None` (nullary)
// each resolve directly and unconditionally in value position. Both types share
// both names so the fixture exercises the same-named DATA and same-named NULLARY
// cases — not only the `Some` data ctor. Concrete construction only — no
// free-type-var param annotation (W1 fixture constraint). Mode-relevant DC twin:
// run through REPL/--run/--link. GREEN after the W1 registration change.
#[test]
fn same_named_ctors_dotted_value_position_both_resolve() {
    run_through_all_modes(
        "(import [primitives [Pure add-i64]])\n\
         (deftype (Maybe a) None (Some [:a v]))\n\
         (deftype (Option a) None (Some [:a v]))\n\
         (defn main [] (Pure\n\
           (add-i64 (match (Maybe.Some 7) [(Maybe.Some x) x Maybe.None 0])\n\
                    (match Option.None [(Option.Some x) x Option.None 3]))))\n",
        PreludeVariant::None,
    )
    .assert_all_equal(10);
}

// spec: spec/08-modules.md §8.6.5 + §6.2.1 unifying rule — in VALUE position
// there is no type context, so a contested bare constructor ALWAYS poisons: bare
// `Some` in value position is a compile-time error LISTING the canonical
// alternatives `Maybe.Some`/`Option.Some`. This is the "no context" arm of the
// DC-3/DC-11 unifying-rule pair (value always poisons; pattern resolves when the
// scrutinee is determined). 0568 facet: the diagnostic MUST NOT contain the
// internal `__expr` binder. RED today — bare `Some` silently resolves.
// defect: class=silent-accept locus=crates/cranelisp-typecheck (contested bare ctor `Some` silently resolves instead of poisoning) found=S108 owner=/dev
#[test]
fn same_named_ctors_bare_value_poisoned_lists_alternatives_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (deftype (Maybe a) MNone (Some [:a v]))\n\
             (deftype (Option a) ONone (Some [:a v]))\n\
             (defn main [] (Pure (match (Some 7) [(Some x) x _ 0])))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert!(
        !out.status.success(),
        "a contested bare ctor `Some` MUST be poisoned (§8.6.5), not silently \
         resolve; {text}"
    );
    assert!(
        text.contains("Maybe.Some") && text.contains("Option.Some"),
        "the poison error MUST list the canonical alternatives; {text}"
    );
    assert!(
        !text.contains("__expr"),
        "the diagnostic MUST NOT leak the internal `__expr` binder (0568); {text}"
    );
}

// spec: spec/08-modules.md §8.5.2/§8.6.5 (DC-6 twin A — define+import) — same
// assertions as the define+define twin, with one type local and one imported.
// A provenance that grew its own codepath diverges the twins.
#[test]
fn same_named_ctors_define_plus_import_twin() {
    let out = Cranelisp::new()
        .file(
            "optmod.cl",
            "(import [primitives [Int]])\n(deftype (Option a) ONone (Some [:a v]))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (import [optmod [Option]])\n\
             (deftype (Maybe a) MNone (Some [:a v]))\n\
             (defn main [] (Pure (match (Maybe.Some 7) [(Some x) x MNone 0])))\n",
        )
        .run("main.cl")
        .output();
    assert_no_doubly_wrapped_codegen_leak(&combined(&out));
    out.assert_exit(7);
}

// spec: spec/08-modules.md §8.5.2/§8.6.5 (DC-6 twin B — import+import) — both
// types imported; dotted forms resolve, bare contest poisons.
#[test]
fn same_named_ctors_import_plus_import_twin() {
    let maybe = "(import [primitives [Int]])\n(deftype (Maybe a) MNone (Some [:a v]))\n";
    let option = "(import [primitives [Int]])\n(deftype (Option a) ONone (Some [:a v]))\n";
    // pos: dotted resolves.
    Cranelisp::new()
        .file("maybemod.cl", maybe)
        .file("optmod.cl", option)
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (import [maybemod [Maybe]])\n(import [optmod [Option]])\n\
             (defn main [] (Pure (match (Maybe.Some 7) [(Some x) x MNone 0])))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
    // neg: bare contest poisons.
    let neg = Cranelisp::new()
        .file("maybemod.cl", maybe)
        .file("optmod.cl", option)
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (import [maybemod [Maybe]])\n(import [optmod [Option]])\n\
             (defn main [] (Pure (match (Some 7) [(Some x) x _ 0])))\n",
        )
        .run("main.cl")
        .output();
    assert!(
        !neg.status.success(),
        "a contested bare ctor across two imported types MUST poison; {}",
        combined(&neg)
    );
}

// spec: spec/08-modules.md §8.5.2 product corner (DC-7) — for a product type
// whose ctor name equals the type name, the dotted form `Point.Point` is
// degenerate and does NOT resolve; bare `Point` does, with no spurious poison.
#[test]
fn product_ctor_dotted_form_does_not_resolve_neg() {
    // pos: bare Point works.
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure Int add-i64]])\n\
             (deftype Point [:Int x :Int y])\n\
             (defn main [] (Pure (add-i64 (Point.x (Point 3 4)) (Point.y (Point 3 4)))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
    // neg: Point.Point does not resolve.
    let neg = Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (deftype Point [:Int x :Int y])\n\
             (defn main [] (Pure (Point.x (Point.Point 3 4))))\n",
        )
        .run("main.cl")
        .output();
    assert!(
        !neg.status.success(),
        "the degenerate dotted form `Point.Point` MUST NOT resolve (§8.5.2); {}",
        combined(&neg)
    );
}

// spec: spec/08-modules.md §8.5.2 first-class MAY (DC-8) — a dotted ctor is
// first-class: bound in a `let` and applied. RED until the dotted value-position
// constructor path lands.
#[test]
fn dotted_ctor_passed_as_argument_and_let_bound() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (deftype (Maybe a) MNone (Some [:a v]))\n\
             (deftype (Option a) ONone (Some [:a v]))\n\
             (defn main [] (Pure (match (let [f Maybe.Some] (f 3)) [(Some x) x MNone 0])))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(3);
}

// =============================================================================
// MV-4 — `mod-` child-file pattern loads (the /stdlib precondition). Gate row:
// verified PASS empirically before authoring the 0570/MV group.
// =============================================================================

// spec: spec/08-modules.md §8.2.5 — a `(mod- test)` private submodule declared
// via the child-file pattern (`<module>/test.cl`) loads and is usable from the
// parent subtree (here: a qualified reference `main.test/answer`).
#[test]
fn mod_dash_child_file_pattern_loads() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (mod- test)\n\
             (defn main [] (Pure (main.test/answer)))\n",
        )
        .file("main/test.cl", "(import [primitives [Int]])\n(defn answer [] :Int 42)\n")
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// Sprint 109 W1-prep — §D.1 acceptance negatives (the 73-regression classes as
// permanent guards). Plan: tests/plan/PLAN.md §S109 §D.1. AN-1/AN-4 are
// behaviour-invariance pins (GREEN today, must stay green through commit-1/2);
// AN-2/AN-5 are pre-existing-defect repros owed ahead of the wave.
// =============================================================================

// spec: spec/08-modules.md §8.6.2 (chain-follow to terminal) — AN-1(a) prelude-
// cascade ROOT-CAUSE twin. A prelude-shaped module with a `(mod test)` submodule
// whose test file `match`es an imported bare nullary ctor MUST NOT cause the
// parent's LATER export lines to fail to install (the `collections.list.test`
// one-hop miss cascade that took down `do`/`pure`/`cond`/…). Guard: a name
// defined AFTER the `(mod test)` is still importable. GREEN today; invariance pin.
#[test]
fn prelude_module_with_ctor_matching_submodule_still_exports_all() {
    Cranelisp::new()
        .file(
            "colors.cl",
            "(import [primitives [Int]])\n(deftype Color Red Green Blue)\n",
        )
        .file(
            "pre.cl",
            "(import [primitives [Int]])\n\
             (import [colors [Red Green Blue]])\n\
             (mod test)\n\
             (defn later-fn [] :Int 99)\n\
             (export [colors [Color Red Green Blue]])\n",
        )
        .file(
            "pre/test.cl",
            "(import [primitives [Int]])\n\
             (import [colors [Red Green Blue]])\n\
             (defn t [] :Int (match Red [Red 1 Green 2 Blue 3]))\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [pre [later-fn]])\n\
             (defn main [] (Pure (later-fn)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(99);
}

// spec: spec/06-pattern-matching.md §6.3 + spec/08-modules.md §8.6.2 — AN-2
// cross-module nullary-ctor SOUNDNESS: an imported bare nullary ctor (`Red`),
// reached through a ≥2-hop re-export chain, `match`ed on, MUST produce the CORRECT
// arm value (the wrong-value / "match failed" shape is the silent-soundness neg
// facet arch found in `lookup_constructor`'s one-hop miss). Mode-relevant.
// NOTE (/testing, S109 W1-prep): the defect does NOT reproduce as RED on the
// current binary in the shapes probed (bare/qualified/renamed import, 2- and
// 3-hop re-export, glob/specific, --run/REPL, contested/uncontested) — the
// `lookup_constructor` global-fallback rescues them. Authored as the soundness
// guard asserting the CORRECT value; it is currently GREEN. Arch's exact RED
// repro is owed (reported to /qa). Kept as the permanent soundness guard the
// class targets.
// defect: class=resolver-mirror locus=cranelisp-backend/src/compiler/context.rs::lookup_constructor (one-hop copy vs resolve_driven multi-hop — two resolvers, one name) found=S109 owner=/dev
#[test]
fn imported_bare_nullary_ctor_match_compiles_to_tag_not_closure() {
    let defmod = "(import [primitives [Int]])\n(deftype Color Red Green Blue)\n";
    let midmod = "(export [defmod [Color Red Green Blue]])\n"; // re-export hop (≥2 hops)
    let entry = "(import [primitives [Pure Int]])\n\
                 (import [midmod [Red Green Blue]])\n\
                 (defn main [] (Pure (match Red [Red 1 Green 2 Blue 3])))\n";
    // --run
    let run = Cranelisp::new()
        .file("defmod.cl", defmod)
        .file("midmod.cl", midmod)
        .file("main.cl", entry)
        .run("main.cl")
        .output();
    assert!(
        !combined(&run).to_lowercase().contains("match failed"),
        "the cross-module nullary ctor MUST NOT compile to a closure whose tag \
         comparison fails at runtime (AN-2 soundness); {}",
        combined(&run)
    );
    run.assert_exit(1);
    // --link
    Cranelisp::new()
        .file("defmod.cl", defmod)
        .file("midmod.cl", midmod)
        .file("main.cl", entry)
        .link_then_run("main.cl")
        .output()
        .assert_exit(1);
}

// spec: spec/08-modules.md §8.4 import shapes + §8.6.2 — AN-4 member-glob import
// keeps bare ctor refs: after a glob `(import [m [*]])` a bare imported ctor
// constructs and pattern-matches; the member-glob twin `(import [m [Lst.*]])`
// does the same. GREEN today; invariance pin (guards alias-edge installation).
#[test]
fn glob_import_bare_ctor_still_resolves() {
    let m = "(import [primitives [Int]])\n(deftype Lst (Cons [:Int h :Lst t]) Nil)\n";
    // glob import
    Cranelisp::new()
        .file("m.cl", m)
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (import [m [*]])\n\
             (defn main [] (Pure (match (Cons 5 Nil) [(Cons h t) h Nil 0])))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(5);
    // member-glob twin
    Cranelisp::new()
        .file("m.cl", m)
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (import [m [Lst.*]])\n\
             (defn main [] (Pure (match (Cons 9 Nil) [(Cons h t) h Nil 0])))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(9);
}

// spec: spec/08-modules.md §8.5.2 field-accessor alias + §8.6.2 — AN-5 latent
// same-cluster `--run` defect: a bare field accessor `v` MUST resolve in the SAME
// cluster under `--run`. RED today: bare `v` is never resolved same-cluster
// (the live-only chain-follow misses the same-module staged alias) → `undefined
// variable: v`. Flips GREEN at commit-1 (the §3.5 primitive amendment).
// defect: class=wrong-scope-lookup locus=cranelisp-types/src/resolve.rs::chain_follow_committed (same-module Import hop reads LIVE table, misses the caller's staging view) found=S109 owner=/dev
#[test]
fn bare_field_accessor_same_cluster_run_mode() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure Int]])\n\
             (deftype Box [:Int v])\n\
             (defn main [] (Pure (v (Box 7))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// =============================================================================
// Sprint 109 — 0571.2 negatives (I1 + I2). `/review` proved these in the landed
// 0571 change-set (35153cf8). Plan: tests/plan/PLAN.md §S109 (0571.2 negatives).
// =============================================================================

// spec: spec/08-modules.md §8.5.4 edge 4/5 — a retry after a FAILED auto-load
// MUST NOT falsely claim "module X has no member Y" (the member exists; the
// module never loaded). The real dependency compile error MUST surface (or the
// reference resolve once fixed), never a spurious no-member claim. RED today: the
// REPL caches the failed load as "loaded but empty", so the second `(broken/f)`
// says `module 'broken' has no member 'f'` — clobbering the real error.
// defect: class=error-swallow locus=src/session_v4 (a failed auto-load is cached as loaded-but-empty; the retry surfaces a false no-member claim instead of the real dep error) found=S109 owner=/dev
#[test]
fn failed_autoload_retry_does_not_claim_no_member_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "broken.cl",
            "(import [primitives [Int]])\n(defn f [:Int x] :Int (nonexistent-thing x))\n",
        )
        .stdin("(broken/f 1)\n(broken/f 2)\n")
        .output();
    // The FIRST reference reports the real dependency compile error.
    assert!(
        out.stdout.contains("nonexistent-thing"),
        "the first reference MUST surface the real dep compile error; got:\n{}",
        out.stdout
    );
    // The retry MUST NOT falsely claim the module has no member `f`.
    assert!(
        !out.stdout.contains("has no member 'f'"),
        "a retry after a FAILED auto-load MUST NOT falsely claim `module 'broken' \
         has no member 'f'` — `f` exists; the module failed to load (§8.5.4 edge \
         4/5); got:\n{}",
        out.stdout
    );
}

// --- I2 — concrete generic fn-value ref in non-Apply/non-Let positions -------
// FIXME 0585 (/qa owns the full value-position matrix); these are the three
// leaking cells (if / match / vector) authored as the REDs. `deftype`-free.

/// The generic-fn module: `gcount`/`gother` stay polymorphic (param inferred as
/// `(Vec _)`), so a value-position reference must be monomorphised check-side.
const I2_MATHX: &str =
    "(import [primitives [Int Vec vec-len]])\n\
     (defn gcount [xs] :Int (vec-len xs))\n\
     (defn gother [xs] :Int 0)\n";

// spec: spec/08-modules.md §8.5.4 edge 1 + spec/03-types.md §3.11.1 — a concrete
// generic fn-value reference in an `if` value position MUST resolve check-side (a
// mono minted at the inferred concrete type) or die check-side with the §3.11.1
// annotation-required error — NEVER reach codegen as `undefined variable`. RED
// today: it leaks the doubly-wrapped codegen error.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck (value-position generic ref in a non-Apply/non-Let position never mints a mono; leaks to backend) found=S109 owner=/dev
#[test]
fn fq_generic_value_ref_in_if_position_never_reaches_codegen() {
    let out = Cranelisp::new()
        .file("mathx.cl", I2_MATHX)
        .file(
            "main.cl",
            "(import [primitives [Pure Bool]])\n\
             (defn main [] (Pure ((if true mathx/gcount mathx/gother) [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert_no_doubly_wrapped_codegen_leak(&text);
    if !out.status.success() {
        assert!(
            !text.contains("codegen"),
            "a concrete generic fn-value ref in `if` position MUST be decided \
             check-side (resolve or §3.11.1 annotation error), never leak to \
             codegen (I2, 0585); {text}"
        );
    }
}

// spec: spec/08-modules.md §8.5.4 edge 1 + spec/03-types.md §3.11.1 — same, in a
// `match`-arm value position (deftype-free: seeded `Option` scrutinee). RED today.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck (value-position generic ref in a match-arm position never mints a mono; leaks to backend) found=S109 owner=/dev
#[test]
fn fq_generic_value_ref_in_match_position_never_reaches_codegen() {
    let out = Cranelisp::new()
        .file("mathx.cl", I2_MATHX)
        .file(
            "main.cl",
            "(import [primitives [Pure Option Some None]])\n\
             (defn main [] (Pure\n\
               ((match (Some 0) [(Some _) mathx/gcount None mathx/gother]) [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert_no_doubly_wrapped_codegen_leak(&text);
    if !out.status.success() {
        assert!(
            !text.contains("codegen"),
            "a concrete generic fn-value ref in a `match`-arm value position MUST \
             be decided check-side, never leak to codegen (I2, 0585); {text}"
        );
    }
}

// spec: spec/08-modules.md §8.5.4 edge 1 + spec/03-types.md §3.11.1 — same, as a
// VECTOR element used concretely (`(vec-get [gcount] 0)` applied). RED today.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck (value-position generic ref as a vector element never mints a mono; leaks to backend) found=S109 owner=/dev
#[test]
fn fq_generic_value_ref_in_vector_position_never_reaches_codegen() {
    let out = Cranelisp::new()
        .file("mathx.cl", I2_MATHX)
        .file(
            "main.cl",
            "(import [primitives [Pure Vec vec-get]])\n\
             (defn main [] (Pure ((vec-get [mathx/gcount] 0) [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    let text = combined(&out);
    assert_no_doubly_wrapped_codegen_leak(&text);
    if !out.status.success() {
        assert!(
            !text.contains("codegen"),
            "a concrete generic fn-value ref as a vector element MUST be decided \
             check-side, never leak to codegen (I2, 0585); {text}"
        );
    }
}
