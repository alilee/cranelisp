// QUARANTINED — Sprint 64 Wave 5 test-port. Not built or run by Cargo.
// FIXME: design/arch/fixmes/0139-harvest-tests-legacy-sprint59_neg.md
// Owning crate: src/ (optional — carry-forward complete)
// Owning skill: /int (optional)
// Quarantined: 2026-05-04
//
// This file's assertions test Rust-internal state with no clean e2e
// equivalent (or the language-behaviour subset has been carried forward
// into the spec-section files). Harvest into `#[cfg(test)]` unit tests
// inside the owning crate per memory/feedback_unit_tests_with_dev.md and
// memory/project_test_strategy.md. Source preserved verbatim; translation
// may require dev-dependency adjustments and import rewrites.

//! Sprint 59 Workstream D — module-boundary negative tests + Defect 8 latent gap.
//!
//! This file authors the four negative tests commissioned by Sprint 59
//! Workstream D plus a regression-guard test for the latent parallel bug in
//! `program_needs_trace` identified in `design/backend/defect-8-repro-notes.md`
//! §"Out-of-scope observations" item 1.
//!
//! Each test carries a `// spec:` annotation naming the section it validates
//! and a `FIXME(/skill)` note naming the resolver. Per
//! `memory/feedback_failing_not_ignored.md`, tests that currently fail are
//! committed as failing (no `#[ignore]`) — the failure IS the durable record.
//!
//! Workstream D deliverables (SPRINT.md):
//!   - §8.3.1 import-of-non-existent-name neg test
//!   - §8.3.7 super-in-top-level-module MUST-error (coverage already exists
//!     in tests/modules.rs::super_import_at_root_is_rejected_neg; this file
//!     adds a reinforcement neg test from a REPL-eval angle to round out
//!     the [Tested+Neg] promotion)
//!   - §8.3.9 import-inside-let MUST-reject neg test
//!   - §8.3.9 imports-available-before-definitions positive-of-negative test
//!     (an import form placed AFTER a definition that uses it must still
//!     work because imports are extracted before macro expansion; the
//!     negative shape is "definitions compile in the wrong order and fail")
//!
//! Defect 8 latent-gap test:
//!   - `defn_body_with_trace_triggers_extern_registration_neg` —
//!     the `program_needs_trace` scan gap identified in the Defect 8
//!     repro notes has the identical shape as `program_uses_test_forms`:
//!     a `defn` body containing `(trace …)` does not trigger
//!     `cranelisp_trace_format` registration, so JIT finalize fails with
//!     "can't resolve symbol trace". Defect 8's primary fix covers
//!     `run-test`/`discover-tests`; this test guards the parallel latent
//!     defect so the single-commit widening (per repro notes) does not
//!     regress.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
use tempfile::TempDir;

// ---------------------------------------------------------------------------
// Shared helper — tempdir project with named files.
// Mirrors the pattern in tests/ring2.rs and tests/modules.rs.
// ---------------------------------------------------------------------------

fn create_test_project(files: &[(&str, &str)]) -> TempDir {
    let dir = tempfile::tempdir().unwrap();
    for (path, content) in files {
        let full = dir.path().join(path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&full, content).unwrap();
    }
    dir
}

// ===========================================================================
// §8.3.1 — import of a non-existent name MUST error
// ===========================================================================

// spec: 08-modules §8.3.1 — each listed name MUST be a public name in the
// source module; otherwise it is a compile-time error.
//
// FIXME(/int): Sprint 59 Workstream D — module-boundary negative coverage.
// Distinct from the existing `import_private_name_errors` test (which
// covers §8.7.3 private-name exclusion); this test exercises the case
// where the name simply does not exist at all in the target module.
#[test]
fn import_of_non_existent_name_errors_neg() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod util)\n(import [main.util [does-not-exist]])\n(defn main [] (does-not-exist))",
        ),
        ("main/util.cl", "(defn exists [] 42)"),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
    assert!(
        result.is_err(),
        "importing a name that does not exist in the source module MUST produce a compile-time error (spec §8.3.1)"
    );
    let msg = match result {
        Err(e) => e.message().to_string(),
        Ok(_) => unreachable!(),
    };
    // Negative assertion: error message should name the missing symbol so
    // the user can fix the import — not a generic "error".
    assert!(
        msg.contains("does-not-exist") || msg.contains("not found") || msg.contains("unknown"),
        "error message should name the missing import or describe it as missing, got: {msg}"
    );
}

// ===========================================================================
// §8.3.7 — super in top-level module MUST error (REPL reinforcement)
// ===========================================================================

// spec: 08-modules §8.3.7 — using `super` in a top-level module MUST produce
// a compile-time error.
//
// FIXME(/int): Sprint 59 Workstream D — cross-check the existing batch-mode
// neg test (tests/modules.rs::super_import_at_root_is_rejected_neg) from
// the REPL-eval surface. A REPL session is inherently in the top-level
// `user` module, so `(import [super [*]])` at the prompt MUST reject with
// the same error as batch mode.
#[test]
fn super_import_at_repl_prompt_rejected_neg() {
    let mut s = repl_session();
    let result = s.eval("(import [super [*]])");
    assert!(
        result.is_err(),
        "super-import at REPL prompt (which is the 'user' top-level module) MUST be rejected (spec §8.3.7)"
    );
    let msg = result.err().unwrap().message().to_string();
    assert!(
        msg.contains("super") || msg.contains("top-level") || msg.contains("parent"),
        "error should mention 'super', 'top-level', or 'parent', got: {msg}"
    );
}

// ===========================================================================
// §8.3.9 — import placement (inside let MUST reject)
// ===========================================================================

// spec: 08-modules §8.3.9 — `import` forms MUST appear as top-level forms.
// They are extracted from the raw S-expression stream before macro expansion.
// A non-top-level `(import …)` — for instance inside a `let` body — MUST NOT
// be accepted.
//
// FIXME(/int): Sprint 59 Workstream D — §8.3.9 neg test (import inside let).
// The spec's "MUST appear as top-level forms" is currently unguarded in
// the test suite. Implementation shortcuts (e.g., scanning for import at
// ANY depth rather than only at the top level) would silently admit the
// invalid program.
#[test]
fn import_inside_let_rejected_neg() {
    let dir = create_test_project(&[
        (
            "main.cl",
            "(mod util)\n(defn main []\n  (let [x 1]\n    (import [main.util [helper]])\n    (helper)))",
        ),
        ("main/util.cl", "(defn helper [] 42)"),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
    assert!(
        result.is_err(),
        "(import …) inside a let body MUST be rejected — spec §8.3.9 requires imports to appear as top-level forms"
    );
    // Negative assertion: the error must not be a silent "helper not found"
    // (which would indicate the import was silently ignored rather than
    // rejected). The implementation must actively diagnose the placement.
    let msg = match result {
        Err(e) => e.message().to_string(),
        Ok(_) => unreachable!(),
    };
    assert!(
        msg.contains("import") || msg.contains("top-level") || msg.contains("let"),
        "error should diagnose the misplaced import, not silently hide it as 'unknown name'; got: {msg}"
    );
}

// ===========================================================================
// §8.3.9 — imports available before definitions (accumulation / ordering)
// ===========================================================================

// spec: 08-modules §8.3.9 — "An implementation MUST process `import` before
// compiling definitions in the same module, so that imported names are
// available during type checking and code generation."
//
// Also §8.3.9 — "A module MAY contain multiple `import` forms. Their effects
// accumulate."
//
// The negative shape this test guards: if imports are processed strictly
// in source order alongside definitions (rather than extracted en bloc
// before compilation), a `defn` placed ABOVE its matching import would
// fail to resolve the imported name. The spec explicitly requires the
// import effect to be visible to all definitions regardless of source
// position.
//
// FIXME(/int): Sprint 59 Workstream D — §8.3.9 imports-before-definitions
// neg test. This is a positive-of-negative check: the program MUST compile
// and run, proving that imports are extracted before compilation (the
// negative being a compile error that would indicate order-sensitive
// processing).
#[test]
fn import_below_use_still_available_before_definitions() {
    let dir = create_test_project(&[
        (
            "main.cl",
            // defn ABOVE the import — per §8.3.9 the import MUST still be
            // available to `main` at typecheck time because imports are
            // extracted before compilation.
            "(mod util)\n(defn main [] (helper))\n(import [main.util [helper]])",
        ),
        ("main/util.cl", "(defn helper [] 42)"),
    ]);
    let result = helpers::batch_run_file(&dir.path().join("main.cl"), &[]);
    match result {
        Ok((value, _ty)) => assert_eq!(
            value, 42,
            "imports MUST be extracted before compilation so `main` sees `helper` even though the import is textually below (spec §8.3.9)"
        ),
        Err(e) => panic!(
            "program MUST compile — imports are extracted before compilation per spec §8.3.9; got error: {}",
            e.message()
        ),
    }
}

// ===========================================================================
// Defect 8 latent gap — program_needs_trace parallel scan-gap regression guard
// ===========================================================================

// spec: design/backend/defect-8-repro-notes.md §"Out-of-scope observations"
// item 1; `src/session_v4.rs::program_needs_trace` must scan `TopLevel::Defn`
// bodies, not just `TopLevel::Expr`, so a `defn` body referencing `trace`
// triggers the `cranelisp_trace_format` extern registration before JIT
// finalize. The parallel latent bug has the identical shape as the
// `program_uses_test_forms` scan gap that Defect 8's primary fix widens.
//
// Per the repro notes: the Defect 8 fix ideally widens BOTH predicates in
// one commit (or refactors to a shared helper). This test guards the
// `program_needs_trace` half so the widening does not accidentally stop
// at `program_uses_test_forms`.
//
// Expected behaviour before the fix: this test fails with a Cranelift JIT
// panic "can't resolve symbol trace" (or similar) at `finalize_definitions`,
// matching the Defect 8 failure signature transposed to `trace`.
//
// FIXME(/int): Sprint 59 Workstream B Defect 8 — widen `program_needs_trace`
// alongside `program_uses_test_forms` in the single commit that resolves
// Defect 8. Repro notes at design/backend/defect-8-repro-notes.md.
#[test]
fn defn_body_with_trace_triggers_extern_registration_neg() {
    let mut s = repl_session_with_test_prelude();

    // Define a `defn` whose BODY references `(trace …)`. This is a
    // `TopLevel::Defn`, not a `TopLevel::Expr`, so the current
    // `program_needs_trace` predicate (which only scans `TopLevel::Expr`)
    // returns false and the trace extern is never registered for this
    // batch. Expected: JIT finalize fails with "can't resolve symbol
    // trace" or equivalent.
    //
    // Once the fix widens the predicate to scan `TopLevel::Defn` bodies,
    // this test flips green — the extern is registered, the batch finalises,
    // and calling `trace-fact` returns successfully.
    let result = s.eval("(defn trace-fact [n] (trace (add-i64 n 1)))");

    match result {
        Ok(_) => {
            // Extern was registered — the predicate was widened correctly.
            // Now verify we can actually invoke the defn and it doesn't
            // crash at runtime either.
            let invoke = s.eval("(trace-fact 5)");
            assert!(
                invoke.is_ok(),
                "invoking a defn whose body references `trace` MUST succeed once the extern is registered — got: {:?}",
                invoke.err().map(|e| e.message().to_string())
            );
        }
        Err(e) => panic!(
            "defining `(defn trace-fact [n] (trace (add-i64 n 1)))` MUST succeed — \
             `program_needs_trace` must widen to scan `TopLevel::Defn` bodies so \
             the `cranelisp_trace_format` extern is registered for this batch. \
             Current failure: {}",
            e.message()
        ),
    }
}
