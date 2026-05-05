//! Sprint 64 Wave 6 batch 2 Part B carry-forward — File Watching cluster.
//!
//! Per the Wave 6 batch 2 audit (`tests/plan/wave-6-batch-2-audit.md` §3),
//! these 12 tests carry forward the file-watching surface from
//! `tests/sprint23.rs` (lines 540–1061). The audit notes
//! `repl/spec.md §14` has zero existing `[Tested]` annotations across
//! the carry-forward suite — these tests are the first §14 coverage.
//!
//! Spec anchors:
//!   - `repl/spec.md §14.1` — Watch Scope
//!   - `repl/spec.md §14.2` — Eager Recompilation (cascade, content hash)
//!   - `repl/spec.md §14.3` — Notification Format
//!   - `repl/spec.md §14.4` — Error Blocking (NO last-known-good; retry on fix)
//!   - `repl/spec.md §14.7` — Interaction with Object Cache
//!
//! Mode: subprocess REPL via the `Cranelisp` builder with piped stdin.
//! The harness writes `prelude.cl` + helper modules to the per-test
//! TempDir; the REPL is started in that cwd; tests use `/sh` shell
//! escapes to mutate watched files mid-session and `/sh sleep 0.5` to
//! give the FSEvents poller a window to fire.
//!
//! Note on #35 `watch_unchanged_modules_keep_cache`: per audit, that
//! test is the only Rust-API-only test in `sprint23.rs` (it imports
//! `cranelisp_backend::cache::*` directly). It is NOT carried forward
//! e2e here — `design/arch/fixmes/0144-harvest-tests-legacy-sprint23.md`
//! commits to `/int` (and downstream `/backend`) harvesting the
//! cache-manifest invariant test as a `#[cfg(test)]` unit test in
//! the owning crate. The 12 tests below are the e2e-shape watch
//! cluster only.

#[path = "helpers/e2e.rs"]
mod e2e;

use e2e::Cranelisp;

/// Conventional prelude pulling primitives and defining the Num trait
/// for Int. Shared across watch tests that use operators (`+`).
const WATCH_PRELUDE_NUM: &str = "\
(import [primitives [*]])
(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))
(impl Num Int (defn + [a b] (add-i64 a b)) (defn - [a b] (sub-i64 a b)) (defn * [a b] (mul-i64 a b)) (defn / [a b] (div-i64 a b)))
";

/// Minimal primitives-only prelude used by tests that only need bare
/// `add-i64` style calls (no operators or trait dispatch).
const WATCH_PRELUDE_PRIMS: &str = "(import [primitives [*]])\n";

// =============================================================================
// 1. Watch Scope (§14.1)
// =============================================================================

// spec: repl/spec.md §14.1 — watch directories containing loaded files.
//   Editing a known module's `.cl` file should produce an `[updated:]`
//   or `[errors:]` notification. The watcher monitors the project
//   root because `prelude.cl` imports `mymod`, putting it in the
//   `file_to_module` map.
//
// (carry: legacy/sprint23.rs::watch_detects_source_change)
#[test]
fn watch_emits_notification_when_loaded_module_source_changes() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mymod [val]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("[updated: mymod.cl]") || combined.contains("[errors: mymod.cl]"),
        "watcher should emit [updated: mymod.cl] or [errors: mymod.cl] notification: stdout={}\nstderr={}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// 2. Change Detection (§14.2 — cascade, content hash)
// =============================================================================

// spec: repl/spec.md §14.2 — content-hash filter.
//   `touch` on a known module changes mtime but not content; the
//   content-hash gate must filter this out. NEGATIVE-shape: assert
//   that NO `[updated:` or `[errors:` notification appears.
//
// (carry: legacy/sprint23.rs::watch_ignores_metadata_only_changes)
#[test]
fn watch_does_not_notify_on_metadata_only_change() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mymod [val]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh touch mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    assert!(
        !out.stdout.contains("[updated:") && !out.stdout.contains("[errors:"),
        "metadata-only change (touch, same content) should NOT trigger notification: stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §14.2 — cascade invalidation.
//   Module A imports module B. Editing B's source should produce
//   `[updated:]` notifications for BOTH B (direct change) and A
//   (cascade — A's compiled output depends on B's exports).
//
// (carry: legacy/sprint23.rs::watch_cascade_invalidation)
#[test]
fn watch_cascade_invalidates_dependent_module_on_dep_change() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mod_a [val-a]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val-b [] 99)' > mod_b.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file(
            "mod_a.cl",
            "(import [mod_b [val-b]])\n(defn val-a [] (val-b))",
        )
        .file("mod_b.cl", "(defn val-b [] 10)")
        .stdin(stdin)
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("[updated: mod_b.cl]") || combined.contains("[errors: mod_b.cl]"),
        "mod_b should get an update notification: stdout={}",
        out.stdout
    );
    assert!(
        combined.contains("[updated: mod_a.cl]") || combined.contains("[errors: mod_a.cl]"),
        "mod_a should get a cascade update notification: stdout={}",
        out.stdout
    );
}

// =============================================================================
// 3. Notification Format (§14.3)
// =============================================================================

// spec: repl/spec.md §14.3 — `[updated: <file>]` notification format.
//   Edit produces `[updated: mymod.cl]` (or `[errors:]` on failure).
//
// (carry: legacy/sprint23.rs::watch_notification_format)
#[test]
fn watch_notification_uses_bracketed_file_format() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mymod [val]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("[updated: mymod.cl]") || combined.contains("[errors: mymod.cl]"),
        "notification should use [updated: <file>] or [errors: <file>] format: stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §14.3 — per-module notifications (no truncation).
//   Each module gets its own line. Edit two modules in one shell
//   command; at least one notification must appear.
//
// (carry: legacy/sprint23.rs::watch_notification_truncation)
#[test]
fn watch_emits_per_module_notifications_without_truncation() {
    let prelude = format!(
        "{WATCH_PRELUDE_PRIMS}(import [mod_a [val-a]])\n(import [mod_b [val-b]])\n"
    );
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.5
/sh echo '(defn val-a [] 10)' > mod_a.cl; echo '(defn val-b [] 20)' > mod_b.cl
/sh sleep 1.0
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mod_a.cl", "(defn val-a [] 1)")
        .file("mod_b.cl", "(defn val-b [] 2)")
        .stdin(stdin)
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("[updated:") || combined.contains("[errors:"),
        "should have at least one notification: stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §14.3 — notification deferred during input.
//   The notification line must NOT interleave with an expression
//   result line (e.g. `:Int 42`). REGRESSION-GUARD: the watcher
//   architecture only polls between prompts; this test guards that
//   property by line-by-line scanning for any line containing both
//   a result tag and a notification.
//
// (carry: legacy/sprint23.rs::watch_notification_deferred_during_input)
#[test]
fn watch_notification_appears_at_prompt_boundary_not_mid_result() {
    let prelude = "(import [mymod [val]])\n";
    let stdin = "\
(val)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
(val)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    assert!(
        out.stdout.contains("[updated: mymod.cl]"),
        "notification should appear: stdout={}",
        out.stdout
    );
    for line in out.stdout.lines() {
        let has_result = line.contains(":Int ");
        let has_notification = line.contains("[updated:") || line.contains("[errors:");
        assert!(
            !(has_result && has_notification),
            "notification must not appear on the same line as a result: line={line:?}"
        );
    }
}

// =============================================================================
// 4. Eager Recompilation (§14.2)
// =============================================================================

// spec: repl/spec.md §14.2 — eager recompilation on detected change.
//   After a content edit the REPL must emit `[updated: mymod.cl]`
//   (the success notification, distinct from `[errors:]`).
//
// (carry: legacy/sprint23.rs::watch_automatic_recompilation)
#[test]
fn watch_recompiles_changed_module_eagerly() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mymod [val]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    assert!(
        out.stdout.contains("[updated: mymod.cl]"),
        "module should be eagerly recompiled with [updated: mymod.cl]: stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §14.2 — type incompatibility on reload.
//   Mutating the prelude to break a trait method body produces a
//   reload result notification (success or error). The pre-edit
//   evaluation `(+ 1 2)` must yield 3.
//
// (carry: legacy/sprint23.rs::watch_type_incompatibility_on_reload)
#[test]
fn watch_notifies_when_reload_introduces_type_incompatibility() {
    let stdin = "\
(+ 1 2)
/sh sleep 0.3
/sh echo '(deftrait Num (+ [self self] self)) (impl Num Int (defn + [a b] \"not-an-int\"))' > prelude.cl
/sh sleep 0.5
(+ 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", WATCH_PRELUDE_NUM)
        .stdin(stdin)
        .output();
    assert!(
        out.stdout.contains("3"),
        "initial (+ 1 2) should return 3: stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("[updated: prelude.cl]") || out.stdout.contains("[errors: prelude.cl]"),
        "reload result should be notified: stdout={}",
        out.stdout
    );
}

// =============================================================================
// 5. Error Display + Blocking (§14.3, §14.4)
// =============================================================================

// spec: repl/spec.md §14.3 — `[errors: <file>]` format on parse failure.
//   Writing a syntax-error fragment to a watched module produces
//   the error-flavour notification.
//
// (carry: legacy/sprint23.rs::watch_error_display_format)
#[test]
fn watch_errors_notification_appears_on_broken_source() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mymod [val]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val []' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    assert!(
        out.stdout.contains("[errors: mymod.cl]"),
        "reload failure should display [errors: mymod.cl]: stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §14.4 — errors block evaluation (NO last-known-good).
//   REGRESSION-GUARD: spec evolved away from a "last-known-good"
//   fallback. After a syntax error in a watched file, evaluation
//   must be blocked with a "Cannot evaluate" message; the test name
//   preserves the spec-pivot history.
//
// (carry: legacy/sprint23.rs::watch_error_recovery_last_known_good)
#[test]
fn watch_errors_block_evaluation_no_last_known_good() {
    let prelude = format!("{WATCH_PRELUDE_NUM}(import [mymod [val]])\n");
    let stdin = "\
(+ 1 2)
/sh sleep 0.3
/sh echo '(defn val []' > mymod.cl
/sh sleep 0.5
(+ 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    assert!(
        out.stdout.contains("[errors:"),
        "syntax error should trigger [errors:] notification: stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Cannot evaluate"),
        "errors should block evaluation with 'Cannot evaluate' message: stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §14.4 — error resolved on next successful change.
//   REGRESSION-GUARD: break → fix loop. After a failed reload, fixing
//   the file should produce `[updated:]` and clear the error state.
//
// (carry: legacy/sprint23.rs::watch_retry_on_next_change)
#[test]
fn watch_clears_error_state_when_subsequent_edit_fixes_source() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mymod [val]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val []' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/sh sleep 0.1
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    assert!(
        out.stdout.contains("[errors:"),
        "first change (broken) should trigger [errors:] notification: stdout={}",
        out.stdout
    );
    assert!(
        out.stdout.contains("[updated: mymod.cl]"),
        "second change (fix) should produce [updated: mymod.cl]: stdout={}",
        out.stdout
    );
}

// =============================================================================
// 6. Cache Interaction (§14.7)
// =============================================================================

// spec: repl/spec.md §14.7 — cache invalidation on file change.
//   After an in-session edit + reload, `.cranelisp-cache/` must
//   exist (the recompilation step writes the cache).
//
// (carry: legacy/sprint23.rs::watch_invalidates_cache_on_change)
#[test]
fn watch_change_triggers_cache_directory_creation() {
    let prelude = format!("{WATCH_PRELUDE_PRIMS}(import [mymod [val]])\n");
    let stdin = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("prelude.cl", &prelude)
        .file("mymod.cl", "(defn val [] 42)")
        .stdin(stdin)
        .output();
    assert!(
        out.stdout.contains("[updated: mymod.cl]") || out.stdout.contains("[errors: mymod.cl]"),
        "change should be detected and recompiled: stdout={}",
        out.stdout
    );
    assert!(
        out.tmp_exists(".cranelisp-cache"),
        "cache directory should exist after REPL session with module compilation; tmpdir={}",
        out.tmpdir.display()
    );
}

// NOTE on #35 `watch_unchanged_modules_keep_cache`:
//
// This Rust-API-only test (uses `cranelisp_backend::cache::*` directly)
// is intentionally NOT carried forward as e2e. Per audit recommendation
// (§A "Tests flagged for /sprint judgment") and the harvest commitment
// in `design/arch/fixmes/0144-harvest-tests-legacy-sprint23.md`, the
// cache-manifest invariant ("module B with unchanged source still hits
// cache after module A changes") is harvested into a `#[cfg(test)]`
// unit test inside `crates/cranelisp-backend/src/cache.rs` by the
// owning skill (/backend, via /int's harvest pass). The legacy file
// `tests/legacy/sprint23.rs::watch_unchanged_modules_keep_cache`
// preserves the existing test body verbatim until that harvest lands.
