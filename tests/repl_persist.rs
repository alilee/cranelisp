//! Sprint 64 Wave 6 batch 2 Part B carry-forward — Session Persistence
//! (`user.cl`) cluster.
//!
//! Per the Wave 6 batch 2 audit, these 16 tests carry forward the
//! session-persistence surface from `tests/sprint23.rs` (lines 1241–2047).
//! The audit notes `repl/spec.md §15` across-restart has zero existing
//! `[Tested]` annotations across the carry-forward suite — these tests are the
//! first §15.2 across-restart coverage. The cluster includes 8 named
//! `_bug{N}_` / `_neg_` / `_bug_macro_*` REGRESSION-GUARD tests that
//! pin specific Sprint 23 defects.
//!
//! Spec anchors:
//!   - `repl/spec.md §15.1` — Source Regeneration
//!   - `repl/spec.md §15.2` — Session Restore
//!   - `repl/spec.md §15.4` — Regeneration Integrity
//!   - `repl/spec.md §15.5` — File Watching Integration
//!   - `repl/spec.md §15.6` — Redefinition
//!   - `design/int/session-persistence.md §2` — definition-like inputs only
//!   - `design/int/session-persistence.md §3` — cache speed restart
//!   - `design/int/session-persistence.md §4` — self-write suppression
//!
//! Mode: subprocess REPL via the `Cranelisp` builder with piped
//! stdin. Most tests run two sessions in the same TempDir via
//! `out.run_again()` to exercise the across-restart surface.
//! Tests requiring a prelude use `PreludeVariant::TestStandard`
//! (operators, ADTs); the macro-expansion-leak tests use the
//! workspace stdlib via `use_workspace_stdlib_for_stdlib_conformance_only()`
//! because they validate that prelude macros (`str`) round-trip
//! through `user.cl` correctly.

#[path = "helpers/e2e.rs"]
mod e2e;

use e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// 1. Definitions survive restart (§15.2 — Session Restore)
// =============================================================================

// spec: repl/spec.md §15.2 — defn persisted via source regeneration.
//   Session 1 defines `foo`; session 2 (same TempDir) calls `(foo)`
//   and gets 42 from the regenerated `user.cl`.
//
// (carry: legacy/sprint23.rs::persist_defn_survives_restart)
#[test]
fn persist_defn_survives_restart_via_user_cl() {
    let first = Cranelisp::new()
        .repl()
        .stdin("(defn foo [] 42)\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly: stderr={}",
        first.stderr
    );

    let second = first.run_again().repl().stdin("(foo)\n/quit\n").output();
    assert!(
        second.stdout.contains("42"),
        "session 2 should find (foo) returning 42 from persisted user.cl: stdout={}",
        second.stdout
    );
}

// spec: repl/spec.md §15.2 — deftype persisted via source regeneration.
//   Session 1 defines a sum type; session 2 references its constructor.
//
// (carry: legacy/sprint23.rs::persist_deftype_survives_restart)
#[test]
fn persist_deftype_constructor_survives_restart() {
    let first = Cranelisp::new()
        .repl()
        .stdin("(deftype Color Red Green Blue)\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly: stderr={}",
        first.stderr
    );

    let second = first
        .run_again()
        .repl()
        .stdin("Color.Red\n/quit\n")
        .output();
    assert!(
        second.stdout.contains("Red") || second.stdout.contains("Color"),
        "session 2 should recognise Color.Red from persisted user.cl: stdout={}",
        second.stdout
    );
}

// spec: repl/spec.md §15.2 — import persisted via source regeneration.
//   REGRESSION-GUARD: legacy carried `FIXME(/int)` (Sprint 58 Wave 2c)
//   for "second session does not see persisted import". The cache
//   directory is deleted between sessions to force session 2 to
//   recompile from `user.cl` (testing true persistence rather than
//   cache-hit loading). Verify the harvest disposition in
//   `design/arch/fixmes/0144-harvest-tests-legacy-sprint23.md` if
//   this test fails in a future regression.
//
// (carry: legacy/sprint23.rs::persist_import_survives_restart)
#[test]
fn persist_import_survives_restart_after_cache_wipe() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .file("helper.cl", "(defn helper-val [] 99)")
        .stdin("(import [helper [helper-val]])\n(helper-val)\n/quit\n")
        .output();
    assert!(
        first.stdout.contains("99"),
        "session 1 should successfully import and call helper-val: stdout={}",
        first.stdout
    );
    assert!(
        first.tmp_exists("user.cl"),
        "user.cl should exist after session 1; tmpdir={}",
        first.tmpdir.display()
    );
    let user_cl = first.read_tmp("user.cl");
    assert!(
        user_cl.contains("import") && user_cl.contains("helper"),
        "user.cl should contain the import statement: {user_cl}"
    );

    // Wipe the cache so session 2 must recompile from user.cl, not
    // a cache hit.
    let cache_dir = first.tmpdir.join(".cranelisp-cache");
    if cache_dir.exists() {
        std::fs::remove_dir_all(&cache_dir).expect("rm .cranelisp-cache");
    }

    let second = first
        .run_again()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(helper-val)\n/quit\n")
        .output();
    assert!(
        second.stdout.contains("99"),
        "session 2 should find helper-val via persisted import in user.cl: stdout={}",
        second.stdout
    );
}

// =============================================================================
// 2. Backing file creation + validity (§15.1, §15.2, §15.4)
// =============================================================================

// spec: repl/spec.md §15.1 — user.cl created as backing file.
//   Defining a function materialises `user.cl` containing the
//   definition.
//
// (carry: legacy/sprint23.rs::persist_user_cl_created)
#[test]
fn persist_user_cl_is_created_with_definition_after_session() {
    let out = Cranelisp::new()
        .repl()
        .stdin("(defn bar [] 7)\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "REPL should exit cleanly: stderr={}",
        out.stderr
    );
    assert!(
        out.tmp_exists("user.cl"),
        "user.cl should be created in the project directory after defining bar"
    );
    let contents = out.read_tmp("user.cl");
    assert!(
        contents.contains("bar"),
        "user.cl should contain the definition of bar: {contents}"
    );
}

// spec: repl/spec.md §15.4 — Regeneration Integrity (valid parseable source).
//   REGRESSION-GUARD: multi-angle. Asserts (a) dependency-order
//   (double appears before quad since quad calls double), AND
//   (b) the regenerated file is itself importable by another session.
//
// (carry: legacy/sprint23.rs::persist_user_cl_is_valid_source)
#[test]
fn persist_user_cl_is_valid_source_with_topological_ordering() {
    let stdin1 = "\
(import [primitives [*]])
(defn double [:Int x] (add-i64 x x))
(defn quad [:Int x] (double (double x)))
(quad 3)
/quit
";
    let first = Cranelisp::new().repl().stdin(stdin1).output();
    assert!(
        first.stdout.contains("12"),
        "session should compute (quad 3) = 12: stdout={}",
        first.stdout
    );
    assert!(first.tmp_exists("user.cl"), "user.cl should exist");
    let contents = first.read_tmp("user.cl");
    assert!(!contents.is_empty(), "user.cl should not be empty");
    assert!(
        contents.contains("double") && contents.contains("quad"),
        "user.cl should contain both double and quad: {contents}"
    );

    // Second pass: import the regenerated user.cl into a fresh
    // session and call `quad` from it. Validates the file is
    // valid module source.
    let stdin2 = "\
(import [primitives [*]])
(import [user [quad]])
(quad 5)
/quit
";
    let second = first.run_again().repl().stdin(stdin2).output();
    assert!(
        second.stdout.contains("20"),
        "importing user.cl and calling (quad 5) should produce 20: stdout={}",
        second.stdout
    );
}

// =============================================================================
// 3. Cache Speed (§15.2 + design/int/session-persistence.md §3)
// =============================================================================

// spec: repl/spec.md §15.2 — cache speeds restart.
//   The durable assertion is correctness across all three sessions
//   (gamma=3 for each); timing is best-effort eprintln only.
//
// (carry: legacy/sprint23.rs::persist_cache_speeds_restart)
#[test]
fn persist_cache_keeps_results_consistent_across_warm_restarts() {
    let stdin1 = "\
(import [primitives [*]])
(defn alpha [] 1)
(defn beta [] (add-i64 (alpha) 1))
(defn gamma [] (add-i64 (beta) 1))
(gamma)
/quit
";
    let first = Cranelisp::new().repl().stdin(stdin1).output();
    assert!(
        first.stdout.contains("3"),
        "session 1: (gamma) should be 3: stdout={}",
        first.stdout
    );

    let stdin_check = "(gamma)\n/quit\n";
    let start2 = std::time::Instant::now();
    let second = first.run_again().repl().stdin(stdin_check).output();
    let dur2 = start2.elapsed();
    assert!(
        second.stdout.contains("3"),
        "session 2: (gamma) should be 3: stdout={}",
        second.stdout
    );

    let start3 = std::time::Instant::now();
    let third = second.run_again().repl().stdin(stdin_check).output();
    let dur3 = start3.elapsed();
    assert!(
        third.stdout.contains("3"),
        "session 3: (gamma) should be 3: stdout={}",
        third.stdout
    );

    eprintln!(
        "persist_cache_keeps_results_consistent_across_warm_restarts: \
         session 2 = {dur2:?}, session 3 = {dur3:?}"
    );
}

// =============================================================================
// 4. File watcher interaction (§15.5)
// =============================================================================

// spec: design/int/session-persistence.md §4 — self-write suppression.
//   REGRESSION-GUARD: defining a function triggers a save to
//   `user.cl`; the watcher must NOT emit a notification for that
//   self-write because the content hash matches what the REPL
//   itself wrote.
//
// (carry: legacy/sprint23.rs::persist_watcher_ignores_self_write)
#[test]
fn persist_watcher_ignores_self_write_to_user_cl() {
    let stdin = "\
(defn self-write-test [] 77)
/sh sleep 0.5
(add-i64 1 1)
/quit
";
    let out = Cranelisp::new().repl().stdin(stdin).output();
    assert!(
        !out.stdout.contains("[updated: user.cl]") && !out.stdout.contains("[errors: user.cl]"),
        "self-write to user.cl should NOT trigger a watcher notification: stdout={}",
        out.stdout
    );
}

// =============================================================================
// 5. Negative — bare expressions not saved (§15.1 + design §2)
// =============================================================================

// spec: design/int/session-persistence.md §2 — only definition-like
//   inputs saved.
//   REGRESSION-GUARD (`_neg_`): bare `(add-i64 1 2)` MUST NOT appear
//   in `user.cl`.
//
// (carry: legacy/sprint23.rs::persist_neg_bare_expr_not_saved)
#[test]
fn persist_neg_bare_expressions_are_not_written_to_user_cl() {
    let stdin = "\
(add-i64 1 2)
(add-i64 10 20)
/quit
";
    let out = Cranelisp::new().repl().stdin(stdin).output();
    assert!(
        out.status.success(),
        "REPL should exit cleanly: stderr={}",
        out.stderr
    );
    if out.tmp_exists("user.cl") {
        let contents = out.read_tmp("user.cl");
        assert!(
            !contents.contains("add-i64 1 2") && !contents.contains("add-i64 10 20"),
            "user.cl must NOT contain bare expressions: {contents}"
        );
    }
    // Absence of user.cl is also acceptable — no definitions means
    // no backing file is needed.
}

// =============================================================================
// 6. Bug-1: all defns saved including constrained polymorphic fns
// =============================================================================

// spec: repl/spec.md §15.2 — all definitions saved including
//   constrained polymorphic fns.
//   REGRESSION-GUARD (`_bug1_`): defines 3 fns (one constrained-poly
//   via the `+` operator) and asserts ALL appear in `user.cl`.
//   The original Sprint 23 defect was that
//   `compile_and_register_defn` was skipped for constrained fns,
//   leaving no `def_codegen` entry and no stored sexp.
//
// (carry: legacy/sprint23.rs::persist_bug1_all_defns_saved_to_user_cl)
#[test]
fn persist_bug1_all_defns_including_constrained_poly_saved_to_user_cl() {
    let stdin = "\
(defn add [x y] (+ x y))
(defn double [:Int x] (add-i64 x x))
(defn triple [:Int x] (add-i64 x (add-i64 x x)))
/quit
";
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(stdin)
        .output();
    assert!(
        out.status.success(),
        "REPL should exit cleanly: stderr={}",
        out.stderr
    );
    assert!(
        out.tmp_exists("user.cl"),
        "user.cl should exist after defining functions"
    );
    let contents = out.read_tmp("user.cl");
    assert!(
        contents.contains("defn add"),
        "user.cl should contain constrained poly fn 'add': {contents}"
    );
    assert!(
        contents.contains("defn double"),
        "user.cl should contain fn 'double': {contents}"
    );
    assert!(
        contents.contains("defn triple"),
        "user.cl should contain fn 'triple': {contents}"
    );
}

// spec: repl/spec.md §15.2 — constrained polymorphic fn restored
//   and callable across restart.
//   REGRESSION-GUARD (`_bug1_` continuation): cache wiped between
//   sessions; session 2 must recompile from `user.cl`.
//
// (carry: legacy/sprint23.rs::persist_bug1_constrained_fn_survives_restart)
#[test]
fn persist_bug1_constrained_polymorphic_fn_callable_after_restart() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(defn add [x y] (+ x y))\n(add 10 20)\n/quit\n")
        .output();
    assert!(
        first.stdout.contains("30"),
        "session 1: (add 10 20) should be 30: stdout={}",
        first.stdout
    );
    assert!(
        first.tmp_exists("user.cl"),
        "user.cl should exist after session 1"
    );
    let user_cl = first.read_tmp("user.cl");
    assert!(
        user_cl.contains("defn add"),
        "user.cl should contain the constrained poly fn 'add': {user_cl}"
    );

    let cache_dir = first.tmpdir.join(".cranelisp-cache");
    if cache_dir.exists() {
        std::fs::remove_dir_all(&cache_dir).expect("rm .cranelisp-cache");
    }

    let second = first
        .run_again()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(add 100 200)\n/quit\n")
        .output();
    assert!(
        second.stdout.contains("300"),
        "session 2: (add 100 200) should be 300 from restored constrained fn: stdout={}",
        second.stdout
    );
}

// =============================================================================
// 7. Bug-2: cache files created after restore
// =============================================================================

// spec: repl/spec.md §15.2 + design/int/session-persistence.md §3 —
//   cache written on restore.
//   REGRESSION-GUARD (`_bug2_`): session 1 saves `user.cl`;
//   session 2 (restoring through `compile_checked_program`) must
//   produce `user.meta.json` + `user.o` in `.cranelisp-cache/`.
//
// (carry: legacy/sprint23.rs::persist_bug2_cache_files_created_after_restore)
#[test]
fn persist_bug2_cache_files_materialise_after_session_restore() {
    let first = Cranelisp::new()
        .repl()
        .stdin("(defn cached-fn [] 42)\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1: REPL should exit cleanly: stderr={}",
        first.stderr
    );
    assert!(
        first.tmp_exists("user.cl"),
        "user.cl should exist after session 1"
    );

    let second = first.run_again().repl().stdin("/quit\n").output();
    assert!(
        second.status.success(),
        "session 2: REPL should exit cleanly: stderr={}",
        second.stderr
    );
    assert!(
        second.tmp_exists(".cranelisp-cache"),
        ".cranelisp-cache/ should exist after restoring user.cl"
    );

    let cache_dir = second.tmpdir.join(".cranelisp-cache");
    let has_user_meta = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries.filter_map(|e| e.ok()).any(|e| {
                let n = e.file_name();
                let n = n.to_string_lossy();
                n.contains("user") && n.ends_with(".meta.json")
            })
        })
        .unwrap_or(false);
    assert!(
        has_user_meta,
        "user.meta.json should exist in .cranelisp-cache/ after restoring user.cl"
    );
    let has_user_o = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries.filter_map(|e| e.ok()).any(|e| {
                let n = e.file_name();
                let n = n.to_string_lossy();
                n.contains("user") && n.ends_with(".o")
            })
        })
        .unwrap_or(false);
    assert!(
        has_user_o,
        "user.o should exist in .cranelisp-cache/ after restoring user.cl"
    );
}

// spec: design/int/session-persistence.md §3 — cache written after
//   first session save (no restore needed).
//   Multi-angle complement to `_bug2_`: same artefacts asserted
//   after the FIRST session, with no restore involved. PRESERVE both
//   per the multi-angle rule.
//
// (carry: legacy/sprint23.rs::cache_repl_produces_object_files)
#[test]
fn persist_first_session_immediately_produces_user_object_files() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(defn double [x] (* x 2))\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "REPL should exit cleanly: stderr={}",
        out.stderr
    );
    assert!(
        out.tmp_exists("user.cl"),
        "user.cl should exist after defining a function"
    );
    assert!(
        out.tmp_exists(".cranelisp-cache"),
        ".cranelisp-cache/ should exist after first session save"
    );
    let cache_dir = out.tmpdir.join(".cranelisp-cache");
    let has_user_meta = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries.filter_map(|e| e.ok()).any(|e| {
                let n = e.file_name();
                let n = n.to_string_lossy();
                n.contains("user") && n.ends_with(".meta.json")
            })
        })
        .unwrap_or(false);
    assert!(
        has_user_meta,
        "user.meta.json should exist in .cranelisp-cache/ after first session"
    );
    let has_user_o = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries.filter_map(|e| e.ok()).any(|e| {
                let n = e.file_name();
                let n = n.to_string_lossy();
                n.contains("user") && n.ends_with(".o")
            })
        })
        .unwrap_or(false);
    assert!(
        has_user_o,
        "user.o should exist in .cranelisp-cache/ after first session"
    );
}

// =============================================================================
// 8. Bug-3: accumulated definitions across sessions; no phantoms
// =============================================================================

// spec: repl/spec.md §15.2 — accumulated definitions across sessions.
//   REGRESSION-GUARD (`_bug3_`): session 1 defines `foo`;
//   session 2 defines `bar`; user.cl must contain BOTH after
//   session 2 (foo restored from session 1's user.cl, then bar
//   added by session 2's save).
//
// (carry: legacy/sprint23.rs::persist_bug3_accumulated_definitions_across_sessions)
#[test]
fn persist_bug3_accumulates_definitions_across_session_restarts() {
    let first = Cranelisp::new()
        .repl()
        .stdin("(defn foo [] 42)\n/quit\n")
        .output();
    assert!(first.status.success(), "session 1 failed: {}", first.stderr);
    let contents1 = first.read_tmp("user.cl");
    assert!(
        contents1.contains("defn foo"),
        "session 1 should save foo: {contents1}"
    );

    let second = first
        .run_again()
        .repl()
        .stdin("(defn bar [] 99)\n/quit\n")
        .output();
    assert!(
        second.status.success(),
        "session 2 failed: {}",
        second.stderr
    );
    let contents2 = second.read_tmp("user.cl");
    assert!(
        contents2.contains("defn foo"),
        "user.cl should still contain foo from session 1: {contents2}"
    );
    assert!(
        contents2.contains("defn bar"),
        "user.cl should contain bar from session 2: {contents2}"
    );
}

// spec: repl/spec.md §15.2 — no stale defns from unrelated sessions.
//   REGRESSION-GUARD (`_bug3_neg_`): negative-coverage complement
//   to the accumulation test. user.cl must NOT contain phantom
//   definitions (`gamma`, `fact` were never defined in either
//   session).
//
// (carry: legacy/sprint23.rs::persist_bug3_neg_no_phantom_definitions)
#[test]
fn persist_bug3_neg_no_phantom_definitions_appear_in_user_cl() {
    let first = Cranelisp::new()
        .repl()
        .stdin("(defn alpha [] 1)\n/quit\n")
        .output();
    let second = first
        .run_again()
        .repl()
        .stdin("(defn beta [] 2)\n/quit\n")
        .output();
    let contents = second.read_tmp("user.cl");
    assert!(
        contents.contains("defn alpha"),
        "alpha should be in user.cl: {contents}"
    );
    assert!(
        contents.contains("defn beta"),
        "beta should be in user.cl: {contents}"
    );
    assert!(
        !contents.contains("defn gamma"),
        "phantom definition 'gamma' should NOT be in user.cl: {contents}"
    );
    assert!(
        !contents.contains("defn fact"),
        "phantom definition 'fact' should NOT be in user.cl: {contents}"
    );
}

// =============================================================================
// 9. Bug — macro expansion not leaked into user.cl
// =============================================================================

// spec: repl/spec.md §15.4 — Regeneration Integrity.
//   The saved `user.cl` MUST preserve the original source form, not
//   the macro-expanded form. `(str ...)` is a stdlib macro that
//   expands to `(str-concat (show ...) (show ...))`; the file must
//   contain `str ` (the original) and NOT `str-concat` (the expansion).
//   Uses workspace stdlib because `str` is a stdlib macro.
//
// (carry: legacy/sprint23.rs::persist_bug_macro_not_expanded_in_user_cl)
#[test]
fn persist_bug_user_cl_preserves_original_str_not_expanded_str_concat() {
    let out = Cranelisp::new()
        .repl()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .stdin("(defn greet [name] (str \"hello, \" name))\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "REPL should exit cleanly. stdout={}\nstderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.tmp_exists("user.cl"),
        "user.cl should exist after defining a function. stdout={}\nstderr={}",
        out.stdout,
        out.stderr
    );
    let contents = out.read_tmp("user.cl");
    assert!(
        contents.contains("str "),
        "user.cl should contain original `str` macro call, not expanded form: {contents}"
    );
    assert!(
        !contents.contains("str-concat"),
        "user.cl must NOT contain macro-expanded `str-concat`: {contents}"
    );
}

// spec: repl/spec.md §15.2 — fns using prelude macros survive restart.
//   REGRESSION-GUARD (`_bug_macro_*`): named Sprint 23 defect — the
//   batch-mode restore path was compiling `user.cl` before the
//   prelude's macros were available, producing "undefined variable:
//   str" on session 2. Uses workspace stdlib (real `str` macro).
//
// (carry: legacy/sprint23.rs::persist_bug_macro_usage_survives_restart)
#[test]
fn persist_bug_macro_usage_in_defn_survives_session_restart() {
    let first = Cranelisp::new()
        .repl()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .stdin("(defn greet [name] (str \"hello, \" name))\n(greet \"world\")\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly. stdout={}\nstderr={}",
        first.stdout,
        first.stderr
    );
    assert!(
        first.stdout.contains("hello, world"),
        "session 1: (greet \"world\") should produce \"hello, world\": stdout={}",
        first.stdout
    );

    let second = first
        .run_again()
        .repl()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .stdin("(greet \"cranelisp\")\n/quit\n")
        .output();
    assert!(
        second.status.success(),
        "session 2 should exit cleanly (not fail on str macro). stdout={}\nstderr={}",
        second.stdout,
        second.stderr
    );
    assert!(
        second.stdout.contains("hello, cranelisp"),
        "session 2: (greet \"cranelisp\") should produce \"hello, cranelisp\" from restored user.cl: stdout={}",
        second.stdout
    );
}

// =============================================================================
// 8. Bug 0220: cache-restored UserFns survive REPL-edit `.cl` regeneration
// =============================================================================

// spec: repl/spec.md §15.4 — Regeneration Integrity invariant 1 (round-trip
//   correctness). FIXME 0220 (resolved S81 W-E) closed the gap where a
//   cache-restored regular `UserFn` with NO REPL introspection record was
//   silently dropped from the regenerated backing `user.cl` when the user
//   edited a *different* symbol in the same module at the REPL. The fix is a
//   lazy re-read + re-parse of the backing `.cl`, driven from
//   `session_v4::regenerate_backing_file`; S122 generalised it from
//   `rehydrate_userfn_introspection_from_source` to every definition kind as
//   `src/save.rs::rehydrate_introspection_from_source`.
//
//   This e2e crosses cache-hit + REPL-edit + `.cl`-regen — the seam the
//   in-crate unit test (`src/save.rs::tests::
//   rehydrate_recovers_cache_loaded_userfn_dropped_from_regen`) cannot reach.
//   FIXME 0334.
//
//   Repro: session 1 has `keep`/`other`/`main` on disk in `user.cl` and runs,
//   populating the on-disk cache. Session 2 (same TempDir) loads the module
//   FROM CACHE — so `keep`/`other` carry no introspection record — then defines
//   a NEW symbol at the REPL, triggering `regenerate_backing_file`. The
//   regenerated `user.cl` MUST still contain `(defn keep …)` and
//   `(defn other …)`; without the 0220 fix they vanish.
#[test]
fn persist_bug0220_cache_restored_userfns_survive_repl_edit_regen() {
    // Session 1: a file-based entry module with two regular UserFns plus main.
    // Running it populates the on-disk `.cranelisp-cache/`.
    let first = Cranelisp::new()
        .file(
            "user.cl",
            "(defn keep [] 1)\n(defn other [] 2)\n(defn main [] (keep))\n",
        )
        .repl()
        .stdin("(keep)\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly: stdout={}\nstderr={}",
        first.stdout,
        first.stderr
    );
    assert!(
        first.tmpdir.join(".cranelisp-cache").exists(),
        "session 1 should populate the on-disk cache"
    );

    // Session 2: same TempDir, so `user.cl` loads FROM CACHE — `keep`/`other`
    // have no introspection record. Define a NEW symbol, which triggers
    // backing-file regeneration.
    let second = first
        .run_again()
        .repl()
        .stdin("(defn added [] 3)\n(added)\n/quit\n")
        .output();
    assert!(
        second.status.success(),
        "session 2 should exit cleanly: stdout={}\nstderr={}",
        second.stdout,
        second.stderr
    );

    // The regenerated user.cl MUST still contain the cache-restored UserFns.
    let regenerated = second.read_tmp("user.cl");
    assert!(
        regenerated.contains("(defn keep"),
        "cache-restored UserFn 'keep' MUST survive regen (FIXME 0220): {regenerated}"
    );
    assert!(
        regenerated.contains("(defn other"),
        "cache-restored UserFn 'other' MUST survive regen (FIXME 0220): {regenerated}"
    );
    // The newly-added symbol is also present (the edit that triggered regen).
    assert!(
        regenerated.contains("(defn added"),
        "the newly-defined symbol 'added' MUST be in the regenerated file: {regenerated}"
    );

    // Round-trip: a third session loads the regenerated file and `keep`/`other`
    // are still callable — proving they were not silently dropped.
    let third = second
        .run_again()
        .repl()
        .stdin("(keep)\n(other)\n/quit\n")
        .output();
    assert!(
        third.status.success(),
        "session 3 should exit cleanly: stdout={}\nstderr={}",
        third.stdout,
        third.stderr
    );
    assert!(
        third.stdout.contains("1") && third.stdout.contains("2"),
        "session 3: (keep)->1 and (other)->2 must resolve from regenerated user.cl: stdout={}",
        third.stdout
    );
}

// =============================================================================
// §15.4 Regeneration Integrity — `(mod child …)` submodule body MUST survive
// source regeneration (FIXME 0343, S81 close)
//
// FAILING-NOT-IGNORED repro for a DATA-CORRUPTION defect (same class as 0217).
// A backing file whose source carries a non-empty `(mod test … defns …)`
// submodule body MUST round-trip through a REPL session that triggers source
// regeneration — the submodule body MUST remain on disk (§15.4 invariant 1:
// "Loading the regenerated file … MUST produce the same … module exports as
// the interactive session"; the body lives in the extracted child file per
// §8.2.2). Today regeneration rewrites the backing `.cl`, collapsing
// `(mod test …)` to a bare `(mod test)` and DROPPING the entire submodule
// body — `generate_mod_decls` reconstructs the decl from the parent's
// `submodules` list, but the child's definitions live in the child's symbol
// table, so the parent regen alone cannot reproduce the body, and it is lost.
//
// Owning skill: /int (source regen — gate it off for dependency modules, or
// round-trip the submodule body). Flips green when the body survives.
// =============================================================================

// spec: repl/spec.md §15.4 — a `(mod test …)` submodule body MUST NOT be
//   clobbered by source regeneration. FIXME(/int 0343).
#[test]
fn mod_submodule_body_survives_source_regeneration() {
    // Pre-existing backing file carrying a non-empty `(mod test …)` body.
    let out = Cranelisp::new()
        .repl()
        .file("user.cl", "(defn f [] 1)\n(mod test\n  (defn g [] 2))\n")
        // Define a new symbol so the REPL regenerates `user.cl` on exit.
        .stdin("(defn h [] 3)\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly: stderr={}",
        out.stderr
    );

    // CORRECT: the submodule's definition is still on disk after regeneration.
    // Today this FAILS — `(mod test …)` is collapsed to a bare `(mod test)`
    // and `(defn g [] 2)` is destroyed (committed source would be corrupted).
    let regenerated = out.read_tmp("user.cl");
    assert!(
        regenerated.contains("(defn g [] 2)") || regenerated.contains("defn g"),
        "regenerated user.cl MUST preserve the `(mod test …)` submodule body \
         `(defn g [] 2)` (spec/08-modules.md §8.2.2 + repl/spec.md §15.4 \
         round-trip correctness); the body was clobbered:\n{}",
        regenerated
    );
}

// =============================================================================
// /port D1 + D2 (S101 Phase 6a exemplar assessment; no FIXME — these guards
// are the record, per the defect discipline). Resolver: /int.
//
// D1 — a macro-defining macro used at the prompt poisons the directory: the
// regenerated backing file persists BOTH the expansion artifact
// (`(defmacro x [] …)`) AND the original call form (`(mdef x 1)`); at
// restart the original form re-expands while `x` is already a macro, so the
// re-expanded `defmacro`'s name position macro-expands and the load dies
// `parse error … defmacro name must be a symbol` — exit 1 before the first
// prompt, `--no-cache` does not recover. Reduced stdlib-free (probed
// 2026-07-03): the stdlib `def` macro (the /port shape `(def x 1)`) is
// mirrored by a local module macro expanding to `(begin (defn …)
// (defmacro …))`.
//
// D2 — the REPL adopts a pre-existing hand-authored `user.cl` as the session
// backing file and REWRITES it on the first defining turn, re-rendering the
// user's source text (reader shorthand `` `(… ~e) `` becomes
// `(quasiquote (… (unquote e)))`) — the data-loss arm of /port's D2.
// PARTIAL REDUCTION: /port's second arm (hybrid batch/REPL cache meta breaks
// the NEXT session outright) did NOT reproduce in six reductions (defmacro /
// imports / stdlib prelude / platform decl / batch-first cache / hybrid
// combinations all restarted green) — exemplar-only so far; recorded in the
// ledger entry, not pinned here.
// =============================================================================

// A macro-defining macro mirroring stdlib defs.cl `def` (D1's mechanism),
// hosted in a local fixture module — stdlib-free per tests/CLAUDE.md.
const MDEF_MODULE: &str = "(import [primitives [*]])\n\
                           (defmacro mdef \"define a named value\" [name value]\n\
                           \x20 (match name\n\
                           \x20   [(macros/SexpSym s)\n\
                           \x20    (let [impl-name (macros/SexpSym (primitives/str-concat s \"-def\"))]\n\
                           \x20      `(begin\n\
                           \x20        (defn ~impl-name [] ~value)\n\
                           \x20        (defmacro ~name [] (macros/SexpList (macros/SCons ~(primitives/quote-sexp impl-name) macros/SNil)))))\n\
                           \x20    _ name]))\n";

// spec: repl/spec.md §15.1 — loading the regenerated backing file MUST
// reproduce the same session state (round-trip MUST, §15.4 invariant 1).
// RED on HEAD (/port D1): session 2 exits 1 before the first prompt with
// `defmacro name must be a symbol` — the regenerated file persists both the
// macro-expansion artifact and the original call form, which do not co-load.
#[test]
fn persist_macro_defining_macro_use_survives_restart() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("mac.cl", MDEF_MODULE)
        .stdin("(import [mac [mdef]])\n(mdef x 1)\nx\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly; stdout={} stderr={}",
        first.stdout,
        first.stderr
    );
    assert!(
        first.stdout.contains(":primitives/Int 1"),
        "session 1 sanity: `x` evaluates to 1; stdout={}",
        first.stdout
    );

    first
        .run_again()
        .repl()
        .stdin("x\n")
        .output()
        .assert_ok() // D1: exits 1 at load today, before any prompt
        .assert_stdout_does_not_contain("defmacro name must be a symbol")
        .assert_stdout_contains(":primitives/Int 1");
}

// spec: repl/spec.md §15.4 — invariant 7 (authorship fidelity: "the
// regenerated file is a faithful record of what the user typed") + invariant
// 3's preservation spirit: a defining turn that never touches a hand-authored
// definition MUST NOT destroy the user's source text for it. RED on HEAD
// (/port D2, data-loss arm): the adopted batch `user.cl`'s reader-shorthand
// macro text is re-rendered from sexps (`` ` ``/`~` become
// `quasiquote`/`unquote`), losing the authored form.
#[test]
fn persist_defining_turn_preserves_hand_authored_macro_source_text() {
    let original_macro_line = "(defmacro twice [e] `(add-i64 ~e ~e))";
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(
            ";; hand-authored batch module\n\
             (defmacro twice [e] `(add-i64 ~e ~e))\n\
             (defn square [x] (mul-i64 x x))\n\
             (defn main [] (Pure (twice (square 4))))\n",
        )
        .stdin("(defn extra [y] (add-i64 y 10))\n/quit\n")
        .output();
    let out = out.assert_ok();
    let regenerated = out.read_tmp("user.cl");
    assert!(
        regenerated.contains(original_macro_line),
        "a defining turn MUST NOT re-render an untouched hand-authored \
         definition's source text (§15.4 authorship fidelity; /port D2 \
         data-loss arm); regenerated user.cl:\n{regenerated}"
    );
    drop(out);
}

// spec: repl/spec.md §15.1 — CONTROL (GREEN on HEAD): regeneration triggers
// on successful DEFINITIONS only; an expression-only session leaves a
// hand-authored `user.cl` byte-identical. Pins the D2 boundary: adoption
// rewrites happen at defining turns, and must never widen to expression
// turns.
#[test]
fn persist_expression_only_session_leaves_hand_authored_user_cl_untouched() {
    let original = ";; hand-authored batch module\n\
                    (defmacro twice [e] `(add-i64 ~e ~e))\n\
                    (defn square [x] (mul-i64 x x))\n\
                    (defn main [] (Pure (twice (square 4))))\n";
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(original)
        .stdin("(square 3)\n/quit\n")
        .output();
    let out = out.assert_ok().assert_stdout_contains(":primitives/Int 9");
    let after = out.read_tmp("user.cl");
    assert_eq!(
        after, original,
        "an expression-only session MUST NOT rewrite the backing file (§15.1)"
    );
    drop(out);
}

// =============================================================================
// S106 — backing-file authorship fidelity (FIXMEs 0548, 0549, 0538)
//
// The regenerated backing `.cl` file MUST faithfully reflect ONLY real, intended
// module content: a FAILED structural form (import/export/mod/platform) that never
// took effect MUST NOT be persisted (0548); a transient non-defining top-level
// EXPRESSION evaluation MUST NOT be persisted (0549, repl/spec.md §15.7); and the
// §5–7 trait/type regen sections MUST render the authored declaration faithfully
// (0538). All RED-first on S106 HEAD; each flips green in its owning /dev change-set.
// =============================================================================

// spec: repl/spec.md §15.4 — a REPL import that FAILS resolution MUST NOT be
// written into the regenerated backing file when a later successful form triggers
// regeneration. RED on HEAD (FIXME 0548): the Pass-0 peel records the import onto
// `symbol_table.imports` BEFORE `handle_import` resolves, so the failed import
// survives to the next regen and corrupts the backing `.cl`.
#[test]
fn persist_failed_import_not_written_to_backing_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user("(defn seed [] 1)\n")
        // Failing import (module does not exist) → then a GOOD defn (triggers regen).
        .stdin("(import [platforms.stdio [*]])\n(defn g [x] (mul-i64 x 2))\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly (the import errors at the prompt, not fatally): stderr={}",
        out.stderr
    );
    let regenerated = out.read_tmp("user.cl");
    // Neg: the phantom failed import MUST be absent from the regenerated backing file.
    assert!(
        !regenerated.contains("platforms.stdio"),
        "a FAILED import MUST NOT be persisted to the regenerated backing file \
         (FIXME 0548, repl/spec.md §15.4); regenerated user.cl:\n{regenerated}"
    );
    // Pos: the real definitions ARE persisted.
    assert!(
        regenerated.contains("defn g") && regenerated.contains("defn seed"),
        "the real defns MUST survive regeneration; regenerated user.cl:\n{regenerated}"
    );
}

// spec: repl/spec.md §15.4 — end-to-end integrity: a session that fails an import
// then defines `main` MUST regenerate a backing project that `--run`s cleanly (no
// phantom `module ... not found`). RED on HEAD (FIXME 0548): the persisted phantom
// import breaks the subsequent `--run`.
#[test]
fn persist_bad_import_then_run_succeeds_e2e() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user("(defn seed [] 1)\n")
        .stdin("(import [platforms.stdio [*]])\n(defn main [] (Pure 6))\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly: stderr={}",
        first.stderr
    );
    // Re-run the regenerated project. A clean backing file runs main (exit 6);
    // a corrupted one fails on the phantom import.
    let ran = first.run_again().run("user").output();
    let combined = format!("{}{}", ran.stdout, ran.stderr);
    assert!(
        !combined.contains("not found") && !combined.contains("platforms.stdio"),
        "the regenerated project MUST `--run` without a phantom-import module error \
         (FIXME 0548 crosses REPL-persist → --run); stdout+stderr:\n{combined}"
    );
    assert_eq!(
        ran.status.code(),
        Some(6),
        "the regenerated project's main MUST run (exit 6); stdout={} stderr={}",
        ran.stdout,
        ran.stderr
    );
}

// spec: repl/spec.md §15.4 — the record-after-success fix MUST apply uniformly to
// every structural form, not just `import`. A FAILED `export` (of a nonexistent
// module) likewise MUST NOT be persisted. RED on HEAD (FIXME 0548): the same
// record-before-resolve ordering afflicts export/mod/platform.
#[test]
fn persist_failed_export_not_written_to_backing_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user("(defn seed [] 1)\n")
        .stdin("(export [ghostmod [*]])\n(defn g [x] (mul-i64 x 2))\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly: stderr={}",
        out.stderr
    );
    let regenerated = out.read_tmp("user.cl");
    assert!(
        !regenerated.contains("ghostmod"),
        "a FAILED export MUST NOT be persisted to the regenerated backing file — the \
         fix applies uniformly across structural forms (FIXME 0548); regenerated \
         user.cl:\n{regenerated}"
    );
    assert!(
        regenerated.contains("defn g"),
        "the real defn MUST survive regeneration; regenerated user.cl:\n{regenerated}"
    );
}

// spec: repl/spec.md §15.7 — a bare top-level EXPRESSION evaluation is transient
// session output and MUST NOT be persisted to the backing file, while the eval
// itself still happens in-session. RED on HEAD (FIXME 0549): `generate_fns_and_macros`
// has no `__expr` filter, so `(add-i64 1 2)` is re-emitted as module content.
#[test]
fn persist_bare_expr_not_written_to_backing_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user("(defn seed [] 1)\n")
        .stdin("(add-i64 1 2)\n(defn g [x] (mul-i64 x 2))\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly: stderr={}",
        out.stderr
    );
    // Pos: the in-session evaluation still happened (the ephemeral result appeared).
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "the bare expression MUST still evaluate in-session (§15.7 suppresses only its \
         SOURCE emission, not the eval); stdout:\n{}",
        out.stdout
    );
    let regenerated = out.read_tmp("user.cl");
    // Neg: the transient expression form MUST NOT be persisted as module content.
    assert!(
        !regenerated.contains("(add-i64 1 2)"),
        "a bare top-level expression MUST NOT be persisted to the backing file \
         (FIXME 0549, repl/spec.md §15.7); regenerated user.cl:\n{regenerated}"
    );
    // Pos: the real defns ARE persisted.
    assert!(
        regenerated.contains("defn g") && regenerated.contains("defn seed"),
        "the real defns MUST survive regeneration; regenerated user.cl:\n{regenerated}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.7 — after persisting a session that evaluated a bare
// expression, re-running the project MUST load cleanly with no re-materialised dead
// top-level expression (no double-eval, no error). RED on HEAD (FIXME 0549).
#[test]
fn persist_bare_expr_then_run_module_clean_e2e() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user("(defn seed [] 1)\n")
        .stdin("(add-i64 1 2)\n(defn main [] (Pure 6))\n/quit\n")
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly: stderr={}",
        first.stderr
    );
    let regenerated = first.read_tmp("user.cl");
    assert!(
        !regenerated.contains("(add-i64 1 2)"),
        "the transient expression MUST NOT be in the regenerated module (§15.7); \
         regenerated user.cl:\n{regenerated}"
    );
    // The module runs cleanly (a re-materialised bare expression at top level would
    // be dead code / a load-time surprise; here the module is clean and runs main).
    let ran = first.run_again().run("user").output();
    assert_eq!(
        ran.status.code(),
        Some(6),
        "the regenerated module MUST run cleanly (exit 6) — no re-materialised dead \
         top-level expression (§18.8); stdout={} stderr={}",
        ran.stdout,
        ran.stderr
    );
}

// spec: repl/spec.md §15.4 — §5–7 regen fidelity: a `deftrait` authored/defined at
// the REPL MUST survive backing-file regeneration faithfully. GREEN (FIXME 0538
// resolved): `save.rs::generate_traits` (§5–7) renders the trait declaration from
// a source-first verbatim slice, so the trait survives the regenerated file.
// (The byte-identical verbatim-slice round-trip is the /dev unit obligation; this
// e2e is the observable envelope: the declaration is present + faithful.)
// NOTE (S112 RT-4, below): the sibling `impl` form is NOT yet regenerated to
// `user.cl` — a distinct DEFECT pinned by `impl_regen_written_to_user_cl` /
// `impl_dispatches_after_restart_without_cache`.
#[test]
fn persist_trait_decl_regen_preserves_source() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        // b1-migration (S112): off the never-applied `(Sizeable a)` head to the
        // settled bare-head + `self` form. Assertion subject UNCHANGED: RT-3 —
        // a REPL-defined `deftrait` (non-canonical spacing) survives backing-file
        // regeneration faithfully (`deftrait`/`Sizeable`/`size` all present).
        // A trait with non-canonical spacing; then a defn triggers regen.
        .stdin("(deftrait Sizeable  (size [self]  Int))\n(defn g [x] (mul-i64 x 2))\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly: stderr={}",
        out.stderr
    );
    let regenerated = out.read_tmp("user.cl");
    assert!(
        regenerated.contains("deftrait")
            && regenerated.contains("Sizeable")
            && regenerated.contains("size"),
        "a REPL-defined `deftrait` MUST survive regeneration faithfully (§5–7 \
         source-first regen, FIXME 0538); regenerated user.cl:\n{regenerated}"
    );
}

// =============================================================================
// RT-4 — impl-source-regen data-loss (S112 W6, plan §6 / §11 ruling 12). A
// DEFECT row (not an accepted mechanism): `impl` forms are NEVER regenerated to
// `user.cl` (conventional AND HKT). `repl/spec.md` §15.4 lists `impl` EXPLICITLY
// among persisted module content ("definitions — defn, deftype, deftrait,
// **impl**, defmacro"), and round-trip invariant 1 requires loading the
// regenerated FILE to reproduce session state. The failure face: a schema bump
// (this sprint's 20→21) refuses the stale cache wholesale, the session restores
// from `user.cl` — and the impls are silently GONE while the traits and defns
// survive: inconsistent-resurrection data loss (the S109-4/0573 class). The
// cache-backed persist path is the carrier that masks it (RT-2 stays green
// because the cache holds the impl); wiping the cache exposes the loss.
// Confirmed on HEAD (2026-07-18, /testing): the regenerated `user.cl` contains
// the `deftrait`, `deftype` and `defn` but NOT the `impl`; reloading without the
// cache reports `no impl of trait user/Disp for type user/W`.
// =============================================================================

// spec: repl/spec.md §15.4 — RT-4 (i): a REPL-defined `impl` MUST be written to
// the regenerated backing file (`impl` is listed among persisted module
// content). RED at HEAD: the regen's persisted-content enumeration omits the
// impl family, so the impl is absent from `user.cl`.
// defect: class=enumeration-miss locus=src/int/save.rs (regen persisted-content enumeration omits the `impl` family — deftrait/deftype/defn survive, impl dropped) found=S112 owner=/dev
#[test]
fn impl_regen_written_to_user_cl() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(deftype W Wv)\n\
             (deftrait Disp (dp [x] Int))\n\
             (impl Disp W (defn dp [w] 42))\n\
             (defn g [x] (add-i64 x 1))\n\
             /quit\n",
        )
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly: stderr={}",
        out.stderr
    );
    let regenerated = out.read_tmp("user.cl");
    // Control: the trait, type and defn DO survive — isolating the impl as the
    // dropped family (inconsistent resurrection).
    assert!(
        regenerated.contains("deftrait")
            && regenerated.contains("deftype")
            && regenerated.contains("defn g"),
        "the trait/type/defn MUST survive regen (control for the impl loss); \
         regenerated user.cl:\n{regenerated}"
    );
    assert!(
        regenerated.contains("impl"),
        "a REPL-defined `impl` MUST be written to the regenerated `user.cl` \
         (§15.4 lists `impl` among persisted module content) — it is silently \
         DROPPED while trait/type/defn survive (enumeration-miss, ruling 12); \
         regenerated user.cl:\n{regenerated}"
    );
}

// spec: repl/spec.md §15.4 (round-trip invariant 1) — the sharper data-loss
// face: restarting from the regenerated `user.cl` WITHOUT the cache (the
// schema-bump wholesale-refusal path) MUST reproduce the session — the impl
// still dispatches. RED at HEAD: the cache masks the loss (dispatch works WITH
// the cache); once wiped, the impl is gone and `(dp Wv)` fails to dispatch.
// defect: class=enumeration-miss locus=src/int/save.rs (impl absent from user.cl → schema-bump/no-cache restore loses the impl; dispatch fails while trait/type/defn survive) found=S112 owner=/dev
#[test]
fn impl_dispatches_after_restart_without_cache() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(deftype W Wv)\n\
             (deftrait Disp (dp [x] Int))\n\
             (impl Disp W (defn dp [w] 42))\n\
             (dp Wv)\n\
             /quit\n",
        )
        .output();
    assert!(
        first.stdout.contains(":primitives/Int 42"),
        "session 1 MUST dispatch `(dp Wv)` → 42; stdout={}",
        first.stdout
    );

    // Wipe the cache so session 2 must recompile from user.cl (the schema-bump
    // wholesale-refusal path, the AG-1 pattern).
    let cache_dir = first.tmpdir.join(".cranelisp-cache");
    if cache_dir.exists() {
        std::fs::remove_dir_all(&cache_dir).expect("rm .cranelisp-cache");
    }

    let second = first
        .run_again()
        .repl()
        .with_prelude_no_overwrite(PreludeVariant::PrimitivesOnly)
        .stdin("(dp Wv)\n/quit\n")
        .output();
    let c = format!("{}{}", second.stdout, second.stderr);
    assert!(
        second.stdout.contains(":primitives/Int 42"),
        "session 2 (cache wiped) MUST reproduce the impl from the regenerated \
         `user.cl` and dispatch `(dp Wv)` → 42 — the impl MUST NOT be lost while \
         the trait/type survive (inconsistent-resurrection data loss, ruling 12); \
         got:\n{c}"
    );
    assert!(
        !c.contains("no impl of trait"),
        "session 2 MUST NOT report `no impl of trait` — the impl was silently \
         dropped from `user.cl` (enumeration-miss); got:\n{c}"
    );
}

// spec: repl/spec.md §15.4 — RT-1 (S112 W5, plan §6): the settled echo-the-head
// HK trait round-trips through the introspection printer. The applied HK deftrait
// head `(Functor f)` and the echoed impl head `(impl (Functor f) (Functor Option)
// …)` are ordinary nested s-expressions; the form-agnostic printer
// (`src/pretty.rs`, `design/frontend/trait-impl-head-parse.md` §6) re-emits them
// faithfully. `/source Functor` re-renders the deftrait with its echoed head
// verbatim — the durable proof that the printer never fell out of sync with the
// b0 grammar.
#[test]
fn hkt_new_form_source_reemits_echoed_head() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
             (impl (Functor f) (Functor Option)\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n\
             /source Functor\n/quit\n",
        )
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly: stderr={}",
        out.stderr
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("(deftrait (Functor f)"),
        "`/source Functor` MUST re-emit the HK deftrait with its echoed head \
         `(Functor f)` verbatim (form-agnostic printer, RT-1); got:\n{c}"
    );
}

// spec: repl/spec.md §15.2 — RT-2 (S112 W5, plan §6): the settled echo-the-head
// HK trait + impl persist across a session restart and the method still
// dispatches. Session 1 defines the HK trait and the echoed-head impl over the
// prelude-seeded `Option`; session 2 (same TempDir, cache present — the normal
// REPL persist path) calls `fmap` and gets 42. This is the b1
// `persist_trait_decl_regen_preserves_source` pattern extended to an HKT impl
// case (the echoed impl form survives the persist/reload round-trip and
// dispatches).
//
// NOTE (routed to /qa, plan §6): impl forms — conventional AND higher-kinded
// alike — are persisted via the compilation cache, NOT source-regenerated into
// `user.cl` (verified: a conventional `(impl …)` is likewise dropped from the
// regenerated file). Source-content regeneration of impls is a pre-existing gap
// (the FIXME-0538 §5–7 family covers deftrait/deftype decls, not impls), NOT a
// b2 concern — so this RT row exercises the cache-backed persist path, the
// mechanism that actually carries impls across a restart.
#[test]
fn hkt_impl_new_form_persists_and_reloads() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
             (impl (Functor f) (Functor Option)\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n\
             (defn trigger [] 1)\n/quit\n",
        )
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly: stderr={}",
        first.stderr
    );

    let second = first
        .run_again()
        .repl()
        .with_prelude_no_overwrite(PreludeVariant::PrimitivesOnly)
        .stdin("(match (fmap (fn [x] (add-i64 x 1)) (Some 41)) [(Some v) v None 0])\n/quit\n")
        .output();
    assert!(
        second.stdout.contains(":primitives/Int 42"),
        "session 2: the persisted echoed-head HK impl MUST reload and `fmap` MUST \
         dispatch over Option → 42 (RT-2); stdout:\n{}\nstderr:\n{}",
        second.stdout,
        second.stderr
    );
}

// spec: repl/spec.md §15.4 — §5–7 regen fidelity: a `deftype` authored/defined at
// the REPL MUST survive backing-file regeneration faithfully. Green regression
// guard for the FIXME-0538 fix (`save.rs::generate_types`, §5–7, no longer drops
// the type declaration). Seed uses the canonical single-bracket product ctor
// `(MkPt [:Int x :Int y])` per spec §5.2 (the two-bracket spelling was an invalid
// fixture silently accepted pre-S114-W-D1; corrected FIXME 0701).
#[test]
fn persist_type_decl_regen_preserves_source() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(deftype Pt (MkPt [:Int x :Int y]))\n(defn g [x] (mul-i64 x 2))\n/quit\n")
        .output();
    assert!(
        out.status.success(),
        "session should exit cleanly: stderr={}",
        out.stderr
    );
    let regenerated = out.read_tmp("user.cl");
    assert!(
        regenerated.contains("deftype")
            && regenerated.contains("Pt")
            && regenerated.contains("MkPt"),
        "a REPL-defined `deftype` MUST survive regeneration faithfully (§5–7 \
         source-first regen, FIXME 0538); regenerated user.cl:\n{regenerated}"
    );
}

// =============================================================================
// PS-RT4 trait-PROVENANCE axis (W5b, was FIXME 0664 — recipe in the plan row).
// The original RT-4 pins sat in the LOCAL-trait cell only; the W4 fix passed them
// while the IMPORTED-trait cell (and the prelude-trait cell) still dropped the
// impl from the regenerated `user.cl` (the D45 model splits on this axis — the
// shell lives at the TRAIT's home, so a variant grew its own missing codepath).
// 0664's fix landed + verified; these are its born-green regression guards.
// =============================================================================

// IMPORTED-trait cell (0664's regression guard): trait `Bump` in a FILE module
// `tlib`, impl for a user type `W` at the user module — the impl must be written to
// the regenerated `user.cl` and dispatch after restart.
// spec: repl/spec.md §15.2 — an imported-trait impl persists across restart.
#[test]
fn imported_trait_impl_survives_restart() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "tlib.cl",
            "(import [primitives [Int]])\n(deftrait Bump (bump [self] Int))\n",
        )
        .stdin(
            "(import [tlib [Bump bump]])\n\
             (deftype W Wv)\n\
             (impl Bump W (defn bump [w] 42))\n\
             (bump Wv)\n\
             /quit\n",
        )
        .output();
    assert!(
        first.stdout.contains(":primitives/Int 42"),
        "session 1 MUST dispatch `(bump Wv)` → 42; stdout={}",
        first.stdout
    );

    let second = first
        .run_again()
        .repl()
        .with_prelude_no_overwrite(PreludeVariant::PrimitivesOnly)
        .stdin("(bump Wv)\n/quit\n")
        .output();
    let c = format!("{}{}", second.stdout, second.stderr);
    assert!(
        second.stdout.contains(":primitives/Int 42"),
        "session 2 MUST restore the IMPORTED-trait impl from the regenerated \
         `user.cl` and dispatch `(bump Wv)` → 42 (0664 — the impl for an imported \
         trait must not be dropped); got:\n{c}"
    );
    assert!(
        !c.contains("no impl of trait"),
        "session 2 MUST NOT report `no impl of trait` — the imported-trait impl was \
         dropped from `user.cl`; got:\n{c}"
    );
}

// PRELUDE-trait cell (highest-value real-usage variant): `impl Display MyType`
// where `Display` comes from the prelude. The impl must survive regen.
// spec: repl/spec.md §15.2 — a prelude-trait impl persists across restart.
#[test]
fn prelude_trait_impl_survives_restart() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(
            "(deftype MyType Mv)\n\
             (impl Display MyType (defn show [x] \"hi\"))\n\
             (show Mv)\n\
             /quit\n",
        )
        .output();
    assert!(
        first.stdout.contains("hi"),
        "session 1 MUST `(show Mv)` → \"hi\"; stdout={}",
        first.stdout
    );

    let second = first
        .run_again()
        .repl()
        .with_prelude_no_overwrite(PreludeVariant::TestStandard)
        .stdin("(show Mv)\n/quit\n")
        .output();
    let c = format!("{}{}", second.stdout, second.stderr);
    assert!(
        second.stdout.contains("hi"),
        "session 2 MUST restore the PRELUDE-trait impl and `(show Mv)` → \"hi\" \
         (0664); got:\n{c}"
    );
    assert!(
        !c.contains("no impl of trait"),
        "session 2 MUST NOT report `no impl of trait`; got:\n{c}"
    );
}

// =============================================================================
// Startup load failure: prompt, error block, repair and failed-source retention
// (repl/spec/15-session-persistence.md §15.2.3, with the §15.1 and
// repl/spec/18-redefinition.md §18.8 retention exceptions)
// =============================================================================

const STARTUP_GOOD: &str = "(defn good [:Int x] (add-i64 x 10))";
const STARTUP_BROKEN: &str = "(defn broken [] (undefined-name 1))";

fn seeded_broken_session() -> Cranelisp {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(&format!("{STARTUP_GOOD}\n{STARTUP_BROKEN}\n"))
}

/// Piped-REPL stdout split at each prompt: index 0 is startup output,
/// index N is the response to the Nth input turn.
fn turns(stdout: &str) -> Vec<&str> {
    stdout.split("user>").collect()
}

// spec: repl/spec/15-session-persistence.md §15.2.3 — a backing file that fails
// to compile at startup is reported and the REPL still reaches a prompt; while
// blocked an ordinary expression is refused; a definition repairing the broken
// name is accepted and clears the block.
#[test]
fn persist_startup_load_failure_reaches_prompt_blocks_then_repairs() {
    let out = seeded_broken_session()
        .stdin("(good 1)\n(defn broken [] 2)\n(broken)\n(good 1)\n")
        .output()
        .assert_ok();
    let all = format!("{}{}", out.stdout, out.stderr);
    // Implementation-specific report text (lifecycle.rs render_startup_error_report);
    // §15.2.3 requires a report, not this wording. A format change updates this line.
    assert!(
        all.contains("[errors: user.cl]"),
        "startup MUST report the load error; got:\n{all}"
    );
    let t = turns(&out.stdout);
    assert!(
        t.len() >= 5,
        "expected a prompt before each of 4 turns; stdout:\n{}",
        out.stdout
    );
    // "has errors" is the implementation's refusal line, not spec-pinned wording.
    assert!(
        t[1].contains("has errors") && !t[1].contains(":primitives/Int"),
        "turn 1 `(good 1)` MUST be refused while blocked; stdout:\n{}",
        out.stdout
    );
    for (n, needle) in [(3, ":primitives/Int 2"), (4, ":primitives/Int 11")] {
        assert!(
            t[n].contains(needle),
            "turn {n} after the repair MUST yield {needle}; stdout:\n{}",
            out.stdout
        );
    }
    for n in 2..=4 {
        assert!(
            !t[n].contains("has errors"),
            "turn {n}: the block MUST clear once the definition repairs it; stdout:\n{}",
            out.stdout
        );
    }
}

// spec: repl/spec/15-session-persistence.md §15.2.3 — startup-failed source is
// retained verbatim through a regeneration triggered by a different name, and
// released once a successful same-name definition replaces it (§15.1, §18.8).
#[test]
fn persist_startup_failed_source_retained_until_same_name_repair_neg() {
    let first = seeded_broken_session()
        .stdin("(defn other [] 3)\n")
        .output()
        .assert_ok();
    let saved = first.read_tmp("user.cl");
    assert!(
        saved.contains("defn other") && saved.contains("defn good"),
        "the different-name definition MUST regenerate the file; user.cl:\n{saved}"
    );
    assert_eq!(
        saved.matches(STARTUP_BROKEN).count(),
        1,
        "a different-name definition MUST NOT drop (or duplicate) the failed \
         source; user.cl:\n{saved}"
    );

    let second = first
        .run_again()
        .repl()
        .stdin("(defn broken [] 2)\n")
        .output()
        .assert_ok();
    let repaired = second.read_tmp("user.cl");
    assert!(
        !repaired.contains("undefined-name") && repaired.matches("defn broken").count() == 1,
        "the same-name repair MUST replace the failed source exactly once; \
         user.cl:\n{repaired}"
    );

    let third = second
        .run_again()
        .repl()
        .stdin("(broken)\n")
        .output()
        .assert_ok();
    let all = format!("{}{}", third.stdout, third.stderr);
    assert!(
        third.stdout.contains(":primitives/Int 2") && !all.contains("[errors:"),
        "the repaired file MUST restore cleanly; got:\n{all}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.2.3 — every later regeneration
// keeps startup-failed source until a successful definition replaces it;
// `/reset` is not such a definition. Was RED when authored (S122): the
// `ReplCommand::Reset` arm cleared `failed_forms`, so regeneration after
// `/reset` omitted the failed source. Reset-free control: session 1 of
// persist_startup_failed_source_retained_until_same_name_repair_neg.
// defect: class=release-path-bypass locus=src/repl/mod.rs::dispatch_command (the `ReplCommand::Reset` arm) found=S122 owner=/dev fixed=S122/9d4f18f5
#[test]
fn persist_startup_failed_source_survives_reset_then_other_definition() {
    let out = seeded_broken_session()
        .stdin("/reset\n(defn other [] 3)\n")
        .output()
        .assert_ok();
    // Implementation-specific `/reset` reply (src/repl/mod.rs); it proves turn 1
    // reached the reset handler, not spec-pinned wording. A reply change updates this line.
    assert!(
        turns(&out.stdout)
            .get(1)
            .is_some_and(|t| t.contains("command not yet available")),
        "turn 1 `/reset` MUST reach the reset handler; stdout:\n{}",
        out.stdout
    );
    let saved = out.read_tmp("user.cl");
    assert!(
        saved.contains("defn other"),
        "the definition after /reset MUST regenerate the file; user.cl:\n{saved}"
    );
    assert_eq!(
        saved.matches(STARTUP_BROKEN).count(),
        1,
        "regeneration after /reset MUST retain the unrepaired failed source; \
         user.cl:\n{saved}"
    );
}

// =============================================================================
// §18.8 — a successful replacement is what the backing file persists
// =============================================================================

/// Define `k` returning 1, replace it with a same-typed `k` returning 100, and
/// call it from a new caller; then restart the REPL and run a no-cache batch
/// program over the saved module. `define` renders one `k` whose body yields
/// the given literal. Every leg observes 100 when the replacement persisted and
/// 1 when the backing file kept the first generation.
fn assert_replacement_persists_through_restart(define: fn(i64) -> String) {
    let first = Cranelisp::new()
        .repl()
        .stdin(&format!(
            "(import [primitives [*]])\n{}\n{}\n(defn new-caller [] (k))\n(new-caller)\n/quit\n",
            define(1),
            define(100)
        ))
        .output()
        .assert_ok();
    assert!(
        first.stdout.contains(":primitives/Int 100") && !first.stdout.contains("Error"),
        "precondition: the live replacement MUST be admitted and used by the new \
         caller; stdout:\n{}",
        first.stdout
    );
    let saved = first.read_tmp("user.cl");
    let k_lines: Vec<&str> = saved
        .lines()
        .filter(|l| l.starts_with("(defmacro k ") || l.starts_with("(defn k "))
        .collect();
    assert!(
        k_lines.len() == 1 && k_lines[0].contains("100"),
        "the backing file MUST hold exactly the latest successful `k` (§18.8, \
         §15.6); user.cl:\n{saved}"
    );

    let restarted = first
        .run_again()
        .repl()
        .stdin("(k)\n(new-caller)\n/quit\n")
        .output()
        .assert_ok();
    assert_eq!(
        restarted.stdout.matches(":primitives/Int 100").count(),
        2,
        "restart MUST compile the saved latest `k`; stdout:\n{}",
        restarted.stdout
    );

    restarted
        .run_again()
        .file(
            "main.cl",
            "(import [primitives [*]])\n(import [user [k]])\n\
             (defn main [] (Pure (add-i64 7 (k))))\n",
        )
        .run("main.cl")
        .cli_flag("--no-cache")
        .output()
        .assert_exit(107);
}

// spec: repl/spec/18-redefinition.md §18.8 — the backing file holds the latest
// successful source of a replaced macro, so restart expands future invocations
// with it (§18.4). RED when authored (S122, ACT-0970): the file keeps the first
// body `(quasiquote 1)`; restart yields 1 and the batch program exits 8, not
// 107. Control: persist_function_replacement_persists_through_restart.
// defect: class=partial-record-update locus=src/process_form/form_dispatch.rs::record_macro_introspection found=S122 owner=/dev fixed=S122/63605970
// The macro writer set the introspection `sexp` only when absent, so after the
// replacement `/source k` showed the new text while `/sexp k`, which save
// emits, still showed the first body. The writer now replaces the record.
#[test]
fn persist_macro_replacement_persists_through_restart() {
    assert_replacement_persists_through_restart(|n| format!("(defmacro k [] `{n})"));
}

// spec: repl/spec/18-redefinition.md §18.8 — control for the macro cell: the
// same session with a same-typed function replacement.
#[test]
fn persist_function_replacement_persists_through_restart() {
    assert_replacement_persists_through_restart(|n| format!("(defn k [] {n})"));
}

// =============================================================================
// §15.4 — cache-restored and file-loaded declarations survive regeneration
// =============================================================================

const DECLS: [&str; 3] = [
    "(deftype Box [:primitives/Int v])",
    "(deftrait Weigh (weigh [x] primitives/Int))",
    "(impl Weigh Box (defn weigh [x] (add-i64 (Box.v x) 1)))",
];

// spec: repl/spec/15-session-persistence.md §15.4 — round-trip correctness: a
// regeneration after a warm-cache restart MUST keep the type, trait and impl
// restored from cache, so a cold restart still has them. RED when authored
// (S122, ACT-0980): session 2's regeneration writes only the import and the new
// function, and the cold restart reports `undefined variable: weigh`. Control
// differing only in declaration kind:
// persist_bug0220_cache_restored_userfns_survive_repl_edit_regen.
// defect: class=enumeration-miss locus=src/save.rs::rehydrate_userfn_introspection_from_source found=S122 owner=/dev fixed=S122/63605970
// Save renders these kinds only from introspection, which cache restore left
// empty and the rehydrator refilled only for plain callables. That seam is
// gone; read `src/save.rs::rehydrate_introspection_from_source`, which covers
// every kind, and `generate_module_source`, which now refuses rather than
// drops an unrendered entry.
#[test]
fn persist_cache_restored_declarations_survive_repl_edit_regen() {
    let first = Cranelisp::new()
        .repl()
        .stdin(&format!(
            "(import [primitives [*]])\n{}\n(weigh (Box 41))\n/quit\n",
            DECLS.join("\n")
        ))
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 42");
    let saved = first.read_tmp("user.cl");
    assert!(
        DECLS.iter().all(|d| saved.contains(d)),
        "precondition: session 1 MUST persist every declaration; user.cl:\n{saved}"
    );
    assert!(
        first.tmp_exists(".cranelisp-cache"),
        "precondition: session 1 MUST populate the cache"
    );

    let second = first
        .run_again()
        .repl()
        .stdin("(defn added [] 3)\n(added)\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 3");
    let regenerated = second.read_tmp("user.cl");
    let missing: Vec<&str> = DECLS
        .iter()
        .copied()
        .filter(|d| !regenerated.contains(d))
        .collect();
    assert!(
        missing.is_empty() && regenerated.contains("(defn added [] 3)"),
        "regeneration after a warm restart MUST keep the cache-restored \
         declarations; missing {missing:?}; user.cl:\n{regenerated}"
    );

    // A cold restart makes the backing file the only authority.
    std::fs::remove_dir_all(second.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    second
        .run_again()
        .repl()
        .stdin("(weigh (Box 41))\n(Box.v (Box 5))\n(added)\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_does_not_contain("Error")
        .assert_stdout_contains_all(&[
            ":primitives/Int 42",
            ":primitives/Int 5",
            ":primitives/Int 3",
        ]);
}

// spec: repl/spec/15-session-persistence.md §15.4 — round-trip correctness: a
// regeneration after an uncached load of the backing file MUST keep the type,
// trait and impl declarations that file authored, so a cold restart still has
// them. Control differing only in declaration kind: `keep`, a function loaded
// from the same file. RED before the fix (S122, PC-1): the regenerated file
// held `keep` and `added` but none of the three declarations.
// defect: class=enumeration-miss locus=src/save.rs::rehydrate_userfn_introspection_from_source found=S122 owner=/dev fixed=S122/63605970
// A fresh load wrote no declaration record, and the rehydrator refilled only
// plain callables. That seam is gone; read
// `src/save.rs::rehydrate_introspection_from_source`, which covers every kind.
#[test]
fn persist_file_loaded_declarations_survive_repl_edit_regen() {
    const KEEP: &str = "(defn keep [] 7)";
    const ADDED: &str = "(defn added [] 3)";
    // A fresh TempDir holds no cache, so session 1 loads user.cl from source.
    let first = Cranelisp::new()
        .user(&format!(
            "(import [primitives [*]])\n{}\n{KEEP}\n",
            DECLS.join("\n")
        ))
        .repl()
        .stdin(&format!("(weigh (Box 41))\n{ADDED}\n/quit\n"))
        .output()
        .assert_ok();
    assert!(
        first.stdout.contains(":primitives/Int 42") && !first.stdout.contains("Error"),
        "precondition: the uncached load MUST make the declarations usable; \
         stdout:\n{}\nstderr:\n{}",
        first.stdout,
        first.stderr
    );

    let regenerated = first.read_tmp("user.cl");
    let count = |form: &str| regenerated.matches(form).count();
    assert_eq!(
        count(ADDED),
        1,
        "defining `added` MUST regenerate the backing file; user.cl:\n{regenerated}"
    );
    assert_eq!(
        count(KEEP),
        1,
        "control: the file-loaded function MUST survive regeneration; user.cl:\n{regenerated}"
    );
    let counts: Vec<(&str, usize)> = DECLS.iter().map(|d| (*d, count(d))).collect();
    assert!(
        counts.iter().all(|&(_, n)| n == 1),
        "regeneration after an uncached load MUST keep each file-loaded \
         declaration exactly once; counts {counts:?}; user.cl:\n{regenerated}"
    );

    // A cold restart makes the backing file the only authority.
    std::fs::remove_dir_all(first.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    let restarted = first
        .run_again()
        .repl()
        .stdin("(weigh (Box 41))\n(Box.v (Box 5))\n(keep)\n(added)\n/quit\n")
        .output()
        .assert_ok();
    assert!(
        !restarted.stdout.contains("Error") && !restarted.stderr.contains("Error"),
        "cold restart MUST load the regenerated file cleanly; stdout:\n{}\nstderr:\n{}",
        restarted.stdout,
        restarted.stderr
    );
    let t = turns(&restarted.stdout);
    let expected = [
        ":primitives/Int 42",
        ":primitives/Int 5",
        ":primitives/Int 7",
        ":primitives/Int 3",
    ];
    for (i, value) in expected.iter().enumerate() {
        assert!(
            t.get(i + 1).is_some_and(|turn| turn.contains(value)),
            "cold restart turn {} MUST yield {value}; stdout:\n{}",
            i + 1,
            restarted.stdout
        );
    }
}

// =============================================================================
// §15.4 — a `begin` spanning declaration sections is written once
// =============================================================================

const SHOW_TRAIT: &str = "(deftrait Show (show [self] primitives/Int))";
/// One authored form whose members land in two regeneration sections: the
/// type section and the impl section.
const SPANNING_BEGIN: &str = "(begin (deftype Token MkToken) (impl Show Token (defn show [_] 41)))";
const G: &str = "(defn g [] 1)";

/// After `session` defined `g`, the backing file MUST hold the spanning
/// `begin` exactly once, and a cold restart from that file alone MUST still
/// dispatch `show` and call `g`. The restart discriminates a fix that drops
/// the form instead of writing it once; a duplicate reloads cleanly, so the
/// count, not the round trip, discriminates duplication.
fn assert_spanning_begin_written_once(session: e2e::CrOutput) {
    let saved = session.read_tmp("user.cl");
    let count = |form: &str| saved.matches(form).count();
    assert_eq!(
        count(G),
        1,
        "control: defining `g` MUST regenerate the backing file; user.cl:\n{saved}"
    );
    assert_eq!(
        count(SHOW_TRAIT),
        1,
        "control: the single-section trait MUST be written once; user.cl:\n{saved}"
    );
    assert_eq!(
        (count("(begin"), count(SPANNING_BEGIN)),
        (1, 1),
        "a `begin` spanning the type and impl sections MUST be written once \
         (design/int/session-persistence.md §1.4); user.cl:\n{saved}"
    );

    std::fs::remove_dir_all(session.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    let restarted = session
        .run_again()
        .repl()
        .stdin("(show MkToken)\n(g)\n/quit\n")
        .output()
        .assert_ok();
    assert!(
        !restarted.stdout.contains("Error") && !restarted.stderr.contains("Error"),
        "cold restart MUST load the regenerated file cleanly; stdout:\n{}\nstderr:\n{}",
        restarted.stdout,
        restarted.stderr
    );
    let t = turns(&restarted.stdout);
    for (i, value) in [":primitives/Int 41", ":primitives/Int 1"]
        .iter()
        .enumerate()
    {
        assert!(
            t.get(i + 1).is_some_and(|turn| turn.contains(value)),
            "cold restart turn {} MUST yield {value}; stdout:\n{}",
            i + 1,
            restarted.stdout
        );
    }
}

// spec: repl/spec/15-session-persistence.md §15.4 — rule 7 authorship fidelity
// and rule 1 round trip: a REPL-entered `begin` whose members span the type and
// impl sections is regenerated as the one form the user typed. PC-8, REPL leg.
// RED before the S122 F2 fix: the file held the `begin` twice; the cold
// restart still gave 41 and 1.
// defect: class=enumeration-miss locus=src/save.rs::generate_module_source found=S122 owner=/dev fixed=S122/63605970
// The shared-authored-form dedup (design §1.4) was scoped to
// `generate_fns_and_macros`, so the type and impl sections each rendered the
// shared `begin`.
#[test]
fn persist_repl_begin_spanning_sections_written_once() {
    let first = Cranelisp::new()
        .repl()
        .stdin(&format!("{SHOW_TRAIT}\n{SPANNING_BEGIN}\n{G}\n/quit\n"))
        .output()
        .assert_ok();
    assert!(
        first.stdout.contains("impl user/Show for user/Token") && !first.stdout.contains("Error"),
        "precondition: the spanning `begin` MUST be admitted; stdout:\n{}",
        first.stdout
    );
    assert_spanning_begin_written_once(first);
}

// spec: repl/spec/15-session-persistence.md §15.4 — rule 6 over rules 7 and 1:
// the same spanning `begin`, loaded uncached from the backing file rather than
// entered at the REPL, is regenerated once. PC-8, seeded-file leg. RED before
// the S122 F2 fix: the file held the `begin` twice; the cold restart still gave
// 41 and 1.
// defect: class=enumeration-miss locus=src/save.rs::generate_module_source found=S122 owner=/dev fixed=S122/63605970
// As for the REPL leg; `rehydrate_introspection_from_source` records the outer
// `begin` under each member, which is the shape §1.4 dedups.
#[test]
fn persist_file_loaded_begin_spanning_sections_written_once() {
    // A fresh TempDir holds no cache, so the session loads user.cl from source.
    let first = Cranelisp::new()
        .user(&format!("{SHOW_TRAIT}\n\n{SPANNING_BEGIN}\n"))
        .repl()
        .stdin(&format!("(show MkToken)\n{G}\n/quit\n"))
        .output()
        .assert_ok();
    assert!(
        turns(&first.stdout)
            .get(1)
            .is_some_and(|t| t.contains(":primitives/Int 41"))
            && !first.stdout.contains("Error"),
        "precondition: the uncached load MUST make `show` dispatch; stdout:\n{}\nstderr:\n{}",
        first.stdout,
        first.stderr
    );
    assert_spanning_begin_written_once(first);
}

// =============================================================================
// §15.3, §14.2, §14.8 — an external edit to the backing file is reloaded
// unless it changes a live type's structure
// =============================================================================

const T_ONE_FIELD: &str = "(deftype T [:primitives/Int v])";
const T_TWO_FIELDS: &str = "(deftype T [:primitives/Int v :primitives/Int w])";
const T_STRING_FIELD: &str = "(deftype T [:primitives/String v])";

/// REPL input that lets the watcher settle, overwrites `file` with the
/// one-line `source`, and waits for the reload: three turns.
fn save(file: &str, source: &str) -> String {
    format!("/sh sleep 0.3\n/sh echo '{source}' > {file}\n/sh sleep 0.5\n")
}

/// The output of a `save` whose first turn is `first`: its echo and settle
/// turns. The reload notification is printed before whichever prompt follows
/// the watcher's detection of the write, so it lands in one of the two.
fn save_notice(turns: &[&str], first: usize) -> String {
    turns.iter().skip(first + 1).take(2).copied().collect()
}

/// Each `[errors: <file>]` notification in `out`, with the lines after it up
/// to the next prompt.
fn error_blocks<'a>(out: &'a e2e::CrOutput, file: &str) -> Vec<&'a str> {
    let marker = format!("[errors: {file}]");
    [out.stdout.as_str(), out.stderr.as_str()]
        .into_iter()
        .flat_map(|stream| {
            stream.match_indices(&marker).map(move |(i, _)| {
                let rest = &stream[i..];
                rest.find("user>").map_or(rest, |end| &rest[..end])
            })
        })
        .collect()
}

/// Whether an error block states §14.8's diagnostic: it names the type `ty`
/// as a whole symbol and says a restart is required. `restart` is matched
/// case-insensitively; the name case-sensitively, since a one-letter name
/// also occurs inside ordinary words.
fn requires_restart_for(block: &str, ty: &str) -> bool {
    let symbol_char = |c: char| c.is_alphanumeric() || "-_?!*".contains(c);
    let names_ty = block.match_indices(ty).any(|(i, _)| {
        !block[..i].chars().next_back().is_some_and(symbol_char)
            && !block[i + ty.len()..]
                .chars()
                .next()
                .is_some_and(symbol_char)
    });
    names_ty && block.to_lowercase().contains("restart")
}

/// The violated observations of a multi-leg cell, so that one run reports
/// every failing leg rather than only the first.
#[derive(Default)]
struct Legs(Vec<&'static str>);

impl Legs {
    fn check(&mut self, holds: bool, leg: &'static str) {
        if !holds {
            self.0.push(leg);
        }
    }

    fn assert_all(self, transcript: &str) {
        assert!(
            self.0.is_empty(),
            "violated:\n- {}\n{transcript}",
            self.0.join("\n- ")
        );
    }
}

fn transcript(out: &e2e::CrOutput) -> String {
    format!(
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    )
}

/// Load `seed` from `user.cl`, overwrite the file externally with the one-line
/// `edited` source, then evaluate `probe`. The reload MUST succeed and `probe`
/// MUST yield `value` from the edited source.
fn assert_external_edit_reloads(seed: &str, edited: &str, probe: &str, value: &str) {
    let out = Cranelisp::new()
        .user(&format!("{seed}\n"))
        .repl()
        .stdin(&format!(
            "/sh sleep 0.3\n/sh echo '{edited}' > user.cl\n/sh sleep 0.5\n{probe}\n/quit\n"
        ))
        .output();
    let all = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("[updated: user.cl]") && !all.contains("[errors:"),
        "the edited backing file MUST reload without error (§14.2 steps 2–3); got:\n{all}"
    );
    assert!(
        turns(&out.stdout).iter().any(|t| t.contains(value)),
        "`{probe}` MUST yield {value} from the edited source; got:\n{all}"
    );
}

// spec: repl/spec/14-file-watching.md §14.8 — a reload that changes a live
// product field's type, keeping the field count, fails: `[errors: user.cl]`
// names `T` and says a restart is required, not that persisted source be
// reloaded, and the edited layout is not established. RB-1. RED when authored
// (S122): the reload is accepted and the probe yields "s".
#[test]
fn persist_external_edit_changing_field_type_fails_requiring_restart() {
    let out = Cranelisp::new()
        .user(&format!("{T_ONE_FIELD}\n"))
        .repl()
        .stdin(&format!(
            "{}(T.v (T \"s\"))\n/quit\n",
            save("user.cl", T_STRING_FIELD)
        ))
        .output();
    let blocks = error_blocks(&out, "user.cl");
    let mut legs = Legs::default();
    legs.check(
        !out.stdout.contains("[updated: user.cl]"),
        "the reload fails: no `[updated: user.cl]`",
    );
    legs.check(
        blocks.iter().any(|b| requires_restart_for(b, "T")),
        "`[errors: user.cl]` names `T` and says a restart is required",
    );
    legs.check(
        !blocks.iter().any(|b| b.contains("reload persisted source")),
        "the refusal does not offer the reload remedy",
    );
    legs.check(
        !out.stdout.contains(":primitives/String \"s\""),
        "`(T.v (T \"s\"))` does not yield the edited layout's \"s\"",
    );
    legs.assert_all(&transcript(&out));
}

// spec: repl/spec/14-file-watching.md §14.8, §14.5 item 5 — the failure and
// its lock stand until a later save reloads successfully (§14.4 item 4): a
// save structurally identical to the live `T` reloads, evaluation resumes, and
// a definition turn is accepted and regenerates the file from the saved
// content. RB-4. RED when authored
// (S122) at its precondition, the RB-1 failure.
#[test]
fn persist_compatible_save_after_structural_reload_failure_releases_the_file() {
    let edited = format!("{T_STRING_FIELD} (defn g [] 1)");
    let restored = format!("{T_ONE_FIELD} (defn g [] 5)");
    // Turns: 1–3 save, 4 (g), 5–7 save, 8 (g), 9 (T.v (T 7)), 10 (defn h [] 2).
    let out = Cranelisp::new()
        .user(&format!("{T_ONE_FIELD} (defn g [] 1)\n"))
        .repl()
        .stdin(&format!(
            "{}(g)\n{}(g)\n(T.v (T 7))\n(defn h [] 2)\n/quit\n",
            save("user.cl", &edited),
            save("user.cl", &restored)
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let failed_at = out.stdout.find("[errors: user.cl]");
    let updated_at = out.stdout.rfind("[updated: user.cl]");
    let mut legs = Legs::default();
    legs.check(
        error_blocks(&out, "user.cl")
            .iter()
            .any(|b| requires_restart_for(b, "T")),
        "precondition: the field-type save fails under §14.8",
    );
    legs.check(
        turn(4).contains("Cannot evaluate"),
        "precondition: evaluation is blocked by the failure",
    );
    legs.check(
        failed_at.zip(updated_at).is_some_and(|(f, u)| f < u),
        "the compatible save reloads after the failure: `[updated: user.cl]`",
    );
    legs.check(
        turn(8).contains(":primitives/Int 5"),
        "evaluation resumes with the saved `g`",
    );
    legs.check(
        turn(9).contains(":primitives/Int 7"),
        "the live `T` reads its field",
    );
    legs.check(
        turn(10).contains("user/h"),
        "the definition turn is accepted",
    );
    let saved = out.read_tmp("user.cl");
    legs.check(
        saved.matches(T_ONE_FIELD).count() == 1
            && saved.matches("(defn g [] 5)").count() == 1
            && saved.matches("(defn h [] 2)").count() == 1
            && !saved.contains(T_STRING_FIELD)
            && !saved.contains("(defn g [] 1)"),
        "the definition regenerates user.cl from the saved content",
    );
    legs.assert_all(&transcript(&out));
}

// spec: repl/spec/15-session-persistence.md §15.3 — control named by ACT-0998:
// the same file with only a function body changed.
#[test]
fn persist_external_edit_changing_defn_body_reloads_control() {
    assert_external_edit_reloads(
        &format!("{T_ONE_FIELD} (defn g [] 1)"),
        &format!("{T_ONE_FIELD} (defn g [] 5)"),
        "(g)",
        ":primitives/Int 5",
    );
}

// =============================================================================
// §15.6, §18.8 — a rejected redefinition is never written
// =============================================================================

/// Define `f` and its caller `k`, have `rejected` refused, then define `other`
/// so the backing file regenerates. The file MUST keep the prior `f`, and a
/// cold restart from it MUST run `k` against that `f`.
fn assert_rejected_redefinition_not_written(rejected: &str) {
    const F: &str = "(defn f [:Int x] (add-i64 x 1))";
    let first = Cranelisp::new()
        .repl()
        .stdin(&format!(
            "(import [primitives [*]])\n{F}\n(defn k [:Int y] (f y))\n{rejected}\n\
             (defn other [] 3)\n/quit\n"
        ))
        .output()
        .assert_ok();
    let t = turns(&first.stdout);
    assert!(
        t.get(4).is_some_and(|t| t.contains("Error"))
            && t.get(5).is_some_and(|t| t.contains("user/other")),
        "precondition: turn 4 MUST be rejected and turn 5 accepted; stdout:\n{}",
        first.stdout
    );
    let saved = first.read_tmp("user.cl");
    assert!(
        saved.matches(F).count() == 1 && !saved.contains(rejected),
        "regeneration after a rejected redefinition MUST write the prior `f`, \
         not the rejected form; user.cl:\n{saved}"
    );

    std::fs::remove_dir_all(first.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    let cold = first
        .run_again()
        .repl()
        .stdin("(k 3)\n(other)\n/quit\n")
        .output()
        .assert_ok();
    assert!(
        !cold.stdout.contains("[errors:")
            && cold.stdout.contains(":primitives/Int 4")
            && cold.stdout.contains(":primitives/Int 3"),
        "cold restart MUST resume the session's coherent state; stdout:\n{}",
        cold.stdout
    );
}

// spec: repl/spec/18-redefinition.md §18.8 — a rejected redefinition is never
// written; repl/spec/15-session-persistence.md §15.6. The redefinition fails
// typecheck. RED when authored (S122, SL-3): the regeneration triggered by
// `other` writes the rejected `f`, and the cold restart is blocked by its
// error. Controls: rejected_change_does_not_write_an_incoherent_backing_file
// (no later regeneration) and persist_function_replacement_persists_through_restart
// (an accepted replacement).
// defect: class=partial-record-update locus=src/process_form.rs::process_regular_form_with_origin found=S122 owner=/dev — the pass-2 record writer runs before typecheck and the commit gate, and a rejection does not restore the record
#[test]
fn persist_typecheck_rejected_redefinition_not_written_by_later_regeneration() {
    assert_rejected_redefinition_not_written("(defn f [:Int x] (nope x))");
}

// spec: repl/spec/18-redefinition.md §18.8 — as the typecheck cell, with the
// redefinition refused at the commit gate because it changes `f`'s type under
// the dependent `k`. RED when authored (S122, SL-3), as that cell.
// defect: class=partial-record-update locus=src/process_form.rs::process_regular_form_with_origin found=S122 owner=/dev — the pass-2 record writer runs before typecheck and the commit gate, and a rejection does not restore the record
#[test]
fn persist_commit_gate_rejected_redefinition_not_written_by_later_regeneration() {
    assert_rejected_redefinition_not_written("(defn f [:String s] (str-len s))");
}

// =============================================================================
// §15.4 rule 6 — a `/mod` turn persists to a module restored from cache
// =============================================================================

/// `lib` defines `x-def` and the macro `x` through a top-level macro call.
const MACRO_LIB: &str = "(defmacro mk [] `(begin (defn x-def [] 1) (defmacro x [] `(x-def))))\n\
                         (mk)\n(defn base [] 5)\n";
const IMPORT_LIB: &str = "(import [lib [base]])\n(base)\n";
const MOD_LIB_TURN: &str = "/mod lib\n(defn later [] 2)\n/mod user\n/quit\n";

/// After `session` defined `later` in `lib`, `lib.cl` MUST hold it beside the
/// macro call and `base`, and a cold restart from the files MUST run all three.
fn assert_mod_turn_persisted_to_lib(session: e2e::CrOutput) {
    let lib = session.read_tmp("lib.cl");
    let counts: Vec<(&str, usize)> = ["(mk)", "(defn base [] 5)", "(defn later [] 2)"]
        .iter()
        .map(|f| (*f, lib.matches(f).count()))
        .collect();
    assert!(
        counts.iter().all(|&(_, n)| n == 1),
        "the `/mod lib` definition MUST regenerate lib.cl with every form once; \
         counts {counts:?}; lib.cl:\n{lib}\nstderr:\n{}",
        session.stderr
    );

    std::fs::remove_dir_all(session.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    let cold = session
        .run_again()
        .repl()
        .stdin("(lib/later)\n(lib/x-def)\n(base)\n/quit\n")
        .output()
        .assert_ok();
    let t = turns(&cold.stdout);
    for (i, value) in [
        ":primitives/Int 2",
        ":primitives/Int 1",
        ":primitives/Int 5",
    ]
    .iter()
    .enumerate()
    {
        assert!(
            t.get(i + 1).is_some_and(|turn| turn.contains(value)),
            "cold restart turn {} MUST yield {value}; stdout:\n{}",
            i + 1,
            cold.stdout
        );
    }
}

// spec: repl/spec/15-session-persistence.md §15.4 rule 6 — rule 1 holds whether
// the module was compiled from source or restored from cache;
// repl/spec/03-slash-commands.md §3.9 names the `/mod M` file-backed dev loop.
// RED when authored (S122, SL-1): with `lib` restored from cache, the turn warns
// `no recorded source for `x-def`` and leaves lib.cl without `later`. The lead's
// entry-module face did not reproduce, including through stdlib `def`. Control:
// persist_mod_turn_on_fresh_macro_expanded_module_control.
// defect: class=enumeration-miss locus=src/save.rs::authored_keys found=S122 owner=/dev — rehydration keys no top-level macro call, so definitions a cached module's macro call produced have no record
#[test]
fn persist_mod_turn_on_cache_restored_macro_expanded_module() {
    let first = Cranelisp::new()
        .repl()
        .file("lib.cl", MACRO_LIB)
        .stdin(&format!("{IMPORT_LIB}/quit\n"))
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 5");
    assert!(
        first.tmp_exists(".cranelisp-cache/lib.meta.json"),
        "precondition: session 1 MUST cache lib"
    );
    let second = first
        .run_again()
        .repl()
        .stdin(MOD_LIB_TURN)
        .output()
        .assert_ok();
    assert_mod_turn_persisted_to_lib(second);
}

// spec: repl/spec/15-session-persistence.md §15.4 rule 6 — control: the same
// `/mod lib` turn in the session that compiled `lib` from source.
#[test]
fn persist_mod_turn_on_fresh_macro_expanded_module_control() {
    let session = Cranelisp::new()
        .repl()
        .file("lib.cl", MACRO_LIB)
        .stdin(&format!("{IMPORT_LIB}{MOD_LIB_TURN}"))
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 5");
    assert_mod_turn_persisted_to_lib(session);
}

// =============================================================================
// §18.5, §15.6 — a live `deftype` layout change is rejected and never written
// =============================================================================

// spec: repl/spec/18-redefinition.md §18.5 — a live same-name `deftype` that adds
// a product field is rejected atomically: the prior constructor and accessor
// stay live and no part of the candidate is published;
// repl/spec/15-session-persistence.md §15.6 — the rejection does not change the
// regenerated source, and a cold restart yields the prior type. The same edit
// arriving by reload also fails, under repl/spec/14-file-watching.md §14.8:
// persist_structural_reload_failure_keeps_saved_edit_until_restart.
#[test]
fn persist_live_deftype_adding_product_field_rejected_and_not_written_neg() {
    let first = Cranelisp::new()
        .repl()
        .stdin(&format!(
            "{T_ONE_FIELD}\n{T_TWO_FIELDS}\n(T.v (T 7))\n(T.w (T 7 8))\n(defn other [] 3)\n/quit\n"
        ))
        .output()
        .assert_ok();
    let t = turns(&first.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    assert!(
        turn(2).contains("Error") && !turn(2).contains("; deftype"),
        "the field-adding redefinition MUST be rejected (§18.5); stdout:\n{}",
        first.stdout
    );
    assert!(
        turn(3).contains(":primitives/Int 7"),
        "the prior constructor and accessor MUST stay live; stdout:\n{}",
        first.stdout
    );
    assert!(
        turn(4).contains("Error") && !turn(4).contains(":primitives/Int 8"),
        "no part of the rejected candidate MAY be published; stdout:\n{}",
        first.stdout
    );
    assert!(
        turn(5).contains("user/other"),
        "precondition: the later definition MUST be accepted; stdout:\n{}",
        first.stdout
    );
    let saved = first.read_tmp("user.cl");
    assert!(
        saved.matches(T_ONE_FIELD).count() == 1
            && !saved.contains(T_TWO_FIELDS)
            && saved.contains("(defn other [] 3)"),
        "regeneration after the rejection MUST write the prior `T` only; user.cl:\n{saved}"
    );

    std::fs::remove_dir_all(first.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    let cold = first
        .run_again()
        .repl()
        .stdin("(T.v (T 7))\n(other)\n/quit\n")
        .output()
        .assert_ok();
    let t = turns(&cold.stdout);
    assert!(
        !cold.stdout.contains("[errors:")
            && t.get(1).is_some_and(|t| t.contains(":primitives/Int 7"))
            && t.get(2).is_some_and(|t| t.contains(":primitives/Int 3")),
        "cold restart MUST yield the prior one-field `T`; stdout:\n{}",
        cold.stdout
    );
}

// spec: repl/spec/18-redefinition.md §18.5 — a live same-name `deftype` that
// changes only a field's type is rejected atomically, under the same rule as a
// reload (§14.8): values built earlier and the prior constructor and accessor
// keep the `Int` layout, the next definition turn writes the `Int` declaration
// once, and a cold restart gives 7. RB-6. Its value probe is `(T.v (x))`, where
// `x` was compiled against the `Int` constructor, so a wrong accept would read
// the `Int` payload under the `String` layout. RED when authored (S122): the
// redefinition was accepted, and `(T.v (x))` ended the process with SIGSEGV.
// defect: class=wrong-accept locus=src/redefine.rs::validate_guarded_redefinition found=S122 owner=/dev fixed=S122/63605970
#[test]
fn persist_live_deftype_changing_field_type_rejected_and_not_written_neg() {
    // Turns: 1 T, 2 x, 3 redefinition, 4 (T.v (x)), 5 (T.v (T 7)), 6 other.
    let first = Cranelisp::new()
        .repl()
        .stdin(&format!(
            "{T_ONE_FIELD}\n(defn x [] (T 7))\n{T_STRING_FIELD}\n(T.v (x))\n(T.v (T 7))\n\
             (defn other [] 3)\n/quit\n"
        ))
        .output();
    let t = turns(&first.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let mut legs = Legs::default();
    legs.check(
        turn(3).contains("Error") && !turn(3).contains("; deftype"),
        "the field-type redefinition is rejected, with no `deftype` echo",
    );
    legs.check(
        turn(4).contains(":primitives/Int 7"),
        "a value built by the prior constructor still reads 7",
    );
    legs.check(
        turn(5).contains(":primitives/Int 7"),
        "the prior constructor and accessor stay live",
    );
    legs.check(
        turn(6).contains("user/other"),
        "precondition: the later definition is accepted",
    );
    let saved = first.read_tmp("user.cl");
    legs.check(
        saved.matches(T_ONE_FIELD).count() == 1 && !saved.contains(T_STRING_FIELD),
        "the regeneration writes the prior `Int` declaration once and not the rejected one",
    );
    let first_log = format!("{}\nuser.cl:\n{saved}", transcript(&first));

    std::fs::remove_dir_all(first.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    let cold = first
        .run_again()
        .repl()
        .stdin("(T.v (T 7))\n/quit\n")
        .output();
    legs.check(
        !cold.stdout.contains("[errors:")
            && turns(&cold.stdout)
                .get(1)
                .is_some_and(|t| t.contains(":primitives/Int 7")),
        "a cold restart gives 7 from the one-field `Int` declaration",
    );
    legs.assert_all(&format!(
        "{first_log}\n--- cold restart ---\n{}",
        transcript(&cold)
    ));
}

// =============================================================================
// §15.3, §15.4, §14.8 — a reloaded declaration edit survives the next
// regeneration; a structural one is retained until restart
// =============================================================================

const T_DOC_PRIOR: &str = "(deftype T \"Prior doc.\" [:primitives/Int v])";
const T_DOC_EDITED: &str = "(deftype T \"Edited doc.\" [:primitives/Int v])";

/// `seed` is the initial `user.cl` (empty for none) and `before` the REPL
/// turns entered before the edit. `edited` then overwrites `user.cl` on one
/// line, the reload MUST make `probe` yield `value`, and `(defn h [] 2)`
/// regenerates the file. That file MUST hold `edited_decl` once and not
/// `stale_decl`, and a cold restart from it MUST yield `value` and 2.
fn assert_reloaded_declaration_persists(
    seed: &str,
    before: &str,
    edited: &str,
    edited_decl: &str,
    stale_decl: &str,
    probe: &str,
    value: &str,
) {
    const H: &str = "(defn h [] 2)";
    let mut session = Cranelisp::new();
    if !seed.is_empty() {
        session = session.user(&format!("{seed}\n"));
    }
    let first = session
        .repl()
        .stdin(&format!(
            "{before}/sh sleep 0.3\n/sh echo '{edited}' > user.cl\n/sh sleep 0.5\n\
             {probe}\n{H}\n/quit\n"
        ))
        .output();
    let all = format!("{}{}", first.stdout, first.stderr);
    assert!(
        first.stdout.contains("[updated: user.cl]")
            && !all.contains("[errors:")
            && turns(&first.stdout).iter().any(|t| t.contains(value)),
        "precondition: the edit MUST reload and `{probe}` yield {value} (§14.2); got:\n{all}"
    );
    let saved = first.read_tmp("user.cl");
    assert!(
        saved.matches(edited_decl).count() == 1 && !saved.contains(stale_decl) && saved.contains(H),
        "the regeneration after the reload MUST write the edited declaration, \
         not the prior one; user.cl:\n{saved}"
    );

    std::fs::remove_dir_all(first.tmpdir.join(".cranelisp-cache")).expect("rm .cranelisp-cache");
    let cold = first
        .run_again()
        .repl()
        .stdin(&format!("{probe}\n(h)\n/quit\n"))
        .output();
    let t = turns(&cold.stdout);
    assert!(
        !cold.stdout.contains("[errors:")
            && t.get(1).is_some_and(|t| t.contains(value))
            && t.get(2).is_some_and(|t| t.contains(":primitives/Int 2")),
        "cold restart MUST yield the edited declaration; stdout:\n{}\nstderr:\n{}",
        cold.stdout,
        cold.stderr
    );
}

// spec: repl/spec/14-file-watching.md §14.8 — a structurally identical
// redeclaration reloads; repl/spec/18-redefinition.md §18.5 — a docstring is
// non-structural and updates live documentation;
// repl/spec/15-session-persistence.md §15.4 rule 1 — the next regeneration
// writes the edited declaration. RB-2(b), REPL-entered route. `T`'s record
// holds the REPL text of the prior generation (design/int/session-persistence.md
// §2.4.4, second limit). This is the safety fence for the S122 P5 correction,
// transposed from a field-type edit that §14.8 now refuses. That field-type
// form was RED before the fix (S122, PR-3): the reload succeeded, but defining
// `h` wrote the old `T` over the edit. This docstring form was not observed RED.
// defect: class=partial-record-update locus=src/process_form.rs::process_regular_form_with_origin found=S122 owner=/dev fixed=S122/63605970 — the record writer recorded only functions, so a successful reload left the prior generation's declaration record to be regenerated
#[test]
fn persist_reloaded_docstring_edit_of_repl_entered_type_survives_regeneration() {
    assert_reloaded_declaration_persists(
        "",
        &format!("{T_DOC_PRIOR}\n"),
        T_DOC_EDITED,
        T_DOC_EDITED,
        T_DOC_PRIOR,
        "/doc T",
        "Edited doc.",
    );
}

// spec: repl/spec/14-file-watching.md §14.8, repl/spec/18-redefinition.md
// §18.5, repl/spec/15-session-persistence.md §15.4 rule 1 — as the
// REPL-entered cell, with `T` loaded from the backing file and a definition
// turn regenerating the file before the edit, so `T`'s record is rehydrated
// from the prior generation (design/int/session-persistence.md §2.4.4, second
// limit). RB-2(b), file-loaded route. Transposed as the REPL-entered cell: the
// field-type form was RED before the fix (S122, PR-3); this docstring form was
// not observed RED.
// defect: class=partial-record-update locus=src/process_form.rs::process_regular_form_with_origin found=S122 owner=/dev fixed=S122/63605970 — the record writer recorded only functions, so a successful reload left the prior generation's declaration record to be regenerated
#[test]
fn persist_reloaded_docstring_edit_of_file_loaded_type_survives_regeneration() {
    assert_reloaded_declaration_persists(
        T_DOC_PRIOR,
        "(defn g [] 1)\n",
        &format!("{T_DOC_EDITED} (defn g [] 1)"),
        T_DOC_EDITED,
        T_DOC_PRIOR,
        "/doc T",
        "Edited doc.",
    );
}

// spec: repl/spec/14-file-watching.md §14.8, §14.5 item 5 — after a
// file-loaded `T` gains a field, the reload fails and the module is locked, so
// the saved edit is retained: a definition turn that would regenerate the file
// is rejected and leaves the session and the file unchanged; evaluation stays
// blocked (§14.4); a second structurally different save fails again. A restart that keeps the cache compiles the
// saved source (§15.2) and establishes the two-field `T`; the next definition
// regenerates the file with it (§15.1). RB-3. RED when authored (S122): the
// definition turn is accepted and overwrites the saved edit (ACT-0998 p2a).
#[test]
fn persist_structural_reload_failure_keeps_saved_edit_until_restart() {
    let first_save = format!("{T_TWO_FIELDS} (defn g [] 1)");
    let second_save = format!("{T_TWO_FIELDS} (defn g [] 3)");
    // Turns: 1 (defn g), 2–4 save, 5 (defn h), 6 /sig h, 7 (g), 8 snapshot of
    // user.cl after the rejected turn, 9–11 save.
    let first = Cranelisp::new()
        .user(&format!("{T_ONE_FIELD}\n"))
        .repl()
        .stdin(&format!(
            "(defn g [] 1)\n{}(defn h [] 2)\n/sig h\n(g)\n/sh cp user.cl after-rejected-turn.txt\n\
             {}/quit\n",
            save("user.cl", &first_save),
            save("user.cl", &second_save)
        ))
        .output();
    let t = turns(&first.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let blocks = error_blocks(&first, "user.cl");
    let mut legs = Legs::default();
    legs.check(
        !first.stdout.contains("[updated: user.cl]"),
        "neither structural save reloads: no `[updated: user.cl]`",
    );
    legs.check(
        blocks.len() == 2 && blocks.iter().all(|b| requires_restart_for(b, "T")),
        "each structural save fails with the §14.8 diagnostic",
    );
    legs.check(
        !turn(5).contains("user/h"),
        "the definition turn during the failure is rejected",
    );
    legs.check(
        !turn(6).contains("user/h"),
        "`/sig h` shows `h` undefined: the rejection left the session unchanged",
    );
    legs.check(
        turn(7).contains("Cannot evaluate") && !turn(7).contains(":primitives/Int"),
        "evaluation is blocked",
    );
    let after_rejected_turn = first.read_tmp("after-rejected-turn.txt");
    legs.check(
        after_rejected_turn == format!("{first_save}\n"),
        "user.cl is byte-identical to the saved edit after the rejected turn",
    );
    let saved = first.read_tmp("user.cl");
    legs.check(
        saved == format!("{second_save}\n"),
        "user.cl is byte-identical to the last save after the session ends",
    );
    let first_log = format!(
        "{}\nuser.cl after the rejected turn:\n{after_rejected_turn}\nuser.cl at exit:\n{saved}",
        transcript(&first)
    );

    let restarted = first
        .run_again()
        .repl()
        .stdin("(T.w (T 1 2))\n(g)\n(defn h [] 2)\n/sig h\n/quit\n")
        .output();
    let t = turns(&restarted.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    legs.check(
        !format!("{}{}", restarted.stdout, restarted.stderr).contains("[errors:"),
        "the restart, keeping the cache, loads the saved source without `[errors:`",
    );
    legs.check(
        turn(1).contains(":primitives/Int 2") && turn(2).contains(":primitives/Int 3"),
        "the restart establishes the two-field `T` and the last saved `g`",
    );
    legs.check(
        turn(3).contains("user/h") && turn(4).contains("user/h"),
        "after the restart a definition is accepted and `/sig h` shows it",
    );
    let regenerated = restarted.read_tmp("user.cl");
    legs.check(
        regenerated.matches(T_TWO_FIELDS).count() == 1
            && regenerated.matches("(defn g [] 3)").count() == 1
            && regenerated.matches("(defn h [] 2)").count() == 1
            && !regenerated.contains(T_ONE_FIELD),
        "the definition regenerates user.cl with the two-field `T`",
    );
    legs.assert_all(&format!(
        "{first_log}\n--- restart ---\n{}\nuser.cl:\n{regenerated}",
        transcript(&restarted)
    ));
}

// =============================================================================
// §14.8 — a structural change to an imported type fails its reload
// =============================================================================

// spec: repl/spec/14-file-watching.md §14.8 — swapping the two fields of `T` in
// `shapes.cl`, which `reader` and the REPL import, is structural, so the reload
// fails: `[errors: shapes.cl]` names `T` and says a restart is required, the
// dependent runs neither the old nor the new layout (§14.4 items 2–3), and
// `/quit` is read. RB-5; QA accepts it after 15 consecutive passes. RED when
// authored (S122): the reorder reloads and the dependent reads 2. The failure
// path it requires is the hang shape of
// tests/repl_watch.rs::watch_type_error_reload_of_imported_module_blocks_without_hanging.
#[test]
fn watch_imported_type_field_reorder_fails_requiring_restart() {
    // Turns: 3 (read-a (T 1 2)), 4–6 save, 7 (read-a (T 1 2)).
    let out = Cranelisp::new()
        .file(
            "shapes.cl",
            "(deftype T [:primitives/Int a :primitives/Int b])\n",
        )
        .file(
            "reader.cl",
            "(import [shapes [T]])\n(defn read-a [t] (T.a t))\n",
        )
        .repl()
        .stdin(&format!(
            "(import [shapes [T]])\n(import [reader [read-a]])\n(read-a (T 1 2))\n\
             {}(read-a (T 1 2))\n/quit\n",
            save(
                "shapes.cl",
                "(deftype T [:primitives/Int b :primitives/Int a])"
            )
        ))
        .timeout(std::time::Duration::from_secs(10))
        .try_output()
        .unwrap_or_else(|e| panic!("the REPL MUST report the failed reload and read `/quit`; {e}"));
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let mut legs = Legs::default();
    legs.check(
        turn(3).contains(":primitives/Int 1"),
        "precondition: `read-a` reads `a` before the edit",
    );
    legs.check(
        out.status.code().is_some(),
        "the session exits after `/quit` (not by a signal)",
    );
    legs.check(
        !out.stdout.contains("[updated: shapes.cl]"),
        "the reload fails: no `[updated: shapes.cl]`",
    );
    legs.check(
        error_blocks(&out, "shapes.cl")
            .iter()
            .any(|b| requires_restart_for(b, "T")),
        "`[errors: shapes.cl]` names `T` and says a restart is required",
    );
    legs.check(
        !turn(7).contains(":primitives/Int 1") && !turn(7).contains(":primitives/Int 2"),
        "the dependent is refused and yields neither 1 nor 2",
    );
    legs.assert_all(&transcript(&out));
}

// =============================================================================
// §14.2 step 2 — a successful reload retires definitions its source omits
// =============================================================================

// spec: repl/spec/14-file-watching.md §14.2 — step 2 clears the module's
// previous definitions, so a save that omits `h` reloads (`[updated:]`) and
// leaves `h` neither callable nor listed by `/sig`; the retained `g` still
// evaluates. repl/spec/15-session-persistence.md §15.1 — the next definition
// regenerates the file with `g` and `k` and without `h`. RM-1 (ACT-1007).
// The prepared commit published the names the source defined and retired no
// omitted one, so `h` stayed callable, listed by `/sig` and written back.
// defect: class=partial-record-update locus=src/worker.rs::finish_prepared_commit found=S122 owner=/dev fixed=S122/e4062202 — fixed by the whole-file rebuild (design/int/session-transaction.md §7.3.1)
#[test]
fn persist_definition_removed_by_save_is_not_callable_or_rewritten() {
    // Turns: 1 (h), 2–4 save, 5 (h), 6 /sig h, 7 (g), 8 (defn k).
    let out = Cranelisp::new()
        .user("(defn g [] 1)\n(defn h [] 2)\n")
        .repl()
        .stdin(&format!(
            "(h)\n{}(h)\n/sig h\n(g)\n(defn k [] 3)\n/quit\n",
            save("user.cl", "(defn g [] 1)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 2"),
        "precondition: `(h)` gives 2 before the save",
    );
    legs.check(
        out.stdout.contains("[updated: user.cl]") && !out.stdout.contains("[errors:"),
        "the save omitting `h` reloads: `[updated: user.cl]`",
    );
    legs.check(
        !turn(5).contains(":primitives/Int 2"),
        "`(h)` does not give 2 after the reload",
    );
    legs.check(
        !turn(6).contains("user/h"),
        "`/sig h` reports `h` undefined",
    );
    legs.check(
        turn(7).contains(":primitives/Int 1"),
        "control: the retained `g` gives 1",
    );
    legs.check(
        turn(8).contains("user/k"),
        "the definition turn is accepted",
    );
    legs.check(
        saved.matches("(defn g [] 1)").count() == 1
            && saved.matches("(defn k [] 3)").count() == 1
            && !saved.contains("defn h"),
        "regeneration writes `g` and `k` and does not write `h` back",
    );
    legs.assert_all(&format!("{}\nuser.cl:\n{saved}", transcript(&out)));
}

// spec: repl/spec/14-file-watching.md §14.2 — steps 2 and 4: `lib.cl` saved
// without `h` reloads, the cascade recompiles its importer, whose import of
// `h` no longer resolves, so it reports `[errors: user.cl]`; `(h)` does not
// give 2. RM-2 (ACT-1007).
// `lib` kept `h`, so the importer reloaded (`[updated: user.cl]`) and `(h)`
// still gave 2: RM-1's retention seen across an import.
// defect: class=partial-record-update locus=src/worker.rs::finish_prepared_commit found=S122 owner=/dev fixed=S122/e4062202 — fixed by the whole-file rebuild (design/int/session-transaction.md §7.3.1)
#[test]
fn watch_definition_removed_from_imported_file_fails_its_importer() {
    // Turns: 1 (h), 2–4 save, 5 (h).
    let out = Cranelisp::new()
        .file("lib.cl", "(defn g [] 1)\n(defn h [] 2)\n")
        .user("(import [lib [g h]])\n")
        .repl()
        .stdin(&format!(
            "(h)\n{}(h)\n/quit\n",
            save("lib.cl", "(defn g [] 1)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 2"),
        "precondition: the imported `(h)` gives 2 before the save",
    );
    legs.check(
        out.stdout.contains("[updated: lib.cl]"),
        "the save omitting `h` reloads: `[updated: lib.cl]`",
    );
    legs.check(
        !error_blocks(&out, "user.cl").is_empty(),
        "the importer reports `[errors: user.cl]`",
    );
    legs.check(
        !turn(5).contains(":primitives/Int 2"),
        "`(h)` does not give 2 after the reload",
    );
    legs.assert_all(&transcript(&out));
}

// spec: repl/spec/14-file-watching.md §14.2 — step 2 retires a generic
// function the save omits as it does a concrete one: after `[updated:]`,
// `(id 5)` does not give 5 and `/sig id` reports `id` undefined; the concrete
// `h` omitted by the same save is the control. repl/spec/15-session-persistence.md
// §15.1 — the next definition regenerates the file without `id`. RM-3
// (ACT-1007 G1).
// The types planner accepted an absent-key removal only for a slotted binding,
// so the slotless generic `id` stayed callable, listed and written back.
// defect: class=partial-record-update locus=crates/cranelisp-types/src/module.rs::plan_staged_publication found=S122 owner=/dev fixed=S122/e4062202 — fixed by the whole-file rebuild (design/int/session-transaction.md §7.3.1)
#[test]
fn persist_generic_definition_removed_by_save_is_not_callable_or_rewritten() {
    // Turns: 1 (id 5), 2–4 save, 5 (h), 6 (id 5), 7 /sig id, 8 (defn k).
    let out = Cranelisp::new()
        .user("(defn g [] 1)\n(defn h [] 2)\n(defn id [x] x)\n")
        .repl()
        .stdin(&format!(
            "(id 5)\n{}(h)\n(id 5)\n/sig id\n(defn k [] 3)\n/quit\n",
            save("user.cl", "(defn g [] 1)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 5"),
        "precondition: `(id 5)` gives 5 before the save",
    );
    legs.check(
        out.stdout.contains("[updated: user.cl]") && !out.stdout.contains("[errors:"),
        "the save omitting `h` and `id` reloads: `[updated: user.cl]`",
    );
    legs.check(
        !turn(5).contains(":primitives/Int 2"),
        "control: the omitted concrete `(h)` fails",
    );
    legs.check(
        !turn(6).contains(":primitives/Int 5"),
        "`(id 5)` does not give 5 after the reload",
    );
    legs.check(
        !turn(7).contains("user/id"),
        "`/sig id` reports `id` undefined",
    );
    legs.check(
        turn(8).contains("user/k"),
        "the definition turn is accepted",
    );
    legs.check(
        saved.matches("(defn k [] 3)").count() == 1 && !saved.contains("defn id"),
        "regeneration writes `k` and does not write `id` back",
    );
    legs.assert_all(&format!("{}\nuser.cl:\n{saved}", transcript(&out)));
}

// spec: repl/spec/14-file-watching.md §14.2 — a save that omits both `h` and
// the generic `wrap` calling it compiles, so it reloads (`[updated: user.cl]`,
// no `[errors:`) and step 2 retires both: `/sig wrap` and `/sig h` report them
// undefined. §14.5 — the save did not fail, so the module is not locked:
// `(g)` gives 1 and a definition is accepted. RM-4 (ACT-1007 G2).
// The referer scan read the callees of the surviving generic `wrap`, refused
// the compiling save as naming the removed `h`, and locked the module.
// defect: class=wrong-reject locus=src/worker.rs::refuse_removed_referers found=S122 owner=/dev fixed=S122/e4062202 — retired with the removal list; the whole-file rebuild (design/int/session-transaction.md §7.3.1) has no referer scan
#[test]
fn persist_save_omitting_generic_caller_and_its_callee_reloads_unlocked() {
    // Turns: 1 (h), 2–4 save, 5 (g), 6 (defn k), 7 /sig wrap, 8 /sig h.
    let out = Cranelisp::new()
        .user("(defn h [] 2)\n(defn wrap [x] (let [y (h)] x))\n")
        .repl()
        .stdin(&format!(
            "(h)\n{}(g)\n(defn k [] 3)\n/sig wrap\n/sig h\n/quit\n",
            save("user.cl", "(defn g [] 1)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 2"),
        "precondition: `(h)` gives 2 before the save",
    );
    legs.check(
        out.stdout.contains("[updated: user.cl]")
            && !format!("{}{}", out.stdout, out.stderr).contains("[errors:"),
        "the compiling save reloads: `[updated: user.cl]` and no `[errors:`",
    );
    legs.check(
        turn(5).contains(":primitives/Int 1"),
        "`(g)` gives 1 from the saved source",
    );
    legs.check(
        turn(6).contains("user/k"),
        "the definition turn is accepted: the module is not locked",
    );
    legs.check(
        !turn(7).contains("user/wrap"),
        "`/sig wrap` reports `wrap` undefined",
    );
    legs.check(
        !turn(8).contains("user/h"),
        "`/sig h` reports `h` undefined",
    );
    legs.assert_all(&transcript(&out));
}

// spec: repl/spec/14-file-watching.md §14.2 — steps 2 and 4: `lib.cl` saved
// without the generic `id` reloads, and the cascade recompiles its importer,
// whose import of `id` no longer resolves, so it reports `[errors: user.cl]`
// and `(call)` does not give 5. §14.5 item 5 — the importer's own save that
// compiles releases it: `[updated: user.cl]`, no further `[errors: user.cl]`,
// `(k)` gives 3 and a definition is accepted. repl/spec/15-session-persistence.md
// §15.1 — regeneration writes `k` and `m` and not the omitted `call`. RM-5
// (ACT-1007 G1 across an import).
// The types planner accepted an absent-key removal only for a slotted binding,
// so `lib` kept the slotless generic `id`, the importer reloaded and `(call)`
// still gave 5. The omitted import this save left behind was ACT-1012's,
// observed by `persist_import_omitted_by_save_is_not_in_scope_or_rewritten`.
// defect: class=partial-record-update locus=crates/cranelisp-types/src/module.rs::plan_staged_publication found=S122 owner=/dev fixed=S122/e4062202 — fixed by the whole-file rebuild (design/int/session-transaction.md §7.3.1)
#[test]
fn watch_generic_removed_from_imported_file_fails_importer_until_its_save() {
    // Turns: 1 (call), 2–4 save lib, 5 (call), 6–8 save user, 9 (k),
    // 10 (defn m).
    let out = Cranelisp::new()
        .file("lib.cl", "(defn g [] 1)\n(defn id [x] x)\n")
        .user("(import [lib [id]])\n(defn call [] (id 5))\n")
        .repl()
        .stdin(&format!(
            "(call)\n{}(call)\n{}(k)\n(defn m [] 4)\n/quit\n",
            save("lib.cl", "(defn g [] 1)"),
            save("user.cl", "(defn k [] 3)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let lib_save: String = (2..=5).map(turn).collect();
    let user_save: String = (6..t.len()).map(turn).collect();
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 5"),
        "precondition: `(call)` gives 5 before the save",
    );
    legs.check(
        lib_save.contains("[updated: lib.cl]"),
        "the save omitting `id` reloads: `[updated: lib.cl]`",
    );
    legs.check(
        lib_save.contains("[errors: user.cl]"),
        "the importer reports `[errors: user.cl]`",
    );
    legs.check(
        !turn(5).contains(":primitives/Int 5"),
        "`(call)` does not give 5 after the reload",
    );
    legs.check(
        user_save.contains("[updated: user.cl]") && !user_save.contains("[errors: user.cl]"),
        "the importer's save that compiles reloads: `[updated: user.cl]` and no `[errors: user.cl]`",
    );
    legs.check(
        turn(9).contains(":primitives/Int 3"),
        "`(k)` gives 3 from the saved source",
    );
    legs.check(
        turn(10).contains("user/m"),
        "the definition turn is accepted: the module is not locked",
    );
    legs.check(
        saved.matches("(defn k [] 3)").count() == 1
            && saved.matches("(defn m [] 4)").count() == 1
            && !saved.contains("(id 5)"),
        "regeneration writes `k` and `m` and does not write `call` back",
    );
    legs.assert_all(&format!("{}\nuser.cl:\n{saved}", transcript(&out)));
}

// =============================================================================
// §14.2 step 2, §15.1 — a successful reload retires an import its source omits
// =============================================================================

/// A session over an unchanged `lib` whose `user.cl` imports `id`, in which
/// `user.cl` is saved as `saved` and then extended by one definition.
/// Turns: 1 `/imports lib`, 2 `(id 5)`, 3–5 save, 6 `(k)`, 7 `/imports lib`,
/// 8 `(id 5)`, 9 `(defn m)`.
fn import_session_after_user_save(saved: &str) -> e2e::CrOutput {
    Cranelisp::new()
        .file("lib.cl", "(defn g [] 1)\n(defn id [x] x)\n")
        .user("(import [lib [id]])\n(defn k [] 2)\n")
        .repl()
        .stdin(&format!(
            "/imports lib\n(id 5)\n{}(k)\n/imports lib\n(id 5)\n(defn m [] 4)\n/quit\n",
            save("user.cl", saved)
        ))
        .output()
}

/// Whether a `/imports lib` response lists `id` under its `From lib:` header.
fn lists_id_from_lib(response: &str) -> bool {
    response.contains("From lib:") && response.split_whitespace().any(|w| w == "id")
}

/// The legs both import cells share: the import is in scope before the save,
/// the save reloads from its own source, and the module stays unlocked.
fn check_import_session_frame(legs: &mut Legs, out: &e2e::CrOutput, t: &[&str]) {
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    legs.check(
        lists_id_from_lib(turn(1)),
        "precondition: `/imports lib` lists `id` before the save",
    );
    legs.check(
        turn(2).contains(":primitives/Int 5"),
        "precondition: the imported `(id 5)` gives 5 before the save",
    );
    legs.check(
        out.stdout.contains("[updated: user.cl]")
            && !format!("{}{}", out.stdout, out.stderr).contains("[errors:"),
        "the save reloads: `[updated: user.cl]` and no `[errors:`",
    );
    legs.check(
        turn(6).contains(":primitives/Int 3"),
        "`(k)` gives 3 from the saved source",
    );
    legs.check(
        turn(9).contains("user/m"),
        "the definition turn is accepted: the module is not locked",
    );
}

// spec: repl/spec/14-file-watching.md §14.2 — step 2 clears the module's
// previous state, so after a save of `user.cl` that omits its only `import`
// reloads (`[updated: user.cl]`), `/imports lib` no longer lists `id` and a
// bare `(id 5)` does not give 5; `lib` is unchanged and defines `id`
// throughout. repl/spec/15-session-persistence.md §15.1 — the next definition
// regenerates the file without the import. ACT-1012 C2; the kept-import twin is
// `persist_import_kept_by_save_stays_in_scope_and_is_written_once_control`.
// The reload kept the omitted import, so `id` stayed listed and
// bare-resolvable, and regeneration wrote the import back.
// defect: class=partial-record-update locus=src/process_form/form_dispatch.rs::record_imports_on_symbol_table found=S122 owner=/dev fixed=S122/e4062202 — the whole-source reload appended to the prior table's record and never reset it; fixed by the whole-file rebuild's fresh table (design/int/session-transaction.md §7.3.1)
#[test]
fn persist_import_omitted_by_save_is_not_in_scope_or_rewritten() {
    let out = import_session_after_user_save("(defn k [] 3)");
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    check_import_session_frame(&mut legs, &out, &t);
    legs.check(
        !lists_id_from_lib(turn(7)),
        "`/imports lib` does not list `id` after the reload",
    );
    legs.check(
        !turn(8).contains(":primitives/Int 5"),
        "a bare `(id 5)` does not give 5 after the reload",
    );
    legs.check(
        saved.matches("(defn k [] 3)").count() == 1
            && saved.matches("(defn m [] 4)").count() == 1
            && !saved.contains("import"),
        "regeneration writes `k` and `m` and does not write the import back",
    );
    legs.assert_all(&format!("{}\nuser.cl:\n{saved}", transcript(&out)));
}

// spec: repl/spec/14-file-watching.md §14.2 — a save of `user.cl` that keeps
// its `import` reloads, and `id` stays listed by `/imports lib` and gives 5 as
// a bare `(id 5)`. repl/spec/15-session-persistence.md §15.1 — the next
// definition regenerates the file with the import exactly once. ACT-1012 C3,
// the control for `persist_import_omitted_by_save_is_not_in_scope_or_rewritten`:
// the save differs from that cell's only by the import.
#[test]
fn persist_import_kept_by_save_stays_in_scope_and_is_written_once_control() {
    let out = import_session_after_user_save("(import [lib [id]]) (defn k [] 3)");
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    check_import_session_frame(&mut legs, &out, &t);
    legs.check(
        lists_id_from_lib(turn(7)),
        "`/imports lib` still lists `id` after the reload",
    );
    legs.check(
        turn(8).contains(":primitives/Int 5"),
        "a bare `(id 5)` still gives 5 after the reload",
    );
    legs.check(
        saved.matches("(import [lib [id]])").count() == 1
            && saved.matches("import").count() == 1
            && saved.matches("(defn k [] 3)").count() == 1
            && saved.matches("(defn m [] 4)").count() == 1,
        "regeneration writes the import exactly once, with `k` and `m`",
    );
    legs.assert_all(&format!("{}\nuser.cl:\n{saved}", transcript(&out)));
}

// =============================================================================
// §14.5 item 5, §14.6, §15.2.3 — a failed reload locks its module's file
// =============================================================================

const FL_TYPE_ERROR: &str = "(defn g [] (undefined-name 1))";
const FL_PARSE_ERROR: &str = "(defn g [] ";
const FL_FIXED: &str = "(defn g [] 5)";

// spec: repl/spec/14-file-watching.md §14.5 item 5 — a save that fails to
// typecheck locks `user.cl`: `[errors: user.cl]` lists the error, a definition
// turn is rejected and leaves the session (`/sig h`) and the file unchanged,
// and evaluation is refused (§14.4). A later parse-error save fails again and
// the lock stands. A save that compiles releases it (§14.4 item 4, §14.6);
// the next definition regenerates the file from the saved content (§15.1).
// FL-1.
#[test]
fn persist_type_error_reload_locks_file_until_a_save_compiles() {
    // Turns: 1–3 save, 4 (defn h), 5 /sig h, 6 (g), 7 snapshot, 8–10 save,
    // 11 (defn h), 12 snapshot, 13–15 save, 16 (g), 17 (defn h).
    let out = Cranelisp::new()
        .user("(defn g [] 1)\n")
        .repl()
        .stdin(&format!(
            "{}(defn h [] 2)\n/sig h\n(g)\n/sh cp user.cl after-type-error.txt\n\
             {}(defn h [] 2)\n/sh cp user.cl after-parse-error.txt\n\
             {}(g)\n(defn h [] 2)\n/quit\n",
            save("user.cl", FL_TYPE_ERROR),
            save("user.cl", FL_PARSE_ERROR),
            save("user.cl", FL_FIXED)
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let after_type_error = out.read_tmp("after-type-error.txt");
    let after_parse_error = out.read_tmp("after-parse-error.txt");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        save_notice(&t, 1).contains("[errors: user.cl]")
            && error_blocks(&out, "user.cl")
                .first()
                .is_some_and(|b| b.contains("undefined-name")),
        "the type-error save fails: `[errors: user.cl]` lists the error",
    );
    legs.check(
        !turn(4).contains("user/h"),
        "the definition turn during the failure is rejected",
    );
    legs.check(
        !turn(5).contains("user/h"),
        "`/sig h` shows `h` undefined: the rejection left the session unchanged",
    );
    legs.check(
        !turn(6).contains(":primitives/Int"),
        "`(g)` is refused while the module has errors",
    );
    legs.check(
        after_type_error == format!("{FL_TYPE_ERROR}\n"),
        "user.cl is byte-identical to the type-error save after the rejected turn",
    );
    legs.check(
        save_notice(&t, 8).contains("[errors: user.cl]"),
        "the parse-error save fails again: `[errors: user.cl]`",
    );
    legs.check(
        !turn(11).contains("user/h"),
        "the lock stands after the second failure: the definition is rejected",
    );
    legs.check(
        after_parse_error == format!("{FL_PARSE_ERROR}\n"),
        "user.cl is byte-identical to the parse-error save after the rejected turn",
    );
    legs.check(
        save_notice(&t, 13).contains("[updated: user.cl]"),
        "the save that compiles reloads: `[updated: user.cl]`",
    );
    legs.check(
        turn(16).contains(":primitives/Int 5"),
        "evaluation resumes with the saved `g`",
    );
    legs.check(
        turn(17).contains("user/h"),
        "the released module accepts the definition",
    );
    legs.check(
        saved.matches("defn g").count() == 1
            && saved.matches(FL_FIXED).count() == 1
            && saved.matches("defn h").count() == 1
            && saved.matches("(defn h [] 2)").count() == 1
            && !saved.contains("undefined-name"),
        "user.cl holds `g` 5 and `h` exactly once each and no `undefined-name`",
    );
    legs.assert_all(&format!(
        "{}\nuser.cl after the type-error rejection:\n{after_type_error}\n\
         user.cl after the parse-error rejection:\n{after_parse_error}\nuser.cl at exit:\n{saved}",
        transcript(&out)
    ));
}

// spec: repl/spec/14-file-watching.md §14.5 item 5 — a save that does not
// parse locks `user.cl`: a definition turn is rejected, `/sig h` shows `h`
// undefined and the file keeps the saved text. §14.6 and
// repl/spec/15-session-persistence.md §15.2.3 (parse-failure lock paragraph) —
// a restart does not bypass the failure: the load error is reported and a
// prompt is reached, `(g)` is refused rather than giving the cached 1, a
// definition is rejected and the file is unchanged. A save that compiles then
// releases the lock. FL-2.
#[test]
fn persist_parse_error_reload_lock_survives_restart_until_a_save_compiles() {
    // Turns: 1–3 save, 4 (defn h), 5 /sig h.
    let first = Cranelisp::new()
        .user("(defn g [] 1)\n")
        .repl()
        .stdin(&format!(
            "{}(defn h [] 2)\n/sig h\n/quit\n",
            save("user.cl", FL_PARSE_ERROR)
        ))
        .output();
    let t = turns(&first.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = first.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        save_notice(&t, 1).contains("[errors: user.cl]"),
        "precondition: the parse-error save fails: `[errors: user.cl]`",
    );
    legs.check(
        !turn(4).contains("user/h"),
        "the definition turn during the failure is rejected",
    );
    legs.check(
        !turn(5).contains("user/h"),
        "`/sig h` shows `h` undefined: the rejection left the session unchanged",
    );
    legs.check(
        saved == format!("{FL_PARSE_ERROR}\n"),
        "user.cl is byte-identical to the parse-error save at exit",
    );
    let first_log = format!("{}\nuser.cl at exit:\n{saved}", transcript(&first));

    // Turns: 1 (g), 2 (defn h), 3 /sig h, 4 snapshot, 5–7 save, 8 (g),
    // 9 (defn h).
    let restarted = first
        .run_again()
        .repl()
        .stdin(&format!(
            "(g)\n(defn h [] 2)\n/sig h\n/sh cp user.cl after-restart-rejection.txt\n\
             {}(g)\n(defn h [] 2)\n/quit\n",
            save("user.cl", FL_FIXED)
        ))
        .output();
    let t = turns(&restarted.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let after_rejection = restarted.read_tmp("after-restart-rejection.txt");
    legs.check(
        format!("{}{}", turn(0), restarted.stderr).contains("[errors: user.cl]") && t.len() > 1,
        "the restart reports the load failure and reaches a prompt",
    );
    legs.check(
        !turn(1).contains(":primitives/Int"),
        "after the restart `(g)` is refused and does not give the cached 1",
    );
    legs.check(
        !turn(2).contains("user/h"),
        "after the restart the definition turn is rejected",
    );
    legs.check(
        !turn(3).contains("user/h"),
        "after the restart `/sig h` shows `h` undefined",
    );
    legs.check(
        after_rejection == format!("{FL_PARSE_ERROR}\n"),
        "after the restart user.cl is byte-identical to the parse-error save",
    );
    legs.check(
        save_notice(&t, 5).contains("[updated: user.cl]"),
        "the save that compiles reloads: `[updated: user.cl]`",
    );
    legs.check(
        turn(8).contains(":primitives/Int 5"),
        "evaluation resumes with the saved `g`",
    );
    legs.check(
        turn(9).contains("user/h"),
        "the released module accepts the definition",
    );
    legs.assert_all(&format!(
        "{first_log}\n--- restart ---\n{}\nuser.cl after the rejected turn:\n{after_rejection}",
        transcript(&restarted)
    ));
}

// spec: repl/spec/14-file-watching.md §14.5 item 5 — a module that fails in
// the cascade of a failed imported file is itself locked: `user`, importing
// `val` from `mymod.cl`, rejects a definition and keeps `user.cl` unchanged
// while `mymod.cl` has a type error. §14.6 — fixing `mymod.cl` recompiles both
// modules, which releases `user` without a save of `user.cl`; the next
// definition regenerates `user.cl` keeping the import and `g`. FL-3.
#[test]
fn watch_cascade_failed_importer_locked_until_import_is_fixed() {
    const USER: &str = "(import [mymod [val]])\n(defn g [] 1)\n";
    // Turns: 1 (val), 2–4 save, 5 (defn h), 6 snapshot, 7–9 save, 10 (val),
    // 11 (defn h).
    let out = Cranelisp::new()
        .file("mymod.cl", "(defn val [] 10)\n")
        .user(USER)
        .repl()
        .stdin(&format!(
            "(val)\n{}(defn h [] 2)\n/sh cp user.cl after-rejection.txt\n{}(val)\n(defn h [] 2)\n/quit\n",
            save("mymod.cl", "(defn val [] (primitives/add-i64 1 \"x\"))"),
            save("mymod.cl", "(defn val [] 20)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let after_rejection = out.read_tmp("after-rejection.txt");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 10"),
        "precondition: `(val)` gives 10 before the edit",
    );
    legs.check(
        !error_blocks(&out, "mymod.cl").is_empty(),
        "the type-error save fails: `[errors: mymod.cl]`",
    );
    legs.check(
        !turn(5).contains("user/h"),
        "the cascade-failed `user` rejects the definition turn",
    );
    legs.check(
        after_rejection == USER,
        "user.cl is byte-identical to its initial content after the rejected turn",
    );
    legs.check(
        save_notice(&t, 7).contains("[updated: mymod.cl]"),
        "the fixed save reloads: `[updated: mymod.cl]`",
    );
    legs.check(
        turn(10).contains(":primitives/Int 20"),
        "both modules reload: evaluation resumes with the fixed `val`",
    );
    legs.check(
        turn(11).contains("user/h"),
        "the released `user` accepts the definition",
    );
    legs.check(
        saved.contains("mymod")
            && saved.matches("(defn g [] 1)").count() == 1
            && saved.matches("(defn h [] 2)").count() == 1,
        "user.cl keeps the import and `g` and adds `h`",
    );
    legs.assert_all(&format!(
        "{}\nuser.cl after the rejected turn:\n{after_rejection}\nuser.cl at exit:\n{saved}",
        transcript(&out)
    ));
}

// spec: repl/spec/14-file-watching.md §14.2 — step 4, with the user's
// 2026-09-29 ruling: `user`, reaching `lib` only through the qualified call
// `(lib/h)` and no `import`, is a dependent of `lib`. A save of `lib.cl`
// omitting `h` fails it: `[errors: user.cl]`, and `(call)` does not give 2.
// §14.5 item 5 — the failed `user` rejects a definition and keeps `user.cl`
// byte-identical. §14.6 — restoring `h` releases it without a save of
// `user.cl`: `(call)` gives the new 5 and the definition is accepted. FQR-1;
// RM-2 and FL-3 are the same removal and lock reached through an `import`.
#[test]
fn watch_qualified_caller_fails_on_removed_callee_until_it_is_restored() {
    const USER: &str = "(defn call [] (lib/h))\n";
    // Turns: 1 (call), 2–4 save, 5 (defn k), 6 snapshot, 7 (call), 8–10 save,
    // 11 (call), 12 (defn k).
    let out = Cranelisp::new()
        .file("lib.cl", "(defn g [] 1)\n(defn h [] 2)\n")
        .user(USER)
        .repl()
        .stdin(&format!(
            "(call)\n{}(defn k [] 3)\n/sh cp user.cl after-rejection.txt\n(call)\n{}(call)\n(defn k [] 3)\n/quit\n",
            save("lib.cl", "(defn g [] 1)"),
            save("lib.cl", "(defn g [] 1) (defn h [] 5)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let after_rejection = out.read_tmp("after-rejection.txt");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 2"),
        "precondition: `(call)` gives 2 before the save",
    );
    legs.check(
        save_notice(&t, 2).contains("[updated: lib.cl]"),
        "the save omitting `h` reloads: `[updated: lib.cl]`",
    );
    legs.check(
        !error_blocks(&out, "user.cl").is_empty(),
        "the qualified caller reports `[errors: user.cl]`",
    );
    legs.check(
        !turn(5).contains("user/k"),
        "the failed `user` rejects the definition turn",
    );
    legs.check(
        after_rejection == USER,
        "user.cl is byte-identical to its initial content after the rejected turn",
    );
    legs.check(
        !turn(7).contains(":primitives/Int 2"),
        "`(call)` does not give 2 after the removal",
    );
    legs.check(
        save_notice(&t, 8).contains("[updated: lib.cl]"),
        "the save restoring `h` reloads: `[updated: lib.cl]`",
    );
    legs.check(
        turn(11).contains(":primitives/Int 5"),
        "the released `user` calls the restored `h`: `(call)` gives 5",
    );
    legs.check(
        turn(12).contains("user/k"),
        "the released `user` accepts the definition",
    );
    legs.check(
        saved.matches("(defn call [] (lib/h))").count() == 1
            && saved.matches("(defn k [] 3)").count() == 1,
        "user.cl holds `call` and `k` exactly once each",
    );
    legs.assert_all(&format!(
        "{}\nuser.cl after the rejected turn:\n{after_rejection}\nuser.cl at exit:\n{saved}",
        transcript(&out)
    ));
}

// spec: repl/spec/14-file-watching.md §14.5 item 5 — with the user's
// 2026-09-29 ruling: `user`, reaching `lib` only through the qualified type
// `:lib/T` and no `import`, is a dependent of `lib`, so a save of `lib.cl`
// that fails typecheck with `T` unchanged locks it: a definition is rejected
// and `user.cl` stays byte-identical. §14.2 step 4 and §14.6 — the compiling
// save recompiles `user` and releases it without a save of `user.cl`. FQR-2;
// FL-3 is the same failure reached through an `import`.
#[test]
fn watch_qualified_type_dependent_locked_until_its_module_compiles() {
    const USER: &str = "(defn f [:lib/T t] 7)\n";
    const T_AND_MK: &str = "(deftype T [:primitives/Int n]) (defn mk [] (T 7))";
    // Turns: 1 (f (lib/mk)), 2–4 save, 5 (defn k), 6 snapshot, 7–9 save,
    // 10 (f (lib/mk)), 11 (defn k).
    let out = Cranelisp::new()
        .file(
            "lib.cl",
            "(deftype T [:primitives/Int n])\n(defn mk [] (T 7))\n(defn ok [] 1)\n",
        )
        .user(USER)
        .repl()
        .stdin(&format!(
            "(f (lib/mk))\n{}(defn k [] 3)\n/sh cp user.cl after-rejection.txt\n{}(f (lib/mk))\n(defn k [] 3)\n/quit\n",
            save(
                "lib.cl",
                &format!("{T_AND_MK} (defn ok [] (primitives/add-i64 1 \"x\"))"),
            ),
            save("lib.cl", &format!("{T_AND_MK} (defn ok [] 2)"))
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let after_rejection = out.read_tmp("after-rejection.txt");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 7"),
        "precondition: `(f (lib/mk))` gives 7 before the save",
    );
    legs.check(
        !error_blocks(&out, "lib.cl").is_empty(),
        "the ill-typed save fails: `[errors: lib.cl]`",
    );
    legs.check(
        !turn(5).contains("user/k"),
        "the locked `user` rejects the definition turn",
    );
    legs.check(
        after_rejection == USER,
        "user.cl is byte-identical to its initial content after the rejected turn",
    );
    legs.check(
        save_notice(&t, 7).contains("[updated: lib.cl]"),
        "the compiling save reloads: `[updated: lib.cl]`",
    );
    legs.check(
        turn(10).contains(":primitives/Int 7"),
        "evaluation resumes: `(f (lib/mk))` gives 7",
    );
    legs.check(
        turn(11).contains("user/k"),
        "the released `user` accepts the definition",
    );
    legs.check(
        saved.matches("(defn f [:lib/T t] 7)").count() == 1
            && saved.matches("(defn k [] 3)").count() == 1,
        "user.cl holds `f` and `k` exactly once each",
    );
    legs.assert_all(&format!(
        "{}\nuser.cl after the rejected turn:\n{after_rejection}\nuser.cl at exit:\n{saved}",
        transcript(&out)
    ));
}

// spec: repl/spec/14-file-watching.md §14.6 — a restart does not bypass a
// failure: `lib.cl`, imported by `user.cl`, fails at startup, and `/mod lib`
// plus a definition leaves the failing `keep-me` source in `lib.cl`, whether
// the turn is rejected or the source retained. §14.5 item 5 — control: the
// same failing `lib.cl` produced by an in-session save locks the module, and
// the same turns keep the file. M1 (ACT-1010).
// The startup-failed dependency was not locked, so the turns regenerated
// `lib.cl` as `(defn z [] 1)` and the failing source was lost.
// defect: class=release-path-bypass locus=src/session_v4/lifecycle.rs::recover_startup_failure found=S122 owner=/dev fixed=S122/e4062202
#[test]
fn persist_mod_definition_keeps_dependency_source_failed_at_startup() {
    const USER: &str = "(import [lib [keep-me]])\n(defn g [] 1)\n";
    const FAILING: &str = "(defn keep-me [] (undefined-name 1))";
    const TURNS: &str = "/mod lib\n(defn z [] 1)\n/mod user\n/quit\n";

    let in_session = Cranelisp::new()
        .file("lib.cl", "(defn keep-me [] 42)\n")
        .user(USER)
        .repl()
        .stdin(&format!("(keep-me)\n{}{TURNS}", save("lib.cl", FAILING)))
        .output();
    let t = turns(&in_session.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let in_session_lib = in_session.read_tmp("lib.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 42"),
        "control precondition: `(keep-me)` gives 42 before the save",
    );
    legs.check(
        !error_blocks(&in_session, "lib.cl").is_empty(),
        "control: the in-session save fails: `[errors: lib.cl]`",
    );
    legs.check(
        in_session_lib.contains(FAILING),
        "control: after the in-session failure lib.cl keeps the failing source",
    );

    let startup = Cranelisp::new()
        .file("lib.cl", &format!("{FAILING}\n"))
        .user(USER)
        .repl()
        .stdin(TURNS)
        .output();
    let startup_lib = startup.read_tmp("lib.cl");
    legs.check(
        format!("{}{}", startup.stdout, startup.stderr).contains("[errors:"),
        "precondition: startup reports the load failure",
    );
    legs.check(
        startup_lib.contains(FAILING),
        "after the startup failure lib.cl keeps the failing source",
    );
    legs.assert_all(&format!(
        "--- in-session control ---\n{}\nlib.cl at exit:\n{in_session_lib}\n\
         --- startup failure ---\n{}\nlib.cl at exit:\n{startup_lib}",
        transcript(&in_session),
        transcript(&startup)
    ));
}

// =============================================================================
// §14.2 step 4, §14.6 — fixing a dependency recompiles its dependents, however
// the dependency came to fail
// =============================================================================

const CHAIN_BASE_FAILING: &str = "(defn b [] (undefined-name 1))";
const CHAIN_BASE_FIXED: &str = "(defn b [] 7)";

/// The import chain `user` → `lib` → `base`, in which `base.cl` fails and is
/// then fixed by a save. `failed_at_startup` selects whether `base.cl` fails
/// when the session loads it or through an earlier save in the session.
/// Returns the output and the turn of the `(f)` that follows the fix; the
/// `(f)` four turns earlier precedes the fix, the fix's save occupies the
/// three turns between, and `(defn k [] 3)` follows it.
fn chain_fixed_after_dependency_failure(failed_at_startup: bool) -> (e2e::CrOutput, usize) {
    let (initial_base, fail_in_session) = if failed_at_startup {
        (CHAIN_BASE_FAILING, String::new())
    } else {
        (
            CHAIN_BASE_FIXED,
            format!("(f)\n{}", save("base.cl", CHAIN_BASE_FAILING)),
        )
    };
    let out = Cranelisp::new()
        .file("base.cl", &format!("{initial_base}\n"))
        .file("lib.cl", "(import [base [b]])\n(defn f [] (b))\n")
        .user("(import [lib [f]])\n(defn g [] 1)\n")
        .repl()
        .stdin(&format!(
            "{fail_in_session}(f)\n{}(f)\n(defn k [] 3)\n/quit\n",
            save("base.cl", CHAIN_BASE_FIXED)
        ))
        .output();
    let after_fix = fail_in_session.lines().count() + 5;
    (out, after_fix)
}

/// The legs both chain cells share: `(f)` is refused while `base` fails, and
/// the fix recompiles `base` and both of its dependents, so `(f)` gives 7.
fn check_chain_released_by_fix(legs: &mut Legs, t: &[&str], after_fix: usize) {
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let notice = save_notice(t, after_fix - 3);
    legs.check(
        !turn(after_fix - 4).contains(":primitives/Int 7"),
        "precondition: `(f)` is refused while `base` fails",
    );
    legs.check(
        notice.contains("[updated: base.cl]"),
        "the fixing save reloads: `[updated: base.cl]`",
    );
    legs.check(
        notice.contains("[updated: lib.cl]") && notice.contains("[updated: user.cl]"),
        "the fix recompiles the dependents: `[updated: lib.cl]` and `[updated: user.cl]`",
    );
    legs.check(
        turn(after_fix).contains(":primitives/Int 7"),
        "the released dependents evaluate: `(f)` gives 7",
    );
}

// spec: repl/spec/14-file-watching.md §14.2 — step 4: `base.cl` fails when the
// session loads it, and the save that fixes it recompiles its importer `lib`
// and `lib`'s importer `user`, reporting `[updated:]` for all three files.
// §14.6 — the fix clears the dependents' errors, so `(f)` gives 7 without a
// save of `lib.cl` or `user.cl`. §15.2.3 — the recompiled `user` then accepts
// `(defn k [] 3)` and regenerates `user.cl` with its import once: a release
// without the rebuild would keep the import retained from the startup failure
// and write it twice. ACT-1011; the control
// `watch_fix_of_dependency_failed_in_session_recompiles_its_dependents_control`
// differs only in when `base.cl` failed.
// DEFECT (open): the fix reports only `[updated: base.cl]`; `lib` and `user`
// are not recompiled and `(f)` stays refused as their modules have errors.
// defect: class=enumeration-miss locus=src/session_v4/lifecycle.rs::recover_startup_failure found=S122 owner=/dev — provisional: at e4062202 the reload plan's edge graph (src/session_v4/lifecycle.rs::reload_edge_graph) holds no edge for a module that failed at startup
#[test]
fn watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents() {
    let (out, after_fix) = chain_fixed_after_dependency_failure(true);
    let t = turns(&out.stdout);
    let mut legs = Legs::default();
    legs.check(
        t.first()
            .is_some_and(|startup| startup.contains("[errors:")),
        "precondition: startup reports the load failure",
    );
    check_chain_released_by_fix(&mut legs, &t, after_fix);
    let saved = out.read_tmp("user.cl");
    legs.check(
        t.get(after_fix + 1)
            .is_some_and(|turn| turn.contains("user/k")),
        "the released `user` accepts `(defn k [] 3)`",
    );
    legs.check(
        saved.matches("(import [lib [f]])").count() == 1,
        "user.cl holds `(import [lib [f]])` exactly once",
    );
    legs.assert_all(&format!("{}\nuser.cl at exit:\n{saved}", transcript(&out)));
}

// spec: repl/spec/14-file-watching.md §14.2 — step 4: `base.cl` compiles at
// startup and fails through a save, and the save that fixes it recompiles
// `lib` and `user`. §14.6 — the fix clears their errors and `(f)` gives 7.
// ACT-1011's control for
// `watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents`.
#[test]
fn watch_fix_of_dependency_failed_in_session_recompiles_its_dependents_control() {
    let (out, after_fix) = chain_fixed_after_dependency_failure(false);
    let t = turns(&out.stdout);
    let mut legs = Legs::default();
    legs.check(
        t.get(1)
            .is_some_and(|turn| turn.contains(":primitives/Int 7")),
        "precondition: `(f)` gives 7 before `base.cl` fails",
    );
    legs.check(
        !error_blocks(&out, "base.cl").is_empty(),
        "precondition: the failing save reports `[errors: base.cl]`",
    );
    check_chain_released_by_fix(&mut legs, &t, after_fix);
    legs.assert_all(&transcript(&out));
}

// spec: repl/spec/14-file-watching.md §14.2 — step 4: a save of `user.cl`
// adds `(import [c [x]])` while `c.cl` fails, so `user` fails through it; the
// save that fixes `c.cl` recompiles `user`, reporting `[updated: user.cl]`.
// §14.6 — the fix clears `user`'s error: `(g)` gives 9 and `(defn k [] 2)` is
// accepted, and the regenerated `user.cl` holds the import exactly once.
// ACT-1011.
// At e4062202 the fix reported only `[updated: c.cl]`, and `user` stayed
// refused as a module with errors.
// defect: class=enumeration-miss locus=src/session_v4/lifecycle.rs::reload_edge_graph found=S122 owner=/dev
#[test]
fn watch_fix_of_module_newly_imported_by_failing_save_recompiles_importer() {
    // Turns: 1 `(g)`, 2–4 save of user.cl, 5 `(g)`, 6–8 save of c.cl,
    // 9 `(g)`, 10 `(defn k [] 2)`.
    let out = Cranelisp::new()
        .file("c.cl", "(defn x [] (nope))\n")
        .user("(defn g [] 1)\n")
        .repl()
        .stdin(&format!(
            "(g)\n{}(g)\n{}(g)\n(defn k [] 2)\n/quit\n",
            save("user.cl", "(import [c [x]]) (defn g [] (x))"),
            save("c.cl", "(defn x [] 9)")
        ))
        .output();
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let notice = save_notice(&t, 6);
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 1"),
        "precondition: `(g)` gives 1 before the saves",
    );
    legs.check(
        !error_blocks(&out, "user.cl").is_empty() && !turn(5).contains(":primitives/Int"),
        "precondition: the save of user.cl fails through `c`, and `(g)` is refused",
    );
    legs.check(
        notice.contains("[updated: c.cl]") && notice.contains("[updated: user.cl]"),
        "the fix of c.cl reports `[updated: c.cl]` and `[updated: user.cl]`",
    );
    legs.check(turn(9).contains(":primitives/Int 9"), "`(g)` gives 9");
    legs.check(turn(10).contains("user/k"), "`(defn k [] 2)` is accepted");
    legs.check(
        saved.matches("(import [c [x]])").count() == 1,
        "user.cl at exit holds `(import [c [x]])` exactly once",
    );
    legs.assert_all(&format!("{}\nuser.cl at exit:\n{saved}", transcript(&out)));
}

/// `lib.cl` (`lib_source`) fails at startup in its own source against
/// `base.cl` (`base_before`); `user` imports `f` from `lib`. A save of
/// `base.cl` as `base_after` removes the failure. Turns: 1 `(g)`, 2–4 save,
/// 5 `(g)`, 6 `(lib/f)`.
fn own_source_failure_then_dependency_save(
    base_before: &str,
    lib_source: &str,
    base_after: &str,
) -> e2e::CrOutput {
    Cranelisp::new()
        .file("base.cl", &format!("{base_before}\n"))
        .file("lib.cl", &format!("{lib_source}\n"))
        .user("(import [lib [f]])\n(defn g [] (f))\n")
        .repl()
        .stdin(&format!(
            "(g)\n{}(g)\n(lib/f)\n/quit\n",
            save("base.cl", base_after)
        ))
        .output()
}

/// `base`'s `b` takes one parameter, which `lib` omits; the save drops it.
const ONE_PARAMETER_B: &str = "(defn b [x] x)";
const NULLARY_B: &str = "(defn b [] 7)";

/// The legs every own-source twin shares: startup reports `lib`'s failure,
/// whose text contains `startup_fault`, and the save of `base.cl` recompiles
/// `lib` and `user`, which then evaluate.
fn own_source_failure_released_legs(out: &e2e::CrOutput, startup_fault: &str) -> Legs {
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let notice = save_notice(&t, 2);
    let mut legs = Legs::default();
    legs.check(
        t.first()
            .is_some_and(|startup| startup.contains("[errors:") && startup.contains(startup_fault)),
        "precondition: startup reports `lib`'s own-source failure",
    );
    legs.check(
        !turn(1).contains(":primitives/Int"),
        "precondition: `(g)` is refused before the save",
    );
    legs.check(
        notice.contains("[updated: base.cl]"),
        "precondition: the save reloads: `[updated: base.cl]`",
    );
    legs.check(
        notice.contains("[updated: lib.cl]") && notice.contains("[updated: user.cl]"),
        "the save recompiles the dependents: `[updated: lib.cl]` and `[updated: user.cl]`",
    );
    legs.check(turn(5).contains(":primitives/Int 7"), "`(g)` gives 7");
    legs.check(turn(6).contains(":primitives/Int 7"), "`(lib/f)` gives 7");
    legs
}

fn assert_own_source_failure_released_by_dependency_save(out: &e2e::CrOutput) {
    own_source_failure_released_legs(out, "arity").assert_all(&transcript(out));
}

// spec: repl/spec/14-file-watching.md §14.2 — step 4: `lib.cl` fails at
// startup in its own source against `base`, which it imports; a save of
// `base.cl` that makes the call type-correct recompiles `lib` and its importer
// `user`, and `(g)` and `(lib/f)` give 7. ACT-1011; the twin
// `watch_dependency_save_recompiles_qualified_caller_failed_at_startup_in_own_source`
// reaches `base` by a qualified reference. The sibling
// `watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents` has
// the dependency itself fail.
// DEFECT (open): the save reports only `[updated: base.cl]`, and `lib` and
// `user` stay refused as modules with errors.
// defect: class=enumeration-miss locus=src/session_v4/lifecycle.rs::recover_startup_failure found=S122 owner=/dev — provisional: the startup purge drops the attempt's `import` edges, and an own-source failure records no failure dependency
#[test]
fn watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source() {
    assert_own_source_failure_released_by_dependency_save(
        &own_source_failure_then_dependency_save(
            ONE_PARAMETER_B,
            "(import [base [b]])\n(defn f [] (b))",
            NULLARY_B,
        ),
    );
}

// spec: repl/spec/14-file-watching.md §14.2 — step 4: as the `import` twin
// `watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source`,
// with `lib` reaching `base` only by the qualified reference `(base/b)`.
// ACT-1011.
// DEFECT (open): the save reports only `[updated: base.cl]`, and `lib` and
// `user` stay refused as modules with errors.
// defect: class=enumeration-miss locus=src/session_v4/lifecycle.rs::recover_startup_failure found=S122 owner=/dev — provisional: an own-source failure records no failure dependency
#[test]
fn watch_dependency_save_recompiles_qualified_caller_failed_at_startup_in_own_source() {
    assert_own_source_failure_released_by_dependency_save(
        &own_source_failure_then_dependency_save(
            ONE_PARAMETER_B,
            "(defn f [] (base/b))",
            NULLARY_B,
        ),
    );
}

// spec: repl/spec/14-file-watching.md §14.2 — step 4, and §14.6: `lib.cl`
// holds `(import [base [c]])` while `base.cl` lacks `c`, so `lib` fails at
// startup resolving its own imports (Pass 0). A save of `base.cl` adding `c`
// recompiles `lib` and then its importer `user`, and `(g)` and `(lib/f)` give
// 7. ACT-1011; the Pass-0 sibling of
// `watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source`.
// DEFECT (open): the save reports only `[updated: base.cl]`, and `lib` and
// `user` stay refused as modules with errors.
// defect: class=enumeration-miss locus=src/session_v4/lifecycle.rs::recover_startup_failure found=S122 owner=/dev — provisional: an own-source failure before the type pass records no failure dependency
#[test]
fn watch_dependency_save_recompiles_importer_failed_at_startup_resolving_import() {
    let out = own_source_failure_then_dependency_save(
        NULLARY_B,
        "(import [base [c]])\n(defn f [] (c))",
        "(defn b [] 7) (defn c [] 7)",
    );
    let mut legs = own_source_failure_released_legs(&out, "'c'");
    let notice = save_notice(&turns(&out.stdout), 2);
    legs.check(
        notice
            .find("[updated: lib.cl]")
            .zip(notice.find("[updated: user.cl]"))
            .is_some_and(|(lib, user)| lib < user),
        "`lib` is recompiled before `user`",
    );
    legs.assert_all(&transcript(&out));
}

// =============================================================================
// §15.2.3 — a dependency's change recompiles a startup-degraded entry, and a
// failure of that recompilation locks it
// =============================================================================

/// `user.cl` imports `f` from `lib.cl`, and its `bad` fails at startup.
const DEGRADED_ENTRY: &str = "(import [lib [f]])\n(defn ok [] (f))\n(defn bad [] (nope))\n";

fn degraded_entry_session(stdin: &str) -> e2e::CrOutput {
    Cranelisp::new()
        .file("lib.cl", "(defn f [] 1)\n")
        .user(DEGRADED_ENTRY)
        .repl()
        .stdin(stdin)
        .output()
}

// spec: repl/spec/15-session-persistence.md §15.2.3 — `user.cl` fails at
// startup, and a changed save of its import `lib.cl` recompiles it as a
// dependent (repl/spec/14-file-watching.md §14.2 step 4). That recompilation
// fails, so `user` is locked (§14.5 item 5): the at-prompt repair
// `(defn bad [] 1)` is refused and `user.cl` is unchanged. A compiling save of
// `user.cl` releases it (§14.6), `(ok)` gives the new 2, and a later definition
// regenerates `user.cl` without the startup-failed `(nope)`. R1; the control
// `persist_startup_degraded_entry_repairs_at_prompt_without_dependency_change_control`
// differs only in the save of `lib.cl`.
#[test]
fn persist_dependency_change_locks_startup_degraded_entry_until_its_save_compiles() {
    // Turns: 1 (ok), 2–4 save of lib.cl, 5 (defn bad), 6 snapshot,
    // 7–9 save of user.cl, 10 (ok), 11 (defn k).
    let out = degraded_entry_session(&format!(
        "(ok)\n{}(defn bad [] 1)\n/sh cp user.cl after-rejection.txt\n{}(ok)\n(defn k [] 4)\n/quit\n",
        save("lib.cl", "(defn f [] 2)"),
        save(
            "user.cl",
            "(import [lib [f]]) (defn ok [] (f)) (defn bad [] 3)"
        )
    ));
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let lib_notice = save_notice(&t, 2);
    let after_rejection = out.read_tmp("after-rejection.txt");
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        t.first()
            .is_some_and(|startup| startup.contains("[errors: user.cl]")),
        "precondition: startup reports `[errors: user.cl]`",
    );
    legs.check(
        !turn(1).contains(":primitives/Int"),
        "precondition: `(ok)` is refused while `user` fails",
    );
    legs.check(
        lib_notice.contains("[updated: lib.cl]") && lib_notice.contains("[errors: user.cl]"),
        "the save of lib.cl reports `[updated: lib.cl]` and `[errors: user.cl]`",
    );
    legs.check(
        !turn(5).contains("user/bad"),
        "the locked `user` refuses `(defn bad [] 1)`",
    );
    legs.check(
        after_rejection == DEGRADED_ENTRY,
        "user.cl is byte-identical to its initial content after the refused turn",
    );
    legs.check(
        save_notice(&t, 7).contains("[updated: user.cl]"),
        "the compiling save of user.cl reports `[updated: user.cl]`",
    );
    legs.check(
        turn(10).contains(":primitives/Int 2"),
        "the released `user` evaluates: `(ok)` gives 2",
    );
    legs.check(turn(11).contains("user/k"), "`(defn k [] 4)` is accepted");
    legs.check(
        !saved.contains("(nope)"),
        "the regenerated user.cl does not write back the startup-failed `(nope)`",
    );
    legs.assert_all(&format!(
        "{}\nuser.cl after the refused turn:\n{after_rejection}\nuser.cl at exit:\n{saved}",
        transcript(&out)
    ));
}

// spec: repl/spec/15-session-persistence.md §15.2.3 — with no recompilation,
// the startup-degraded `user` accepts the at-prompt repair `(defn bad [] 1)`,
// and the regenerated `user.cl` holds it in place of the failed `(nope)`. R1's
// control for
// `persist_dependency_change_locks_startup_degraded_entry_until_its_save_compiles`.
#[test]
fn persist_startup_degraded_entry_repairs_at_prompt_without_dependency_change_control() {
    let out = degraded_entry_session("(ok)\n(defn bad [] 1)\n/quit\n");
    let t = turns(&out.stdout);
    let saved = out.read_tmp("user.cl");
    let mut legs = Legs::default();
    legs.check(
        t.first()
            .is_some_and(|startup| startup.contains("[errors: user.cl]")),
        "precondition: startup reports `[errors: user.cl]`",
    );
    legs.check(
        t.get(2).is_some_and(|turn| turn.contains("user/bad")),
        "the degraded `user` accepts `(defn bad [] 1)`",
    );
    legs.check(
        saved.contains("(defn bad [] 1)") && !saved.contains("(nope)"),
        "user.cl holds `(defn bad [] 1)` and not `(nope)`",
    );
    legs.assert_all(&format!("{}\nuser.cl at exit:\n{saved}", transcript(&out)));
}

// =============================================================================
// spec §8.5.4 edge 6 — a reload that closes a qualified-reference cycle
// =============================================================================

/// `user` calls `b/g`, which calls `a/f`; `a.cl` is then saved with `f` giving
/// 5 and a new `(defn h [] <h_body>)`. Turns: 1 `(run)`, 2–4 save, 5 `(a/h)`,
/// 6 `(run)`.
fn qualified_chain_after_save_of_a(h_body: &str) -> e2e::CrOutput {
    Cranelisp::new()
        .file("a.cl", "(defn f [] 1)\n")
        .file("b.cl", "(defn g [] (a/f))\n")
        .user("(defn run [] (b/g))\n")
        .repl()
        .stdin(&format!(
            "(run)\n{}(a/h)\n(run)\n/quit\n",
            save("a.cl", &format!("(defn h [] {h_body}) (defn f [] 5)"))
        ))
        .output()
}

// spec: spec/08-modules.md §8.5.4 — edge 6: a qualified reference that closes
// a module dependency cycle MUST be reported as a circular-dependency error,
// at parity with `import` cycles (§8.10.2). A save of `a.cl` adding
// `(defn h [] (b/g))`, while `b` calls `a/f`, closes the cycle `a → b → a`, so
// the reload reports an error naming the cycle and the cyclic `h` is not
// installed. repl/spec/14-file-watching.md §14.2, §14.4. ACT-1013; the control
// `watch_save_adding_acyclic_qualified_call_reloads_control` differs only in
// `h`'s body.
// DEFECT (open): the save is accepted with `[updated:]` for all three files,
// with no error, and `(a/h)` gives 5.
// defect: class=silent-accept locus=src/session_v4/lifecycle.rs::run_reload_plan found=S122 owner=/dev — provisional: cycle detection runs only while a module loads (review A2)
#[test]
fn watch_save_closing_qualified_module_cycle_reports_circular_dependency() {
    let out = qualified_chain_after_save_of_a("(b/g)");
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let names_cycle = ["a.cl", "b.cl", "user.cl"]
        .iter()
        .flat_map(|file| error_blocks(&out, file))
        .any(|block| {
            let block = block.to_lowercase();
            block.contains("circular") || block.contains("cycle")
        });
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 1"),
        "precondition: `(run)` gives 1 before the save",
    );
    legs.check(
        names_cycle,
        "the save reports an `[errors:` block naming a circular dependency",
    );
    legs.check(
        !turn(5).contains(":primitives/Int 5"),
        "the cyclic `h` is not installed: `(a/h)` does not give 5",
    );
    legs.assert_all(&transcript(&out));
}

// spec: spec/08-modules.md §8.5.4 — a save of `a.cl` adding `(defn h [] 2)`
// closes no cycle, so it reloads with `[updated: a.cl]` and no error, `(a/h)`
// gives 2, and `user`'s qualified chain gives the new 5. repl/spec/14-file-watching.md
// §14.2. ACT-1013's control for
// `watch_save_closing_qualified_module_cycle_reports_circular_dependency`.
#[test]
fn watch_save_adding_acyclic_qualified_call_reloads_control() {
    let out = qualified_chain_after_save_of_a("2");
    let t = turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 1"),
        "precondition: `(run)` gives 1 before the save",
    );
    legs.check(
        save_notice(&t, 2).contains("[updated: a.cl]")
            && !format!("{}{}", out.stdout, out.stderr).contains("[errors:"),
        "the save reloads: `[updated: a.cl]` and no `[errors:`",
    );
    legs.check(turn(5).contains(":primitives/Int 2"), "`(a/h)` gives 2");
    legs.check(
        turn(6).contains(":primitives/Int 5"),
        "`(run)` gives the new 5",
    );
    legs.assert_all(&transcript(&out));
}

/// Piped-REPL stdout split at each prompt, whatever module it names: index 0
/// is startup output, index N is the response to the Nth input turn. A prompt
/// reads `<elapsed>ms; <module>> `.
fn prompted_turns(stdout: &str) -> Vec<&str> {
    regex::Regex::new(r"\d+\+\d+ms; [a-zA-Z][a-zA-Z0-9._-]*> ")
        .unwrap()
        .split(stdout)
        .collect()
}

/// `user` calls `b/g`, which calls `a/f`, and a REPL turn in `a` enters
/// `definition`. Turns: 1 `(run)`, 2 `/mod a`, 3 `definition`, then `rest`.
fn turn_in_a_while_b_calls_a(b_source: &str, definition: &str, rest: &str) -> e2e::CrOutput {
    Cranelisp::new()
        .file("a.cl", "(defn f [] 1)\n")
        .file("b.cl", &format!("{b_source}\n"))
        .user("(defn run [] (b/g))\n")
        .repl()
        .stdin(&format!("(run)\n/mod a\n{definition}\n{rest}/quit\n"))
        .output()
}

// spec: spec/08-modules.md §8.5.4 — edge 6: a REPL definition turn in `a`
// adding `(defn h [] (b/g))`, while `b` calls `a/f`, closes the cycle
// `a → b → a` and is refused naming it. The refused `h` is not installed:
// `a` accepts `(defn k [] 2)`, `user`'s chain still gives 1, and
// repl/spec/15-session-persistence.md §15.1 regenerates `a.cl` with `k` and
// without `h`. ACT-1013.
// At e4062202 the turn was accepted as `a/h` and written to `a.cl`.
// defect: class=silent-accept locus=src/worker.rs::prepare_cluster_commit_with_demands found=S122 owner=/dev
#[test]
fn repl_definition_closing_qualified_module_cycle_refused_and_not_written() {
    // Turns: 4 `(defn k [] 2)`, 5 `/mod user`, 6 `(run)`.
    let out = turn_in_a_while_b_calls_a(
        "(defn g [] (a/f))",
        "(defn h [] (b/g))",
        "(defn k [] 2)\n/mod user\n(run)\n",
    );
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("a.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 1"),
        "precondition: `(run)` gives 1",
    );
    legs.check(
        turn(3).contains("a -> b -> a") && !turn(3).contains("a/h"),
        "the `(defn h [] (b/g))` turn is refused naming `a -> b -> a`",
    );
    legs.check(turn(4).contains("a/k"), "`(defn k [] 2)` is accepted");
    legs.check(
        turn(6).contains(":primitives/Int 1"),
        "`(run)` in `user` still gives 1",
    );
    legs.check(
        saved.contains("(defn k [] 2)") && !saved.contains("(defn h"),
        "a.cl at exit holds `k` and not `h`",
    );
    legs.assert_all(&format!("{}\na.cl at exit:\n{saved}", transcript(&out)));
}

/// The `defmacro` turn whose clause calls `b/g`; its expansion is the literal 1.
const MACRO_CALLING_B: &str = "(defmacro m [] (let [v (b/g)] `1))";

/// Turns after `MACRO_CALLING_B`: 4 `(m)`, 5 `(defn k [] 2)`.
const AFTER_MACRO: &str = "(m)\n(defn k [] 2)\n";

// spec: spec/08-modules.md §8.5.4 — edge 6: a REPL `defmacro` turn in `a`
// whose clause calls `b/g`, while `b` calls `a/f`, closes the cycle
// `a → b → a` as a definition's body does, so it is refused naming the cycle
// and not written to `a.cl`; `a` then accepts `(defn k [] 2)`. ACT-1013; the
// control `repl_defmacro_clause_calling_acyclic_qualified_dependency_accepted_control`
// differs only in `b`.
// DEFECT (open): the `defmacro` turn is accepted and written to `a.cl`; `(m)`
// and `(defn k [] 2)` are then refused as the cycle `a -> b -> a`.
// defect: class=silent-accept locus=src/process_form/macro_clause.rs::compile_macro_checkpoint found=S122 owner=/dev — provisional: a clause published at its checkpoint is not cycle-checked
#[test]
fn repl_defmacro_clause_closing_qualified_module_cycle_refused_and_not_written() {
    let out = turn_in_a_while_b_calls_a("(defn g [] (a/f))", MACRO_CALLING_B, AFTER_MACRO);
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("a.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 1"),
        "precondition: `(run)` gives 1",
    );
    legs.check(
        turn(3).contains("a -> b -> a") && !turn(3).contains("a/m"),
        "the `defmacro` turn is refused naming `a -> b -> a`",
    );
    legs.check(turn(5).contains("a/k"), "`(defn k [] 2)` is accepted");
    legs.check(
        !saved.contains("(defmacro m"),
        "a.cl at exit has no `defmacro m`",
    );
    legs.assert_all(&format!("{}\na.cl at exit:\n{saved}", transcript(&out)));
}

// spec: spec/08-modules.md §8.5.4 — a `defmacro` turn in `a` whose clause
// calls `b/g`, while `b` does not reach `a`, closes no cycle: it is accepted,
// `(m)` gives 1 and `(defn k [] 2)` is accepted. ACT-1013's control for
// `repl_defmacro_clause_closing_qualified_module_cycle_refused_and_not_written`.
#[test]
fn repl_defmacro_clause_calling_acyclic_qualified_dependency_accepted_control() {
    let out = turn_in_a_while_b_calls_a("(defn g [] 3)", MACRO_CALLING_B, AFTER_MACRO);
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 3"),
        "precondition: `(run)` gives 3",
    );
    legs.check(turn(3).contains("a/m"), "the `defmacro` turn is accepted");
    legs.check(turn(4).contains(":primitives/Int 1"), "`(m)` gives 1");
    legs.check(turn(5).contains("a/k"), "`(defn k [] 2)` is accepted");
    legs.assert_all(&transcript(&out));
}

// =============================================================================
// ACT-1014 — a prelude save that imports a prelude-dependent module agrees
// with a restart on the saved files
// =============================================================================

/// The outcome of evaluating `(x/get (P 4))`, as the parity cell compares it.
fn get_p4_outcome(response: &str) -> &'static str {
    if response.contains(":primitives/Int 4") {
        "gives 4"
    } else if !response.contains(":primitives/Int")
        && (response.contains("Error") || response.contains("Cannot evaluate"))
    {
        "refused"
    } else {
        "other"
    }
}

// spec: spec/08-modules.md §8.8.2 — `x` uses the prelude's type `P` through
// the implicit import (§8.8.1), and a save of `prelude.cl` adds
// `(import [x [one]])`. A session and a restart on the saved files MUST agree
// (root CLAUDE.md: a REPL/restart divergence is a defect): `(x/get (P 4))`
// gives 4 in both or is refused in both. The cell takes no position on which,
// pending the §8.8.1/§8.10.2 ruling ACT-1014 carries.
// DEFECT (open): the session gives 4; the restart refuses, with `prelude`
// failing on `dependency 'x' failed: … unknown type P`.
// defect: class=mode-divergence locus=src/session_v4/lifecycle.rs::reload_plan found=S122 owner=/dev — unattributed
#[test]
fn prelude_save_importing_prelude_dependent_module_agrees_with_restart() {
    const GET_P4: &str = "(x/get (P 4))";
    // Turns: 1 `(x/one)`, 2–4 save of prelude.cl, 5 `GET_P4`.
    let session = Cranelisp::new()
        .prelude("(export [primitives [*]])\n(deftype P [:Int n])\n")
        .file("x.cl", "(defn get [:P p] (P.n p))\n(defn one [] 1)\n")
        .user("(defn u [] 1)\n")
        .repl()
        .stdin(&format!(
            "(x/one)\n{}{GET_P4}\n/quit\n",
            save(
                "prelude.cl",
                "(export [primitives [*]]) (import [x [one]]) (deftype P [:Int n])"
            )
        ))
        .output();
    let session_transcript = transcript(&session);
    let t = turns(&session.stdout);
    let precondition = t
        .get(1)
        .is_some_and(|turn| turn.contains(":primitives/Int 1"));
    let in_session = get_p4_outcome(t.get(5).copied().unwrap_or(""));

    let restart = session
        .run_again()
        .repl()
        .cli_flag("--no-cache")
        .stdin(&format!("{GET_P4}\n/quit\n"))
        .output();
    let after_restart = get_p4_outcome(turns(&restart.stdout).get(1).copied().unwrap_or(""));
    let mut legs = Legs::default();
    legs.check(
        precondition,
        "precondition: `(x/one)` gives 1 before the save",
    );
    legs.check(
        in_session != "other" && after_restart != "other",
        "each `(x/get (P 4))` gives 4 or is refused",
    );
    legs.check(
        in_session == after_restart,
        "the session and the restart agree on `(x/get (P 4))`",
    );
    legs.assert_all(&format!(
        "session: {in_session}; restart: {after_restart}\n\
         --- session ---\n{session_transcript}\n--- restart ---\n{}",
        transcript(&restart)
    ));
}

// =============================================================================
// ACT-1014 — the implicit prelude import is a dependency at reload and at a
// REPL turn (spec §8.8.1, PD-2 and PD-3)
// =============================================================================

/// A session whose prelude does not yet import `x`, and whose `x.cl` gives
/// `(x/one)` 3, carrying the null import (§8.3.7) when `opt_out`. Turn 1 is
/// `(x/one)`.
fn prelude_not_yet_importing_x(opt_out: bool, turns_after_first: &str) -> e2e::CrOutput {
    let opt_out_line = if opt_out {
        "(import [prelude []])\n"
    } else {
        ""
    };
    Cranelisp::new()
        .prelude("(export [primitives [*]])\n")
        .file("x.cl", &format!("{opt_out_line}(defn one [] 3)\n"))
        .user("")
        .repl()
        .stdin(&format!("(x/one)\n{turns_after_first}/quit\n"))
        .output()
}

/// Turns 2–4 save `prelude.cl` with `(import [x [one]])`; turn 5 is `(x/one)`.
fn save_prelude_importing_x(opt_out: bool) -> e2e::CrOutput {
    let saved = save("prelude.cl", "(export [primitives [*]]) (import [x [one]])");
    prelude_not_yet_importing_x(opt_out, &format!("{saved}(x/one)\n"))
}

/// Turns 2 `/mod prelude`, 3 `(import [x [one]])`, 4 `/mod user`, 5 `(x/one)`.
fn mod_prelude_import_of_x(opt_out: bool) -> e2e::CrOutput {
    prelude_not_yet_importing_x(
        opt_out,
        "/mod prelude\n(import [x [one]])\n/mod user\n(x/one)\n",
    )
}

/// A restart on the session's saved files, with `(x/one)` as turn 1.
fn restart_evaluating_x_one(session: e2e::CrOutput) -> e2e::CrOutput {
    session
        .run_again()
        .repl()
        .cli_flag("--no-cache")
        .stdin("(x/one)\n/quit\n")
        .output()
}

/// Whether some line of `text` reports a circular dependency naming both
/// `prelude` and `x` as whole words.
fn names_prelude_x_cycle(text: &str) -> bool {
    text.lines().any(|line| {
        let words: Vec<&str> = line
            .split(|c: char| !(c.is_alphanumeric() || c == '-' || c == '_'))
            .collect();
        line.to_lowercase().contains("circular")
            && words.contains(&"prelude")
            && words.contains(&"x")
    })
}

// spec: spec/08-modules.md §8.8.1 and §8.10.2 — a save of `prelude.cl` adding
// `(import [x [one]])`, where `x.cl` does not reference `prelude`, closes
// `prelude -> x -> prelude` through `x`'s implicit prelude import. The reload
// MUST refuse the save naming the cycle, and a restart on the saved files MUST
// report the same cycle (REPL/restart parity, root CLAUDE.md).
#[test]
fn prelude_save_importing_module_without_opt_out_neg_refused_as_cycle_like_restart() {
    let session = save_prelude_importing_x(false);
    let session_transcript = transcript(&session);
    let mut legs = Legs::default();
    {
        let t = prompted_turns(&session.stdout);
        let notice = save_notice(&t, 2);
        legs.check(
            t.get(1)
                .is_some_and(|turn| turn.contains(":primitives/Int 3")),
            "precondition: `(x/one)` gives 3 before the save",
        );
        legs.check(
            notice.contains("[errors:") && names_prelude_x_cycle(&notice),
            "the save is refused naming the cycle of `prelude` and `x`",
        );
        legs.check(
            !notice.contains("[updated: prelude.cl]"),
            "the save does not report `[updated: prelude.cl]`",
        );
    }
    let restart = restart_evaluating_x_one(session);
    legs.check(
        names_prelude_x_cycle(&format!("{}\n{}", restart.stdout, restart.stderr)),
        "a restart on the saved files reports the same cycle",
    );
    legs.assert_all(&format!(
        "--- session ---\n{session_transcript}\n--- restart ---\n{}",
        transcript(&restart)
    ));
}

// spec: spec/08-modules.md §8.8.1 and §8.3.7 — control: the same save when
// `x.cl` carries `(import [prelude []])`. The null import loads nothing, so no
// cycle forms: the save reports `[updated: prelude.cl]`, `(x/one)` gives 3
// after it, and a restart on the saved files agrees.
// DEFECT (open): the save reports `[errors: prelude.cl] … 'one' not found in
// module 'x'` and evaluation is blocked; the restart gives 3. The twin without
// the null import reloads, and the pre-S122 build reloads both.
// defect: class=enumeration-miss locus=src/cache/dependency_record.rs::reload_edges found=S122 owner=/dev — provisional: the null import is read as the edge `x -> prelude`
#[test]
fn prelude_save_importing_opted_out_module_reloads_like_restart_control() {
    let session = save_prelude_importing_x(true);
    let session_transcript = transcript(&session);
    let mut legs = Legs::default();
    {
        let t = prompted_turns(&session.stdout);
        let notice = save_notice(&t, 2);
        legs.check(
            t.get(1)
                .is_some_and(|turn| turn.contains(":primitives/Int 3")),
            "precondition: `(x/one)` gives 3 before the save",
        );
        legs.check(
            notice.contains("[updated: prelude.cl]") && !notice.contains("[errors:"),
            "the save reports `[updated: prelude.cl]` and no errors",
        );
        legs.check(
            t.get(5)
                .is_some_and(|turn| turn.contains(":primitives/Int 3")),
            "`(x/one)` gives 3 after the save",
        );
    }
    let restart = restart_evaluating_x_one(session);
    legs.check(
        prompted_turns(&restart.stdout)
            .get(1)
            .is_some_and(|turn| turn.contains(":primitives/Int 3")),
        "a restart on the saved files gives 3",
    );
    legs.assert_all(&format!(
        "--- session ---\n{session_transcript}\n--- restart ---\n{}",
        transcript(&restart)
    ));
}

// spec: spec/08-modules.md §8.8.1 and §8.10.2 — a REPL turn in `prelude`
// entering `(import [x [one]])`, where `x.cl` does not reference `prelude`,
// closes `prelude -> x -> prelude`. The turn MUST be refused naming the cycle
// and not written to `prelude.cl`; `(x/one)` in `user` still gives 3.
#[test]
fn mod_prelude_import_of_module_without_opt_out_neg_refused_as_cycle() {
    let out = mod_prelude_import_of_x(false);
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("prelude.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 3"),
        "precondition: `(x/one)` gives 3",
    );
    legs.check(
        names_prelude_x_cycle(turn(3)),
        "the import turn is refused naming the cycle of `prelude` and `x`",
    );
    legs.check(
        !saved.contains("[x ["),
        "prelude.cl at exit has no import of `x`",
    );
    legs.check(
        turn(5).contains(":primitives/Int 3"),
        "`(x/one)` in `user` still gives 3",
    );
    legs.assert_all(&format!(
        "{}\nprelude.cl at exit:\n{saved}",
        transcript(&out)
    ));
}

// spec: spec/08-modules.md §8.8.1 and §8.3.7 — control: the same turn when
// `x.cl` carries `(import [prelude []])`. No cycle forms, so the turn is
// accepted and written to `prelude.cl` once, and `(x/one)` in `user` gives 3.
#[test]
fn mod_prelude_import_of_opted_out_module_accepted_and_written_once_control() {
    let out = mod_prelude_import_of_x(true);
    let t = prompted_turns(&out.stdout);
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let saved = out.read_tmp("prelude.cl");
    let mut legs = Legs::default();
    legs.check(
        turn(1).contains(":primitives/Int 3"),
        "precondition: `(x/one)` gives 3",
    );
    legs.check(
        !turn(3).to_lowercase().contains("error") && !turn(3).contains("circular"),
        "the import turn is accepted",
    );
    legs.check(
        saved.matches("(import [x [one]])").count() == 1,
        "prelude.cl at exit holds `(import [x [one]])` once",
    );
    legs.check(
        turn(5).contains(":primitives/Int 3"),
        "`(x/one)` in `user` gives 3",
    );
    legs.assert_all(&format!(
        "{}\nprelude.cl at exit:\n{saved}",
        transcript(&out)
    ));
}

// =============================================================================
// ACT-1014 — prelude reach to `x` by `export` or a qualified reference closes
// the implicit-import cycle at reload and at a restart (spec §8.8.1, PD-4 and
// PD-5)
// =============================================================================

/// A session whose prelude defines `P` and does not reach `x`, and whose `user`
/// calls `x/one` (3). Without `opt_out`, `x.cl` uses `P` bare; with it, `x.cl`
/// carries the null import (§8.3.7) and does not use `P`. Turn 1 is `(x/one)`,
/// turns 2–4 save `prelude.cl` as `saved_prelude`, and turn 5 is `(one)`.
fn prelude_save_reaching_x(opt_out: bool, saved_prelude: &str) -> e2e::CrOutput {
    let x_source = if opt_out {
        "(import [prelude []])\n(defn one [] 3)\n"
    } else {
        "(defn get [:P p] (P.n p))\n(defn one [] 3)\n"
    };
    Cranelisp::new()
        .prelude("(export [primitives [*]])\n(deftype P [:Int n])\n")
        .file("x.cl", x_source)
        .user("(defn u [] (x/one))\n")
        .repl()
        .stdin(&format!(
            "(x/one)\n{}(one)\n/quit\n",
            save("prelude.cl", saved_prelude)
        ))
        .output()
}

/// The prelude save re-exporting `x`'s `one`.
const PRELUDE_EXPORTING_X: &str =
    "(export [primitives [*]]) (export [x [one]]) (deftype P [:Int n])";

/// Whether some line of `text` reports the type `P` as unresolved, unknown or
/// undefined.
fn reports_p_unresolved(text: &str) -> bool {
    text.lines().any(|line| {
        let lower = line.to_lowercase();
        line.split(|c: char| !(c.is_alphanumeric() || c == '-' || c == '_'))
            .any(|word| word == "P")
            && ["unresolved", "unknown", "undefined"]
                .iter()
                .any(|fault| lower.contains(fault))
    })
}

/// PD-4 and PD-5: the save of `saved_prelude`, which reaches `x` while `x`
/// uses `P` through the implicit import, is refused naming the cycle, and a
/// restart on the saved files reports the same cycle rather than `P`
/// unresolved.
fn assert_prelude_reach_refused_as_cycle_like_restart(saved_prelude: &str) {
    let session = prelude_save_reaching_x(false, saved_prelude);
    let session_transcript = transcript(&session);
    let mut legs = Legs::default();
    {
        let t = prompted_turns(&session.stdout);
        let turn = |i: usize| t.get(i).copied().unwrap_or("");
        let notice = save_notice(&t, 2);
        legs.check(
            turn(1).contains(":primitives/Int 3"),
            "precondition: `(x/one)` gives 3 before the save",
        );
        legs.check(
            notice.contains("[errors:") && names_prelude_x_cycle(&notice),
            "the save is refused naming the cycle of `prelude` and `x`",
        );
        legs.check(
            !notice.contains("[updated: prelude.cl]"),
            "the save does not report `[updated: prelude.cl]`",
        );
    }
    let restart = restart_evaluating_x_one(session);
    let restart_output = format!("{}\n{}", restart.stdout, restart.stderr);
    legs.check(
        names_prelude_x_cycle(&restart_output),
        "a restart on the saved files reports the same cycle",
    );
    legs.check(
        !reports_p_unresolved(&restart_output),
        "the restart does not report `P` unresolved, unknown or undefined",
    );
    legs.assert_all(&format!(
        "--- session ---\n{session_transcript}\n--- restart ---\n{}",
        transcript(&restart)
    ));
}

// spec: spec/08-modules.md §8.8.1, §8.10.1 and §8.10.2 — PD-4: `x.cl` uses the
// prelude's `P` through the implicit import, and a save of `prelude.cl` adding
// `(export [x [one]])` closes `prelude -> x -> prelude`, since `export` is a
// dependency edge. The reload MUST refuse the save naming the cycle, and a
// restart on the saved files MUST report the same cycle, not `P` unresolved.
// The twin `prelude_save_calling_x_qualified_neg_refused_as_cycle_like_restart`
// reaches `x` by a qualified reference.
#[test]
fn prelude_save_exporting_x_neg_refused_as_cycle_like_restart() {
    assert_prelude_reach_refused_as_cycle_like_restart(PRELUDE_EXPORTING_X);
}

// spec: spec/08-modules.md §8.5.4 — item 6, with §8.8.1: PD-5, as
// `prelude_save_exporting_x_neg_refused_as_cycle_like_restart` with the
// prelude reaching `x` only by the qualified call `(x/one)`. The qualified
// reference closing the cycle MUST be reported as the circular dependency, at
// the reload and at a restart, and MUST NOT surface as an unresolved name.
#[test]
fn prelude_save_calling_x_qualified_neg_refused_as_cycle_like_restart() {
    assert_prelude_reach_refused_as_cycle_like_restart(
        "(export [primitives [*]]) (deftype P [:Int n]) (defn pone [] (x/one))",
    );
}

// spec: spec/08-modules.md §8.8.1 and §8.3.7 — PD-4c, the control for
// `prelude_save_exporting_x_neg_refused_as_cycle_like_restart`: `x.cl` carries
// `(import [prelude []])` and does not use `P`. The null import loads nothing,
// so the export closes no cycle: the save reports `[updated: prelude.cl]`, the
// re-exported `(one)` gives 3, and a restart on the saved files agrees.
#[test]
fn prelude_save_exporting_opted_out_x_reloads_like_restart_control() {
    let session = prelude_save_reaching_x(true, PRELUDE_EXPORTING_X);
    let session_transcript = transcript(&session);
    let mut legs = Legs::default();
    {
        let t = prompted_turns(&session.stdout);
        let turn = |i: usize| t.get(i).copied().unwrap_or("");
        let notice = save_notice(&t, 2);
        legs.check(
            turn(1).contains(":primitives/Int 3"),
            "precondition: `(x/one)` gives 3 before the save",
        );
        legs.check(
            notice.contains("[updated: prelude.cl]") && !notice.contains("[errors:"),
            "the save reports `[updated: prelude.cl]` and no errors",
        );
        legs.check(
            turn(5).contains(":primitives/Int 3"),
            "the re-exported `(one)` gives 3 after the save",
        );
    }
    let restart = session
        .run_again()
        .repl()
        .cli_flag("--no-cache")
        .stdin("(one)\n/quit\n")
        .output();
    legs.check(
        prompted_turns(&restart.stdout)
            .get(1)
            .is_some_and(|turn| turn.contains(":primitives/Int 3")),
        "a restart on the saved files gives 3 for `(one)`",
    );
    legs.assert_all(&format!(
        "--- session ---\n{session_transcript}\n--- restart ---\n{}",
        transcript(&restart)
    ));
}
