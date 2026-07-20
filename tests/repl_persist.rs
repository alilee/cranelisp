//! Sprint 64 Wave 6 batch 2 Part B carry-forward — Session Persistence
//! (`user.cl`) cluster.
//!
//! Per the Wave 6 batch 2 audit (`tests/plan/wave-6-batch-2-audit.md` §5),
//! these 16 tests carry forward the session-persistence surface from
//! `tests/sprint23.rs` (lines 1241–2047). The audit notes
//! `repl/spec.md §15` across-restart has zero existing `[Tested]`
//! annotations across the carry-forward suite — these tests are the
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

    let second = first
        .run_again()
        .repl()
        .stdin("(foo)\n/quit\n")
        .output();
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
        !out.stdout.contains("[updated: user.cl]")
            && !out.stdout.contains("[errors: user.cl]"),
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
    assert!(first.tmp_exists("user.cl"), "user.cl should exist after session 1");
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
    assert!(first.tmp_exists("user.cl"), "user.cl should exist after session 1");

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
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
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
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
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
    assert!(out.tmp_exists("user.cl"), "user.cl should exist after defining a function");
    assert!(
        out.tmp_exists(".cranelisp-cache"),
        ".cranelisp-cache/ should exist after first session save"
    );
    let cache_dir = out.tmpdir.join(".cranelisp-cache");
    let has_user_meta = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
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
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
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
    assert!(second.status.success(), "session 2 failed: {}", second.stderr);
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
        out.stdout, out.stderr
    );
    assert!(
        out.tmp_exists("user.cl"),
        "user.cl should exist after defining a function. stdout={}\nstderr={}",
        out.stdout, out.stderr
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
        first.stdout, first.stderr
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
        second.stdout, second.stderr
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
//   lazy re-read + re-parse of the backing `.cl` in
//   `src/save.rs::rehydrate_userfn_introspection_from_source`, driven from
//   `session_v4::regenerate_backing_file`.
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
        first.stdout, first.stderr
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
        second.stdout, second.stderr
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
        third.stdout, third.stderr
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
// are the record, per the defect discipline). Ledger:
// tests/plan/ledger.md §"Sprint 101 Phase 6a/6b defect set". Resolver: /int.
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
    assert!(out.status.success(), "session should exit cleanly: stderr={}", out.stderr);
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
    assert!(out.status.success(), "session should exit cleanly: stderr={}", out.stderr);
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

// spec: repl/spec.md §18.8 — after persisting a session that evaluated a bare
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
    assert!(first.status.success(), "session 1 should exit cleanly: stderr={}", first.stderr);
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
    assert!(out.status.success(), "session should exit cleanly: stderr={}", out.stderr);
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
             (deftrait Disp (dp [x] :Int))\n\
             (impl Disp W (defn dp [w] 42))\n\
             (defn g [x] (add-i64 x 1))\n\
             /quit\n",
        )
        .output();
    assert!(out.status.success(), "session should exit cleanly: stderr={}", out.stderr);
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
             (deftrait Disp (dp [x] :Int))\n\
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
    assert!(out.status.success(), "session should exit cleanly: stderr={}", out.stderr);
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
    assert!(first.status.success(), "session 1 should exit cleanly: stderr={}", first.stderr);

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
        second.stdout, second.stderr
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
    assert!(out.status.success(), "session should exit cleanly: stderr={}", out.stderr);
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
