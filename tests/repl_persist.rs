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
