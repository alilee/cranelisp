mod helpers;
use helpers::e2e::Cranelisp;
use helpers::e2e::Stage;

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.6, §18
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q51_function_turn_redefinition_neg() {
    let out = Cranelisp::new()
        .stdin(
            r#"(defmacro make [n] `(defn ~n [] 10))
(make generated)
(defn generated [] 20)
(generated)
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.to_lowercase().contains("generated")
            && (text.contains("redefin") || text.contains("macro-generated"))
            && (text.contains("at ") || text.contains(":3:") || text.contains(":1:")),
        "located generated-name refusal: {text}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 10"),
        "original definition must survive: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert!(
        (saved.contains("(make generated)") || saved.contains("(make Generated)"))
            && !saved.contains(r#"(defn generated [] 20)"#),
        "backing file unchanged by refusal: {saved}"
    );
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.6, §18
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q51_function_file_redefinition_neg() {
    let out = Cranelisp::new()
        .user(
            r#"(defmacro make [n] `(defn ~n [] 10))
(make generated)
"#,
        )
        .stdin(
            r#"(defn generated [] 20)
(generated)
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.to_lowercase().contains("generated")
            && (text.contains("redefin") || text.contains("macro-generated"))
            && (text.contains("at ") || text.contains(":3:") || text.contains(":1:")),
        "located generated-name refusal: {text}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 10"),
        "original definition must survive: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert!(
        (saved.contains("(make generated)") || saved.contains("(make Generated)"))
            && !saved.contains(r#"(defn generated [] 20)"#),
        "backing file unchanged by refusal: {saved}"
    );
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.6, §18
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q51_type_turn_redefinition_neg() {
    let out = Cranelisp::new()
        .stdin(
            r#"(defmacro make [n] `(deftype ~n Original))
(make Generated)
(deftype Generated Original)
Original
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.to_lowercase().contains("generated")
            && (text.contains("redefin") || text.contains("macro-generated"))
            && (text.contains("at ") || text.contains(":3:") || text.contains(":1:")),
        "located generated-name refusal: {text}"
    );
    assert!(
        out.stdout.contains("Generated.Original"),
        "original definition must survive: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert!(
        (saved.contains("(make generated)") || saved.contains("(make Generated)"))
            && !saved.contains(r#"(deftype Generated Original)"#),
        "backing file unchanged by refusal: {saved}"
    );
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.6, §18
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q51_type_file_redefinition_neg() {
    let out = Cranelisp::new()
        .user(
            r#"(defmacro make [n] `(deftype ~n Original))
(make Generated)
"#,
        )
        .stdin(
            r#"(deftype Generated Original)
Original
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.to_lowercase().contains("generated")
            && (text.contains("redefin") || text.contains("macro-generated"))
            && (text.contains("at ") || text.contains(":3:") || text.contains(":1:")),
        "located generated-name refusal: {text}"
    );
    assert!(
        out.stdout.contains("Generated.Original"),
        "original definition must survive: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert!(
        (saved.contains("(make generated)") || saved.contains("(make Generated)"))
            && !saved.contains(r#"(deftype Generated Original)"#),
        "backing file unchanged by refusal: {saved}"
    );
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.6, §18
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q51_impl_turn_redefinition_neg() {
    let out = Cranelisp::new().stdin(r#"(deftrait Score (score [x] primitives/Int)) (deftype Token HasToken) (defmacro make [n] `(impl Score Token (defn score [x] 10)))
(make Generated)
(impl Score Token (defn score [x] 20))
(score HasToken)
"#).output().assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.to_lowercase().contains("generated")
            && (text.contains("redefin") || text.contains("macro-generated"))
            && (text.contains("at ") || text.contains(":3:") || text.contains(":1:")),
        "located generated-name refusal: {text}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 10"),
        "original definition must survive: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert!(
        (saved.contains("(make generated)") || saved.contains("(make Generated)"))
            && !saved.contains(r#"(impl Score Token (defn score [x] 20))"#),
        "backing file unchanged by refusal: {saved}"
    );
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.6, §18
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q51_impl_file_redefinition_neg() {
    let out = Cranelisp::new().user(r#"(deftrait Score (score [x] primitives/Int)) (deftype Token HasToken) (defmacro make [n] `(impl Score Token (defn score [x] 10)))
(make Generated)
"#).stdin(r#"(impl Score Token (defn score [x] 20))
(score HasToken)
"#).output().assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.to_lowercase().contains("generated")
            && (text.contains("redefin") || text.contains("macro-generated"))
            && (text.contains("at ") || text.contains(":3:") || text.contains(":1:")),
        "located generated-name refusal: {text}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 10"),
        "original definition must survive: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert!(
        (saved.contains("(make generated)") || saved.contains("(make Generated)"))
            && !saved.contains(r#"(impl Score Token (defn score [x] 20))"#),
        "backing file unchanged by refusal: {saved}"
    );
}

// spec: spec/09-macros.md §9.6.1
#[test]
fn s125_q51_written_redefinition_control() {
    Cranelisp::new()
        .stdin(
            "(defn f [] 10)
(defn f [] 20)
(f)
",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 20");
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.4
#[test]
fn s125_q52_same_replaces() {
    let out = Cranelisp::new()
        .file("m.cl", "(defmacro make [x] `(defn generated [] ~x))")
        .stdin(
            r#"(defmacro make [x] `(defn generated [] ~x))
(make 10)
(defmacro make [x] `(defn generated [] (primitives/add-i64 ~x 1)))
(make 10)
(generated)
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 11"),
        "call identity must preserve or replace the intended body: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert_eq!(
        saved
            .lines()
            .filter(|l| l.starts_with("(make 10)") || l.starts_with("(m/make 10)"))
            .count(),
        1,
        "one retained call: {saved}"
    );
    assert!(!text.contains("error:"), "identical call accepted: {text}");
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.4
#[test]
fn s125_q52_qualified_replaces() {
    let out = Cranelisp::new()
        .file("m.cl", "(defmacro make [x] `(defn generated [] ~x))")
        .stdin(
            r#"(import [m [make]])
(make 10)
(m/make 10)
(generated)
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 10"),
        "call identity must preserve or replace the intended body: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert_eq!(
        saved
            .lines()
            .filter(|l| l.starts_with("(make 10)") || l.starts_with("(m/make 10)"))
            .count(),
        1,
        "one retained call: {saved}"
    );
    assert!(!text.contains("error:"), "identical call accepted: {text}");
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.4
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q52_arguments_neg() {
    let out = Cranelisp::new()
        .file("m.cl", "(defmacro make [x] `(defn generated [] ~x))")
        .stdin(
            r#"(defmacro make [x] `(defn generated [] ~x))
(make 10)
(make 20)
(generated)
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 10"),
        "call identity must preserve or replace the intended body: {text}"
    );
    assert!(
        text.contains("redefin") || text.contains("macro-generated"),
        "other call must refuse: {text}"
    );
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.4
// defect: class=silent-accept locus=src/process_form/form_dispatch.rs found=S125 owner=/dev
#[test]
fn s125_q52_other_macro_neg() {
    let out = Cranelisp::new()
        .file("m.cl", "(defmacro make [x] `(defn generated [] ~x))")
        .stdin(
            r#"(defmacro make [x] `(defn generated [] ~x))
(make 10)
(defmacro other [x] `(defn generated [] ~x))
(other 20)
(generated)
"#,
        )
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 10"),
        "call identity must preserve or replace the intended body: {text}"
    );
    assert!(
        text.contains("redefin") || text.contains("macro-generated"),
        "other call must refuse: {text}"
    );
}

// spec: spec/09-macros.md §9.6.1; repl/spec.md §15.6
#[test]
fn s125_q53_reload_retires_generated_origin() {
    let out = Cranelisp::new()
        .user(
            "(defmacro make [] `(defn f [] 10))
(make)
",
        )
        .staged_output(&[
            Stage::Line("(f)"),
            Stage::Write(
                "user.cl",
                b"(defn f [] 20)
",
            ),
            Stage::LineUntilOutput("(f)", ":primitives/Int 20"),
            Stage::Line("(defn f [] 30)"),
            Stage::Line("(f)"),
        ])
        .assert_ok();
    out.assert_stdout_contains(":primitives/Int 20")
        .assert_stdout_contains(":primitives/Int 30")
        .assert_stdout_does_not_contain("error:");
}

// spec: spec/09-macros.md §9.6.1
#[test]
fn s125_q53_one_file_duplicate_neg_run() {
    let cr = Cranelisp::new().user(
        r#"(defmacro make [] `(defn f [] 10))
(make)
(defn f [] 20)
(defn main [] (primitives/pure (f)))
"#,
    );
    let out = cr.run("user.cl").output();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.contains("error")
            && (text.contains("redefin") || text.to_lowercase().contains("generated")),
        "same-file duplicate must refuse: {text}"
    );
}

// spec: spec/09-macros.md §9.6.1
#[test]
fn s125_q53_one_file_duplicate_neg_link() {
    let cr = Cranelisp::new().user(
        r#"(defmacro make [] `(defn f [] 10))
(make)
(defn f [] 20)
(defn main [] (primitives/pure (f)))
"#,
    );
    let out = cr.link("user.cl").output();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.contains("error")
            && (text.contains("redefin") || text.to_lowercase().contains("generated")),
        "same-file duplicate must refuse: {text}"
    );
}

// spec: spec/09-macros.md §9.6.1
#[test]
fn s125_q53_one_file_duplicate_neg_reload() {
    let cr = Cranelisp::new().user(
        r#"(defmacro make [] `(defn f [] 10))
(make)
(defn f [] 20)
(defn main [] (primitives/pure (f)))
"#,
    );
    let out = cr.staged_output(&[
        Stage::Line("1"),
        Stage::Write(
            "user.cl",
            b"(defmacro make [] `(defn f [] 10))\n(make)\n(defn f [] 20)\n",
        ),
        Stage::Line("2"),
    ]);
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        text.contains("error")
            && (text.contains("redefin") || text.to_lowercase().contains("generated")),
        "same-file duplicate must refuse: {text}"
    );
}

// spec: repl/spec.md §15.4
#[test]
fn s125_ps2_cache_authored_order() {
    let first = Cranelisp::new()
        .user(
            r#"(defn first [] 1)
(defn second [] 2)
"#,
        )
        .stdin("1\n")
        .output()
        .assert_ok();
    assert!(first.tmp_exists(".cranelisp-cache/user.o"), "seed cached");
    let out = first
        .run_again()
        .stdin(
            r#"(defn third [] 3)
"#,
        )
        .output()
        .assert_ok();
    let saved = out.read_tmp("user.cl");
    assert!(
        saved.find("(defn first").unwrap() < saved.find("(defn second").unwrap()
            && saved.find("(defn second").unwrap() < saved.find("(defn third").unwrap(),
        "authored and appended order: {saved}"
    );
    out.run_again()
        .stdin("(third)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: repl/spec.md §15.4
#[test]
fn s125_ps2_append_authored_order() {
    let first = Cranelisp::new()
        .user(
            r#"(defn first [] 1)
(defn second [] 2)
"#,
        )
        .stdin("1\n")
        .output()
        .assert_ok();
    let out = first
        .run_again()
        .stdin(
            r#"(defn third [] 3)
"#,
        )
        .output()
        .assert_ok();
    let saved = out.read_tmp("user.cl");
    assert!(
        saved.find("(defn first").unwrap() < saved.find("(defn second").unwrap()
            && saved.find("(defn second").unwrap() < saved.find("(defn third").unwrap(),
        "authored and appended order: {saved}"
    );
    out.run_again()
        .stdin("(third)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: repl/spec.md §15.4
#[test]
fn s125_ps2_macro_dependency_authored_order() {
    let first = Cranelisp::new()
        .user(
            r#"(defmacro early [x] x)
(defmacro later [x] x)
"#,
        )
        .stdin("1\n")
        .output()
        .assert_ok();
    let out = first
        .run_again()
        .stdin(
            r#"(defmacro early [x] (later x))
"#,
        )
        .output()
        .assert_ok();
    let saved = out.read_tmp("user.cl");
    assert!(
        saved.find("(defmacro early").unwrap() < saved.find("(defmacro later").unwrap(),
        "authored order retained: {saved}"
    );
    out.run_again()
        .stdin("(early 42)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: repl/spec.md §15.4
// defect: class=mode-divergence locus=src/repl found=S125 owner=/dev
#[test]
fn s125_ps3_inline_no_ghost_restore() {
    let out = Cranelisp::new()
        .user(
            "(defn old [] 1)
(mod nested (defn child [] 1))
",
        )
        .stdin(
            "(defn unsaved [] 42)
",
        )
        .output()
        .assert_ok();
    let saved = out.read_tmp("user.cl");
    assert!(
        !saved.contains("unsaved"),
        "inline module guard refuses save: {saved}"
    );
    let restarted = out
        .run_again()
        .stdin(
            "(unsaved)
",
        )
        .output()
        .assert_ok();
    assert!(
        (restarted.stdout.contains("undefined") || restarted.stdout.contains("has no member"))
            && !restarted.stdout.contains(":primitives/Int 42"),
        "unsaved definition must not restore: {}{}",
        restarted.stdout,
        restarted.stderr
    );
}

// spec: repl/spec.md §15.4
#[test]
fn s125_ps3_write_failure_no_ghost_restore() {
    let cr = Cranelisp::new().user(
        "(defn old [] 1)
",
    );
    let root = cr.tmpdir_path();
    let path = root.join("user.cl");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o500)).unwrap();
    }
    let mut permissions = std::fs::metadata(&path).unwrap().permissions();
    permissions.set_readonly(true);
    std::fs::set_permissions(&path, permissions).unwrap();
    let out = cr
        .stdin(
            "(defn unsaved [] 42)
",
        )
        .output()
        .assert_ok();
    let saved = out.read_tmp("user.cl");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700)).unwrap();
    }
    let mut permissions = std::fs::metadata(&path).unwrap().permissions();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        permissions.set_mode(0o600);
    }
    std::fs::set_permissions(&path, permissions).unwrap();
    assert!(
        !saved.contains("unsaved"),
        "write must fail on read-only backing file: {saved}"
    );
    let restarted = out
        .run_again()
        .stdin(
            "(unsaved)
",
        )
        .output()
        .assert_ok();
    assert!(
        (restarted.stdout.contains("undefined") || restarted.stdout.contains("has no member"))
            && !restarted.stdout.contains(":primitives/Int 42"),
        "unsaved definition must not restore: {}{}",
        restarted.stdout,
        restarted.stderr
    );
}

// spec: repl/spec.md §15.4
#[test]
fn s125_ps3_inline_module_no_ghost_restore() {
    let out = Cranelisp::new()
        .file("m.cl", "(defn old [] 1)\n(mod nested (defn child [] 1))\n")
        .stdin("(m/old)\n/mod m\n(defn unsaved [] 42)\n/mod user\n")
        .output()
        .assert_ok();
    let saved = out.read_tmp("m.cl");
    assert!(
        !saved.contains("unsaved"),
        "inline module guard refuses save: {saved}"
    );
    let restarted = out
        .run_again()
        .env("CRANELISP_MODULE_TRACE", "1")
        .stdin("(m/unsaved)\n")
        .output()
        .assert_ok();
    assert!(
        restarted
            .stderr
            .contains("module-trace: cache hit (.meta valid) for m"),
        "restore precondition: {}{}",
        restarted.stdout,
        restarted.stderr
    );
    assert!(
        (restarted.stdout.contains("undefined") || restarted.stdout.contains("has no member"))
            && !restarted.stdout.contains(":primitives/Int 42"),
        "unsaved module definition must not restore: {}{}",
        restarted.stdout,
        restarted.stderr
    );
}

// spec: repl/spec.md §15.4
#[test]
fn s125_ps3_inline_batch_control() {
    Cranelisp::new()
        .user(
            "(defn old [] 1)
(mod nested (defn child [] 1))
(defn unsaved [] 42)
(defn main [] (primitives/pure 0))
",
        )
        .run("user.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/09-macros.md §9.6.1 — T-Q9 refuses a shrinking identical-call re-entry.
// defect: class=silent-accept locus=src/process_form.rs found=S125 owner=/dev
#[test]
fn s125_q9_shrinking_reentry_refused_without_changing_live_definitions_or_file() {
    let out = Cranelisp::new()
        .stdin("(defmacro two [] '(begin (defn p [] 1) (defn q [] 2)))\n(two)\n(defmacro two [] '(defn p [] 1))\n/sh cp user.cl before.cl\n(two)\n(p)\n(q)\n")
        .output().assert_ok();
    let turns: Vec<_> = out.stdout.split("user>").collect();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        turns.len() >= 8
            && turns[..5]
                .iter()
                .all(|t| !t.contains("Error:") && !t.contains("[errors:")),
        "T-Q9 setup: {text}"
    );
    let refusal = turns[5];
    let before = std::fs::read(out.tmpdir.join("before.cl")).unwrap();
    let after = std::fs::read(out.tmpdir.join("user.cl")).unwrap();
    let clauses = [
        (
            refusal.contains("q")
                && (refusal.contains("refus")
                    || refusal.contains("Error:")
                    || refusal.contains("error:")),
            "shrinking re-entry refused with diagnostic naming q",
        ),
        (turns[6].contains(":primitives/Int 1"), "p remains 1"),
        (turns[7].contains(":primitives/Int 2"), "q remains 2"),
        (
            before == after,
            "refused re-entry leaves backing file byte-identical",
        ),
    ];
    let failed: Vec<_> = clauses
        .iter()
        .filter_map(|(holds, clause)| (!holds).then_some(*clause))
        .collect();
    assert!(
        failed.is_empty(),
        "violated: {failed:?}\n{text}\nbefore:\n{}\nafter:\n{}",
        String::from_utf8_lossy(&before),
        String::from_utf8_lossy(&after)
    );
}

// spec: spec/09-macros.md §9.6.1 — T-Q9 control: a superset expansion may replace the entry.
#[test]
fn s125_q9_superset_reentry_control() {
    let out = Cranelisp::new()
        .stdin("(defmacro two [] '(begin (defn p [] 1) (defn q [] 2)))\n(two)\n(defmacro two [] '(begin (defn p [] 1) (defn q [] 2) (defn r [] 3)))\n(two)\n(p)\n(q)\n(r)\n")
        .output().assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !text.contains("Error:") && !text.contains("error:") && !text.contains("[errors:"),
        "superset re-entry accepted: {text}"
    );
    let turns: Vec<_> = out.stdout.split("user>").collect();
    for (turn, value) in [(5, 1), (6, 2), (7, 3)] {
        assert!(
            turns
                .get(turn)
                .is_some_and(|t| t.contains(&format!(":primitives/Int {value}"))),
            "superset call turn {turn} yields {value}: {text}"
        );
    }
}

// spec: spec/09-macros.md §9.6.1 — T-Q9 control: unchanged identical-call re-entry is accepted.
#[test]
fn s125_q9_unchanged_reentry_control() {
    let out = Cranelisp::new()
        .stdin("(defmacro two [] '(begin (defn p [] 1) (defn q [] 2)))\n(two)\n(two)\n(p)\n(q)\n")
        .output()
        .assert_ok();
    let text = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !text.contains("Error:") && !text.contains("error:") && !text.contains("[errors:"),
        "unchanged re-entry accepted: {text}"
    );
    let turns: Vec<_> = out.stdout.split("user>").collect();
    assert!(
        turns
            .get(4)
            .is_some_and(|t| t.contains(":primitives/Int 1"))
            && turns
                .get(5)
                .is_some_and(|t| t.contains(":primitives/Int 2")),
        "unchanged re-entry retains p and q: {text}"
    );
    let saved = out.read_tmp("user.cl");
    assert_eq!(
        saved.lines().filter(|line| line.trim() == "(two)").count(),
        1,
        "one retained call: {saved}"
    );
}
