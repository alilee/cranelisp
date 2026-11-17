mod helpers;
use helpers::e2e::{Cranelisp, PreludeVariant};

fn field_projection(program: &str, expected: i32, mode: &str) {
    let cr = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_RC_DEC_CHECK", "1")
        .linked_environment(&[("CRANELISP_RC_STATS", "1"), ("CRANELISP_RC_DEC_CHECK", "1")]);
    let out = match mode {
        "run" => cr.file("p.cl", program).run("p.cl").output(),
        "link" => cr.file("p.cl", program).link_then_run("p.cl").output(),
        _ => cr.stdin(&format!("{program}\n(main)\n")).output(),
    };
    if mode == "repl" {
        assert!(
            out.status.success() && out.stdout.contains(&format!(":primitives/Int {expected}")),
            "{}{}",
            out.stdout,
            out.stderr
        );
    } else {
        assert_eq!(
            out.status.code(),
            Some(expected % 256),
            "{}{}",
            out.stdout,
            out.stderr
        );
    }
    let stderr = if mode == "link" {
        out.linked_stderr.as_deref().expect("linked execution")
    } else {
        &out.stderr
    };
    let stats = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .expect("RC statistics must be present");
    let count = |key: &str| {
        stats
            .split_whitespace()
            .find_map(|s| s.strip_prefix(key).and_then(|v| v.parse::<i64>().ok()))
            .expect("RC count")
    };
    assert!(count("allocs=") > 0, "{stats}");
    assert_eq!(count("allocs="), count("deallocs="), "{stats}");
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-a field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_a_subject_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (P a b) (MkP [:b y :a x])) (defn f [p] (match p [(MkP y x) (add-i64 x (str-len y))])) (defn main [] (Pure (f (MkP "abc" 2000))))"#,
        2003,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-a field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_a_subject_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (P a b) (MkP [:b y :a x])) (defn f [p] (match p [(MkP y x) (add-i64 x (str-len y))])) (defn main [] (Pure (f (MkP "abc" 2000))))"#,
        2003,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-a field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_a_subject_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (P a b) (MkP [:b y :a x])) (defn f [p] (match p [(MkP y x) (add-i64 x (str-len y))])) (defn main [] (Pure (f (MkP "abc" 2000))))"#,
        2003,
        "repl",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-a field projection
#[test]
fn s124_1062_a_control_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (P a b) (MkP [:a x :b y])) (defn f [p] (match p [(MkP x y) (add-i64 x (str-len y))])) (defn main [] (Pure (f (MkP 2000 "abc"))))"#,
        2003,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-a field projection
#[test]
fn s124_1062_a_control_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (P a b) (MkP [:a x :b y])) (defn f [p] (match p [(MkP x y) (add-i64 x (str-len y))])) (defn main [] (Pure (f (MkP 2000 "abc"))))"#,
        2003,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-a field projection
#[test]
fn s124_1062_a_control_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (P a b) (MkP [:a x :b y])) (defn f [p] (match p [(MkP x y) (add-i64 x (str-len y))])) (defn main [] (Pure (f (MkP 2000 "abc"))))"#,
        2003,
        "repl",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-b field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_b_subject_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (R a b) (MkR [:b y])) (defn f [:(R Int String) p] (match p [(MkR y) (str-len y)])) (defn main [] (Pure (f (MkR "abc"))))"#,
        3,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-b field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_b_subject_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (R a b) (MkR [:b y])) (defn f [:(R Int String) p] (match p [(MkR y) (str-len y)])) (defn main [] (Pure (f (MkR "abc"))))"#,
        3,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-b field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_b_subject_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (R a b) (MkR [:b y])) (defn f [:(R Int String) p] (match p [(MkR y) (str-len y)])) (defn main [] (Pure (f (MkR "abc"))))"#,
        3,
        "repl",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-b field projection
#[test]
fn s124_1062_b_control_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (R b a) (MkR [:b y])) (defn f [:(R String Int) p] (match p [(MkR y) (str-len y)])) (defn main [] (Pure (f (MkR "abc"))))"#,
        3,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-b field projection
#[test]
fn s124_1062_b_control_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (R b a) (MkR [:b y])) (defn f [:(R String Int) p] (match p [(MkR y) (str-len y)])) (defn main [] (Pure (f (MkR "abc"))))"#,
        3,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-b field projection
#[test]
fn s124_1062_b_control_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (R b a) (MkR [:b y])) (defn f [:(R String Int) p] (match p [(MkR y) (str-len y)])) (defn main [] (Pure (f (MkR "abc"))))"#,
        3,
        "repl",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-c field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_c_subject_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (E a b) (L [:b l]) (R [:a r])) (defn f [:(E Int String) p] (match p [(L s) (str-len s) (R n) (add-i64 n 3)])) (defn main [] (Pure (f (R 2000))))"#,
        2003,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-c field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_c_subject_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (E a b) (L [:b l]) (R [:a r])) (defn f [:(E Int String) p] (match p [(L s) (str-len s) (R n) (add-i64 n 3)])) (defn main [] (Pure (f (R 2000))))"#,
        2003,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-c field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_c_subject_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (E a b) (L [:b l]) (R [:a r])) (defn f [:(E Int String) p] (match p [(L s) (str-len s) (R n) (add-i64 n 3)])) (defn main [] (Pure (f (R 2000))))"#,
        2003,
        "repl",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-c field projection
#[test]
fn s124_1062_c_control_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (E a b) (R [:a r]) (L [:b l])) (defn f [:(E Int String) p] (match p [(L s) (str-len s) (R n) (add-i64 n 3)])) (defn main [] (Pure (f (R 2000))))"#,
        2003,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-c field projection
#[test]
fn s124_1062_c_control_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (E a b) (R [:a r]) (L [:b l])) (defn f [:(E Int String) p] (match p [(L s) (str-len s) (R n) (add-i64 n 3)])) (defn main [] (Pure (f (R 2000))))"#,
        2003,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-c field projection
#[test]
fn s124_1062_c_control_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (E a b) (R [:a r]) (L [:b l])) (defn f [:(E Int String) p] (match p [(L s) (str-len s) (R n) (add-i64 n 3)])) (defn main [] (Pure (f (R 2000))))"#,
        2003,
        "repl",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-d field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_d_subject_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (Duo a b) [:b y :a x]) (defn f [d] (add-i64 (Duo.x d) (str-len (Duo.y d)))) (defn main [] (Pure (f (Duo "abc" 2000))))"#,
        2003,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-d field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_d_subject_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (Duo a b) [:b y :a x]) (defn f [d] (add-i64 (Duo.x d) (str-len (Duo.y d)))) (defn main [] (Pure (f (Duo "abc" 2000))))"#,
        2003,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-d field projection
// defect: class=projection-mirror locus=crates/cranelisp-backend::CompileContext::ctor_field_types found=S124 owner=/dev
#[test]
fn s124_1062_d_subject_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (Duo a b) [:b y :a x]) (defn f [d] (add-i64 (Duo.x d) (str-len (Duo.y d)))) (defn main [] (Pure (f (Duo "abc" 2000))))"#,
        2003,
        "repl",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-d field projection
#[test]
fn s124_1062_d_control_run() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (Duo a b) [:a x :b y]) (defn f [d] (add-i64 (Duo.x d) (str-len (Duo.y d)))) (defn main [] (Pure (f (Duo 2000 "abc"))))"#,
        2003,
        "run",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-d field projection
#[test]
fn s124_1062_d_control_link() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (Duo a b) [:a x :b y]) (defn f [d] (add-i64 (Duo.x d) (str-len (Duo.y d)))) (defn main [] (Pure (f (Duo 2000 "abc"))))"#,
        2003,
        "link",
    );
}

// spec: spec/04-expressions.md §4.6 — REPRO-1062-d field projection
#[test]
fn s124_1062_d_control_repl() {
    field_projection(
        r#"(import [primitives [*]]) (deftype (Duo a b) [:a x :b y]) (defn f [d] (add-i64 (Duo.x d) (str-len (Duo.y d)))) (defn main [] (Pure (f (Duo 2000 "abc"))))"#,
        2003,
        "repl",
    );
}

const S124_1062_SHAPES: &str = r#"(import [primitives [*]])
(deftype (P a b) (MkP [:b y :a x]))
(deftype (Q a b) (MkQ [:a x :b y]))
(defn obsp [:(P Int String) p] (match p [(MkP y x) (add-i64 1 x)]))
(defn obsq [:(Q Int String) q] (match q [(MkQ x y) (add-i64 1 x)]))
(defn obsps [:(P Int Int) p] (match p [(MkP y x) (add-i64 y x)]))
"#;

fn s124_1062_display(leg: &str) {
    let (value, expected) = match leg {
        "subject" => (
            r#"(MkP "s" 2000)"#,
            r#":(shapes/P primitives/Int primitives/String) (P.MkP "s" 2000)"#,
        ),
        "ordered_control" => (
            r#"(MkQ 2000 "s")"#,
            r#":(shapes/Q primitives/Int primitives/String) (Q.MkQ 2000 "s")"#,
        ),
        "scalar_control" => (
            "(MkP 7 2000)",
            ":(shapes/P primitives/Int primitives/Int) (P.MkP 7 2000)",
        ),
        _ => unreachable!(),
    };
    Cranelisp::new()
        .file("shapes.cl", S124_1062_SHAPES)
        .stdin(&format!("(import [shapes [*]])\n{value}\n"))
        .output()
        .assert_ok()
        .assert_stdout_contains(expected)
        .assert_stdout_does_not_contain("error:");
}

fn s124_1062_trace(leg: &str, mode: &str) {
    let (call, argument, result) = match leg {
        "subject" => (r#"(obsp (MkP "s" 2000))"#, r#"(P.MkP "s" 2000)"#, "2001"),
        "ordered_control" => (r#"(obsq (MkQ 2000 "s"))"#, r#"(Q.MkQ 2000 "s")"#, "2001"),
        "scalar_control" => ("(obsps (MkP 7 2000))", "(P.MkP 7 2000)", "2007"),
        "untraced_control" => (r#"(obsp (MkP "s" 2000))"#, "", "2001"),
        _ => unreachable!(),
    };
    let callee = match leg {
        "ordered_control" => "shapes/obsq",
        "scalar_control" => "shapes/obsps",
        _ => "shapes/obsp",
    };
    let checker = format!(
        r#"(defn check-frames [frames]
      (match frames [SNil -4 (SCons frame rest)
        (match frame [(TraceCall n p r c ns)
          (if (str-eq n {callee:?})
            (match p [SNil -1 (SCons h t)
              (if (str-eq h {argument:?}) (if (str-eq r {result:?}) 77 -2) -3)])
            (check-frames rest))])]))"#
    );
    let body = if leg == "untraced_control" {
        call.to_owned()
    } else {
        format!(
            "(match (trace {call}) [(TraceCall root rp rr children rn) (check-frames children)])"
        )
    };
    let program = format!(
        "(import [primitives [*]])\n(import [macros [SCons SNil]])\n(import [shapes [*]])\n{checker}\n(defn main [] (Pure {body}))\n"
    );
    let cr = Cranelisp::new()
        .file("shapes.cl", S124_1062_SHAPES)
        .env("CRANELISP_NO_LENIENT", "1");
    let out = match mode {
        "run" => cr.file("p.cl", &program).run("p.cl").output(),
        "link" => cr.file("p.cl", &program).link_then_run("p.cl").output(),
        "repl" => cr.stdin(&format!("{program}(main)\n")).output(),
        _ => unreachable!(),
    };
    let expected = if leg == "untraced_control" { 2001 } else { 77 };
    if mode == "repl" {
        out.assert_ok()
            .assert_stdout_contains(&format!(":primitives/Int {expected}"))
            .assert_stdout_does_not_contain("error:");
    } else {
        out.assert_exit(expected % 256);
    }
}

// spec: spec/12-runtime.md §12.9 — REPRO-1062-e subject
// defect: class=projection-mirror locus=src/display.rs::build_adt_subst found=S124 owner=/dev
#[test]
fn s124_1062_e_subject_repl() {
    s124_1062_display("subject");
}

// spec: spec/12-runtime.md §12.9 — REPRO-1062-e ordered_control
#[test]
fn s124_1062_e_ordered_control_repl() {
    s124_1062_display("ordered_control");
}

// spec: spec/12-runtime.md §12.9 — REPRO-1062-e scalar_control
#[test]
fn s124_1062_e_scalar_control_repl() {
    s124_1062_display("scalar_control");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f subject
// defect: class=projection-mirror locus=crates/cranelisp-backend/src/compiler/trace_codegen.rs found=S124 owner=/dev
#[test]
fn s124_1062_f_subject_run() {
    s124_1062_trace("subject", "run");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f subject
// defect: class=projection-mirror locus=crates/cranelisp-backend/src/compiler/trace_codegen.rs found=S124 owner=/dev
#[test]
fn s124_1062_f_subject_link() {
    s124_1062_trace("subject", "link");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f subject
// defect: class=projection-mirror locus=crates/cranelisp-backend/src/compiler/trace_codegen.rs found=S124 owner=/dev
#[test]
fn s124_1062_f_subject_repl() {
    s124_1062_trace("subject", "repl");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f ordered_control
#[test]
fn s124_1062_f_ordered_control_run() {
    s124_1062_trace("ordered_control", "run");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f ordered_control
#[test]
fn s124_1062_f_ordered_control_link() {
    s124_1062_trace("ordered_control", "link");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f ordered_control
#[test]
fn s124_1062_f_ordered_control_repl() {
    s124_1062_trace("ordered_control", "repl");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f scalar_control
#[test]
fn s124_1062_f_scalar_control_run() {
    s124_1062_trace("scalar_control", "run");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f scalar_control
#[test]
fn s124_1062_f_scalar_control_link() {
    s124_1062_trace("scalar_control", "link");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f scalar_control
#[test]
fn s124_1062_f_scalar_control_repl() {
    s124_1062_trace("scalar_control", "repl");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f untraced_control
#[test]
fn s124_1062_f_untraced_control_run() {
    s124_1062_trace("untraced_control", "run");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f untraced_control
#[test]
fn s124_1062_f_untraced_control_link() {
    s124_1062_trace("untraced_control", "link");
}

// spec: spec/04-expressions.md §4.12.2 — REPRO-1062-f untraced_control
#[test]
fn s124_1062_f_untraced_control_repl() {
    s124_1062_trace("untraced_control", "repl");
}
