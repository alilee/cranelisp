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
