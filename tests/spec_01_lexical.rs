mod helpers;
use helpers::e2e::Cranelisp;

// spec: spec/01-lexical.md §1.4.2
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/reader.rs::read_plus_or_operator found=S124 owner=/dev
#[test]
fn s124_r3_plus() {
    let out = Cranelisp::new()
        .file(
            "p.cl",
            r#"(defn main [] (primitives/Pure (let [+* 5] (primitives/add-i64 +*1))))"#,
        )
        .run("p.cl")
        .output();
    assert!(
        !out.status.success(),
        "operator run accepted: {}{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr
            .contains("operator symbol must not be immediately followed by a digit"),
        "{}",
        out.stderr
    );
}

// spec: spec/01-lexical.md §1.4.2
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/reader.rs::read_plus_or_operator found=S124 owner=/dev
#[test]
fn s124_r3_minus() {
    let out = Cranelisp::new()
        .file(
            "p.cl",
            r#"(defn main [] (primitives/Pure (let [-* 5] (primitives/add-i64 -*1))))"#,
        )
        .run("p.cl")
        .output();
    assert!(
        !out.status.success(),
        "operator run accepted: {}{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr
            .contains("operator symbol must not be immediately followed by a digit"),
        "{}",
        out.stderr
    );
}

// spec: spec/01-lexical.md §1.4.2
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/reader.rs::read_plus_or_operator found=S124 owner=/dev
#[test]
fn s124_r3_arrow() {
    let out = Cranelisp::new()
        .file(
            "p.cl",
            r#"(defn main [] (primitives/Pure (let [-> 5] (primitives/add-i64 ->1))))"#,
        )
        .run("p.cl")
        .output();
    assert!(
        !out.status.success(),
        "operator run accepted: {}{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr
            .contains("operator symbol must not be immediately followed by a digit"),
        "{}",
        out.stderr
    );
}

// spec: spec/01-lexical.md §1.4.2
#[test]
fn s124_r3_star_control() {
    let out = Cranelisp::new()
        .file(
            "p.cl",
            r#"(defn main [] (primitives/Pure (let [** 5] (primitives/add-i64 **1))))"#,
        )
        .run("p.cl")
        .output();
    assert!(
        !out.status.success(),
        "operator run accepted: {}{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr
            .contains("operator symbol must not be immediately followed by a digit"),
        "{}",
        out.stderr
    );
}

// spec: spec/01-lexical.md §1.4.2
#[test]
fn s124_r3_risk_controls() {
    for body in [
        "(primitives/add-i64 +3 -3)",
        "(let [+* 5] (primitives/sub-i64 (primitives/add-i64 +* 1) 6))",
        "(let [- 1 -> 2 += 3] (primitives/sub-i64 (primitives/add-i64 - (primitives/add-i64 -> +=)) 6))",
        "(let [-> (fn [x f] (f x))] (-> 0 (fn [x] x)))",
    ] {
        Cranelisp::new()
            .file("p.cl", &format!("(defn main [] (primitives/Pure {body}))"))
            .run("p.cl")
            .output()
            .assert_exit(0);
    }
}
