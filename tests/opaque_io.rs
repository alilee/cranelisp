mod helpers;
use helpers::e2e::Cranelisp;

fn refuses(source: &str, mode: &str, constructor: &str) {
    let cr = Cranelisp::new().user(source);
    let out = match mode {
        "run" => cr.run("user.cl").output(),
        "link" => cr.link("user.cl").output(),
        _ => cr.stdin("7\n").output(),
    };
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains(constructor)
            && (diag.contains("undefined")
                || diag.contains("unknown")
                || diag.contains("private")
                || diag.contains("not found")
                || diag.contains("cannot construct internal type constructor")
                || diag.contains("cannot match on internal type constructor")),
        "IO constructor must be unavailable: {diag}"
    );
    if mode != "repl" {
        assert_eq!(out.status.code(), Some(1), "{diag}");
    }
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_dotted_neg_run() {
    refuses(
        r#"(import [primitives [IO]]) (defn main [] (IO.Pure 1))"#,
        "run",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_dotted_neg_repl() {
    refuses(
        r#"(import [primitives [IO]]) (defn main [] (IO.Pure 1))"#,
        "repl",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_dotted_neg_link() {
    refuses(
        r#"(import [primitives [IO]]) (defn main [] (IO.Pure 1))"#,
        "link",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_imported_neg_run() {
    refuses(
        r#"(import [primitives [Pure]]) (defn main [] (Pure 1))"#,
        "run",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_imported_neg_repl() {
    refuses(
        r#"(import [primitives [Pure]]) (defn main [] (Pure 1))"#,
        "repl",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_pattern_neg_run() {
    refuses(
        r#"(import [primitives [IO]]) (defn probe [x] (match x [(IO.Pure y) 1 _ 0])) (defn main [] (primitives/pure 0))"#,
        "run",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_pattern_neg_repl() {
    refuses(
        r#"(import [primitives [IO]]) (defn probe [x] (match x [(IO.Pure y) 1 _ 0])) (defn main [] (primitives/pure 0))"#,
        "repl",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_pure_dotted_control() {
    user_constructor_control("Pure", "dotted");
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_pure_imported_control() {
    user_constructor_control("Pure", "imported");
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_pure_pattern_control() {
    user_constructor_control("Pure", "pattern");
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_dotted_neg_run() {
    refuses(
        r#"(import [primitives [IO]]) (defn main [] (let [node (IO.Effect 1)] (primitives/sleep 0)))"#,
        "run",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_dotted_neg_repl() {
    refuses(
        r#"(import [primitives [IO]]) (defn main [] (let [node (IO.Effect 1)] (primitives/sleep 0)))"#,
        "repl",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_imported_neg_run() {
    refuses(
        r#"(import [primitives [Effect]]) (defn main [] (let [node (Effect 1)] (primitives/sleep 0)))"#,
        "run",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_imported_neg_repl() {
    refuses(
        r#"(import [primitives [Effect]]) (defn main [] (let [node (Effect 1)] (primitives/sleep 0)))"#,
        "repl",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_pattern_neg_run() {
    refuses(
        r#"(import [primitives [IO]]) (defn probe [x] (match x [(IO.Effect y) 1 _ 0])) (defn main [] (primitives/pure 0))"#,
        "run",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_pattern_neg_repl() {
    refuses(
        r#"(import [primitives [IO]]) (defn probe [x] (match x [(IO.Effect y) 1 _ 0])) (defn main [] (primitives/pure 0))"#,
        "repl",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_effect_dotted_control() {
    user_constructor_control("Effect", "dotted");
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_effect_imported_control() {
    user_constructor_control("Effect", "imported");
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_effect_pattern_control() {
    user_constructor_control("Effect", "pattern");
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_dotted_neg_run() {
    refuses(
        r#"(import [primitives [IO]]) (defn main [] (IO.Bind (primitives/sleep 0) (fn [x] (primitives/sleep 0))))"#,
        "run",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_dotted_neg_repl() {
    refuses(
        r#"(import [primitives [IO]]) (defn main [] (IO.Bind (primitives/sleep 0) (fn [x] (primitives/sleep 0))))"#,
        "repl",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_imported_neg_run() {
    refuses(
        r#"(import [primitives [Bind]]) (defn main [] (Bind (primitives/sleep 0) (fn [x] (primitives/sleep 0))))"#,
        "run",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_imported_neg_repl() {
    refuses(
        r#"(import [primitives [Bind]]) (defn main [] (Bind (primitives/sleep 0) (fn [x] (primitives/sleep 0))))"#,
        "repl",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_pattern_neg_run() {
    refuses(
        r#"(import [primitives [IO]]) (defn probe [x] (match x [(IO.Bind y k) 1 _ 0])) (defn main [] (primitives/pure 0))"#,
        "run",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_pattern_neg_repl() {
    refuses(
        r#"(import [primitives [IO]]) (defn probe [x] (match x [(IO.Bind y k) 1 _ 0])) (defn main [] (primitives/pure 0))"#,
        "repl",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_bind_dotted_control() {
    user_constructor_control("Bind", "dotted");
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_bind_imported_control() {
    user_constructor_control("Bind", "imported");
}

// spec: spec/10-io.md §10.1
#[test]
fn s125_io1_user_bind_pattern_control() {
    user_constructor_control("Bind", "pattern");
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_applied_scalar_run() {
    let out = lift_case(&lift_program("applied", r#"42"#), "run");
    assert!(
        lift_observed(&out, "run", 42),
        "lift must deliver its payload through applied: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_applied_scalar_link() {
    let out = lift_case(&lift_program("applied", r#"42"#), "link");
    assert!(
        lift_observed(&out, "link", 42),
        "lift must deliver its payload through applied: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_applied_scalar_repl() {
    let out = lift_case(&lift_program("applied", r#"42"#), "repl");
    assert!(
        lift_observed(&out, "repl", 42),
        "lift must deliver its payload through applied: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_applied_heap_run() {
    let out = lift_case(&lift_program("applied", r#""hello""#), "run");
    assert!(
        lift_observed(&out, "run", 5),
        "lift must deliver its payload through applied: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_applied_heap_link() {
    let out = lift_case(&lift_program("applied", r#""hello""#), "link");
    assert!(
        lift_observed(&out, "link", 5),
        "lift must deliver its payload through applied: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_applied_heap_repl() {
    let out = lift_case(&lift_program("applied", r#""hello""#), "repl");
    assert!(
        lift_observed(&out, "repl", 5),
        "lift must deliver its payload through applied: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_passed_scalar_run() {
    let out = lift_case(&lift_program("passed", r#"42"#), "run");
    assert!(
        lift_observed(&out, "run", 42),
        "lift must deliver its payload through passed: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_passed_scalar_link() {
    let out = lift_case(&lift_program("passed", r#"42"#), "link");
    assert!(
        lift_observed(&out, "link", 42),
        "lift must deliver its payload through passed: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_passed_scalar_repl() {
    let out = lift_case(&lift_program("passed", r#"42"#), "repl");
    assert!(
        lift_observed(&out, "repl", 42),
        "lift must deliver its payload through passed: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_passed_heap_run() {
    let out = lift_case(&lift_program("passed", r#""hello""#), "run");
    assert!(
        lift_observed(&out, "run", 5),
        "lift must deliver its payload through passed: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_passed_heap_link() {
    let out = lift_case(&lift_program("passed", r#""hello""#), "link");
    assert!(
        lift_observed(&out, "link", 5),
        "lift must deliver its payload through passed: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_passed_heap_repl() {
    let out = lift_case(&lift_program("passed", r#""hello""#), "repl");
    assert!(
        lift_observed(&out, "repl", 5),
        "lift must deliver its payload through passed: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_bound_scalar_run() {
    let out = lift_case(&lift_program("bound", r#"42"#), "run");
    assert!(
        lift_observed(&out, "run", 42),
        "lift must deliver its payload through bound: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_bound_scalar_link() {
    let out = lift_case(&lift_program("bound", r#"42"#), "link");
    assert!(
        lift_observed(&out, "link", 42),
        "lift must deliver its payload through bound: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_bound_scalar_repl() {
    let out = lift_case(&lift_program("bound", r#"42"#), "repl");
    assert!(
        lift_observed(&out, "repl", 42),
        "lift must deliver its payload through bound: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_bound_heap_run() {
    let out = lift_case(&lift_program("bound", r#""hello""#), "run");
    assert!(
        lift_observed(&out, "run", 5),
        "lift must deliver its payload through bound: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_bound_heap_link() {
    let out = lift_case(&lift_program("bound", r#""hello""#), "link");
    assert!(
        lift_observed(&out, "link", 5),
        "lift must deliver its payload through bound: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_bound_heap_repl() {
    let out = lift_case(&lift_program("bound", r#""hello""#), "repl");
    assert!(
        lift_observed(&out, "repl", 5),
        "lift must deliver its payload through bound: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_captured_scalar_run() {
    let out = lift_case(&lift_program("captured", r#"42"#), "run");
    assert!(
        lift_observed(&out, "run", 42),
        "lift must deliver its payload through captured: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_captured_scalar_link() {
    let out = lift_case(&lift_program("captured", r#"42"#), "link");
    assert!(
        lift_observed(&out, "link", 42),
        "lift must deliver its payload through captured: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_captured_scalar_repl() {
    let out = lift_case(&lift_program("captured", r#"42"#), "repl");
    assert!(
        lift_observed(&out, "repl", 42),
        "lift must deliver its payload through captured: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_captured_heap_run() {
    let out = lift_case(&lift_program("captured", r#""hello""#), "run");
    assert!(
        lift_observed(&out, "run", 5),
        "lift must deliver its payload through captured: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_captured_heap_link() {
    let out = lift_case(&lift_program("captured", r#""hello""#), "link");
    assert!(
        lift_observed(&out, "link", 5),
        "lift must deliver its payload through captured: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_captured_heap_repl() {
    let out = lift_case(&lift_program("captured", r#""hello""#), "repl");
    assert!(
        lift_observed(&out, "repl", 5),
        "lift must deliver its payload through captured: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_stored_scalar_run() {
    let out = lift_case(&lift_program("stored", r#"42"#), "run");
    assert!(
        lift_observed(&out, "run", 42),
        "lift must deliver its payload through stored: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_stored_scalar_link() {
    let out = lift_case(&lift_program("stored", r#"42"#), "link");
    assert!(
        lift_observed(&out, "link", 42),
        "lift must deliver its payload through stored: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_stored_scalar_repl() {
    let out = lift_case(&lift_program("stored", r#"42"#), "repl");
    assert!(
        lift_observed(&out, "repl", 42),
        "lift must deliver its payload through stored: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_stored_heap_run() {
    let out = lift_case(&lift_program("stored", r#""hello""#), "run");
    assert!(
        lift_observed(&out, "run", 5),
        "lift must deliver its payload through stored: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_stored_heap_link() {
    let out = lift_case(&lift_program("stored", r#""hello""#), "link");
    assert!(
        lift_observed(&out, "link", 5),
        "lift must deliver its payload through stored: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_stored_heap_repl() {
    let out = lift_case(&lift_program("stored", r#""hello""#), "repl");
    assert!(
        lift_observed(&out, "repl", 5),
        "lift must deliver its payload through stored: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/10-io.md §10.2; spec/12-runtime.md §12.3.1
// defect: class=wrong-reject locus=src/bootstrap.rs::pure-seed found=S124 owner=/dev
#[test]
fn s125_io2_twice_forced_heap_balances() {
    use helpers::marginal::{Child, Instrument, MarginalPair};
    let control =
        Child::new(r#"(defn main [] (primitives/pure 0))"#).env("CRANELISP_RC_DEC_CHECK", "1");
    let subject = Child::new(r#"(defn main [] (let [node (primitives/pure (primitives/str-concat "he" "llo"))] (primitives/bind node (fn [a] (primitives/bind node (fn [b] (primitives/pure (primitives/add-i64 (primitives/str-len a) (primitives/str-len b)))))))))"#).env("CRANELISP_RC_DEC_CHECK", "1");
    let result = MarginalPair::new("twice forced IO heap", control, subject)
        .instrument(Instrument::RcStats)
        .measure();
    assert_eq!(result.control().exit_code(), Some(0), "{}", result.report());
    assert_eq!(
        result.subject().exit_code(),
        Some(10),
        "{}",
        result.report()
    );
    result.assert_balanced("heap payload retained through both forces and dropped");
}

// spec: repl/spec.md §1.2.1, §1.5
// defect: class=display-envelope-mirror locus=src/display.rs found=S125 owner=/dev
#[test]
fn s125_io5_box_display() {
    let out = Cranelisp::new()
        .stdin(
            r#"(deftype (Box a) (Wrap [:a value]))
(Wrap (primitives/pure 1))
"#,
        )
        .output()
        .assert_ok();
    assert!(
        out.stdout.contains("(Box.Wrap #io)"),
        "opaque IO display: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: repl/spec.md §1.2.1, §1.5
// defect: class=display-envelope-mirror locus=src/display.rs found=S125 owner=/dev
#[test]
fn s125_io5_vector_display() {
    let out = Cranelisp::new()
        .stdin(
            r#"
[[(primitives/sleep 0)]]
"#,
        )
        .output()
        .assert_ok();
    assert!(
        out.stdout.contains("[[#io]]"),
        "opaque IO display: {}{}",
        out.stdout,
        out.stderr
    );
}

// spec: repl/spec.md §1.2.1, §1.5
// defect: class=check-domain-overreach locus=src/result_owner.rs found=S125 owner=/dev
#[test]
fn s125_io5_double_display() {
    let out = Cranelisp::new()
        .stdin(
            r#"
(primitives/pure (primitives/pure 1))
"#,
        )
        .output()
        .assert_ok();
    assert!(
        out.stdout.contains(":(primitives/IO primitives/Int) #io"),
        "opaque IO display: {}{}",
        out.stdout,
        out.stderr
    );
    out.assert_stdout_contains("Executing IO…");
}

fn user_constructor_control(constructor: &str, spelling: &str) {
    let call = if spelling == "dotted" {
        format!("User.{constructor}")
    } else {
        constructor.into()
    };
    let src = format!(
        "(import [c [User {constructor}]]) (defn get [x] (match x [({constructor} n) n])) (defn main [] (primitives/pure (get ({call} 42))))"
    );
    for mode in ["run", "link", "repl"] {
        let cr = Cranelisp::new()
            .file(
                "c.cl",
                &format!("(deftype User ({constructor} [:primitives/Int n]))"),
            )
            .user(&src);
        let out = match mode {
            "run" => cr.run("user.cl").output(),
            "link" => cr.link_then_run("user.cl").output(),
            _ => cr.stdin("(main)\n").output(),
        };
        if mode == "repl" {
            out.assert_ok().assert_stdout_contains(":primitives/Int 42");
        } else {
            out.assert_exit(42);
        }
    }
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_bare_pattern_neg_run() {
    refuses(
        r#"(defn probe [] (match (primitives/sleep 0) [(Pure y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "run",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_bare_pattern_neg_repl() {
    refuses(
        r#"(defn probe [] (match (primitives/sleep 0) [(Pure y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "repl",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_imported_pattern_neg_run() {
    refuses(
        r#"(import [primitives [Pure]]) (defn probe [] (match (primitives/sleep 0) [(Pure y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "run",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_pure_imported_pattern_neg_repl() {
    refuses(
        r#"(import [primitives [Pure]]) (defn probe [] (match (primitives/sleep 0) [(Pure y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "repl",
        "Pure",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_bare_pattern_neg_run() {
    refuses(
        r#"(defn probe [] (match (primitives/sleep 0) [(Effect y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "run",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_bare_pattern_neg_repl() {
    refuses(
        r#"(defn probe [] (match (primitives/sleep 0) [(Effect y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "repl",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_imported_pattern_neg_run() {
    refuses(
        r#"(import [primitives [Effect]]) (defn probe [] (match (primitives/sleep 0) [(Effect y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "run",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_effect_imported_pattern_neg_repl() {
    refuses(
        r#"(import [primitives [Effect]]) (defn probe [] (match (primitives/sleep 0) [(Effect y) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "repl",
        "Effect",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_bare_pattern_neg_run() {
    refuses(
        r#"(defn probe [] (match (primitives/sleep 0) [(Bind y k) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "run",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_bare_pattern_neg_repl() {
    refuses(
        r#"(defn probe [] (match (primitives/sleep 0) [(Bind y k) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "repl",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_imported_pattern_neg_run() {
    refuses(
        r#"(import [primitives [Bind]]) (defn probe [] (match (primitives/sleep 0) [(Bind y k) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "run",
        "Bind",
    );
}

// spec: spec/10-io.md §10.1
// defect: class=silent-accept locus=src/bootstrap.rs found=S125 owner=/dev
#[test]
fn s125_io1_bind_imported_pattern_neg_repl() {
    refuses(
        r#"(import [primitives [Bind]]) (defn probe [] (match (primitives/sleep 0) [(Bind y k) 1 _ 0])) (defn main [] (primitives/pure (probe)))"#,
        "repl",
        "Bind",
    );
}

fn lift_observed(out: &helpers::e2e::CrOutput, mode: &str, expected: i32) -> bool {
    if mode == "repl" {
        out.status.success()
            && out.stdout.contains(&format!(":primitives/Int {expected}"))
            && !out.stdout.contains("Error:")
    } else {
        out.status.code() == Some(expected)
    }
}

fn lift_program(shape: &str, payload: &str) -> String {
    let expression = match shape {
        "applied" => format!("(primitives/pure {payload})"),
        "passed" => format!("(lift primitives/pure {payload})"),
        "bound" => format!("(let [p primitives/pure] (p {payload}))"),
        "captured" => format!("(let [p primitives/pure f (fn [x] (p x))] (f {payload}))"),
        "stored" => format!("(let [ps [primitives/pure]] ((primitives/vec-get ps 0) {payload}))"),
        _ => unreachable!(),
    };
    let result = if payload.starts_with('"') {
        format!("(primitives/bind {expression} (fn [s] (primitives/pure (primitives/str-len s))))")
    } else {
        expression
    };
    format!("(defn lift [f x] (f x)) (defn main [] {result})")
}

fn lift_case(source: &str, mode: &str) -> helpers::e2e::CrOutput {
    let cr = Cranelisp::new()
        .user(source)
        .env("CRANELISP_RC_DEC_CHECK", "1");
    match mode {
        "run" => cr.run("user.cl").output(),
        "link" => cr.link_then_run("user.cl").output(),
        _ => cr.stdin("(main)\n").output(),
    }
}

// spec: spec/10-io.md §10.2; AGENTS.md — Assurance
#[test]
fn s125_io2_payload_observer_detection_proof() {
    for shape in ["applied", "passed", "bound", "captured", "stored"] {
        for (good, bad, expected) in [("42", "41", 42), (r#""hello""#, r#""bad""#, 5)] {
            for mode in ["run", "link", "repl"] {
                // Only payload contents vary; both subjects use the same callable positions.
                let alias = "(defn counterfactual-pure [x] (primitives/pure x)) ";
                let good = format!(
                    "{alias}{}",
                    lift_program(shape, good).replace("primitives/pure", "counterfactual-pure")
                );
                let bad = format!(
                    "{alias}{}",
                    lift_program(shape, bad).replace("primitives/pure", "counterfactual-pure")
                );
                let control = lift_case(&good, mode);
                assert!(
                    lift_observed(&control, mode, expected),
                    "{shape} {mode} sound control: {}{}",
                    control.stdout,
                    control.stderr
                );
                let fault = lift_case(&bad, mode);
                assert!(
                    !lift_observed(&fault, mode, expected),
                    "{shape} {mode} wrong payload must fail the allocated assertion"
                );
                assert!(
                    fault.status.code().is_some() && !fault.stderr.contains("error:"),
                    "fault is a wrong result, not failed setup: {}{}",
                    fault.stdout,
                    fault.stderr
                );
            }
        }
    }
}

// spec: spec/10-io.md §10.2; spec/12-runtime.md §12.3.1
#[test]
fn s125_io2_twice_forced_fixture_control() {
    use helpers::marginal::{Child, Instrument, MarginalPair};
    let alias = "(defn counterfactual-pure [x] (primitives/pure x)) ";
    let control = format!("{alias}(defn main [] (counterfactual-pure 0))");
    let subject = format!(
        r#"{alias}(defn main [] (let [node (counterfactual-pure (primitives/str-concat "he" "llo"))] (primitives/bind node (fn [a] (primitives/bind node (fn [b] (counterfactual-pure (primitives/add-i64 (primitives/str-len a) (primitives/str-len b)))))))))"#
    );
    let measured = MarginalPair::new(
        "counterfactual twice-forced fixture",
        Child::new(&control).env("CRANELISP_RC_DEC_CHECK", "1"),
        Child::new(&subject).env("CRANELISP_RC_DEC_CHECK", "1"),
    )
    .instrument(Instrument::RcStats)
    .measure();
    assert_eq!(
        measured.control().exit_code(),
        Some(0),
        "{}",
        measured.report()
    );
    assert_eq!(
        measured.subject().exit_code(),
        Some(10),
        "{}",
        measured.report()
    );
    measured.assert_balanced("fixture executes both forces and releases its heap payload");
}
