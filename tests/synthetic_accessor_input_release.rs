//! S123 U-12: synthetic accessors discharge their input after reading its field.
//! Concrete accessor frames previously omitted their input release.
#[path = "helpers/mod.rs"]
mod helpers;
use helpers::marginal::{Child, MarginalPair};

fn child(defs: &str, value: &str, linked: bool) -> Child {
    // ACT-1049: all constructors are inside go, never freshly placed in main.
    let c = Child::new(&format!(
        "(import [primitives [*]])\n{defs}\n\
         (defn go [n acc]\n\
           (if (eq-i64 n 0) acc\n\
             (go (add-i64 n -1) (add-i64 acc {value}))))\n\
         (defn main [] (Pure (go 100 0)))\n"
    ))
    .env("CRANELISP_RC_DEC_CHECK", "1");
    if linked { c.link_then_run() } else { c }
}

fn check(label: &str, defs: &str, control: &str, subject: &str, expected: i32, linked: bool) {
    let m = MarginalPair::new(
        label,
        child(defs, control, linked),
        child(defs, subject, linked),
    )
    .measure();
    eprintln!("{}", m.report());
    for half in [m.control(), m.subject()] {
        assert_eq!(
            half.exit_code(),
            Some(expected),
            "{}\n{}",
            m.report(),
            half.stderr
        );
    }
    m.assert_balanced(label);
}

const POINT: &str = "(deftype Point [:Int x :Int y])\n(defn py [p] (match p [(Point x y) y]))";

// spec: spec/12-runtime.md §12.3.1 — U-12 concrete scalar-field accessor, run.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_match found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn point_y_releases_its_input_run() {
    check(
        "U-12 Point.y run",
        POINT,
        "(py (Point n 7))",
        "(Point.y (Point n 7))",
        700 % 256,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-12 concrete heap-field accessor, run.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_match found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn box_items_releases_its_input_and_returned_field_run() {
    check(
        "U-12 Box.items run",
        "(deftype Box [:(Vec Int) items])\n(defn box-items [b] (match b [(Box xs) xs]))",
        "(vec-len (box-items (Box [n 2 3])))",
        "(vec-len (Box.items (Box [n 2 3])))",
        300 % 256,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-12 concrete scalar-field accessor, link.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_match found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn point_y_releases_its_input_link() {
    check(
        "U-12 Point.y link",
        POINT,
        "(py (Point n 7))",
        "(Point.y (Point n 7))",
        700 % 256,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-12 generic accessor guard.
#[test]
fn generic_y_releases_its_input_and_returned_field() {
    check(
        "U-12 generic P.y guard",
        "(deftype (P a) [:a x :a y])\n(defn py [p] (match p [(P x y) y]))",
        "(vec-len (py (P [n] [n 2])))",
        "(vec-len (P.y (P [n] [n 2])))",
        200,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-17 moves-off concrete scalar-field accessor.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_match found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn point_y_releases_its_input_moves_off() {
    let m = MarginalPair::new(
        "U-17 Point.y moves off",
        child(POINT, "(py (Point n 7))", false).env("CRANELISP_NO_OWNERSHIP", "1"),
        child(POINT, "(Point.y (Point n 7))", false).env("CRANELISP_NO_OWNERSHIP", "1"),
    )
    .measure();
    eprintln!("{}", m.report());
    for half in [m.control(), m.subject()] {
        assert_eq!(
            half.exit_code(),
            Some(700 % 256),
            "{}\n{}",
            m.report(),
            half.stderr
        );
    }
    m.assert_balanced("U-17 moves-off Point.y releases its input");
}
