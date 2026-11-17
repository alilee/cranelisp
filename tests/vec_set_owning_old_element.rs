//! S123 U-11: replacement must release the old element's entire owned graph.
//! In-place replacement previously released owning old elements only shallowly.
#[path = "helpers/mod.rs"]
mod helpers;
use helpers::marginal::{Child, Marginal, MarginalPair};

fn child(body: &str, linked: bool) -> Child {
    let c = Child::new(&format!(
        "(import [primitives [*]])\n\
         (deftype B (MkB [:String s]))\n\
         (defn ap [f v i x] (f v i x))\n\
         (defn work [] {body})\n(defn main [] (Pure (work)))\n"
    ))
    .env("CRANELISP_RC_DEC_CHECK", "1");
    if linked { c.link_then_run() } else { c }
}

fn measure(label: &str, control: &str, subject: &str, expected: i32, linked: bool) -> Marginal {
    let m = MarginalPair::new(label, child(control, linked), child(subject, linked)).measure();
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
    m
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-11 Vec element, run.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_set_in_place found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn replacing_the_last_reference_to_a_vec_element_releases_its_contents_run() {
    measure(
        "U-11 Vec run",
        "(vec-len [[\"new\"]])",
        "(vec-len (vec-set [[\"old\"]] 0 [\"new\"]))",
        1,
        false,
    )
    .assert_balanced("U-11 Vec old element's owned graph is released");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-11 ADT element, run.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_set_in_place found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn replacing_the_last_reference_to_an_adt_element_releases_its_field_run() {
    measure(
        "U-11 ADT run",
        "(vec-len [(MkB \"new\")])",
        "(vec-len (vec-set [(MkB \"old\")] 0 (MkB \"new\")))",
        1,
        false,
    )
    .assert_balanced("U-11 ADT old element's owned field is released");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-11 value-position wrapper.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_set_in_place found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn vec_set_as_a_value_releases_the_old_elements_contents_run() {
    measure(
        "U-11 value position run",
        "(vec-len (ap vec-set [\"old\"] 0 \"new\"))",
        "(vec-len (ap vec-set [[\"old\"]] 0 [\"new\"]))",
        1,
        false,
    )
    .assert_balanced("U-11 value-position old element's owned graph is released");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-11 Vec element, link.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_set_in_place found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn replacing_the_last_reference_to_a_vec_element_releases_its_contents_link() {
    measure(
        "U-11 Vec link",
        "(vec-len [[\"new\"]])",
        "(vec-len (vec-set [[\"old\"]] 0 [\"new\"]))",
        1,
        true,
    )
    .assert_balanced("U-11 linked Vec old element's owned graph is released");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-11 flat-element guard.
#[test]
fn replacing_a_flat_string_element_balances() {
    measure(
        "U-11 flat guard",
        "(vec-len [\"new\"])",
        "(vec-len (vec-set [\"old\"] 0 \"new\"))",
        1,
        false,
    )
    .assert_balanced("flat old elements are released");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-11 shared-old Vec guard.
#[test]
fn replacing_a_shared_vec_element_keeps_its_contents_live() {
    measure("U-11 shared-old Vec guard",
        "(let [old [\"old\"] v [[\"new\"]]] (add-i64 (vec-len v) (str-len (vec-get old 0))))",
        "(let [old [\"old\"] v (vec-set [old] 0 [\"new\"]) ] (add-i64 (vec-len v) (str-len (vec-get old 0))))", 4, false)
        .assert_balanced("a shared old Vec survives replacement and is later released");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-11 shared-old ADT guard.
#[test]
fn replacing_a_shared_adt_element_keeps_its_field_live() {
    measure("U-11 shared-old ADT guard",
        "(let [old (MkB \"old\") v [(MkB \"new\")]] (add-i64 (vec-len v) (match old [(MkB s) (str-len s)])))",
        "(let [old (MkB \"old\") v (vec-set [old] 0 (MkB \"new\"))] (add-i64 (vec-len v) (match old [(MkB s) (str-len s)])))", 4, false)
        .assert_balanced("a shared old ADT survives replacement and is later released");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — U-17 moves-off Vec replacement.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_set_in_place found=S123 owner=/dev fixed=S123/3bdf398e
#[test]
fn replacing_the_last_reference_to_a_vec_element_releases_its_contents_moves_off() {
    let m = MarginalPair::new(
        "U-17 Vec moves off",
        child("(vec-len [[\"new\"]])", false).env("CRANELISP_NO_OWNERSHIP", "1"),
        child("(vec-len (vec-set [[\"old\"]] 0 [\"new\"]))", false)
            .env("CRANELISP_NO_OWNERSHIP", "1"),
    )
    .measure();
    eprintln!("{}", m.report());
    for half in [m.control(), m.subject()] {
        assert_eq!(half.exit_code(), Some(1), "{}\n{}", m.report(), half.stderr);
    }
    m.assert_balanced("U-17 moves-off Vec old element's owned graph is released");
}
