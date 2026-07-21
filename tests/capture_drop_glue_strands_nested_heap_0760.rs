// capture_drop_glue_strands_nested_heap_0760.rs — S115 W3c, FIXME 0760 repros.
//
// THREE FAILING-NOT-IGNORED REPROS (open defects) plus their GREEN controls.
//
// The S115 W3/W3b sweep closed three faces of one class — "a release that frees
// the box and strands what the box owns" — by routing every release site onto ONE
// type-directed `rc_emission::emit_typed_rc_dec` (Vec → `vec_drop` + per-element
// dec; ADT → recursive inline glue; `Fn` → the box's embedded `DROP_GLUE_PTR`).
// TWO faces of the same class survive, both measured by `/dev`(backend) at W3b
// HEAD and, until this file, recorded ONLY as prose in FIXME 0760:
//
//   1. THE CAPTURE GLUE'S NON-CLOSURE CASES. `lambda.rs::emit_capture_dec_glue`
//      builds its body in a SEPARATE Cranelift context, so it cannot call the
//      `&mut self` type-directed release; a capture that is a Vec-of-heap or an
//      ADT-with-heap-fields still takes a bare `heap::emit_rc_dec(.., None)` and
//      strands the nested heap. Measured: K (closure capturing a Vec of Strings)
//      leaks 2/iteration, L (closure capturing an ADT with a String field) leaks
//      1/iteration — both toggle-INDEPENDENT.
//
//   2. THE INLINE-GLUE DEPTH TRUNCATION. `rc_emission.rs:496`
//      `MAX_DROP_GLUE_DEPTH = 4` falls back to a plain dec past the limit, and its
//      own comment already admits "fields leak" there. Measured here for the first
//      time: the cliff is EXACTLY at nesting depth 5 — depth ≤ 4 balances, depth 5
//      leaks 1/iteration (the leaf String), depth 6 leaks 2/iteration (the depth-5
//      box AND the String). Also toggle-independent. This is the SECOND,
//      independent instance of the class named in 0760's proposed resolution (b).
//
// Both faces flip when `/design`(backend) rules FIXME 0760 — (a) borrowed-builder
// parameterisation of the type-directed release, or (b) per-type named drop-glue
// FUNCTIONS called from every release site, which collapses the depth truncation
// too — and `/dev`(backend) implements it. These tests are the acceptance pins.
//
// Provenance: /sprint W3c addendum (the user asked whether the exemplar-uncovered
// leak was reproduced free-standing). It was not: the surviving faces existed only
// as measurements in a FIXME. The nested exemplar shape itself — an ADT whose field
// is a Vec of ADTs, the `solve-range` shape — is pinned below and is GREEN.
//
// Serial (`CRANELISP_NO_LENIENT=1`). PrimitivesOnly, free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// The 100-iteration driver: a per-closure leak shows as ~N missing deallocs.
const DRIVER: &str = "(defn go [n acc] (if (eq-i64 n 0) acc \
     (go (sub-i64 n 1) (add-i64 acc (one)))))\n\
     (defn main [] (Pure (go 100 0)))\n";

fn rc_balance(src: &str, ownership_off: bool) -> (i64, i64) {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1");
    if ownership_off {
        b = b.env("CRANELISP_NO_OWNERSHIP", "1");
    }
    let out = b.output();
    let line = out
        .stderr
        .lines()
        .rev()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line:\n{}", out.stderr))
        .to_string();
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            .unwrap_or_else(|| panic!("no {k} in: {line}"))
    };
    (field("allocs="), field("deallocs="))
}

/// Assert EXACT balance in BOTH ownership-toggle states. Every shape in this file
/// is toggle-independent, so a divergence between the two states would itself be
/// news — the assertion states the invariant, not the current numbers.
fn assert_balanced(shape: &str, src: &str) {
    for ownership_off in [false, true] {
        let (allocs, deallocs) = rc_balance(src, ownership_off);
        let toggle = if ownership_off {
            "CRANELISP_NO_OWNERSHIP=1"
        } else {
            "ownership analysis ON"
        };
        assert_eq!(
            allocs, deallocs,
            "{shape} ({toggle}) MUST balance exactly: allocs={allocs} \
             deallocs={deallocs} (residue {}). A release must reach everything the \
             released value owns.",
            allocs - deallocs
        );
    }
}

// The nesting-depth family: `(W1 (W2 ... (Wd "hello")))` passed to a function that
// ignores it, so the whole chain is released at the call boundary.
fn nested_chain(depth: usize) -> String {
    let mut defs = String::new();
    let mut open = String::new();
    let mut close = String::new();
    for i in 1..=depth {
        defs.push_str(&format!("(deftype T{i} (W{i} [f]))\n"));
        open.push_str(&format!("(W{i} "));
        close.push(')');
    }
    format!("{defs}(defn peek [x] 7)\n(defn one [] (peek {open}\"hello\"{close}))\n{DRIVER}")
}

// =============================================================================
// Face 1 — the capture glue's non-closure cases (FIXME 0760, RED)
// =============================================================================

// K (RED) — a closure capturing a Vec of Strings. The capture drop glue bare-decs
// the vec: the vec's own box is freed but its two element Strings are stranded, so
// the program leaks 2 objects per closure created. Measured at W3b HEAD:
// allocs=401 deallocs=201, identical under both ownership toggles.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::emit_capture_dec_glue — non-closure capture takes a bare dec, stranding a Vec's elements (FIXME 0760; blocked on the /design(backend) borrowed-builder-vs-named-glue ruling) found=S115 owner=/dev
#[test]
fn closure_capturing_vec_of_strings_does_not_leak() {
    let src = format!(
        "(defn mk [] (let [v [\"aa\" \"bbb\"]] \
           (fn [c] (add-i64 c (str-len (vec-get v 0))))))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("K (closure capturing a Vec of Strings)", &src);
}

// L (RED) — a closure capturing an ADT with a String field. Same seam, the ADT arm:
// the `Wr` box is freed, its String field is stranded — 1 leaked object per closure.
// Measured at W3b HEAD: allocs=301 deallocs=201, both toggles.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::emit_capture_dec_glue — non-closure capture takes a bare dec, stranding an ADT's heap field (FIXME 0760) found=S115 owner=/dev
#[test]
fn closure_capturing_adt_with_string_field_does_not_leak() {
    let src = format!(
        "(deftype W (Wr [s]))\n\
         (defn mk [] (let [w (Wr \"hello\")] \
           (fn [c] (add-i64 c (match w [(Wr s) (str-len s)])))))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("L (closure capturing an ADT with a String field)", &src);
}

// CONTROLS (GREEN) — the capture positions that ARE exact, which is what localises
// the defect to the non-closure arm of the capture glue rather than to captures in
// general: a plain Vec of scalars (nothing nested to strand, 201/201) and a
// captured CLOSURE that itself captures a String (301/301 — the W3b `ClosureBox`
// arm routes through the box's embedded drop glue).
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
#[test]
fn closure_capture_controls_balance_green() {
    let vec_of_scalars = format!(
        "(defn mk [] (let [v [1 2]] (fn [c] (add-i64 c (vec-get v 0)))))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("control (capture a Vec of scalars)", &vec_of_scalars);

    let closure_capture = format!(
        "(defn mk [] (let [s \"hello\"] \
           (let [g (fn [b] (add-i64 b (str-len s)))] (fn [c] (g c)))))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("control (capture a closure that captures a String)", &closure_capture);
}

// CONTROLS (GREEN) — the POSITION twins of K and L: the identical values passed as
// `Borrowed` ARGUMENTS instead of captured. These route through the W3b
// `emit_post_call_decs` arm, which DOES use the type-directed release, and they
// balance exactly. Same value, same nesting, one axis changed — the twin fixture
// that names the seam (`tests/CLAUDE.md` §"Coverage by definition variants").
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
#[test]
fn borrowed_argument_twins_of_k_and_l_balance_green() {
    let vec_arg = format!(
        "(defn use [v c] (add-i64 c (str-len (vec-get v 0))))\n\
         (defn one [] (let [v [\"aa\" \"bbb\"]] (use v 2)))\n{DRIVER}"
    );
    assert_balanced("control (Vec of Strings as a Borrowed argument)", &vec_arg);

    let adt_arg = format!(
        "(deftype W (Wr [s]))\n\
         (defn use [w c] (add-i64 c (match w [(Wr s) (str-len s)])))\n\
         (defn one [] (let [w (Wr \"hello\")] (use w 2)))\n{DRIVER}"
    );
    assert_balanced("control (ADT with a String field as a Borrowed argument)", &adt_arg);
}

// =============================================================================
// The nested exemplar shape (GREEN) — deeper than the 0753 reduced shape
// =============================================================================

// The `solve-range` shape from the f4_sudoku golden drift: an ADT whose field is a
// Vec of ADTs — one level deeper than the 0753 reduced `(Pure (peek (Gr [5 5])))`
// pinned in `rc_escape_release_0763.rs`. GREEN in both toggles, with a scalar leaf
// (401/401) and with a String leaf (601/601): the W3b type-directed release recurses
// through ADT → Vec → ADT → String correctly. Pinned because "the fix handles the
// depth" is a claim, and this is the shape the exemplar actually exercises.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
#[test]
fn adt_wrapping_vec_of_adts_balances_green() {
    let scalar_leaf = format!(
        "(deftype C (Cell [v]))\n\
         (deftype G (Gr [cells]))\n\
         (defn peek [g] (match g [(Gr cs) (match (vec-get cs 0) [(Cell v) v])]))\n\
         (defn one [] (peek (Gr [(Cell 5) (Cell 6)])))\n{DRIVER}"
    );
    assert_balanced("nested (ADT → Vec of ADTs → scalar)", &scalar_leaf);

    let string_leaf = format!(
        "(deftype C (Cell [s]))\n\
         (deftype G (Gr [cells]))\n\
         (defn peek [g] (match g [(Gr cs) (match (vec-get cs 0) [(Cell s) (str-len s)])]))\n\
         (defn one [] (peek (Gr [(Cell \"aa\") (Cell \"bbb\")])))\n{DRIVER}"
    );
    assert_balanced("nested (ADT → Vec of ADTs → String)", &string_leaf);
}

// =============================================================================
// Face 2 — the MAX_DROP_GLUE_DEPTH truncation (RED)
// =============================================================================

// CONTROL (GREEN) — nesting depth 1..4 is exact: `(W1 (W2 (W3 (W4 "hello"))))`
// balances at every depth up to the inline-glue limit (201/201, 301/301, 401/401,
// 501/501). The lower half of the cliff; it must stay green when the truncation is
// removed, so a fix cannot trade the deep face for the shallow one.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
#[test]
fn nested_adt_chain_up_to_glue_depth_limit_balances_green() {
    for depth in 1..=4 {
        assert_balanced(&format!("nested chain depth {depth}"), &nested_chain(depth));
    }
}

// RED — past `MAX_DROP_GLUE_DEPTH = 4` the inline drop glue falls back to a plain
// dec and the remaining fields leak, exactly as the constant's own comment admits.
// The cliff is at depth 5: depth 5 leaks 1/iteration (601/501 — the leaf String),
// depth 6 leaks 2/iteration (701/501 — the depth-5 box AND the String), i.e. the
// leak grows with every level past the limit. Toggle-independent.
//
// Both depths are asserted in ONE test (one defect, one record) and BOTH residues
// are reported before failing, so the fix can be verified against the shape of the
// leak, not just its presence.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs:496 MAX_DROP_GLUE_DEPTH=4 inline-glue truncation falls back to a plain dec and strands every field past the limit (FIXME 0760 resolution (b) collapses this face) found=S115 owner=/dev
#[test]
fn nested_adt_chain_past_glue_depth_limit_does_not_leak() {
    let mut residues: Vec<(usize, bool, i64, i64)> = Vec::new();
    for depth in [5usize, 6] {
        for ownership_off in [false, true] {
            let (allocs, deallocs) = rc_balance(&nested_chain(depth), ownership_off);
            residues.push((depth, ownership_off, allocs, deallocs));
        }
    }
    let leaking: Vec<String> = residues
        .iter()
        .filter(|(_, _, a, d)| a != d)
        .map(|(depth, off, a, d)| {
            format!("depth {depth} (NO_OWNERSHIP={off}): {a}/{d}, residue {}", a - d)
        })
        .collect();
    assert!(
        leaking.is_empty(),
        "a nested ADT chain deeper than MAX_DROP_GLUE_DEPTH MUST still release every \
         level: {}. The inline drop glue truncates at depth 4 and plain-decs the \
         rest, so the leak grows one object per level past the limit.",
        leaking.join("; ")
    );
}
