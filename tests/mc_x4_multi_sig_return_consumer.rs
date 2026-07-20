// mc_x4_multi_sig_return_consumer.rs — MC-X4 (S113, /port consumer residual).
//
// A POLY Vec callee (`mycount`, `(Vec a) -> Int`) consuming a MULTI-SIG fn's bare
// `(Vec Int)` return ⇒ codegen `undefined function: mycount`. Mode-uniform
// (run+link); the two-FUNCTION control is GREEN (the §5.1.2 equivalence-divergence
// standalone-twin instrument). Concrete caller (≠ R2), consuming-the-RETURN (≠ D3),
// ADT-wrapped return dodges.
//
// P26-TEMPORAL mechanism (/qa): the multi-sig call's RESULT type settles POST-drain,
// but the consumer's mono harvest keys its instance request PRE-settlement ⇒ the
// request carries a residual Var ⇒ no ground `mycount` instance minted ⇒ loud keyed
// miss (correct consumer). Fix keys on the SETTLED ground result (§11.3.2).
// Owner /dev(typecheck), `class=carrier-loss`. Re-authored free-standing from the
// /port `probe/min.cl` + `minctl.cl` repros (stdlib `conj`/`count` → `vec-push`/
// `vec-len`). Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// `build`: a MULTI-SIG acc-threader; 1-arg entry seeds acc, 2-arg sibling pushes.
// Returns a bare `(Vec Int)`. `(build 3)` → [0 3 2 1] (4 elements).
const BUILD_MULTISIG: &str = "(defn build\n\
     \x20 ([n]     (build n [0]))\n\
     \x20 ([n acc] (if (eq-i64 n 0) acc (build (add-i64 n -1) (vec-push acc n)))))\n";

fn assert_run_and_link(user: &str, code: i32) -> [i32; 2] {
    let mut out = [0i32; 2];
    for (i, link) in [false, true].into_iter().enumerate() {
        let b = Cranelisp::new().with_prelude(PreludeVariant::PrimitivesOnly);
        let b = if link {
            b.link_then_run("user.cl")
        } else {
            b.run("user.cl")
        };
        let o = b.user(user).output();
        out[i] = o.status.code().unwrap_or(-1);
        assert_eq!(
            o.status.code(),
            Some(code),
            "[{}] expected exit {code}; got {:?}:\n{}{}",
            if link { "--link" } else { "--run" },
            o.status.code(),
            o.stdout,
            o.stderr
        );
    }
    out
}

// MC-X4 pin (RED ×run+link) — the poly `mycount` consuming the multi-sig `(Vec Int)`
// return. `(mycount (build 3))` MUST be 4; today codegen `undefined function:
// mycount` (the ground instance is never minted). Mode-uniform.
// spec: spec/05-definitions.md §5.1.2 — a poly callee consuming a multi-sig fn's
// return is monomorphised for the settled ground result type.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck consumer mono harvest keys the multi-sig call's result instance PRE-settlement (residual Var; §11.3.2 derive-at-settlement) found=S113 owner=/dev
#[test]
fn poly_consumer_of_multi_sig_return_mono_miss() {
    assert_run_and_link(
        &format!(
            "(defn mycount [v] (vec-len v))\n\
             {BUILD_MULTISIG}\
             (defn main [] (Pure (mycount (build 3))))\n"
        ),
        4,
    );
}

// MC-X4 CONTROL TWIN (GREEN) — the SAME poly consumer over a TWO-FUNCTION `build`
// (single-sig `build` delegating to a single-sig helper `bh`). The only difference
// from the pin is the multi-sig-ness of `build`; this runs to 4. The §5.1.2
// equivalence-divergence instrument: the two agree except on the multi-sig axis.
// spec: spec/05-definitions.md §5.1.2 — a poly consumer over a single-sig producer.
#[test]
fn poly_consumer_of_single_sig_return_control_green() {
    assert_run_and_link(
        "(defn mycount [v] (vec-len v))\n\
         (defn bh [n acc] (if (eq-i64 n 0) acc (bh (add-i64 n -1) (vec-push acc n))))\n\
         (defn build [n] (bh n [0]))\n\
         (defn main [] (Pure (mycount (build 3))))\n",
        4,
    );
}

// MC-X4 ADT-WRAPPED BOUNDARY FENCE (GREEN) — wrapping the multi-sig return in an
// ADT makes the consumer's request GROUND (concrete `VBox`, not a residual `(Vec
// Var)`) ⇒ the miss dodges. Guards the fix's boundary: the pin is specifically the
// bare-poly-return path, not ADT-wrapped returns.
// spec: spec/05-definitions.md §5.1.2 — an ADT-wrapped multi-sig return consumed
// via pattern match.
#[test]
fn adt_wrapped_multi_sig_return_consumer_green() {
    assert_run_and_link(
        "(deftype VBox (MkVBox [:(Vec Int) v]))\n\
         (defn mycount [b] (match b [(MkVBox v) (vec-len v)]))\n\
         (defn build\n\
         \x20 ([n]     (build n [0]))\n\
         \x20 ([n acc] (if (eq-i64 n 0) (MkVBox acc) (build (add-i64 n -1) (vec-push acc n)))))\n\
         (defn main [] (Pure (mycount (build 3))))\n",
        4,
    );
}
