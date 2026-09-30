//! A COW scrutinee plans like any owned temporary
//! (`design/backend/ownership-codegen.md` §13.7 "The match seam has no COW
//! rule"; §13.5 "Match scrutinee plan" row; ACT-1024, ACT-1027).
//!
//! Every COW result owns exactly one reference on every branch and path, so a
//! forwarding variable arm carries that reference out: the arm emits no
//! release, and a returned match needs no protect. A consuming arm releases the
//! scrutinee once. Each cell compiles a real body through the production
//! per-body seam over an owned `Vec Int` parameter `v`, whose own slot
//! releases once at scope exit.

use cranelisp_types::Type;

use crate::test_support::cow_site_fixture::{
    compile_f, increments, int, let_in, match_var, match_wildcard, releases, vec_len, vec_set,
    vec_ty, vec_var,
};

/// `(defn f [v] (match (vec-set v 0 5) [r r]))`: the in-place site retains
/// the reused box, and the arm forwards it as the result.
fn forwarded_and_returned(escapes: Option<bool>) -> String {
    let body = match_var(vec_set(vec_var("v")), "r", vec_var("r"), vec_ty());
    compile_f(&["v"], body, vec_ty(), escapes)
}

// spec: spec/12-runtime.md §12.3.1 — U-R3a (ACT-1027). The forwarding arm
// does not release the scrutinee, and `f`'s return adds no increment: the one
// increment is the site's retention, and the one release is `v`'s scope exit.
// The old COW exception added an arm release with no protect after it: on the
// in-place branch `v`'s scope exit then freed the returned box, and on the copy
// branch the arm freed the fresh one.
#[test]
fn a_forwarding_arm_over_a_cow_scrutinee_neither_releases_nor_protects_it() {
    let clif = forwarded_and_returned(Some(true));
    assert_eq!(
        (increments(&clif), releases(&clif)),
        (1, 1),
        "expected (retention, `v`'s scope exit) only. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.3.1 — U-R3b (ACT-1027, D2-C). `v` is read after
// the site, so it lowers to the copy extern, whose fresh box the arm forwards
// into `w`. Nothing releases it before `w` binds; `w` is the returned value,
// so the only release is `v`'s scope exit.
#[test]
fn a_forwarded_compile_time_copy_is_not_released_before_its_binder() {
    // (defn f [v] (let [w (match (vec-set v 0 5) [r r]) n (vec-len v)] w))
    let body = let_in(
        vec![
            (
                "w",
                match_var(vec_set(vec_var("v")), "r", vec_var("r"), vec_ty()),
            ),
            ("n", vec_len(vec_var("v"))),
        ],
        vec_var("w"),
        vec_ty(),
    );
    let clif = compile_f(&["v"], body, vec_ty(), Some(true));
    assert_eq!(
        releases(&clif),
        1,
        "expected `v`'s scope exit only. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — U-R3c. An arm that does not
// forward the scrutinee consumes it: a consuming variable arm and a wildcard
// arm each release the COW result once at the arm's end, beside `v`'s scope
// exit. The retention is unchanged.
#[test]
fn a_consuming_arm_over_a_cow_scrutinee_releases_it_once_neg() {
    let consuming = match_var(vec_set(vec_var("v")), "r", vec_len(vec_var("r")), Type::Int);
    let wildcard = match_wildcard(vec_set(vec_var("v")), int(0), Type::Int);
    for (label, body) in [
        ("consuming variable arm", consuming),
        ("wildcard arm", wildcard),
    ] {
        let clif = compile_f(&["v"], body, Type::Int, Some(true));
        assert_eq!(
            (increments(&clif), releases(&clif)),
            (1, 2),
            "{label}: expected (retention, arm release + `v`'s scope exit). CLIF:\n{clif}"
        );
    }
}

// spec: spec/12-runtime.md §12.3.1 — escape-axis invariance through the
// match. The plan reads ownership and arm shape only, and the site retains
// whatever the escape fact, so U-R3a's emission is identical under every fact.
#[test]
fn a_forwarded_cow_scrutinee_emits_the_same_code_under_every_escape_fact() {
    let escaping = forwarded_and_returned(Some(true));
    assert_eq!(escaping, forwarded_and_returned(Some(false)));
    assert_eq!(escaping, forwarded_and_returned(None));
}
