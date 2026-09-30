//! A `match` binder shadowed by a same-name `match` binder over a different
//! vector (S122, ACT-1029 R1 probe, `tests/plan/s122-evidence-delta.md`
//! "ACT-1029 R1 probe — settled handoff").
//!
//! The outer `(match q [alias …])` views `q`'s box; an inner
//! `(match p [alias alias])` in the tail argument binds a second `alias` over
//! `p`. The outer `alias` is still forwarded as the new `q`, so the push on `q`
//! is not at `q`'s last use and must copy. The control renames only the inner
//! binder, so a difference between the halves is attributable to the shared
//! name alone. Under value semantics both halves compute 3: each step makes
//! `p` = [9 1] and keeps `q` = [9].

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, MarginalPair};

fn shadowed_alias_loop(inner_binder: &str) -> Child {
    Child::new(&format!(
        "(import [primitives [Pure add-i64 eq-i64 vec-len vec-push]])\n\
         (defn go [n p q]\n\
           (if (eq-i64 n 0)\n\
               (add-i64 (vec-len p) (vec-len q))\n\
               (match q [alias\n\
                 (go (add-i64 n -1)\n\
                     (vec-push q 1)\n\
                     (let [t (match p [{inner_binder} {inner_binder}])] alias))])))\n\
         (defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))\n"
    ))
    .env("CRANELISP_RC_DEC_CHECK", "1")
}

// spec: spec/12-runtime.md §12.3.1 — every reference is released exactly once
// when a vector viewed by a `match`-binder alias is shadowed by a same-name
// alias over a different root.
// defect: class=binder-name-underkey locus=crates/cranelisp-backend/src/heap.rs::register_alias found=S122 owner=/design
#[test]
fn push_under_a_same_name_shadowed_match_binder_balances() {
    let pair = MarginalPair::new(
        "(vec-push q 1) with q's match binder shadowed by a same-name binder over p",
        shadowed_alias_loop("b"),
        shadowed_alias_loop("alias"),
    )
    .measure();
    assert!(
        pair.control().exit_code() == Some(3) && pair.subject().exit_code() == Some(3),
        "both halves must exit 3\n{}\n--- control stderr ---\n{}\n--- subject stderr ---\n{}",
        pair.report(),
        pair.control().stderr,
        pair.subject().stderr
    );
    pair.assert_balanced("the push beside a same-name shadowed match binder");
}
