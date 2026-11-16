//! The first ACT-1029 R1 probe pair (S122, `tests/plan/s122-evidence-delta.md`
//! "ACT-1029 R1 probe — T0 control fault and redesigned delta").
//!
//! The outer `(match q [alias …])` views `q`'s box. The tail argument
//! `(let [t (match p [X X])] alias)` forwards the outer `alias` as the new `q`,
//! so the push on `q` is not at `q`'s last use and must copy. The halves differ
//! only in the inner binder `X`: `b` (control) or `alias` (subject). Under value
//! semantics both compute 3: each step makes `p` = [9 1] and keeps `q` = [9].
//!
//! Both halves carried the `let`-wrapped tail argument, and the control stopped
//! armed with `USE-AFTER-FREE` before the subject ran (ACT-1030). U′ removed
//! the fault; both halves then returned 3 and balanced. The L6 cell separately
//! isolated the let-wrapped forwarding face (ACT-1031).

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
// when a self-tail argument forwards a `match`-binder alias through a `let`.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call found=S122 owner=/dev fixed=S123/3bdf398e
#[test]
fn push_under_a_same_name_shadowed_match_binder_balances() {
    let pair = MarginalPair::new(
        "(vec-push q 1) beside a let-wrapped tail argument forwarding q's match binder",
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
    pair.assert_balanced("the push beside a let-wrapped tail argument");
}
