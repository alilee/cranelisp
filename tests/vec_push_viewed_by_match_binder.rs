//! A `vec-push` on a vector that a variable-pattern `match` binder still views
//! (S122, ACT-1021 final intake, `tests/plan/s122-evidence-delta.md`
//! "ACT-1021 amendment — final intake").
//!
//! `(match q [alias …])` binds `alias` to `q`'s box without counting a
//! reference. A push on `q` whose only later use is through `alias` must copy:
//! `q` is not at its last use, and the pushed value must not be visible
//! through `alias`. A-T is the self-tail face, measured armed; A-V is the
//! non-tail value face.
//!
//! On 2026-09-30 (source diff `ab8004af…` over `e4062202`) the push took the
//! in-place core. A-T's subject stopped armed with `USE-AFTER-FREE` in
//! `vec_push_copy(src)` on a buffer freed by `vec_drop`, while the control
//! balanced; `go` is `modes=[Copy, Borrowed, Owned]` with `Consumed` flow in
//! both halves (`CRANELISP_OWNERSHIP_TRACE`). A-V read 2 under the REPL and
//! `--run`, and the linked executable aborted in glibc.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{PreludeVariant, run_through_all_modes};
use helpers::marginal::{Child, MarginalPair};

/// Three steps from `p` = [1] and `q` = [9]. Each step pushes onto `q` into
/// the new `p` and passes `forward` as the new `q`; the base case returns
/// `len p + len q`. Under value semantics `q` stays [9] and `p` becomes
/// [9 1], so either `forward` computes 3.
fn alias_loop(forward: &str) -> Child {
    Child::new(&format!(
        "(import [primitives [Pure add-i64 eq-i64 vec-len vec-push]])\n\
         (defn go [n p q]\n\
           (if (eq-i64 n 0)\n\
               (add-i64 (vec-len p) (vec-len q))\n\
               (match q [alias (go (add-i64 n -1) (vec-push q 1) {forward})])))\n\
         (defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))\n"
    ))
    .env("CRANELISP_RC_DEC_CHECK", "1")
}

// spec: spec/12-runtime.md §12.3.1 — a vector viewed by a variable-pattern
// `match` binder that is forwarded to a self-tail call keeps its value, and
// every reference is released exactly once.
//
// A-T. The control forwards `q` itself, a direct later use, so its push
// copies; the subject forwards the binder `alias`.
// defect: class=enumeration-miss locus=crates/cranelisp-backend/src/heap.rs::compute_last_uses found=S122 owner=/dev
#[test]
fn push_on_a_vector_forwarded_through_a_match_binder_balances() {
    let pair = MarginalPair::new(
        "(vec-push q 1) with q forwarded through a match binder",
        alias_loop("q"),
        alias_loop("alias"),
    )
    .measure();
    assert!(
        pair.control().exit_code() == Some(3) && pair.subject().exit_code() == Some(3),
        "both halves must exit 3\n{}\n--- control stderr ---\n{}\n--- subject stderr ---\n{}",
        pair.report(),
        pair.control().stderr,
        pair.subject().stderr
    );
    pair.assert_balanced("the push beside a match-binder alias");
}

// spec: spec/12-runtime.md §12.3.3 — a `vec-push` on a vector a `match`
// binder still views leaves the binder's value unchanged.
//
// A-V. `v` is `let`-bound, so its frame owns it; `a` views the same box. The
// push's result `w` is unused. An in-place push would make `a` read 2.
#[test]
fn push_on_a_vector_viewed_by_a_match_binder_leaves_the_binder_unchanged() {
    run_through_all_modes(
        "(import [primitives [Pure vec-len vec-push]])\n\
         (defn main []\n\
           (Pure (let [v (vec-push [] 9)]\n\
                   (match v [a (let [w (vec-push v 1)] (vec-len a))]))))\n",
        PreludeVariant::None,
    )
    .assert_all_equal(1);
}
