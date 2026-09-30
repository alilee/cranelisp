//! The §13.7 two-state COW source classification at the producer
//! (`design/backend/ownership-codegen.md` §13.7; §13.5 "COW cores" row;
//! ACT-1024).
//!
//! A `Var` source is `Owned` only when its exact site holds the consuming
//! claim; every other `Var` source is `Borrowed` and retains the reused box on
//! the mutate and grow branches. The escape fact is not an input. Each cell
//! compiles a real body through the production per-body seam. With `Int`
//! elements the only increment a COW site can emit is that retention, and only
//! an `Owned` source's copy block releases inline.

use cranelisp_types::Type;

use crate::test_support::cow_site_fixture::{
    compile_f, empty_vec, increments, let_in, vec_len, vec_push, vec_push_of, vec_set, vec_ty,
    vec_var,
};

const ESCAPE_FACTS: [Option<bool>; 3] = [Some(true), Some(false), None];

/// Inline decrements: an `Owned` source's copy-block release, or an inline
/// op's temporary release.
fn inline_releases(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 sub").count()
}

/// `(defn f [v] (vec-len (<op> v …)))`: an unclaimed `Var` source at its last
/// use, whose result an in-frame inline op consumes.
fn consumed_in_frame(set: bool, escapes: Option<bool>) -> String {
    let site = if set {
        vec_set(vec_var("v"))
    } else {
        vec_push(vec_var("v"), 0)
    };
    compile_f(&["v"], vec_len(site), Type::Int, escapes)
}

// spec: spec/12-runtime.md §12.3.1 — the producer cell (ACT-1024). An
// unclaimed `Var` source is `Borrowed`: the mutate (`vec-set`) and unique
// (`vec-push`, covering fast and grow) blocks retain the reused box even when
// the site's result stays in the frame (`escapes = Some(false)`), because the
// in-frame consumer and the source slot each release one reference.
#[test]
fn an_unclaimed_var_source_retains_the_reused_box_when_its_result_stays_in_frame() {
    for set in [true, false] {
        let clif = consumed_in_frame(set, Some(false));
        assert_eq!(
            increments(&clif),
            1,
            "set={set}: expected the one retention increment. CLIF:\n{clif}"
        );
        assert_eq!(
            inline_releases(&clif),
            1,
            "set={set}: expected only the inline op's temporary release; a \
             `Borrowed` copy block releases nothing. CLIF:\n{clif}"
        );
    }
}

// spec: spec/12-runtime.md §12.3.1 — escape-axis invariance. The escape fact
// is not an input to the classification, so an unclaimed site's emission is
// byte-identical under every fact, including a `Var` in a nested operand of a
// claimed site.
#[test]
fn an_unclaimed_site_emits_the_same_code_under_every_escape_fact() {
    // (defn f [v w] (vec-push v (vec-len (vec-push w 1))))
    let nested = |escapes| {
        let inner = vec_len(vec_push(vec_var("w"), 1));
        compile_f(
            &["v", "w"],
            vec_push_of(vec_var("v"), inner),
            vec_ty(),
            escapes,
        )
    };
    for set in [true, false] {
        let [t, f, n] = ESCAPE_FACTS.map(|e| consumed_in_frame(set, e));
        assert_eq!(t, f, "set={set}: Some(true) vs Some(false)");
        assert_eq!(t, n, "set={set}: Some(true) vs absent");
    }
    let [t, f, n] = ESCAPE_FACTS.map(nested);
    assert_eq!(t, f, "nested operand: Some(true) vs Some(false)");
    assert_eq!(t, n, "nested operand: Some(true) vs absent");
    assert_eq!(
        increments(&t),
        1,
        "the nested `w` site does not inherit the enclosing site's claim. CLIF:\n{t}"
    );
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — lead L8. A `let` binder
// shadowing the return-COW source's name takes no `Owned` lowering from the
// claim. In this shape its site is never at its last use (the outer source's
// direct `Var` counts as the name's later use), so it copies: no retention
// anywhere, and exactly three inline releases — the fresh `[]` site's and the
// claimed outer site's copy blocks, and `vec-len`'s temporary. The claim's
// node key itself is pinned at the issuer (`return_cow_source_tests`).
#[test]
fn a_binder_shadowing_the_return_cow_source_is_not_claimed_neg() {
    // (defn f [v] (vec-push v (let [v (vec-push [] 2)] (vec-len (vec-push v 3)))))
    let inner = let_in(
        vec![("v", vec_push(empty_vec(), 2))],
        vec_len(vec_push(vec_var("v"), 3)),
        Type::Int,
    );
    let body = vec_push_of(vec_var("v"), inner);
    let clif = compile_f(&["v"], body, vec_ty(), None);
    assert_eq!(
        (increments(&clif), inline_releases(&clif)),
        (0, 3),
        "expected no retention and three inline releases. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — a claimed site keeps its
// emission. The function-body return-COW site takes its source slot's
// reference: its mutate branch transfers (no increment) and its copy block
// releases the source, under every escape fact. (The self-tail issuer's
// negative leg is `consuming_cow_argument_tests`.)
#[test]
fn the_return_cow_site_is_owned_under_every_escape_fact_neg() {
    for set in [true, false] {
        for escapes in ESCAPE_FACTS {
            let body = if set {
                vec_set(vec_var("v"))
            } else {
                vec_push(vec_var("v"), 1)
            };
            let clif = compile_f(&["v"], body, vec_ty(), escapes);
            assert_eq!(
                (increments(&clif), inline_releases(&clif)),
                (0, 1),
                "set={set} escapes={escapes:?}: expected no retention and the \
                 copy block's source release. CLIF:\n{clif}"
            );
        }
    }
}
