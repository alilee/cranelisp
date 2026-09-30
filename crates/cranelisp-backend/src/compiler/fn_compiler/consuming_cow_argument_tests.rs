//! The consuming in-place COW argument (`design/backend/ownership-codegen.md`
//! §13.3 and the §13.5 "Consuming COW argument" row; ACT-1021).
//!
//! A top-level self-tail argument that is an in-place COW site on a frame-owned
//! parameter consumes that slot's reference. Two readers share the one fact:
//! the COW producer lowers the source `Owned`, and the parameter flush skips
//! exactly that slot. Every other COW site keeps the §13.7 classification and
//! the flush releases its source slot.
//!
//! The pure fact is pinned over its matrix: COW site × source slot × argument
//! position × toggle, plus the carrier identity. The seam cells compile
//! `(defn go [n o x y] …)` through the production per-body seam and compare
//! emission across one difference: argument order (which decides whether the
//! push is in place or copy-only), or the escape fact typecheck publishes for
//! the push. A consuming site's emission does not depend on the escape fact;
//! that independence is what the retain-verdict reading of §6 row 3 lacked.

use std::collections::HashMap;

use cranelisp_types::{
    ConcreteType, Expr, ModeSummary, MonoExpr, ResolvedCall, Span, Symbol, Type,
};

use super::tail_branch_forward_tests::{
    Form, compile, go_defn, no_site_facts, span, tail_call, tail_vec_push_does_not_escape, var,
    vec_push, vec_ty, x_borrowed,
};
use super::{
    CowSourceFacts, SlotFrame, SlotOwnershipFacts, consuming_cow_arguments,
    cow_argument_consumes_slot,
};

// ---------------------------------------------------------------------------
// The pure fact
// ---------------------------------------------------------------------------

const OWNED_PARAM: SlotOwnershipFacts = SlotOwnershipFacts {
    frame: SlotFrame::Param,
    heap: true,
    borrowed: false,
    promoted: false,
};
const PROMOTED_PARAM: SlotOwnershipFacts = SlotOwnershipFacts {
    frame: SlotFrame::Param,
    heap: true,
    borrowed: true,
    promoted: true,
};
const LET_VALUE: SlotOwnershipFacts = SlotOwnershipFacts {
    frame: SlotFrame::Local,
    heap: true,
    borrowed: false,
    promoted: false,
};

// spec: spec/12-runtime.md §12.3.1 — a COW argument consumes its source slot
// only when it lowers in place on a frame-owned parameter with analysis on. A
// copy-only site consumes nothing; a `let` slot is not a parameter slot; a
// promoted Borrowed parameter is never in place (`is_last_use` refuses a
// borrowed slot, which `a_promoted_parameter_source_is_not_consumed_neg`
// observes at the seam); toggle-off never consumes (FIXME 0695).
#[test]
fn the_consuming_fact_over_its_source_matrix() {
    // (slot, in place, analysis off) → consumes
    let table = [
        (OWNED_PARAM, true, false, true),
        (OWNED_PARAM, false, false, false),
        (OWNED_PARAM, true, true, false),
        (OWNED_PARAM, false, true, false),
        (PROMOTED_PARAM, false, false, false),
        (LET_VALUE, true, false, false),
        (LET_VALUE, false, false, false),
        (LET_VALUE, true, true, false),
    ];
    for (slot, in_place, analysis_off, consumes) in table {
        let facts = CowSourceFacts { slot, in_place };
        assert_eq!(
            cow_argument_consumes_slot(facts, analysis_off),
            consumes,
            "{facts:?}, analysis_off={analysis_off}"
        );
    }
}

fn mono_var(name: &str) -> MonoExpr {
    MonoExpr::Var {
        name: Symbol::from(name),
        span: Span::new(0, 1),
        resolved_call: None,
        resolution: cranelisp_types::VarRef::Local {
            binder: Symbol::from(name),
            binding_span: Span::SYNTHETIC,
        },
        ty: ConcreteType::Int,
    }
}

/// `(<spelled> <source> …)` resolved to the builtin `carrier`, or to a user
/// function when `carrier` is `None`.
fn cow_site(spelled: &str, source: MonoExpr, carrier: Option<&str>) -> MonoExpr {
    MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(mono_var(spelled)),
        args: vec![source, mono_var("i")],
        span: Span::new(0, 1),
        resolved_call: carrier.map(|name| {
            Box::new(ResolvedCall::BuiltinFn {
                name: Symbol::from(name),
            })
        }),
        ty: ConcreteType::Int,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

fn under_a_branch(expr: MonoExpr) -> MonoExpr {
    MonoExpr::If {
        cond: Box::new(mono_var("c")),
        then_branch: Box::new(mono_var("q")),
        else_branch: Box::new(expr),
        span: Span::new(0, 1),
        ty: ConcreteType::Int,
    }
}

/// The source names [`consuming_cow_arguments`] reports, for sources that
/// all resolve to in-place owned parameters.
fn consuming_sources(args: &[MonoExpr], analysis_off: bool) -> Vec<Symbol> {
    consuming_cow_arguments(args, analysis_off, |name, _| {
        Some((
            name.clone(),
            CowSourceFacts {
                slot: OWNED_PARAM,
                in_place: true,
            },
        ))
    })
    .into_iter()
    .map(|(_, slot)| slot)
    .collect()
}

// spec: spec/12-runtime.md §12.3.1 — the consuming site is a top-level
// argument at any position (FIXME 0691), identified by its resolution carrier
// (FIXME 0752). It is reported with its source node, which the producer keys
// on.
#[test]
fn a_top_level_cow_argument_consumes_at_any_position() {
    let push = || cow_site("vec-push", mono_var("p"), Some("vec-push"));
    let set = || cow_site("vec-set", mono_var("p"), Some("vec-set"));
    assert_eq!(consuming_sources(&[push()], false), [Symbol::from("p")]);
    assert_eq!(
        consuming_sources(&[mono_var("n"), mono_var("w"), set()], false),
        [Symbol::from("p")]
    );
    let args = [mono_var("n"), push()];
    let reported = consuming_cow_arguments(&args, false, |_, _| {
        Some((
            (),
            CowSourceFacts {
                slot: OWNED_PARAM,
                in_place: true,
            },
        ))
    });
    let MonoExpr::Apply {
        args: site_args, ..
    } = &args[1]
    else {
        unreachable!()
    };
    assert!(
        std::ptr::eq(reported[0].0, &site_args[0]),
        "the reported source is the site's own source node"
    );
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — nothing consumes a slot
// toggle-off, under a branch (lead L7), through a non-`Var` source, or through
// a call that merely spells a COW builtin.
#[test]
fn only_a_carrier_identified_top_level_site_consumes_neg() {
    let push = || cow_site("vec-push", mono_var("p"), Some("vec-push"));
    let cases = [
        ("toggle-off", vec![push()], true),
        ("under a branch", vec![under_a_branch(push())], false),
        (
            "fresh source",
            vec![cow_site(
                "vec-push",
                cow_site("vec-push", mono_var("p"), Some("vec-push")),
                Some("vec-push"),
            )],
            false,
        ),
        (
            "user fn spelled vec-set",
            vec![cow_site("vec-set", mono_var("p"), None)],
            false,
        ),
        (
            "spelled vec-set, resolved to vec-get",
            vec![cow_site("vec-set", mono_var("p"), Some("vec-get"))],
            false,
        ),
        (
            "persistent op",
            vec![cow_site("conj", mono_var("p"), Some("conj"))],
            false,
        ),
    ];
    for (label, args, analysis_off) in cases {
        assert!(
            consuming_sources(&args, analysis_off).is_empty(),
            "{label}: consumed a slot"
        );
    }
}

// ---------------------------------------------------------------------------
// The seam: the producer and the parameter flush
// ---------------------------------------------------------------------------

/// A typecheck site-fact supplier for the compiled body.
type SiteFacts = fn(&mut MonoExpr);

/// The escape-fact settings a consuming site must not depend on: absent, and
/// the `Some(false)` typecheck publishes for a result consumed by the next
/// iteration.
const SITE_FACTS: [(&str, SiteFacts); 2] = [
    ("no escape fact", no_site_facts),
    ("escapes = Some(false)", tail_vec_push_does_not_escape),
];

/// `(if n 0 x)`: a branch that forwards the parameter `x`.
fn forward_x() -> Expr {
    Form::If.wrap(var("x", &vec_ty()), &vec_ty(), &mut HashMap::new())
}

/// `(go 0 o (if n 0 x) (vec-push x 1))`: the push holds `x`'s last use, so it
/// lowers in place and consumes `x`'s slot.
fn consuming_order() -> Expr {
    tail_call(forward_x(), vec_push("x"), &vec_ty())
}

/// `(go 0 o (vec-push x 1) (if n 0 x))`: `x` is used after the push, so the
/// push lowers to the copy extern and consumes nothing.
fn copy_only_order() -> Expr {
    tail_call(vec_push("x"), forward_x(), &vec_ty())
}

fn clif(body: Expr, summary: Option<ModeSummary>, site_facts: SiteFacts) -> String {
    compile(
        &go_defn(body),
        summary,
        &vec_ty(),
        &HashMap::new(),
        site_facts,
    )
}

/// Releases through a canonical drop-glue call: every tail-jump flush release.
fn glue_releases(clif: &str) -> usize {
    crate::test_support::count_release_ops(clif) - inline_releases(clif)
}

/// Inline decrements: the COW copy block's source release.
fn inline_releases(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 sub").count()
}

fn increments(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 add").count()
}

// spec: spec/12-runtime.md §12.3.1 — the parameter flush releases a slot
// unless a top-level argument consumes it. The copy-only order releases `x`
// (its push copies and consumes nothing); the consuming order does not (its
// push takes `x`'s reference). Both orders release `y`, which the other
// argument supersedes, so the difference is exactly `x`'s flush release,
// whatever escape fact the push carries.
#[test]
fn the_flush_releases_a_copy_only_source_and_skips_a_consuming_one() {
    let mut failures = Vec::new();
    for (label, facts) in SITE_FACTS {
        let copy_only = glue_releases(&clif(copy_only_order(), None, facts));
        let consuming = glue_releases(&clif(consuming_order(), None, facts));
        if copy_only != consuming + 1 {
            failures.push(format!(
                "{label}: copy-only order {copy_only} flush releases, consuming order \
                 {consuming}; expected exactly one more (`x`) in the copy-only order"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// spec: spec/12-runtime.md §12.3.1 — a consuming site's source is `Owned`: its
// copy block releases the slot's reference and its unique block forwards the
// box with no retention increment, whatever the escape fact. The copy-only
// order emits neither (the copy extern), and both orders forward `x` through
// the same branch, so the consuming order differs by exactly one inline
// release and no increment.
#[test]
fn a_consuming_site_lowers_its_source_owned_whatever_the_escape_fact() {
    let mut failures = Vec::new();
    for (label, facts) in SITE_FACTS {
        let copy_only = clif(copy_only_order(), None, facts);
        let consuming = clif(consuming_order(), None, facts);
        let (released, released_control) =
            (inline_releases(&consuming), inline_releases(&copy_only));
        if released != released_control + 1 {
            failures.push(format!(
                "{label}: {released} inline releases, copy-only control {released_control}; \
                 expected the copy block's one source release"
            ));
        }
        let (retained, retained_control) = (increments(&consuming), increments(&copy_only));
        if retained != retained_control {
            failures.push(format!(
                "{label}: {retained} increments, copy-only control {retained_control}; \
                 expected no retention increment in the unique block"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — a promoted Borrowed parameter
// is never at its last use, so its push copies and consumes nothing. The flush
// releases the promoted slot's frame-owned reference under either escape fact.
#[test]
fn a_promoted_parameter_source_is_not_consumed_neg() {
    let body = || tail_call(vec_push("x"), var("y", &vec_ty()), &vec_ty());
    let [without, with] =
        SITE_FACTS.map(|(_, facts)| glue_releases(&clif(body(), x_borrowed(), facts)));
    assert_eq!(
        without, with,
        "the escape fact must not exempt a promoted parameter from the flush"
    );
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — the fact covers parameter
// slots only. A `let`-rooted tail push (lead L7) holds no consuming claim, so
// it keeps the §13.7 classification: `Borrowed`, retaining the reused box that
// the `let` flush then releases. The escape fact is not an input, so its
// emission is the same under both facts (ACT-1024).
#[test]
fn a_let_rooted_source_is_borrowed_whatever_the_escape_fact_neg() {
    let body = || Expr::Let {
        bindings: vec![(Symbol::from("v"), vec_push("y"))],
        body: Box::new(tail_call(vec_push("v"), var("x", &vec_ty()), &vec_ty())),
        span: span(),
        inferred_type: Some(Box::new(Type::Int)),
    };
    let [without, with] = SITE_FACTS.map(|(_, facts)| clif(body(), None, facts));
    assert_eq!(
        without, with,
        "the escape fact must not change the emission"
    );
    assert_eq!(
        increments(&with),
        2,
        "both `Var`-sourced pushes (`y` and the `let`-bound `v`) are unclaimed \
         and retain. CLIF:\n{with}"
    );
}
