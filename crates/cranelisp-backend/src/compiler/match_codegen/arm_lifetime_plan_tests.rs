//! S118 slice S3 — the per-arm scrutinee lifetime plan
//! (`design/backend/transitive-drop-glue.md` §5, §10 row 5).
//!
//! [`super::scrutinee_lifetime_for_arm`] is pure over `(owned, cow_retains,
//! arm)`, so the whole rule is exercised without a live `FnCompiler` — the
//! `is_fresh_construction` / `cow_site_source` precedent. Two properties carry
//! the defects this slice closes:
//!
//! - the answer is **per arm**, so a sibling var arm's forwarding cannot
//!   suppress a constructor arm's release (FIXME 0726's mixed-arm leak);
//! - the ownership half comes from ONE recorded answer, so constructor and var
//!   patterns are never on different owners for the same lifetime event
//!   (FIXME 0782's double release).

use cranelisp_types::{ConcreteType, MonoExpr, MonoMatchArm, Pattern, Span, Symbol, VarRef};

use super::{ScrutineeLifetime, scrutinee_lifetime_for_arm};

fn var(name: &str) -> MonoExpr {
    MonoExpr::Var {
        resolution: VarRef::Local {
            binder: Symbol::from(name),
            binding_span: Span::SYNTHETIC,
        },
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

fn int(v: i64) -> MonoExpr {
    MonoExpr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    }
}

fn arm(pattern: Pattern, body: MonoExpr) -> MonoMatchArm {
    MonoMatchArm {
        pattern,
        body,
        span: Span::SYNTHETIC,
        provenance: None,
        resolved_ctor: None,
    }
}

/// `[r r]` — a var arm that forwards the whole scrutinee.
fn forwarding_var_arm() -> MonoMatchArm {
    arm(
        Pattern::Var {
            name: Symbol::from("r"),
            span: Span::SYNTHETIC,
        },
        var("r"),
    )
}

/// `[xs (…)]` — a var arm that binds the scrutinee but yields something else.
fn consuming_var_arm() -> MonoMatchArm {
    arm(
        Pattern::Var {
            name: Symbol::from("xs"),
            span: Span::SYNTHETIC,
        },
        int(1),
    )
}

/// `[(Jus g2) …]` — a constructor arm. It binds FIELDS, so it can never name
/// (and therefore never forward) the wrapper.
fn ctor_arm() -> MonoMatchArm {
    arm(
        Pattern::Constructor {
            name: cranelisp_types::SymbolRef::new(None, Symbol::from("Jus")),
            bindings: vec![Symbol::from("g2")],
            span: Span::SYNTHETIC,
        },
        var("g2"),
    )
}

// spec: spec/06-pattern-matching.md §6.2.1 — a scrutinee owned elsewhere is
// released by its owner. The plan is `Borrowed` for EVERY arm shape: no arm of
// a borrowed match releases the wrapper, and no pattern kind changes that.
#[test]
fn a_borrowed_scrutinee_is_never_released_by_any_arm_neg() {
    for a in [forwarding_var_arm(), consuming_var_arm(), ctor_arm()] {
        assert_eq!(
            scrutinee_lifetime_for_arm(false, false, &a),
            ScrutineeLifetime::Borrowed,
            "{:?}",
            a.pattern
        );
    }
}

// spec: spec/12-runtime.md §12.3.1 — an arm that forwards the whole scrutinee
// carries the one owner out; releasing it here would free a value that travels
// (the `[r r]` control that must stay green).
#[test]
fn a_forwarding_var_arm_over_an_owned_temporary_transfers_the_owner() {
    assert_eq!(
        scrutinee_lifetime_for_arm(true, false, &forwarding_var_arm()),
        ScrutineeLifetime::OwnedForwarded
    );
}

// spec: spec/12-runtime.md §12.3.1 / FIXME 0782 — a var arm that CONSUMES the
// temporary releases it exactly once, at the arm's end. The binder itself is a
// borrow; it is never a second release owner.
#[test]
fn a_consuming_var_arm_releases_the_owned_temporary() {
    assert_eq!(
        scrutinee_lifetime_for_arm(true, false, &consuming_var_arm()),
        ScrutineeLifetime::OwnedConsumed
    );
}

// spec: spec/12-runtime.md §12.3.1 / FIXME 0726 — THE mixed-arm cell. The plan
// is decided per arm, so the constructor path of a match whose sibling var arm
// forwards still releases the temporary it genuinely consumed. HEAD asked
// `arms.iter().any(|a| a forwards)` and suppressed the release on EVERY path.
#[test]
fn a_ctor_arm_still_releases_when_a_sibling_var_arm_forwards() {
    // The mixed match, as `compile_match` sees it: one ctor arm, one forwarding
    // var default. The `any`-arm approximation answers "forwards" for the whole
    // match; the per-arm plan answers each arm on its own terms.
    let arms = [ctor_arm(), forwarding_var_arm()];
    assert!(
        crate::compiler::fn_compiler::match_forwards_scrutinee(&arms),
        "precondition: the whole-match approximation would say this match forwards"
    );
    assert_eq!(
        scrutinee_lifetime_for_arm(true, false, &arms[0]),
        ScrutineeLifetime::OwnedConsumed,
        "the ctor path consumed the temporary; a sibling arm's forwarding is \
         not its business"
    );
    assert_eq!(
        scrutinee_lifetime_for_arm(true, false, &arms[1]),
        ScrutineeLifetime::OwnedForwarded,
        "and the var path still transfers, so the fix is not 'release everywhere'"
    );
}

// spec: spec/12-runtime.md §12.3.1 (§13.7 escape gate) — the COW exception
// travels PER ARM and keeps its polarity: when the producer emitted the
// retention inc on the reused pointer, this release is its balancing dec and
// MUST fire, even on the arm that forwards. It is the dec side of one gate,
// never an independent exemption.
#[test]
fn the_cow_retain_exception_forces_a_release_on_a_forwarding_arm() {
    assert_eq!(
        scrutinee_lifetime_for_arm(true, true, &forwarding_var_arm()),
        ScrutineeLifetime::OwnedConsumed
    );
    // ... and it cannot manufacture a release out of a BORROWED scrutinee: the
    // ownership answer is recorded once and dominates.
    assert_eq!(
        scrutinee_lifetime_for_arm(false, true, &forwarding_var_arm()),
        ScrutineeLifetime::Borrowed
    );
}
