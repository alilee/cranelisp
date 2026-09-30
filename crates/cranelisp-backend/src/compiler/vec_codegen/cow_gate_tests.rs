//! The §13.7 COW source classification and COW-site identity, as pure
//! predicates (`design/backend/ownership-codegen.md` §13.7).
//!
//! A source is `Borrowed` exactly when analysis is on, its site does not hold
//! the consuming claim, and it is not an owned temporary. The escape fact is
//! not an input, so it does not appear here. Site identity is the resolution
//! carrier, never the callee's spelling (FIXME 0693/0752, Principle 24). The
//! emission these answers drive is pinned in `cow_claim_tests` and
//! `cow_polarity_tests`.

use cranelisp_types::{ConcreteType, FQSymbol, MonoExpr, ResolvedCall, Span, Symbol, VarRef};

use super::{
    cow_site_source, cow_source_has_separate_owner, cow_source_is_borrowed, is_cow_vec_op,
};

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

/// A non-`Var` COW source — a fresh producing temporary (its sole reference
/// transfers; no separate owner).
fn temp() -> MonoExpr {
    MonoExpr::VecLit {
        elements: vec![],
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
        escapes: None,
        confined: None,
        unique_static: None,
    }
}

/// Build a COW-site `Apply`. `carrier` selects how the call was RESOLVED:
/// `Some(name)` = typecheck resolved it to the builtin `name` (the real COW
/// site); `None` = it resolved to something else (a user-defined fn that merely
/// spells `vec-set`, a trait/sig dispatch, …).
fn cow_apply(callee_spelling: &str, carrier: Option<&str>, source: MonoExpr) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(callee_spelling)),
        args: vec![source, var("i"), var("x")],
        span: Span::SYNTHETIC,
        resolved_call: carrier.map(|n| {
            Box::new(ResolvedCall::BuiltinFn {
                name: Symbol::from(n),
            })
        }),
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        ty: ConcreteType::Int,
        escapes: Some(true),
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

// spec: design/backend/ownership-codegen.md §13.7 — the COW sites are the two
// ops whose in-place branch returns the SOURCE pointer; the read ops
// (`vec-get`/`vec-len`) have no COW branch.
#[test]
fn only_the_two_cow_ops_are_sites() {
    assert!(is_cow_vec_op("vec-set"));
    assert!(is_cow_vec_op("vec-push"));
    assert!(!is_cow_vec_op("vec-get"));
    assert!(!is_cow_vec_op("vec-len"));
    assert!(!is_cow_vec_op("conj"));
}

// spec: design/backend/ownership-codegen.md §13.7 — the two-state
// classification over {unclaimed `Var`, claimed `Var`, fresh temporary} ×
// toggle. Only an unclaimed `Var` with analysis on is `Borrowed`; with
// analysis off the site counts a separately owned source instead (R14).
#[test]
fn only_an_unclaimed_var_with_analysis_on_is_borrowed() {
    let rows = [
        ("unclaimed var", var("v"), false, true),
        ("claimed var", var("v"), true, false),
        ("fresh temporary", temp(), false, false),
        ("fresh temporary, claimed", temp(), true, false),
    ];
    for (label, source, claimed, separate_owner) in rows {
        assert_eq!(
            cow_source_has_separate_owner(&source, claimed),
            separate_owner,
            "{label}: separate owner"
        );
        assert_eq!(
            cow_source_is_borrowed(&source, claimed, false),
            separate_owner,
            "{label}: analysis on"
        );
        assert!(
            !cow_source_is_borrowed(&source, claimed, true),
            "{label}: analysis off is never Borrowed"
        );
    }
}

// spec: design/backend/ownership-codegen.md §13.7 — a carrier-identified site
// yields its own first argument as the source.
#[test]
fn a_builtin_cow_site_yields_its_source_node() {
    for op in ["vec-set", "vec-push"] {
        let node = cow_apply(op, Some(op), var("v"));
        let MonoExpr::Apply { args, .. } = &node else {
            unreachable!()
        };
        assert!(cow_site_source(&node).is_some_and(|s| std::ptr::eq(s, &args[0])));
    }
}

// spec: design/backend/ownership-codegen.md §13.7 (FIXME 0693) — a
// user-defined fn that merely SPELLS `vec-set` is not a COW site: the identity
// comes from the resolution carrier, never the callee spelling.
#[test]
fn user_defined_fn_spelling_a_cow_op_is_not_a_site_neg() {
    assert!(cow_site_source(&cow_apply("vec-set", None, var("v"))).is_none());
    assert!(cow_site_source(&cow_apply("vec-set", Some("vec-get"), var("v"))).is_none());
}

// spec: design/backend/ownership-codegen.md §13.7 — a COW-spelling call resolved
// to a NON-builtin dispatch (trait method / sig dispatch) is likewise not a
// site: the carrier discriminates, not the spelling.
#[test]
fn non_builtin_carrier_is_not_a_site_neg() {
    let node = MonoExpr::Apply {
        callee: Box::new(var("vec-push")),
        args: vec![var("v"), var("x")],
        span: Span::SYNTHETIC,
        resolved_call: Some(Box::new(crate::test_support::sig_binding(
            "user",
            "vec-push$Vec",
        ))),
        dispatch: cranelisp_types::ApplyRef::Dispatch(FQSymbol {
            module: cranelisp_types::ModuleFullPath::from("user"),
            symbol: Symbol::from("vec-push$Vec"),
        }),
        ty: ConcreteType::Int,
        escapes: Some(true),
        confined: None,
        unique_static: None,
        provenance: None,
    };
    assert!(cow_site_source(&node).is_none());
}

// spec: design/backend/ownership-codegen.md §13.7 — a non-`Apply` node (a
// bare `Var`, a literal) is not a site at all.
#[test]
fn non_apply_node_is_not_a_site_neg() {
    assert!(cow_site_source(&var("v")).is_none());
    assert!(cow_site_source(&temp()).is_none());
}
