//! FIXME 0693 — the §13.7 COW retain gate is ONE predicate, and the R3
//! dec-side seam agrees with the producer by construction.
//!
//! Before S115 W3 the dec side (`fn_compiler.rs::scrutinee_cow_retains_reused`)
//! re-derived the site's identity from the SYNTACTIC callee spelling
//! (`matches!(callee_name, "vec-set" | "vec-push")`) and added a `variables`
//! liveness condition the producer does not have. Two divergences followed:
//!
//! 1. a user-defined fn literally named `vec-set` (legal under
//!    `PreludeVariant::None`) made the consumer's name test TRUE although the
//!    producer's COW gate never ran — the consumer would then emit a
//!    "balancing" dec for an inc that does not exist (spurious dec ⇒ UAF).
//!    Masked at HEAD only because typecheck records `escapes = Some(false)` on
//!    that scrutinee; the S115 W4 escape-fact correction can lift that mask.
//! 2. a non-live source made the consumer decline where the producer had
//!    classified `Borrowed` and emitted the inc (the leak direction).
//!
//! Both sides now call the SAME pure predicates below. These cells are the
//! disagreement fence at the unit tier: the producer's classification chain
//! (`cow_source_is_borrowed` → `cow_retains_reused_gate`, exactly what
//! `cow_source_ownership` runs) and the consumer's site verdict
//! (`cow_site_retain_verdict`) must agree on every row of the §13.5-style
//! matrix — builtin/user-named × escapes true/false/absent × return-source y/n
//! × Var/temp source × both ownership toggles.

use cranelisp_types::{
    ConcreteType, FQSymbol, JitSymbol, MonoExpr, ResolvedCall, Span, Symbol, VarRef,
};

use super::{cow_retains_reused_gate, cow_site_retain_verdict, cow_source_is_borrowed, is_cow_vec_op};

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

/// A non-`Var` COW source — a fresh producing temporary (the `Owned`
/// classification: its sole reference transfers, no separate owner).
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
fn cow_apply(callee_spelling: &str, carrier: Option<&str>, source: MonoExpr, escapes: Option<bool>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(callee_spelling)),
        args: vec![source, var("i"), var("x")],
        span: Span::SYNTHETIC,
        resolved_call: carrier
            .map(|n| Box::new(ResolvedCall::BuiltinFn { name: Symbol::from(n) })),
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        ty: ConcreteType::Int,
        escapes,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

/// The producer's own decision, computed exactly as `cow_source_ownership`
/// computes it (classification, then the escape gate) — the "was an inc
/// emitted at this site?" oracle the consumer must match.
fn producer_emitted_inc(
    source: &MonoExpr,
    escapes: Option<bool>,
    return_cow_source: Option<&Symbol>,
    analysis_off: bool,
) -> bool {
    if !cow_source_is_borrowed(source, return_cow_source, analysis_off) {
        return false; // Owned ⇒ transfer, no mutate-branch retention inc
    }
    cow_retains_reused_gate(source, escapes, return_cow_source, analysis_off)
}

// spec: design/backend/ownership-codegen.md §13.7 — the gate sites are the two
// COW ops whose in-place branch returns the SOURCE pointer; the read ops
// (`vec-get`/`vec-len`) have no COW branch and are not gate sites.
#[test]
fn only_the_two_cow_ops_are_gate_sites() {
    assert!(is_cow_vec_op("vec-set"));
    assert!(is_cow_vec_op("vec-push"));
    assert!(!is_cow_vec_op("vec-get"));
    assert!(!is_cow_vec_op("vec-len"));
    assert!(!is_cow_vec_op("conj"));
}

// spec: design/backend/ownership-codegen.md §13.7 (FIXME 0693) — the R3
// consumer and the COW producer agree on EVERY row of the matrix.
#[test]
fn consumer_verdict_matches_producer_emitted_inc_over_the_matrix() {
    let ret_src = Symbol::from("r");
    for op in ["vec-set", "vec-push"] {
        for analysis_off in [false, true] {
            for escapes in [Some(true), Some(false), None] {
                for (label, source) in [
                    ("live-var", var("v")),
                    ("return-cow-source", var("r")),
                    ("fresh-temp", temp()),
                ] {
                    for return_cow_source in [None, Some(&ret_src)] {
                        let node = cow_apply(op, Some(op), source.clone(), escapes);
                        let consumer = cow_site_retain_verdict(&node, return_cow_source, analysis_off);
                        let producer =
                            producer_emitted_inc(&source, escapes, return_cow_source, analysis_off);
                        assert_eq!(
                            consumer,
                            Some(producer),
                            "0693 disagreement: op={op} source={label} escapes={escapes:?} \
                             return_cow_source={return_cow_source:?} analysis_off={analysis_off} \
                             — the R3 dec-side verdict MUST equal the producer's emitted-inc \
                             decision (a consumer `true` without a producer inc is a spurious \
                             dec ⇒ UAF; a consumer `false` under a producer inc leaks)."
                        );
                    }
                }
            }
        }
    }
}

// spec: design/backend/ownership-codegen.md §13.7 (FIXME 0693) — THE latent-UAF
// row: a user-defined fn that merely SPELLS `vec-set` is not a COW site. The
// identity comes from the resolution carrier, never the callee spelling
// (Principle 24 — the name is a trigger, the carrier is the identity).
#[test]
fn user_defined_fn_spelling_a_cow_op_is_not_a_gate_site_neg() {
    // `(defn vec-set [v i x] v)` + `(match (vec-set v 0 5) [r r])`: an escaping
    // live-`Var` source — every condition the OLD syntactic mirror tested is
    // satisfied, so it would have said "the escape-inc fired, let the dec run".
    // The producer never ran a COW gate here: there is no inc to balance.
    let node = cow_apply("vec-set", None, var("v"), Some(true));
    assert_eq!(
        cow_site_retain_verdict(&node, None, false),
        None,
        "a user-defined `vec-set` is NOT a COW gate site — the R3 seam must not \
         emit a balancing dec for an inc the COW producer never emitted (0693 \
         latent UAF channel; the `escapes = Some(false)` mask is not the fence)"
    );
}

// spec: design/backend/ownership-codegen.md §13.7 — a COW-spelling call resolved
// to a NON-builtin dispatch (trait method / sig dispatch) is likewise not a gate
// site: the carrier discriminates, not the spelling.
#[test]
fn non_builtin_carrier_is_not_a_gate_site_neg() {
    let node = MonoExpr::Apply {
        callee: Box::new(var("vec-push")),
        args: vec![var("v"), var("x")],
        span: Span::SYNTHETIC,
        resolved_call: Some(Box::new(ResolvedCall::SigDispatch {
            mangled_name: JitSymbol::from("user/vec-push$Vec"),
        })),
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
    assert_eq!(cow_site_retain_verdict(&node, None, false), None);
}

// spec: design/backend/ownership-codegen.md §13.7 — a non-`Apply` scrutinee (a
// bare `Var`, a literal) is not a gate site at all.
#[test]
fn non_apply_node_is_not_a_gate_site_neg() {
    assert_eq!(cow_site_retain_verdict(&var("v"), None, false), None);
    assert_eq!(cow_site_retain_verdict(&temp(), None, false), None);
}

// spec: design/backend/ownership-codegen.md §13.7 — the escape gate itself:
// escape OR absent-fact ⇒ inc (the UAF-safe P25 default); a recorded
// `Some(false)` (recur-transfer / in-frame consume) ⇒ no inc (l_c3 reuse).
#[test]
fn escape_gate_polarity_absent_fact_incs() {
    let live = var("v");
    assert!(cow_retains_reused_gate(&live, Some(true), None, false));
    assert!(
        cow_retains_reused_gate(&live, None, None, false),
        "an ABSENT escape fact must default to the inc (P25), never to elision"
    );
    assert!(!cow_retains_reused_gate(&live, Some(false), None, false));
}

// spec: design/backend/ownership-codegen.md §13.7 / R14 — analysis-OFF is the
// conservative all-`Owned` lowering: `Borrowed` is unreachable, so no retention
// inc exists and the consumer must never ask for a balancing dec.
#[test]
fn toggle_off_has_no_borrowed_source_and_no_retention_neg() {
    let live = var("v");
    assert!(!cow_source_is_borrowed(&live, None, true));
    assert!(!cow_retains_reused_gate(&live, Some(true), None, true));
    let node = cow_apply("vec-set", Some("vec-set"), var("v"), Some(true));
    assert_eq!(cow_site_retain_verdict(&node, None, true), Some(false));
}
