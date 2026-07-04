//! CS-1 Principle-23 matrices for `classify.rs`
//! (`design/typecheck/ownership-inference.md` §13.7 `classify.rs` block).
//!
//! - *Complexity matrix* — the eight §2.1 Apply-shape × `resolved_call` rows.
//! - *Edge* — `PrimitiveBody::Inline` vs `Extern` reach `DeclaredLeaf` the
//!   same way; a pinned boundary is Decision-24.
//! - *Negative* — never moded for closure-valued / `AutoCurry` sites; the
//!   `Copy` classifier admits exactly `{Int, Bool, Float}`; memo determinism.

use cranelisp_types::{
    ConcreteType, FQTypeName, JitSymbol, ModuleFullPath, MonoExpr, ResolvedCall, Span, Symbol,
    TypeName,
};

use super::*;

fn var(name: &str) -> MonoExpr {
    MonoExpr::Var {
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

fn nonvar_callee() -> MonoExpr {
    // A computed callee — an `if` producing a closure value, say.
    MonoExpr::If {
        cond: Box::new(MonoExpr::BoolLit { value: true, span: Span::SYNTHETIC, ty: ConcreteType::Bool }),
        then_branch: Box::new(var("f")),
        else_branch: Box::new(var("g")),
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    }
}

fn adt(name: &str) -> ConcreteType {
    ConcreteType::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from(name)), vec![])
}

// --- Complexity matrix: the eight §2.1 rows ---

#[test]
fn row_sigdispatch_is_summarised_by_mangled_name() {
    // spec: design/typecheck/ownership-inference.md §2.1 — Var+SigDispatch ⇒ static moded
    let rc = ResolvedCall::SigDispatch { mangled_name: JitSymbol::from("id$Int") };
    let got = classify_call(Some(&rc), &var("id"), |_| None);
    assert_eq!(got, CallClass::Summarised(Symbol::from("id$Int")));
}

#[test]
fn row_traitmethod_is_summarised_by_mangled_name() {
    // spec: §2.1 — Var+TraitMethod ⇒ static moded (post-mono named impl)
    let rc = ResolvedCall::TraitMethod {
        trait_name: cranelisp_types::FQTraitName::new(
            ModuleFullPath::from("user"),
            cranelisp_types::TraitName::from("Eq"),
        ),
        method_name: Symbol::from("eq"),
        impl_type: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Int")),
        mangled_name: JitSymbol::from("Eq.eq$Int"),
    };
    let got = classify_call(Some(&rc), &var("eq"), |_| None);
    assert_eq!(got, CallClass::Summarised(Symbol::from("Eq.eq$Int")));
}

#[test]
fn row_builtin_is_summarised_declared_leaf() {
    // spec: §2.1 — Var+BuiltinFn ⇒ declared leaf (facts from §9 table)
    let rc = ResolvedCall::BuiltinFn { name: Symbol::from("vec-get") };
    let got = classify_call(Some(&rc), &var("vec-get"), |_| None);
    assert_eq!(got, CallClass::Summarised(Symbol::from("vec-get")));
}

#[test]
fn row_none_var_chain_resolves_userfn_is_summarised() {
    // spec: §2.1 — Var+None→UserFn ⇒ static moded
    let got = classify_call(None, &var("helper"), |n| {
        (n.as_ref() == "helper").then_some(TerminalKind::UserFnConcrete)
    });
    assert_eq!(got, CallClass::Summarised(Symbol::from("helper")));
}

#[test]
fn row_none_var_chain_resolves_leaf_is_summarised() {
    // spec: §2.1/§9.3 — Var+None→Primitive (declared leaf) ⇒ summarised
    let got = classify_call(None, &var("vec-len"), |_| Some(TerminalKind::DeclaredLeaf));
    assert_eq!(got, CallClass::Summarised(Symbol::from("vec-len")));
}

#[test]
fn row_none_var_pinned_boundary_is_decision24() {
    // spec: §2.1 — Var+None→Constructor/PlatformEffect ⇒ pinned Decision-24
    let got = classify_call(None, &var("Some"), |_| Some(TerminalKind::PinnedBoundary));
    assert_eq!(got, CallClass::Decision24);
}

#[test]
fn row_none_var_closure_binding_is_decision24() {
    // spec: §2.1 — Var resolving to a let/param binding (closure value) ⇒ Decision-24
    let got = classify_call(None, &var("f"), |_| None);
    assert_eq!(got, CallClass::Decision24);
}

#[test]
fn row_nonvar_callee_is_decision24() {
    // spec: §2.1 — non-Var (computed) callee ⇒ Decision-24
    let got = classify_call(None, &nonvar_callee(), |_| Some(TerminalKind::UserFnConcrete));
    assert_eq!(got, CallClass::Decision24);
}

#[test]
fn row_autocurry_is_decision24() {
    // spec: §2.1 — AutoCurry ⇒ Decision-24 (partial application is a closure value)
    let rc = ResolvedCall::AutoCurry {
        target_name: Symbol::from("add"),
        applied_count: 1,
        total_count: 2,
        trait_resolution: None,
    };
    let got = classify_call(Some(&rc), &var("add"), |_| Some(TerminalKind::UserFnConcrete));
    assert_eq!(got, CallClass::Decision24);
}

// --- Negative: resolved_call dominates the callee-shape fallback ---

#[test]
fn resolved_call_dominates_and_resolver_not_consulted() {
    // spec: §2.1 — a resolved SigDispatch never consults the None-row resolver
    let rc = ResolvedCall::SigDispatch { mangled_name: JitSymbol::from("f$Int") };
    // Resolver would say Decision-24 (PinnedBoundary) but must be ignored.
    let got = classify_call(Some(&rc), &var("f"), |_| Some(TerminalKind::PinnedBoundary));
    assert_eq!(got, CallClass::Summarised(Symbol::from("f$Int")));
}

// --- Copy classifier matrix ---

#[test]
fn copy_admits_exactly_scalars() {
    // spec: §2.2 — increment-I Copy = {Int, Bool, Float}
    let c = CopyClassifier::new();
    assert!(c.is_copy(&ConcreteType::Int));
    assert!(c.is_copy(&ConcreteType::Bool));
    assert!(c.is_copy(&ConcreteType::Float));
}

#[test]
fn copy_rejects_heap_and_fn_types() {
    // spec: §2.2 (negative) — String / Vec / ADT / Fn are NOT Copy in increment I
    let c = CopyClassifier::new();
    assert!(!c.is_copy(&ConcreteType::String));
    assert!(!c.is_copy(&adt("Point")));
    assert!(!c.is_copy(&ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int))));
    // A Vec is an ADT in this representation; its element being Copy does not
    // make the Vec Copy in increment I (representation clause fails).
    assert!(!c.is_copy(&ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
        vec![ConcreteType::Int],
    )));
}

#[test]
fn copy_is_deterministic_under_memo() {
    // spec: §2.2 — memoized classifier returns identical verdicts across repeats
    let c = CopyClassifier::new();
    for _ in 0..3 {
        assert!(c.is_copy(&ConcreteType::Int));
        assert!(!c.is_copy(&ConcreteType::String));
        assert!(!c.is_copy(&adt("T")));
    }
}
