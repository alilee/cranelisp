//! DEF-2 — the `vec-push` element-argument consuming-inc decision.
//!
//! Pins the seam where DEF-2 lived: a heap-ADT element forwarded into
//! `vec-push` through a user `defn` wrapper (so the element is a heap-typed
//! Var, not a fresh temporary) was stored into the Vec WITHOUT a caller-side
//! consuming inc, while the wrapper's scope cleanup dec'd the same single
//! reference — under-counting the element by 1 (the COW single-owner test
//! then fired against a stale rc and mutated an aliased backing). The fix
//! (`element_consuming_inc`, the predicate now shared with vec-set / DEF-3)
//! emits the inc for a heap-typed Var element, matching
//! `compile_consuming_arg_list` (Decision 24 §3.1).
use super::*;

fn var(ty: ConcreteType) -> MonoExpr {
    MonoExpr::Var {
        resolved_target: None,
        name: cranelisp_types::Symbol::from("x"),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty,
    }
}

// spec: spec/12-runtime.md §12.3.3 — DEF-2: a heap ADT element forwarded as a
// Var into vec-push (the wrapper path) MUST get a caller-side consuming inc so
// the Vec's stored reference and the wrapper-scope dec balance. The bug: no inc
// → under-count → COW mutates an aliased backing → over-count on read-back.
// (`ConcreteType::String` stands in for any AlwaysHeap element type; the
// decision keys on Var-ness + the passed `HeapCategory`, not the type's shape.)
#[test]
fn heap_adt_var_element_gets_consuming_inc() {
    let elem = var(ConcreteType::String);
    assert_eq!(
        element_consuming_inc(&elem, HeapCategory::AlwaysHeap),
        Some(HeapCategory::AlwaysHeap),
        "a heap-typed (AlwaysHeap) Var element MUST be consuming-inc'd (DEF-2)"
    );
}

// spec: spec/12-runtime.md §12.3.3 — a Mixed-ADT Var element is guarded-inc'd
// (the <1024 nullary-tag discriminator), still the consuming convention.
#[test]
fn mixed_adt_var_element_gets_guarded_inc() {
    let elem = var(ConcreteType::String);
    assert_eq!(
        element_consuming_inc(&elem, HeapCategory::Mixed),
        Some(HeapCategory::Mixed),
        "a Mixed Var element MUST be guarded-consuming-inc'd (DEF-2)"
    );
}

// spec: spec/12-runtime.md §12.3.3 — CONTROL: a scalar (Int / NeverHeap) Var
// element is NOT inc'd — nothing to refcount. Pins that the scalar-wrapper
// control test stays GREEN (Int elements are unaffected by DEF-2).
#[test]
fn scalar_var_element_not_inc_neg() {
    let elem = var(ConcreteType::Int);
    assert_eq!(
        element_consuming_inc(&elem, HeapCategory::NeverHeap),
        None,
        "a NeverHeap (Int) Var element MUST NOT be inc'd"
    );
}

// spec: spec/12-runtime.md §12.3.3 — CONTROL: a TEMPORARY heap element (e.g.
// `(Box i)` — a non-Var constructor call) transfers its rc=1 reference into the
// Vec and MUST NOT be inc'd. Pins that the DIRECT path (and the temporary-into-
// vec-push case generally) stays GREEN — inc'ing it would leak.
#[test]
fn heap_temporary_element_not_inc_neg() {
    // A non-Var heap expression: an Int literal stands in structurally for
    // "any non-Var temporary" — the decision keys on the Var-ness, and a
    // heap temporary (e.g. a constructor call) is likewise non-Var.
    let temp = MonoExpr::IntLit {
        value: 0,
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    };
    assert_eq!(
        element_consuming_inc(&temp, HeapCategory::AlwaysHeap),
        None,
        "a temporary (non-Var) element transfers ownership — MUST NOT be inc'd"
    );
}
