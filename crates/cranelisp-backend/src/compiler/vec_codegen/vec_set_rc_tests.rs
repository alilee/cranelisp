//! DEF-3 / FIXME 0417 — the `vec-set` new-element consuming-inc decision, now
//! FULLY SYMMETRIC with `vec-push` (DEF-2).
//!
//! Pins the seam where DEF-3 lived: `vec-set`'s inline-COW codegen (and the
//! `vec_set_copy` runtime helper) inc'd the NEW element UNCONDITIONALLY.
//! Correct for a heap-typed Var element (the Vec gains a reference while the
//! Var stays scope-owned), but a one-reference LEAK for a TEMPORARY heap
//! element — `(vec-set v i (Box 7))` — whose sole rc=1 reference must
//! TRANSFER into the Vec (no inc). The fix routes the decision through the
//! shared `element_consuming_inc` predicate (Principle 7): inc iff heap-typed
//! Var — exactly the end state DEF-2 aligned vec-push to.
//!
//! FIXME 0417 completed the alignment: `compile_vec_set` now emits the
//! consuming inc UP-FRONT (gated by `element_consuming_inc`), exactly as
//! `compile_vec_push` does. BOTH the mutate-in-place and copy sub-paths store
//! `new_val` with NO further inc; `vec_set_copy` no longer inc's the new value
//! (it inc's only retained copied-over elements); the codegen compensation dec
//! (`emit_vec_set_copy_temp_compensation`) is DELETED. One predicate, one
//! division of labour — identical to vec-push. PAIRED-OR-UAF: the runtime inc
//! drop and the compensation deletion land together (mis-pairing reintroduces
//! FIXME 0296's use-after-free).
//!
//! This module pins the DECISION (`element_consuming_inc`, the same predicate
//! both ops now consult). The up-front codegen inc gates on `Some(_)`; the
//! decision-table below is the single source of the inc-or-transfer behaviour
//! for BOTH the COW and copy paths.
use super::*;

fn var(ty: ConcreteType) -> MonoExpr {
    MonoExpr::Var {
        resolution: cranelisp_types::VarRef::Local {
            binder: cranelisp_types::Symbol::from("v"),
            binding_span: Span::SYNTHETIC,
        },
        name: cranelisp_types::Symbol::from("v"),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty,
    }
}

// spec: spec/12-runtime.md §12.3.3 — DEF-3: a heap-typed Var element handed to
// vec-set (e.g. `c` in `(vec-set (cells-of g) idx c)`) MUST get a consuming
// inc — the Vec gains a reference while the Var stays scope-owned. (Direction
// check: this is the case that MUST keep inc'ing — DEF-3 must not regress
// DEF-2's under-count for Var elements.)
#[test]
fn heap_var_element_gets_consuming_inc() {
    let elem = var(ConcreteType::String);
    assert_eq!(
        element_consuming_inc(&elem, HeapCategory::AlwaysHeap),
        Some(HeapCategory::AlwaysHeap),
        "a heap-typed (AlwaysHeap) Var element handed to vec-set MUST be \
         consuming-inc'd (the Vec gains a reference; do not regress DEF-2)"
    );
}

// spec: spec/12-runtime.md §12.3.3 — a Mixed-ADT Var element is guarded-inc'd
// (the <1024 nullary-tag discriminator), still the consuming convention.
#[test]
fn mixed_var_element_gets_guarded_inc() {
    let elem = var(ConcreteType::String);
    assert_eq!(
        element_consuming_inc(&elem, HeapCategory::Mixed),
        Some(HeapCategory::Mixed),
        "a Mixed Var element handed to vec-set MUST be guarded-consuming-inc'd"
    );
}

// spec: spec/12-runtime.md §12.3.3 — THE DEF-3 BUG SEAM: a TEMPORARY heap
// element — `(vec-set v i (Box 7))`, a non-Var constructor call — transfers
// its rc=1 reference into the Vec and MUST NOT be inc'd. The prior code inc'd
// unconditionally → the temporary leaked one heap object (5 allocs / 4 frees).
// The decision MUST be `None` here so the COW path skips the inc (and the copy
// path compensates the runtime's unconditional inc).
#[test]
fn heap_temporary_element_not_inc_neg() {
    // An Int literal stands in structurally for "any non-Var temporary" — the
    // decision keys on Var-ness, and a heap temporary (e.g. `(Box 7)`) is
    // likewise non-Var. Passing AlwaysHeap models a heap element type.
    let temp = MonoExpr::IntLit {
        value: 7,
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    };
    assert_eq!(
        element_consuming_inc(&temp, HeapCategory::AlwaysHeap),
        None,
        "a TEMPORARY (non-Var) heap element handed to vec-set transfers \
         ownership — MUST NOT be inc'd (DEF-3 leak when it was)"
    );
}

// spec: spec/12-runtime.md §12.3.3 — CONTROL: a scalar (Int / NeverHeap) Var
// element handed to vec-set is NOT inc'd — nothing to refcount. Pins that the
// scalar control stays GREEN (Int elements are unaffected by DEF-3).
#[test]
fn scalar_var_element_not_inc_neg() {
    let elem = var(ConcreteType::Int);
    assert_eq!(
        element_consuming_inc(&elem, HeapCategory::NeverHeap),
        None,
        "a NeverHeap (Int) Var element handed to vec-set MUST NOT be inc'd"
    );
}

// spec: spec/12-runtime.md §12.3.3 — FIXME 0417 ALIGNMENT GUARD: vec-set and
// vec-push consult the SAME `element_consuming_inc` predicate, so for any
// (element-expr, heap-category) the consuming-inc decision is IDENTICAL across
// the two ops. This is the structural property the up-front-inc refactor
// depends on: `compile_vec_set` and `compile_vec_push` both emit the inc
// up-front gated by this one predicate; `vec_set_copy`/`vec_push_copy` both
// skip the new value. Pin that the predicate yields one decision for both —
// the single-source-of-truth (Principle 7) the FIXME established. (A drift
// where vec-set diverged from vec-push is exactly the PAIRED-OR-UAF hazard.)
#[test]
fn vec_set_and_vec_push_share_one_consuming_inc_decision() {
    let heap_var = var(ConcreteType::String);
    let temp = MonoExpr::IntLit {
        value: 7,
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    };
    let scalar_var = var(ConcreteType::Int);

    // The predicate is the single source both ops read — same inputs ⇒ same
    // decision, by construction. Cover the three discriminating cases: heap Var
    // (inc), heap temporary (transfer/None), scalar Var (None). Each row is the
    // value vec-set hoists AND the value vec-push hoists — they cannot diverge.
    for (elem, category, expected) in [
        (
            &heap_var,
            HeapCategory::AlwaysHeap,
            Some(HeapCategory::AlwaysHeap),
        ),
        (&heap_var, HeapCategory::Mixed, Some(HeapCategory::Mixed)),
        (&temp, HeapCategory::AlwaysHeap, None),
        (&scalar_var, HeapCategory::NeverHeap, None),
    ] {
        assert_eq!(
            element_consuming_inc(elem, category),
            expected,
            "vec-set and vec-push MUST share one consuming-inc decision \
             (FIXME 0417 single-source-of-truth) for category {category:?}"
        );
    }
}
