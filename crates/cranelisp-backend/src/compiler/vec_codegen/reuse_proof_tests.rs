//! Increment-II reuse-token static-uniqueness proof seam (§6.4). Pins the
//! `node_unique_static` reader — the HARD REQUIREMENT that the write-path proof
//! is read off the **fresh-producing** node (`VecLit`/`Apply`/`ConstrADT`/
//! `StringLit`), NEVER off a consuming-use `Var` (which carries no
//! `unique_static` field, so reading it there would make every proof `None` ⇒
//! the check-elision silently dead — a mis-read is the whole-optimization-dead
//! defect the Wave-2 /review fenced).
//!
//! Strategy-derived scenarios (seam × class, `feedback_dev_strategy_derived_unit_scenarios`):
//!   - complexity: the proof reads through on each fresh-producing variant;
//!   - edge: `Some(false)` and `None` are distinct from `Some(true)` (only the
//!     latter elides the dynamic rc==1 check);
//!   - negative: a `Var` (the consuming-use node) ALWAYS reads `None`, even
//!     though a `Var` cannot structurally carry the field — the guard is that
//!     the reader does not fabricate a proof for it.

use super::node_unique_static;
use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

// The `node_unique_static` reader matches on the node VARIANT and reads the
// `unique_static` field; it never inspects `ty`, so a scalar `ty` suffices for
// the pure-reader scenarios (keeps the fixtures free of `FQTypeName` plumbing).
fn ty() -> ConcreteType {
    ConcreteType::Int
}

/// A fresh-producing `VecLit` node carrying an explicit `unique_static`.
fn veclit(unique_static: Option<bool>) -> MonoExpr {
    MonoExpr::VecLit {
        elements: vec![],
        span: Span::SYNTHETIC,
        ty: ty(),
        escapes: None,
        confined: None,
        unique_static,
    }
}

/// A fresh-producing `Apply` node (a call whose summary proved `result_unique`)
/// carrying an explicit `unique_static`.
fn apply(unique_static: Option<bool>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(MonoExpr::Var {
            name: Symbol::from("build"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
        }),
        args: vec![],
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ty(),
        escapes: None,
        confined: None,
        unique_static,
        provenance: None,
    }
}

/// The consuming-use `Var` node — the node the HARD REQUIREMENT forbids reading
/// the proof off.
fn var() -> MonoExpr {
    MonoExpr::Var {
        name: Symbol::from("v"),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ty(),
    }
}

// spec: design/backend/ownership-codegen.md §6.4 — a fresh-producing VecLit
// proven unique reads Some(true) (the proof-elision permission).
#[test]
fn veclit_some_true_reads_through() {
    assert_eq!(node_unique_static(&veclit(Some(true))), Some(true));
}

// spec: design/backend/ownership-codegen.md §6.4 — a fresh-producing Apply
// (result_unique-chained call result) proven unique reads Some(true).
#[test]
fn apply_some_true_reads_through() {
    assert_eq!(node_unique_static(&apply(Some(true))), Some(true));
}

// spec: design/backend/ownership-codegen.md §6.4 — EDGE: Some(false) is NOT the
// elision permission (only Some(true) elides the dynamic check).
#[test]
fn some_false_is_not_elision() {
    assert_eq!(node_unique_static(&veclit(Some(false))), Some(false));
    assert_ne!(node_unique_static(&veclit(Some(false))), Some(true));
}

// spec: design/backend/ownership-codegen.md §6.4 — EDGE: absent proof (None,
// e.g. analysis-off / unproven) ⇒ None ⇒ the dynamic token, verbatim.
#[test]
fn none_stays_none() {
    assert_eq!(node_unique_static(&veclit(None)), None);
    assert_eq!(node_unique_static(&apply(None)), None);
}

// spec: design/backend/ownership-codegen.md §6.4 — NEGATIVE (the HARD
// REQUIREMENT / Wave-2 /review fence): a consuming-use `Var` reads `None`. The
// proof MUST be read off the fresh-producing node, never the Var — otherwise
// every proof collapses to None and the optimization is dead (or, worse, a mis-
// read of a Var-adjacent fact would be an unsound elision).
#[test]
fn var_never_carries_a_proof_neg() {
    assert_eq!(
        node_unique_static(&var()),
        None,
        "a consuming-use Var must NEVER yield a uniqueness proof (§6.4 HARD \
         requirement); reading the proof off the Var is the whole-optimization-\
         dead defect"
    );
}

// spec: design/backend/ownership-codegen.md §6.4 — NEGATIVE: control-flow /
// binding nodes (Let/If/Match) are not fresh-producing carriers — conservative
// None (the proof lives on the leaf origin, not the composite).
#[test]
fn non_fresh_composite_nodes_read_none_neg() {
    let let_node = MonoExpr::Let {
        bindings: vec![],
        body: Box::new(var()),
        span: Span::SYNTHETIC,
        ty: ty(),
    };
    assert_eq!(node_unique_static(&let_node), None);
}
