//! Per-submodule test module for `type_resolve.rs` — default-method body
//! construction (`build_default_body`). Relocated verbatim from the pooled
//! `traits/tests.rs` (S102 FIXME 0497 de-pool), now a sibling of the code it
//! exercises, per METHOD §2.2 / Principle 23.
//!
//! FIXME 0590: the former `resolve_trait_type_expr` unit tests were deleted with
//! the mirror they exercised; their cases (Self substitution, type-var fresh /
//! pre-seed / co-reference) are re-homed onto the canonical resolver's tests in
//! `crate::resolve::tests` (now covering the `Self` and con-var arms too).

use cranelisp_types::{Span, Symbol};

use super::*;
use crate::traits::test_helpers::*;

// -----------------------------------------------------------------------
// build_default_body (default method-body generation)
// -----------------------------------------------------------------------

// spec: 07-traits §7.1.5 — default method body: != is (not (= x y))
#[test]
fn test_build_default_body_neq() {
    // != → (not (= x y))
    let body = build_default_body(
        "Eq",
        "!=",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    )
    .unwrap();

    assert_apply_callee(&body, "not");
    let not_args = apply_args(&body);
    assert_eq!(not_args.len(), 1);
    assert_apply_callee(&not_args[0], "=");
    let eq_args = apply_args(&not_args[0]);
    assert_eq!(eq_args.len(), 2);
    assert_var(&eq_args[0], "x");
    assert_var(&eq_args[1], "y");
}

// spec: 07-traits §7.1.5 — default method body: > is (< y x)
#[test]
fn test_build_default_body_gt() {
    // > → (< y x)
    let body = build_default_body(
        "Ord",
        ">",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    )
    .unwrap();

    assert_apply_callee(&body, "<");
    let args = apply_args(&body);
    assert_eq!(args.len(), 2);
    assert_var(&args[0], "y");
    assert_var(&args[1], "x");
}

// spec: 07-traits §7.1.5 — default method body: <= is (not (< y x))
#[test]
fn test_build_default_body_le() {
    // <= → (not (< y x))
    let body = build_default_body(
        "Ord",
        "<=",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    )
    .unwrap();

    assert_apply_callee(&body, "not");
    let not_args = apply_args(&body);
    assert_eq!(not_args.len(), 1);
    assert_apply_callee(&not_args[0], "<");
    let lt_args = apply_args(&not_args[0]);
    assert_eq!(lt_args.len(), 2);
    assert_var(&lt_args[0], "y");
    assert_var(&lt_args[1], "x");
}

// spec: 07-traits §7.1.5 — default method body: >= is (not (< x y))
#[test]
fn test_build_default_body_ge() {
    // >= → (not (< x y))
    let body = build_default_body(
        "Ord",
        ">=",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    )
    .unwrap();

    assert_apply_callee(&body, "not");
    let not_args = apply_args(&body);
    assert_eq!(not_args.len(), 1);
    assert_apply_callee(&not_args[0], "<");
    let lt_args = apply_args(&not_args[0]);
    assert_eq!(lt_args.len(), 2);
    assert_var(&lt_args[0], "x");
    assert_var(&lt_args[1], "y");
}

// spec: 07-traits §7.1.5 — unknown trait/method has no default body
#[test]
fn test_build_default_body_unknown_method_errors() {
    let result = build_default_body(
        "Unknown",
        "foo",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    );
    assert!(result.is_err());
}

// spec: 07-traits §7.1.5 — default body with wrong param count errors
#[test]
fn test_build_default_body_wrong_param_count_errors() {
    let result = build_default_body("Eq", "!=", &[Symbol::from("x")], Span::SYNTHETIC);
    assert!(result.is_err());
}
