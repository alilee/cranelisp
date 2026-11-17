//! The constructor probe's determinant
//! (`design/backend/non-concrete-release-contract.md` §6.2.1).
//!
//! [`CtorMeta::value_shape`] is the ONE read of a constructor's field list.
//! `literals::nullary_constructor_tag` decides the bare-`iconst` lowering from
//! it, and `fn_compiler::value_provenance` decides what that emission carries
//! from it, so the two cannot disagree — a provenance verdict disagreeing with
//! what was emitted is FIXME 0917's own shape one level down. These cells pin
//! the classification; that only ONE such read exists is code shape, and is
//! `review`'s to check.

use cranelisp_types::Type;

use super::{CtorField, CtorMeta, CtorValueShape};

fn meta(field_count: usize) -> CtorMeta {
    CtorMeta {
        tag: 3,
        fields: (0..field_count)
            .map(|_| CtorField { ty: Type::Int })
            .collect(),
    }
}

// spec: design/backend/non-concrete-release-contract.md §6.2.1 — a zero-field
// constructor's value IS its tag, so it carries no heap reference; anything
// with fields mints or moves a payload box.
#[test]
fn zero_fields_is_a_bare_tag_and_any_field_is_a_payload() {
    assert_eq!(meta(0).value_shape(), CtorValueShape::BareTag);
    assert_eq!(meta(1).value_shape(), CtorValueShape::Payload);
    assert_eq!(meta(4).value_shape(), CtorValueShape::Payload);
}

// spec: §6.2.1 (NEGATIVE) — a constructor WITH fields must never answer
// "bare tag". That answer is the licence to treat the word as carrying no
// reference, and on a payload constructor it is the leak/UAF direction:
// `NoReference` on a real box tells `protect_return_value` there is nothing to
// keep alive past scope cleanup.
#[test]
fn a_constructor_with_fields_never_answers_bare_tag_neg() {
    for field_count in 1..8 {
        assert_ne!(
            meta(field_count).value_shape(),
            CtorValueShape::BareTag,
            "{field_count}-field constructor claimed to be a bare tag"
        );
    }
}
