//! The constructor probe's determinant
//! (`design/backend/non-concrete-release-contract.md` §6.2.1).
//!
//! [`CtorMeta::value_shape`] is the ONE read of a constructor's field list;
//! `literals::nullary_constructor_tag` decides the bare-`iconst` lowering from
//! it. These cells pin the classification.

use cranelisp_types::Type;

use super::{CtorField, CtorMeta, CtorValueShape};

fn meta(field_count: usize) -> CtorMeta {
    CtorMeta {
        tag: 3,
        fields: (0..field_count)
            .map(|_| CtorField { ty: Type::Int })
            .collect(),
        params: Vec::new(),
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
// "bare tag": that answer lowers its use to a bare tag `iconst`, a word that
// is not the constructor's payload box.
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
