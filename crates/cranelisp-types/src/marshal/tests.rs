//! Drift-guard for the shared Sexp/SList marshal tag constants (FIXME 0498).
//!
//! `marshal.rs` is a cross-crate constant table its rustdoc *claims* must stay
//! byte-synced with `cranelisp-primitives/src/marshal.rs` and with the
//! constructor order in typecheck's `register_macros_module`. That claim was a
//! guarding comment with no guard — the exact "true statement that rots
//! silently" shape the S101 `kept_jits` finding flagged. These tests turn the
//! comment into a guard, at the level the crate topology permits:
//!
//! - The **primitives ↔ types** edge is already structurally drift-proof:
//!   `cranelisp-primitives/src/marshal.rs` *imports* `TAG_*` from
//!   `cranelisp_types` (there is no second copy to diverge). What remains
//!   pinnable *here* is (a) the exact tag VALUES — a careless renumber in this
//!   file is caught — and (b) the structural invariant that each ADT's tags are
//!   a **dense 0-indexed sequence** (constructor tags are assigned `0..n` in
//!   registration order, so a gap or duplicate is a marshalling corruption).
//! - The **types ↔ typecheck `register_macros_module` ctor-order** edge cannot
//!   be asserted from here without inverting the dependency DAG
//!   (`cranelisp-types` depends on nothing in-workspace). That half is owned by
//!   a typecheck-side unit assertion or a macro-round-trip e2e — noted as
//!   0498 residue.

use super::*;

// spec: design/arch/fixmes/0498 — marshal tag values are pinned, not just commented
#[test]
fn slist_tag_values_are_pinned() {
    assert_eq!(TAG_SNIL, 0);
    assert_eq!(TAG_SCONS, 1);
}

// spec: design/arch/fixmes/0498 — Sexp tag values are pinned, not just commented
#[test]
fn sexp_tag_values_are_pinned() {
    assert_eq!(TAG_SEXP_INT, 0);
    assert_eq!(TAG_SEXP_FLOAT, 1);
    assert_eq!(TAG_SEXP_BOOL, 2);
    assert_eq!(TAG_SEXP_STR, 3);
    assert_eq!(TAG_SEXP_SYM, 4);
    assert_eq!(TAG_SEXP_LIST, 5);
    assert_eq!(TAG_SEXP_BRACKET, 6);
}

// spec: design/arch/fixmes/0498 — SList tags are a dense 0-indexed sequence
#[test]
fn slist_tags_are_dense_and_distinct() {
    let mut tags = [TAG_SNIL, TAG_SCONS];
    tags.sort_unstable();
    for (i, tag) in tags.iter().enumerate() {
        assert_eq!(
            *tag, i as i64,
            "SList ctor tags must be dense 0..n (registration order); \
             a gap/duplicate corrupts marshalling"
        );
    }
}

// spec: design/arch/fixmes/0498 — Sexp tags are a dense 0-indexed sequence
#[test]
fn sexp_tags_are_dense_and_distinct() {
    let mut tags = [
        TAG_SEXP_INT,
        TAG_SEXP_FLOAT,
        TAG_SEXP_BOOL,
        TAG_SEXP_STR,
        TAG_SEXP_SYM,
        TAG_SEXP_LIST,
        TAG_SEXP_BRACKET,
    ];
    tags.sort_unstable();
    for (i, tag) in tags.iter().enumerate() {
        assert_eq!(
            *tag, i as i64,
            "Sexp ctor tags must be dense 0..n (registration order); \
             a gap/duplicate corrupts marshalling"
        );
    }
}

// spec: design/arch/fixmes/0498 — the two ADTs' tag spaces are independent
// (each is 0-indexed in its own value; SNil and SexpInt share tag 0 legitimately
// because they are distinguished by static type, not by a shared tag space).
#[test]
fn slist_and_sexp_tag_spaces_are_independent() {
    // Both start at 0 — this is correct: the marshaller knows the static ADT of
    // the value, so tag 0 means SNil in an SList and SexpInt in a Sexp. The
    // guard pins that both remain 0-based (a shift would desync the runtime).
    assert_eq!(TAG_SNIL, TAG_SEXP_INT, "both ADTs are 0-based by construction");
}
