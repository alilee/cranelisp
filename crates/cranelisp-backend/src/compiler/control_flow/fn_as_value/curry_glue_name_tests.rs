//! F2 (Wave 11 B3.1a-R) — the auto-curry drop-glue naming identity.
//!
//! The drop glue for an auto-curry closure's captures MUST key by the SAME
//! identity as its sibling wrapper (`__curry_{target}_{disc}{span}__`): the mono
//! discriminator (`inner_fn_discriminator`) folded with the span, NOT the span
//! alone. Span-only keying under-identifies: two monomorphizations of one span
//! with DIFFERENT capture `HeapCategory`s produce distinct wrappers but would
//! COLLIDE on a span-only glue name, so the `get_name` idempotency skip would
//! hand the 2nd mono the 1st mono's glue → wrong capture-drop (silent
//! corruption / leak — previously a loud `Duplicate definition`).

use super::curry_drop_glue_name;
use crate::compiler::resolution::inner_fn_discriminator_for;
use cranelisp_types::{Span, Symbol};

// spec: spec/12-runtime.md §12.3.1 — a closure and its capture drop glue are one
// object with one identity. Two mono instances of one source fn carry distinct
// mangled names → distinct discriminators → the glue names at a SHARED span must
// differ, so each mono defines and installs its own correct capture-drop.
#[test]
fn distinct_monos_get_distinct_curry_glue_at_shared_span() {
    let span = Span::new(305, 312);
    let disc_a = inner_fn_discriminator_for(Some(&Symbol::from("cap$Int+Vec")));
    let disc_b = inner_fn_discriminator_for(Some(&Symbol::from("cap$String+Vec")));
    assert_ne!(disc_a, disc_b, "distinct monos must yield distinct discriminators");

    let glue_a = curry_drop_glue_name(&disc_a, span);
    let glue_b = curry_drop_glue_name(&disc_b, span);
    assert_ne!(
        glue_a, glue_b,
        "same span, different monos (different capture categories) MUST get \
         distinct glue names — a collision hands the 2nd mono the 1st's glue \
         (wrong capture-drop). glue_a={glue_a} glue_b={glue_b}"
    );
}

// spec: spec/12-runtime.md §12.3.1 — the glue name folds the discriminator (the
// wrapper's keying), so it is NOT span-only.
#[test]
fn curry_glue_name_folds_the_discriminator() {
    let span = Span::new(10, 20);
    let disc = inner_fn_discriminator_for(Some(&Symbol::from("cap$Int+Vec")));
    assert!(!disc.is_empty(), "a monomorphic instance has a non-empty discriminator");
    let glue = curry_drop_glue_name(&disc, span);
    assert!(
        glue.contains(&disc),
        "glue name must carry the discriminator (wrapper-identity keying): {glue}"
    );
    // The span-only form the fix replaced would have been identical across monos.
    assert_ne!(glue, format!("runtime/curry_drop_glue_{}_{}", span.start, span.end));
}

// spec: spec/12-runtime.md §12.3.1 — idempotency is preserved for the intended
// case: the two arms of ONE create-gate compile the SAME expression (identical
// disc + span), so they share one glue name (the `get_name` skip dedups them).
#[test]
fn same_mono_same_span_shares_one_glue_name() {
    let span = Span::new(42, 55);
    let disc = inner_fn_discriminator_for(Some(&Symbol::from("cap$Int+Vec")));
    assert_eq!(
        curry_drop_glue_name(&disc, span),
        curry_drop_glue_name(&disc, span),
        "same mono at same span must produce one stable glue name (idempotency)"
    );
}
