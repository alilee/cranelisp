// Unit tests for the resolution-adjacent symbol-naming primitives.
//
// **S110 W3:** the resolver-family tests (`resolve_got_target_*`,
// `resolve_vec_query_primitive_*`, `resolve_extern_target_*`,
// `resolve_platform_effect_target_*`, `resolve_poll_effect_target_*`, and their
// `ModuleEntry`-fixture helpers) were DELETED with the resolvers they exercised
// (`backend-keyed-consumer.md` §4/§5 — the backend no longer resolves names; it
// keyed-reads the `resolved_target` carrier). What remains pins the two
// surviving symbol-naming primitives: the per-mono-instance discriminator used
// for inner-fn body names (0347) and closure drop-glue names (0350).

use super::*;

// ── inner-fn name discriminator (FIXME 0347 defect 1) ────────────────────

// spec: design/arch/fixmes/0347 — span-derived inner-fn names
//   (`__lambda_…`, `__wrap_…`) MUST be uniquified per monomorphic instance
//   of the enclosing fn, else N mono copies collide on one symbol.
#[test]
fn inner_fn_discriminator_uniquifies_per_mono_instance() {
    use cranelisp_types::Symbol;
    // Two monomorphic instances of one source fn carry distinct mangled
    // names; the discriminator must differ so a shared lambda span yields
    // distinct symbols.
    let a = inner_fn_discriminator_for(Some(&Symbol::from("reduce$Int+Vec")));
    let b = inner_fn_discriminator_for(Some(&Symbol::from("reduce$Float+Vec")));
    assert_ne!(a, b, "distinct mono instances must yield distinct discriminators");

    // The composed lambda names (the actual collision surface) differ.
    let span = (305usize, 312usize);
    let name_a = format!("__lambda_{a}{}_{}__", span.0, span.1);
    let name_b = format!("__lambda_{b}{}_{}__", span.0, span.1);
    assert_ne!(
        name_a, name_b,
        "two mono copies of one lambda span must emit distinct symbols \
         (else the 2nd define_function collides)"
    );

    // Sanitization: $/+/./ become _, leaving a clean Cranelift symbol.
    assert!(
        a.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'),
        "discriminator must be a clean symbol: {a:?}"
    );
    assert_eq!(a, "reduce_Int_Vec__");

    // No enclosing fn (top-level expr / nested-lambda inner compiler): empty
    // prefix — the span alone disambiguates within that scope.
    assert_eq!(inner_fn_discriminator_for(None), "");
}

// ── drop-glue naming identity (S111 R6 §4.4 — the ONE consolidated test) ──
//
// Calls the PRODUCTION naming functions (`closure_drop_glue_name` /
// `curry_drop_glue_name` / `adt_drop_glue_name`), NOT an inline `format!`
// re-composition (the A.4 caveat: a `format!` drift in the production fn must
// FAIL this test, so it must exercise the real fn). Pins the two invariants the
// FIXME 0350 (closure) / ledger-25 (curry) defect class needs:
//   (1) distinct monos ⇒ distinct glue (different `inner_fn_discriminator` ⇒
//       different name, so the 2nd mono's `define_function` does not collide);
//   (2) one create-gate's two arms ⇒ one glue (same disc+span ⇒ the SAME name,
//       so the `emit_capture_dec_glue` `get_name` idempotency skip dedups them).

// spec: design/arch/fixmes/0350 (closure) + spec/12-runtime.md §12.3.1 — a
// closure and its capture drop glue are one object with one identity.
#[test]
fn drop_glue_naming_identity_span_keyed_mirrors() {
    use cranelisp_types::{Span, Symbol};
    // Two mono instances of one source fn — the shape that collided on the
    // lambda body name in 0347 and the drop-glue name in 0350 / ledger-25.
    let a = inner_fn_discriminator_for(Some(&Symbol::from("apply$Int+Vec")));
    let b = inner_fn_discriminator_for(Some(&Symbol::from("apply$Float+Vec")));
    assert_ne!(a, b, "distinct monos must yield distinct discriminators");
    let span = Span::new(2004, 2022);

    // (1) distinct monos ⇒ distinct glue, for BOTH span-keyed kinds.
    assert_ne!(
        closure_drop_glue_name(&a, span),
        closure_drop_glue_name(&b, span),
        "closure: two mono copies at one span must emit distinct drop-glue symbols"
    );
    assert_ne!(
        curry_drop_glue_name(&a, span),
        curry_drop_glue_name(&b, span),
        "curry: two mono copies at one span (differing capture categories) must \
         emit distinct glue names — a collision mis-drops captures"
    );

    // The drop-glue name shares the lambda body's discriminator scheme so the
    // (body, drop-glue) pair stay paired per mono instance.
    assert!(
        closure_drop_glue_name(&a, span).contains(&a),
        "closure glue must carry the discriminator (wrapper-identity keying)"
    );
    assert!(
        curry_drop_glue_name(&b, span).contains(&b),
        "curry glue must carry the discriminator (wrapper-identity keying)"
    );

    // (2) one create-gate's two arms (same disc+span) ⇒ one glue name — the
    // idempotency the `get_name` skip dedups on.
    assert_eq!(
        closure_drop_glue_name(&a, span),
        closure_drop_glue_name(&a, span),
        "same mono+span must produce one stable closure glue name (idempotency)"
    );
    assert_eq!(
        curry_drop_glue_name(&a, span),
        curry_drop_glue_name(&a, span),
        "same mono+span must produce one stable curry glue name (idempotency)"
    );

    // No enclosing fn: empty prefix, span alone disambiguates — the pre-0350
    // behaviour for top-level / nested-lambda scopes is preserved.
    let none = inner_fn_discriminator_for(None);
    assert_eq!(none, "");
    assert_eq!(
        closure_drop_glue_name(&none, span),
        "runtime/closure_drop_glue_2004_2022"
    );
}

// spec: spec/12-runtime.md §12.3.1 — the ADT drop glue is per-TYPE (fqtn-keyed,
// no span/disc), so distinct types get distinct glue and the same type is
// stable (the `get_name` per-module re-emit dedup).
#[test]
fn adt_drop_glue_naming_identity_is_fqtn_keyed() {
    use cranelisp_types::{FQTypeName, ModuleFullPath, TypeName};
    let box_t = FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box"));
    let pair_t = FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Pair"));
    assert_ne!(
        adt_drop_glue_name(&box_t),
        adt_drop_glue_name(&pair_t),
        "distinct ADTs must get distinct drop-glue names"
    );
    assert_eq!(
        adt_drop_glue_name(&box_t),
        adt_drop_glue_name(&box_t),
        "one ADT must produce one stable drop-glue name (per-module re-emit dedup)"
    );
    assert_eq!(adt_drop_glue_name(&box_t), "runtime/drop_glue_Box");
}
