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

// ── ADT drop-glue INSTANTIATION identity (S111 CS-1.1 §4.4 / 0633-R3) ─────
//
// The ADT drop glue is per-INSTANTIATION, not per-type: `build_adt_drop_glue_fn`
// substitutes the concrete type args into each ctor field and classifies
// per-field heap-ness before emitting the field decs, so the glue name must
// carry the full instantiation identity (module + type name + concrete args).
// The CS-1 predecessor (`adt_drop_glue_naming_identity_is_fqtn_keyed`) asserted
// the OPPOSITE — that bare-`fqtn.name` keying was collision-free — which was a
// false regression guard masking the FIXME 0633 SIGBUS/leak. This battery pins
// the corrected identity: distinct concrete args ⇒ distinct glue, distinct
// module ⇒ distinct glue, same instantiation ⇒ stable glue (so the `get_name`
// reuse is sound). The vec elem-dec layer keys on the same mangle
// (`adt_instantiation_mangle`), so pinning it here pins both layers.
//
// Calls the PRODUCTION naming fns (`adt_drop_glue_name` /
// `adt_instantiation_mangle`), never an inline `format!` re-composition (the
// A.4 caveat: a mangle drift must FAIL this test).

// Build a concrete `Type::ADT(module/Name, args)` for the identity assertions.
#[cfg(test)]
fn adt(module: &str, name: &str, args: Vec<cranelisp_types::Type>) -> cranelisp_types::Type {
    use cranelisp_types::{FQTypeName, ModuleFullPath, Type, TypeName};
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name)),
        args,
    )
}

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop:
// a per-instantiation drop glue keyed under the full instantiation so distinct
// heap-category-divergent instantiations get distinct glue.
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/{resolution.rs::adt_drop_glue_name,vec_codegen.rs::build_elem_dec_fn} found=S111 owner=/dev
#[test]
fn adt_drop_glue_identity_keys_on_full_instantiation() {
    use cranelisp_types::Type;

    // (i) same fqtn, DIFFERENT concrete args ⇒ DIFFERENT glue. This is the
    // concrete-args axis (0633-R1): `(Duo Int Str)` vs `(Duo Str Int)` have
    // divergent per-field heap categories, so they MUST NOT share glue.
    let duo_int_str = adt("user", "Duo", vec![Type::Int, Type::String]);
    let duo_str_int = adt("user", "Duo", vec![Type::String, Type::Int]);
    assert_ne!(
        adt_drop_glue_name(&duo_int_str),
        adt_drop_glue_name(&duo_str_int),
        "same ADT, different concrete args (heap-category-divergent) must get \
         distinct drop-glue names — sharing them is the 0633 SIGBUS/leak"
    );

    // (ii) same bare name, DIFFERENT module ⇒ DIFFERENT glue. This is the module
    // axis (0633-R2): `ma/Thing` and `mb/Thing` are distinguished everywhere
    // upstream by `FQTypeName`; the glue name must not drop the module.
    let ma_thing = adt("ma", "Thing", vec![]);
    let mb_thing = adt("mb", "Thing", vec![]);
    assert_ne!(
        adt_drop_glue_name(&ma_thing),
        adt_drop_glue_name(&mb_thing),
        "same bare type name from different modules must get distinct drop-glue \
         names — the bare-name key dropped the module (0633 axis b)"
    );

    // (iii) same instantiation twice ⇒ ONE stable glue name — the identity the
    // `get_name` per-module re-emit dedup relies on (reuse is CORRECT here).
    assert_eq!(
        adt_drop_glue_name(&duo_int_str),
        adt_drop_glue_name(&adt("user", "Duo", vec![Type::Int, Type::String])),
        "one instantiation must produce one stable glue name (get_name reuse)"
    );

    // Nested concrete args participate in the identity: `(Box (Duo Int Str))`
    // and `(Box (Duo Str Int))` differ, so a Vec-of-Box glue does not collide
    // across nested-instantiation divergence.
    let box_duo_a = adt("user", "Box", vec![duo_int_str.clone()]);
    let box_duo_b = adt("user", "Box", vec![duo_str_int.clone()]);
    assert_ne!(
        adt_drop_glue_name(&box_duo_a),
        adt_drop_glue_name(&box_duo_b),
        "nested concrete-arg divergence must yield distinct glue"
    );

    // The mangle is a clean Cranelift symbol suffix (no `/`, spaces, or parens
    // from the `render_type` walk survive sanitization).
    let mangle = adt_instantiation_mangle(&duo_int_str);
    assert!(
        mangle.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'),
        "instantiation mangle must be a clean symbol: {mangle:?}"
    );
    // The module qualifier of the head AND of each concrete arg is present (the
    // two axes the bare key dropped): user (head), primitives (Int/String args).
    assert!(mangle.contains("user"), "head module present: {mangle:?}");
    assert!(mangle.contains("Duo"), "head type name present: {mangle:?}");
    assert!(
        mangle.contains("primitives") && mangle.contains("Int") && mangle.contains("String"),
        "concrete arg types present: {mangle:?}"
    );
}
