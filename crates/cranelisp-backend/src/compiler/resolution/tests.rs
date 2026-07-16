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

// spec: design/arch/fixmes/0350 — the span-derived closure DROP-GLUE name
//   (`runtime/closure_drop_glue_<start>_<end>`) MUST be uniquified per
//   monomorphic instance the SAME way the lambda body name is (0347), else
//   N mono copies of one lambda span emit N drop-glue defs with the
//   identical name → linker `Duplicate definition of identifier`.
#[test]
fn closure_drop_glue_name_uniquifies_per_mono_instance() {
    use cranelisp_types::Symbol;
    // Two monomorphic instances of one source fn — the same shape that
    // collided on the lambda body name in 0347.
    let a = inner_fn_discriminator_for(Some(&Symbol::from("apply$Int+Vec")));
    let b = inner_fn_discriminator_for(Some(&Symbol::from("apply$Float+Vec")));

    // The composed drop-glue names (the 0350 collision surface) differ.
    let span = (2004usize, 2022usize);
    let glue_a =
        format!("runtime/closure_drop_glue_{a}{}_{}", span.0, span.1);
    let glue_b =
        format!("runtime/closure_drop_glue_{b}{}_{}", span.0, span.1);
    assert_ne!(
        glue_a, glue_b,
        "two mono copies of one lambda span must emit distinct drop-glue \
         symbols (else the 2nd define_function collides)"
    );

    // The drop-glue name MUST share the lambda body's discriminator scheme
    // so the (body, drop-glue) pair stay paired per mono instance.
    let body_a = format!("__lambda_{a}{}_{}__", span.0, span.1);
    let body_b = format!("__lambda_{b}{}_{}__", span.0, span.1);
    assert!(
        glue_a.contains(&a) && body_a.contains(&a),
        "body+drop-glue of instance A must carry the same discriminator"
    );
    assert!(
        glue_b.contains(&b) && body_b.contains(&b),
        "body+drop-glue of instance B must carry the same discriminator"
    );

    // No enclosing fn: empty prefix, span alone disambiguates — the
    // pre-0350 behaviour for top-level / nested-lambda scopes is preserved.
    let none = inner_fn_discriminator_for(None);
    assert_eq!(none, "");
    assert_eq!(
        format!("runtime/closure_drop_glue_{none}{}_{}", span.0, span.1),
        "runtime/closure_drop_glue_2004_2022"
    );
}
