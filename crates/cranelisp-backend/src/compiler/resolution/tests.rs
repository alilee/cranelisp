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
    assert_ne!(
        a, b,
        "distinct mono instances must yield distinct discriminators"
    );

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

// The ADT drop-glue INSTANTIATION-identity battery that lived here is DELETED
// with its subject (S118 slice S6, §8): `adt_drop_glue_name` /
// `adt_instantiation_mangle` / `escape_symbol` were the naming half of the
// SECOND named-glue identity home, and a second identity scheme for one concept
// is the state arch ruling 10 exists to prevent. The two claims the battery
// carried — glue identity keys on the FULL concrete instantiation (module + type
// name + concrete args), and distinct spellings never collide — are now
// properties of the types-owned `drop_glue_symbol_name` and are pinned there:
// `drop_glue::tests::glue_identity_discriminates_module_name_and_concrete_args`.

// ── R4 — the GOT data-symbol mint (S115 W3 change-set 4) ─────────────────
//
// `design/arch/safety-invariants.md` §4 R4 ("every mangle semantic-identity →
// symbol is injective, or additionally disambiguator-keyed"); census in
// `design/backend/s115-carrier-and-rc-sweep.md` §4, where `got_data_symbol_name`
// is the ONE backend-facing OWED-witness.
//
// TWO facts are pinned here, and only one of them is closable inside this crate:
//
// 1. **P7 agreement (closed).** The scheme's canonical home is
//    `cranelisp_types::got_data_symbol_name` (relocated DOWN at S76 so it is not
//    duplicated). The backend REFERENCES the symbol; **int DEFINES** it off the
//    types-owned fn. A backend-local second body is a definer/consumer
//    divergence channel — verified the hard way during this change-set: escaping
//    the path here alone made every cross-module call fail with
//    `can't resolve symbol __cranelisp_got_compare_dord` and the whole stdlib
//    stopped loading. This cell is that fence.
// 2. **Injectivity (CLOSED S119, FIXME 0748).** The types-owned mint now
//    escapes injectively (`_`→`__`, `.`→`_d`, `-`→`_h`, `_u{cp:06x}`
//    catch-all; alphanumerics fixed points; `_entry` outside the image). The
//    fix landed at the types home exactly because a one-sided change here
//    breaks the definer/consumer agreement (see 1).

// spec: design/arch/principles/07-single-source-of-truth.md — the GOT
// data-symbol scheme has ONE home (`cranelisp_types::got_data_symbol_name`); the
// backend's `got_data_symbol_name` is a forward, never a second body. A
// divergence breaks every cross-module GOT-indirect call at link time (the
// consumer emits a relocation against a name the definer never registers).
#[test]
fn got_data_symbol_name_agrees_with_the_types_owned_home() {
    use cranelisp_types::ModuleFullPath;
    for path in [
        "",
        "user",
        "prelude",
        "primitives",
        "compare.ord",
        "fn.option.test",
        "a.b",
        "a_b",
        "a-b",
        "my-lib.sub_mod.deep",
    ] {
        let m = ModuleFullPath::from(path);
        assert_eq!(
            got_data_symbol_name(&m),
            cranelisp_types::got_data_symbol_name(&m),
            "backend and types MUST mint the identical GOT data symbol for {path:?} \
             — the backend references what int defines"
        );
    }
}

// spec: design/arch/safety-invariants.md §4 R4 — the pinned link-time ABI names.
// `__cranelisp_got_primitives` is an `export_name` LITERAL in
// `cranelisp-primitives/src/lib.rs`, so this mint must agree with it exactly;
// any future injectivity fix (FIXME 0748) must keep purely-alphanumeric paths as
// fixed points or move that literal in the same change-set.
#[test]
fn got_data_symbol_name_matches_the_pinned_link_time_abi_literals() {
    use cranelisp_types::ModuleFullPath;
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("primitives")),
        "__cranelisp_got_primitives",
        "must match the `export_name` literal in cranelisp-primitives"
    );
    for path in ["prelude", "user", "macros"] {
        assert_eq!(
            got_data_symbol_name(&ModuleFullPath::from(path)),
            format!("__cranelisp_got_{path}")
        );
    }
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("")),
        "__cranelisp_got__entry"
    );
}

// spec: design/arch/safety-invariants.md §4 R4 — the R4 witness, INVERTED at
// S119 (FIXME 0748 fixed at the types home): the injective escape mints
// DISTINCT GOT slab data symbols for `a.b` and `a_b`. The types-side
// round-trip battery (`cranelisp-types/src/module/tests.rs`) carries the
// full injectivity argument; this cell is the backend-visible fence.
#[test]
fn got_data_symbol_name_collision_is_the_owed_r4_witness() {
    use cranelisp_types::ModuleFullPath;
    assert_ne!(
        got_data_symbol_name(&ModuleFullPath::from("a.b")),
        got_data_symbol_name(&ModuleFullPath::from("a_b")),
        "R4 (FIXME 0748, fixed S119): two distinct modules must never share \
         one GOT slab data symbol"
    );
}
