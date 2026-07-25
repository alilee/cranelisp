//! S97 — a data constructor used as a first-class fn-value must INLINE-construct
//! in its generated wrapper body, never call a (possibly missing) function.
//!
//! Pins the seam of the constructor-as-fn-value SIGSEGV
//! (`tests/regression.rs::constructor_as_fn_value_applied_indirectly_does_not_segfault`,
//! spec §5.2.7 "data constructors are functions"). A PRIMITIVE constructor
//! (`Some` / `None`) has no callable JIT body — its GOT slot is not a
//! constructor function — so the old fn-as-value wrapper's GOT-indirect call
//! jumped to a non-function and crashed. `emit_adt_construct_into` is the
//! builder-parameterized construction the wrapper now emits instead: `alloc` +
//! tag store + field stores for an N-field constructor, and a bare tag `iconst`
//! (NO allocation, NO call) for a nullary constructor.

use super::emit_adt_construct_into;
use crate::jit::Jit;
use cranelift::prelude::*;
use cranelift_module::Module;
use cranelisp_types::Span;

/// Build a throwaway function whose body is `emit_adt_construct_into(tag, params)`
/// over `n_fields` i64 params, and return its CLIF text.
fn clif_of_construct(tag: usize, n_fields: usize) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let ids = jit.declare_intrinsics().expect("intrinsics declare");
    let alloc_id = ids.alloc;

    let module = jit.jit_module();
    let mut ctx = module.make_context();
    let mut fctx = FunctionBuilderContext::new();
    for _ in 0..n_fields {
        ctx.func.signature.params.push(AbiParam::new(types::I64));
    }
    ctx.func.signature.returns.push(AbiParam::new(types::I64));

    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let params: Vec<Value> = builder.block_params(entry).to_vec();

    let result = emit_adt_construct_into(
        &mut builder,
        module,
        alloc_id,
        tag,
        &params,
        Span::SYNTHETIC,
    )
    .expect("emit_adt_construct_into");
    builder.ins().return_(&[result]);
    builder.seal_all_blocks();
    builder.finalize();

    format!("{}", ctx.func.display())
}

// spec: spec/05-definitions.md §5.2.7 — an N-field constructor as a value
// inline-constructs (alloc + tag + field stores), so the wrapper never depends
// on a callable constructor function (which a primitive constructor lacks).
#[test]
fn one_field_constructor_wrapper_inline_constructs_with_alloc_and_stores() {
    let clif = clif_of_construct(1, 1); // tag=1 (e.g. Option's Some), 1 field

    assert!(
        clif.contains("call ") && clif.contains("store"),
        "an N-field constructor-as-value wrapper MUST inline-construct (an alloc \
         `call` + field `store`s), not dispatch through a GOT-indirect call to a \
         missing constructor function (the S97 SIGSEGV seam). CLIF:\n{clif}"
    );
    // The crash path was a `call_indirect` through a non-function GOT slot — the
    // inline-construct path must NOT emit one.
    assert!(
        !clif.contains("call_indirect"),
        "the inline construct must not emit a GOT-indirect call (the crash path). \
         CLIF:\n{clif}"
    );
}

// spec: spec/05-definitions.md §5.2.7 — a nullary constructor folds to a bare
// tag (no allocation, no call).
#[test]
fn nullary_constructor_wrapper_is_a_bare_tag_no_alloc() {
    let clif = clif_of_construct(0, 0); // tag=0, nullary

    assert!(
        clif.contains("iconst.i64 0"),
        "a nullary constructor-as-value must fold to a bare tag iconst. CLIF:\n{clif}"
    );
    assert!(
        !clif.contains("call"),
        "a nullary constructor-as-value must NOT allocate or call. CLIF:\n{clif}"
    );
}
