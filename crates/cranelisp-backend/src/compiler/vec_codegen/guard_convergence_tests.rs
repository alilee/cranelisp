//! S122 Q9 — Vec copies use the canonical nullary-tag guard and polarity.

use super::*;
use crate::compiler::fn_compiler::assert_threshold_guarded_adds;
use crate::jit::Jit;

fn elem_adapter_clif(guarded: bool) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fn_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fn_ctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let val = builder.block_params(entry)[0];
    emit_elem_inc_body(&mut builder, module, val, guarded);
    builder.finalize();
    ctx.func.display().to_string()
}

fn mixed_vec_get_clif() -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let mut panic_sig = module.make_signature();
    panic_sig.params.push(AbiParam::new(types::I64));
    panic_sig.params.push(AbiParam::new(types::I64));
    let panic_id = module
        .declare_function("runtime/panic", Linkage::Import, &panic_sig)
        .expect("declare panic import");

    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fn_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fn_ctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let vec_val = builder.block_params(entry)[0];
    let idx_val = builder.block_params(entry)[1];
    let elem = emit_vec_get_core(
        &mut builder,
        module,
        panic_id,
        Some(HeapCategory::Mixed),
        vec_val,
        idx_val,
        Span::SYNTHETIC,
        false,
    )
    .expect("emit mixed vec-get");
    builder.ins().return_(&[elem]);
    builder.finalize();
    ctx.func.display().to_string()
}

// spec: design/backend/s122-closure.md §3 — both the generated element-copy
// adapter and an inline Mixed-element Vec read place their RC increment on the
// not-taken arm of `value < NULLARY_TAG_THRESHOLD` through the shared emitter.
#[test]
fn vec_copy_shapes_share_the_canonical_nullary_guard_polarity() {
    let adapter = elem_adapter_clif(true);
    assert_threshold_guarded_adds(&adapter, 1, "mixed Vec element adapter");

    let inline = mixed_vec_get_clif();
    assert_threshold_guarded_adds(&inline, 1, "inline mixed Vec read");
}

// The NeverHeap/AlwaysHeap adapter control remains unguarded.
#[test]
fn always_heap_element_adapter_keeps_the_unguarded_control() {
    let adapter = elem_adapter_clif(false);
    assert_eq!(adapter.matches("atomic_rmw.i64 add").count(), 1);
    assert!(!adapter.contains("icmp.i64 ult"));
}
