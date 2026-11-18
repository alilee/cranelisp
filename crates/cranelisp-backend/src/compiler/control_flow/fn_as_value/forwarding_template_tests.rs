//! The forwarding template of generated wrappers (`uniform-counting.md` §3.3).
//!
//! Each probe is a real JIT function `probe(env, p…) -> first argument` whose
//! body is the template over a hand-built environment; the cells read the
//! counts the template leaves on the captures and parameters it forwards.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::HeapHeader;

use super::forwarding_template_args;
use crate::heap::HeapCategory;
use crate::jit::Jit;
use cranelisp_intrinsics::alloc::HeapClosure;

/// Build `probe(env, params…)`: the template over `captures`, returning the
/// argument at `returned`. Returns the JIT and the entry address.
fn probe(captures: &[HeapCategory], params: usize, returned: usize) -> (Jit, *const u8, String) {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let mut sig = module.make_signature();
    for _ in 0..=params {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));
    let func = module
        .declare_function("forwarding_probe", Linkage::Export, &sig)
        .expect("declare probe");
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut fctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let block = builder.block_params(entry).to_vec();
        let args = forwarding_template_args(&mut builder, module, block[0], captures, &block[1..]);
        assert_eq!(
            args.len(),
            captures.len() + params,
            "one argument per capture and parameter"
        );
        builder.ins().return_(&[args[returned]]);
        builder.seal_all_blocks();
        builder.finalize();
    }
    let clif = ctx.func.display().to_string();
    module
        .define_function(func, &mut ctx)
        .expect("define probe");
    module.clear_context(&mut ctx);
    module.finalize_definitions().expect("finalize probe");
    let code = jit.jit_module().get_finalized_function(func);
    (jit, code, clif)
}

fn string(text: &str) -> i64 {
    cranelisp_intrinsics::heap_string::alloc_string(text.as_bytes()) as i64
}

/// SAFETY: `ptr` must name a live heap allocation carrying a `HeapHeader`.
unsafe fn rc_of(ptr: i64) -> i64 {
    unsafe { *((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const i64) }
}

/// A closure environment with `captures` in its capture slots.
fn environment(captures: &[i64]) -> Vec<i64> {
    let words = HeapClosure::capture_offset(captures.len()) as usize / 8;
    let mut env = vec![0i64; words];
    for (slot, value) in captures.iter().enumerate() {
        env[HeapClosure::capture_offset(slot) as usize / 8] = *value;
    }
    env
}

// spec: design/backend/uniform-counting.md §3.3 — an applied heap capture is
// forwarded duplicated, once per call: the environment keeps its reference.
#[test]
fn an_applied_heap_capture_is_forwarded_duplicated() {
    let (_jit, code, _) = probe(&[HeapCategory::AlwaysHeap], 1, 0);
    let f: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code) };
    let captured = string("captured");
    let env = environment(&[captured]);
    assert_eq!(f(env.as_ptr() as i64, 0), captured, "captures come first");
    // SAFETY: `captured` is live on the environment's reference.
    assert_eq!(unsafe { rc_of(captured) }, 2, "one duplicate per call");
    f(env.as_ptr() as i64, 0);
    // SAFETY: as above.
    assert_eq!(
        unsafe { rc_of(captured) },
        3,
        "and one more on the next call"
    );
}

// spec: design/backend/uniform-counting.md §3.3 (NEGATIVE) — a parameter moves:
// the template emits nothing for it, and a scalar capture is not counted.
#[test]
fn a_parameter_moves_and_a_scalar_capture_is_not_counted_neg() {
    let (_jit, code, clif) = probe(&[HeapCategory::NeverHeap], 1, 1);
    assert!(
        !clif.contains("atomic_rmw"),
        "no RC operation for a parameter or a scalar capture:\n{clif}"
    );
    let f: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code) };
    let param = string("param");
    let env = environment(&[7]);
    assert_eq!(
        f(env.as_ptr() as i64, param),
        param,
        "parameters follow captures"
    );
    // SAFETY: `param` is live on the reference the call moved back out.
    assert_eq!(
        unsafe { rc_of(param) },
        1,
        "the parameter's reference moves"
    );
}
