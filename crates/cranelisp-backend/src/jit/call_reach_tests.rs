//! M-1070-a: a call compiled through the JIT's module does not depend on
//! where the JIT places code (`design/backend/jit-object-convergence.md` §3).
//!
//! Placement follows the global allocator and cannot be forced out of range
//! deterministically, so the row observes the property that makes placement
//! irrelevant: the caller's machine code holds no pc-relative call relocation.
//! The bare `JITModule` leg is the control that proves the observation detects
//! a near call.

use cranelift::codegen::binemit::Reloc;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};

use super::Jit;

const CALLEE_RESULT: i64 = 7;

fn is_near_call(kind: Reloc) -> bool {
    matches!(kind, Reloc::Arm64Call | Reloc::X86CallPCRel4)
}

/// Define a callee returning [`CALLEE_RESULT`] and a caller that returns its
/// call through a `colocated` reference. Returns the caller and the relocation
/// kinds of its compiled code.
fn define_caller_of_local_callee(module: &mut impl Module) -> (FuncId, Vec<Reloc>) {
    let mut sig = module.make_signature();
    sig.returns.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("callee", Linkage::Local, &sig)
        .expect("declare callee");
    let caller = module
        .declare_function("caller", Linkage::Local, &sig)
        .expect("declare caller");
    let mut ctx = module.make_context();
    let mut fbc = FunctionBuilderContext::new();

    ctx.func.signature = sig.clone();
    {
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let value = fb.ins().iconst(types::I64, CALLEE_RESULT);
        fb.ins().return_(&[value]);
        fb.finalize();
    }
    module
        .define_function(callee, &mut ctx)
        .expect("define callee");
    module.clear_context(&mut ctx);

    ctx.func.signature = sig;
    let callee_ref = module.declare_func_in_func(callee, &mut ctx.func);
    assert!(
        ctx.func.dfg.ext_funcs[callee_ref].colocated,
        "a Local callee is referenced colocated, as the backend's own callees are"
    );
    {
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let call = fb.ins().call(callee_ref, &[]);
        let result = fb.inst_results(call)[0];
        fb.ins().return_(&[result]);
        fb.finalize();
    }
    module
        .define_function(caller, &mut ctx)
        .expect("define caller");
    let relocs = ctx
        .compiled_code()
        .expect("compiled caller")
        .buffer
        .relocs()
        .iter()
        .map(|reloc| reloc.kind)
        .collect();
    (caller, relocs)
}

// spec: spec/03-types.md §3.10 — ACT-1070, a JIT call reaches its callee wherever it is placed
#[test]
fn jit_module_compiles_a_colocated_call_far() {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let (caller, relocs) = define_caller_of_local_callee(jit.jit_module());
    assert!(
        !relocs.iter().any(|&kind| is_near_call(kind)),
        "a call through the JIT's module must not be pc-relative: {relocs:?}"
    );

    jit.finalize().expect("finalize");
    // SAFETY: `caller` was just finalized with signature `extern "C" fn() -> i64`.
    let call: extern "C" fn() -> i64 =
        unsafe { std::mem::transmute(jit.get_finalized_ptr(caller)) };
    assert_eq!(call(), CALLEE_RESULT, "the far call reaches the callee");
}

// spec: spec/03-types.md §3.10 — ACT-1070, control: a bare JITModule compiles the call near
#[test]
fn bare_jit_module_compiles_a_colocated_call_near() {
    let isa = crate::cache::object::build_isa(false).expect("ISA");
    let mut module = JITModule::new(JITBuilder::with_isa(
        isa,
        cranelift_module::default_libcall_names(),
    ));
    let (_, relocs) = define_caller_of_local_callee(&mut module);
    assert!(
        relocs.iter().any(|&kind| is_near_call(kind)),
        "the control must observe a pc-relative call: {relocs:?}"
    );
}
