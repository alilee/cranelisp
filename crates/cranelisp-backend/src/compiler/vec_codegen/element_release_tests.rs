use crate::compiler::{CompileContext, FnCompiler};
use crate::jit::FarCallModule;
use crate::test_support::{empty_tables, probe_glue_registry};
use cranelift::prelude::*;
use cranelift_module::Module;
use cranelisp_types::{ConcreteType, CranelispError, ModuleFullPath, Span};
use std::collections::HashMap;

/// Run `probe` against a body compiler whose builder sits in an open block.
fn with_compiler(probe: impl FnOnce(&mut FnCompiler<'_, FarCallModule>)) {
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
    let ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).unwrap();
    let tables = empty_tables();
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let module_path = ModuleFullPath::from("user");
    let ctx = CompileContext {
        func_ids: &func_ids,
        unit_slots: &std::collections::HashMap::new(),
        func_arities: &func_arities,
        symbol_tables: &tables,
        trace_modules: &std::collections::BTreeSet::new(),
        current_module: module_path.clone(),
        alloc_func_id: ids.alloc,
        dealloc_func_id: ids.dealloc.unwrap(),
        alloc_string_func_id: ids.alloc_string,
        panic: ids.panic,
        vec_new_func_id: ids.vec_new,
        vec_drop_func_id: ids.vec_drop,
    };
    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::user(0, 0),
        jit.jit_module().make_signature(),
    );
    let mut builder_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);
    let block = builder.create_block();
    builder.switch_to_block(block);
    let mut glue = probe_glue_registry(module_path, &ids);
    let mut compiler = FnCompiler::inner(
        builder,
        jit.far_call_module(),
        ctx,
        crate::compiler::census::Frame::for_test(),
        Span::SYNTHETIC,
        &mut glue,
        0,
        crate::compiler::ownership_plan::OwnershipPlan::default(),
    );
    probe(&mut compiler);
}

fn expect_located_refusal(error: CranelispError, span: Span) {
    let CranelispError::CodegenError { message, location } = error else {
        panic!("expected located codegen refusal, got {error:?}");
    };
    assert!(message.contains("missing element type"), "{message}");
    assert_eq!(location.span, span);
}

// spec: design/backend/non-concrete-release-contract.md §7.4 — absence is not a scalar type.
#[test]
fn element_release_requires_type_but_accepts_scalar_without_adapter() {
    with_compiler(|compiler| {
        let span = Span::new(117, 129);
        assert_eq!(
            compiler
                .request_elem_dec_adapter(&Some(ConcreteType::Int), span)
                .unwrap(),
            None
        );
        let error = compiler.request_elem_dec_adapter(&None, span).unwrap_err();
        expect_located_refusal(error, span);
    });
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 2, §9 — the
// element increment pointer: a heap element resolves its increment function, a
// scalar element needs none, and a missing element type is a located refusal
// where it was once assumed to own no heap.
#[test]
fn element_increment_requires_type_and_resolves_by_category() {
    with_compiler(|compiler| {
        let span = Span::new(40, 52);
        compiler
            .resolve_elem_inc_fn_ptr(&Some(ConcreteType::String), span)
            .expect("a heap element resolves its increment");
        assert!(
            compiler
                .module
                .get_name("runtime/vec_elem_inc_heap")
                .is_some(),
            "a heap element's increment function is declared"
        );
        compiler
            .resolve_elem_inc_fn_ptr(&Some(ConcreteType::Int), span)
            .expect("a scalar element needs no increment");
        assert!(
            compiler
                .module
                .get_name("runtime/vec_elem_inc_mixed")
                .is_none(),
            "a scalar element declares no increment function"
        );
        let error = compiler.resolve_elem_inc_fn_ptr(&None, span).unwrap_err();
        expect_located_refusal(error, span);
    });
}
