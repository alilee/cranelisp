use crate::compiler::{CompileContext, FnCompiler};
use crate::test_support::{empty_tables, probe_glue_registry};
use cranelift::prelude::*;
use cranelift_module::Module;
use cranelisp_types::{CranelispError, ModuleFullPath, Span, Type};
use std::collections::HashMap;

// spec: design/backend/s121-c4-visit.md §7.3, §8.5 — absence is not a scalar type.
#[test]
fn element_release_requires_type_but_accepts_scalar_without_adapter() {
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
    let ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).unwrap();
    let tables = empty_tables();
    let func_ids = HashMap::new();
    let func_arities = HashMap::new();
    let module_path = ModuleFullPath::from("user");
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        current_module: module_path.clone(),
        alloc_func_id: ids.alloc,
        dealloc_func_id: ids.dealloc.unwrap(),
        alloc_string_func_id: ids.alloc_string,
        panic_func_id: ids.panic,
        vec_new_func_id: ids.vec_new,
        vec_drop_func_id: ids.vec_drop,
    };
    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::user(0, 0),
        jit.jit_module().make_signature(),
    );
    let mut builder_ctx = FunctionBuilderContext::new();
    let builder = FunctionBuilder::new(&mut func, &mut builder_ctx);
    let mut glue = probe_glue_registry(module_path, &ids);
    let mut compiler =
        FnCompiler::inner(builder, jit.jit_module(), ctx, &mut glue, 0, HashMap::new());
    let span = Span::new(117, 129);
    assert_eq!(
        compiler
            .request_elem_dec_adapter(&Some(Type::Int), span)
            .unwrap(),
        None
    );
    let error = compiler.request_elem_dec_adapter(&None, span).unwrap_err();
    let CranelispError::CodegenError { message, location } = error else {
        panic!("expected located codegen refusal, got {error:?}");
    };
    assert!(message.contains("missing element type"), "{message}");
    assert_eq!(location.span, span);
}
