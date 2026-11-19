//! M-1063 (`compile-to-module.md` §12.1): a wrapper whose target is a
//! host-promised IO combinator emits the node direct application emits — the
//! same tag, fields and result disposer — because both reach one lowering.

use cranelift::prelude::*;
use cranelift_codegen::ir::{Function, UserFuncName};
use cranelift_module::Module;
use cranelisp_types::{
    ApplyRef, ConcreteType, FQSymbol, FQTypeName, ModuleFullPath, MonoExpr, ResolvedCall, Span,
    Symbol, SymbolTable, TypeName, VarRef,
};
use dashmap::DashMap;

use super::{HostPromisedLowering, IoCombinator};
use crate::compiler::ownership_plan::Intro;
use crate::compiler::{CompileContext, FnCompiler};

fn primitives_adt(name: &str, args: Vec<ConcreteType>) -> ConcreteType {
    ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name)),
        args,
    )
}

/// `(IO String)`: a heap payload, so the result disposer is a glue address.
fn io_string() -> ConcreteType {
    primitives_adt("IO", vec![ConcreteType::String])
}

/// The operand types of one saturated call of `combinator`.
fn operand_types(combinator: IoCombinator) -> Vec<ConcreteType> {
    match combinator {
        IoCombinator::Bind => vec![
            io_string(),
            ConcreteType::Fn(vec![ConcreteType::String], Box::new(io_string())),
        ],
        IoCombinator::Race => vec![io_string(), io_string()],
        IoCombinator::Select => vec![primitives_adt("Vec", vec![io_string()])],
        IoCombinator::Sleep => vec![ConcreteType::Int],
    }
}

fn name_of(combinator: IoCombinator) -> &'static str {
    match combinator {
        IoCombinator::Bind => "bind",
        IoCombinator::Race => "race",
        IoCombinator::Select => "select",
        IoCombinator::Sleep => "sleep",
    }
}

enum Path {
    /// `(combinator p0 p1 …)` compiled as an expression over the parameters.
    Direct,
    /// The wrapper's rule: the lowering over the evaluated parameters.
    Wrapper,
}

/// Render `probe(p0, p1, …)` whose body calls `combinator` on its parameters
/// along `path`.
fn render(combinator: IoCombinator, path: Path) -> String {
    let name = name_of(combinator);
    let types = operand_types(combinator);
    let user = ModuleFullPath::from("user");
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    tables.insert(user.clone(), SymbolTable::new(user.clone()));
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).expect("intrinsics");
    let func_ids = std::collections::HashMap::new();
    let func_arities = std::collections::HashMap::new();
    let ctx = CompileContext {
        func_ids: &func_ids,
        unit_slots: &std::collections::HashMap::new(),
        func_arities: &func_arities,
        symbol_tables: &tables,
        trace_modules: &std::collections::BTreeSet::new(),
        current_module: user.clone(),
        alloc_func_id: ids.alloc,
        dealloc_func_id: ids.dealloc.expect("dealloc"),
        alloc_string_func_id: ids.alloc_string,
        panic: ids.panic,
        vec_new_func_id: ids.vec_new,
        vec_drop_func_id: ids.vec_drop,
    };
    let mut glue = crate::test_support::probe_glue_registry(user.clone(), &ids);

    let params: Vec<Symbol> = (0..types.len())
        .map(|i| Symbol::from(format!("p{i}")))
        .collect();
    let args: Vec<MonoExpr> = params
        .iter()
        .zip(&types)
        .map(|(p, ty)| MonoExpr::Var {
            name: p.clone(),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ty.clone(),
            resolution: VarRef::Local {
                binder: p.clone(),
                binding_span: Span::SYNTHETIC,
            },
        })
        .collect();
    let target = FQSymbol {
        module: ModuleFullPath::from("primitives"),
        symbol: Symbol::from(name),
    };
    let call = MonoExpr::Apply {
        dispatch: ApplyRef::Dispatch(target.clone()),
        callee: Box::new(MonoExpr::Var {
            name: Symbol::from(name),
            span: Span::new(1, 2),
            resolved_call: None,
            ty: ConcreteType::Fn(types.clone(), Box::new(io_string())),
            resolution: VarRef::Global(target.clone()),
        }),
        args,
        span: Span::new(1, 2),
        resolved_call: Some(Box::new(ResolvedCall::BuiltinFn {
            name: Symbol::from(name),
        })),
        ty: io_string(),
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    };

    let mut sig = jit.jit_module().make_signature();
    for _ in &types {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));
    let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig);
    let mut fctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut func, &mut fctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let values = builder.block_params(entry).to_vec();

    let plan = FnCompiler::<crate::jit::FarCallModule>::plan_body(&call, &params, &[], "probe")
        .expect("plan");
    let mut compiler = FnCompiler::inner(
        builder,
        jit.jit_module(),
        ctx,
        crate::compiler::census::Frame::for_test(),
        Span::SYNTHETIC,
        &mut glue,
        types.len(),
        plan,
    );
    let result = match path {
        Path::Direct => {
            for (i, ((p, ty), v)) in params.iter().zip(&types).zip(&values).enumerate() {
                compiler
                    .bind_binder(Intro::Param(i), p, *v, ty.clone())
                    .expect("bind parameter");
            }
            compiler.compile_expr(&call).expect("direct call")
        }
        Path::Wrapper => compiler
            .lower_host_promised(
                HostPromisedLowering::Io(combinator),
                &target,
                &types,
                &values,
                Span::new(1, 2),
            )
            .expect("wrapper lowering"),
    };
    compiler.builder.ins().return_(&[result]);
    compiler.builder.seal_all_blocks();
    compiler.builder.finalize();
    func.display().to_string()
}

// spec: design/backend/compile-to-module.md §12.1 "One lowering per primitive"
// (M-1063) — for each IO combinator with a value face, the wrapper's lowering
// and direct application emit identical CLIF: the node's tag, its fields and
// the result disposer derived from the first operand's type.
#[test]
fn wrapper_and_direct_application_emit_one_io_node() {
    for combinator in [IoCombinator::Bind, IoCombinator::Race, IoCombinator::Select] {
        let direct = render(combinator, Path::Direct);
        let wrapper = render(combinator, Path::Wrapper);
        assert!(
            direct.contains("func_addr"),
            "{combinator:?}: a heap payload's disposer is a glue address\n{direct}"
        );
        assert_eq!(
            direct, wrapper,
            "{combinator:?}: the wrapper's node differs"
        );
    }
}
