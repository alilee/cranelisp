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
        IoCombinator::Pure => vec![ConcreteType::String],
    }
}

fn name_of(combinator: IoCombinator) -> &'static str {
    match combinator {
        IoCombinator::Bind => "bind",
        IoCombinator::Race => "race",
        IoCombinator::Select => "select",
        IoCombinator::Sleep => "sleep",
        IoCombinator::Pure => "pure",
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
    let lowering = match path {
        Path::Direct => None,
        Path::Wrapper => Some(HostPromisedLowering::Io(combinator)),
    };
    render_call(
        name_of(combinator),
        operand_types(combinator),
        io_string(),
        lowering,
    )
    .clif
}

/// One probe body's CLIF and the names of the functions its module declares.
struct Probe {
    clif: String,
    declared: Vec<String>,
}

/// Render `probe(p0, p1, …)` whose body applies the `BuiltinFn` carrier `name`
/// to its parameters: directly when `lowering` is `None`, else through
/// [`FnCompiler::lower_host_promised`] with that lowering.
fn render_call(
    name: &str,
    types: Vec<ConcreteType>,
    result_ty: ConcreteType,
    lowering: Option<HostPromisedLowering>,
) -> Probe {
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
            ty: ConcreteType::Fn(types.clone(), Box::new(result_ty.clone())),
            resolution: VarRef::Global(target.clone()),
        }),
        args,
        span: Span::new(1, 2),
        resolved_call: Some(Box::new(ResolvedCall::BuiltinFn {
            name: Symbol::from(name),
        })),
        ty: result_ty,
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
    let result = match lowering {
        None => {
            for (i, ((p, ty), v)) in params.iter().zip(&types).zip(&values).enumerate() {
                compiler
                    .bind_binder(Intro::Param(i), p, *v, ty.clone())
                    .expect("bind parameter");
            }
            compiler.compile_expr(&call).expect("direct call")
        }
        Some(lowering) => compiler
            .lower_host_promised(lowering, &target, &types, &values, Span::new(1, 2))
            .expect("wrapper lowering"),
    };
    compiler.builder.ins().return_(&[result]);
    compiler.builder.seal_all_blocks();
    compiler.builder.finalize();
    let declared = jit
        .jit_module()
        .declarations()
        .get_functions()
        .filter_map(|(_, decl)| decl.name.clone())
        .collect();
    Probe {
        clif: func.display().to_string(),
        declared,
    }
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

// spec: design/backend/compile-to-module.md §12.1 "One lowering per primitive"
// — the classification is load-bearing: an unclassified `pure` carrier falls
// to the by-name extern fallback and imports a symbol named `pure` that
// nothing defines.
#[test]
fn direct_pure_declares_no_import_named_pure() {
    let probe = render_call(
        "pure",
        vec![ConcreteType::String],
        primitives_adt("IO", vec![ConcreteType::String]),
        None,
    );
    assert!(
        !probe.declared.iter().any(|name| name == "pure"),
        "a direct `(pure x)` must lower inline, not import `pure`: {:?}\n{}",
        probe.declared,
        probe.clif
    );
}

/// `probe(p0)` whose body is `(pure p0)` over a `payload`, along both paths.
fn render_pure(payload: ConcreteType) -> (Probe, Probe) {
    let io = primitives_adt("IO", vec![payload.clone()]);
    let direct = render_call("pure", vec![payload.clone()], io.clone(), None);
    let wrapper = render_call(
        "pure",
        vec![payload],
        io,
        Some(HostPromisedLowering::Io(IoCombinator::Pure)),
    );
    (direct, wrapper)
}

// spec: design/backend/compile-to-module.md §12.1 "One lowering per primitive";
// design/backend/non-concrete-release-contract.md §5.3 — direct and first-class
// `pure` emit one `Pure` node whose glue word comes from the payload type: the
// glue address for a heap payload, 0 for a scalar, never `Claimed(1)`.
#[test]
fn pure_direct_and_wrapper_emit_one_pure_node_with_typed_glue() {
    let (direct, wrapper) = render_pure(ConcreteType::String);
    assert_eq!(
        direct.clif, wrapper.clif,
        "String: the wrapper's node differs"
    );
    assert!(
        direct.clif.contains("func_addr.i64"),
        "a heap payload stamps its glue address:\n{}",
        direct.clif
    );
    assert!(
        !direct.clif.contains("iconst.i64 1\n"),
        "construction never stamps Claimed(1):\n{}",
        direct.clif
    );

    let (direct, wrapper) = render_pure(ConcreteType::Int);
    assert_eq!(direct.clif, wrapper.clif, "Int: the wrapper's node differs");
    assert!(
        !direct.clif.contains("func_addr"),
        "a scalar payload owns no glue:\n{}",
        direct.clif
    );
    assert!(
        direct
            .clif
            .contains(&format!("iconst.i64 {}\n", cranelisp_platform::IO_TAG_PURE)),
        "the node carries the Pure tag:\n{}",
        direct.clif
    );
    assert!(
        !direct.clif.contains("iconst.i64 1\n"),
        "construction never stamps Claimed(1):\n{}",
        direct.clif
    );
}
