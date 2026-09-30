//! Value-wrapper and auto-curry adaptation against the derived entry
//! convention (`design/backend/non-concrete-release-contract.md` §7.6, the §9
//! "fn_as_value wrapper and auto-curry" row).
//!
//! The wrapper owns every argument it receives (closure protocol). It releases
//! one after the target call only where the target borrows it, which only a
//! compiled body can do. The discriminating pair is a borrowing body, which
//! keeps its release, and an extern shim declaring the same `Borrowed` mode,
//! which gets none: deleting every wrapper release, or keying the release off
//! the declared mode, fails one half.

use cranelift::codegen::ir::{Function, UserFuncName};
use cranelift::prelude::*;
use cranelift_module::Module;
use cranelisp_types::{
    CallableOrigin, FQSymbol, Mode, ModeSummary, ModuleFullPath, Realization, ResolvedCall,
    ResultMode, Scheme, Span, Symbol, SymbolTable, Type, Visibility,
};
use std::collections::HashMap;

use crate::compiler::{CompileContext, FnCompiler};
use crate::jit::{Jit, declare_intrinsics_generic};

fn borrowed_read() -> ModeSummary {
    ModeSummary {
        param_modes: vec![Mode::Borrowed],
        result: ResultMode::Fresh,
        ..ModeSummary::default()
    }
}

fn string_to_int() -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Fn(vec![Type::String], Box::new(Type::Int)),
    }
}

fn primitives_key(name: &str) -> FQSymbol {
    FQSymbol {
        module: ModuleFullPath::from("primitives"),
        symbol: Symbol::from(name),
    }
}

/// A `primitives` table holding `name` as an extern shim that declares a
/// borrowed read — the shape of the six string externs of ACT-0974.
fn borrowed_extern(name: &str) -> SymbolTable {
    let mut table = SymbolTable::new(ModuleFullPath::from("primitives"));
    table
        .install_extern(
            Symbol::from(name),
            string_to_int(),
            vec![Symbol::from("s")],
            None,
            0,
            None,
            Some(borrowed_read()),
            Visibility::Public,
        )
        .expect("install extern fixture");
    table
}

/// A `user` table holding `peek` as a compiled body that borrows its argument.
fn borrowing_body() -> SymbolTable {
    let variant = cranelisp_types::DefnVariant {
        params: vec![("s".into(), None)],
        body: cranelisp_types::Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        },
        span: Span::SYNTHETIC,
    };
    let user = ModuleFullPath::from("user");
    let name = Symbol::from("peek");
    let view = crate::test_support::test_codegen_view(&name, &variant, &HashMap::new());
    let mut table = SymbolTable::new(user.clone());
    table
        .install_concrete(
            name.clone(),
            string_to_int(),
            vec![Symbol::from("s")],
            None,
            0,
            CallableOrigin::Plain,
            Realization::Body {
                view: view.clone(),
                code: None,
            },
            Some(variant),
            vec![],
            Visibility::Public,
        )
        .expect("install body fixture");
    table
        .publish_body_ownership(
            &crate::test_support::binding_target(&user, &name),
            borrowed_read(),
            view,
        )
        .expect("publish the body's borrowing summary");
    table
}

/// How the wrapper reaches its target.
enum Reach<'r> {
    /// The fn-as-value wrapper tail, keyed by the target's storage key.
    Wrapper(&'r FQSymbol),
    /// The auto-curry target call, from the typechecker's resolution.
    Curry(ResolvedCall),
}

/// Emit a one-argument wrapper body reaching `reach` and return its CLIF.
fn wrapper_clif(tables: Vec<SymbolTable>, reach: Reach) -> String {
    let symbol_tables = crate::test_support::empty_tables();
    for table in tables {
        symbol_tables.insert(table.path.clone(), table);
    }
    let mut jit = Jit::new_with_symbols(&[]).expect("jit");
    let intrinsics = declare_intrinsics_generic(jit.jit_module()).expect("intrinsics");
    let (func_ids, func_arities) = (HashMap::new(), HashMap::new());
    let ctx = CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &symbol_tables,
        current_module: ModuleFullPath::from("user"),
        alloc_func_id: intrinsics.alloc,
        dealloc_func_id: intrinsics.dealloc.expect("dealloc"),
        alloc_string_func_id: intrinsics.alloc_string,
        panic_func_id: intrinsics.panic,
        vec_new_func_id: intrinsics.vec_new,
        vec_drop_func_id: intrinsics.vec_drop,
    };
    let mut enclosing_sig = jit.jit_module().make_signature();
    enclosing_sig.returns.push(AbiParam::new(types::I64));
    let mut enclosing = Function::with_name_signature(UserFuncName::user(0, 0), enclosing_sig);
    let mut enclosing_ctx = FunctionBuilderContext::new();
    let mut wrapper_sig = jit.jit_module().make_signature();
    wrapper_sig.params.push(AbiParam::new(types::I64));
    wrapper_sig.returns.push(AbiParam::new(types::I64));
    let mut wrapper = Function::with_name_signature(UserFuncName::user(0, 1), wrapper_sig);
    let mut wrapper_ctx = FunctionBuilderContext::new();
    let mut glue =
        crate::test_support::probe_glue_registry(ModuleFullPath::from("user"), &intrinsics);
    {
        let mut compiler = FnCompiler::inner(
            FunctionBuilder::new(&mut enclosing, &mut enclosing_ctx),
            jit.jit_module(),
            ctx,
            &mut glue,
            0,
            HashMap::new(),
        );
        let mut builder = FunctionBuilder::new(&mut wrapper, &mut wrapper_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let params = builder.block_params(entry).to_vec();
        let result = match reach {
            Reach::Wrapper(target) => compiler.emit_wrapper_call(
                &mut builder,
                &target.symbol,
                &params,
                Span::SYNTHETIC,
                None,
                None,
                Some(target),
            ),
            Reach::Curry(resolved) => compiler.emit_curry_target_call(
                &mut builder,
                &Symbol::from("target"),
                &params,
                Span::SYNTHETIC,
                Some(&resolved),
                None,
                None,
            ),
        }
        .expect("wrapper target call");
        builder.ins().return_(&[result]);
        builder.seal_all_blocks();
        builder.finalize();
    }
    wrapper.display().to_string()
}

fn post_call_releases(clif: &str) -> usize {
    let (_, after_call) = clif
        .split_once(" = call")
        .expect("the wrapper calls its target");
    after_call
        .lines()
        .filter(|line| line.contains("atomic_rmw") && line.contains("sub"))
        .count()
}

// spec: spec/12-runtime.md §12.3.1 — a value use of a borrowing body releases
// the argument the wrapper received and the body did not consume.
#[test]
fn a_borrowing_body_keeps_its_one_post_call_release() {
    let key = FQSymbol {
        module: ModuleFullPath::from("user"),
        symbol: Symbol::from("peek"),
    };
    let clif = wrapper_clif(vec![borrowing_body()], Reach::Wrapper(&key));
    assert_eq!(post_call_releases(&clif), 1, "{clif}");
}

// spec: spec/12-runtime.md §12.3.1 — an extern shim consumes its argument, so a
// release after the call would release it twice (ACT-0974 F1).
#[test]
fn an_extern_shim_declaring_a_borrow_gets_no_post_call_release() {
    let key = primitives_key("str-len");
    let clif = wrapper_clif(vec![borrowed_extern("str-len")], Reach::Wrapper(&key));
    assert!(clif.contains("call_indirect"), "{clif}");
    assert_eq!(post_call_releases(&clif), 0, "{clif}");
}

// spec: spec/12-runtime.md §12.3.1 — a curried extern is the same consuming
// entry, reached by name; its adapter emits nothing and stacks no wrapper.
#[test]
fn auto_curry_over_an_extern_shim_emits_no_adaptation() {
    let clif = wrapper_clif(
        vec![borrowed_extern("str-len")],
        Reach::Curry(ResolvedCall::BuiltinFn {
            name: "str-len".into(),
        }),
    );
    assert_eq!(
        clif.matches(" = call").count(),
        1,
        "one adapter, one call:\n{clif}"
    );
    assert_eq!(post_call_releases(&clif), 0, "{clif}");
}
