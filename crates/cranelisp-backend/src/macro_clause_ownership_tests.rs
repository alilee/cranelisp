//! S122 Q4: ownership observations for real macro-clause compile targets.

use crate::test_support::*;
use cranelisp_types::{
    CallableArmDraft, CallableArmId, CallableOrigin, ConcreteType, FQTypeName, Life,
    MacroClauseDraft, MonoDefnVariant, MonoExpr, MonoMatchArm, Pattern, Scheme, SymbolRef,
    SynthSpec, TemplateBody, TemplateKind, TypeDefInfo, TypeName, VarRef,
};

fn fq_type(module: &str, name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name))
}

fn fn_scheme(params: Vec<Type>, result: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Fn(params, Box::new(result)),
    }
}

fn install_macro_types(tables: &DashMap<ModuleFullPath, SymbolTable>) -> (Type, Type) {
    let macros = ModuleFullPath::from("macros");
    let sexp_name = fq_type("macros", "Sexp");
    let slist_name = fq_type("macros", "SList");
    let sexp = Type::ADT(sexp_name.clone(), vec![]);
    let slist_sexp = Type::ADT(slist_name.clone(), vec![sexp.clone()]);
    let mut table = SymbolTable::new(macros.clone());

    install_type_fixture(
        &mut table,
        Symbol::from("Sexp"),
        TypeDefInfo {
            name: sexp_name.clone(),
            type_params: vec![],
            constructors: vec![Symbol::from("SexpSym")],
        },
    );
    install_ctor_fixture(
        &mut table,
        Symbol::from("SexpSym"),
        fn_scheme(vec![Type::String], sexp.clone()),
        vec![Symbol::from("name")],
        sexp_name,
        0,
        1,
        None,
        None,
        None,
    );

    install_type_fixture(
        &mut table,
        Symbol::from("SList"),
        TypeDefInfo {
            name: slist_name.clone(),
            type_params: vec![Symbol::from("a")],
            constructors: vec![Symbol::from("SNil"), Symbol::from("SCons")],
        },
    );
    let generic_slist = Type::ADT(slist_name.clone(), vec![Type::Var(0)]);
    let synth = |tag| {
        TemplateBody::Synth(SynthSpec::new(DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: tag,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        }))
    };
    table
        .install_template(
            Symbol::from("SNil"),
            Scheme {
                type_vars: vec![0],
                constraints: HashMap::new(),
                ty: generic_slist.clone(),
            },
            vec![],
            None,
            0,
            CallableOrigin::Ctor {
                type_name: slist_name.clone(),
                tag: 0,
                field_count: 0,
                internal: false,
                type_def: None,
            },
            synth(0),
            TemplateKind::Parametric,
            vec![],
            Visibility::Public,
        )
        .unwrap();
    table
        .install_template(
            Symbol::from("SCons"),
            Scheme {
                type_vars: vec![0],
                constraints: HashMap::new(),
                ty: Type::Fn(
                    vec![Type::Var(0), generic_slist.clone()],
                    Box::new(generic_slist),
                ),
            },
            vec![Symbol::from("head"), Symbol::from("tail")],
            None,
            1,
            CallableOrigin::Ctor {
                type_name: slist_name,
                tag: 1,
                field_count: 2,
                internal: false,
                type_def: None,
            },
            synth(1),
            TemplateKind::Parametric,
            vec![],
            Visibility::Public,
        )
        .unwrap();
    tables.insert(macros, table);
    (slist_sexp, sexp)
}

fn macro_clause_fixture() -> (
    DashMap<ModuleFullPath, SymbolTable>,
    ModuleFullPath,
    CallableTarget,
    Scheme,
) {
    let tables = empty_tables();
    let (slist_sexp, sexp) = install_macro_types(&tables);
    let module = ModuleFullPath::from("user");
    let macro_name = Symbol::from("ident");
    let args = Symbol::from("__args__");
    let head = Symbol::from("head");
    let tail = Symbol::from("tail");
    let scheme = fn_scheme(vec![slist_sexp.clone()], sexp.clone());
    let ast = DefnVariant {
        params: vec![(args.clone(), None)],
        body: Expr::IntLit {
            value: 0,
            span: Span::new(0, 1),
            inferred_type: Some(Box::new(sexp.clone())),
        },
        span: Span::new(0, 20),
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(MonoExpr::Var {
            name: args.clone(),
            span: Span::new(2, 3),
            resolved_call: None,
            resolution: VarRef::Local {
                binder: args.clone(),
                binding_span: Span::SYNTHETIC,
            },
            ty: ConcreteType::from_type(&slist_sexp).unwrap(),
        }),
        arms: vec![MonoMatchArm {
            pattern: Pattern::Constructor {
                name: SymbolRef::new(None, Symbol::from("SCons")),
                bindings: vec![head.clone(), tail],
                span: Span::new(4, 10),
            },
            body: MonoExpr::Var {
                name: head.clone(),
                span: Span::new(11, 12),
                resolved_call: None,
                resolution: VarRef::Local {
                    binder: head,
                    binding_span: Span::SYNTHETIC,
                },
                ty: ConcreteType::from_type(&sexp).unwrap(),
            },
            span: Span::new(4, 12),
            provenance: Some(args.clone()),
            resolved_ctor: Some(FQSymbol {
                module: ModuleFullPath::from("macros"),
                symbol: Symbol::from("SCons"),
            }),
        }],
        span: Span::new(2, 14),
        compiler_generated: true,
        ty: ConcreteType::from_type(&sexp).unwrap(),
    };
    let view = MonoDefnVariant {
        name: macro_name.clone(),
        params: vec![args],
        body,
        span: ast.span,
        mode_summary: None,
    };
    let mut table = SymbolTable::new(module.clone());
    table
        .install_macro(
            macro_name.clone(),
            None,
            0,
            cranelisp_types::Sexp::Symbol("ident".into(), Span::SYNTHETIC),
            vec![MacroClauseDraft::new(
                vec![],
                None,
                CallableArmDraft::concrete_body(
                    scheme.clone(),
                    vec![Symbol::from("__args__")],
                    ast,
                    view,
                    vec![],
                ),
            )],
            Visibility::Private,
        )
        .unwrap();
    tables.insert(module.clone(), table);
    let target = CallableTarget::MacroClause {
        owner: FQSymbol {
            module: module.clone(),
            symbol: macro_name,
        },
        clause: CallableArmId::from_ordinal(0).unwrap(),
    };
    (tables, module, target, scheme)
}

fn constructor_result_clause_fixture() -> (
    DashMap<ModuleFullPath, SymbolTable>,
    ModuleFullPath,
    CallableTarget,
) {
    let tables = empty_tables();
    let (slist_sexp, sexp) = install_macro_types(&tables);
    let module = ModuleFullPath::from("user");
    let macro_name = Symbol::from("fresh");
    let args = Symbol::from("__args__");
    let scheme = fn_scheme(vec![slist_sexp], sexp.clone());
    let ast = DefnVariant {
        params: vec![(args.clone(), None)],
        body: Expr::IntLit {
            value: 0,
            span: Span::new(20, 21),
            inferred_type: Some(Box::new(sexp.clone())),
        },
        span: Span::new(20, 40),
    };
    let view = MonoDefnVariant {
        name: macro_name.clone(),
        params: vec![args],
        body: MonoExpr::ConstrADT {
            type_name: fq_type("macros", "Sexp"),
            tag: 0,
            fields: vec![MonoExpr::StringLit {
                value: "fresh".into(),
                span: Span::new(25, 30),
                ty: ConcreteType::String,
                escapes: None,
                confined: None,
                unique_static: None,
            }],
            span: Span::new(24, 31),
            ty: ConcreteType::from_type(&sexp).unwrap(),
            escapes: None,
            confined: None,
            unique_static: None,
        },
        span: ast.span,
        mode_summary: None,
    };
    let mut table = SymbolTable::new(module.clone());
    table
        .install_macro(
            macro_name.clone(),
            None,
            0,
            cranelisp_types::Sexp::Symbol("fresh".into(), Span::SYNTHETIC),
            vec![MacroClauseDraft::new(
                vec![],
                None,
                CallableArmDraft::concrete_body(
                    scheme,
                    vec![Symbol::from("__args__")],
                    ast,
                    view,
                    vec![],
                ),
            )],
            Visibility::Private,
        )
        .unwrap();
    tables.insert(module.clone(), table);
    let target = CallableTarget::MacroClause {
        owner: FQSymbol {
            module: module.clone(),
            symbol: macro_name,
        },
        clause: CallableArmId::from_ordinal(0).unwrap(),
    };
    (tables, module, target)
}

fn retain_count(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 add").count()
}

// spec: design/backend/s122-closure.md §7 — the real MacroClause target owns
// the canonical heap parameter scheme and carries no inferred ownership
// summary. The constructor arm upgrades its borrowed returned field and reports
// that owner to the enclosing function, which must not protect it again.
#[test]
fn macro_clause_projection_carries_parameter_authority_and_one_result_owner() {
    let (tables, module, target, expected_scheme) = macro_clause_fixture();
    let table = tables.get(&module).unwrap();
    let arm = table.callable_target(&target).unwrap();
    assert_eq!(arm.scheme.ty, expected_scheme.ty);
    assert!(matches!(
        arm.life,
        Life::Concrete {
            mode_summary: None,
            ..
        }
    ));
    assert!(matches!(
        crate::compiler::signature_heap_category(
            match &arm.scheme.ty {
                Type::Fn(params, _) => &params[0],
                other => panic!("macro clause must carry a function scheme, got {other}"),
            },
            Some(&tables),
        ),
        crate::heap::HeapCategory::Mixed
    ));
    assert!(
        table.get("ident$macro-clause$0").is_none(),
        "the generated executable label is not the selected clause's scheme owner"
    );
    drop(table);

    let mut jit = Jit::new(&tables).unwrap();
    let artifacts = compile_to_module(
        module,
        std::slice::from_ref(&target),
        &tables,
        jit.jit_module(),
        true,
    )
    .unwrap();
    assert_eq!(
        retain_count(&artifacts.clif_ir),
        1,
        "the borrowed-field upgrade is the result's one owner:\n{}",
        artifacts.clif_ir
    );
    assert_eq!(
        count_release_ops(&artifacts.clif_ir),
        1,
        "the all-Owned macro parameter must still be consumed once:\n{}",
        artifacts.clif_ir
    );
}

// spec: design/backend/s122-closure.md §7 — a constructor result already owns
// its returned cell, while the selected clause scheme still makes the unused
// all-Owned argument visible to parameter cleanup. It needs no result retain
// and exactly one argument-root release.
#[test]
fn macro_clause_constructor_result_adds_no_retain_and_consumes_its_parameter() {
    let (tables, module, target) = constructor_result_clause_fixture();
    let mut jit = Jit::new(&tables).unwrap();
    let artifacts = compile_to_module(
        module,
        std::slice::from_ref(&target),
        &tables,
        jit.jit_module(),
        true,
    )
    .unwrap();
    assert_eq!(retain_count(&artifacts.clif_ir), 0, "{}", artifacts.clif_ir);
    assert_eq!(
        count_release_ops(&artifacts.clif_ir),
        1,
        "the selected scheme must type the unused argument for cleanup:\n{}",
        artifacts.clif_ir
    );
}
