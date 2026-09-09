//! Backend safety fence for expansion-only macro clauses.

use crate::test_support::*;
use cranelisp_types::{
    CallableArmDraft, ConcreteType, FQSymbol, MacroClauseDraft, MonoDefnVariant, MonoExpr, Scheme,
};

fn install_macro(table: &mut SymbolTable, name: &Symbol) {
    let variant = DefnVariant {
        params: vec![],
        body: Expr::IntLit {
            value: 7,
            span: Span::new(1, 2),
            inferred_type: Some(Box::new(Type::Int)),
        },
        span: Span::new(0, 3),
    };
    let view = MonoDefnVariant {
        name: name.clone(),
        params: vec![],
        body: MonoExpr::IntLit {
            value: 7,
            span: Span::new(1, 2),
            ty: ConcreteType::Int,
        },
        span: variant.span,
        mode_summary: None,
    };
    table
        .install_macro(
            name.clone(),
            None,
            0,
            cranelisp_types::Sexp::Symbol(name.to_string(), Span::SYNTHETIC),
            vec![MacroClauseDraft::new(
                Vec::new(),
                None,
                CallableArmDraft::concrete_body(
                    Scheme {
                        type_vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Fn(vec![], Box::new(Type::Int)),
                    },
                    vec![],
                    variant,
                    view,
                    vec![],
                ),
            )],
            Visibility::Private,
        )
        .expect("macro declaration is valid");
}

fn compile_reference(body: Expr, reference_spans: &[Span]) -> CranelispError {
    let module = ModuleFullPath::from("user");
    let clause = Symbol::from("opaque-macro");
    let mut table = SymbolTable::new(module.clone());
    install_macro(&mut table, &clause);
    let tables = empty_tables();
    tables.insert(module.clone(), table);

    let caller = Defn {
        name: Symbol::from("caller"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::new(10, 30),
        }],
        visibility: Visibility::Public,
        span: Span::new(10, 30),
    };
    let fq = FQSymbol {
        module: module.clone(),
        symbol: clause,
    };
    let targets = reference_spans
        .iter()
        .copied()
        .map(|span| (span, fq.clone()))
        .collect();

    let mut object = make_object_module();
    try_compile_defns_in_module(&[&caller], &[], &[], &targets, &tables, module, &mut object)
        .expect_err("an ordinary carrier must not expose a macro clause to codegen")
}

fn assert_expansion_only(error: CranelispError) {
    let message = format!("{error:?}");
    assert!(
        message.contains("expansion-only macro clause") && message.contains("opaque-macro"),
        "the refusal must identify the selected clause and its restriction: {message}"
    );
}

// spec: 09-macros §9.2.6; QA MC-9 — even a hand-built, otherwise-valid
// checked Global carrier cannot call a macro binding through ordinary language
// codegen.
#[test]
fn ordinary_call_carrier_to_macro_clause_refuses_before_emission() {
    let callee_span = Span::new(14, 15);
    let apply_span = Span::new(13, 16);
    let error = compile_reference(
        Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("opaque-macro"),
                span: callee_span,
                resolved_call: None,
                inferred_type: Some(Box::new(Type::Fn(vec![], Box::new(Type::Int)))),
            }),
            args: vec![],
            span: apply_span,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        },
        &[callee_span, apply_span],
    );
    assert_expansion_only(error);
}

// spec: 09-macros §9.2.6; QA MC-9 — the same checked carrier cannot turn the
// clause into a first-class language value. Macro expansion's dedicated host
// invocation path does not use backend expression codegen.
#[test]
fn ordinary_value_carrier_to_macro_clause_refuses_before_emission() {
    let span = Span::new(20, 21);
    let error = compile_reference(
        Expr::Var {
            name: Symbol::from("opaque-macro"),
            span,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Fn(vec![], Box::new(Type::Int)))),
        },
        &[span],
    );
    assert_expansion_only(error);
}
