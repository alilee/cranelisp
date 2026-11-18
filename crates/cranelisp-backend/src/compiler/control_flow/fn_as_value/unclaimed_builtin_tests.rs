//! The curry wrapper's `BuiltinFn` arm refuses a name no rule claims
//! (`design/backend/compile-to-module.md` §12.1): the partial application is
//! a located internal error raised before any import is declared, so no
//! wrapper can bind a host-process symbol by name. The recognised-builtin
//! control shows the same shape compiles and declares its extern import, so
//! the refusal is the arm's decision and not a fixture failure.

use crate::test_support::*;
use cranelift_module::{Linkage, Module};
use cranelisp_types::ResolvedCall;

/// `(defn useit [] (<builtin> 1))`: a 2-arg builtin partially applied, its
/// identity on the `BuiltinFn` carrier and no Apply-span carrier.
fn builtin_partial_defn(builtin: &str) -> Defn {
    let apply_span = Span::new(100, 110);
    Defn {
        name: Symbol::from("useit"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from(builtin),
                    span: Span::new(101, 104),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: Span::new(108, 109),
                    inferred_type: Some(Box::new(Type::Int)),
                }],
                span: apply_span,
                resolved_call: Some(Box::new(ResolvedCall::AutoCurry {
                    target_name: Symbol::from(builtin),
                    applied_count: 1,
                    total_count: 2,
                    trait_resolution: Some(Box::new(ResolvedCall::BuiltinFn {
                        name: Symbol::from(builtin),
                    })),
                })),
                inferred_type: Some(Box::new(Type::Fn(vec![Type::Int], Box::new(Type::Int)))),
            },
            span: Span::new(0, 200),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 200),
    }
}

/// Compile the partial application of `builtin` into a fresh object module;
/// returns the result and every name the module declared as an import.
fn compile_builtin_partial(
    builtin: &str,
) -> (
    Result<CompilationArtifacts, crate::CompilationError>,
    Vec<String>,
) {
    let useit = builtin_partial_defn(builtin);
    let user = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        install_def_entry_at_slot(&mut st, useit.clone(), 0);
        tables.insert(user.clone(), st);
    }
    let mut obj = make_object_module();
    let result = compile_names_to_module(
        user,
        std::slice::from_ref(&useit.name),
        &tables,
        &mut obj,
        true,
    );
    let imports = obj
        .declarations()
        .get_functions()
        .filter(|(_, decl)| decl.linkage == Linkage::Import)
        .filter_map(|(_, decl)| decl.name.clone())
        .collect();
    (result, imports)
}

// spec: design/backend/compile-to-module.md §12.1 — an unclaimed builtin's
// partial application is refused, located, before any import is declared.
#[test]
fn unclaimed_builtin_partial_application_is_refused_before_import() {
    let (result, imports) = compile_builtin_partial("ghost-prim");
    let err = match result {
        Ok(_) => panic!(
            "a partial application of a builtin no rule claims MUST be refused; \
             a clean compile means the by-name extern fallback was reintroduced \
             (imports declared: {imports:?})"
        ),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("internal invariant violation")
            && msg.contains("ghost-prim")
            && msg.contains("matches no wrapper rule"),
        "the refusal names the builtin as an internal invariant failure; got: {msg}"
    );
    assert!(
        !imports.iter().any(|name| name == "ghost-prim"),
        "the refusal precedes any import of the unclaimed name; imports: {imports:?}"
    );
}

// spec: design/backend/compile-to-module.md §12.1 (control) — a recognised
// extern builtin in the same shape compiles and declares its import.
#[test]
fn recognised_builtin_partial_application_declares_its_import() {
    let (result, imports) = compile_builtin_partial("str-concat");
    if let Err(e) = result {
        panic!("a recognised extern builtin's partial application must compile; got: {e:?}");
    }
    assert!(
        imports.iter().any(|name| name == "str-concat"),
        "the recognised builtin's wrapper imports its extern; imports: {imports:?}"
    );
}
