//! Every constructor call allocates on the RC heap, whatever its escape fact
//! (`design/backend/ownership-codegen.md` §4: stack placement retired in S124).

use crate::jit::Jit;
use crate::test_support::{
    insert_user_fn_stub, option_type_tables, try_compile_defns_in_module_with_pattern_ctors,
};
use cranelisp_types::{
    Defn, DefnVariant, Expr, FQSymbol, ModuleFullPath, MonoExpr, Span, Symbol, Visibility,
};
use std::collections::HashMap;

/// `(defn mk [] (Some 7))` in `main`, whose `Some` has one `Int` field.
fn mk_some() -> Defn {
    Defn {
        name: Symbol::from("mk"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: Span::new(1, 5),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 7,
                    span: Span::new(6, 7),
                    inferred_type: None,
                }],
                span: Span::new(0, 8),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// The CLIF of `mk` with `escapes` supplied on its constructor `Apply`.
fn mk_clif(escapes: Option<bool>) -> String {
    let module_path = ModuleFullPath::from("main");
    let tables = option_type_tables();
    insert_user_fn_stub(&mut tables.get_mut(&module_path).unwrap(), "mk", 0);
    let mut resolved_targets = HashMap::new();
    resolved_targets.insert(
        Span::new(1, 5),
        FQSymbol {
            module: module_path.clone(),
            symbol: Symbol::from("Some"),
        },
    );
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let defn = mk_some();
    let mut clifs = try_compile_defns_in_module_with_pattern_ctors(
        &[&defn],
        &[],
        &resolved_targets,
        &HashMap::new(),
        &tables,
        module_path,
        jit.jit_module(),
        &|body| {
            if let MonoExpr::Apply { escapes: e, .. } = body {
                *e = escapes;
            }
        },
    )
    .expect("mk compiles");
    clifs.remove(0)
}

// spec: design/backend/ownership-codegen.md §4 — a NoEscape scalar-payload
// constructor call takes the heap path: no stack slot, no immortal header, and
// the same emission as an escaping twin.
#[test]
fn a_no_escape_scalar_constructor_call_allocates_on_the_heap() {
    let no_escape = mk_clif(Some(false));
    let escaping = mk_clif(Some(true));
    assert!(
        escaping.contains("call fn"),
        "the escaping control allocates through runtime/alloc:\n{escaping}"
    );
    assert!(
        !no_escape.contains("explicit_slot") && !no_escape.contains("stack_addr"),
        "a NoEscape construction must not be stack-placed:\n{no_escape}"
    );
    assert!(
        !no_escape.contains("0x4000_0000_0000_0000"),
        "no immortal header is written:\n{no_escape}"
    );
    assert_eq!(
        no_escape, escaping,
        "placement must not depend on the escape fact"
    );
}
