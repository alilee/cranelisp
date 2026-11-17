//! Binder types (`non-concrete-release-contract.md` §7.4 step 2, §9): a
//! parameter's type comes from its source, never from an occurrence, so an
//! unused heap parameter is still released at its introduction.

use cranelift_module::{FuncOrDataId, Module};
use cranelisp_types::{ConcreteType, drop_glue_symbol_name};

use crate::test_support::*;

fn user() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn int(value: i64, at: u32) -> Expr {
    Expr::IntLit {
        value,
        span: Span::new(at, at + 1),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn defn(name: &str, params: &[&str], body: Expr) -> Defn {
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: params.iter().map(|p| (Symbol::from(*p), None)).collect(),
            body,
            span: Span::new(0, 50),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 50),
    }
}

/// Compile `defn`, whose scheme is `(Fn params Int)`, and report whether the
/// module declared the canonical `String` glue: the one release of a `String`.
fn releases_a_string(defn: &Defn, params: &[Type]) -> bool {
    let mut table = SymbolTable::new(user());
    insert_user_fn_stub_typed(&mut table, defn.name.as_ref(), params, Type::Int);
    let tables = empty_tables();
    tables.insert(user(), table);
    let mut module = make_object_module();
    compile_defns_in_module(&[defn], &[], &HashMap::new(), &tables, user(), &mut module);
    let glue = drop_glue_symbol_name(&user(), &ConcreteType::String);
    matches!(module.get_name(glue.as_ref()), Some(FuncOrDataId::Func(_)))
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 2 (edge) —
// an unused heap parameter of a defn, which no occurrence can type, is
// released at its introduction at its scheme's type; the scalar twin releases
// nothing (NEGATIVE).
#[test]
fn an_unused_heap_defn_parameter_is_released_at_introduction() {
    let unused = defn("binder_unused_param", &["s"], int(0, 10));
    assert!(releases_a_string(&unused, &[Type::String]));
    let scalar = defn("binder_unused_scalar", &["s"], int(0, 10));
    assert!(!releases_a_string(&scalar, &[Type::Int]));
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 2 (edge) —
// an unused heap parameter of a lambda is typed by the `Lambda` node's
// function type and released at its introduction in the lambda's body; the
// scalar twin releases nothing (NEGATIVE).
#[test]
fn an_unused_heap_lambda_parameter_is_released_at_introduction() {
    let lambda = |param: Type| Expr::Lambda {
        params: vec![(Symbol::from("s"), None)],
        body: Box::new(int(0, 20)),
        span: Span::new(10, 30),
        inferred_type: Some(Box::new(Type::Fn(vec![param], Box::new(Type::Int)))),
    };
    let heap = defn("binder_unused_lambda", &[], lambda(Type::String));
    assert!(releases_a_string(&heap, &[]));
    let scalar = defn("binder_unused_lambda_scalar", &[], lambda(Type::Int));
    assert!(!releases_a_string(&scalar, &[]));
}
