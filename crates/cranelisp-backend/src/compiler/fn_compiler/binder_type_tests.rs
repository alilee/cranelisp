//! Binder types (`non-concrete-release-contract.md` §7.4 step 2, §9): a
//! parameter's type comes from its source, never from an occurrence, so an
//! unused heap parameter is still released at its introduction.

use cranelisp_types::{ConcreteType, drop_glue_symbol_name};
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

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

/// Compile `defn`, whose scheme is `(Fn params Int)`, emit the object, and
/// report whether the code of the function whose symbol starts with `body`
/// calls the canonical `String` glue: the one release of a `String`. A glue
/// body the registry defined but no function calls does not count.
fn body_releases_a_string(defn: &Defn, params: &[Type], body: &str) -> bool {
    let mut table = SymbolTable::new(user());
    insert_user_fn_stub_typed(&mut table, defn.name.as_ref(), params, Type::Int);
    let tables = empty_tables();
    tables.insert(user(), table);
    let mut module = make_object_module();
    compile_defns_in_module(&[defn], &[], &HashMap::new(), &tables, user(), &mut module);
    let glue = drop_glue_symbol_name(&user(), &ConcreteType::String);
    let bytes = module.finish().emit().expect("emit object");
    let file = object::File::parse(&*bytes).expect("parse object");

    let mut bodies = file
        .symbols()
        .filter(|s| s.name().is_ok_and(|n| n.starts_with(body)));
    let func = bodies
        .next()
        .unwrap_or_else(|| panic!("no function '{body}'"));
    assert!(bodies.next().is_none(), "'{body}' names one function");
    let section = file
        .section_by_index(func.section_index().expect("function in a section"))
        .expect("function section");
    let range = func.address()..func.address() + func.size();
    section.relocations().any(|(offset, reloc)| {
        range.contains(&offset)
            && matches!(reloc.target(), RelocationTarget::Symbol(i)
                if file.symbol_by_index(i).and_then(|s| s.name().map(str::to_owned)).ok()
                    == Some(glue.to_string()))
    })
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 2 (edge) —
// an unused heap parameter of a defn, which no occurrence can type, is
// released at its introduction at its scheme's type: the defn's own code
// calls the String glue. The scalar twin releases nothing (NEGATIVE).
#[test]
fn an_unused_heap_defn_parameter_is_released_at_introduction() {
    let unused = defn("binder_unused_param", &["s"], int(0, 10));
    assert!(body_releases_a_string(
        &unused,
        &[Type::String],
        "binder_unused_param"
    ));
    let scalar = defn("binder_unused_scalar", &["s"], int(0, 10));
    assert!(!body_releases_a_string(
        &scalar,
        &[Type::Int],
        "binder_unused_scalar"
    ));
}

// spec: design/backend/non-concrete-release-contract.md §7.4 step 2 (edge) —
// an unused heap parameter of a lambda is typed by the `Lambda` node's
// function type and released at its introduction in the lambda's body: the
// lambda's code, not the enclosing defn's, calls the String glue. The scalar
// twin releases nothing (NEGATIVE).
#[test]
fn an_unused_heap_lambda_parameter_is_released_at_introduction() {
    let lambda = |param: Type| Expr::Lambda {
        params: vec![(Symbol::from("s"), None)],
        body: Box::new(int(0, 20)),
        span: Span::new(10, 30),
        inferred_type: Some(Box::new(Type::Fn(vec![param], Box::new(Type::Int)))),
    };
    let heap = defn("binder_unused_lambda", &[], lambda(Type::String));
    assert!(body_releases_a_string(&heap, &[], "__lambda_"));
    assert!(!body_releases_a_string(&heap, &[], "binder_unused_lambda"));
    let scalar = defn("binder_unused_lambda_scalar", &[], lambda(Type::Int));
    assert!(!body_releases_a_string(&scalar, &[], "__lambda_"));
}
