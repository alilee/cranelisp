use std::collections::HashMap;

use cranelisp_types::{
    CallableOrigin, DefnVariant, Expr, FQSymbol, FQTypeName, ModuleFullPath, Realization, Scheme,
    Span, Symbol, Type, TypeName, Visibility,
};

use super::*;

fn option_of(arg: Type) -> Type {
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
        vec![arg],
    )
}

fn test_type() -> Type {
    Type::Fn(vec![], Box::new(option_of(Type::String)))
}

fn scheme(ty: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

/// Install a concrete definition `name : ty` homed in `table`.
fn define(table: &mut SessionSymbolTable, name: &str, ty: Type) {
    let params: Vec<Symbol> = match &ty {
        Type::Fn(params, _) => (0..params.len())
            .map(|i| Symbol::from(format!("p{i}")))
            .collect(),
        _ => Vec::new(),
    };
    let variant = DefnVariant {
        params: params.iter().map(|p| (p.clone(), None)).collect(),
        body: Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: None,
        },
        span: Span::new(3, 9),
    };
    let view = cranelisp_types::MonoDefnVariant {
        name: Symbol::from(name),
        params: params.clone(),
        body: cranelisp_types::MonoExpr::lenient_from_expr(
            &variant.body,
            &Default::default(),
            &Default::default(),
            &Default::default(),
        ),
        span: Span::SYNTHETIC,
        mode_summary: None,
    };
    table
        .install_concrete(
            Symbol::from(name),
            scheme(ty),
            params,
            None,
            0,
            CallableOrigin::Plain,
            Realization::Body { view, code: None },
            Some(variant),
            Vec::new(),
            Visibility::Public,
        )
        .expect("definition fixture installs");
}

fn tables(
    modules: Vec<(&str, Vec<(&str, Type)>)>,
) -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
    let tables = dashmap::DashMap::new();
    for (module, definitions) in modules {
        let path = ModuleFullPath::from(module);
        let mut table = SessionSymbolTable::new_with_params(path.clone());
        for (name, ty) in definitions {
            define(&mut table, name, ty);
        }
        tables.insert(path, table);
    }
    tables
}

fn fq(module: &str, symbol: &str) -> FQSymbol {
    FQSymbol {
        module: ModuleFullPath::from(module),
        symbol: Symbol::from(symbol),
    }
}

fn scan(
    tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    modules: &[&str],
) -> Discovery {
    let modules: Vec<ModuleFullPath> = modules.iter().copied().map(ModuleFullPath::from).collect();
    scan_modules(tables, &modules)
}

// spec: repl/spec/16-test-discovery.md §16.1 Test Function Convention — a
// `test-` function of exactly `(Fn [] (Option String))` is a test; other
// definitions are not (design/int/test-runner.md §10 discovery row 1).
#[test]
fn exact_scheme_test_is_eligible_and_other_definitions_are_not() {
    let tables = tables(vec![(
        "user",
        vec![
            ("test-ok", test_type()),
            ("helper", test_type()),
            ("testing-x", test_type()),
        ],
    )]);
    let discovery = scan(&tables, &["user"]);
    assert_eq!(discovery.tests, [fq("user", "test-ok")]);
    assert!(discovery.warnings.is_empty(), "{:?}", discovery.warnings);
}

// spec: repl/spec/16-test-discovery.md §16.1 Test Function Convention — each
// mistyped `test-` function is excluded with one warning naming it by FQ name
// (§10 discovery row 2).
#[test]
fn each_mistyped_test_is_excluded_with_one_warning_naming_it() {
    let tables = tables(vec![(
        "user",
        vec![
            ("test-int", Type::Fn(vec![], Box::new(Type::Int))),
            (
                "test-arg",
                Type::Fn(vec![Type::Int], Box::new(option_of(Type::String))),
            ),
            (
                "test-option-int",
                Type::Fn(vec![], Box::new(option_of(Type::Int))),
            ),
        ],
    )]);
    let discovery = scan(&tables, &["user"]);
    assert!(discovery.tests.is_empty(), "{:?}", discovery.tests);
    assert_eq!(discovery.warnings.len(), 3, "{:?}", discovery.warnings);
    for name in ["user/test-int", "user/test-arg", "user/test-option-int"] {
        let warned: Vec<&Warning> = discovery
            .warnings
            .iter()
            .filter(|w| w.message.contains(&format!("`{name}`")))
            .collect();
        assert_eq!(warned.len(), 1, "one warning names {name}");
        assert_eq!(warned[0].kind, WarningKind::Other);
        assert_eq!(warned[0].span, Span::new(3, 9), "the definition's span");
    }
}

// spec: repl/spec/16-test-discovery.md §16.1 Test Function Convention — a
// test imported or re-exported into another module is not that module's test,
// so it is listed once, under its home (§10 discovery row 3).
#[test]
fn imported_test_is_listed_only_under_its_home() {
    let tables = tables(vec![
        ("home", vec![("test-x", test_type())]),
        ("user", vec![]),
    ]);
    tables
        .get_mut(&ModuleFullPath::from("user"))
        .unwrap()
        .expose_candidate(
            Symbol::from("test-x"),
            fq("home", "test-x"),
            Visibility::Public,
        )
        .expect("re-export fixture installs");
    assert!(scan(&tables, &["user"]).tests.is_empty());
    assert_eq!(
        scan(&tables, &["user", "home"]).tests,
        [fq("home", "test-x")]
    );
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — tests are listed
// in fully-qualified-name order across the selected modules (§10 discovery
// row 4).
#[test]
fn tests_are_listed_in_fq_name_order_across_modules() {
    let tables = tables(vec![
        ("b", vec![("test-a", test_type())]),
        ("a", vec![("test-z", test_type()), ("test-m", test_type())]),
        ("a.b", vec![("test-a", test_type())]),
    ]);
    let discovery = scan(&tables, &["b", "a", "a.b", "absent"]);
    assert_eq!(
        discovery.tests,
        [
            fq("a.b", "test-a"),
            fq("a", "test-m"),
            fq("a", "test-z"),
            fq("b", "test-a")
        ]
    );
}

// spec: repl/spec/16-test-discovery.md §16.1 Test Function Convention — only
// the exact scheme is admitted: arity, return head and argument all count.
#[test]
fn test_scheme_is_exactly_zero_arity_option_string() {
    assert!(is_test_scheme(&scheme(test_type())));
    assert!(!is_test_scheme(&scheme(Type::Fn(
        vec![Type::Int],
        Box::new(option_of(Type::String))
    ))));
    assert!(!is_test_scheme(&scheme(Type::Fn(
        vec![],
        Box::new(option_of(Type::Int))
    ))));
    assert!(!is_test_scheme(&scheme(Type::Fn(
        vec![],
        Box::new(Type::ADT(
            FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Option")),
            vec![Type::String],
        )),
    ))));
    assert!(!is_test_scheme(&scheme(option_of(Type::String))));
}
