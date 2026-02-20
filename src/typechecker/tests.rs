use super::*;
use crate::ast_builder::parse_program;
use crate::error::CranelispError;

const PRELUDE: &str = include_str!("../unittest_prelude.cl");

fn check(src: &str) -> Result<CheckResult, CranelispError> {
    let prelude = parse_program(PRELUDE).unwrap();
    let user = parse_program(src).unwrap();
    let program: Vec<_> = prelude.into_iter().chain(user).collect();
    let mut tc = TypeChecker::new();
    tc.check_program(&program)
}

#[test]
fn infer_add() {
    let src = "(defn main [] (pure (+ 1 2)))";
    assert!(check(src).is_ok());
}

#[test]
fn reject_add_bool() {
    let src = "(defn main [] (pure (+ 1 true)))";
    assert!(check(src).is_err());
}

#[test]
fn check_factorial() {
    let src = r#"
        (defn fact [n]
          (if (= n 0)
            1
            (* n (fact (- n 1)))))
        (defn main []
          (pure (fact 10)))
    "#;
    assert!(check(src).is_ok());
}

#[test]
fn check_if_branch_mismatch() {
    // then returns Int, else returns Bool
    let src = "(defn main [] (pure (if true 1 false)))";
    assert!(check(src).is_err());
}

#[test]
fn check_let_binding() {
    let src = "(defn main [] (pure (let [x 5] (+ x 1))))";
    assert!(check(src).is_ok());
}

#[test]
fn check_unbound_variable() {
    let src = "(defn main [] (pure y))";
    assert!(check(src).is_err());
}

#[test]
fn check_forward_reference() {
    let src = r#"
        (defn main [] (pure (helper 1)))
        (defn helper [x] (+ x 1))
    "#;
    assert!(check(src).is_ok());
}

#[test]
fn check_no_main() {
    let src = "(defn foo [x] x)";
    assert!(check(src).is_err());
}

#[test]
fn check_comparison_returns_bool() {
    let src = "(defn main [] (pure (if (< 1 2) 10 20)))";
    assert!(check(src).is_ok());
}

#[test]
fn check_nested_let() {
    let src = "(defn main [] (pure (let [x 1 y (+ x 2)] (+ x y))))";
    assert!(check(src).is_ok());
}

#[test]
fn check_lambda_identity() {
    // Lambda used in let and called
    let src = "(defn main [] (pure (let [f (fn [x] x)] (f 42))))";
    assert!(check(src).is_ok());
}

#[test]
fn check_lambda_add() {
    let src = "(defn main [] (pure ((fn [x] (+ x 1)) 5)))";
    assert!(check(src).is_ok());
}

#[test]
fn check_higher_order_function() {
    let src = r#"
        (defn apply-fn [f x] (f x))
        (defn main [] (pure (apply-fn (fn [x] (* x 2)) 5)))
    "#;
    assert!(check(src).is_ok());
}

#[test]
fn check_lambda_type_error() {
    // Pass bool to lambda expecting int arithmetic
    let src = "(defn main [] (pure ((fn [x] (+ x 1)) true)))";
    assert!(check(src).is_err());
}

// ── IO type system tests ────────────────────────────────────────────

#[test]
fn check_pure_wraps_in_io() {
    let src = "(defn main [] (pure 42))";
    assert!(check(src).is_ok());
}

#[test]
fn check_do_returns_last_type() {
    // do is now a macro (not available in unit tests) — use let to sequence
    let src = "(defn main [] (let [_ (pure 1)] (pure 2)))";
    assert!(check(src).is_ok());
}

#[test]
fn check_bind_extracts_and_continues() {
    let src = "(defn main [] (bind (pure 42) (fn [x] (pure (+ x 1)))))";
    assert!(check(src).is_ok());
}

#[test]
fn check_bind_rejects_non_io_first_arg() {
    let src = "(defn main [] (bind 42 (fn [x] (pure x))))";
    assert!(check(src).is_err());
}

#[test]
fn check_if_branches_io_mismatch() {
    // One branch IO Int, other Int — error
    let src = "(defn main [] (if true (pure 1) 0))";
    assert!(check(src).is_err());
}

#[test]
fn check_if_branches_with_pure() {
    // Both branches IO Int — ok
    let src = "(defn main [] (if true (pure 1) (pure 0)))";
    assert!(check(src).is_ok());
}

#[test]
fn check_main_must_return_io() {
    let src = "(defn main [] 42)";
    assert!(check(src).is_err());
}

// ── Polymorphism tests ─────────────────────────────────────────────

#[test]
fn program_polymorphic_fn_used_at_different_types() {
    // do is now a macro (not available in unit tests) — use let to sequence
    let src = r#"
        (defn id [x] x)
        (defn main []
          (let [_ (pure (id "hello"))]
            (pure (if (id true) 1 0))))
    "#;
    assert!(check(src).is_ok());
}

// ── Float type tests ──────────────────────────────────────────────

#[test]
fn infer_float_add() {
    let src = "(defn main [] (pure (+ 1.5 2.5)))";
    assert!(check(src).is_ok());
}

#[test]
fn reject_float_plus_int() {
    let src = "(defn main [] (pure (+ 1 1.0)))";
    assert!(check(src).is_err());
}

// ── Module scope tracking tests ─────────────────────────────────────────

#[test]
fn end_module_scope_removes_bare_names() {
    let mut tc = TypeChecker::new();
    // Simulate a prelude name (installed via implied import, not part of any module)
    // "show" goes into "user" module (the default current_module_path)
    tc.insert_def(
        "show".into(),
        Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
    );

    // Switch to "mymod" module, then define "helper" there
    let scheme = Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Int,
    };
    tc.set_current_module_path(ModuleFullPath::from("mymod"));
    tc.insert_def("helper".into(), scheme);

    // Before end_module_scope, bare name exists (current module is "mymod")
    assert!(tc.lookup("helper").is_some());

    tc.end_module_scope();

    // Switch back to "user" module
    tc.set_current_module_path(ModuleFullPath::from("user"));

    // After: bare name not visible from "user", qualified name works, prelude preserved
    assert!(tc.lookup("helper").is_none());
    assert!(tc.lookup("mymod/helper").is_some());
    assert!(tc.lookup("show").is_some());
}

#[test]
fn begin_module_scope_installs_imports() {
    let mut tc = TypeChecker::new();

    // Source module has a definition
    let scheme = Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Int,
    };
    // Populate CompiledModule for module-walk resolution
    let mut util_cm = crate::module::CompiledModule::new(ModuleFullPath::from("util"));
    util_cm.insert_def(Symbol::from("helper"), scheme, Visibility::Public, None);
    tc.modules.insert(ModuleFullPath::from("util"), util_cm);

    // Import it
    let imports = vec![("helper".to_string(), "util".to_string())];
    tc.begin_module_scope(&imports).unwrap();

    // Now bare "helper" is accessible via module-walk (Import → source module Def)
    assert!(tc.lookup("helper").is_some());
}

#[test]
fn begin_module_scope_detects_ambiguity() {
    let mut tc = TypeChecker::new();

    // Two modules define the same name — bare name becomes Ambiguous (not a hard error)
    let imports = vec![
        ("foo".to_string(), "modA".to_string()),
        ("foo".to_string(), "modB".to_string()),
    ];
    let result = tc.begin_module_scope(&imports);
    assert!(result.is_ok());
    // The bare name "foo" should now be Ambiguous in the current module
    assert!(tc.lookup("foo").is_none(), "ambiguous name should not resolve");
}

#[test]
fn begin_module_scope_same_source_not_ambiguous() {
    let mut tc = TypeChecker::new();

    // Same name from same source (e.g. via re-export) — not ambiguous
    let imports = vec![
        ("foo".to_string(), "util".to_string()),
        ("foo".to_string(), "util".to_string()),
    ];
    assert!(tc.begin_module_scope(&imports).is_ok());
}

#[test]
fn end_module_scope_removes_imported_names() {
    let mut tc = TypeChecker::new();

    // Source module
    let scheme = Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Int,
    };
    // Populate CompiledModule for module-walk resolution
    let mut util_cm = crate::module::CompiledModule::new(ModuleFullPath::from("util"));
    util_cm.insert_def(Symbol::from("helper"), scheme, Visibility::Public, None);
    tc.modules.insert(ModuleFullPath::from("util"), util_cm);

    // Switch to "mymod" so imports go there, then import and end scope
    tc.set_current_module_path(ModuleFullPath::from("mymod"));
    let imports = vec![("helper".to_string(), "util".to_string())];
    tc.begin_module_scope(&imports).unwrap();
    assert!(tc.lookup("helper").is_some());

    tc.end_module_scope();
    // Switch back to "user" — imported bare name should not be visible
    tc.set_current_module_path(ModuleFullPath::from("user"));
    assert!(tc.lookup("helper").is_none());
    // Qualified still accessible via module-walk
    assert!(tc.lookup("util/helper").is_some());
}

#[test]
fn begin_module_scope_makes_imported_names_resolvable() {
    let mut tc = TypeChecker::new();

    let scheme = Scheme {
        vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Int,
    };
    // Populate CompiledModule for module-walk resolution
    let mut util_cm = crate::module::CompiledModule::new(ModuleFullPath::from("util"));
    util_cm.insert_def(Symbol::from("helper"), scheme, Visibility::Public, None);
    tc.modules.insert(ModuleFullPath::from("util"), util_cm);

    let imports = vec![("helper".to_string(), "util".to_string())];
    tc.begin_module_scope(&imports).unwrap();

    // lookup resolves bare name through CompiledModule Import → source module Def
    assert!(tc.lookup("helper").is_some());
    // qualified access also works
    assert!(tc.lookup("util/helper").is_some());
}

#[test]
fn get_module_public_names_filters_private() {
    let mut tc = TypeChecker::new();
    // Set up via CompiledModule directly
    let mod_path = ModuleFullPath::from("mymod");
    let cm = tc
        .modules
        .entry(mod_path.clone())
        .or_insert_with(|| crate::module::CompiledModule::new(mod_path));
    cm.insert_def(
        crate::names::Symbol::from("public_fn"),
        Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
        Visibility::Public,
        None,
    );
    cm.insert_def(
        crate::names::Symbol::from("private_fn"),
        Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
        Visibility::Private,
        None,
    );

    let public = tc.get_module_public_names("mymod");
    assert_eq!(public, vec!["public_fn".to_string()]);
}

#[test]
fn get_module_all_names_includes_both() {
    let mut tc = TypeChecker::new();
    // Set up via CompiledModule directly
    let mod_path = ModuleFullPath::from("mymod");
    let cm = tc
        .modules
        .entry(mod_path.clone())
        .or_insert_with(|| crate::module::CompiledModule::new(mod_path));
    cm.insert_def(
        crate::names::Symbol::from("pub_fn"),
        Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
        Visibility::Public,
        None,
    );
    cm.insert_def(
        crate::names::Symbol::from("priv_fn"),
        Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
        Visibility::Private,
        None,
    );

    let all = tc.get_module_all_names("mymod");
    assert_eq!(all.len(), 2);
    assert!(all.contains(&("pub_fn".to_string(), Visibility::Public)));
    assert!(all.contains(&("priv_fn".to_string(), Visibility::Private)));
}

// register_qualified_aliases_includes_constrained_fns test removed:
// constrained_fns lifecycle has been replaced by CompiledModule module-walk resolution.
// Qualified alias propagation is no longer needed — resolve_constrained_fn_via_modules()
// follows Import/Reexport chains directly.

#[test]
fn qualify_adt_name_local_type_unqualified() {
    let mut tc = TypeChecker::new();
    // Register a type in the current module (root "")
    let mod_path = ModuleFullPath::root();
    let cm = tc
        .modules
        .entry(mod_path.clone())
        .or_insert_with(|| crate::module::CompiledModule::new(mod_path));
    cm.symbols.insert(
        crate::names::Symbol::from("Point"),
        crate::module::ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: "Point".to_string(),
                type_params: vec![],
                constructors: vec![ConstructorInfo {
                    name: "Point".to_string(),
                    tag: 0,
                    fields: vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Int)],
                    docstring: None,
                }],
                docstring: None,
            },
            visibility: Visibility::Public,
            constructor_scheme: None,
            sexp: None,
        },
    );

    // From root module, Point should be unqualified
    assert_eq!(tc.qualify_adt_name("Point"), "Point");
}

#[test]
fn qualify_adt_name_foreign_type_qualified() {
    let mut tc = TypeChecker::new();
    // Register a type in module "foo", but current module is root ""
    let mod_path = ModuleFullPath::from("foo");
    let cm = tc
        .modules
        .entry(mod_path.clone())
        .or_insert_with(|| crate::module::CompiledModule::new(mod_path));
    cm.symbols.insert(
        crate::names::Symbol::from("Point2"),
        crate::module::ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: "Point2".to_string(),
                type_params: vec![],
                constructors: vec![ConstructorInfo {
                    name: "Point2".to_string(),
                    tag: 0,
                    fields: vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Int)],
                    docstring: None,
                }],
                docstring: None,
            },
            visibility: Visibility::Public,
            constructor_scheme: None,
            sexp: None,
        },
    );

    // From root module, Point2 should be qualified as "foo/Point2"
    assert_eq!(tc.qualify_adt_name("Point2"), "foo/Point2");
}

#[test]
fn qualify_adt_name_already_qualified_unchanged() {
    let tc = TypeChecker::new();
    // Already-qualified names pass through unchanged
    assert_eq!(tc.qualify_adt_name("foo/Point"), "foo/Point");
}

#[test]
fn qualify_adt_name_unknown_type_unchanged() {
    let tc = TypeChecker::new();
    // Unknown type names pass through unchanged
    assert_eq!(tc.qualify_adt_name("NoSuchType"), "NoSuchType");
}
