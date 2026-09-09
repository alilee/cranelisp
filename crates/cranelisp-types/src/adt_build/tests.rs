use super::*;
use crate::{Decl, ModuleFullPath, SymbolTable, TypeName};

fn fq(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("m"), TypeName::from(name))
}

#[test]
fn sum_recipes_are_canonical_then_type_facet() {
    let entries = build_adt_entries::<()>(
        &fq("Maybe"),
        &[Symbol::from("a")],
        &[0],
        Some("maybe"),
        &[
            AdtCtorSpec::new(
                Symbol::from("Just"),
                vec![FieldInfo {
                    name: Symbol::from("value"),
                    ty: Type::Var(0),
                }],
                Some("just".into()),
                false,
            ),
            AdtCtorSpec::new(Symbol::from("Nothing"), Vec::new(), None, false),
        ],
        Visibility::Public,
    );

    assert_eq!(
        entries
            .iter()
            .map(|(key, _)| key.as_ref())
            .collect::<Vec<_>>(),
        vec!["Maybe.Just", "Maybe.Nothing", "Maybe"]
    );
    let AdtEntrySpec::Callable(just) = &entries[0].1 else {
        panic!("canonical constructor must be a callable recipe");
    };
    assert!(matches!(
        &just.origin,
        CallableOrigin::Ctor {
            type_name,
            tag: 0,
            field_count: 1,
            type_def: None,
            ..
        } if type_name == &fq("Maybe")
    ));
    assert!(matches!(
        &just.scheme.ty,
        Type::Fn(params, ret)
            if params == &vec![Type::Var(0)]
                && ret.as_ref() == &Type::ADT(fq("Maybe"), vec![Type::Var(0)])
    ));

    let AdtEntrySpec::Binding(type_binding) = &entries[2].1 else {
        panic!("sum must end with type facet");
    };
    assert!(matches!(
        &type_binding.declaration,
        Decl::Type(TypeRecord::Defined {
            info,
            docstring: Some(doc)
        }) if info.constructors == vec![Symbol::from("Just"), Symbol::from("Nothing")]
            && doc == "maybe"
    ));
}

#[test]
fn product_recipe_carries_dual_type_facet_and_doc_fallback() {
    let entries = build_adt_entries::<()>(
        &fq("Pair"),
        &[],
        &[],
        Some("pair docs"),
        &[AdtCtorSpec::new(
            Symbol::from("Pair"),
            vec![
                FieldInfo {
                    name: Symbol::from("left"),
                    ty: Type::Int,
                },
                FieldInfo {
                    name: Symbol::from("right"),
                    ty: Type::Bool,
                },
            ],
            None,
            false,
        )],
        Visibility::Private,
    );
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].0, Symbol::from("Pair"));
    let AdtEntrySpec::Callable(pair) = &entries[0].1 else {
        panic!("product must be one callable recipe");
    };
    assert_eq!(pair.docstring.as_deref(), Some("pair docs"));
    assert_eq!(
        pair.param_names,
        vec![Symbol::from("left"), Symbol::from("right")]
    );
    assert!(matches!(
        &pair.origin,
        CallableOrigin::Ctor {
            tag: 0,
            field_count: 2,
            type_def: Some(info),
            ..
        } if info.name == fq("Pair")
    ));
}

#[test]
fn generic_constructor_recipe_has_no_slot_or_lifecycle_state() {
    let entries = build_adt_entries::<()>(
        &fq("Box"),
        &[Symbol::from("a")],
        &[7],
        None,
        &[AdtCtorSpec::new(
            Symbol::from("Box"),
            vec![FieldInfo {
                name: Symbol::from("v"),
                ty: Type::Var(7),
            }],
            None,
            false,
        )],
        Visibility::Public,
    );
    let AdtEntrySpec::Callable(spec) = &entries[0].1 else {
        panic!("expected callable recipe");
    };
    assert_eq!(spec.scheme.type_vars, vec![7]);
    assert!(matches!(spec.scheme.ty, Type::Fn(_, _)));
    assert!(matches!(
        spec.synth.variant.body,
        Expr::ConstrADT {
            tag: 0,
            ref fields,
            ..
        } if fields.len() == 1
    ));
}

#[derive(Debug, Clone)]
struct TestCodeStore;

#[test]
fn non_unit_type_binding_recipe_installs_without_rewrapping() {
    let entries = build_adt_entries::<TestCodeStore>(
        &fq("Maybe"),
        &[],
        &[],
        None,
        &[
            AdtCtorSpec::new(Symbol::from("Just"), Vec::new(), None, false),
            AdtCtorSpec::new(Symbol::from("Nothing"), Vec::new(), None, false),
        ],
        Visibility::Public,
    );
    let mut table = SymbolTable::<TestCodeStore, ()>::new_with_params(ModuleFullPath::from("m"));

    for (key, recipe) in entries {
        if let AdtEntrySpec::Binding(binding) = recipe {
            table.install_binding(key, binding).unwrap();
        }
    }

    assert!(table.get("Just").is_none());
    assert!(matches!(
        &table.get("Maybe").unwrap().declaration,
        Decl::Type(_)
    ));
}
