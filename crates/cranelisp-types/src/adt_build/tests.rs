//! Unit tests for the ADT-entry builder (S110 R-2 — the single derivation the
//! typecheck `deftype` writer and the int bootstrap seeder both call).

use super::*;
use crate::{ModuleFullPath, TypeName};

fn fqtn(module: &str, name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name))
}

fn field(name: &str, ty: Type) -> FieldInfo {
    FieldInfo { name: Symbol::from(name), ty }
}

/// A sum ADT yields, per ctor in tag order: the canonical `Type.Ctor` Def then
/// the bare-name Import alias; then the TypeDef last (the ordering contract).
#[test]
fn sum_adt_entries_canonical_keys_aliases_and_typedef() {
    let fq = fqtn("m", "Maybe");
    let ctors = vec![
        AdtCtorSpec::new(Symbol::from("Just"), vec![field("v", Type::Var(7))], None, false, 3),
        AdtCtorSpec::new(Symbol::from("Nothing"), vec![], None, false, 4),
    ];
    let entries = build_adt_entries::<()>(
        &fq,
        &[Symbol::from("a")],
        &[7],
        Some("maybe a value"),
        &ctors,
        Visibility::Public,
    );

    let keys: Vec<&str> = entries.iter().map(|(k, _)| k.as_ref()).collect();
    assert_eq!(keys, vec!["Maybe.Just", "Just", "Maybe.Nothing", "Nothing", "Maybe"]);

    // Canonical Just: data ctor Def — tag 0, slot 3, quantified Fn scheme.
    let (_, just) = &entries[0];
    let ModuleEntry::Def { kind, scheme, param_names, ast, .. } = just else {
        panic!("canonical ctor key must hold the Def");
    };
    let DefKind::Constructor { got_slot, tag, field_count, internal, type_def, .. } =
        kind.as_ref()
    else {
        panic!("ctor Def must be DefKind::Constructor");
    };
    assert_eq!((*got_slot, *tag, *field_count, *internal), (3, 0, 1, false));
    assert!(type_def.is_none(), "sum ctor carries no type facet");
    assert_eq!(scheme.type_vars, vec![7]);
    assert!(matches!(&scheme.ty, Type::Fn(params, _) if params.len() == 1));
    assert_eq!(param_names.as_slice(), &[Symbol::from("v")]);
    // Synthesised ConstrADT body.
    let body = &ast.as_ref().expect("ctor Def carries a synthesised ast").body;
    assert!(matches!(body, Expr::ConstrADT { tag: 0, fields, .. } if fields.len() == 1));

    // Bare alias points at the canonical key in the type's home module.
    let (_, alias) = &entries[1];
    let ModuleEntry::Import { source, visibility } = alias else {
        panic!("bare ctor name must be an Import alias");
    };
    assert_eq!(source.module.as_ref(), "m");
    assert_eq!(source.symbol.as_ref(), "Maybe.Just");
    assert_eq!(*visibility, Visibility::Public);

    // Nullary Nothing: bare-ADT scheme, still quantified, tag 1.
    let (_, nothing) = &entries[2];
    let ModuleEntry::Def { kind, scheme, .. } = nothing else { panic!("Def expected") };
    let DefKind::Constructor { tag, field_count, .. } = kind.as_ref() else {
        panic!("Constructor expected")
    };
    assert_eq!((*tag, *field_count), (1, 0));
    assert_eq!(scheme.type_vars, vec![7]);
    assert!(matches!(&scheme.ty, Type::ADT(name, args) if name == &fq && args.len() == 1));

    // TypeDef last: full ctor list + the deftype docstring.
    let (_, td) = &entries[4];
    let ModuleEntry::TypeDef { info, docstring, .. } = td else { panic!("TypeDef expected") };
    assert_eq!(info.constructors, vec![Symbol::from("Just"), Symbol::from("Nothing")]);
    assert_eq!(info.type_params, vec![Symbol::from("a")]);
    assert_eq!(docstring.as_deref(), Some("maybe a value"));
}

/// A single-ctor product yields exactly ONE entry: the got-slotted ctor Def at
/// the bare type name, carrying the type facet — no alias, no TypeDef, and the
/// deftype-level docstring falls back onto the ctor Def.
#[test]
fn product_adt_single_dual_facet_entry_with_docstring_fallback() {
    let fq = fqtn("primitives", "Pair");
    let ctors = vec![AdtCtorSpec::new(
        Symbol::from("Pair"),
        vec![field("fst", Type::Var(1)), field("snd", Type::Var(2))],
        None,
        false,
        9,
    )];
    let entries = build_adt_entries::<()>(
        &fq,
        &[Symbol::from("a"), Symbol::from("b")],
        &[1, 2],
        Some("a pair"),
        &ctors,
        Visibility::Public,
    );

    assert_eq!(entries.len(), 1, "product: one dual-facet entry, no alias, no TypeDef");
    let (key, entry) = &entries[0];
    assert_eq!(key.as_ref(), "Pair");
    let ModuleEntry::Def { kind, docstring, param_names, .. } = entry else {
        panic!("Def expected")
    };
    let DefKind::Constructor { got_slot, type_def, .. } = kind.as_ref() else {
        panic!("Constructor expected")
    };
    assert_eq!(*got_slot, 9);
    let facet = type_def.as_ref().expect("product ctor carries the type facet");
    assert_eq!(facet.constructors, vec![Symbol::from("Pair")]);
    assert_eq!(docstring.as_deref(), Some("a pair"), "deftype docstring falls back to ctor");
    assert_eq!(param_names.as_slice(), &[Symbol::from("fst"), Symbol::from("snd")]);
}

/// The `internal` discriminator rides each ctor's `DefKind::Constructor`
/// (`IO`'s `Bind` seed — excluded from user exhaustiveness).
#[test]
fn internal_flag_rides_the_ctor_kind() {
    let fq = fqtn("primitives", "IO");
    let ctors = vec![
        AdtCtorSpec::new(Symbol::from("Pure"), vec![field("v", Type::Var(1))], None, true, 0),
        AdtCtorSpec::new(Symbol::from("Effect"), vec![field("e", Type::Var(1))], None, true, 1),
    ];
    let entries =
        build_adt_entries::<()>(&fq, &[Symbol::from("t")], &[1], None, &ctors, Visibility::Public);
    for (key, entry) in &entries {
        if let ModuleEntry::Def { kind, .. } = entry {
            let DefKind::Constructor { internal, .. } = kind.as_ref() else {
                panic!("Constructor expected")
            };
            assert!(*internal, "ctor {key} must carry internal: true");
        }
    }
}

/// A monomorphic sum (no type params) produces unquantified schemes and a
/// TypeDef with an empty param list — the `Result`-seed shape.
#[test]
fn monomorphic_sum_schemes_are_unquantified() {
    let fq = fqtn("m", "Color");
    let ctors = vec![
        AdtCtorSpec::new(Symbol::from("Red"), vec![], None, false, 0),
        AdtCtorSpec::new(Symbol::from("Green"), vec![], None, false, 1),
    ];
    let entries = build_adt_entries::<()>(&fq, &[], &[], None, &ctors, Visibility::Public);
    let (_, red) = &entries[0];
    let ModuleEntry::Def { scheme, .. } = red else { panic!("Def expected") };
    assert!(scheme.type_vars.is_empty());
    assert!(matches!(&scheme.ty, Type::ADT(_, args) if args.is_empty()));
}
