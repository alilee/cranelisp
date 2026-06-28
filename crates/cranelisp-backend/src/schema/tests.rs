use super::*;
use cranelisp_types::{Scheme, Visibility};
use std::collections::HashMap;

fn fqtn(module: &str, name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from(module), name.into())
}

/// Register a product `deftype` (single same-named ctor) into `tables`,
/// supplying positional `_{i}` field names. Use `register_product_named`
/// to supply real declared names.
fn register_product(
    tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &str,
    name: &str,
    field_types: Vec<Type>,
) {
    let param_names: Vec<Symbol> = (0..field_types.len())
        .map(|i| Symbol::from(format!("_{i}")))
        .collect();
    register_product_named(tables, module, name, param_names, field_types);
}

/// Register a product `deftype` with explicit declared field names —
/// the S79 Option 3a dual-facet shape: a got-slotted ctor `Def` with
/// `DefKind::Constructor { type_def: Some(..), .. }` carrying its real
/// `param_names` (field names) and `scheme` (field types).
fn register_product_named(
    tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &str,
    name: &str,
    param_names: Vec<Symbol>,
    field_types: Vec<Type>,
) {
    let m = ModuleFullPath::from(module);
    let mut st = tables
        .remove(&m)
        .map(|(_, t)| t)
        .unwrap_or_else(|| SymbolTable::new(m.clone()));
    let adt = Type::ADT(fqtn(module, name), vec![]);
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Fn(field_types.clone(), Box::new(adt)),
    };
    let type_def = cranelisp_types::TypeDefInfo {
        name: fqtn(module, name),
        type_params: vec![],
        constructors: vec![Symbol::from(name)],
    };
    st.insert(
        Symbol::from(name),
        ModuleEntry::Def {
            scheme,
            visibility: Visibility::Public,
            docstring: None,
            param_names,
            kind: Box::new(DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn(module, name),
                tag: 0,
                field_count: field_types.len(),
                internal: false,
                type_def: Some(Box::new(type_def)),
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
        },
    );
    tables.insert(m, st);
}

// spec: design/arch/platform-interface.md §5.5.2 — a product type's schema
//       entry lists its single same-named constructor (tag 0) with ordered
//       typed fields; scalar field types render as bare FQ names.
#[test]
fn product_type_schema_lists_typed_fields() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_product_named(
        &tables,
        "shapes",
        "Rectangle",
        vec![Symbol::from("w"), Symbol::from("h")],
        vec![Type::Int, Type::Int],
    );

    let root = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);
    let text = generate_schema(&tables, &[root]);

    assert!(text.starts_with(";; layout-hash: "), "header line present");
    assert!(text.contains("(shapes/Rectangle"), "type keyed by FQ name");
    // S79 Option 3a: the product ctor `Def`'s real `param_names` (w/h) are
    // emitted, NOT positional `_0`/`_1` — the FIXME 0319 field-name fix.
    assert!(
        text.contains("(Rectangle 0 ((w primitives/Int) (h primitives/Int)))"),
        "ctor tag 0 with two real-named typed fields; got:\n{text}",
    );
}

// spec: design/arch/platform-interface.md §5.5.1 — the transitive closure
//       pulls a nested ADT into the schema (a field whose type is another
//       ADT joins the set). Scalar leaves terminate.
#[test]
fn closure_pulls_nested_adt() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_product(&tables, "geometry", "Point", vec![Type::Int, Type::Int]);
    register_product(
        &tables,
        "shapes",
        "Box",
        vec![Type::ADT(fqtn("geometry", "Point"), vec![])],
    );

    let root = Type::ADT(fqtn("shapes", "Box"), vec![]);
    let text = generate_schema(&tables, &[root]);
    assert!(text.contains("(shapes/Box"), "root in schema");
    assert!(
        text.contains("(geometry/Point"),
        "nested ADT pulled into the closure; got:\n{text}",
    );
    assert!(
        text.contains("geometry/Point"),
        "Box's field renders the nested ADT type by FQ name",
    );
}

// spec: design/arch/platform-interface.md §5.5.4 — regenerating the schema
//       over identical resolved source yields an identical hash (the walk is
//       source-positional + canonical-text; q-tag-stability). A layout change
//       changes the hash.
#[test]
fn layout_hash_is_stable_and_change_sensitive() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_product(&tables, "shapes", "Rectangle", vec![Type::Int, Type::Int]);
    let root = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);

    let h1 = compute_layout_hash(&tables, std::slice::from_ref(&root));
    let h2 = compute_layout_hash(&tables, std::slice::from_ref(&root));
    assert_eq!(h1, h2, "two runs over identical source agree");

    // The header hash equals compute_layout_hash.
    let text = generate_schema(&tables, std::slice::from_ref(&root));
    assert!(
        text.contains(&format!(";; layout-hash: {h1}")),
        "header hash matches compute_layout_hash",
    );

    // A changed layout (one fewer field) changes the hash.
    let tables2: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_product(&tables2, "shapes", "Rectangle", vec![Type::Int]);
    let h3 = compute_layout_hash(&tables2, &[root]);
    assert_ne!(h1, h3, "a layout change must change the hash");
}

// spec: design/arch/platform-interface.md §5.5.1 — `platform_effect_roots`
//       derives the root ADT set from the PlatformEffect sig schemes,
//       excluding scalars; the schema closes over exactly those.
#[test]
fn platform_effect_roots_excludes_scalars() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_product(&tables, "shapes", "Rectangle", vec![Type::Int, Type::Int]);

    // A platform module with one effect: (Fn [shapes/Rectangle] primitives/Int).
    let plat = ModuleFullPath::from("platform.shapes");
    let mut pt = SymbolTable::new(plat.clone());
    let rect = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);
    pt.insert(
        Symbol::from("rectangle-area"),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![rect.clone()], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![Symbol::from("r")],
            kind: Box::new(DefKind::PlatformEffect {
                scheduling_class: cranelisp_types::SchedulingClass::Sequential,
                poll_shape: false,
                got_slot: 0,
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
        },
    );
    tables.insert(plat.clone(), pt);

    let roots = platform_effect_roots(tables.get(&plat).unwrap().value());
    assert_eq!(roots, vec![rect], "Rectangle is the only ADT root; Int excluded");
}

// ── subst_for_ctor_fields: identity self-map elision (FIXME 0284) ──────────

// A polymorphic type instantiated at its OWN residual type var produces a
// positional mapping `{field_var -> Var(field_var)}` — the same id on both
// sides. `cranelisp_types::apply` treats `{id -> Var(id)}` as an
// occurs-check violation and `debug_assert!`-panics on it. The baker must
// NOT emit that no-op mapping. This is the bake-side root of the trace
// ADT-render crash (e.g. tracing `mk : (Fn [] (Option a))`).
#[test]
fn subst_skips_identity_self_map() {
    // Option-shaped: None has no fields, Some has one field of type `a`
    // (Var(0)). Instantiated at `[Var(0)]` — its own var.
    let field_type_lists = vec![vec![], vec![Type::Var(0)]];
    let subst = subst_for_ctor_fields(&field_type_lists, &[Type::Var(0)]);
    assert!(
        !subst.contains_key(&0),
        "identity self-map {{0 -> Var(0)}} must be elided, not inserted: {subst:?}"
    );
    // And applying the (empty) subst to the field type must not panic and
    // must leave the residual var intact (rendered bare downstream).
    let resolved = cranelisp_types::apply(&subst, &Type::Var(0));
    assert_eq!(resolved, Type::Var(0));
}

// A non-identity instantiation is still recorded (the elision is narrow:
// only `{id -> Var(id)}` is skipped, concrete and cross-var maps stand).
#[test]
fn subst_keeps_concrete_and_cross_var_maps() {
    let field_type_lists = vec![vec![Type::Var(0)], vec![Type::Var(1)]];
    // Var(0) -> Int (concrete), Var(1) -> Var(2) (cross-var, not identity).
    let subst = subst_for_ctor_fields(
        &field_type_lists,
        &[Type::Int, Type::Var(2)],
    );
    assert_eq!(subst.get(&0), Some(&Type::Int), "concrete map kept");
    assert_eq!(subst.get(&1), Some(&Type::Var(2)), "cross-var map kept");
}
