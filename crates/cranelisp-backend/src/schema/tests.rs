use super::*;
use cranelisp_types::{
    CallableOrigin, ConcreteType, DefnVariant, Expr, MonoDefnVariant, MonoExpr, Realization,
    Scheme, Span, SynthSpec, TemplateBody, TemplateKind, Visibility,
};
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
    let symbol = Symbol::from(name);
    st.install_concrete(
        symbol.clone(),
        scheme,
        param_names,
        None,
        0,
        CallableOrigin::Ctor {
            type_name: fqtn(module, name),
            tag: 0,
            field_count: field_types.len(),
            type_def: Some(Box::new(type_def)),
        },
        Realization::Body {
            view: MonoDefnVariant {
                name: symbol,
                params: vec![],
                body: MonoExpr::IntLit {
                    value: 0,
                    span: Span::SYNTHETIC,
                    ty: ConcreteType::Int,
                },
                span: Span::SYNTHETIC,
                mode_summary: None,
            },
            code: None,
        },
        None,
        vec![],
        Visibility::Public,
    )
    .expect("install product constructor fixture");
    tables.insert(m, st);
}

/// [`register_product_named`] for a type declaring the parameters
/// `type_vars`, in declaration order: its constructor is a template.
fn register_parametric_product(
    tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &str,
    name: &str,
    type_vars: &[cranelisp_types::TypeId],
    param_names: Vec<Symbol>,
    field_types: Vec<Type>,
) {
    let m = ModuleFullPath::from(module);
    let mut st = tables
        .remove(&m)
        .map(|(_, t)| t)
        .unwrap_or_else(|| SymbolTable::new(m.clone()));
    let adt = Type::ADT(
        fqtn(module, name),
        type_vars.iter().map(|&id| Type::Var(id)).collect(),
    );
    let type_def = cranelisp_types::TypeDefInfo {
        name: fqtn(module, name),
        type_params: type_vars
            .iter()
            .map(|id| Symbol::from(format!("t{id}")))
            .collect(),
        constructors: vec![Symbol::from(name)],
    };
    st.install_template(
        Symbol::from(name),
        Scheme {
            type_vars: type_vars.to_vec(),
            constraints: HashMap::new(),
            ty: Type::Fn(field_types.clone(), Box::new(adt)),
        },
        param_names,
        None,
        0,
        CallableOrigin::Ctor {
            type_name: fqtn(module, name),
            tag: 0,
            field_count: field_types.len(),
            type_def: Some(Box::new(type_def)),
        },
        TemplateBody::Synth(SynthSpec::new(DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        })),
        TemplateKind::Parametric,
        vec![],
        Visibility::Public,
    )
    .expect("install parametric product constructor fixture");
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
    pt.install_platform(
        Symbol::from("rectangle-area"),
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![rect.clone()], Box::new(Type::Int)),
        },
        vec![Symbol::from("r")],
        None,
        0,
        cranelisp_types::SchedulingClass::Sequential,
        false,
        0,
        Visibility::Public,
    )
    .expect("install platform-effect fixture");
    tables.insert(plat.clone(), pt);

    let roots = platform_effect_roots(tables.get(&plat).unwrap().value());
    assert_eq!(
        roots,
        vec![rect],
        "Rectangle is the only ADT root; Int excluded"
    );
}

// ── ctor_field_types_at: pairing by declared parameter (ACT-1062) ──────────

fn adt(name: &str, args: Vec<Type>) -> Type {
    Type::ADT(fqtn("user", name), args)
}

// spec: design/backend/trace-codegen.md §3 — `(deftype (P a b) (MkP [:b y
//       :a x]))` at `(P Int String)`: `y` takes `b`'s argument and `x` takes
//       `a`'s, whatever order the fields mention them in.
#[test]
fn ctor_fields_out_of_order_product_take_their_parameters_types() {
    let (a, b) = (Type::Var(0), Type::Var(1));
    let got = ctor_field_types_at(
        &[b, a.clone()],
        &[Type::Var(0), Type::Var(1)],
        &[Type::Int, Type::String],
    );
    assert_eq!(got, Ok(vec![Type::String, Type::Int]));
}

// spec: design/backend/trace-codegen.md §3 — a sum whose constructors
//       disagree on first appearance: each constructor's fields are decided
//       by its own declared parameters, not by an order across constructors.
#[test]
fn ctor_fields_of_a_sum_are_decided_per_constructor() {
    // (deftype (E a b) (L [:b l]) (R [:a r])) at (E Int String).
    let params = [Type::Var(0), Type::Var(1)];
    let args = [Type::Int, Type::String];
    assert_eq!(
        ctor_field_types_at(&[Type::Var(1)], &params, &args),
        Ok(vec![Type::String]),
        "L's field mentions b"
    );
    assert_eq!(
        ctor_field_types_at(&[Type::Var(0)], &params, &args),
        Ok(vec![Type::Int]),
        "R's field mentions a"
    );
}

// spec: design/backend/trace-codegen.md §3 — a parameter no field mentions
//       does not shift the later pairings.
#[test]
fn ctor_fields_skip_an_unmentioned_parameter() {
    // (deftype (R a b) (MkR [:b y])) at (R Int String) yields [String].
    let got = ctor_field_types_at(
        &[Type::Var(1)],
        &[Type::Var(0), Type::Var(1)],
        &[Type::Int, Type::String],
    );
    assert_eq!(got, Ok(vec![Type::String]));
}

// spec: design/backend/trace-codegen.md §3 — a nested field type is
//       substituted throughout.
#[test]
fn ctor_fields_substitute_inside_a_nested_field_type() {
    let got = ctor_field_types_at(
        &[adt("Option", vec![Type::Var(1)])],
        &[Type::Var(0), Type::Var(1)],
        &[Type::Int, Type::String],
    );
    assert_eq!(got, Ok(vec![adt("Option", vec![Type::String])]));
}

// spec: design/backend/trace-codegen.md §3 — an argument count that differs
//       from the declared count is a keying error.
#[test]
fn ctor_fields_refuse_an_argument_count_mismatch() {
    let got = ctor_field_types_at(&[Type::Var(0)], &[Type::Var(0), Type::Var(1)], &[Type::Int]);
    assert_eq!(
        got,
        Err(ParamPairingError::Arity {
            declared: 2,
            supplied: 1
        })
    );
}

// spec: design/backend/trace-codegen.md §3 — a declared parameter that is not
//       a variable must equal its argument; equal passes, unequal is refused.
#[test]
fn ctor_fields_check_a_concrete_declared_parameter() {
    let params = [Type::Int, Type::Var(1)];
    assert_eq!(
        ctor_field_types_at(&[Type::Var(1)], &params, &[Type::Int, Type::Bool]),
        Ok(vec![Type::Bool])
    );
    assert_eq!(
        ctor_field_types_at(&[Type::Var(1)], &params, &[Type::String, Type::Bool]),
        Err(ParamPairingError::Mismatch { position: 0 })
    );
}

// spec: design/backend/trace-codegen.md §3 — the identity elision of FIXME
//       0284: a type instantiated at its own residual variable maps nothing,
//       so `apply` never sees `{id -> Var(id)}` and the field stays residual.
#[test]
fn ctor_fields_elide_the_identity_pairing() {
    // Option-shaped `Some` at `(Option a)` with `a` its own variable.
    let got = ctor_field_types_at(&[Type::Var(0)], &[Type::Var(0)], &[Type::Var(0)]);
    assert_eq!(got, Ok(vec![Type::Var(0)]));
}

// spec: design/backend/trace-codegen.md §3 — a pairing to another variable
//       is kept; the elision is only the identity.
#[test]
fn ctor_fields_keep_a_cross_variable_pairing() {
    let got = ctor_field_types_at(&[Type::Var(0)], &[Type::Var(0)], &[Type::Var(2)]);
    assert_eq!(got, Ok(vec![Type::Var(2)]));
}

// spec: design/backend/trace-codegen.md §3 — the declared parameters are the
//       arguments of the scheme's result ADT, for a data and a nullary
//       constructor alike.
#[test]
fn declared_params_read_the_scheme_result() {
    let result = adt("P", vec![Type::Var(0), Type::Var(1)]);
    let data = Type::Fn(vec![Type::Var(1)], Box::new(result.clone()));
    assert_eq!(declared_params(&data), &[Type::Var(0), Type::Var(1)]);
    assert_eq!(declared_params(&result), &[Type::Var(0), Type::Var(1)]);
    assert!(declared_params(&Type::Int).is_empty());
}

// spec: design/backend/trace-codegen.md §3 — the schema walk names each
//       field with the argument of the parameter it mentions: `(P Int
//       String)` for `(deftype (P a b) (P [:b y :a x]))` lists `y` as a
//       String and `x` as an Int.
#[test]
fn schema_walk_pairs_an_out_of_order_product_by_declared_parameter() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_parametric_product(
        &tables,
        "shapes",
        "P",
        &[0, 1],
        vec![Symbol::from("y"), Symbol::from("x")],
        vec![Type::Var(1), Type::Var(0)],
    );

    let root = Type::ADT(fqtn("shapes", "P"), vec![Type::Int, Type::String]);
    let text = generate_schema(&tables, &[root]);

    assert!(
        text.contains("(P 0 ((y primitives/String) (x primitives/Int)))"),
        "fields take their declared parameters' arguments; got:\n{text}",
    );
}

// ── IO's layout is the ABI, as Vec's is (S125 opaque IO, row IO-T) ─────────

/// `primitives/IO` as the bootstrap installs it under row IO-T: one type
/// parameter and no constructors.
fn register_constructorless_io(tables: &DashMap<ModuleFullPath, SymbolTable>) {
    let m = ModuleFullPath::from("primitives");
    let mut st = tables
        .remove(&m)
        .map(|(_, t)| t)
        .unwrap_or_else(|| SymbolTable::new(m.clone()));
    crate::test_support::install_type_fixture(
        &mut st,
        Symbol::from("IO"),
        cranelisp_types::TypeDefInfo {
            name: fqtn("primitives", "IO"),
            type_params: vec![Symbol::from("a")],
            constructors: vec![],
        },
    );
    tables.insert(m, st);
}

fn io_of(payload: Type) -> Type {
    Type::ADT(fqtn("primitives", "IO"), vec![payload])
}

// spec: design/backend/io-trampoline.md §1.5 — a platform effect
//       `(Fn [] (primitives/IO shapes/Rectangle))` roots `Rectangle` alone: `IO`
//       is never a root and never a schema entry.
#[test]
fn io_result_root_yields_its_payload_and_no_io_entry() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_constructorless_io(&tables);
    register_product(&tables, "shapes", "Rectangle", vec![Type::Int, Type::Int]);
    let rect = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);

    let plat = ModuleFullPath::from("platform.shapes");
    let mut pt = SymbolTable::new(plat.clone());
    pt.install_platform(
        Symbol::from("make-rectangle"),
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![], Box::new(io_of(rect.clone()))),
        },
        vec![],
        None,
        0,
        cranelisp_types::SchedulingClass::Sequential,
        false,
        0,
        Visibility::Public,
    )
    .expect("install platform-effect fixture");
    tables.insert(plat.clone(), pt);

    let roots = platform_effect_roots(tables.get(&plat).unwrap().value());
    assert_eq!(roots, vec![rect], "IO is not a root; its payload is");
    let text = generate_schema(&tables, &roots);
    assert!(!text.contains("primitives/IO"), "no IO key; got:\n{text}");
    assert!(
        text.contains("(shapes/Rectangle"),
        "payload entry; got:\n{text}"
    );
}

// spec: design/backend/io-trampoline.md §1.5 — an ADT reached only
//       through an `IO`-typed field of another ADT is in the closure.
#[test]
fn adt_reached_only_through_an_io_field_is_in_the_closure() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_constructorless_io(&tables);
    register_product(&tables, "shapes", "Inner", vec![Type::Int]);
    register_product_named(
        &tables,
        "shapes",
        "Holder",
        vec![Symbol::from("action")],
        vec![io_of(Type::ADT(fqtn("shapes", "Inner"), vec![]))],
    );

    let root = Type::ADT(fqtn("shapes", "Holder"), vec![]);
    let text = generate_schema(&tables, &[root]);
    assert!(
        text.contains("(shapes/Inner"),
        "Inner joins the closure through Holder's IO field; got:\n{text}"
    );
    assert!(
        !text.contains("\n  ((primitives/IO") && !text.contains("\n  (primitives/IO"),
        "IO is not an entry; got:\n{text}"
    );
}

// spec: design/backend/io-trampoline.md §1.5 — `Vec` output is
//       byte-identical: no `Vec` entry, the element walked, a `Vec` field
//       rendered in its applied form.
#[test]
fn vec_schema_output_is_unchanged() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    register_product_named(
        &tables,
        "geometry",
        "Point",
        vec![Symbol::from("x")],
        vec![Type::Int],
    );
    let point = Type::ADT(fqtn("geometry", "Point"), vec![]);
    let vec_of = |t: Type| Type::ADT(fqtn("primitives", "Vec"), vec![t]);
    register_product_named(
        &tables,
        "shapes",
        "Path",
        vec![Symbol::from("points")],
        vec![vec_of(point.clone())],
    );

    let mut roots = Vec::new();
    collect_adt_roots(
        &Type::Fn(
            vec![vec_of(Type::ADT(fqtn("shapes", "Path"), vec![]))],
            Box::new(Type::Int),
        ),
        &mut roots,
    );
    assert_eq!(roots, vec![Type::ADT(fqtn("shapes", "Path"), vec![])]);
    let text = generate_schema(&tables, &roots);
    let body = text.split_once('\n').expect("header line").1;
    assert_eq!(
        body,
        "(schema\n  (geometry/Point\n    (Point 0 ((x primitives/Int))))\n  \
         (shapes/Path\n    (Path 0 ((points (Vec geometry/Point))))))",
    );
}
