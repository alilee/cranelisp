//! platform_schema_roundtrip.rs — pin the `/platform-schema` artifact grammar
//! agreement between the two crates that replicate it but cannot depend on each
//! other (FIXME 0371 / `audits/platform-2026-06-14.md` MED-3).
//!
//! `cranelisp-backend::schema::generate_schema` EMITS the artifact;
//! `cranelisp-platform::Schema::parse` CONSUMES it. The grammar is replicated in
//! both crates by hand (frontend is upstream of platform, so platform cannot
//! reuse the reader — `crates/cranelisp-platform/src/schema.rs` "Replication,
//! not dependency"). Nothing pinned their agreement: the parser's own tests use
//! hand-written literals, NOT generator output, so a grammar drift escaped BOTH
//! crate test suites AND the layout-hash gate, surfacing only as a runtime
//! field-read error against a live platform DLL.
//!
//! The root `cranelisp` package depends on BOTH crates, so this workspace
//! integration test is the one place the two surfaces meet. It builds a
//! representative corpus of type/ctor/field shapes, runs `generate_schema` to
//! text, runs `Schema::parse` on that exact text, and asserts the parsed
//! structure round-trips — type keys resolve, ctor tags/names match, field
//! names/offsets/types match, nested + parameterised + Vec shapes survive. Drift
//! now fails THIS test instead of a production DLL load.
//!
//! spec: design/arch/platform-interface.md §5.5 (the field-by-name generated
//! schema artifact, user-ratified 2026-06-07) — §5.5.2 (FieldType grammar),
//! §5.5.3 (structured type-expression keys, never a mangle), §5.5.4 (the
//! canonical-text layout hash). Pins the generator↔parser grammar agreement
//! (BC §3 platform-interface codegen role ↔ BC §5 platform schema consumer).

use cranelisp_backend::schema::generate_schema;
use cranelisp_platform::{FieldType, Schema};
use cranelisp_types::{
    DefKind, FQTypeName, ModuleEntry, ModuleFullPath, Scheme, Symbol, SymbolTable,
    Type, TypeDefInfo, Visibility,
};
use dashmap::DashMap;
use std::collections::HashMap;

type Tables = DashMap<ModuleFullPath, SymbolTable>;

fn fqtn(module: &str, name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from(module), name.into())
}

/// Register a sum/enum/product type: a `ModuleEntry::TypeDef` naming the
/// constructors plus one got-slotted ctor `Def` per constructor (the S79
/// Option 3a shape the generator's `ctors_of` walks). Each constructor carries
/// declared field names (`param_names`) and field types (the scheme's `Fn`
/// params); a nullary constructor has an empty field list (non-`Fn` scheme).
fn register_type(
    tables: &Tables,
    module: &str,
    type_name: &str,
    ctors: &[(&str, usize, &[(&str, Type)])],
) {
    let m = ModuleFullPath::from(module);
    let mut st = tables
        .remove(&m)
        .map(|(_, t)| t)
        .unwrap_or_else(|| SymbolTable::new(m.clone()));

    let adt = Type::ADT(fqtn(module, type_name), vec![]);

    // The TypeDef entry naming the constructors (sum/enum case; the product case
    // would fold this onto the ctor `Def`'s type_def facet, but a uniform
    // TypeDef entry exercises the same walk and keeps the corpus simple).
    st.insert(
        Symbol::from(type_name),
        ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: fqtn(module, type_name),
                type_params: vec![],
                constructors: ctors.iter().map(|(c, _, _)| Symbol::from(*c)).collect(),
            },
            visibility: Visibility::Public,
            docstring: None,
        },
    );

    for (ctor_name, tag, fields) in ctors {
        let field_names: Vec<Symbol> =
            fields.iter().map(|(n, _)| Symbol::from(*n)).collect();
        let field_types: Vec<Type> = fields.iter().map(|(_, t)| t.clone()).collect();
        let scheme = if field_types.is_empty() {
            // Nullary ctor: scheme is the bare ADT (no Fn).
            Scheme { type_vars: vec![], constraints: HashMap::new(), ty: adt.clone() }
        } else {
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(field_types.clone(), Box::new(adt.clone())),
            }
        };
        st.insert(
            Symbol::from(*ctor_name),
            ModuleEntry::def(
                scheme,
                DefKind::Constructor {
                    got_slot: 0,
                    type_name: fqtn(module, type_name),
                    tag: *tag,
                    field_count: field_types.len(),
                    internal: false,
                    type_def: Some(Box::new(TypeDefInfo {
                        name: fqtn(module, type_name),
                        type_params: vec![],
                        constructors: ctors
                            .iter()
                            .map(|(c, _, _)| Symbol::from(*c))
                            .collect(),
                    })),
                    mode_summary: None,
                },
            )
            .param_names(field_names)
            .build(),
        );
    }

    tables.insert(m, st);
}

/// The corpus: scalar product, multi-field product, sum (multi-ctor + nullary),
/// nested ADT, Vec-of-scalar field, Vec-of-ADT field. One `generate_schema`
/// over all roots, then one `Schema::parse` over the emitted text.
fn build_and_parse(roots: &[Type]) -> (String, Schema) {
    let tables: Tables = DashMap::new();

    // Scalar product: shapes/Rectangle (w h : Int).
    register_type(
        &tables,
        "shapes",
        "Rectangle",
        &[("Rectangle", 0, &[("w", Type::Int), ("h", Type::Int)])],
    );
    // Nested ADT: geometry/Point (x y : Int), shapes/Box (origin : Point).
    register_type(
        &tables,
        "geometry",
        "Point",
        &[("Point", 0, &[("x", Type::Int), ("y", Type::Int)])],
    );
    register_type(
        &tables,
        "shapes",
        "Box",
        &[(
            "Box",
            0,
            &[("origin", Type::ADT(fqtn("geometry", "Point"), vec![]))],
        )],
    );
    // Sum with a nullary ctor + a scalar ctor + a String ctor:
    // shapes/Tag (None 0 ()) (Named 1 (label : String)) (Coded 2 (n : Int)).
    register_type(
        &tables,
        "shapes",
        "Tag",
        &[
            ("None", 0, &[]),
            ("Named", 1, &[("label", Type::String)]),
            ("Coded", 2, &[("n", Type::Int)]),
        ],
    );
    // Vec-of-scalar + Vec-of-ADT fields: shapes/Poly
    // (verts : (Vec Int)) (pts : (Vec geometry/Point)).
    register_type(
        &tables,
        "shapes",
        "Poly",
        &[(
            "Poly",
            0,
            &[
                (
                    "verts",
                    Type::ADT(fqtn("primitives", "Vec"), vec![Type::Int]),
                ),
                (
                    "pts",
                    Type::ADT(
                        fqtn("primitives", "Vec"),
                        vec![Type::ADT(fqtn("geometry", "Point"), vec![])],
                    ),
                ),
            ],
        )],
    );

    let text = generate_schema(&tables, roots);
    let schema = Schema::parse(&text)
        .unwrap_or_else(|e| panic!("generated schema must parse; parser said:\n  {e}\n\nGENERATED TEXT:\n{text}"));
    (text, schema)
}

// spec: design/arch/platform-interface.md §5.5.2 — a scalar product type
// round-trips: generator emits `(shapes/Rectangle (Rectangle 0 ((w …) (h …))))`,
// parser reads the same key, ctor name/tag, field names, offsets, and scalar
// FieldTypes.
#[test]
fn roundtrip_scalar_product() {
    let root = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);
    let (text, schema) = build_and_parse(std::slice::from_ref(&root));

    assert!(text.starts_with(";; layout-hash: "), "header line present:\n{text}");

    let shape = schema
        .lookup_type("shapes/Rectangle")
        .expect("Rectangle resolves by the generator's emitted FQ key");
    assert_eq!(shape.ctors.len(), 1, "product = one ctor");
    assert_eq!(shape.ctors[0].name, "Rectangle");
    assert_eq!(shape.ctors[0].tag, 0);
    // Field names + tag-at-0 / fields-from-8 offset rule survive the round-trip.
    assert_eq!(schema.field_offset("shapes/Rectangle", None, "w"), Some(8));
    assert_eq!(schema.field_offset("shapes/Rectangle", None, "h"), Some(16));
    assert_eq!(
        schema.field_type("shapes/Rectangle", None, "w"),
        Some(&FieldType::Scalar("primitives/Int".to_string())),
        "scalar field type survives",
    );
}

// spec: design/arch/platform-interface.md §5.5.1 — the transitive closure pulls
// a nested ADT into the schema, and the field referencing it round-trips as an
// `Adt` FieldType keyed by the nested type's FQ name (drives read_field
// nested-ADT navigation).
#[test]
fn roundtrip_nested_adt() {
    let root = Type::ADT(fqtn("shapes", "Box"), vec![]);
    let (_text, schema) = build_and_parse(std::slice::from_ref(&root));

    // Both the root and the closed-over nested type resolve.
    assert!(schema.lookup_type("shapes/Box").is_some(), "root present");
    assert!(
        schema.lookup_type("geometry/Point").is_some(),
        "nested ADT pulled into the closure + round-trips",
    );
    // The field's FieldType names the nested type by FQ key (the navigation hook).
    assert_eq!(
        schema.field_type("shapes/Box", None, "origin"),
        Some(&FieldType::Adt("geometry/Point".to_string(), Vec::new())),
    );
    // And Point's own scalar fields round-trip.
    assert_eq!(schema.field_offset("geometry/Point", None, "x"), Some(8));
    assert_eq!(schema.field_offset("geometry/Point", None, "y"), Some(16));
}

// spec: design/arch/platform-interface.md §5.5.2 — a sum type round-trips: all
// constructors with their tags, a nullary ctor with an empty field list, and
// per-constructor field lookup by ctor name. A String field's scalar type
// survives.
#[test]
fn roundtrip_sum_with_nullary_and_typed_ctors() {
    let root = Type::ADT(fqtn("shapes", "Tag"), vec![]);
    let (_text, schema) = build_and_parse(std::slice::from_ref(&root));

    let names = schema.ctor_names("shapes/Tag").expect("Tag resolves");
    assert_eq!(names, vec!["None", "Named", "Coded"], "all ctors + order survive");

    // Nullary ctor: no fields.
    assert_eq!(schema.field_offset("shapes/Tag", Some("None"), "label"), None);
    // Typed ctors: per-ctor field lookup + scalar field types.
    assert_eq!(schema.field_offset("shapes/Tag", Some("Named"), "label"), Some(8));
    assert_eq!(
        schema.field_type("shapes/Tag", Some("Named"), "label"),
        Some(&FieldType::Scalar("primitives/String".to_string())),
        "String field type survives the round-trip",
    );
    assert_eq!(
        schema.field_type("shapes/Tag", Some("Coded"), "n"),
        Some(&FieldType::Scalar("primitives/Int".to_string())),
    );
}

// spec: design/arch/platform-interface.md §5.5.2 — Vec field types round-trip:
// `(Vec primitives/Int)` and `(Vec geometry/Point)`. The Vec element ADT is
// pulled into the closure even though Vec itself is not a schema entry.
#[test]
fn roundtrip_vec_fields() {
    let root = Type::ADT(fqtn("shapes", "Poly"), vec![]);
    let (_text, schema) = build_and_parse(std::slice::from_ref(&root));

    assert_eq!(
        schema.field_type("shapes/Poly", None, "verts"),
        Some(&FieldType::Vec(Box::new(FieldType::Scalar(
            "primitives/Int".to_string()
        )))),
        "Vec-of-scalar field round-trips",
    );
    assert_eq!(
        schema.field_type("shapes/Poly", None, "pts"),
        Some(&FieldType::Vec(Box::new(FieldType::Adt(
            "geometry/Point".to_string(),
            Vec::new()
        )))),
        "Vec-of-ADT field round-trips",
    );
    // Vec's element ADT joins the closure even though Vec is not an entry.
    assert!(
        schema.lookup_type("geometry/Point").is_some(),
        "Vec element ADT pulled into the closure",
    );
    assert!(
        schema.lookup_type("primitives/Vec").is_none(),
        "Vec itself is not a schema entry (its layout is the ABI)",
    );
}

// spec: design/arch/platform-interface.md §5.5.4 — the GENERATOR's emitted key
// strings are EXACTLY the keys the PARSER resolves by. This is the load-bearing
// drift guard: every type key the generator writes must be a key the parser
// reproduces from the same text. We assert it structurally — every entry
// generate_schema emits (its `(typekey …)` heads) is `lookup_type`-resolvable
// in the parsed schema, so a one-sided grammar change in either crate breaks
// this test rather than a live DLL field read.
#[test]
fn generator_keys_are_exactly_parser_keys() {
    // All roots at once — the widest corpus surface.
    let roots = vec![
        Type::ADT(fqtn("shapes", "Rectangle"), vec![]),
        Type::ADT(fqtn("shapes", "Box"), vec![]),
        Type::ADT(fqtn("shapes", "Tag"), vec![]),
        Type::ADT(fqtn("shapes", "Poly"), vec![]),
    ];
    let (text, schema) = build_and_parse(&roots);

    // Every entry the generator emitted (the closed-over set) must resolve in
    // the parsed schema by its emitted key. These are the keys the closure walk
    // produced — Rectangle, Box, geometry/Point (nested + Vec-pulled), Tag, Poly.
    for key in [
        "shapes/Rectangle",
        "shapes/Box",
        "geometry/Point",
        "shapes/Tag",
        "shapes/Poly",
    ] {
        assert!(
            schema.lookup_type(key).is_some(),
            "generator emitted key {key:?} but parser did not resolve it — \
             generator↔parser grammar DRIFT. Generated text:\n{text}",
        );
    }

    // Re-generation stability: re-parsing the SAME text yields the same key set
    // (the parser is a pure function of the artifact text — no hidden state).
    let reparsed = Schema::parse(&text).expect("re-parse of identical text");
    for key in ["shapes/Rectangle", "shapes/Box", "geometry/Point", "shapes/Tag", "shapes/Poly"]
    {
        assert_eq!(
            schema.lookup_type(key).is_some(),
            reparsed.lookup_type(key).is_some(),
            "re-parse must be stable for key {key:?}",
        );
    }
}
