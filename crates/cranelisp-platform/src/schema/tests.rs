use super::*;

// spec: design/arch/platform-interface.md §5.5.2 — a product type parses
// to one constructor with ordered named+typed fields; field offsets follow
// the tag-at-0 / fields-from-8 layout rule.
#[test]
fn parse_product_rectangle() {
    let artifact = "\
;; layout-hash: deadbeef
(schema
  (shapes/Rectangle
    (Rectangle 0 ((w primitives/Int) (h primitives/Int)))))";
    let schema = Schema::parse(artifact).expect("parses");
    assert!(!schema.is_empty());
    let shape = schema
        .lookup_type("shapes/Rectangle")
        .expect("entry present");
    assert_eq!(shape.ctors.len(), 1);
    assert_eq!(shape.ctors[0].name, "Rectangle");
    assert_eq!(shape.ctors[0].tag, 0);
    assert_eq!(schema.field_offset("shapes/Rectangle", None, "w"), Some(8));
    assert_eq!(schema.field_offset("shapes/Rectangle", None, "h"), Some(16));
    assert_eq!(
        schema.field_type("shapes/Rectangle", None, "w"),
        Some(&FieldType::Scalar("primitives/Int".to_string()))
    );
}

// spec: design/arch/platform-interface.md §5.5.2 — a sum type lists all
// constructors with their tags; per-constructor field lookup uses the ctor
// name.
#[test]
fn parse_sum_option() {
    let artifact = "\
;; layout-hash: abc
(schema
  (shapes/OptionInt
    (None 0 ())
    (Some 1 ((val primitives/Int)))))";
    let schema = Schema::parse(artifact).expect("parses");
    let names = schema.ctor_names("shapes/OptionInt").unwrap();
    assert_eq!(names, vec!["None", "Some"]);
    assert_eq!(
        schema.field_offset("shapes/OptionInt", Some("Some"), "val"),
        Some(8)
    );
    // None has no fields.
    assert_eq!(
        schema.field_offset("shapes/OptionInt", Some("None"), "val"),
        None
    );
    // Unqualified lookup on a sum is ambiguous → None.
    assert_eq!(schema.field_offset("shapes/OptionInt", None, "val"), None);
}

// spec: design/arch/platform-interface.md §5.5.2 — typed fields drive
// nested-ADT navigation: a field whose type is another ADT records that
// ADT's key so read_field can look it up in the same map.
#[test]
fn parse_nested_adt_field() {
    let artifact = "\
;; layout-hash: 00
(schema
  (shapes/Box
    (Box 0 ((origin geometry/Point))))
  (geometry/Point
    (Point 0 ((x primitives/Int) (y primitives/Int)))))";
    let schema = Schema::parse(artifact).expect("parses");
    assert_eq!(
        schema.field_type("shapes/Box", None, "origin"),
        Some(&FieldType::Adt("geometry/Point".to_string(), Vec::new()))
    );
    // The nested type is reachable in the same map.
    assert!(schema.lookup_type("geometry/Point").is_some());
}

// spec: design/arch/platform-interface.md §5.5.3 — a concrete
// instantiation is keyed by the structured type expression, never a mangle.
#[test]
fn parse_concrete_instantiation_key() {
    let artifact = "\
;; layout-hash: 11
(schema
  ((Option shapes/Rectangle)
    (None 0 ())
    (Some 1 ((val shapes/Rectangle)))))";
    let schema = Schema::parse(artifact).expect("parses");
    assert!(schema.lookup_type("(Option shapes/Rectangle)").is_some());
}

// spec: design/arch/platform-interface.md §5.5.2 — Vec field type round-trips.
#[test]
fn parse_vec_field_type() {
    let artifact = "\
(schema
  (shapes/Poly
    (Poly 0 ((verts (Vec primitives/Int))))))";
    let schema = Schema::parse(artifact).expect("parses");
    assert_eq!(
        schema.field_type("shapes/Poly", None, "verts"),
        Some(&FieldType::Vec(Box::new(FieldType::Scalar(
            "primitives/Int".to_string()
        ))))
    );
}

// spec: design/arch/platform-interface.md §5.5 — an artifact carrying only
// the layout-hash header (a platform that marshals no ADTs) parses to an
// empty schema.
#[test]
fn parse_header_only_is_empty() {
    let schema = Schema::parse(";; layout-hash: cafe\n").expect("parses");
    assert!(schema.is_empty());
}

// spec: design/arch/platform-interface.md §5.5.1 — the parser reads the
// artifact grammar verbatim; a non-`(schema …)` head is rejected.
#[test]
fn reject_missing_schema_keyword() {
    let err = Schema::parse("(notschema)").unwrap_err();
    assert!(matches!(err, SchemaParseError::MissingSchemaKeyword { .. }));
}
