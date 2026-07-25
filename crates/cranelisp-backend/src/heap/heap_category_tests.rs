use super::*;
use cranelisp_types::{DefKind, FQTypeName, Scheme, Type, TypeDefInfo, TypeName, Visibility};

const TEST_MOD: &str = "test";

/// A constructor spec for test fixtures: name, tag, and field count.
struct CtorSpec {
    name: &'static str,
    tag: usize,
    field_count: usize,
}

/// Test helper: create an FQTypeName in a "test" module.
fn test_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from(TEST_MOD), TypeName::from(name))
}

/// Helper: nullary constructor spec (no fields).
fn nullary_ctor(name: &'static str, tag: usize) -> CtorSpec {
    CtorSpec {
        name,
        tag,
        field_count: 0,
    }
}

/// Helper: data constructor spec with the given field count.
fn data_ctor(name: &'static str, tag: usize, field_count: usize) -> CtorSpec {
    CtorSpec {
        name,
        tag,
        field_count,
    }
}

/// Build a constructor `Def` entry under the ctor-as-Def shape.
/// `type_def` is `Some(..)` for a single-ctor product type (the ctor IS
/// its own type — S79 Option 3a dual facet), `None` for sum/enum ctors.
fn ctor_def_entry(
    type_fqtn: &FQTypeName,
    spec: &CtorSpec,
    type_def: Option<Box<TypeDefInfo>>,
) -> ModuleEntry {
    let scheme = Scheme {
        type_vars: vec![],
        constraints: std::collections::HashMap::new(),
        ty: Type::ADT(type_fqtn.clone(), vec![]),
    };
    ModuleEntry::Def {
        scheme,
        visibility: Visibility::Public,
        docstring: None,
        param_names: (0..spec.field_count)
            .map(|i| Symbol::from(format!("f{i}")))
            .collect(),
        kind: Box::new(DefKind::Constructor {
            got_slot: 0,
            type_name: type_fqtn.clone(),
            tag: spec.tag,
            field_count: spec.field_count,
            internal: false,
            type_def,
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

/// Build a DashMap with a single module, mirroring the production
/// registration shape (S79 Option 3a, `cranelisp-typecheck::adt`):
/// every constructor — sum, enum, OR product — is a got-slotted
/// `ModuleEntry::Def { kind: DefKind::Constructor { .. }, .. }`. For a
/// **product type** (single constructor whose name equals the type name)
/// that `Def` ALSO carries the type facet `type_def: Some(TypeDefInfo)`
/// and IS the `type_name` key — there is no separate `TypeDef` entry, and
/// the prior `constructor_scheme`-smuggling `TypeDef` is retired. For
/// sum/enum types each ctor `Def` is keyed distinctly and a separate
/// `ModuleEntry::TypeDef` is inserted under the type name.
fn tables_with_type(
    type_name: &str,
    type_params: &[&str],
    ctors: &[CtorSpec],
) -> dashmap::DashMap<ModuleFullPath, SymbolTable> {
    let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let mut st = SymbolTable::new(ModuleFullPath::from(TEST_MOD));
    let fqtn = test_fqtn(type_name);

    let info = TypeDefInfo {
        name: fqtn.clone(),
        type_params: type_params.iter().map(|s| Symbol::from(*s)).collect(),
        constructors: ctors.iter().map(|c| Symbol::from(c.name)).collect(),
    };

    let is_product = ctors.len() == 1 && ctors[0].name == type_name;

    // Insert ctor Defs. The product ctor carries its type facet and IS the
    // type-name key; sum/enum ctors carry `type_def: None`.
    for spec in ctors {
        let type_def = if is_product {
            Some(Box::new(info.clone()))
        } else {
            None
        };
        st.insert(
            Symbol::from(spec.name),
            ctor_def_entry(&fqtn, spec, type_def),
        );
    }

    // Sum/enum: a separate `TypeDef` entry under the type name. A product
    // type needs NONE — its got-slotted ctor `Def` already answers as the
    // type via its `type_def` facet.
    if !is_product {
        st.insert(
            Symbol::from(type_name),
            ModuleEntry::TypeDef {
                info,
                visibility: Visibility::Public,
                docstring: None,
            },
        );
    }
    tables.insert(ModuleFullPath::from(TEST_MOD), st);
    tables
}

// --- Primitive types (no tables needed) ---

// Build a concrete ADT `ConcreteType` from a test type name + concrete args.
fn cadt(name: &str, args: Vec<ConcreteType>) -> ConcreteType {
    ConcreteType::ADT(test_fqtn(name), args)
}

#[test]
fn test_primitives_never_heap() {
    assert_eq!(
        HeapCategory::classify::<(), ()>(&ConcreteType::Int, None),
        HeapCategory::NeverHeap
    );
    assert_eq!(
        HeapCategory::classify::<(), ()>(&ConcreteType::Bool, None),
        HeapCategory::NeverHeap
    );
    assert_eq!(
        HeapCategory::classify::<(), ()>(&ConcreteType::Float, None),
        HeapCategory::NeverHeap
    );
}

#[test]
fn test_string_always_heap() {
    assert_eq!(
        HeapCategory::classify::<(), ()>(&ConcreteType::String, None),
        HeapCategory::AlwaysHeap
    );
}

#[test]
fn test_fn_always_heap() {
    let fn_ty = ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int));
    assert_eq!(
        HeapCategory::classify::<(), ()>(&fn_ty, None),
        HeapCategory::AlwaysHeap
    );
}

// S84 Phase 3 (concrete-boundary-type.md §3.1, FIXME 0391). `classify` now
// takes a `ConcreteType` — there is NO `Var` and NO `TyConApp` variant, so
// the old `test_var_*` / `test_tyconapp_*` / `(Option Var)` / `(Vec Var)`
// backstop-deferred cases are **structurally inexpressible**: you cannot
// construct a `ConcreteType::Var` to hand to `classify` (the migration's
// whole proof — `cargo check` rejects `ConcreteType::Var(0)` at compile time).
// The four behavioural `Var`-guards collapsed to that one structural property;
// §3.11.1 ambiguity is caught upstream at typecheck + `MonoExpr::from_expr`,
// never at this seam.

// --- ADT without tables (conservative fallback) ---

#[test]
fn test_adt_without_tables_is_mixed() {
    let color = cadt("Color", vec![]);
    assert_eq!(
        HeapCategory::classify::<(), ()>(&color, None),
        HeapCategory::Mixed,
    );
}

#[test]
fn test_parameterized_adt_without_tables_is_mixed() {
    let option_int = cadt("Option", vec![ConcreteType::Int]);
    assert_eq!(
        HeapCategory::classify::<(), ()>(&option_int, None),
        HeapCategory::Mixed,
    );
}

// --- ADT with tables: enum-only (all nullary) ---

#[test]
fn test_enum_only_adt_never_heap() {
    // (deftype Color Red Green Blue)
    let tables = tables_with_type(
        "Color",
        &[],
        &[
            nullary_ctor("Red", 0),
            nullary_ctor("Green", 1),
            nullary_ctor("Blue", 2),
        ],
    );
    let color = cadt("Color", vec![]);
    assert_eq!(
        HeapCategory::classify(&color, Some(&tables)),
        HeapCategory::NeverHeap,
    );
}

// --- ADT with tables: all data constructors ---

#[test]
fn test_data_only_adt_always_heap() {
    // (deftype Wrapper [val]) — non-parameterized with data constructor
    // This is the F-2 bug case: was incorrectly NeverHeap
    let tables = tables_with_type("Wrapper", &[], &[data_ctor("Wrapper", 0, 1)]);
    let wrapper = cadt("Wrapper", vec![]);
    assert_eq!(
        HeapCategory::classify(&wrapper, Some(&tables)),
        HeapCategory::AlwaysHeap,
    );
}

#[test]
fn test_product_type_always_heap() {
    // (deftype IPoint (IPoint [:Int x :Int y])) — product type
    let tables = tables_with_type("IPoint", &[], &[data_ctor("IPoint", 0, 2)]);
    let point = cadt("IPoint", vec![]);
    assert_eq!(
        HeapCategory::classify(&point, Some(&tables)),
        HeapCategory::AlwaysHeap,
    );
}

// --- ADT with tables: mixed constructors ---

// regression: KEPT path (FIXME 0375/0379). A type-KNOWN `Mixed` ADT with NO
// free var (`is_representation_undetermined()` is FALSE) still classifies as
// `Mixed` and keeps its sound `<1024` nullary-tag discrimination guard — it
// must NOT be swept into the widened panic. This is the `(true,true)` ctor
// shape → `Mixed` → `emit_rc_*_guarded` chain that must stay intact.
#[test]
fn test_mixed_adt_with_tables() {
    // (deftype (Option a) None (Some [:a val]))
    let tables = tables_with_type(
        "Option",
        &["a"],
        &[nullary_ctor("None", 0), data_ctor("Some", 1, 1)],
    );
    let option_int = cadt("Option", vec![ConcreteType::Int]);
    assert_eq!(
        HeapCategory::classify(&option_int, Some(&tables)),
        HeapCategory::Mixed,
    );
}

// --- ADT with tables: parameterized but only nullary ---

#[test]
fn test_phantom_type_never_heap() {
    // (deftype (Phantom a) PhantomVal) — parameterized, but only nullary constructor
    // This was incorrectly Mixed with the old heuristic
    let tables = tables_with_type("Phantom", &["a"], &[nullary_ctor("PhantomVal", 0)]);
    let phantom = cadt("Phantom", vec![ConcreteType::Int]);
    assert_eq!(
        HeapCategory::classify(&phantom, Some(&tables)),
        HeapCategory::NeverHeap,
    );
}

// --- ADT with tables: unknown type (not in tables) ---

#[test]
fn test_unknown_adt_with_empty_tables_is_mixed() {
    let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let unknown = cadt("Unknown", vec![]);
    assert_eq!(
        HeapCategory::classify(&unknown, Some(&tables)),
        HeapCategory::Mixed,
    );
}

// --- Vec type (built-in, always heap) ---

#[test]
fn test_vec_always_heap_without_tables() {
    let vec_int = ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
        vec![ConcreteType::Int],
    );
    assert_eq!(
        HeapCategory::classify::<(), ()>(&vec_int, None),
        HeapCategory::AlwaysHeap,
    );
}

#[test]
fn test_vec_always_heap_with_tables() {
    let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let vec_str = ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
        vec![ConcreteType::String],
    );
    assert_eq!(
        HeapCategory::classify(&vec_str, Some(&tables)),
        HeapCategory::AlwaysHeap,
    );
}

// ---------------------------------------------------------------------------
// R5 value-flattening (II-B1) — the `HeapCategory::Value` arm.
//
// spec: design/backend/ownership-codegen.md §7.1/§7.2 — a Copy-eligible,
// single-constructor ADT whose fully-flattened payload is ≤ 1 word classifies
// `Value` (bare-word move, no header/RC). These fixtures build **faithful**
// constructor schemes (`Type::Fn(field_types, ADT)`) — unlike `tables_with_type`
// (which leaves `scheme.ty = ADT`), because `value_layout` reads the ctor's Fn
// scheme to recover field types. NOTE: these tests assume the process-global
// ownership toggle is ON (the default; `CRANELISP_NO_OWNERSHIP` unset) — the
// gate is `!ownership_analysis_off()`.
// ---------------------------------------------------------------------------

/// Insert a single-constructor **product** type with a faithful `Type::Fn`
/// constructor scheme (field types → ADT). Multiple calls compose into one
/// table so nested value types resolve.
fn insert_product_typed(st: &mut SymbolTable, type_name: &str, field_types: Vec<Type>) {
    let fqtn = test_fqtn(type_name);
    let info = TypeDefInfo {
        name: fqtn.clone(),
        type_params: vec![],
        constructors: vec![Symbol::from(type_name)],
    };
    let field_count = field_types.len();
    // Faithful ctor scheme: `field_types -> ADT` (a nullary product's scheme is
    // the ADT directly, matching production / `value_layout`'s reader).
    let scheme_ty = if field_count == 0 {
        Type::ADT(fqtn.clone(), vec![])
    } else {
        Type::Fn(field_types, Box::new(Type::ADT(fqtn.clone(), vec![])))
    };
    let entry = ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: scheme_ty,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: (0..field_count)
            .map(|i| Symbol::from(format!("f{i}")))
            .collect(),
        kind: Box::new(DefKind::Constructor {
            got_slot: 0,
            type_name: fqtn.clone(),
            tag: 0,
            field_count,
            internal: false,
            type_def: Some(Box::new(info)),
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    };
    st.insert(Symbol::from(type_name), entry);
}

fn product_tables(specs: &[(&str, Vec<Type>)]) -> dashmap::DashMap<ModuleFullPath, SymbolTable> {
    let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let mut st = SymbolTable::new(ModuleFullPath::from(TEST_MOD));
    for (name, fts) in specs {
        insert_product_typed(&mut st, name, fts.clone());
    }
    tables.insert(ModuleFullPath::from(TEST_MOD), st);
    tables
}

// Positive: one-word single-ctor scalar wrapper (the F2v `(Cell [:Int value])`
// shape) → Value.
#[test]
fn test_r5_scalar_wrapper_is_value() {
    let tables = product_tables(&[("Cell", vec![Type::Int])]);
    assert_eq!(
        HeapCategory::classify(&cadt("Cell", vec![]), Some(&tables)),
        HeapCategory::Value,
    );
}

// Positive: a nested single-field wrapper over a Value type composes to one word
// → still Value (nested values flatten transitively).
#[test]
fn test_r5_nested_value_wrapper_is_value() {
    let tables = product_tables(&[
        ("Cell", vec![Type::Int]),
        ("Outer", vec![Type::ADT(test_fqtn("Cell"), vec![])]),
    ]);
    assert_eq!(
        HeapCategory::classify(&cadt("Outer", vec![]), Some(&tables)),
        HeapCategory::Value,
    );
}

// Negative: a heap-typed field (String) is NOT Copy-eligible → stays AlwaysHeap.
#[test]
fn test_r5_heap_field_wrapper_stays_heap() {
    let tables = product_tables(&[("Boxed", vec![Type::String])]);
    assert_eq!(
        HeapCategory::classify(&cadt("Boxed", vec![]), Some(&tables)),
        HeapCategory::AlwaysHeap,
    );
}

// Negative: two scalar fields = 2 words > VALUE_LAYOUT_MAX_WORDS (1) → stays
// AlwaysHeap (the >1-word first-landing exclusion).
#[test]
fn test_r5_two_word_product_stays_heap() {
    let tables = product_tables(&[("Pair2", vec![Type::Int, Type::Int])]);
    assert_eq!(
        HeapCategory::classify(&cadt("Pair2", vec![]), Some(&tables)),
        HeapCategory::AlwaysHeap,
    );
}

// Negative: a multi-constructor ADT with scalar fields is NOT Value (a tag word
// is needed alongside the payload — excluded from the first landing). This is
// the F2 two-ctor `Cell` shape (the II-G4 honesty witness).
#[test]
fn test_r5_multi_ctor_scalar_not_value() {
    // (deftype Cell (Given [:Int value]) (Solved [:Int value])) — Mixed is
    // impossible (both data), so it classifies AlwaysHeap; the point is: NOT
    // Value.
    let tables = tables_with_type(
        "TwoCell",
        &[],
        &[data_ctor("Given", 0, 1), data_ctor("Solved", 1, 1)],
    );
    let cat = HeapCategory::classify(&cadt("TwoCell", vec![]), Some(&tables));
    assert_ne!(cat, HeapCategory::Value);
}

// Negative: a fieldless single-ctor product (0-word) is NOT flattened to Value —
// it has no payload; today's NeverHeap lowering (single nullary ctor) stands.
#[test]
fn test_r5_zero_word_product_not_value() {
    let tables = product_tables(&[("UnitLike", vec![])]);
    let cat = HeapCategory::classify(&cadt("UnitLike", vec![]), Some(&tables));
    assert_ne!(cat, HeapCategory::Value);
}

// Wave-3a /review BLOCKER 1 (0-word-but-≥1-field product) — the backend half of
// the divergence guard. `(P [:U u])`, U nullary (0 words): the backend MUST
// classify P as a real heap object (`AlwaysHeap`), NOT `Value` — matching
// typecheck's `Copy` verdict (both read `value_layout`, now `None` for P). If
// this ever regressed to `Value`, P would be bit-copied across a Copy edge with
// no `rc_inc` while its RC still governs a heap allocation → leak/UAF.
#[test]
fn test_r5_zero_word_field_product_not_value() {
    let tables = product_tables(&[
        ("U", vec![]),
        ("P", vec![Type::ADT(test_fqtn("U"), vec![])]),
    ]);
    let cat = HeapCategory::classify(&cadt("P", vec![]), Some(&tables));
    assert_ne!(
        cat,
        HeapCategory::Value,
        "0-word-field product must not flatten"
    );
    assert_eq!(
        cat,
        HeapCategory::AlwaysHeap,
        "P is a real heap object (RC-governed)"
    );
}

// Wave-3a /review BLOCKER 2 (multi-field-but-≤1-word) — the backend half.
// `(M [:Int x :U u])` = 1 word across 2 fields: MUST classify heap, NOT `Value`.
// A `Value` verdict here would split construction (2-field heap) from match
// (flat single-word bind) → garbage pointer.
#[test]
fn test_r5_multi_field_one_word_product_not_value() {
    let tables = product_tables(&[
        ("U", vec![]),
        ("M", vec![Type::Int, Type::ADT(test_fqtn("U"), vec![])]),
    ]);
    let cat = HeapCategory::classify(&cadt("M", vec![]), Some(&tables));
    assert_ne!(
        cat,
        HeapCategory::Value,
        "≥2-field product must not flatten"
    );
    assert_eq!(cat, HeapCategory::AlwaysHeap);
}
