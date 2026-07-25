use super::*;
use cranelisp_types::{ModuleFullPath, SymbolTable};

// spec: design/backend/module-caching.md §5 — build_isa with PIC produces valid ISA
#[test]
fn test_build_isa_pic() {
    let isa = build_isa(true).unwrap();
    assert!(!isa.triple().to_string().is_empty());
}

// spec: design/backend/module-caching.md §5 — build_isa without PIC produces valid ISA
#[test]
fn test_build_isa_non_pic() {
    let isa = build_isa(false).unwrap();
    assert!(!isa.triple().to_string().is_empty());
}

// spec: design/backend/module-caching.md §7 — IntrinsicTable construction
#[test]
fn test_intrinsic_table_default() {
    let table = IntrinsicTable::new();
    assert!(table.runtime_fns.is_empty());
    assert!(table.primitive_fns.is_empty());
    assert!(table.platform_fns.is_empty());
    assert!(table.global_names.is_empty());
}

// spec: design/backend/module-caching.md §7 — build_cache_packet creates valid packet
#[test]
fn test_build_cache_packet() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("test.module");
    let symbol_table = SymbolTable::new(mp.clone());
    let input = ObjectCompileInput {
        module_path: mp.clone(),
        defns: vec![],
        method_resolutions: cranelisp_types::MethodResolutions::new(),
        fn_slot_assignments: HashMap::new(),
        fn_to_module: HashMap::new(),
        intrinsics: IntrinsicTable::new(),
        expr_types: HashMap::new(),
        next_got_slot: 0,
        cross_module_fns: vec![],
    };

    let packet = build_cache_packet(
        dir.path(),
        &mp,
        "abc123",
        false,
        HashMap::new(),
        &symbol_table,
        input,
    )
    .unwrap();

    assert_eq!(packet.module_path, mp);
    assert_eq!(packet.source_hash, "abc123");
    assert!(!packet.meta_json_bytes.is_empty());
    assert!(
        packet
            .meta_path
            .to_str()
            .unwrap()
            .contains("module.meta.json")
    );
    assert!(packet.object_path.to_str().unwrap().contains("module.o"));
}

// spec: design/backend/module-caching.md §7 — process_cache_packet writes files
#[test]
fn test_process_cache_packet() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("user");
    let symbol_table = SymbolTable::new(mp.clone());
    let input = ObjectCompileInput {
        module_path: mp.clone(),
        defns: vec![],
        method_resolutions: cranelisp_types::MethodResolutions::new(),
        fn_slot_assignments: HashMap::new(),
        fn_to_module: HashMap::new(),
        intrinsics: IntrinsicTable::new(),
        expr_types: HashMap::new(),
        next_got_slot: 0,
        cross_module_fns: vec![],
    };

    let packet = build_cache_packet(
        dir.path(),
        &mp,
        "hash123",
        false,
        HashMap::new(),
        &symbol_table,
        input,
    )
    .unwrap();

    let result = process_cache_packet(&packet, &dashmap::DashMap::new()).unwrap();
    assert_eq!(result.module_path, mp);
    assert_eq!(result.source_hash, "hash123");

    // Verify .meta.json was written
    assert!(packet.meta_path.exists());
}

// spec: design/backend/module-caching.md §13.4 — GOT data symbol naming
#[test]
fn test_got_data_symbol_name() {
    // Canonical home is `crate::compiler::got_data_symbol_name` (S75 W3 —
    // the cache re-export collapsed to a single `pub(crate)` home).
    use crate::compiler::got_data_symbol_name;
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("user")),
        "__cranelisp_got_user"
    );
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("core.numerics")),
        "__cranelisp_got_core_numerics"
    );
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("")),
        "__cranelisp_got__entry"
    );
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("prelude")),
        "__cranelisp_got_prelude"
    );
}

/// Helper: create an ObjectModule for testing.
fn test_object_module() -> ObjectModule {
    use cranelift_module::default_libcall_names;
    use cranelift_object::ObjectBuilder;

    let isa = build_isa(true).unwrap();
    let builder = ObjectBuilder::new(isa, "test", default_libcall_names()).unwrap();
    ObjectModule::new(builder)
}

// Helper: build a SymbolTable containing `defn` as a `ModuleEntry::Def`
// with `ast: Some(defn)`. Mirrors the Wave 0 contract for these tests —
// the backend reads the AST body from the symbol table, never a Program.
fn table_with_def(
    module: &ModuleFullPath,
    defn: cranelisp_types::Defn,
    scheme: cranelisp_types::Scheme,
) -> dashmap::DashMap<ModuleFullPath, SymbolTable> {
    use cranelisp_types::{
        DefKind, ModuleEntry, MonoDefnVariant, MonoExpr, UserFnState, Visibility,
    };
    let tables = dashmap::DashMap::new();
    let mut st = SymbolTable::new(module.clone());
    let name = defn.name.clone();
    let param_names: Vec<Symbol> = defn
        .variants
        .first()
        .map(|v| v.params.iter().map(|(n, _)| n.clone()).collect())
        .unwrap_or_default();
    let variant = defn.variants.first().cloned();
    // S84 Phase 3 (FIXME 0391): a `Concrete{slot}` UserFn codegen target
    // carries a populated `codegen_view` (the `MonoExpr` body, every node
    // `ConcreteType`-typed). Build it from the concretely-annotated `ast`
    // body the fixtures supply.
    let codegen_view = variant.as_ref().map(|v| {
        let (var_refs, apply_refs) = crate::test_support::resolved_targets_to_typed_maps(
            &v.body,
            &std::collections::HashMap::new(),
        );
        let body = MonoExpr::from_expr(
            &v.body,
            &std::collections::HashMap::new(),
            &var_refs,
            &apply_refs,
        )
        .expect("test fixture body must be concretely typed for the codegen view");
        MonoDefnVariant {
            name: name.clone(),
            params: v.params.iter().map(|(n, _)| n.clone()).collect(),
            body,
            span: v.span,
            mode_summary: None,
        }
    });
    st.insert(
        name,
        ModuleEntry::Def {
            scheme,
            visibility: Visibility::Public,
            docstring: None,
            param_names,
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete {
                    got_slot: 0,
                    mode_summary: None,
                },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: variant,
            codegen_view,
            code: None,
            value_use: false,
        },
    );
    tables.insert(module.clone(), st);
    tables
}

// spec: design/backend/module-caching.md §13.2 — compile simple module to .o
#[test]
fn test_compile_module_to_object_simple() {
    use cranelisp_types::{Defn, DefnVariant, Expr, Scheme, Visibility};

    let defn = Defn {
        name: Symbol::from("answer"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 42,
                span: Span::new(10, 12),
                inferred_type: Some(Box::new(cranelisp_types::Type::Int)),
            },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let module = ModuleFullPath::from("user");
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: cranelisp_types::Type::Fn(vec![], Box::new(cranelisp_types::Type::Int)),
    };
    let tables = table_with_def(&module, defn.clone(), scheme);

    let mut obj_module = test_object_module();
    let _result = crate::compile_to_module(
        module,
        std::slice::from_ref(&defn.name),
        &tables,
        &mut obj_module,
        false,
    )
    .unwrap();

    let product = obj_module.finish();
    let bytes = product.emit().unwrap();
    assert!(!bytes.is_empty(), "object file should not be empty");

    // Verify it is a valid object file by parsing with the `object` crate
    use ::object::{Object, ObjectSymbol};
    let obj = ::object::File::parse(&*bytes).expect("should be parseable as object file");

    // Verify we have a text section
    let text = obj
        .section_by_name("__text")
        .or_else(|| obj.section_by_name(".text"));
    assert!(text.is_some(), "should have a text section");

    // Verify the function symbol is exported
    let has_answer = obj.symbols().any(|sym| {
        sym.name()
            .map(|n| n.strip_prefix('_').unwrap_or(n) == "answer")
            .unwrap_or(false)
    });
    assert!(has_answer, "should export 'answer' symbol");
}

// spec: design/backend/module-caching.md §13.2 — compile module with params
#[test]
fn test_compile_module_to_object_with_params() {
    use cranelisp_types::{Defn, DefnVariant, Expr, Scheme, Visibility};

    let defn = Defn {
        name: Symbol::from("identity"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(20, 21),
                resolved_call: None,
                inferred_type: Some(Box::new(cranelisp_types::Type::Int)),
            },
            span: Span::new(0, 25),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 25),
    };

    let module = ModuleFullPath::from("user");
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: cranelisp_types::Type::Fn(
            vec![cranelisp_types::Type::Int],
            Box::new(cranelisp_types::Type::Int),
        ),
    };
    let tables = table_with_def(&module, defn.clone(), scheme);

    let mut obj_module = test_object_module();
    let _result = crate::compile_to_module(
        module,
        std::slice::from_ref(&defn.name),
        &tables,
        &mut obj_module,
        false,
    )
    .unwrap();

    let product = obj_module.finish();
    let bytes = product.emit().unwrap();
    assert!(!bytes.is_empty());

    // Verify parseable
    let _obj = ::object::File::parse(&*bytes).expect("should parse");
}

// spec: design/backend/module-caching.md §13 — process_cache_packet writes .o file
#[test]
fn test_process_cache_packet_writes_object_file() {
    use cranelisp_types::{Defn, DefnVariant, Expr, Scheme, Visibility};

    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("user");
    let symbol_table = SymbolTable::new(mp.clone());

    let defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 0,
                span: Span::new(10, 11),
                inferred_type: Some(Box::new(cranelisp_types::Type::Int)),
            },
            span: Span::new(0, 15),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 15),
    };
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: cranelisp_types::Type::Fn(vec![], Box::new(cranelisp_types::Type::Int)),
    };

    let input = ObjectCompileInput {
        module_path: mp.clone(),
        defns: vec![(defn.clone(), scheme.clone())],
        method_resolutions: cranelisp_types::MethodResolutions::new(),
        fn_slot_assignments: HashMap::new(),
        fn_to_module: HashMap::new(),
        intrinsics: IntrinsicTable::new(),
        expr_types: HashMap::new(),
        next_got_slot: 0,
        cross_module_fns: vec![],
    };

    let packet = build_cache_packet(
        dir.path(),
        &mp,
        "hash456",
        false,
        HashMap::new(),
        &symbol_table,
        input,
    )
    .unwrap();

    // Post-Phase-2: process_cache_packet reads AST bodies from the symbol
    // tables via compile_to_module's name-list interface.
    let tables = table_with_def(&mp, defn, scheme);
    let result = process_cache_packet(&packet, &tables).unwrap();
    assert_eq!(result.source_hash, "hash456");

    // Both .meta.json and .o should exist
    assert!(packet.meta_path.exists(), ".meta.json should exist");
    assert!(packet.object_path.exists(), ".o file should exist");

    // The .o file should be non-empty and parseable
    let obj_bytes = std::fs::read(&packet.object_path).unwrap();
    assert!(!obj_bytes.is_empty());
    let _obj = ::object::File::parse(&*obj_bytes).expect("should be valid object file");
}

// spec: design/backend/module-caching.md §13.6 — empty defns skip .o generation
#[test]
fn test_process_cache_packet_no_object_for_empty_defns() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("types_only");
    let symbol_table = SymbolTable::new(mp.clone());
    let input = ObjectCompileInput {
        module_path: mp.clone(),
        defns: vec![], // No functions
        method_resolutions: cranelisp_types::MethodResolutions::new(),
        fn_slot_assignments: HashMap::new(),
        fn_to_module: HashMap::new(),
        intrinsics: IntrinsicTable::new(),
        expr_types: HashMap::new(),
        next_got_slot: 0,
        cross_module_fns: vec![],
    };

    let packet = build_cache_packet(
        dir.path(),
        &mp,
        "empty",
        false,
        HashMap::new(),
        &symbol_table,
        input,
    )
    .unwrap();

    let _result = process_cache_packet(&packet, &dashmap::DashMap::new()).unwrap();

    // .meta.json should exist, but .o should NOT
    assert!(packet.meta_path.exists());
    assert!(!packet.object_path.exists(), "no .o for empty defns");
}
