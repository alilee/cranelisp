use super::*;
use crate::cache::linker::Linker;
use cranelisp_types::{ModuleFullPath, SymbolTable};

/// Helper: write a fresh-build SymbolTable to the cache path using the
/// authoritative API (`write_meta` + `CACHE_SCHEMA_VERSION`). Replaces
/// the pre-§14 `make_test_metadata` + `write_cached_metadata` pattern
/// inside this test module.
fn write_test_table(meta_path: &std::path::Path, module_path: &str) {
    let mp = ModuleFullPath::from(module_path);
    let table = SymbolTable::new(mp);
    serialize::write_meta(meta_path, &table, CACHE_SCHEMA_VERSION).unwrap();
}

// spec: design/backend/module-caching.md §8 — cache load returns metadata
#[test]
fn test_try_load_cached_module_success() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("user");

    // Write a fresh-build SymbolTable to the expected path.
    let (meta_path, _) = module_cache_path(dir.path(), &mp);
    write_test_table(&meta_path, "user");

    // Load it back via the back-compat wrapper.
    let result = try_load_cached_module(dir.path(), &mp).unwrap();
    assert!(result.is_some());
    let cached = result.unwrap();
    assert_eq!(cached.symbol_table().path, mp);
    assert!(!cached.has_object); // No .o file written
}

// spec: design/backend/module-caching.md §8 — missing .meta.json returns None
#[test]
fn test_try_load_cached_module_missing() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("nonexistent");
    let result = try_load_cached_module(dir.path(), &mp).unwrap();
    assert!(result.is_none());
}

// spec: design/backend/module-caching.md §8 — corrupt .meta.json returns None
#[test]
fn test_try_load_cached_module_corrupt() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("user");
    let (meta_path, _) = module_cache_path(dir.path(), &mp);
    atomic_write(&meta_path, b"not valid json").unwrap();

    let result = try_load_cached_module(dir.path(), &mp).unwrap();
    assert!(result.is_none());
}

// spec: design/backend/module-caching.md §8 — module path mismatch returns None
#[test]
fn test_try_load_cached_module_path_mismatch() {
    let dir = tempfile::tempdir().unwrap();
    // Write a SymbolTable with module path "other" at the cache slot
    // expected by module path "user" — defence against file mix-ups.
    let mp_user = ModuleFullPath::from("user");
    let (meta_path, _) = module_cache_path(dir.path(), &mp_user);
    write_test_table(&meta_path, "other");

    let result = try_load_cached_module(dir.path(), &mp_user).unwrap();
    assert!(result.is_none());
}

// spec: design/backend/module-caching.md §8 — nested module cache load
#[test]
fn test_try_load_cached_module_nested() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("core.numerics");

    let (meta_path, _) = module_cache_path(dir.path(), &mp);
    write_test_table(&meta_path, "core.numerics");

    let result = try_load_cached_module(dir.path(), &mp).unwrap();
    assert!(result.is_some());
    let cached = result.unwrap();
    assert_eq!(cached.symbol_table().path, mp);
}

// spec: design/backend/module-caching.md §8 — has_object detects real .o file
#[test]
fn test_try_load_cached_module_with_object() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("user");

    let (meta_path, object_path) = module_cache_path(dir.path(), &mp);
    write_test_table(&meta_path, "user");
    // Write a non-empty .o file
    atomic_write(&object_path, b"fake object data").unwrap();

    let result = try_load_cached_module(dir.path(), &mp).unwrap();
    assert!(result.is_some());
    let cached = result.unwrap();
    assert!(cached.has_object);
}

// spec: design/backend/module-caching.md §8 — empty .o file treated as no object
#[test]
fn test_try_load_cached_module_empty_object() {
    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("user");

    let (meta_path, object_path) = module_cache_path(dir.path(), &mp);
    write_test_table(&meta_path, "user");
    // Write empty .o
    atomic_write(&object_path, b"").unwrap();

    let result = try_load_cached_module(dir.path(), &mp).unwrap();
    assert!(result.is_some());
    let cached = result.unwrap();
    assert!(!cached.has_object); // Empty .o is not valid
}

// spec: spec/08-modules.md — module path to filesystem mapping
#[test]
fn test_module_dir_and_stem_simple() {
    let mp = ModuleFullPath::from("user");
    let (dir, stem) = module_dir_and_stem(&mp);
    assert_eq!(dir, "");
    assert_eq!(stem, "user");
}

// spec: spec/08-modules.md — nested module path to filesystem mapping
#[test]
fn test_module_dir_and_stem_nested() {
    let mp = ModuleFullPath::from("core.numerics");
    let (dir, stem) = module_dir_and_stem(&mp);
    assert_eq!(dir, "core");
    assert_eq!(stem, "numerics");
}

// spec: spec/08-modules.md — deeply nested module path
#[test]
fn test_module_dir_and_stem_deep() {
    let mp = ModuleFullPath::from("core.collections.list");
    let (dir, stem) = module_dir_and_stem(&mp);
    assert_eq!(dir, "core/collections");
    assert_eq!(stem, "list");
}

// spec: spec/08-modules.md — root/entry module
#[test]
fn test_module_dir_and_stem_root() {
    let mp = ModuleFullPath::from("_root");
    let (dir, stem) = module_dir_and_stem(&mp);
    assert_eq!(dir, "");
    assert_eq!(stem, "_entry");
}

// spec: design/backend/module-caching.md §10 — cache path generation
#[test]
fn test_module_cache_path() {
    let cache_dir = std::path::Path::new("/tmp/.cranelisp-cache");
    let mp = ModuleFullPath::from("core.numerics");
    let (meta, obj) = module_cache_path(cache_dir, &mp);
    assert_eq!(
        meta,
        std::path::PathBuf::from("/tmp/.cranelisp-cache/core/numerics.meta.json")
    );
    assert_eq!(
        obj,
        std::path::PathBuf::from("/tmp/.cranelisp-cache/core/numerics.o")
    );
}

// spec: design/backend/module-caching.md §10 — atomic write correctness
#[test]
fn test_atomic_write() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test.txt");
    atomic_write(&path, b"hello").unwrap();
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "hello");
    // Overwrite
    atomic_write(&path, b"world").unwrap();
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "world");
}

// spec: design/backend/module-caching.md §10 — atomic write creates parent dirs
#[test]
fn test_atomic_write_creates_parents() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("a/b/c/test.txt");
    atomic_write(&path, b"nested").unwrap();
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "nested");
}

// spec: design/backend/module-caching.md §13 — end-to-end: compile .o, load via linker, execute
#[test]
fn test_compile_load_and_execute_cached_module() {
    use cranelisp_types::{DefKind, Defn, DefnVariant, Expr, ModuleEntry, ModuleFullPath, Scheme, Span, Symbol,
        SymbolTable, Type, UserFnState, Visibility,
    };
    use cranelift_module::default_libcall_names;
    use cranelift_object::{ObjectBuilder, ObjectModule};

    // Step 1: Create a minimal module with (defn answer [] 42)
    let defn = Defn {
        name: Symbol::from("answer"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 42,
                span: Span::new(10, 12),
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    // Wave 0 contract: backend reads the AST from the symbol table.
    let module = ModuleFullPath::from("user");
    let tables = dashmap::DashMap::new();
    let mut st = SymbolTable::new(module.clone());
    st.insert(
        defn.name.clone(),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: Default::default(),
                ty: Type::Fn(vec![], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::NotDetermined,
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: defn.variants.first().cloned(),
            // W0.b: every codegen-reached body carries a typecheck-populated view
            // (KC-W0-6 fixture obligation; the backend hard-errors on None).
            codegen_view: Some(crate::test_support::test_codegen_view(
                &defn.name,
                defn.variants.first().unwrap(),
                &Default::default(),
            )),
            code: None,
            value_use: false,
        },
    );
    tables.insert(module.clone(), st);

    // Step 2: Compile to .o bytes via compile_to_module<ObjectModule>
    let isa = super::object::build_isa(true).unwrap();
    let obj_builder = ObjectBuilder::new(isa, "test", default_libcall_names()).unwrap();
    let mut obj_module = ObjectModule::new(obj_builder);

    let aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
    crate::compile_to_module(
        module,
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        &mut obj_module,
        false,
    ).unwrap();

    let product = obj_module.finish();
    let obj_bytes = product.emit().unwrap();
    assert!(!obj_bytes.is_empty());

    // Step 3: Load via linker
    let mut linker = Linker::new().unwrap();
    linker.load_object("test", &obj_bytes).unwrap();

    // Step 4: Get function pointer and execute it
    let answer_ptr = linker.get_symbol("answer").expect("should find 'answer' symbol");
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(answer_ptr) };
    let result = func();
    assert_eq!(result, 42, "cached function should return 42");
}

// spec: design/backend/module-caching.md §8 — imported_modules extracts dep paths
#[test]
fn test_imported_modules_extracts_deps() {
    use cranelisp_types::{FQSymbol, ModuleEntry, Scheme, Symbol, Type};

    let dir = tempfile::tempdir().unwrap();
    let mp = ModuleFullPath::from("main.mid");
    let mut table = SymbolTable::new(mp.clone());

    // Add an Import entry from main.mid.leaf
    table.insert(
        Symbol::from("base-val"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("main.mid.leaf"),
                symbol: Symbol::from("base-val"),
            },
            visibility: cranelisp_types::Visibility::Private,
        },
    );

    // Add a Def entry (should NOT appear in imported_modules)
    table.insert(
        Symbol::from("relay"),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Fn(vec![], Box::new(Type::Int)),
            },
            visibility: cranelisp_types::Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(cranelisp_types::DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );

    // Add an Import from primitives (should be excluded)
    table.insert(
        Symbol::from("add-i64"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("add-i64"),
            },
            visibility: cranelisp_types::Visibility::Private,
        },
    );

    let metadata = serialize::CacheMetadata {
        symbol_table: table,
        dependencies: Vec::new(),
    };
    let cached = CachedModule {
        metadata,
        meta_path: dir.path().join("test.meta.json"),
        object_path: dir.path().join("test.o"),
        has_object: false,
    };

    let imported = cached.imported_modules();
    assert_eq!(imported.len(), 1);
    assert!(imported.contains(&ModuleFullPath::from("main.mid.leaf")));
}
