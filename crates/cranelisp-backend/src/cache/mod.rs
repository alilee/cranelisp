use cranelisp_types::ErrorLocation;
// Module caching: persist compiled module metadata and object files to disk.
//
// Layout:
//   .cranelisp-cache/
//     manifest.json           # version, target triple, module hashes
//     <module>.meta.json      # serialized SymbolTable (includes GOT slot assignments)
//     <module>.o              # relocatable object file
//
// See design/backend/module-caching.md for the full design.

pub mod manifest;
pub mod serialize;
pub mod object;
pub mod linker;

pub use manifest::{
    CacheManifest, CachedModuleRef, CacheInvalidReason, check_manifest, hash_source,
    read_manifest, write_manifest, binary_fingerprint,
};
// Authoritative cache API (Sprint 58 Step 5b — `module-caching.md` §14):
// `.meta.json` IS a serialised `SymbolTable`; `CacheStale` is the
// failure-mode discriminator caller logs / branches on.
pub use serialize::{
    deserialise_meta, load_meta, serialise_meta, write_meta, CacheStale,
};
// Deprecated shims — present so `/int`-owned (`src/session_v4.rs`) and
// `/qa`-owned (`tests/cache.rs`) call sites continue to compile during the
// Wave 2b parallel migration. Migrate to the authoritative API above.
#[allow(deprecated)]
pub use serialize::{CacheMetadata, read_cached_metadata, write_cached_metadata};
pub use object::{
    ObjectCompileInput, IntrinsicTable, IntrinsicEntry,
    CacheWritePacket, build_cache_packet, process_cache_packet,
    got_data_symbol_name,
};
pub use linker::Linker;

/// Cache schema version (Decision 34, Sprint 58 §14.2).
///
/// Stamped onto `SymbolTable.schema_version` at cache-write time. Cache-load
/// peeks the field first; mismatch returns `CacheStale::SchemaMismatch` and
/// the caller falls through to a fresh build (same code path as dep-hash
/// mismatch).
///
/// Bump on:
/// * field deletions on `SymbolTable` / any `ModuleEntry` variant,
/// * field type changes (deserialise<New> would fail on persisted Old),
/// * enum variant additions to a serde-tagged enum used inside `SymbolTable`,
/// * variant renames.
///
/// Field additions with `#[serde(default)]` whose default matches a fresh-build
/// value do NOT require a bump.
pub const CACHE_SCHEMA_VERSION: u32 = 1;

/// Compile-time build identifier (Sprint 60 Workstream C).
///
/// Emitted by `build.rs` as `<pkg_version>+<git_sha>` (e.g. `0.1.0+3b2df720fe63`),
/// stamped onto `.meta.json` next to `schema_version`, and compared on cache-load.
/// Mismatch routes through the same `CacheStale` fall-through as a schema-version
/// bump or a source-mtime change.
///
/// **This is an ADDITIONAL cache-invalidation trigger, not a substitute for the
/// manual `CACHE_SCHEMA_VERSION` bump that Decision 34 requires on explicit
/// serialised-shape changes.** The build-id catches the "I rebuilt the compiler
/// and forgot the cache was keyed on the old shape" class of mystery; it does
/// NOT replace the discipline of bumping `CACHE_SCHEMA_VERSION` whenever a
/// `SymbolTable` / `ModuleEntry` field is deleted, retyped, or renamed. Both
/// triggers coexist: shape changes that also rebuild the compiler hit the
/// build-id gate first; shape changes that land without a compiler-side rebuild
/// (cross-branch cache reuse) are caught only by the schema-version gate.
///
/// Pre-Sprint-60 `.meta.json` files lack the `build_id` field; they deserialise
/// with the `#[serde(default)]` empty string, which never matches a non-empty
/// `BUILD_ID` and routes through the same fall-through path.
pub const BUILD_ID: &str = env!("CRANELISP_BUILD_ID");

/// **SUPERSEDED (Sprint 58 §14.2)**: renamed to `CACHE_SCHEMA_VERSION` so
/// `/int`'s `symbol-table-cache.md` and Decision 34 use one term. The semantic
/// is unchanged. Kept as an alias so `tests/cache.rs` (owned by `/qa`)
/// continues to compile during the Wave 2b parallel migration. Doc-only
/// deprecation: a `#[deprecated]` attribute would surface warnings inside
/// files this crate is forbidden to edit.
pub const CACHE_FORMAT_VERSION: u32 = CACHE_SCHEMA_VERSION;

/// Compute the cache directory path for module files.
///
/// Module hierarchy maps to filesystem directories:
///   `core.numerics` -> `core/numerics.{meta.json,o}`
///   `user` -> `user.{meta.json,o}`
///   entry module -> `_entry.{meta.json,o}`
pub fn module_cache_path(
    cache_dir: &std::path::Path,
    module_path: &cranelisp_types::ModuleFullPath,
) -> (std::path::PathBuf, std::path::PathBuf) {
    let (dir, stem) = module_dir_and_stem(module_path);
    let base = if dir.is_empty() {
        cache_dir.to_path_buf()
    } else {
        cache_dir.join(dir)
    };
    (
        base.join(format!("{stem}.meta.json")),
        base.join(format!("{stem}.o")),
    )
}

/// Split a module path into (directory, stem) components.
/// `core.numerics` -> ("core", "numerics")
/// `user` -> ("", "user")
/// Root/entry -> ("", "_entry")
fn module_dir_and_stem(module_path: &cranelisp_types::ModuleFullPath) -> (String, String) {
    let path_str = module_path.0.as_str();
    if path_str.is_empty() || path_str == "_root" || path_str == "_entry" {
        return (String::new(), "_entry".to_string());
    }
    if let Some(dot_pos) = path_str.rfind('.') {
        let dir = path_str[..dot_pos].replace('.', "/");
        let stem = path_str[dot_pos + 1..].to_string();
        (dir, stem)
    } else {
        (String::new(), path_str.to_string())
    }
}

/// Result of loading a cached module from disk.
///
/// Contains all the metadata needed to restore a module into the compilation
/// session without re-parsing, expanding macros, or type-checking. The `/int`
/// pipeline installs these into the TypeChecker and codegen state.
///
/// **Sprint 22 scope**: Metadata-only cache. On cache hit, the symbol table
/// and module structure are restored from `.meta.json`, allowing downstream
/// modules to typecheck against this module's exports. Codegen is still
/// re-done from source (fast compared to full pipeline). Full `.o` loading
/// via the Linker is deferred to a future sprint.
#[derive(Debug, Clone)]
#[allow(deprecated)]
pub struct CachedModule {
    /// The deserialized module metadata (symbol table, structure, codegen state).
    ///
    /// **Note (Sprint 58 §14.4)**: this field still typed as `CacheMetadata`
    /// for back-compat during Wave 2b. New callers should consume
    /// `cached.symbol_table()` directly and ignore the envelope. The envelope
    /// dissolves when the `/int` worker migrates to the `load_meta` API.
    pub metadata: serialize::CacheMetadata,
    /// Path to the `.meta.json` file (for diagnostics).
    pub meta_path: std::path::PathBuf,
    /// Path to the `.o` file (may not exist yet in metadata-only mode).
    pub object_path: std::path::PathBuf,
    /// Whether a valid `.o` file exists on disk.
    pub has_object: bool,
}

#[allow(deprecated)]
impl CachedModule {
    /// Get the restored symbol table.
    pub fn symbol_table(&self) -> &cranelisp_types::SymbolTable {
        &self.metadata.symbol_table
    }

    /// Extract the set of module paths this cached module imports from.
    ///
    /// Scans Import entries in the symbol table and collects the unique
    /// source module paths. The orchestration layer uses this to
    /// recursively load transitive dependencies from cache.
    ///
    /// Excludes `primitives` and `macros` (synthetic compiler modules)
    /// since they are always available without cache loading.
    pub fn imported_modules(&self) -> std::collections::HashSet<cranelisp_types::ModuleFullPath> {
        let mut modules = std::collections::HashSet::new();
        for (_name, entry) in self.metadata.symbol_table.all_symbols() {
            if let cranelisp_types::ModuleEntry::Import { source } = entry {
                let mod_path = &source.module;
                // Skip synthetic compiler modules.
                if mod_path.as_ref() != "primitives" && mod_path.as_ref() != "macros" {
                    modules.insert(mod_path.clone());
                }
            }
        }
        modules
    }
}

/// Attempt to load a cached module from disk.
///
/// Returns `Ok(Some(CachedModule))` if the `.meta.json` exists and is valid.
/// Returns `Ok(None)` if the cache files are missing or corrupt (cache miss).
/// Returns `Err` only on unexpected I/O errors.
///
/// The caller (pipeline) is responsible for:
/// 1. Checking the manifest first via `check_manifest()` to confirm the
///    module's source hash is current.
/// 2. Installing the returned `CachedModule` into the TypeChecker.
/// 3. Deciding whether to skip codegen (if `.o` exists) or recompile
///    (metadata-only mode).
///
/// **Cache-load/fresh-compile equivalence invariant**: The deserialized
/// `SymbolTable` must have the same entries as a freshly typechecked module.
/// This is enforced structurally: both paths feed the same
/// `install_module_scope()` function in the pipeline.
#[allow(deprecated)]
pub fn try_load_cached_module(
    cache_dir: &std::path::Path,
    module_path: &cranelisp_types::ModuleFullPath,
) -> Result<Option<CachedModule>, cranelisp_types::CranelispError> {
    let (meta_path, object_path) = module_cache_path(cache_dir, module_path);

    // Use the authoritative `load_meta` API; treat any `CacheStale` variant
    // as a cache miss (§14.7 — every variant maps to "fall through to fresh
    // build" caller-side).
    let symbol_table = match serialize::load_meta(&meta_path) {
        Ok(t) => t,
        Err(_stale) => return Ok(None),
    };

    // Validate the module path matches (defense against file mix-ups)
    if symbol_table.path != *module_path {
        return Ok(None);
    }

    // Check for .o file existence (for future full-cache-hit path)
    let has_object = object_path.exists()
        && std::fs::metadata(&object_path)
            .map(|m| m.len() > 0)
            .unwrap_or(false);

    // Wrap the symbol table back into the deprecated `CacheMetadata` envelope
    // for back-compat with the `CachedModule { metadata }` field shape. Once
    // `/int` migrates `try_cache_hit_load` to consume `SymbolTable` directly,
    // this wrapper goes away with `CacheMetadata` itself.
    let metadata = serialize::CacheMetadata {
        symbol_table,
        dependencies: Vec::new(),
    };

    Ok(Some(CachedModule {
        metadata,
        meta_path,
        object_path,
        has_object,
    }))
}

/// Load a cached module's `.o` file into the linker and return function addresses.
///
/// This is the entry point for `/int` to use on cache hit with `has_object: true`.
/// It reads the `.o` file, loads it into the linker (resolving relocations against
/// registered symbols), and returns a map of function name → code pointer for
/// wiring into the live GOT.
///
/// **Prerequisites** (the caller must ensure before calling):
/// 1. All external symbols the `.o` references are registered with the linker:
///    - Runtime intrinsics (`linker.register_symbol("runtime/alloc", ptr)`)
///    - Functions from already-loaded modules (topo order guarantees this)
///    - GOT base pointers for already-compiled modules
/// 2. The `CachedModule` was loaded via `try_load_cached_module()` and
///    `has_object` is `true`.
///
/// **After calling**, the caller should wire the returned function pointers
/// into the live GOT using the slot assignments from `cached.codegen_state().got_slots`.
///
/// Returns a map of function name → code pointer (`*const u8`).
#[allow(deprecated)]
pub fn load_cached_object(
    linker: &mut linker::Linker,
    cached: &CachedModule,
) -> Result<std::collections::HashMap<String, *const u8>, cranelisp_types::CranelispError> {
    let obj_bytes = std::fs::read(&cached.object_path).map_err(|e| {
        cranelisp_types::CranelispError::CodegenError {
            message: format!(
                "failed to read cached object file '{}': {e}",
                cached.object_path.display()
            ),
            location: ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
        }
    })?;

    let module_name = cached.metadata.symbol_table.path.as_ref().to_string();
    linker.load_object(&module_name, &obj_bytes)?;

    // Collect function addresses from the linker's defined_symbols.
    // Function names with GOT slots are on ModuleEntry::Def in the symbol table.
    let mut fn_addrs = std::collections::HashMap::new();
    for (name, entry) in cached.symbol_table().all_symbols() {
        if matches!(entry, cranelisp_types::ModuleEntry::Def { got_slot: Some(_), .. })
            && let Some(addr) = linker.get_symbol(name.as_ref())
        {
            fn_addrs.insert(name.as_ref().to_string(), addr);
        }
    }

    Ok(fn_addrs)
}

/// Atomic file write: write to temp file then rename.
/// Prevents concurrent readers from seeing partial writes.
pub(crate) fn atomic_write(
    path: &std::path::Path,
    data: &[u8],
) -> std::io::Result<()> {
    use std::io::Write;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let tmp_path = path.with_extension("tmp");
    let mut f = std::fs::File::create(&tmp_path)?;
    f.write_all(data)?;
    f.sync_all()?;
    std::fs::rename(&tmp_path, path)?;
    Ok(())
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use super::*;
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
            SymbolTable, Type, Visibility,
        };
        use cranelift_module::default_libcall_names;
        use cranelift_object::{ObjectBuilder, ObjectModule};

        // Step 1: Create a minimal module with (defn answer [] 42)
        let defn = Defn {
            name: Symbol::from("answer"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 42,
                    span: Span::new(10, 12),
                    inferred_type: None,
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
                    vars: vec![],
                    constraints: Default::default(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                ast: Some(defn.clone()),
                code: None,
                fn_ptr: None,
            },
        );
        tables.insert(module.clone(), st);

        // Step 2: Compile to .o bytes via compile_to_module<ObjectModule>
        let isa = super::object::build_isa(true).unwrap();
        let obj_builder = ObjectBuilder::new(isa, "test", default_libcall_names()).unwrap();
        let mut obj_module = ObjectModule::new(obj_builder);

        crate::compile_to_module(
            module,
            std::slice::from_ref(&defn.name),
            &tables,
            &mut obj_module,
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
            },
        );

        // Add a Def entry (should NOT appear in imported_modules)
        table.insert(
            Symbol::from("relay"),
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: std::collections::HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: cranelisp_types::Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(cranelisp_types::DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: Some(0),
                trait_origin: None,
                ast: None,
                code: None,
                fn_ptr: None,
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
}
