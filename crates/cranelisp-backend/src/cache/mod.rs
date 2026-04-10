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
pub use serialize::{CacheMetadata, read_cached_metadata, write_cached_metadata};
pub use object::{
    ObjectCompileInput, IntrinsicTable, IntrinsicEntry,
    CacheWritePacket, build_cache_packet, process_cache_packet,
    compile_module_to_object, got_data_symbol_name,
};
pub use linker::Linker;

/// Cache format version. Bump when .o or .meta.json layout changes.
/// On mismatch, all cached modules are invalidated and recompiled.
pub const CACHE_FORMAT_VERSION: u32 = 1;

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
pub struct CachedModule {
    /// The deserialized module metadata (symbol table, structure, codegen state).
    pub metadata: serialize::CacheMetadata,
    /// Path to the `.meta.json` file (for diagnostics).
    pub meta_path: std::path::PathBuf,
    /// Path to the `.o` file (may not exist yet in metadata-only mode).
    pub object_path: std::path::PathBuf,
    /// Whether a valid `.o` file exists on disk.
    pub has_object: bool,
}

impl CachedModule {
    /// Get the restored symbol table.
    pub fn symbol_table(&self) -> &cranelisp_types::SymbolTable {
        &self.metadata.symbol_table
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
pub fn try_load_cached_module(
    cache_dir: &std::path::Path,
    module_path: &cranelisp_types::ModuleFullPath,
) -> Result<Option<CachedModule>, cranelisp_types::CranelispError> {
    let (meta_path, object_path) = module_cache_path(cache_dir, module_path);

    // Check if .meta.json exists
    if !meta_path.exists() {
        return Ok(None);
    }

    // Attempt to deserialize
    let metadata = match serialize::read_cached_metadata(&meta_path) {
        Ok(m) => m,
        Err(_) => {
            // Corrupt or incompatible metadata — treat as cache miss.
            // The file will be overwritten on next successful compilation.
            return Ok(None);
        }
    };

    // Validate the module path matches (defense against file mix-ups)
    if metadata.symbol_table.path != *module_path {
        return Ok(None);
    }

    // Check for .o file existence (for future full-cache-hit path)
    let has_object = object_path.exists()
        && std::fs::metadata(&object_path)
            .map(|m| m.len() > 0)
            .unwrap_or(false);

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
            span: cranelisp_types::Span::SYNTHETIC,
        }
    })?;

    let module_name = cached.metadata.symbol_table.path.as_ref().to_string();
    linker.load_object(&module_name, &obj_bytes)?;

    // Collect function addresses from the linker's defined_symbols.
    // Function names with GOT slots are on ModuleEntry::Def in the symbol table.
    let mut fn_addrs = std::collections::HashMap::new();
    for (name, entry) in cached.symbol_table().all_symbols() {
        if matches!(entry, cranelisp_types::ModuleEntry::Def { got_slot: Some(_), .. }) {
            if let Some(addr) = linker.get_symbol(name.as_ref()) {
                fn_addrs.insert(name.as_ref().to_string(), addr);
            }
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
mod tests {
    use super::*;
    use cranelisp_types::{ModuleFullPath, SymbolTable};

    fn make_test_metadata(module_path: &str) -> serialize::CacheMetadata {
        let mp = ModuleFullPath::from(module_path);
        serialize::CacheMetadata {
            symbol_table: SymbolTable::new(mp),
        }
    }

    // spec: design/backend/module-caching.md §8 — cache load returns metadata
    #[test]
    fn test_try_load_cached_module_success() {
        let dir = tempfile::tempdir().unwrap();
        let mp = ModuleFullPath::from("user");
        let metadata = make_test_metadata("user");

        // Write metadata to expected path
        let (meta_path, _) = module_cache_path(dir.path(), &mp);
        serialize::write_cached_metadata(&meta_path, &metadata).unwrap();

        // Load it back
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
        // Write metadata for "other" at the path for "user"
        let mp_user = ModuleFullPath::from("user");
        let metadata = make_test_metadata("other");
        let (meta_path, _) = module_cache_path(dir.path(), &mp_user);
        serialize::write_cached_metadata(&meta_path, &metadata).unwrap();

        let result = try_load_cached_module(dir.path(), &mp_user).unwrap();
        assert!(result.is_none());
    }

    // spec: design/backend/module-caching.md §8 — nested module cache load
    #[test]
    fn test_try_load_cached_module_nested() {
        let dir = tempfile::tempdir().unwrap();
        let mp = ModuleFullPath::from("core.numerics");
        let metadata = make_test_metadata("core.numerics");

        let (meta_path, _) = module_cache_path(dir.path(), &mp);
        serialize::write_cached_metadata(&meta_path, &metadata).unwrap();

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
        let metadata = make_test_metadata("user");

        let (meta_path, object_path) = module_cache_path(dir.path(), &mp);
        serialize::write_cached_metadata(&meta_path, &metadata).unwrap();
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
        let metadata = make_test_metadata("user");

        let (meta_path, object_path) = module_cache_path(dir.path(), &mp);
        serialize::write_cached_metadata(&meta_path, &metadata).unwrap();
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
        use cranelisp_types::{Defn, DefnVariant, Expr, Scheme, Span, Symbol, Visibility};
        use super::object::{ObjectCompileInput, IntrinsicTable};

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
                },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };
        let scheme = Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: cranelisp_types::Type::Fn(vec![], Box::new(cranelisp_types::Type::Int)),
        };

        let input = ObjectCompileInput {
            module_path: ModuleFullPath::from("test"),
            defns: vec![(defn, scheme)],
            method_resolutions: HashMap::new(),
            fn_slot_assignments: HashMap::new(),
            fn_to_module: HashMap::new(),
            intrinsics: IntrinsicTable::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
            expr_types: HashMap::new(),
            next_got_slot: 0,
            cross_module_fns: vec![],
        };

        // Step 2: Compile to .o bytes
        let obj_bytes = super::object::compile_module_to_object(&input, &input).unwrap();
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
}
