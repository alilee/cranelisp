//! `.o` build-packet construction + processing — the object-path plumbing.
//!
//! Drives the object compilation path: `compile_to_module::<ObjectModule>`
//! followed by the caller's `obj_module.finish().emit()` (the caller-finalize
//! contract — there is no separate `compile_to_object` backend free function).
//! The structs here ([`ObjectCompileInput`], [`CacheWritePacket`],
//! [`IntrinsicTable`], …) cross the backend↔int boundary: the nice worker
//! produces them, `int` writes the resulting `.o` + sidecar to disk.
//!
//! [`build_isa`] is the **single ISA construction point** (re-exported at the
//! crate root as `cranelisp_backend::build_isa`); `got_data_symbol_name`
//! produces the `__cranelisp_got_{module}` data-symbol name (Decision 23).
//!
//! Key design decisions:
//! - [`ObjectCompileInput`] groups the codegen input (replaces the sketch's 21
//!   positional params).
//! - `GotReference::DataSymbol` for `ObjectModule` GOT references.
//! - Single `build_isa(is_pic: bool)` for ISA construction.
//! - [`IntrinsicTable`] unifies all extern-symbol declarations (the three
//!   buckets track Decision 43's three-crate split of relocation targets).
//!
//! See `design/backend/module-caching.md` §5 and §7.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use cranelift_object::ObjectModule;

use serde::{Deserialize, Serialize};

use cranelisp_types::{ErrorLocation, 
    CranelispError, Defn, MethodResolutions, ModuleFullPath,
    Scheme, Span, Symbol, SymbolTable, Type,
};

#[allow(deprecated)]
use super::serialize::CacheMetadata;

/// All inputs needed to compile a module to an ObjectModule.
/// Grouped to replace the sketch's 21 positional parameters (HIGH-3).
#[derive(Debug, Clone)]
pub struct ObjectCompileInput {
    pub module_path: ModuleFullPath,
    pub defns: Vec<(Defn, Scheme)>,
    pub method_resolutions: MethodResolutions,
    pub fn_slot_assignments: HashMap<Symbol, FnSlotInfo>,
    pub fn_to_module: HashMap<Symbol, ModuleFullPath>,
    pub intrinsics: IntrinsicTable,
    pub expr_types: HashMap<Span, Type>,
    pub next_got_slot: usize,
    /// Cross-module function references: (name, param_count) for functions
    /// from dependency modules that this module's compiled code may call.
    /// Includes both qualified names ("util/helper") and bare imported names ("helper").
    pub cross_module_fns: Vec<(Symbol, usize)>,
}

/// Information about a function's GOT slot assignment.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FnSlotInfo {
    pub slot: usize,
    pub param_count: usize,
}

/// All extern symbols that compiled code may reference.
/// Single source of truth -- shared between JIT setup and ObjectModule compilation.
/// Addresses cache audit HIGH-1 (intrinsic coverage) and HIGH-3 (parameter explosion).
#[derive(Debug, Clone)]
pub struct IntrinsicTable {
    /// Runtime infrastructure functions: alloc, free, panic, trace_*, rc_*.
    pub runtime_fns: Vec<IntrinsicEntry>,
    /// User-visible primitive functions: add-i64, str-concat, etc.
    pub primitive_fns: Vec<IntrinsicEntry>,
    /// Platform DLL functions (Ring 4).
    pub platform_fns: Vec<IntrinsicEntry>,
    /// Special forms + primitives names (for liveness analysis globals).
    pub global_names: std::collections::HashSet<Symbol>,
}

impl IntrinsicTable {
    pub fn new() -> Self {
        IntrinsicTable {
            runtime_fns: Vec::new(),
            primitive_fns: Vec::new(),
            platform_fns: Vec::new(),
            global_names: std::collections::HashSet::new(),
        }
    }
}

impl Default for IntrinsicTable {
    fn default() -> Self {
        Self::new()
    }
}

/// A single extern function entry.
#[derive(Debug, Clone)]
pub struct IntrinsicEntry {
    /// User-visible name (e.g., "+", "str-concat").
    pub user_name: Symbol,
    /// JIT symbol name (e.g., "runtime/alloc", "add-i64").
    pub jit_name: String,
    /// Number of parameters.
    pub param_count: usize,
}

/// An owned snapshot for background cache writing. Fully Send-safe.
///
/// Contains everything needed to compile an ObjectModule and write
/// the `.meta.json` and `.o` files without access to any live session state.
pub struct CacheWritePacket {
    /// Directory to write cache files into.
    pub cache_dir: PathBuf,
    /// Module identity.
    pub module_path: ModuleFullPath,
    /// Source hash for manifest update.
    pub source_hash: String,
    /// Whether this is a stdlib module.
    pub is_stdlib: bool,
    /// Dependency hashes for manifest update.
    pub dependency_hashes: HashMap<String, String>,

    /// Pre-serialized metadata JSON bytes (computed on the sending thread).
    pub meta_json_bytes: Vec<u8>,
    /// Path within cache_dir for the .meta.json file.
    pub meta_path: PathBuf,
    /// Path within cache_dir for the .o file.
    pub object_path: PathBuf,

    /// Inputs for ObjectModule compilation.
    pub object_compile_input: ObjectCompileInput,
}

// CacheWritePacket must be Send for background thread use.
// ObjectCompileInput contains no raw pointers.
unsafe impl Send for CacheWritePacket {}

/// Build ISA for the host architecture.
///
/// Single ISA construction point (architecture decision 7, addresses HIGH-2).
/// - `is_pic: false` for JIT (absolute addresses)
/// - `is_pic: true` for ObjectModule (relocatable code)
pub fn build_isa(
    is_pic: bool,
) -> Result<Arc<dyn cranelift_codegen::isa::TargetIsa>, CranelispError> {
    use cranelift_codegen::settings::{self, Configurable};

    let mut flag_builder = settings::builder();
    flag_builder
        .set("use_colocated_libcalls", "false")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    flag_builder
        .set("is_pic", if is_pic { "true" } else { "false" })
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let isa_builder =
        cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
            message: format!("host architecture not supported: {msg}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to build ISA: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })
}

/// Build a `CacheWritePacket` from compiled module state.
///
/// Pure function: captures all needed data as owned values.
/// Called on the main thread; the resulting packet can be sent to a background writer.
///
/// **Sprint 58 §14.4**: callers should serialise the `SymbolTable` directly
/// via `serialise_meta(&table, CACHE_SCHEMA_VERSION)` and pass the resulting
/// bytes to a future `build_cache_packet` overload that does not require the
/// envelope. The current `metadata: &CacheMetadata` parameter is preserved
/// during the Wave 2b parallel migration; it is wrapped onto an
/// already-deprecated type.
#[allow(deprecated)]
pub fn build_cache_packet(
    cache_dir: &Path,
    module_path: &ModuleFullPath,
    source_hash: &str,
    is_stdlib: bool,
    dependency_hashes: HashMap<String, String>,
    metadata: &CacheMetadata,
    object_compile_input: ObjectCompileInput,
) -> Result<CacheWritePacket, CranelispError> {
    let (meta_path, object_path) = super::module_cache_path(cache_dir, module_path);

    let meta_json_bytes =
        serde_json::to_string_pretty(metadata)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to serialize module metadata: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?
            .into_bytes();

    Ok(CacheWritePacket {
        cache_dir: cache_dir.to_path_buf(),
        module_path: module_path.clone(),
        source_hash: source_hash.to_string(),
        is_stdlib,
        dependency_hashes,
        meta_json_bytes,
        meta_path,
        object_path,
        object_compile_input,
    })
}

/// Process a `CacheWritePacket`: write `.meta.json` and `.o` files to disk.
///
/// Writes the `.meta.json` containing SymbolTable +
/// CacheCodegenState. Then compiles the module's functions into a
/// relocatable `.o` file via Cranelift's `ObjectModule` and writes that too.
///
/// On cache hit, the `.meta.json` restores typechecker state (skip parsing,
/// macro expansion, typechecking), and the `.o` is loaded via the `Linker`
/// to restore function code (skip codegen).
///
/// Returns a `ProcessedPacket` with the module identity and hashes for
/// manifest tracking.
pub fn process_cache_packet(
    packet: &CacheWritePacket,
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SymbolTable>,
) -> Result<ProcessedPacket, CranelispError> {
    // Write .meta.json atomically
    super::atomic_write(&packet.meta_path, &packet.meta_json_bytes).map_err(|e| {
        CranelispError::CodegenError {
            message: format!(
                "failed to write cache metadata for {}: {e}",
                packet.module_path
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })?;

    // Compile ObjectModule and write .o (only if there are defns to compile)
    if !packet.object_compile_input.defns.is_empty() {
        use cranelift_module::default_libcall_names;
        use cranelift_object::ObjectBuilder;

        let input = &packet.object_compile_input;

        // Post-Phase-2: the backend reads defn bodies from `symbol_tables[module].get(name).ast`.
        // The packet's `defns` field only supplies the name list here; the
        // canonical AST already lives on the symbol table (Wave 0 invariant).
        let names: Vec<Symbol> = input
            .defns
            .iter()
            .map(|(defn, _scheme)| defn.name.clone())
            .collect();

        let isa = build_isa(true)?;
        let obj_builder = ObjectBuilder::new(isa, "cranelisp_module", default_libcall_names())
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to create ObjectBuilder: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        let mut obj_module = ObjectModule::new(obj_builder);

        // Object-mode full-module compile: cross-module references are emitted
        // GOT-indirect and resolved by the linker at load (not via alias-prefix
        // resolution at codegen), so an empty alias table is the correct,
        // behaviour-preserving input here — `resolve_got_target` then takes its
        // prior child/absolute qualified-name path. (S75 W2 D41 rotation added
        // the `module_aliases` param to `compile_to_module`.)
        let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
        // Object-mode cache rebuild is a batch path (introspection off) — the
        // CLIF text is dropped unread, so skip rendering it (FIXME 0325).
        crate::compile_to_module(
            input.module_path.clone(),
            &names,
            symbol_tables,
            &module_aliases,
            &mut obj_module,
            false,
        )?;

        let product = obj_module.finish();
        let obj_bytes = product.emit().map_err(|e| CranelispError::CodegenError {
            message: format!("failed to emit object file: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

        super::atomic_write(&packet.object_path, &obj_bytes).map_err(|e| {
            CranelispError::CodegenError {
                message: format!(
                    "failed to write object file for {}: {e}",
                    packet.module_path
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
    }

    Ok(ProcessedPacket {
        module_path: packet.module_path.clone(),
        source_hash: packet.source_hash.clone(),
        is_stdlib: packet.is_stdlib,
        dependency_hashes: packet.dependency_hashes.clone(),
    })
}

// GOT data symbol naming collapsed to a single `pub(crate)` home in S75 W3
// (per the /arch re-ruling): the canonical fn is
// `crate::compiler::got_data_symbol_name`. The former `cache::object`
// re-export — which existed only to serve int's call path — is removed; all
// in-crate callers use the `crate::compiler::` path directly.

/// Result of processing a cache write packet. Used by the caller to
/// update the manifest.
pub struct ProcessedPacket {
    pub module_path: ModuleFullPath,
    pub source_hash: String,
    pub is_stdlib: bool,
    pub dependency_hashes: HashMap<String, String>,
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
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
        let metadata = CacheMetadata {
            symbol_table: SymbolTable::new(mp.clone()),
            dependencies: Vec::new(),
        };
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
            &metadata,
            input,
        )
        .unwrap();

        assert_eq!(packet.module_path, mp);
        assert_eq!(packet.source_hash, "abc123");
        assert!(!packet.meta_json_bytes.is_empty());
        assert!(packet.meta_path.to_str().unwrap().contains("module.meta.json"));
        assert!(packet.object_path.to_str().unwrap().contains("module.o"));
    }

    // spec: design/backend/module-caching.md §7 — process_cache_packet writes files
    #[test]
    fn test_process_cache_packet() {
        let dir = tempfile::tempdir().unwrap();
        let mp = ModuleFullPath::from("user");
        let metadata = CacheMetadata {
            symbol_table: SymbolTable::new(mp.clone()),
            dependencies: Vec::new(),
        };
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
            &metadata,
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
        use cranelisp_types::{DefKind, ModuleEntry, Visibility};
        let tables = dashmap::DashMap::new();
        let mut st = SymbolTable::new(module.clone());
        let name = defn.name.clone();
        let param_names: Vec<Symbol> = defn
            .variants
            .first()
            .map(|v| v.params.iter().map(|(n, _)| n.clone()).collect())
            .unwrap_or_default();
        let variant = defn.variants.first().cloned();
        st.insert(
            name,
            ModuleEntry::Def {
                scheme,
                visibility: Visibility::Public,
                docstring: None,
                param_names,
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                seq: 0,
                ast: variant,
                code: None,
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
                    inferred_type: None,
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
        let aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
        let _result = crate::compile_to_module(
            module,
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            &mut obj_module,
            false,
        ).unwrap();

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
                    inferred_type: None,
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
        let aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
        let _result = crate::compile_to_module(
            module,
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            &mut obj_module,
            false,
        ).unwrap();

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
        let metadata = CacheMetadata {
            symbol_table: SymbolTable::new(mp.clone()),
            dependencies: Vec::new(),
        };

        let defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                    value: 0,
                    span: Span::new(10, 11),
                    inferred_type: None,
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
            &metadata,
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
        let metadata = CacheMetadata {
            symbol_table: SymbolTable::new(mp.clone()),
            dependencies: Vec::new(),
        };
        let input = ObjectCompileInput {
            module_path: mp.clone(),
            defns: vec![],  // No functions
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
            &metadata,
            input,
        )
        .unwrap();

        let _result = process_cache_packet(&packet, &dashmap::DashMap::new()).unwrap();

        // .meta.json should exist, but .o should NOT
        assert!(packet.meta_path.exists());
        assert!(!packet.object_path.exists(), "no .o for empty defns");
    }
}
