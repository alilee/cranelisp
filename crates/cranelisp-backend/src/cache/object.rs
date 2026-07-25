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

use cranelisp_types::{
    CranelispError, Defn, ErrorLocation, MethodResolutions, ModuleFullPath, Scheme, Span, Symbol,
    SymbolTable, Type,
};

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

    let isa_builder = cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
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
/// **S111 CS-5 (FIXME 0634)**: takes the `SymbolTable` directly and serialises
/// it via `serialise_meta(table, CACHE_SCHEMA_VERSION)` — the SymbolTable-direct
/// on-disk format `load_meta` reads. The deprecated `CacheMetadata` envelope is
/// gone.
pub fn build_cache_packet(
    cache_dir: &Path,
    module_path: &ModuleFullPath,
    source_hash: &str,
    is_stdlib: bool,
    dependency_hashes: HashMap<String, String>,
    symbol_table: &SymbolTable,
    object_compile_input: ObjectCompileInput,
) -> Result<CacheWritePacket, CranelispError> {
    let (meta_path, object_path) = super::module_cache_path(cache_dir, module_path);

    let meta_json_bytes =
        super::serialize::serialise_meta(symbol_table, super::CACHE_SCHEMA_VERSION)?;

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
        // GOT-indirect and resolved by the linker at load, and the keyed entry
        // fetch (`entry_at`) reads the callee by its fully-qualified name with
        // no alias substitution (the S110-W1-deleted `resolve_got_target`
        // qualified-name path no longer runs; the S111-R4-deleted
        // `module_aliases` compile param carried nothing after W3).
        // Object-mode cache rebuild is a batch path (introspection off) — the
        // CLIF text is dropped unread, so skip rendering it (FIXME 0325).
        crate::compile_to_module(
            input.module_path.clone(),
            &names,
            symbol_tables,
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
mod tests;
