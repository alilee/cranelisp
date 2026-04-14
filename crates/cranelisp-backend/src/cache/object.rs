// ObjectModule compilation for module caching.
//
// Re-emits a module's functions into a Cranelift ObjectModule to produce
// a relocatable `.o` file. This is the second compilation pass (the first
// targets JITModule for immediate execution).
//
// Key design decisions:
// - `ObjectCompileInput` struct replaces the sketch's 21 positional params
// - `GotReference::DataSymbol` for ObjectModule GOT references
// - Single `build_isa(is_pic: bool)` for ISA construction
// - `IntrinsicTable` unifies all extern symbol declarations
//
// See design/backend/module-caching.md §5 and §7.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use cranelift::prelude::*;
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::ObjectModule;

use serde::{Deserialize, Serialize};

use cranelisp_types::{
    CranelispError, Defn, MethodResolutions, ModuleFullPath,
    Scheme, Span, Symbol, SymbolTable, Type,
};

use super::serialize::CacheMetadata;
use crate::compiler::{CompileContext, FnCompiler};

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

impl crate::compiler::CompilationEnv for ObjectCompileInput {
    fn resolve_got(&self, _name: &Symbol) -> Option<(i64, usize)> {
        None // Legacy path — unused for object codegen.
    }

    fn resolve_got_module(&self, name: &Symbol) -> Option<(ModuleFullPath, usize)> {
        let slot_info = self.fn_slot_assignments.get(name)?;
        let module = self.fn_to_module.get(name).unwrap_or(&self.module_path);
        Some((module.clone(), slot_info.slot))
    }

    fn func_arity(&self, name: &Symbol) -> Option<usize> {
        self.fn_slot_assignments.get(name).map(|s| s.param_count)
    }
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

/// CompilationEnv for ObjectModule compilation.
///
/// Resolves GOT slots by reading from symbol tables (not live runtime state).
/// Replaces the `ObjectCompileInput impl CompilationEnv` after the unification.
pub struct ObjectCompilationEnv<'a> {
    pub symbol_tables: &'a dashmap::DashMap<ModuleFullPath, SymbolTable>,
    pub current_module: ModuleFullPath,
}

impl crate::compiler::CompilationEnv for ObjectCompilationEnv<'_> {
    fn resolve_got(&self, _name: &Symbol) -> Option<(i64, usize)> {
        // Object path doesn't use runtime pointers.
        None
    }

    fn resolve_got_module(&self, name: &Symbol) -> Option<(ModuleFullPath, usize)> {
        // Look up in current module's symbol table, following Import chains.
        let table = self.symbol_tables.get(&self.current_module)?;
        match table.get(name.as_ref())? {
            cranelisp_types::ModuleEntry::Def { got_slot: Some(slot), .. } => {
                Some((self.current_module.clone(), *slot))
            }
            cranelisp_types::ModuleEntry::Import { source } => {
                let source_mod = source.module.clone();
                let source_sym = source.symbol.clone();
                drop(table); // Release guard before getting another
                let source_table = self.symbol_tables.get(&source_mod)?;
                if let Some(cranelisp_types::ModuleEntry::Def { got_slot: Some(slot), .. }) =
                    source_table.get(source_sym.as_ref())
                {
                    Some((source_mod, *slot))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn func_arity(&self, name: &Symbol) -> Option<usize> {
        let table = self.symbol_tables.get(&self.current_module)?;
        match table.get(name.as_ref())? {
            cranelisp_types::ModuleEntry::Def { scheme, .. } => {
                if let cranelisp_types::Type::Fn(params, _) = &scheme.ty {
                    Some(params.len())
                } else {
                    None
                }
            }
            cranelisp_types::ModuleEntry::Import { source } => {
                let source_mod = source.module.clone();
                let source_sym = source.symbol.clone();
                drop(table);
                let source_table = self.symbol_tables.get(&source_mod)?;
                if let Some(cranelisp_types::ModuleEntry::Def { scheme, .. }) =
                    source_table.get(source_sym.as_ref())
                {
                    if let cranelisp_types::Type::Fn(params, _) = &scheme.ty {
                        Some(params.len())
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }
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
            span: Span::SYNTHETIC,
        })?;
    flag_builder
        .set("is_pic", if is_pic { "true" } else { "false" })
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            span: Span::SYNTHETIC,
        })?;

    let isa_builder =
        cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
            message: format!("host architecture not supported: {msg}"),
            span: Span::SYNTHETIC,
        })?;

    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to build ISA: {e}"),
            span: Span::SYNTHETIC,
        })
}

/// Build a `CacheWritePacket` from compiled module state.
///
/// Pure function: captures all needed data as owned values.
/// Called on the main thread; the resulting packet can be sent to a background writer.
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
                span: Span::SYNTHETIC,
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
            span: Span::SYNTHETIC,
        }
    })?;

    // Compile ObjectModule and write .o (only if there are defns to compile)
    if !packet.object_compile_input.defns.is_empty() {
        use cranelift_module::default_libcall_names;
        use cranelift_object::ObjectBuilder;

        let input = &packet.object_compile_input;

        // Convert ObjectCompileInput to compile_to_module params.
        let program: Vec<cranelisp_types::TopLevel> = input.defns.iter()
            .map(|(defn, _scheme)| cranelisp_types::TopLevel::Defn(defn.clone()))
            .collect();
        let check = cranelisp_types::CheckResult {
            method_resolutions: input.method_resolutions.clone(),
            constrained_fn_names: std::collections::HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: input.expr_types.clone(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };

        let isa = build_isa(true)?;
        let obj_builder = ObjectBuilder::new(isa, "cranelisp_module", default_libcall_names())
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to create ObjectBuilder: {e}"),
                span: Span::SYNTHETIC,
            })?;
        let mut obj_module = ObjectModule::new(obj_builder);

        crate::compile_to_module(
            input.module_path.clone(),
            &program,
            &check,
            symbol_tables,
            &mut obj_module,
        )?;

        let product = obj_module.finish();
        let obj_bytes = product.emit().map_err(|e| CranelispError::CodegenError {
            message: format!("failed to emit object file: {e}"),
            span: Span::SYNTHETIC,
        })?;

        super::atomic_write(&packet.object_path, &obj_bytes).map_err(|e| {
            CranelispError::CodegenError {
                message: format!(
                    "failed to write object file for {}: {e}",
                    packet.module_path
                ),
                span: Span::SYNTHETIC,
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

/// Compute the well-known GOT data symbol name for a module.
///
// Re-export from compiler module (single source of truth).
pub use crate::compiler::got_data_symbol_name;

/// Compile a module's functions into a relocatable `.o` file.
///
/// This is the second compilation pass — the first targets `JITModule` for
/// immediate execution. This pass re-emits the same functions through
/// `FnCompiler<ObjectModule>` to produce a relocatable object file that
/// the `Linker` can load on cache hit.
///
/// See design/backend/module-caching.md §13.2 for the detailed design.
pub fn _deprecated_compile_module_to_object(
    _input: &ObjectCompileInput,
    _env: &dyn crate::compiler::CompilationEnv,
    _symbol_tables: &dashmap::DashMap<ModuleFullPath, SymbolTable>,
) -> Result<Vec<u8>, CranelispError> {
    unimplemented!("superseded by compile_to_module")
}

// ---------------------------------------------------------------------------
// Helper functions for compile_module_to_object
// ---------------------------------------------------------------------------

/// Declare GOT data symbols for every module whose GOT is referenced.
fn declare_got_data_symbols(
    obj_module: &mut ObjectModule,
    self_path: &ModuleFullPath,
    fn_to_module: &HashMap<Symbol, ModuleFullPath>,
) -> Result<HashMap<ModuleFullPath, cranelift_module::DataId>, CranelispError> {
    let mut got_data_ids: HashMap<ModuleFullPath, cranelift_module::DataId> = HashMap::new();

    // Collect all referenced modules
    let mut referenced_modules: HashSet<ModuleFullPath> = HashSet::new();
    referenced_modules.insert(self_path.clone());
    for mod_path in fn_to_module.values() {
        referenced_modules.insert(mod_path.clone());
    }

    for mod_path in &referenced_modules {
        let symbol_name = got_data_symbol_name(mod_path);
        let is_self = mod_path == self_path;

        // All GOT data symbols are Export + writable. Foreign modules get
        // 8-byte literal pool entries (linker patches with GotTable address).
        // Self-module is declared here but defined later with actual GOT content.
        let data_id = obj_module
            .declare_data(
                &symbol_name,
                Linkage::Export,
                true,  // writable
                false, // tls
            )
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare GOT data symbol '{symbol_name}': {e}"),
                span: Span::SYNTHETIC,
            })?;

        // Foreign GOT symbols: define as 8-byte zeroed entry (linker patches).
        // Self-module: defined later with function address relocations.
        if !is_self {
            let mut desc = DataDescription::new();
            desc.define(Box::new([0u8; 8]));
            obj_module
                .define_data(data_id, &desc)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define GOT data symbol '{symbol_name}': {e}"),
                    span: Span::SYNTHETIC,
                })?;
        }

        got_data_ids.insert(mod_path.clone(), data_id);
    }

    Ok(got_data_ids)
}

/// Declare all intrinsic (runtime + primitive + platform) functions as imports.
///
/// Delegates to `declare_intrinsics_generic<M>` for the standard intrinsics,
/// then adds any platform-specific entries from the IntrinsicTable.
fn declare_intrinsic_imports(
    obj_module: &mut ObjectModule,
    intrinsics: &IntrinsicTable,
) -> Result<HashMap<String, FuncId>, CranelispError> {
    // Use the generic path for all standard intrinsics.
    let generic_ids = crate::jit::declare_intrinsics_generic(obj_module)?;

    // Convert IntrinsicFuncIds to the HashMap<String, FuncId> expected by callers.
    let mut ids: HashMap<String, FuncId> = HashMap::new();
    for (name, func_id) in &generic_ids.by_name {
        ids.insert(name.as_ref().to_string(), *func_id);
    }

    // Add platform-specific entries (not covered by intrinsic_symbols()).
    for entry in &intrinsics.platform_fns {
        if ids.contains_key(&entry.jit_name) {
            continue;
        }
        let mut sig = obj_module.make_signature();
        for _ in 0..entry.param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = obj_module
            .declare_function(&entry.jit_name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!(
                    "failed to declare platform intrinsic '{}': {e}",
                    entry.jit_name
                ),
                span: Span::SYNTHETIC,
            })?;
        ids.insert(entry.jit_name.clone(), func_id);
        ids.insert(entry.user_name.as_ref().to_string(), func_id);
    }

    Ok(ids)
}

/// Declare all module functions as exports (Pass 1: get FuncIds before compilation).
///
/// Uses bare function names (e.g., `add-one`) as the linker symbol, matching
/// how the JIT cache-load path registers symbols. Cross-module import
/// declarations strip the module prefix to match (see `compile_all_functions`).
fn declare_module_functions(
    obj_module: &mut ObjectModule,
    defns: &[(Defn, Scheme)],
) -> Result<Vec<FuncId>, CranelispError> {
    let mut func_ids = Vec::with_capacity(defns.len());
    for (defn, _scheme) in defns {
        let mut sig = obj_module.make_signature();
        for _ in defn.params() {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = obj_module
            .declare_function(defn.name.as_ref(), Linkage::Export, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare function '{}': {e}", defn.name),
                span: defn.span,
            })?;
        func_ids.push(func_id);
    }
    Ok(func_ids)
}

/// Define the current module's GOT data section with function-address relocations.
///
/// IMPORTANT: Uses `data_desc.define(vec![0u8; ...])` NOT `define_zeroinit()`.
/// The latter places data in __bss on Mach-O, which has no file-backed content
/// and causes the system linker to SIGSEGV when applying relocations.
/// See design/backend/module-caching.md §13.6 (__data vs __bss GOTCHA).
#[allow(clippy::too_many_arguments)]
fn define_got_data(
    obj_module: &mut ObjectModule,
    self_path: &ModuleFullPath,
    got_data_ids: &HashMap<ModuleFullPath, cranelift_module::DataId>,
    declared_func_ids: &[FuncId],
    defns: &[(Defn, Scheme)],
    fn_slot_assignments: &HashMap<Symbol, FnSlotInfo>,
    fn_to_module: &HashMap<Symbol, ModuleFullPath>,
    next_got_slot: usize,
) -> Result<(), CranelispError> {
    let self_got_data_id = match got_data_ids.get(self_path) {
        Some(id) => *id,
        None => return Ok(()), // No GOT for this module
    };

    if next_got_slot == 0 {
        return Ok(());
    }

    // Build name→FuncId mapping from declared functions
    let name_to_func_id: HashMap<&str, FuncId> = defns
        .iter()
        .zip(declared_func_ids.iter())
        .map(|((defn, _), &fid)| (defn.name.as_ref(), fid))
        .collect();

    // Build slot→FuncId mapping for self-module functions
    let mut slot_to_func_id: HashMap<usize, FuncId> = HashMap::new();
    for (name, slot_info) in fn_slot_assignments {
        // Only include functions owned by this module
        let is_self = fn_to_module
            .get(name)
            .is_some_and(|m| m == self_path);
        if (is_self || !fn_to_module.contains_key(name))
            && let Some(&fid) = name_to_func_id.get(name.as_ref())
        {
            slot_to_func_id.insert(slot_info.slot, fid);
        }
    }

    let mut data_desc = DataDescription::new();
    // Use explicit zero bytes (NOT define_zeroinit) — see GOTCHA above.
    data_desc.define(vec![0u8; next_got_slot * 8].into_boxed_slice());
    data_desc.set_align(8);

    // Add function-address relocations for each occupied GOT slot
    for (&slot, &func_id) in &slot_to_func_id {
        let func_ref = obj_module.declare_func_in_data(func_id, &mut data_desc);
        data_desc.write_function_addr((slot * 8) as u32, func_ref);
    }

    obj_module
        .define_data(self_got_data_id, &data_desc)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define GOT data: {e:?}"),
            span: Span::SYNTHETIC,
        })?;

    Ok(())
}

/// Object-module GOT slot info: maps function names to their module's DataId
/// and slot index, so FnCompiler can load function pointers via data symbols.
///
/// Currently unused because the ObjectModule path uses Batch mode (direct calls).
/// When Interactive-mode ObjectModule compilation is added (requiring the
/// GotReference::DataSymbol abstraction from §13.2), these fields will be used
/// to emit GOT-indirect calls in the generated code.
#[allow(dead_code)]
struct ObjFnSlot {
    /// DataId of the module's GOT data symbol.
    got_data_id: cranelift_module::DataId,
    /// Slot index within the GOT.
    slot: usize,
    /// Number of parameters (for signature generation).
    param_count: usize,
}

/// Build fn_slots with per-module DataId GOT references for ObjectModule.
fn build_obj_fn_slots(
    fn_slot_assignments: &HashMap<Symbol, FnSlotInfo>,
    fn_to_module: &HashMap<Symbol, ModuleFullPath>,
    got_data_ids: &HashMap<ModuleFullPath, cranelift_module::DataId>,
    self_path: &ModuleFullPath,
) -> Result<HashMap<Symbol, ObjFnSlot>, CranelispError> {
    let mut obj_fn_slots = HashMap::new();

    for (name, slot_info) in fn_slot_assignments {
        let mod_path = fn_to_module.get(name).unwrap_or(self_path);
        let data_id = got_data_ids.get(mod_path).copied().ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!(
                    "no GOT data symbol for function '{}' (module '{}')",
                    name, mod_path
                ),
                span: Span::SYNTHETIC,
            }
        })?;
        obj_fn_slots.insert(
            name.clone(),
            ObjFnSlot {
                got_data_id: data_id,
                slot: slot_info.slot,
                param_count: slot_info.param_count,
            },
        );
    }

    Ok(obj_fn_slots)
}

/// Compile all function bodies into the ObjectModule (Pass 2).
///
/// Uses `FnCompiler<ObjectModule>` — the same codegen as the JIT path,
/// but targeting relocatable code instead of immediate execution.
fn compile_all_functions(
    obj_module: &mut ObjectModule,
    input: &ObjectCompileInput,
    declared_func_ids: &[FuncId],
    intrinsic_func_ids: &HashMap<String, FuncId>,
    _obj_fn_slots: &HashMap<Symbol, ObjFnSlot>,
    env: &dyn crate::compiler::CompilationEnv,
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SymbolTable>,
) -> Result<(), CranelispError> {
    // Build func_ids: intrinsics + all module functions get direct calls.
    // In object files, the system linker resolves symbol references, so both
    // self-module and cross-module function calls can use direct BL. This
    // avoids depending on runtime GOT initialization, which is required for
    // JIT mode but unnecessary for linked executables.
    let mut func_ids: HashMap<Symbol, FuncId> = HashMap::new();
    for (name, &fid) in intrinsic_func_ids {
        func_ids.insert(Symbol::from(name.as_str()), fid);
    }
    // Add self-module functions (declared in Pass 1).
    for ((defn, _), &fid) in input.defns.iter().zip(declared_func_ids.iter()) {
        func_ids.insert(defn.name.clone(), fid);
    }
    // Declare cross-module functions as imports and add to func_ids.
    // The system linker resolves these against the importing module's .o file.
    for (name, param_count) in &input.cross_module_fns {
        if func_ids.contains_key(name) {
            continue;
        }
        let bare_name = if let Some(slash_pos) = name.as_ref().find('/') {
            &name.as_ref()[slash_pos + 1..]
        } else {
            name.as_ref()
        };
        // Cross-module functions may already be declared (as self-module or intrinsic).
        if func_ids.contains_key(bare_name) {
            continue;
        }
        let mut sig = obj_module.make_signature();
        for _ in 0..*param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        match obj_module.declare_function(bare_name, Linkage::Import, &sig) {
            Ok(fid) => {
                func_ids.insert(Symbol::from(bare_name), fid);
                // Also register the qualified name
                func_ids.insert(name.clone(), fid);
            }
            Err(_) => {
                // If declaration fails (e.g., symbol already declared with different
                // linkage), fall back to GOT-indirect for this function.
            }
        }
    }

    // Build func_arities map (local defns + cross-module functions)
    let mut func_arities: HashMap<Symbol, usize> = input
        .defns
        .iter()
        .map(|(defn, _)| (defn.name.clone(), defn.params().len()))
        .collect();
    for (name, param_count) in &input.cross_module_fns {
        func_arities.entry(name.clone()).or_insert(*param_count);
        // Also register bare name arity for qualified imports
        if let Some(slash_pos) = name.as_ref().find('/') {
            let bare = Symbol::from(&name.as_ref()[slash_pos + 1..]);
            func_arities.entry(bare).or_insert(*param_count);
        }
    }

    // Resolve intrinsic FuncIds for the compile context
    let alloc_func_id = intrinsic_func_ids.get("runtime/alloc").copied();
    let dealloc_func_id = intrinsic_func_ids.get("runtime/dealloc").copied();
    let alloc_string_func_id = intrinsic_func_ids.get("runtime/alloc_string").copied();
    let panic_func_id = intrinsic_func_ids.get("runtime/panic").copied();
    let vec_new_func_id = intrinsic_func_ids.get("runtime/vec_new").copied();
    let vec_drop_func_id = intrinsic_func_ids.get("runtime/vec_drop").copied();

    let mut func_ctx = FunctionBuilderContext::new();

    for ((defn, _scheme), &func_id) in input.defns.iter().zip(declared_func_ids.iter()) {
        let mut sig = obj_module.make_signature();
        for _ in defn.params() {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let mut func = cranelift::codegen::ir::Function::with_name_signature(
            cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
            sig,
        );

        // Build CompileContext for this function.
        // GOT-indirect calls via got_refs — Cranelift emits ADRP+ADD
        // relocations for the GOT data symbol, resolved by the linker.
        // Same calling convention as the JIT path (global_value).
        let compile_ctx = CompileContext {
            method_resolutions: &input.method_resolutions,
            expr_types: &input.expr_types,
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables,
            current_module: input.module_path.clone(),
            env: Some(env),
            traced_fns: None,
            alloc_func_id,
            dealloc_func_id,
            alloc_string_func_id,
            panic_func_id,
            vec_new_func_id,
            vec_drop_func_id,
        };

        FnCompiler::compile_body(
            defn,
            &mut func,
            &mut func_ctx,
            obj_module,
            compile_ctx,
        )?;

        let mut ctx = cranelift::codegen::Context::for_function(func);
        obj_module
            .define_function(func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define function '{}': {e:?}", defn.name),
                span: defn.span,
            })?;
    }

    Ok(())
}

/// Result of processing a cache write packet. Used by the caller to
/// update the manifest.
pub struct ProcessedPacket {
    pub module_path: ModuleFullPath,
    pub source_hash: String,
    pub is_stdlib: bool,
    pub dependency_hashes: HashMap<String, String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{ModuleFullPath, SymbolTable};

    // spec: design/backend/module-caching.md §5 — build_isa with PIC produces valid ISA
    #[test]
    fn test_build_isa_pic() {
        let isa = build_isa(true).unwrap();
        assert!(isa.triple().to_string().len() > 0);
    }

    // spec: design/backend/module-caching.md §5 — build_isa without PIC produces valid ISA
    #[test]
    fn test_build_isa_non_pic() {
        let isa = build_isa(false).unwrap();
        assert!(isa.triple().to_string().len() > 0);
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
            method_resolutions: HashMap::new(),
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
            method_resolutions: HashMap::new(),
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

    // spec: design/backend/module-caching.md §13.2 — compile simple module to .o
    #[test]
    fn test_compile_module_to_object_simple() {
        use cranelisp_types::{CheckResult, Defn, DefnVariant, Expr, TopLevel, Visibility};

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

        let program = vec![TopLevel::Defn(defn)];
        let check = CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: std::collections::HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };

        let mut obj_module = test_object_module();
        let _result = crate::compile_to_module(
            ModuleFullPath::from("user"),
            &program,
            &check,
            &dashmap::DashMap::new(),
            &mut obj_module,
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
        use cranelisp_types::{CheckResult, Defn, DefnVariant, Expr, TopLevel, Visibility};

        let defn = Defn {
            name: Symbol::from("identity"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(20, 21),
                },
                span: Span::new(0, 25),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 25),
        };

        let program = vec![TopLevel::Defn(defn)];
        let check = CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: std::collections::HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };

        let mut obj_module = test_object_module();
        let _result = crate::compile_to_module(
            ModuleFullPath::from("user"),
            &program,
            &check,
            &dashmap::DashMap::new(),
            &mut obj_module,
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
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 0,
                    span: Span::new(10, 11),
                },
                span: Span::new(0, 15),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 15),
        };
        let scheme = Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: cranelisp_types::Type::Fn(vec![], Box::new(cranelisp_types::Type::Int)),
        };

        let input = ObjectCompileInput {
            module_path: mp.clone(),
            defns: vec![(defn, scheme)],
            method_resolutions: HashMap::new(),
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

        let result = process_cache_packet(&packet, &dashmap::DashMap::new()).unwrap();
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
            method_resolutions: HashMap::new(),
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
