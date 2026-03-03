//! Module cache: persist compiled module metadata and object files to disk.
//!
//! Cache layout:
//! ```
//! .cranelisp-cache/
//!   manifest.json           # version, target triple, module hashes
//!   <module>.meta.json      # serialized CompiledModule
//!   <module>.o              # relocatable object file
//! ```

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use cranelift::prelude::*;
use cranelift_module::{default_libcall_names, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::codegen::{
    compile_function_indirect, FnSlot, GotReference, TypeDefInfoCg,
};
use crate::error::{CranelispError, Span};
use crate::module::CompiledModule;
use crate::names::ModuleFullPath;
use crate::typechecker::MethodResolutions;
use crate::types::Type;

// ── Extracted cache input types ─────────────────────────────────────────

/// A primitive function entry extracted from CompiledModule for cache compilation.
/// Contains enough information to declare the function as an import in ObjectModule.
pub struct PrimitiveEntry {
    pub user_name: String,
    pub jit_name: String,
    pub param_count: usize,
}

/// Pre-extracted data from `modules` needed by `compile_module_to_object`.
/// This avoids passing the full `HashMap<ModuleFullPath, CompiledModule>` (which
/// contains non-Send raw pointers in GOT tables) to background threads.
pub struct CacheInputs {
    /// Mangled function name → owning module short name (for GOT data symbol lookup).
    pub fn_to_module: HashMap<String, String>,
    /// Primitive functions with JIT names (for declaring imports in ObjectModule).
    pub primitive_entries: Vec<PrimitiveEntry>,
    /// All Primitive + SpecialForm names (for liveness analysis globals).
    pub global_names: std::collections::HashSet<String>,
}

/// Extract cache-compilation inputs from loaded modules.
///
/// This scans all `CompiledModule`s to build:
/// - `fn_to_module`: maps each UserFn's name (bare + qualified) to its owning module
/// - `primitive_entries`: all Primitive entries that have JIT names (for import declaration)
/// - `global_names`: all Primitive + SpecialForm symbol names (for liveness globals)
pub fn extract_cache_inputs(
    modules: &HashMap<ModuleFullPath, CompiledModule>,
) -> CacheInputs {
    let mut fn_to_module = HashMap::new();
    let mut primitive_entries = Vec::new();
    let mut global_names = std::collections::HashSet::new();

    for (mod_path_key, cm) in modules {
        let mod_short = mod_path_key.short_name().to_string();
        for (sym, entry) in &cm.symbols {
            match entry {
                crate::module::ModuleEntry::Def {
                    kind:
                        crate::module::DefKind::UserFn {
                            codegen:
                                crate::module::DefCodegen {
                                    got_slot: Some(_), ..
                                },
                            ..
                        },
                    ..
                } => {
                    fn_to_module.insert(sym.to_string(), mod_short.clone());
                    fn_to_module.insert(format!("{}/{}", mod_short, sym), mod_short.clone());
                }
                crate::module::ModuleEntry::Def {
                    kind:
                        crate::module::DefKind::Primitive {
                            jit_name: Some(jn),
                            ..
                        },
                    scheme,
                    ..
                } => {
                    primitive_entries.push(PrimitiveEntry {
                        user_name: sym.to_string(),
                        jit_name: jn.to_string(),
                        param_count: scheme.param_count(),
                    });
                    global_names.insert(sym.to_string());
                }
                crate::module::ModuleEntry::Def {
                    kind: crate::module::DefKind::Primitive { jit_name: None, .. },
                    ..
                } => {
                    // Primitives without JIT names still contribute to liveness globals
                    global_names.insert(sym.to_string());
                }
                crate::module::ModuleEntry::Def {
                    kind: crate::module::DefKind::SpecialForm { .. },
                    ..
                } => {
                    global_names.insert(sym.to_string());
                }
                _ => {}
            }
        }
    }

    CacheInputs {
        fn_to_module,
        primitive_entries,
        global_names,
    }
}

// ── Cache manifest ──────────────────────────────────────────────────────

/// Cache format version — bump when .o layout changes (e.g., GOT-in-.o).
/// On mismatch, all cached modules are invalidated and recompiled.
pub const CACHE_FORMAT_VERSION: u32 = 4;

#[derive(Serialize, Deserialize)]
pub struct CacheManifest {
    pub cranelisp_version: String,
    pub target_triple: String,
    #[serde(default)]
    pub cache_format_version: u32,
    #[serde(default)]
    pub binary_fingerprint: String,
    pub modules: Vec<CachedModuleRef>,
}

#[derive(Serialize, Deserialize)]
pub struct CachedModuleRef {
    pub module_path: ModuleFullPath,
    pub source_hash: String, // hex-encoded SHA-256
}

impl CacheManifest {
    pub fn new(target_triple: &str) -> Self {
        CacheManifest {
            cranelisp_version: env!("CARGO_PKG_VERSION").to_string(),
            target_triple: target_triple.to_string(),
            cache_format_version: CACHE_FORMAT_VERSION,
            binary_fingerprint: binary_fingerprint(),
            modules: Vec::new(),
        }
    }

    /// Check if a module is cached with a matching source hash.
    pub fn is_cached(&self, module_path: &ModuleFullPath, source_hash: &str) -> bool {
        self.modules.iter().any(|m| {
            m.module_path == *module_path && m.source_hash == source_hash
        })
    }

    /// Add or update a module entry.
    pub fn upsert_module(&mut self, module_path: ModuleFullPath, source_hash: String) {
        if let Some(entry) = self.modules.iter_mut().find(|m| m.module_path == module_path) {
            entry.source_hash = source_hash;
        } else {
            self.modules.push(CachedModuleRef {
                module_path,
                source_hash,
            });
        }
    }
}

// ── Source hashing ──────────────────────────────────────────────────────

/// Compute a hex-encoded SHA-256 hash of source text.
pub fn hash_source(source: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(source.as_bytes());
    let result = hasher.finalize();
    hex_encode(&result)
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Fingerprint of the running cranelisp binary based on its modification time.
/// Changes on any rebuild, ensuring cached .o files match the current codegen.
/// Memoized via OnceLock — computed at most once per process.
fn binary_fingerprint() -> String {
    static FINGERPRINT: OnceLock<String> = OnceLock::new();
    FINGERPRINT
        .get_or_init(|| {
            let t0 = std::time::Instant::now();
            let exe = match std::env::current_exe() {
                Ok(p) => p,
                Err(_) => return String::new(),
            };
            let meta = match fs::metadata(&exe) {
                Ok(m) => m,
                Err(_) => return String::new(),
            };
            let mtime = match meta.modified() {
                Ok(t) => t,
                Err(_) => return String::new(),
            };
            let duration = mtime
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default();
            let fp = format!("mtime-{}.{}", duration.as_secs(), duration.subsec_nanos());
            if timing_enabled() {
                eprintln!("; timing: binary_fingerprint {}ms", t0.elapsed().as_millis());
            }
            fp
        })
        .clone()
}

/// Check whether `CRANELISP_TIMING=1` is set.
pub fn timing_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("CRANELISP_TIMING").is_ok())
}

// ── Cache directory management ──────────────────────────────────────────

/// Get the cache directory path for a project.
pub fn cache_dir(project_root: &Path) -> PathBuf {
    project_root.join(".cranelisp-cache")
}

/// Read the cache manifest, if it exists and is valid.
pub fn read_manifest(cache_dir: &Path) -> Option<CacheManifest> {
    let path = cache_dir.join("manifest.json");
    let content = fs::read_to_string(path).ok()?;
    serde_json::from_str(&content).ok()
}

/// Write bytes to a file atomically by writing to a temp file then renaming.
/// Prevents concurrent readers from seeing partially-written files.
fn atomic_write(path: &Path, data: &[u8]) -> std::io::Result<()> {
    let tmp_path = path.with_extension("tmp");
    let mut f = fs::File::create(&tmp_path)?;
    f.write_all(data)?;
    f.sync_all()?;
    fs::rename(&tmp_path, path)?;
    Ok(())
}

/// Write the cache manifest to disk.
pub fn write_manifest(
    cache_dir: &Path,
    manifest: &CacheManifest,
) -> Result<(), CranelispError> {
    fs::create_dir_all(cache_dir).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to create cache dir: {}", e),
        span: (0, 0),
    })?;
    let path = cache_dir.join("manifest.json");
    let json = serde_json::to_string_pretty(manifest).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to serialize manifest: {}", e),
            span: (0, 0),
        }
    })?;
    atomic_write(&path, json.as_bytes()).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to write manifest: {}", e),
        span: (0, 0),
    })?;
    Ok(())
}

/// Read a cached CompiledModule from disk.
pub fn read_cached_module(
    cache_dir: &Path,
    module_path: &ModuleFullPath,
) -> Option<CompiledModule> {
    let filename = module_file_name(module_path);
    let path = cache_dir.join(format!("{}.meta.json", filename));
    let content = fs::read_to_string(path).ok()?;
    serde_json::from_str(&content).ok()
}

/// Write a CompiledModule to the cache directory.
pub fn write_cached_module(
    cache_dir: &Path,
    module_path: &ModuleFullPath,
    module: &CompiledModule,
) -> Result<(), CranelispError> {
    fs::create_dir_all(cache_dir).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to create cache dir: {}", e),
        span: (0, 0),
    })?;
    let filename = module_file_name(module_path);
    let path = cache_dir.join(format!("{}.meta.json", filename));
    let json = serde_json::to_string_pretty(module).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to serialize module: {}", e),
            span: (0, 0),
        }
    })?;
    atomic_write(&path, json.as_bytes()).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to write cached module: {}", e),
        span: (0, 0),
    })?;
    Ok(())
}

/// Read cached object file bytes.
pub fn read_cached_object(cache_dir: &Path, module_path: &ModuleFullPath) -> Option<Vec<u8>> {
    let filename = module_file_name(module_path);
    let path = cache_dir.join(format!("{}.o", filename));
    fs::read(path).ok()
}

/// Write object file bytes to cache.
pub fn write_cached_object(
    cache_dir: &Path,
    module_path: &ModuleFullPath,
    bytes: &[u8],
) -> Result<(), CranelispError> {
    fs::create_dir_all(cache_dir).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to create cache dir: {}", e),
        span: (0, 0),
    })?;
    let filename = module_file_name(module_path);
    let path = cache_dir.join(format!("{}.o", filename));
    atomic_write(&path, bytes).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to write object file: {}", e),
        span: (0, 0),
    })?;
    Ok(())
}

/// Sanitize a module path into a filesystem-safe name.
pub fn module_file_name(module_path: &ModuleFullPath) -> String {
    if module_path.is_root() {
        "_root".to_string()
    } else {
        module_path.0.replace('.', "_")
    }
}

// ── ObjectModule compilation ────────────────────────────────────────────

/// Compile a module's definitions to a relocatable object file (.o).
///
/// Uses the same `compile_function_indirect` as the JIT path, but targets
/// `ObjectModule` instead of `JITModule`. The GOT base address becomes a
/// data symbol reference (resolved at link time) instead of an embedded constant.
///
/// Takes pre-extracted `CacheInputs` instead of the full `modules` map,
/// making this function callable from a background thread (no non-Send pointers).
#[allow(clippy::too_many_arguments)]
pub fn compile_module_to_object(
    module_path: &ModuleFullPath,
    defns: &[(&crate::ast::Defn, &crate::types::Scheme)],
    method_resolutions: &MethodResolutions,
    fn_slots_base: &HashMap<String, FnSlot>,
    fn_to_module: &HashMap<String, String>,
    primitive_entries: &[PrimitiveEntry],
    global_names: &std::collections::HashSet<String>,
    builtin_method_info: &HashMap<String, (String, usize)>,
    trait_method_names: &std::collections::HashSet<String>,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&HashMap<String, String>>,
    expr_types: &HashMap<Span, Type>,
    alloc_jit_name: &str,
    free_jit_name: &str,
    panic_jit_name: &str,
    par_eval_jit_name: &str,
    ivar_create_jit_name: &str,
    ivar_spark_jit_name: &str,
    ivar_force_jit_name: &str,
    next_got_slot: usize,
) -> Result<Vec<u8>, CranelispError> {
    // Create ObjectModule with the same ISA as the JIT
    let mut flag_builder = settings::builder();
    // ObjectModule needs PIC mode for relocatable code
    flag_builder
        .set("is_pic", "true")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set flag: {}", e),
            span: (0, 0),
        })?;
    let isa_builder =
        cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
            message: format!("host not supported: {}", msg),
            span: (0, 0),
        })?;
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to build ISA: {}", e),
            span: (0, 0),
        })?;

    let obj_builder = ObjectBuilder::new(
        isa,
        format!("cranelisp_{}", module_path),
        default_libcall_names(),
    )
    .map_err(|e| CranelispError::CodegenError {
        message: format!("failed to create ObjectBuilder: {}", e),
        span: (0, 0),
    })?;
    let mut obj_module = ObjectModule::new(obj_builder);

    // Declare per-module GOT base data symbols.
    // Each module has its own GOT table; functions reference their own module's GOT.
    // fn_to_module is pre-extracted: maps function name → owning module short name.
    let self_mod_short = module_path.short_name().to_string();
    let mut got_data_ids: HashMap<String, cranelift_module::DataId> = HashMap::new();
    for mod_short in fn_to_module.values() {
        if got_data_ids.contains_key(mod_short) {
            continue;
        }
        let mod_fp = ModuleFullPath::from(mod_short.as_str());
        let got_symbol_name = format!("__cranelisp_got_{}", module_file_name(&mod_fp));
        let is_self = *mod_short == self_mod_short;
        let data_id = obj_module
            .declare_data(&got_symbol_name, if is_self { Linkage::Export } else { Linkage::Import }, is_self, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare GOT data symbol '{}': {}", got_symbol_name, e),
                span: (0, 0),
            })?;
        got_data_ids.insert(mod_short.clone(), data_id);
    }
    // Ensure current module's GOT is declared even if no functions reference it yet
    if !got_data_ids.contains_key(&self_mod_short) && !defns.is_empty() {
        let got_symbol_name = format!("__cranelisp_got_{}", module_file_name(module_path));
        let data_id = obj_module
            .declare_data(&got_symbol_name, Linkage::Export, true, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare GOT data symbol '{}': {}", got_symbol_name, e),
                span: (0, 0),
            })?;
        got_data_ids.insert(self_mod_short.clone(), data_id);
    }

    // Declare intrinsics as imported functions
    let alloc_func_id = declare_imported_func(&mut obj_module, alloc_jit_name, 1, 1)?;
    let free_func_id = declare_imported_func(&mut obj_module, free_jit_name, 1, 1)?;
    let panic_func_id = declare_imported_func(&mut obj_module, panic_jit_name, 1, 1)?;
    let par_eval_func_id = declare_imported_func(&mut obj_module, par_eval_jit_name, 2, 1)?;
    let ivar_create_func_id =
        declare_imported_func(&mut obj_module, ivar_create_jit_name, 1, 1)?;
    let ivar_spark_func_id =
        declare_imported_func(&mut obj_module, ivar_spark_jit_name, 1, 1)?;
    let ivar_force_func_id =
        declare_imported_func(&mut obj_module, ivar_force_jit_name, 1, 1)?;

    // Declare builtin methods as imported functions (using correct JIT names and param counts)
    let mut obj_builtin_methods = HashMap::new();
    for (user_name, (jit_name, param_count)) in builtin_method_info {
        let fid = declare_imported_func(&mut obj_module, jit_name, *param_count, 1)?;
        obj_builtin_methods.insert(user_name.clone(), fid);
    }

    // Declare ALL primitive entries (including platform functions).
    // This ensures ResolvedCall::BuiltinFn can find the correct ObjectModule FuncIds.
    for pe in primitive_entries {
        // Skip if already declared via builtin_method_info
        if obj_builtin_methods.contains_key(&pe.user_name) {
            continue;
        }
        let fid = declare_imported_func(&mut obj_module, &pe.jit_name, pe.param_count, 1)?;
        obj_builtin_methods.insert(pe.user_name.clone(), fid);
    }

    // Pass 1: Declare all exported functions (get FuncIds before GOT data definition)
    let mut declared_func_ids: Vec<FuncId> = Vec::new();
    for (defn, _scheme) in defns {
        let mut sig = obj_module.make_signature();
        for _ in &defn.params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = obj_module
            .declare_function(&defn.name, Linkage::Export, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare function '{}': {}", defn.name, e),
                span: defn.span,
            })?;
        declared_func_ids.push(func_id);
    }

    // Define current module's GOT data with function-address relocations.
    // Build slot→FuncId mapping from defns + fn_slots_base (no CompiledModule lookup needed).
    if let Some(self_got_data_id) = got_data_ids.get(&self_mod_short).copied() {
        if next_got_slot > 0 {
            // Build name→FuncId mapping from the functions we just declared
            let name_to_func_id: HashMap<&str, FuncId> = defns
                .iter()
                .zip(declared_func_ids.iter())
                .map(|((defn, _), &fid)| (defn.name.as_str(), fid))
                .collect();

            // Build slot→FuncId mapping from fn_slots_base for self-module functions
            let mut slot_to_func_id: HashMap<usize, FuncId> = HashMap::new();
            for (name, fn_slot) in fn_slots_base {
                // Only include functions owned by this module
                if fn_to_module.get(name).is_some_and(|m| *m == self_mod_short) {
                    if let Some(&fid) = name_to_func_id.get(name.as_str()) {
                        slot_to_func_id.insert(fn_slot.slot, fid);
                    }
                }
            }

            let mut data_desc = cranelift_module::DataDescription::new();
            // Use `define` (not `define_zeroinit`) so the GOT lands in __DATA,__data
            // instead of __DATA,__bss. BSS sections have no file-backed content, so
            // the system linker (ld) crashes (SIGSEGV) when applying relocations to
            // BSS on macOS. Using explicit zero bytes gives us a real data section
            // that can hold the function-address relocations added below.
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
                    message: format!("failed to define GOT data: {:?}", e),
                    span: (0, 0),
                })?;
        }
    }

    // Build fn_slots with per-module DataSymbol GOT references for ObjectModule
    let mut obj_fn_slots: HashMap<String, FnSlot> = HashMap::new();
    for (name, slot) in fn_slots_base {
        // Look up which module this function belongs to, use that module's GOT data symbol
        let data_id = fn_to_module
            .get(name)
            .and_then(|mod_short| got_data_ids.get(mod_short))
            .copied()
            .unwrap_or_else(|| {
                // Fallback: use the current module's GOT (for local functions)
                *got_data_ids
                    .get(&self_mod_short)
                    .unwrap_or_else(|| {
                        panic!(
                            "no GOT data symbol for function '{}' (module '{}' not found in {:?})",
                            name, module_file_name(module_path), got_data_ids.keys().collect::<Vec<_>>()
                        )
                    })
            });
        obj_fn_slots.insert(
            name.clone(),
            FnSlot {
                got_ref: GotReference::DataSymbol(data_id),
                slot: slot.slot,
                param_count: slot.param_count,
            },
        );
    }

    // Build a minimal modules map for compile_function_indirect.
    // Only needed for build_liveness_globals (primitive + special form name collection).
    // FnCompiler's fallback module lookups for func_ids won't find entries here
    // (func_id: None), but obj_builtin_methods already has all required ObjectModule FuncIds.
    let minimal_modules = build_minimal_modules_for_codegen(global_names);

    // Pass 2: Define (compile) each function
    let mut func_ctx = FunctionBuilderContext::new();
    for ((defn, _scheme), &func_id) in defns.iter().zip(declared_func_ids.iter()) {
        let mut sig = obj_module.make_signature();
        for _ in &defn.params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let mut func = cranelift::codegen::ir::Function::with_name_signature(
            cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
            sig,
        );

        let param_types = match &_scheme.ty {
            crate::types::Type::Fn(params, _) => params.clone(),
            _ => Vec::new(),
        };
        compile_function_indirect(
            defn,
            &mut func,
            &mut func_ctx,
            &mut obj_module,
            alloc_func_id,
            free_func_id,
            par_eval_func_id,
            ivar_create_func_id,
            ivar_spark_func_id,
            ivar_force_func_id,
            &obj_fn_slots,
            method_resolutions,
            None,
            &obj_builtin_methods,
            &minimal_modules,
            trait_method_names,
            type_defs,
            constructor_to_type,
            Some(panic_func_id),
            expr_types,
            &param_types,
        )?;

        let mut ctx = cranelift::codegen::Context::for_function(func);
        obj_module
            .define_function(func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define function '{}': {:?}", defn.name, e),
                span: defn.span,
            })?;
    }

    // Emit the object file
    let product = obj_module.finish();
    let bytes = product.emit().map_err(|e| CranelispError::CodegenError {
        message: format!("failed to emit object file: {}", e),
        span: (0, 0),
    })?;

    Ok(bytes)
}

/// Build a minimal modules map containing only Primitive/SpecialForm name entries.
/// Used by `compile_function_indirect` for liveness globals computation.
/// The entries have `func_id: None` since ObjectModule uses its own FuncIds via
/// `obj_builtin_methods`.
fn build_minimal_modules_for_codegen(
    global_names: &std::collections::HashSet<String>,
) -> HashMap<ModuleFullPath, CompiledModule> {
    use crate::module::{DefKind, ModuleEntry};
    use crate::names::Symbol;
    use crate::types::Scheme;

    let mut cm = CompiledModule::new(ModuleFullPath::from("_cache_globals"));
    for name in global_names {
        cm.symbols.insert(
            Symbol::from(name.as_str()),
            ModuleEntry::Def {
                scheme: Scheme::mono(Type::Int), // placeholder — not used for liveness
                visibility: crate::ast::Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: DefKind::SpecialForm {
                    description: String::new(),
                },
                meta: None,
            },
        );
    }
    let mut map = HashMap::new();
    map.insert(ModuleFullPath::from("_cache_globals"), cm);
    map
}

/// Declare an imported function in an ObjectModule.
fn declare_imported_func(
    module: &mut ObjectModule,
    name: &str,
    param_count: usize,
    return_count: usize,
) -> Result<FuncId, CranelispError> {
    let mut sig = module.make_signature();
    for _ in 0..param_count {
        sig.params.push(AbiParam::new(types::I64));
    }
    for _ in 0..return_count {
        sig.returns.push(AbiParam::new(types::I64));
    }
    module
        .declare_function(name, Linkage::Import, &sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare imported function '{}': {}", name, e),
            span: (0, 0),
        })
}

// ── fn_slots filtering for deterministic cache ─────────────────────────

/// Filter fn_slots to only include functions from modules reachable by the
/// given module (self + transitive imports + synthetic modules). This ensures
/// the compiled .o is deterministic regardless of what other unrelated modules
/// happen to be loaded in the JIT session.
pub fn filter_fn_slots_for_module(
    mod_path: &ModuleFullPath,
    all_fn_slots: &HashMap<String, FnSlot>,
    modules: &HashMap<ModuleFullPath, CompiledModule>,
) -> HashMap<String, FnSlot> {
    use std::collections::HashSet;

    // Collect transitive dependency module paths
    let mut relevant = HashSet::new();
    collect_module_deps(mod_path, modules, &mut relevant);

    // Build set of function names from relevant modules
    let mut relevant_fn_names: HashSet<String> = HashSet::new();
    for dep_path in &relevant {
        if let Some(cm) = modules.get(dep_path) {
            let mod_name = dep_path.short_name();
            for (sym, entry) in &cm.symbols {
                if let crate::module::ModuleEntry::Def {
                    kind: crate::module::DefKind::UserFn {
                        codegen: crate::module::DefCodegen {
                            got_slot: Some(_),
                            ..
                        },
                        ..
                    },
                    ..
                } = entry
                {
                    relevant_fn_names.insert(sym.to_string());
                    relevant_fn_names.insert(format!("{}/{}", mod_name, sym));
                }
            }
        }
    }

    // Filter fn_slots to only include relevant entries
    all_fn_slots
        .iter()
        .filter(|(name, _)| relevant_fn_names.contains(name.as_str()))
        .map(|(name, slot)| (name.clone(), slot.clone()))
        .collect()
}

fn collect_module_deps(
    mod_path: &ModuleFullPath,
    modules: &HashMap<ModuleFullPath, CompiledModule>,
    visited: &mut std::collections::HashSet<ModuleFullPath>,
) {
    if !visited.insert(mod_path.clone()) {
        return;
    }
    if let Some(cm) = modules.get(mod_path) {
        for import_spec in &cm.import_specs {
            let dep_path = ModuleFullPath::from(import_spec.module_path.as_str());
            collect_module_deps(&dep_path, modules, visited);
        }
    }
}

// ── Shared cache write helper ────────────────────────────────────────────

/// Write a module's cache files (.meta.json and .o) using data from CompiledModule.
/// Best-effort: logs warnings on failure, doesn't propagate errors.
/// Callers are responsible for clearing transient cache fields afterwards if needed.
#[allow(clippy::too_many_arguments)]
pub fn write_module_cache(
    cache_dir: &Path,
    mod_path: &ModuleFullPath,
    mod_name: &str,
    modules: &mut HashMap<ModuleFullPath, CompiledModule>,
    fn_slots: &HashMap<String, FnSlot>,
    builtin_method_info: &HashMap<String, (String, usize)>,
    trait_method_names: &std::collections::HashSet<String>,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&HashMap<String, String>>,
) {
    // Write CompiledModule metadata (.meta.json)
    if let Some(cm) = modules.get(mod_path) {
        if let Err(e) = write_cached_module(cache_dir, mod_path, cm) {
            eprintln!("warning: failed to write cache for {}: {}", mod_name, e);
        }
    }

    // Extract defn refs and cache transients for .o compilation
    let (defn_data, cache_mr, cache_et, next_slot) = {
        if let Some(cm) = modules.get(mod_path) {
            let defns: Vec<(crate::ast::Defn, crate::types::Scheme)> = cm
                .compiled_defns()
                .into_iter()
                .map(|(d, s)| (d.clone(), s.clone()))
                .collect();
            let mr = cm.cache_method_resolutions.clone();
            let et = cm.cache_expr_types.clone();
            let ns = cm.next_got_slot;
            (defns, mr, et, ns)
        } else {
            return;
        }
    };

    // Write .o file (only if there are compiled definitions)
    if !defn_data.is_empty() {
        // Extract cache inputs from modules (fn_to_module, primitive_entries, global_names)
        let cache_inputs = extract_cache_inputs(modules);
        let defn_refs: Vec<(&crate::ast::Defn, &crate::types::Scheme)> = defn_data
            .iter()
            .map(|(d, s)| (d, s))
            .collect();
        match compile_module_to_object(
            mod_path,
            &defn_refs,
            &cache_mr,
            fn_slots,
            &cache_inputs.fn_to_module,
            &cache_inputs.primitive_entries,
            &cache_inputs.global_names,
            builtin_method_info,
            trait_method_names,
            type_defs,
            constructor_to_type,
            &cache_et,
            "cranelisp_alloc",
            "cranelisp_free",
            "cranelisp_panic",
            "cranelisp_par_eval",
            "cranelisp_ivar_create",
            "cranelisp_ivar_spark",
            "cranelisp_ivar_force",
            next_slot,
        ) {
            Ok(obj_bytes) => {
                if let Err(e) = write_cached_object(cache_dir, mod_path, &obj_bytes) {
                    eprintln!("warning: failed to write .o cache for {}: {}", mod_name, e);
                }
            }
            Err(e) => {
                eprintln!("warning: failed to compile .o for cache {}: {}", mod_name, e);
            }
        }
    }

}

// ── Cache write packet (Send-able snapshot for background writes) ────────

/// An owned snapshot of all data needed to write a module's cache files.
/// All fields are owned (no borrowed pointers), making this Send-safe
/// for use with background threads or rayon parallel iterators.
pub struct CacheWritePacket {
    pub cache_dir: PathBuf,
    pub module_path: ModuleFullPath,
    pub meta_json_bytes: Vec<u8>,
    pub defn_data: Vec<(crate::ast::Defn, crate::types::Scheme)>,
    pub method_resolutions: MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
    pub fn_slots_snapshot: HashMap<String, (usize, usize)>, // fn name → (slot, param_count)
    pub fn_to_module: HashMap<String, String>,
    pub primitive_entries: Vec<PrimitiveEntry>,
    pub global_names: std::collections::HashSet<String>,
    pub builtin_method_info: HashMap<String, (String, usize)>,
    pub trait_method_names: std::collections::HashSet<String>,
    pub type_defs: Option<HashMap<String, TypeDefInfoCg>>,
    pub constructor_to_type: Option<HashMap<String, String>>,
    pub is_lib: bool,
    pub source_hash: String,
    pub next_got_slot: usize,
}

/// Build a `CacheWritePacket` by snapshotting data from the live session.
///
/// The `fn_slots` are converted to `(slot, param_count)` pairs since the
/// ObjectModule path creates its own `GotReference::DataSymbol` values.
/// `cache_inputs` should be pre-extracted via `extract_cache_inputs`.
#[allow(clippy::too_many_arguments)]
pub fn build_cache_packet(
    cache_dir: &Path,
    mod_path: &ModuleFullPath,
    modules: &HashMap<ModuleFullPath, CompiledModule>,
    fn_slots: &HashMap<String, FnSlot>,
    cache_inputs: &CacheInputs,
    builtin_method_info: &HashMap<String, (String, usize)>,
    trait_method_names: &std::collections::HashSet<String>,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&HashMap<String, String>>,
    is_lib: bool,
    source_hash: &str,
) -> Option<CacheWritePacket> {
    let cm = modules.get(mod_path)?;

    // Serialize CompiledModule to JSON bytes
    let meta_json_bytes = match serde_json::to_string_pretty(cm) {
        Ok(json) => json.into_bytes(),
        Err(e) => {
            eprintln!("warning: failed to serialize module {}: {}", mod_path, e);
            return None;
        }
    };

    // Clone defns and cache transients
    let defn_data: Vec<(crate::ast::Defn, crate::types::Scheme)> = cm
        .compiled_defns()
        .into_iter()
        .map(|(d, s)| (d.clone(), s.clone()))
        .collect();
    let method_resolutions = cm.cache_method_resolutions.clone();
    let expr_types = cm.cache_expr_types.clone();
    let next_got_slot = cm.next_got_slot;

    // Snapshot fn_slots as (slot, param_count) — GotReference is rebuilt by ObjectModule
    let fn_slots_snapshot: HashMap<String, (usize, usize)> = fn_slots
        .iter()
        .map(|(name, fs)| (name.clone(), (fs.slot, fs.param_count)))
        .collect();

    Some(CacheWritePacket {
        cache_dir: cache_dir.to_path_buf(),
        module_path: mod_path.clone(),
        meta_json_bytes,
        defn_data,
        method_resolutions,
        expr_types,
        fn_slots_snapshot,
        fn_to_module: cache_inputs.fn_to_module.clone(),
        primitive_entries: cache_inputs
            .primitive_entries
            .iter()
            .map(|pe| PrimitiveEntry {
                user_name: pe.user_name.clone(),
                jit_name: pe.jit_name.clone(),
                param_count: pe.param_count,
            })
            .collect(),
        global_names: cache_inputs.global_names.clone(),
        builtin_method_info: builtin_method_info.clone(),
        trait_method_names: trait_method_names.clone(),
        type_defs: type_defs.cloned(),
        constructor_to_type: constructor_to_type.cloned(),
        is_lib,
        source_hash: source_hash.to_string(),
        next_got_slot,
    })
}

/// Process a `CacheWritePacket`: compile the .o and write both .meta.json and .o to disk.
/// Returns `(module_path, source_hash, is_lib)` on success for manifest tracking.
pub fn process_cache_packet(
    packet: &CacheWritePacket,
) -> Option<(ModuleFullPath, String, bool)> {
    let mod_name = packet.module_path.short_name().to_string();

    // Write .meta.json
    if let Err(e) = fs::create_dir_all(&packet.cache_dir) {
        eprintln!("warning: failed to create cache dir for {}: {}", mod_name, e);
        return None;
    }
    let meta_path = packet
        .cache_dir
        .join(format!("{}.meta.json", module_file_name(&packet.module_path)));
    if let Err(e) = atomic_write(&meta_path, &packet.meta_json_bytes) {
        eprintln!("warning: failed to write .meta.json for {}: {}", mod_name, e);
        return None;
    }

    // Compile and write .o (only if there are definitions)
    if !packet.defn_data.is_empty() {
        // Reconstruct FnSlot map with placeholder GotReferences (ObjectModule replaces them)
        let fn_slots_base: HashMap<String, FnSlot> = packet
            .fn_slots_snapshot
            .iter()
            .map(|(name, (slot, param_count))| {
                (
                    name.clone(),
                    FnSlot {
                        got_ref: GotReference::Immediate(0), // placeholder
                        slot: *slot,
                        param_count: *param_count,
                    },
                )
            })
            .collect();

        let defn_refs: Vec<(&crate::ast::Defn, &crate::types::Scheme)> = packet
            .defn_data
            .iter()
            .map(|(d, s)| (d, s))
            .collect();

        match compile_module_to_object(
            &packet.module_path,
            &defn_refs,
            &packet.method_resolutions,
            &fn_slots_base,
            &packet.fn_to_module,
            &packet.primitive_entries,
            &packet.global_names,
            &packet.builtin_method_info,
            &packet.trait_method_names,
            packet.type_defs.as_ref(),
            packet.constructor_to_type.as_ref(),
            &packet.expr_types,
            "cranelisp_alloc",
            "cranelisp_free",
            "cranelisp_panic",
            "cranelisp_par_eval",
            "cranelisp_ivar_create",
            "cranelisp_ivar_spark",
            "cranelisp_ivar_force",
            packet.next_got_slot,
        ) {
            Ok(obj_bytes) => {
                if let Err(e) = write_cached_object(
                    &packet.cache_dir,
                    &packet.module_path,
                    &obj_bytes,
                ) {
                    eprintln!(
                        "warning: failed to write .o cache for {}: {}",
                        mod_name, e
                    );
                }
            }
            Err(e) => {
                eprintln!(
                    "warning: failed to compile .o for cache {}: {}",
                    mod_name, e
                );
            }
        }
    }

    Some((
        packet.module_path.clone(),
        packet.source_hash.clone(),
        packet.is_lib,
    ))
}

// ── Cache validation ────────────────────────────────────────────────────

/// Check if a cached manifest is compatible with the current runtime.
pub fn is_manifest_compatible(manifest: &CacheManifest) -> bool {
    // Cache format version check
    if manifest.cache_format_version != CACHE_FORMAT_VERSION {
        return false;
    }
    // Version check: must match exactly
    if manifest.cranelisp_version != env!("CARGO_PKG_VERSION") {
        return false;
    }
    // Binary fingerprint check: catches code changes, dependency updates, debug/release
    let current_fp = binary_fingerprint();
    if !current_fp.is_empty()
        && !manifest.binary_fingerprint.is_empty()
        && manifest.binary_fingerprint != current_fp
    {
        return false;
    }
    // Architecture check: must match
    if !manifest.target_triple.contains(std::env::consts::ARCH) {
        return false;
    }
    // OS check: handle the macos/darwin mismatch
    // std::env::consts::OS returns "macos" but Cranelift triples use "darwin"
    let os = std::env::consts::OS;
    if manifest.target_triple.contains(os) {
        return true;
    }
    if os == "macos" && manifest.target_triple.contains("darwin") {
        return true;
    }
    false
}
