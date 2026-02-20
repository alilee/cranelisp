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

/// SHA-256 fingerprint of the running cranelisp binary.
/// Changes on any rebuild, ensuring cached .o files match the current codegen.
fn binary_fingerprint() -> String {
    let exe = match std::env::current_exe() {
        Ok(p) => p,
        Err(_) => return String::new(),
    };
    let bytes = match std::fs::read(&exe) {
        Ok(b) => b,
        Err(_) => return String::new(),
    };
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    let result = hasher.finalize();
    hex_encode(&result)
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
#[allow(clippy::too_many_arguments)]
pub fn compile_module_to_object(
    module_path: &ModuleFullPath,
    defns: &[(&crate::ast::Defn, &crate::types::Scheme)],
    method_resolutions: &MethodResolutions,
    fn_slots_base: &HashMap<String, FnSlot>,
    modules: &HashMap<ModuleFullPath, CompiledModule>,
    builtin_method_info: &HashMap<String, (String, usize)>,
    trait_method_names: &std::collections::HashSet<String>,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&HashMap<String, String>>,
    expr_types: &HashMap<Span, Type>,
    alloc_jit_name: &str,
    free_jit_name: &str,
    panic_jit_name: &str,
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
    // Build a mapping: function name → module short name (for GOT data symbol lookup).
    let mut fn_to_module: HashMap<String, String> = HashMap::new();
    for (mod_path_key, cm) in modules {
        let mod_short = mod_path_key.short_name().to_string();
        for (sym, entry) in &cm.symbols {
            if let crate::module::ModuleEntry::Def {
                kind:
                    crate::module::DefKind::UserFn {
                        codegen:
                            crate::module::DefCodegen {
                                got_slot: Some(_), ..
                            },
                        ..
                    },
                ..
            } = entry
            {
                fn_to_module.insert(sym.to_string(), mod_short.clone());
                // Also qualified name
                fn_to_module.insert(format!("{}/{}", mod_short, sym), mod_short.clone());
            }
        }
    }

    // Declare GOT data symbols for all modules that have functions in fn_slots.
    // Current module's GOT: Linkage::Export (writable, defined with function-address relocations).
    // Other modules' GOTs: Linkage::Import (resolved by linker from those modules' .o files).
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

    // Declare builtin methods as imported functions (using correct JIT names and param counts)
    let mut obj_builtin_methods = HashMap::new();
    for (user_name, (jit_name, param_count)) in builtin_method_info {
        let fid = declare_imported_func(&mut obj_module, jit_name, *param_count, 1)?;
        obj_builtin_methods.insert(user_name.clone(), fid);
    }

    // Declare ALL primitive entries from all modules (including platform functions).
    // This ensures ResolvedCall::BuiltinFn can find the correct ObjectModule FuncIds.
    for cm in modules.values() {
        for (sym, entry) in &cm.symbols {
            if let crate::module::ModuleEntry::Def {
                kind:
                    crate::module::DefKind::Primitive {
                        jit_name: Some(jn),
                        ..
                    },
                scheme,
                ..
            } = entry
            {
                let user_name = sym.to_string();
                // Skip if already declared via builtin_method_info
                if obj_builtin_methods.contains_key(&user_name) {
                    continue;
                }
                // Derive param count from the type scheme
                let param_count = scheme.param_count();
                let fid = declare_imported_func(&mut obj_module, jn, param_count, 1)?;
                obj_builtin_methods.insert(user_name, fid);
            }
        }
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
    // Build slot→FuncId mapping from this module's CompiledModule symbols and declared FuncIds.
    if let Some(self_got_data_id) = got_data_ids.get(&self_mod_short).copied() {
        let self_cm = modules.get(module_path);
        let next_got_slot = self_cm.map(|cm| cm.next_got_slot).unwrap_or(0);

        if next_got_slot > 0 {
            // Build name→FuncId mapping from the functions we just declared
            let name_to_func_id: HashMap<&str, FuncId> = defns
                .iter()
                .zip(declared_func_ids.iter())
                .map(|((defn, _), &fid)| (defn.name.as_str(), fid))
                .collect();

            // Build slot→FuncId mapping from CompiledModule symbols
            let mut slot_to_func_id: HashMap<usize, FuncId> = HashMap::new();
            if let Some(cm) = self_cm {
                for (sym, entry) in &cm.symbols {
                    if let crate::module::ModuleEntry::Def {
                        kind:
                            crate::module::DefKind::UserFn {
                                codegen:
                                    crate::module::DefCodegen {
                                        got_slot: Some(slot),
                                        ..
                                    },
                                ..
                            },
                        ..
                    } = entry
                    {
                        if let Some(&fid) = name_to_func_id.get(sym.as_ref()) {
                            slot_to_func_id.insert(*slot, fid);
                        }
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

        compile_function_indirect(
            defn,
            &mut func,
            &mut func_ctx,
            &mut obj_module,
            alloc_func_id,
            free_func_id,
            &obj_fn_slots,
            method_resolutions,
            None,
            &obj_builtin_methods,
            modules,
            trait_method_names,
            type_defs,
            constructor_to_type,
            Some(panic_func_id),
            expr_types,
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
    let (defn_data, cache_mr, cache_et) = {
        if let Some(cm) = modules.get(mod_path) {
            let defns: Vec<(crate::ast::Defn, crate::types::Scheme)> = cm
                .compiled_defns()
                .into_iter()
                .map(|(d, s)| (d.clone(), s.clone()))
                .collect();
            let mr = cm.cache_method_resolutions.clone();
            let et = cm.cache_expr_types.clone();
            (defns, mr, et)
        } else {
            return;
        }
    };

    // Write .o file (only if there are compiled definitions)
    if !defn_data.is_empty() {
        // Need an immutable borrow of modules for compile_module_to_object
        let defn_refs: Vec<(&crate::ast::Defn, &crate::types::Scheme)> = defn_data
            .iter()
            .map(|(d, s)| (d, s))
            .collect();
        match compile_module_to_object(
            mod_path,
            &defn_refs,
            &cache_mr,
            fn_slots,
            modules,
            builtin_method_info,
            trait_method_names,
            type_defs,
            constructor_to_type,
            &cache_et,
            "cranelisp_alloc",
            "cranelisp_free",
            "cranelisp_panic",
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
