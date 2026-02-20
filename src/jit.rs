use std::collections::{HashMap, HashSet};
use std::mem;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{default_libcall_names, FuncId, Linkage, Module};
use libloading::Library;

use crate::ast::{Defn, Expr, Program, Visibility};
use crate::codegen::{self, compile_function, compile_function_indirect, FnSlot, GotReference};
use crate::error::{CranelispError, Span};
use crate::intrinsics;
use crate::platform::{self, OwnedPlatformFnDescriptor};
use crate::primitives;
use crate::typechecker::{CheckResult, MethodResolutions, TypeChecker};
use crate::types::{Scheme, Type};

/// Wrapper to make raw pointers Send-safe for the dynamic symbol lookup closure.
struct SendPtr(*const u8);
unsafe impl Send for SendPtr {}
unsafe impl Sync for SendPtr {}

/// Metadata returned from compiling a function definition.
/// Contains codegen artifacts that can be stored in CompiledModule.
pub struct CompileMetadata {
    pub got_slot: usize,
    pub code_ptr: *const u8,
    pub clif_ir: String,
    pub disasm: Option<String>,
    pub code_size: Option<usize>,
    pub compile_duration: std::time::Duration,
    pub param_count: usize,
}

pub struct Jit {
    /// Loaded platform libraries. Must be declared before `module` for drop order
    /// (Rust drops fields in declaration order; Libraries must outlive JITModule).
    #[allow(dead_code)]
    loaded_libraries: Vec<Library>,
    /// Dynamic symbol table for platform functions loaded after JIT construction.
    dynamic_symbols: Arc<Mutex<HashMap<String, SendPtr>>>,
    module: JITModule,
    ctx: cranelift::codegen::Context,
    func_ctx: FunctionBuilderContext,
    alloc_func_id: FuncId,
    panic_func_id: FuncId,
    free_func_id: FuncId,
    /// Builtin trait method implementations (mangled name -> FuncId).
    builtin_methods: HashMap<String, FuncId>,
    /// Builtin method info: user name → (JIT symbol name, param count).
    /// Used by the cache system to declare correct imports in ObjectModule.
    builtin_method_info: HashMap<String, (String, usize)>,
    /// Trait method names (e.g., "show", "doubled") for globals in captures analysis.
    trait_method_names: HashSet<String>,
    /// Type definitions for ADT codegen (populated in REPL mode).
    type_defs_cg: Option<HashMap<String, codegen::TypeDefInfoCg>>,
    /// Constructor name → type name mapping (populated in REPL mode).
    constructor_to_type_cg: Option<HashMap<String, String>>,
}

/// Build the ISA for the current host architecture.
fn build_isa() -> Result<std::sync::Arc<dyn cranelift::codegen::isa::TargetIsa>, CranelispError> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("use_colocated_libcalls", "false")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set flag: {}", e),
            span: (0, 0),
        })?;
    flag_builder
        .set("is_pic", "false")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set flag: {}", e),
            span: (0, 0),
        })?;

    let isa_builder =
        cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
            message: format!("host not supported: {}", msg),
            span: (0, 0),
        })?;

    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to build ISA: {}", e),
            span: (0, 0),
        })
}

/// Register non-platform symbols (intrinsics, primitives, operators) on a JITBuilder.
fn register_non_platform_symbols(builder: &mut JITBuilder) {
    // Intrinsics
    builder.symbol("cranelisp_alloc", intrinsics::alloc as *const u8);
    builder.symbol("cranelisp_panic", intrinsics::panic as *const u8);
    builder.symbol("cranelisp_free", intrinsics::free as *const u8);

    // Extern primitive FFI symbols
    builder.symbol("int-to-string", primitives::int_to_string as *const u8);
    builder.symbol("bool-to-string", primitives::bool_to_string as *const u8);
    builder.symbol("string-identity", primitives::string_identity as *const u8);
    builder.symbol("float-to-string", primitives::float_to_string as *const u8);
    builder.symbol("parse-int", primitives::parse_int as *const u8);
    builder.symbol("str-concat", primitives::str_concat as *const u8);
    builder.symbol("quote-sexp", crate::marshal::quote_sexp as *const u8);
    builder.symbol("vec-get", primitives::vec_get as *const u8);
    builder.symbol("vec-set", primitives::vec_set as *const u8);
    builder.symbol("vec-push", primitives::vec_push as *const u8);
    builder.symbol("vec-len", primitives::vec_len as *const u8);
    builder.symbol("vec-map", primitives::vec_map as *const u8);
    builder.symbol("vec-reduce", primitives::vec_reduce as *const u8);

    // Operator wrapper symbols
    for (sym_name, func_ptr) in &[
        ("cranelisp_op_add", primitives::op_add as *const u8),
        ("cranelisp_op_sub", primitives::op_sub as *const u8),
        ("cranelisp_op_mul", primitives::op_mul as *const u8),
        ("cranelisp_op_div", primitives::op_div as *const u8),
        ("cranelisp_op_eq", primitives::op_eq as *const u8),
        ("cranelisp_op_lt", primitives::op_lt as *const u8),
        ("cranelisp_op_gt", primitives::op_gt as *const u8),
        ("cranelisp_op_le", primitives::op_le as *const u8),
        ("cranelisp_op_ge", primitives::op_ge as *const u8),
        ("cranelisp_op_fadd", primitives::op_fadd as *const u8),
        ("cranelisp_op_fsub", primitives::op_fsub as *const u8),
        ("cranelisp_op_fmul", primitives::op_fmul as *const u8),
        ("cranelisp_op_fdiv", primitives::op_fdiv as *const u8),
        ("cranelisp_op_feq", primitives::op_feq as *const u8),
        ("cranelisp_op_flt", primitives::op_flt as *const u8),
        ("cranelisp_op_fgt", primitives::op_fgt as *const u8),
        ("cranelisp_op_fle", primitives::op_fle as *const u8),
        ("cranelisp_op_fge", primitives::op_fge as *const u8),
    ] {
        builder.symbol(*sym_name, *func_ptr);
    }
}

/// Declare non-platform functions (intrinsics, primitives, operators) on the JIT module.
/// Returns (alloc_func_id, panic_func_id, free_func_id, builtin_methods, builtin_method_info).
#[allow(clippy::type_complexity)]
fn declare_non_platform_functions(
    module: &mut JITModule,
) -> Result<
    (
        FuncId,
        FuncId,
        FuncId,
        HashMap<String, FuncId>,
        HashMap<String, (String, usize)>,
    ),
    CranelispError,
> {
    // Declare alloc builtin: i64 -> i64
    let mut alloc_sig = module.make_signature();
    alloc_sig.params.push(AbiParam::new(types::I64));
    alloc_sig.returns.push(AbiParam::new(types::I64));
    let alloc_func_id = module
        .declare_function("cranelisp_alloc", Linkage::Import, &alloc_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare alloc builtin: {}", e),
            span: (0, 0),
        })?;

    // Declare panic builtin: i64 -> i64
    let mut panic_sig = module.make_signature();
    panic_sig.params.push(AbiParam::new(types::I64));
    panic_sig.returns.push(AbiParam::new(types::I64));
    let panic_func_id = module
        .declare_function("cranelisp_panic", Linkage::Import, &panic_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare panic builtin: {}", e),
            span: (0, 0),
        })?;

    // Declare free builtin: i64 -> i64 (no-op for v1 RC)
    let mut free_sig = module.make_signature();
    free_sig.params.push(AbiParam::new(types::I64));
    free_sig.returns.push(AbiParam::new(types::I64));
    let free_func_id = module
        .declare_function("cranelisp_free", Linkage::Import, &free_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare free builtin: {}", e),
            span: (0, 0),
        })?;

    // Declare extern primitive functions: i64 -> i64
    let mut builtin_methods = HashMap::new();
    let mut builtin_method_info: HashMap<String, (String, usize)> = HashMap::new();
    for name in &[
        "int-to-string",
        "bool-to-string",
        "string-identity",
        "float-to-string",
        "parse-int",
        "quote-sexp",
    ] {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern primitive '{}': {}", name, e),
                span: (0, 0),
            })?;
        builtin_methods.insert(name.to_string(), func_id);
        builtin_method_info.insert(name.to_string(), (name.to_string(), 1));
    }

    // Declare str-concat: (i64, i64) -> i64
    {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function("str-concat", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare str-concat: {}", e),
                span: (0, 0),
            })?;
        builtin_methods.insert("str-concat".to_string(), fid);
        builtin_method_info.insert("str-concat".to_string(), ("str-concat".to_string(), 2));
    }

    // Declare Vec primitive functions with varying signatures
    {
        // vec-get: (i64, i64) -> i64
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function("vec-get", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare vec-get: {}", e),
                span: (0, 0),
            })?;
        builtin_methods.insert("vec-get".to_string(), fid);
        builtin_method_info.insert("vec-get".to_string(), ("vec-get".to_string(), 2));
    }
    {
        // vec-set: (i64, i64, i64) -> i64
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function("vec-set", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare vec-set: {}", e),
                span: (0, 0),
            })?;
        builtin_methods.insert("vec-set".to_string(), fid);
        builtin_method_info.insert("vec-set".to_string(), ("vec-set".to_string(), 3));
    }
    {
        // vec-push: (i64, i64) -> i64
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function("vec-push", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare vec-push: {}", e),
                span: (0, 0),
            })?;
        builtin_methods.insert("vec-push".to_string(), fid);
        builtin_method_info.insert("vec-push".to_string(), ("vec-push".to_string(), 2));
    }
    {
        // vec-len: (i64) -> i64
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function("vec-len", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare vec-len: {}", e),
                span: (0, 0),
            })?;
        builtin_methods.insert("vec-len".to_string(), fid);
        builtin_method_info.insert("vec-len".to_string(), ("vec-len".to_string(), 1));
    }
    {
        // vec-map: (i64, i64) -> i64
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function("vec-map", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare vec-map: {}", e),
                span: (0, 0),
            })?;
        builtin_methods.insert("vec-map".to_string(), fid);
        builtin_method_info.insert("vec-map".to_string(), ("vec-map".to_string(), 2));
    }
    {
        // vec-reduce: (i64, i64, i64) -> i64
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function("vec-reduce", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare vec-reduce: {}", e),
                span: (0, 0),
            })?;
        builtin_methods.insert("vec-reduce".to_string(), fid);
        builtin_method_info.insert("vec-reduce".to_string(), ("vec-reduce".to_string(), 3));
    }

    // Declare operator wrapper functions: (i64, i64) -> i64, keyed by operator symbol
    for (op_sym, c_name) in &[
        ("+", "cranelisp_op_add"),
        ("-", "cranelisp_op_sub"),
        ("*", "cranelisp_op_mul"),
        ("/", "cranelisp_op_div"),
        ("=", "cranelisp_op_eq"),
        ("<", "cranelisp_op_lt"),
        (">", "cranelisp_op_gt"),
        ("<=", "cranelisp_op_le"),
        (">=", "cranelisp_op_ge"),
    ] {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(c_name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare operator '{}': {}", op_sym, e),
                span: (0, 0),
            })?;
        builtin_methods.insert(op_sym.to_string(), func_id);
        builtin_method_info.insert(op_sym.to_string(), (c_name.to_string(), 2));
    }

    Ok((
        alloc_func_id,
        panic_func_id,
        free_func_id,
        builtin_methods,
        builtin_method_info,
    ))
}

/// Declare platform functions from owned descriptors on the JIT module.
fn declare_platform_functions_owned(
    module: &mut JITModule,
    descriptors: &[OwnedPlatformFnDescriptor],
) -> Result<(), CranelispError> {
    for func in descriptors {
        let mut sig = module.make_signature();
        for _ in 0..func.param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let _func_id = module
            .declare_function(&func.jit_name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare platform fn '{}': {}", func.name, e),
                span: (0, 0),
            })?;
    }
    Ok(())
}

/// Load a platform DLL and extract its manifest + function descriptors.
/// Returns (library, name, version, descriptors).
fn load_platform_dll(
    path: &std::path::Path,
) -> Result<(Library, String, String, Vec<OwnedPlatformFnDescriptor>), CranelispError> {
    let lib = unsafe { Library::new(path) }.map_err(|e| CranelispError::CodegenError {
        message: format!("failed to load platform library: {}", e),
        span: (0, 0),
    })?;

    // Get manifest function
    let manifest_fn: libloading::Symbol<
        extern "C" fn(*const platform::HostCallbacksC) -> platform::PlatformManifestC,
    > = unsafe { lib.get(b"cranelisp_platform_manifest") }.map_err(|e| {
        CranelispError::CodegenError {
            message: format!("platform missing manifest function: {}", e),
            span: (0, 0),
        }
    })?;

    // Call manifest with host callbacks
    let callbacks = platform::HostCallbacksC {
        alloc: intrinsics::alloc,
    };
    let manifest = manifest_fn(&callbacks);

    // Check ABI version
    if manifest.abi_version != platform::ABI_VERSION {
        return Err(CranelispError::CodegenError {
            message: format!(
                "platform ABI version mismatch: platform has {}, host expects {}",
                manifest.abi_version,
                platform::ABI_VERSION
            ),
            span: (0, 0),
        });
    }

    // Extract descriptors
    let (name, version, descriptors) =
        unsafe { platform::manifest_to_descriptors(&manifest) }.map_err(|e| {
            CranelispError::CodegenError {
                message: e,
                span: (0, 0),
            }
        })?;

    Ok((lib, name, version, descriptors))
}

impl Jit {
    /// Create a JIT with no platform — platforms are loaded later via `load_platform()`.
    pub fn new() -> Result<Self, CranelispError> {
        let isa = build_isa()?;
        let mut builder = JITBuilder::with_isa(isa, default_libcall_names());

        // Register non-platform symbols (intrinsics, primitives, operators)
        register_non_platform_symbols(&mut builder);

        // Set up dynamic symbol lookup for platform functions loaded after construction
        let dynamic_symbols = Arc::new(Mutex::new(HashMap::<String, SendPtr>::new()));
        let syms = dynamic_symbols.clone();
        builder.symbol_lookup_fn(Box::new(move |name| {
            syms.lock().unwrap().get(name).map(|sp| sp.0)
        }));

        let mut module = JITModule::new(builder);
        let ctx = module.make_context();
        let func_ctx = FunctionBuilderContext::new();

        // Declare non-platform functions
        let (alloc_func_id, panic_func_id, free_func_id, builtin_methods, builtin_method_info) =
            declare_non_platform_functions(&mut module)?;

        Ok(Jit {
            loaded_libraries: Vec::new(),
            dynamic_symbols,
            module,
            ctx,
            func_ctx,
            alloc_func_id,
            panic_func_id,
            free_func_id,
            builtin_methods,
            builtin_method_info,
            trait_method_names: HashSet::new(),
            type_defs_cg: None,
            constructor_to_type_cg: None,
        })
    }

    /// Builtin method info for cache system: user name → (JIT symbol name, param count).
    pub fn builtin_method_info(&self) -> &HashMap<String, (String, usize)> {
        &self.builtin_method_info
    }

    /// Trait method names (globals for captures analysis).
    pub fn trait_method_names(&self) -> &HashSet<String> {
        &self.trait_method_names
    }

    /// Type definitions for ADT codegen.
    pub fn type_defs_cg(&self) -> Option<&HashMap<String, codegen::TypeDefInfoCg>> {
        self.type_defs_cg.as_ref()
    }

    /// Constructor name → type name mapping.
    pub fn constructor_to_type_cg(&self) -> Option<&HashMap<String, String>> {
        self.constructor_to_type_cg.as_ref()
    }

    /// Load a platform DLL at runtime.
    /// Returns the platform name, version, and function descriptors.
    pub fn load_platform(
        &mut self,
        path: &std::path::Path,
    ) -> Result<(String, String, Vec<OwnedPlatformFnDescriptor>), CranelispError> {
        let (lib, name, version, descriptors) = load_platform_dll(path)?;

        // Insert each function's (jit_name, fn_ptr) into dynamic_symbols
        {
            let mut syms = self.dynamic_symbols.lock().unwrap();
            for func in &descriptors {
                syms.insert(func.jit_name.clone(), SendPtr(func.ptr));
            }
        }

        // Declare platform functions on the JIT module
        declare_platform_functions_owned(&mut self.module, &descriptors)?;

        // Keep the library alive
        self.loaded_libraries.push(lib);

        Ok((name, version, descriptors))
    }

    /// Populate `func_id` on all `DefKind::Primitive` module entries that have a `jit_name`.
    /// Must be called after `Jit::new()` has declared all builtin FuncIds.
    pub fn populate_builtin_func_ids(
        &self,
        modules: &mut HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    ) {
        for cm in modules.values_mut() {
            for entry in cm.symbols.values_mut() {
                if let crate::module::ModuleEntry::Def {
                    kind:
                        crate::module::DefKind::Primitive {
                            jit_name: Some(jn),
                            func_id,
                            ..
                        },
                    ..
                } = entry
                {
                    // Look up the FuncId by JIT name. The function has already been declared
                    // during Jit::new(), so this is effectively a lookup (not a new declaration).
                    if let Ok(fid) = self.module.get_name(jn.as_ref()).ok_or(()).and_then(|name_id| {
                        if let cranelift_module::FuncOrDataId::Func(f) = name_id {
                            Ok(f)
                        } else {
                            Err(())
                        }
                    }) {
                        *func_id = Some(fid);
                    }
                }
            }
        }
    }

    /// Register a trait method name so it's treated as a global in captures analysis.
    pub fn register_trait_method(&mut self, name: &str) {
        self.trait_method_names.insert(name.to_string());
    }

    /// Register type definitions for ADT codegen (REPL mode).
    pub fn register_type_defs(&mut self, tc: &TypeChecker) {
        let all_type_defs = tc.collect_all_type_defs();
        let type_defs_cg = codegen::build_type_defs_cg(&all_type_defs);
        let constructor_to_type_cg = tc.collect_all_constructor_to_type();
        // Also register constructor names as trait method names (globals for captures)
        for ctor_name in constructor_to_type_cg.keys() {
            self.trait_method_names.insert(ctor_name.clone());
        }
        // Register accessor names as globals
        for td in type_defs_cg.values() {
            for ctor in &td.constructors {
                for fname in &ctor.fields {
                    self.trait_method_names.insert(fname.clone());
                }
            }
        }
        self.type_defs_cg = if type_defs_cg.is_empty() {
            None
        } else {
            Some(type_defs_cg)
        };
        self.constructor_to_type_cg = if constructor_to_type_cg.is_empty() {
            None
        } else {
            Some(constructor_to_type_cg)
        };
    }

    /// Register all runtime symbols with a linker for resolving cached .o files.
    /// This includes intrinsics, extern primitives, operator wrappers, and platform DLL symbols.
    pub fn register_runtime_symbols(&self, linker: &mut crate::linker::Linker) {
        // Intrinsics
        linker.register_symbol("cranelisp_alloc", intrinsics::alloc as *const u8);
        linker.register_symbol("cranelisp_panic", intrinsics::panic as *const u8);
        linker.register_symbol("cranelisp_free", intrinsics::free as *const u8);

        // Extern primitive FFI symbols
        linker.register_symbol("int-to-string", primitives::int_to_string as *const u8);
        linker.register_symbol("bool-to-string", primitives::bool_to_string as *const u8);
        linker.register_symbol("string-identity", primitives::string_identity as *const u8);
        linker.register_symbol("float-to-string", primitives::float_to_string as *const u8);
        linker.register_symbol("parse-int", primitives::parse_int as *const u8);
        linker.register_symbol("str-concat", primitives::str_concat as *const u8);
        linker.register_symbol("quote-sexp", crate::marshal::quote_sexp as *const u8);
        linker.register_symbol("vec-get", primitives::vec_get as *const u8);
        linker.register_symbol("vec-set", primitives::vec_set as *const u8);
        linker.register_symbol("vec-push", primitives::vec_push as *const u8);
        linker.register_symbol("vec-len", primitives::vec_len as *const u8);
        linker.register_symbol("vec-map", primitives::vec_map as *const u8);
        linker.register_symbol("vec-reduce", primitives::vec_reduce as *const u8);

        // Operator wrapper symbols
        for (sym_name, func_ptr) in &[
            ("cranelisp_op_add", primitives::op_add as *const u8),
            ("cranelisp_op_sub", primitives::op_sub as *const u8),
            ("cranelisp_op_mul", primitives::op_mul as *const u8),
            ("cranelisp_op_div", primitives::op_div as *const u8),
            ("cranelisp_op_eq", primitives::op_eq as *const u8),
            ("cranelisp_op_lt", primitives::op_lt as *const u8),
            ("cranelisp_op_gt", primitives::op_gt as *const u8),
            ("cranelisp_op_le", primitives::op_le as *const u8),
            ("cranelisp_op_ge", primitives::op_ge as *const u8),
            ("cranelisp_op_fadd", primitives::op_fadd as *const u8),
            ("cranelisp_op_fsub", primitives::op_fsub as *const u8),
            ("cranelisp_op_fmul", primitives::op_fmul as *const u8),
            ("cranelisp_op_fdiv", primitives::op_fdiv as *const u8),
            ("cranelisp_op_feq", primitives::op_feq as *const u8),
            ("cranelisp_op_flt", primitives::op_flt as *const u8),
            ("cranelisp_op_fgt", primitives::op_fgt as *const u8),
            ("cranelisp_op_fle", primitives::op_fle as *const u8),
            ("cranelisp_op_fge", primitives::op_fge as *const u8),
        ] {
            linker.register_symbol(sym_name, *func_ptr);
        }

        // Platform DLL symbols (loaded dynamically)
        if let Ok(syms) = self.dynamic_symbols.lock() {
            for (name, ptr) in syms.iter() {
                linker.register_symbol(name, ptr.0);
            }
        }
    }

    /// Build the FnSlot map from CompiledModule data.
    /// Each slot carries the GOT base address of its owning module.
    pub fn build_fn_slots_from_modules(
        &self,
        modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    ) -> HashMap<String, FnSlot> {
        let mut slots = HashMap::new();
        for (mod_path, cm) in modules {
            let got_addr = match cm.got_table_addr() {
                Some(addr) => addr,
                None => continue, // module has no GOT (no compiled functions)
            };
            let mod_name = mod_path.short_name();
            for (sym, entry) in &cm.symbols {
                if let crate::module::ModuleEntry::Def {
                    kind:
                        crate::module::DefKind::UserFn {
                            codegen:
                                crate::module::DefCodegen {
                                    got_slot: Some(slot),
                                    param_count: Some(pc),
                                    ..
                                },
                            ..
                        },
                    ..
                } = entry
                {
                    let fn_slot = FnSlot {
                        got_ref: GotReference::Immediate(got_addr),
                        slot: *slot,
                        param_count: *pc,
                    };
                    slots.insert(sym.to_string(), fn_slot.clone());
                    // Also add qualified name
                    let qualified = format!("{}/{}", mod_name, sym);
                    slots.insert(qualified, fn_slot);
                }
            }
        }
        slots
    }

    /// Compile a function definition for REPL mode.
    /// Caller provides a pre-allocated slot and pre-computed fn_slots.
    pub fn compile_defn(
        &mut self,
        defn: &Defn,
        _scheme: &Scheme,
        method_resolutions: &MethodResolutions,
        expr_types: &HashMap<Span, Type>,
        slot: usize,
        fn_slots: &HashMap<String, FnSlot>,
        modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    ) -> Result<CompileMetadata, CranelispError> {
        self.compile_defn_with_resolutions(
            defn,
            _scheme,
            method_resolutions,
            None,
            expr_types,
            slot,
            fn_slots,
            modules,
        )
    }

    pub fn compile_defn_with_resolutions(
        &mut self,
        defn: &Defn,
        _scheme: &Scheme,
        method_resolutions: &MethodResolutions,
        fn_specific_resolutions: Option<&MethodResolutions>,
        expr_types: &HashMap<Span, Type>,
        slot: usize,
        fn_slots: &HashMap<String, FnSlot>,
        modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    ) -> Result<CompileMetadata, CranelispError> {
        // Build signature
        let mut sig = self.module.make_signature();
        for _ in &defn.params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        // Use anonymous function to avoid DuplicateDefinition errors on redefinition
        let func_id = self.module.declare_anonymous_function(&sig).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to declare function '{}': {}", defn.name, e),
                span: defn.span,
            }
        })?;

        self.ctx.func.signature = sig;
        self.ctx.func.name = cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32());

        let alloc_fid = self.alloc_func_id;
        let panic_fid = self.panic_func_id;
        let free_fid = self.free_func_id;
        let trait_names = self.trait_method_names.clone();
        compile_function_indirect(
            defn,
            &mut self.ctx.func,
            &mut self.func_ctx,
            &mut self.module,
            alloc_fid,
            free_fid,
            fn_slots,
            method_resolutions,
            fn_specific_resolutions,
            &self.builtin_methods,
            modules,
            &trait_names,
            self.type_defs_cg.as_ref(),
            self.constructor_to_type_cg.as_ref(),
            Some(panic_fid),
            expr_types,
        )?;

        // Capture CLIF IR before compilation lowers it
        let clif_ir = format!("{}", self.ctx.func);

        // Enable disassembly capture
        self.ctx.set_disasm(true);

        let compile_start = Instant::now();

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define function '{}': {}", defn.name, e),
                span: defn.span,
            })?;

        // Capture disasm + code size after compilation, before clear_context
        let (disasm, code_size) = if let Some(compiled) = self.ctx.compiled_code() {
            (
                compiled.vcode.clone(),
                Some(compiled.code_info().total_size as usize),
            )
        } else {
            (None, None)
        };

        self.module.clear_context(&mut self.ctx);

        self.module
            .finalize_definitions()
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to finalize: {}", e),
                span: (0, 0),
            })?;

        let compile_duration = compile_start.elapsed();
        let code_ptr = self.module.get_finalized_function(func_id);

        Ok(CompileMetadata {
            got_slot: slot,
            code_ptr,
            clif_ir,
            disasm,
            code_size,
            compile_duration,
            param_count: defn.params.len(),
        })
    }

    /// Compile a function definition into a module's GOT (multi-module batch mode).
    /// Caller provides a pre-allocated slot and pre-computed fn_slots.
    #[allow(clippy::too_many_arguments)]
    pub fn compile_defn_in_module(
        &mut self,
        defn: &Defn,
        _scheme: &Scheme,
        method_resolutions: &MethodResolutions,
        _module_name: &str,
        expr_types: &HashMap<Span, Type>,
        slot: usize,
        fn_slots: &HashMap<String, FnSlot>,
        modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    ) -> Result<CompileMetadata, CranelispError> {
        // Build signature
        let mut sig = self.module.make_signature();
        for _ in &defn.params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self.module.declare_anonymous_function(&sig).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to declare function '{}': {}", defn.name, e),
                span: defn.span,
            }
        })?;

        self.ctx.func.signature = sig;
        self.ctx.func.name = cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32());

        let alloc_fid = self.alloc_func_id;
        let panic_fid = self.panic_func_id;
        let free_fid = self.free_func_id;
        let trait_names = self.trait_method_names.clone();
        compile_function_indirect(
            defn,
            &mut self.ctx.func,
            &mut self.func_ctx,
            &mut self.module,
            alloc_fid,
            free_fid,
            fn_slots,
            method_resolutions,
            None,
            &self.builtin_methods,
            modules,
            &trait_names,
            self.type_defs_cg.as_ref(),
            self.constructor_to_type_cg.as_ref(),
            Some(panic_fid),
            expr_types,
        )?;

        // Capture CLIF IR before compilation lowers it
        let clif_ir = format!("{}", self.ctx.func);

        self.ctx.set_disasm(true);

        let compile_start = Instant::now();

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| {
                eprintln!("CLIF IR for failed function '{}':\n{}", defn.name, clif_ir);
                CranelispError::CodegenError {
                    message: format!("failed to define function '{}': {}", defn.name, e),
                    span: defn.span,
                }
            })?;

        let (disasm, code_size) = if let Some(compiled) = self.ctx.compiled_code() {
            (
                compiled.vcode.clone(),
                Some(compiled.code_info().total_size as usize),
            )
        } else {
            (None, None)
        };

        self.module.clear_context(&mut self.ctx);

        self.module
            .finalize_definitions()
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to finalize: {}", e),
                span: (0, 0),
            })?;

        let compile_duration = compile_start.elapsed();
        let code_ptr = self.module.get_finalized_function(func_id);

        Ok(CompileMetadata {
            got_slot: slot,
            code_ptr,
            clif_ir,
            disasm,
            code_size,
            compile_duration,
            param_count: defn.params.len(),
        })
    }

    /// Call the compiled `main()` function. Used by multi-module batch mode.
    pub fn call_main(
        &self,
        modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    ) -> Result<(), CranelispError> {
        // Find "main" in any module
        for cm in modules.values() {
            if let Some(crate::module::ModuleEntry::Def {
                kind:
                    crate::module::DefKind::UserFn {
                        codegen:
                            crate::module::DefCodegen {
                                code_ptr: Some(ptr),
                                ..
                            },
                        ..
                    },
                ..
            }) = cm.get("main")
            {
                if !ptr.is_null() {
                    let main_fn =
                        unsafe { mem::transmute::<*const u8, extern "C" fn() -> i64>(*ptr) };
                    main_fn();
                    return Ok(());
                }
            }
        }
        Err(CranelispError::CodegenError {
            message: "no main function defined".to_string(),
            span: (0, 0),
        })
    }

    /// Evaluate a bare expression in REPL mode. Wraps it in an anonymous zero-arg function,
    /// compiles, executes, and returns the result.
    /// Caller provides pre-computed fn_slots.
    pub fn eval_expr(
        &mut self,
        expr: &Expr,
        method_resolutions: &MethodResolutions,
        expr_types: &HashMap<Span, Type>,
        fn_slots: &HashMap<String, FnSlot>,
        modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    ) -> Result<i64, CranelispError> {
        // Wrap the expression in a synthetic defn with no params
        let wrapper = Defn {
            visibility: Visibility::Public,
            name: "__repl_expr__".to_string(),
            docstring: None,
            params: vec![],
            param_annotations: vec![],
            body: expr.clone(),
            span: expr.span(),
        };

        let mut sig = self.module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self.module.declare_anonymous_function(&sig).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to declare eval wrapper: {}", e),
                span: expr.span(),
            }
        })?;

        self.ctx.func.signature = sig;
        self.ctx.func.name = cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32());

        let alloc_fid = self.alloc_func_id;
        let panic_fid = self.panic_func_id;
        let free_fid = self.free_func_id;
        let trait_names = self.trait_method_names.clone();
        compile_function_indirect(
            &wrapper,
            &mut self.ctx.func,
            &mut self.func_ctx,
            &mut self.module,
            alloc_fid,
            free_fid,
            fn_slots,
            method_resolutions,
            None,
            &self.builtin_methods,
            modules,
            &trait_names,
            self.type_defs_cg.as_ref(),
            self.constructor_to_type_cg.as_ref(),
            Some(panic_fid),
            expr_types,
        )?;

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define eval wrapper: {}", e),
                span: expr.span(),
            })?;

        self.module.clear_context(&mut self.ctx);

        self.module
            .finalize_definitions()
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to finalize: {}", e),
                span: (0, 0),
            })?;

        let code = self.module.get_finalized_function(func_id);
        let eval_fn = unsafe { mem::transmute::<*const u8, extern "C" fn() -> i64>(code) };
        Ok(eval_fn())
    }

    /// Compile and run a whole program (batch mode — direct calls, no fn_table).
    pub fn compile_and_run(
        &mut self,
        program: &Program,
        multi_defns: &[Defn],
        result: &CheckResult,
        tc: &TypeChecker,
    ) -> Result<i64, CranelispError> {
        let method_resolutions = &result.method_resolutions;

        // Build codegen type info from typechecker
        let all_type_defs = tc.collect_all_type_defs();
        let type_defs_cg = codegen::build_type_defs_cg(&all_type_defs);
        let constructor_to_type_cg = tc.collect_all_constructor_to_type();

        let program_defns = crate::ast::defns(program);
        let impl_method_defns = crate::ast::impl_method_defns(program);
        let mut all_defns: Vec<&Defn> = program_defns;
        for d in &impl_method_defns {
            all_defns.push(d);
        }
        for d in multi_defns {
            all_defns.push(d);
        }

        // Filter out constrained fns (they are compiled as monomorphised specializations)
        all_defns.retain(|d| !result.constrained_fn_names.contains(&d.name));

        // Add monomorphised defns
        for (md, _defining_mod) in &result.mono_defns {
            all_defns.push(&md.defn);
        }

        // Build mono resolution map for per-fn resolutions
        let mono_resolution_map: HashMap<&str, &MethodResolutions> = result
            .mono_defns
            .iter()
            .map(|(md, _)| (md.defn.name.as_str(), &md.resolutions))
            .collect();

        // Build combined extra_defns: multi_defns + mono defns
        // (needed so compile_function can discover all function names for direct calls)
        let mut combined_extra: Vec<Defn> = multi_defns.to_vec();
        for (md, _) in &result.mono_defns {
            combined_extra.push(md.defn.clone());
        }

        // Pass 1: Declare all functions
        let mut func_ids = Vec::new();
        for defn in &all_defns {
            let mut sig = self.module.make_signature();
            for _ in &defn.params {
                sig.params.push(AbiParam::new(types::I64));
            }
            sig.returns.push(AbiParam::new(types::I64));

            let func_id = self
                .module
                .declare_function(&defn.name, Linkage::Local, &sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare function '{}': {}", defn.name, e),
                    span: defn.span,
                })?;
            func_ids.push(func_id);
        }

        // Pass 2: Define all functions
        for (defn, &func_id) in all_defns.iter().zip(func_ids.iter()) {
            let mut sig = self.module.make_signature();
            for _ in &defn.params {
                sig.params.push(AbiParam::new(types::I64));
            }
            sig.returns.push(AbiParam::new(types::I64));

            self.ctx.func.signature = sig;
            self.ctx.func.name = cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32());

            // Use per-fn resolutions for monomorphised defns
            let fn_specific = mono_resolution_map.get(defn.name.as_str()).copied();

            let td_opt = if type_defs_cg.is_empty() {
                None
            } else {
                Some(&type_defs_cg)
            };
            let c2t_opt = if constructor_to_type_cg.is_empty() {
                None
            } else {
                Some(&constructor_to_type_cg)
            };
            compile_function(
                defn,
                program,
                &combined_extra,
                &mut self.ctx.func,
                &mut self.func_ctx,
                &mut self.module,
                self.alloc_func_id,
                self.free_func_id,
                method_resolutions,
                fn_specific,
                &self.builtin_methods,
                &tc.modules,
                td_opt,
                c2t_opt,
                Some(self.panic_func_id),
                &result.expr_types,
            )?;

            self.module
                .define_function(func_id, &mut self.ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define function '{}': {}", defn.name, e),
                    span: defn.span,
                })?;

            self.module.clear_context(&mut self.ctx);
        }

        // Finalize
        self.module
            .finalize_definitions()
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to finalize: {}", e),
                span: (0, 0),
            })?;

        // Find and call main
        let main_id = func_ids
            .iter()
            .zip(all_defns.iter())
            .find(|(_, d)| d.name == "main")
            .map(|(&id, _)| id)
            .ok_or_else(|| CranelispError::CodegenError {
                message: "no main function".to_string(),
                span: (0, 0),
            })?;

        let code = self.module.get_finalized_function(main_id);
        let main_fn = unsafe { mem::transmute::<*const u8, extern "C" fn() -> i64>(code) };
        Ok(main_fn())
    }
}
