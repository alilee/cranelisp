// Cranelift ISA setup and JIT module lifecycle.
//
// Single ISA construction point. Addresses audit finding about
// multiple ISA constructions in the prototype.
//
// Ring 1: registers all runtime intrinsics by function pointer
// on the JITBuilder. Uses the naming convention from src/CLAUDE.md
// §"JIT Symbol Names".

use std::collections::HashMap;
use std::sync::Arc;

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_types::{
    CheckResult, CompileMode, CranelispError, Defn, Span, Symbol,
};

use crate::compiler::{CompileContext, CrossModuleGot, FnCompiler};

/// Build the ISA for the current host architecture.
///
/// Single construction point for the entire backend.
pub fn build_isa() -> Result<Arc<dyn cranelift::codegen::isa::TargetIsa>, CranelispError> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("use_colocated_libcalls", "false")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            span: Span::SYNTHETIC,
        })?;
    flag_builder
        .set("is_pic", "false")
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

/// Register all runtime intrinsics on a JITBuilder by function pointer.
///
/// Single source of truth for the JIT name -> function pointer mapping.
/// Addresses cache audit HIGH-1: one authoritative registry for both
/// JIT and (future) ObjectModule paths.
///
/// Convention: runtime infrastructure uses `runtime/name` prefix.
/// User-visible primitives use spec kebab-case names.
fn register_intrinsics(builder: &mut JITBuilder) {
    // Runtime infrastructure (internal, not user-callable)
    builder.symbol("runtime/alloc", cranelisp_runtime::heap_alloc as *const u8);
    builder.symbol("runtime/dealloc", cranelisp_runtime::heap_dealloc as *const u8);
    builder.symbol("runtime/panic", cranelisp_runtime::runtime_panic as *const u8);
    builder.symbol(
        "runtime/rc_underflow_check",
        cranelisp_runtime::rc_underflow_check as *const u8,
    );
    builder.symbol(
        "runtime/alloc_string",
        cranelisp_runtime::heap_alloc_string as *const u8,
    );
    builder.symbol(
        "runtime/string_read",
        cranelisp_runtime::string_read as *const u8,
    );

    // Vec runtime infrastructure
    builder.symbol("runtime/vec_new", cranelisp_runtime::vec_new as *const u8);
    builder.symbol("runtime/vec_drop", cranelisp_runtime::vec_drop as *const u8);

    // Vec extern primitives (user-visible and internal)
    builder.symbol("vec-len", cranelisp_runtime::vec_len as *const u8);
    builder.symbol("vec-set-copy", cranelisp_runtime::vec_set_copy as *const u8);
    builder.symbol("vec-push-copy", cranelisp_runtime::vec_push_copy as *const u8);
    builder.symbol("vec-push-grow", cranelisp_runtime::vec_push_grow as *const u8);

    // Extern primitives (user-visible via primitives module)
    builder.symbol("str-concat", cranelisp_runtime::str_concat as *const u8);
    builder.symbol("str-eq", cranelisp_runtime::str_eq as *const u8);
    builder.symbol("str-len", cranelisp_runtime::str_len as *const u8);
    builder.symbol("string-identity", cranelisp_runtime::string_identity as *const u8);
    builder.symbol("int-to-string", cranelisp_runtime::int_to_string as *const u8);
    builder.symbol("float-to-string", cranelisp_runtime::float_to_string as *const u8);
    builder.symbol("bool-to-string", cranelisp_runtime::bool_to_string as *const u8);
    builder.symbol("parse-int", cranelisp_runtime::parse_int as *const u8);

    // Marshal primitives (macros module + primitives module)
    builder.symbol("sconcat", cranelisp_runtime::sconcat as *const u8);
    builder.symbol("quote-sexp", cranelisp_runtime::quote_sexp as *const u8);
}

/// JIT module wrapper. Owns the Cranelift JIT module and provides
/// function compilation and execution services.
pub struct Jit {
    module: JITModule,
    ctx: cranelift::codegen::Context,
    func_ctx: FunctionBuilderContext,
    /// FuncId for `runtime/alloc` — needed by heap emission helpers.
    alloc_func_id: Option<FuncId>,
    /// FuncId for `runtime/dealloc` — needed by RC dec emission.
    dealloc_func_id: Option<FuncId>,
    /// FuncId for `runtime/alloc_string` — needed by string literal codegen.
    alloc_string_func_id: Option<FuncId>,
    /// FuncId for `runtime/panic` — needed for match exhaustiveness failure.
    panic_func_id: Option<FuncId>,
    /// FuncId for `runtime/vec_new` — needed by Vec literal codegen.
    vec_new_func_id: Option<FuncId>,
    /// FuncId for `runtime/vec_drop` — needed by Vec drop glue.
    vec_drop_func_id: Option<FuncId>,
}

impl Jit {
    /// Create a new JIT instance for the current host architecture.
    pub fn new() -> Result<Self, CranelispError> {
        Self::new_with_symbols(&[])
    }

    /// Create a new JIT instance with extra symbol registrations.
    ///
    /// Same as `new()` but pre-registers additional symbols on the
    /// JITBuilder before creating the module. This enables cross-module
    /// function calls (P4): when compiling module B that depends on
    /// module A, A's compiled function pointers are passed in as
    /// extra symbols so B can link against them.
    pub fn new_with_symbols(
        extra_symbols: &[(&str, *const u8)],
    ) -> Result<Self, CranelispError> {
        let isa = build_isa()?;

        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        register_intrinsics(&mut builder);

        // Register extra symbols from previously compiled JIT modules.
        for &(name, ptr) in extra_symbols {
            builder.symbol(name, ptr);
        }

        let module = JITModule::new(builder);

        let ctx = module.make_context();
        let func_ctx = FunctionBuilderContext::new();

        Ok(Jit {
            module,
            ctx,
            func_ctx,
            alloc_func_id: None,
            dealloc_func_id: None,
            alloc_string_func_id: None,
            panic_func_id: None,
            vec_new_func_id: None,
            vec_drop_func_id: None,
        })
    }

    /// Declare runtime intrinsics as imported functions in the JIT module.
    ///
    /// Must be called before compiling any function that needs heap operations.
    /// Returns the declared FuncIds for use by codegen.
    pub fn declare_intrinsics(&mut self) -> Result<IntrinsicIds, CranelispError> {
        let alloc_id = self.declare_import("runtime/alloc", 1, 1)?;
        let dealloc_id = self.declare_import("runtime/dealloc", 1, 1)?;
        let alloc_string_id = self.declare_import("runtime/alloc_string", 2, 1)?;
        let panic_id = self.declare_import_no_return("runtime/panic", 2)?;
        let vec_new_id = self.declare_import("runtime/vec_new", 1, 1)?;
        // vec_drop returns void in Rust, but we declare it with no returns for Cranelift.
        let vec_drop_id = self.declare_import_void("runtime/vec_drop", 2)?;

        self.alloc_func_id = Some(alloc_id);
        self.dealloc_func_id = Some(dealloc_id);
        self.alloc_string_func_id = Some(alloc_string_id);
        self.panic_func_id = Some(panic_id);
        self.vec_new_func_id = Some(vec_new_id);
        self.vec_drop_func_id = Some(vec_drop_id);

        Ok(IntrinsicIds {
            alloc: alloc_id,
            dealloc: dealloc_id,
            alloc_string: alloc_string_id,
            panic: panic_id,
            vec_new: vec_new_id,
            vec_drop: vec_drop_id,
        })
    }

    /// Declare all functions in the JIT module, returning a name->FuncId map.
    /// Used in Batch mode so functions can reference each other.
    pub fn declare_functions(
        &mut self,
        defns: &[&Defn],
    ) -> Result<HashMap<Symbol, FuncId>, CranelispError> {
        let mut func_ids = HashMap::new();
        for defn in defns {
            let sig = self.build_sig(defn.params.len());
            let func_id = self
                .module
                .declare_function(&defn.name, Linkage::Export, &sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare function '{}': {e}", defn.name),
                    span: defn.span,
                })?;
            func_ids.insert(defn.name.clone(), func_id);
        }
        Ok(func_ids)
    }

    /// Declare imported functions in the JIT module for cross-module linking.
    ///
    /// In Batch mode, when a module calls functions from other modules, those
    /// functions must be declared with `Linkage::Import` so that Cranelift's
    /// linker can resolve the cross-references. The orchestrator compiles
    /// modules in dependency order, so imported functions are already finalized
    /// by the time the calling module is compiled.
    ///
    /// Each entry is `(name, param_count)`. Returns the declared FuncIds merged
    /// into the provided `func_ids` map.
    pub fn declare_imported_functions(
        &mut self,
        imports: &[(Symbol, usize)],
        func_ids: &mut HashMap<Symbol, FuncId>,
    ) -> Result<(), CranelispError> {
        for (name, param_count) in imports {
            let sig = self.build_sig(*param_count);
            let func_id = self
                .module
                .declare_function(name, Linkage::Import, &sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!(
                        "failed to declare imported function '{}': {e}",
                        name
                    ),
                    span: Span::SYNTHETIC,
                })?;
            func_ids.insert(name.clone(), func_id);
        }
        Ok(())
    }

    /// Compile a function definition into Cranelift IR.
    /// Returns the CLIF IR text for introspection.
    ///
    /// The `compile_ctx` bundles all environment needed for codegen: function IDs,
    /// arities, GOT state, and intrinsic IDs. Construct it at the call site using
    /// `Jit::build_compile_context`.
    pub fn compile_defn(
        &mut self,
        defn: &Defn,
        compile_ctx: CompileContext<'_>,
    ) -> Result<String, CranelispError> {
        self.ctx.func.signature = self.build_sig(defn.params.len());
        self.ctx.func.name =
            cranelift::codegen::ir::UserFuncName::testcase(defn.name.as_bytes());

        // Build the function body.
        FnCompiler::compile_body(
            defn,
            &mut self.ctx.func,
            &mut self.func_ctx,
            &mut self.module,
            compile_ctx,
        )?;

        // Capture CLIF IR text before compilation.
        let clif_ir = format!("{}", self.ctx.func.display());

        // Compile to machine code.
        let func_id = *compile_ctx
            .func_ids
            .get(&defn.name)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("function '{}' not declared", defn.name),
                span: defn.span,
            })?;

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define function '{}': {e}", defn.name),
                span: defn.span,
            })?;

        self.module.clear_context(&mut self.ctx);

        Ok(clif_ir)
    }

    /// Build a `CompileContext` from a `CheckResult` and environment parameters.
    ///
    /// Bundles all the information needed for codegen into a single struct,
    /// eliminating the need to pass individual fields to `compile_defn`.
    #[allow(clippy::too_many_arguments)]
    pub fn build_compile_context<'a>(
        &self,
        check: &'a CheckResult,
        mode: CompileMode,
        func_ids: &'a HashMap<Symbol, FuncId>,
        func_arities: &'a HashMap<Symbol, usize>,
        got_slots: Option<&'a HashMap<Symbol, usize>>,
        got_base_ptr: Option<i64>,
        cross_module_got: Option<&'a CrossModuleGot>,
    ) -> CompileContext<'a> {
        CompileContext {
            method_resolutions: &check.method_resolutions,
            expr_types: &check.expr_types,
            func_ids,
            func_arities,
            mode,
            type_defs: &check.type_defs,
            constructor_to_type: &check.constructor_to_type,
            got_slots,
            got_base_ptr,
            cross_module_got,
            alloc_func_id: self.alloc_func_id,
            dealloc_func_id: self.dealloc_func_id,
            alloc_string_func_id: self.alloc_string_func_id,
            panic_func_id: self.panic_func_id,
            vec_new_func_id: self.vec_new_func_id,
            vec_drop_func_id: self.vec_drop_func_id,
        }
    }

    /// Finalize all pending function definitions.
    pub fn finalize(&mut self) -> Result<(), CranelispError> {
        self.module.finalize_definitions().map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to finalize JIT definitions: {e}"),
                span: Span::SYNTHETIC,
            }
        })
    }

    /// Get the finalized code pointer for a function by FuncId.
    pub fn get_finalized_ptr(&self, func_id: FuncId) -> *const u8 {
        self.module.get_finalized_function(func_id)
    }

    /// Finalize definitions and return the code pointer for a named function.
    /// Convenience method that looks up the FuncId by name (re-declaring with
    /// the same param count).
    pub fn finalize_and_get_ptr(
        &mut self,
        name: &Symbol,
        param_count: usize,
    ) -> Result<*const u8, CranelispError> {
        self.finalize()?;

        // Re-declare with same signature to get the existing FuncId.
        let sig = self.build_sig(param_count);
        let func_id = self
            .module
            .declare_function(name, Linkage::Export, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to look up function '{}': {e}", name),
                span: Span::SYNTHETIC,
            })?;

        Ok(self.module.get_finalized_function(func_id))
    }

    /// Look up a finalized function pointer by name and param count.
    ///
    /// Must be called after `finalize()`. Re-declares the function with
    /// the same signature to obtain the FuncId, then returns the code pointer.
    pub fn get_ptr_by_name(
        &mut self,
        name: &Symbol,
        param_count: usize,
    ) -> Result<*const u8, CranelispError> {
        let sig = self.build_sig(param_count);
        let func_id = self
            .module
            .declare_function(name, Linkage::Export, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to look up function '{}': {e}", name),
                span: Span::SYNTHETIC,
            })?;
        Ok(self.module.get_finalized_function(func_id))
    }

    /// Get a mutable reference to the inner JIT module.
    /// Needed by FnCompiler for declaring extern functions.
    pub fn jit_module(&mut self) -> &mut JITModule {
        &mut self.module
    }

    /// Build a Cranelift function signature: all params and return are i64.
    fn build_sig(&self, param_count: usize) -> cranelift::codegen::ir::Signature {
        let mut sig = self.module.make_signature();
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        sig
    }

    /// Declare an imported function (from runtime) with n params, m returns.
    fn declare_import(
        &mut self,
        name: &str,
        n_params: usize,
        n_returns: usize,
    ) -> Result<FuncId, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in 0..n_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        for _ in 0..n_returns {
            sig.returns.push(AbiParam::new(types::I64));
        }
        self.module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare intrinsic '{name}': {e}"),
                span: Span::SYNTHETIC,
            })
    }

    /// Declare an imported void function (no return value).
    fn declare_import_void(
        &mut self,
        name: &str,
        n_params: usize,
    ) -> Result<FuncId, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in 0..n_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        // No return values.
        self.module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare intrinsic '{name}': {e}"),
                span: Span::SYNTHETIC,
            })
    }

    /// Declare an imported function that never returns (panic).
    fn declare_import_no_return(
        &mut self,
        name: &str,
        n_params: usize,
    ) -> Result<FuncId, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in 0..n_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        // Panic returns i64 for cranelift compatibility (never actually returns).
        sig.returns.push(AbiParam::new(types::I64));
        self.module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare intrinsic '{name}': {e}"),
                span: Span::SYNTHETIC,
            })
    }
}

/// FuncIds for declared runtime intrinsics.
pub struct IntrinsicIds {
    pub alloc: FuncId,
    pub dealloc: FuncId,
    pub alloc_string: FuncId,
    pub panic: FuncId,
    pub vec_new: FuncId,
    pub vec_drop: FuncId,
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::ModuleFullPath;

    // spec: 12-runtime §12.1 — ISA construction for host platform
    #[test]
    fn test_build_isa() {
        let isa = build_isa();
        assert!(isa.is_ok(), "ISA construction should succeed on host");
    }

    // spec: 12-runtime §12.1 — JIT engine creation
    #[test]
    fn test_jit_creation() {
        let jit = Jit::new();
        assert!(jit.is_ok(), "JIT creation should succeed");
    }

    // spec: 12-runtime §12.3 — runtime intrinsic function declarations (alloc, dealloc, panic)
    #[test]
    fn test_intrinsic_declaration() {
        let mut jit = Jit::new().unwrap();
        let ids = jit.declare_intrinsics();
        assert!(ids.is_ok(), "intrinsic declaration should succeed");
    }

    // spec: 08-modules §8.3 — imported function declarations for cross-module calls
    #[test]
    fn test_declare_imported_functions() {
        let mut jit = Jit::new().unwrap();
        let mut func_ids = HashMap::new();

        let imports = vec![
            (Symbol::from("math/add"), 2usize),
            (Symbol::from("math/mul"), 2usize),
        ];
        let result = jit.declare_imported_functions(&imports, &mut func_ids);
        assert!(result.is_ok(), "imported function declaration should succeed");
        assert!(func_ids.contains_key(&Symbol::from("math/add")));
        assert!(func_ids.contains_key(&Symbol::from("math/mul")));
        assert_eq!(func_ids.len(), 2);
    }

    // spec: 08-modules §8.3 — imported declarations merge with local function declarations
    #[test]
    fn test_declare_imported_functions_merges_with_existing() {
        let mut jit = Jit::new().unwrap();

        // Declare a local function first.
        let defn = Defn {
            name: Symbol::from("local_fn"),
            params: vec![Symbol::from("x")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: cranelisp_types::Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(0, 1),
            },
            docstring: None,
            span: Span::new(0, 10),
        };
        let mut func_ids = jit.declare_functions(&[&defn]).unwrap();
        assert_eq!(func_ids.len(), 1);

        // Now declare an imported function -- should merge into the same map.
        let imports = vec![(Symbol::from("other/helper"), 1usize)];
        jit.declare_imported_functions(&imports, &mut func_ids).unwrap();
        assert_eq!(func_ids.len(), 2);
        assert!(func_ids.contains_key(&Symbol::from("local_fn")));
        assert!(func_ids.contains_key(&Symbol::from("other/helper")));
    }

    // spec: pipeline-orchestration §4 — JIT with extra symbols for cross-module calls
    #[test]
    fn test_jit_new_with_symbols() {
        // An empty extra_symbols list should work identically to new().
        let jit = Jit::new_with_symbols(&[]);
        assert!(jit.is_ok(), "new_with_symbols with empty list should succeed");

        // Extra symbols should be accepted (though we can't call them in
        // this unit test, we verify the builder doesn't reject them).
        extern "C" fn dummy_fn(_x: i64) -> i64 {
            0
        }
        let jit2 = Jit::new_with_symbols(&[("test/dummy", dummy_fn as *const u8)]);
        assert!(
            jit2.is_ok(),
            "new_with_symbols with extra symbol should succeed"
        );
    }

    // spec: 08-modules §8.3 — compile context with cross-module GOT for module imports
    #[test]
    fn test_build_compile_context_with_cross_module_got() {
        let jit = Jit::new().unwrap();
        let check = CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: std::collections::HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };
        let func_ids = HashMap::new();
        let func_arities = HashMap::new();

        // Build with cross-module GOT.
        let mut xmod = HashMap::new();
        xmod.insert(
            (ModuleFullPath::from("math"), Symbol::from("add")),
            (0x1000i64, 3usize),
        );

        let ctx = jit.build_compile_context(
            &check,
            CompileMode::Interactive,
            &func_ids,
            &func_arities,
            None,
            None,
            Some(&xmod),
        );
        assert!(ctx.cross_module_got.is_some());

        // Build without cross-module GOT.
        let ctx2 = jit.build_compile_context(
            &check,
            CompileMode::Batch,
            &func_ids,
            &func_arities,
            None,
            None,
            None,
        );
        assert!(ctx2.cross_module_got.is_none());
    }
}
