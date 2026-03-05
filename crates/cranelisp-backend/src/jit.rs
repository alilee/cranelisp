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

use crate::compiler::{CompileContext, FnCompiler};

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

    // Extern primitives (user-visible via primitives module)
    builder.symbol("str-concat", cranelisp_runtime::str_concat as *const u8);
    builder.symbol("str-eq", cranelisp_runtime::str_eq as *const u8);
    builder.symbol("str-len", cranelisp_runtime::str_len as *const u8);
    builder.symbol("string-identity", cranelisp_runtime::string_identity as *const u8);
    builder.symbol("int-to-string", cranelisp_runtime::int_to_string as *const u8);
    builder.symbol("float-to-string", cranelisp_runtime::float_to_string as *const u8);
    builder.symbol("bool-to-string", cranelisp_runtime::bool_to_string as *const u8);
    builder.symbol("parse-int", cranelisp_runtime::parse_int as *const u8);
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
}

impl Jit {
    /// Create a new JIT instance for the current host architecture.
    pub fn new() -> Result<Self, CranelispError> {
        let isa = build_isa()?;

        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        register_intrinsics(&mut builder);

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

        self.alloc_func_id = Some(alloc_id);
        self.dealloc_func_id = Some(dealloc_id);
        self.alloc_string_func_id = Some(alloc_string_id);
        self.panic_func_id = Some(panic_id);

        Ok(IntrinsicIds {
            alloc: alloc_id,
            dealloc: dealloc_id,
            alloc_string: alloc_string_id,
            panic: panic_id,
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
    pub fn build_compile_context<'a>(
        &self,
        check: &'a CheckResult,
        mode: CompileMode,
        func_ids: &'a HashMap<Symbol, FuncId>,
        func_arities: &'a HashMap<Symbol, usize>,
        got_slots: Option<&'a HashMap<Symbol, usize>>,
        got_base_ptr: Option<i64>,
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
            alloc_func_id: self.alloc_func_id,
            dealloc_func_id: self.dealloc_func_id,
            alloc_string_func_id: self.alloc_string_func_id,
            panic_func_id: self.panic_func_id,
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_isa() {
        let isa = build_isa();
        assert!(isa.is_ok(), "ISA construction should succeed on host");
    }

    #[test]
    fn test_jit_creation() {
        let jit = Jit::new();
        assert!(jit.is_ok(), "JIT creation should succeed");
    }

    #[test]
    fn test_intrinsic_declaration() {
        let mut jit = Jit::new().unwrap();
        let ids = jit.declare_intrinsics();
        assert!(ids.is_ok(), "intrinsic declaration should succeed");
    }
}
