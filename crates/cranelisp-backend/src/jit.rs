// Cranelift ISA setup and JIT module lifecycle.
//
// Single ISA construction point. Addresses audit finding about
// multiple ISA constructions in the prototype.

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

/// JIT module wrapper. Owns the Cranelift JIT module and provides
/// function compilation and execution services.
pub struct Jit {
    module: JITModule,
    ctx: cranelift::codegen::Context,
    func_ctx: FunctionBuilderContext,
}

impl Jit {
    /// Create a new JIT instance for the current host architecture.
    pub fn new() -> Result<Self, CranelispError> {
        let isa = build_isa()?;

        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        let module =
            JITModule::new(builder);

        let ctx = module.make_context();
        let func_ctx = FunctionBuilderContext::new();

        Ok(Jit {
            module,
            ctx,
            func_ctx,
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
    /// In Interactive mode, `got_slots` and `got_base_ptr` must be provided
    /// so that function calls emit GOT-indirect `call_indirect` instructions.
    pub fn compile_defn(
        &mut self,
        defn: &Defn,
        check: &CheckResult,
        mode: CompileMode,
        func_ids: &HashMap<Symbol, FuncId>,
        got_slots: Option<&HashMap<Symbol, usize>>,
        got_base_ptr: Option<i64>,
    ) -> Result<String, CranelispError> {
        self.ctx.func.signature = self.build_sig(defn.params.len());
        self.ctx.func.name =
            cranelift::codegen::ir::UserFuncName::testcase(defn.name.as_bytes());

        // Build the compilation context.
        let compile_ctx = CompileContext {
            method_resolutions: &check.method_resolutions,
            expr_types: &check.expr_types,
            func_ids,
            mode,
            type_defs: &check.type_defs,
            constructor_to_type: &check.constructor_to_type,
            got_slots,
            got_base_ptr,
        };

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
        let func_id = *func_ids
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

    /// Build a Cranelift function signature: all params and return are i64.
    fn build_sig(&self, param_count: usize) -> cranelift::codegen::ir::Signature {
        let mut sig = self.module.make_signature();
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        sig
    }
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
}
