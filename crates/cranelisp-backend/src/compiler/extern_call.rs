//! The single arity-generic extern-call helper (audit F5, HIGH-3 dedup).
//!
//! Replaces the former `emit_extern_call_1`/`_2`/`_3`/`_4` arity ladder
//! (control_flow IVar plumbing used `_1`; vec_codegen used `_2`/`_3`/`_4`).
//! One slice-based method `emit_extern_call(name, &[Value], span)` declares the
//! `extern "C"` import with one `i64` param per arg + an `i64` return, emits the
//! call into `self.builder`, and returns the single result value. This closes
//! the "do not add `emit_extern_call_5`" trap the ladder invited.
//!
//! Distinct from `control_flow::fn_as_value::emit_extern_call_in_wrapper`, a
//! free fn that emits into a *borrowed* `&mut FunctionBuilder` for auto-curry
//! wrapper bodies (it cannot take `&mut self` because it runs while a wrapper
//! function — not `self.builder` — is under construction). That variant is
//! already slice-based and is left in place.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, Span};

use super::FnCompiler;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Emit a call to an extern "C" function taking `args.len()` i64 arguments
    /// and returning i64. Declares/imports the extern, builds the call into
    /// `self.builder`, and returns the single result value.
    pub(crate) fn emit_extern_call(
        &mut self,
        name: &str,
        args: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in args {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern function '{name}': {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let local_func = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(local_func, args);
        Ok(self.builder.inst_results(call)[0])
    }
}
