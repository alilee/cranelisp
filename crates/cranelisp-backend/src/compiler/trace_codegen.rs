//! Trace form codegen: `compile_trace` method for `FnCompiler`.
//!
//! Implements `(trace body)` -- GOT-swap wrapper around a body expression,
//! returning a `Trace` ADT representing the call tree.
//!
//! Wrappers format parameter values and return values using
//! `cranelisp_trace_format` (backed by the REPL's `format_result_value`).
//! The TypeChecker pointer is set via the integration layer before evaluation.

use cranelift::codegen::ir::{StackSlotData, StackSlotKind};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_types::{ErrorLocation, CranelispError, Expr, Span};

use super::{FnCompiler, TracedFnInfo};

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Discard a body result by decrementing its RC if it is heap-allocated.
    /// Used by both `compile_trace` and `compile_trace_no_swap` to drop the
    /// body value (the trace result is the Trace ADT, not the body's value).
    fn emit_body_discard(&mut self, body_val: Value, body: &Expr) {
        if let Some(ty) = body.inferred_type().cloned()
            && self.is_heap_type(&ty)
        {
            crate::heap::emit_rc_dec(
                &mut self.builder,
                self.module,
                body_val,
                self.ctx.dealloc_func_id,
                None,
            );
        }
    }

    /// Compile a `(trace body)` expression.
    ///
    /// Returns a `Value` that is a heap pointer to a `Trace` ADT.
    pub(crate) fn compile_trace(
        &mut self,
        _modules: &[cranelisp_types::Symbol],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // In batch mode there are no traced functions, so tracing is unavailable.
        // Fall back to evaluating the body and returning an empty TraceCall.
        if self.ctx.traced_fns.is_none() {
            return self.compile_trace_no_swap(body, span);
        }

        // Get the traced functions from the compile context.
        let traced = match self.ctx.traced_fns {
            Some(fns) if !fns.is_empty() => fns,
            _ => return self.compile_trace_no_swap(body, span),
        };

        // Group by GOT base address (each module has its own GOT table).
        let mut got_groups: Vec<(i64, Vec<&TracedFnInfo>)> = Vec::new();
        for tf in traced {
            if let Some(grp) = got_groups.iter_mut().find(|(addr, _)| *addr == tf.got_base) {
                grp.1.push(tf);
            } else {
                got_groups.push((tf.got_base, vec![tf]));
            }
        }

        // Declare trace runtime functions in the module (idempotent for Import linkage).
        let swap_id = self.declare_trace_extern("cranelisp_trace_swap_got", 4, true, span)?;
        let restore_id =
            self.declare_trace_extern("cranelisp_trace_restore_got", 2, false, span)?;
        let collect_id =
            self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;

        // For each GOT group: compile wrappers and emit swap_got call.
        let mut swap_results: Vec<(i64, Value)> = Vec::new();

        for (got_base, group) in &got_groups {
            let n = group.len();

            // Allocate and leak a u32 slots array (known at compile time).
            let slots: Box<[u32]> = group
                .iter()
                .map(|tf| tf.got_slot as u32)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            let slots_ptr = Box::into_raw(slots) as *mut u32 as i64;

            // Allocate and leak a wrappers buffer (i64, filled at JIT runtime via func_addr).
            let wrappers_buf: Box<[i64]> = vec![0i64; n].into_boxed_slice();
            let wrappers_buf_ptr = Box::into_raw(wrappers_buf) as *mut i64 as i64;

            // For each function: compile a trace wrapper, then emit a store of its
            // code_ptr into the wrappers buffer at runtime.
            let buf_addr_val = self.builder.ins().iconst(types::I64, wrappers_buf_ptr);
            for (i, tf) in group.iter().enumerate() {
                let wrapper_id = self.compile_trace_wrapper_fn(tf, span)?;
                let func_ref = self
                    .module
                    .declare_func_in_func(wrapper_id, self.builder.func);
                let wrapper_ptr_val = self.builder.ins().func_addr(types::I64, func_ref);
                let offset = (i * 8) as i32;
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), wrapper_ptr_val, buf_addr_val, offset);
            }

            // Emit cranelisp_trace_swap_got(got_base, n_slots, slots_ptr, wrappers_ptr).
            let got_base_val = self.builder.ins().iconst(types::I64, *got_base);
            let n_val = self.builder.ins().iconst(types::I64, n as i64);
            let slots_val = self.builder.ins().iconst(types::I64, slots_ptr);
            let wrappers_val = self.builder.ins().iconst(types::I64, wrappers_buf_ptr);
            let swap_ref = self
                .module
                .declare_func_in_func(swap_id, self.builder.func);
            let call = self.builder.ins().call(
                swap_ref,
                &[got_base_val, n_val, slots_val, wrappers_val],
            );
            let saved_got_val = self.builder.inst_results(call)[0];
            swap_results.push((*got_base, saved_got_val));
        }

        // Compile the body expression.
        // Disable sparkability analysis inside trace bodies — trace must
        // execute sequentially to produce deterministic trace trees.
        let saved_trace = self.in_trace_body;
        self.in_trace_body = true;
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let body_result = self.compile_expr(body)?;
        self.in_tail_position = saved_tail;
        self.in_trace_body = saved_trace;

        // Discard body result (dec RC if it is heap-allocated).
        // The trace result is the Trace ADT, not the body's value.
        self.emit_body_discard(body_result, body);

        // Restore GOTs in reverse order (for clean nesting semantics).
        let restore_ref = self
            .module
            .declare_func_in_func(restore_id, self.builder.func);
        for (got_base, saved_got_val) in swap_results.iter().rev() {
            let got_base_val = self.builder.ins().iconst(types::I64, *got_base);
            self.builder
                .ins()
                .call(restore_ref, &[got_base_val, *saved_got_val]);
        }

        // Call cranelisp_collect_trace() -> Trace ADT heap ptr.
        let collect_ref = self
            .module
            .declare_func_in_func(collect_id, self.builder.func);
        let collect_call = self.builder.ins().call(collect_ref, &[]);
        Ok(self.builder.inst_results(collect_call)[0])
    }

    /// Fallback path used in batch mode (no GOT) or when there are no traced functions.
    ///
    /// Evaluates the body (discards result) and returns an empty TraceCall via
    /// `cranelisp_collect_trace`. The trace stack will be empty so it returns a
    /// minimal TraceCall with the root "::trace::" name.
    fn compile_trace_no_swap(
        &mut self,
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let body_result = self.compile_expr(body)?;
        self.in_tail_position = saved_tail;

        // Discard body result.
        self.emit_body_discard(body_result, body);

        // Return empty trace from collect_trace (handles empty stack gracefully).
        let collect_id =
            self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;
        let collect_ref = self
            .module
            .declare_func_in_func(collect_id, self.builder.func);
        let call = self.builder.ins().call(collect_ref, &[]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Declare a trace runtime extern function in the module.
    ///
    /// `n_params`: number of `i64` parameters.
    /// `has_return`: whether the function returns an `i64`.
    ///
    /// Idempotent: re-declaring with the same signature returns the existing FuncId.
    fn declare_trace_extern(
        &mut self,
        name: &str,
        n_params: usize,
        has_return: bool,
        span: Span,
    ) -> Result<FuncId, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in 0..n_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        if has_return {
            sig.returns.push(AbiParam::new(types::I64));
        }
        self.module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare trace extern '{}': {}", name, e),
                location: ErrorLocation::from_span(span),
            })
    }

    /// Compile a thin trace wrapper function for a single traced function.
    ///
    /// Wrapper signature: `(arg0: i64, ..., argN-1: i64) -> i64`
    ///
    /// Wrapper body:
    /// ```text
    /// str_ptr_0 = cranelisp_trace_format(arg0, type_ptr_0)
    /// ...
    /// store str_ptrs into stack slot
    /// cranelisp_trace_enter(name_ptr, name_len, arity, array_ptr)
    /// orig_result = call_indirect(original_code_ptr, [arg0..argN-1])
    /// result_str  = cranelisp_trace_format(orig_result, result_type_ptr)
    /// final       = cranelisp_trace_exit(orig_result, result_str)
    /// return final
    /// ```
    ///
    /// The original code ptr is embedded as an `iconst` -- calls bypass the GOT and
    /// call the original implementation directly. Recursive calls inside the original
    /// go through the (swapped) GOT, naturally building the call tree.
    ///
    /// Type pointers are leaked `Box<Type>` values, valid for the program lifetime.
    fn compile_trace_wrapper_fn(
        &mut self,
        tf: &TracedFnInfo,
        span: Span,
    ) -> Result<FuncId, CranelispError> {
        assert_eq!(
            tf.arity,
            tf.param_types.len(),
            "trace wrapper arity mismatch for '{}': arity={} but param_types={}",
            tf.name,
            tf.arity,
            tf.param_types.len()
        );

        // Wrapper signature: (arg0..argN-1) -> i64.
        let mut sig = self.module.make_signature();
        for _ in 0..tf.arity {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_anonymous_function(&sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!(
                    "failed to declare trace wrapper for '{}': {}",
                    tf.name, e
                ),
                location: ErrorLocation::from_span(span),
            })?;

        // Declare trace_enter (4 params), trace_exit (2 params), and trace_format (2 params).
        let enter_id =
            self.declare_trace_extern("cranelisp_trace_enter", 4, false, span)?;
        let exit_id =
            self.declare_trace_extern("cranelisp_trace_exit", 2, true, span)?;
        let format_id =
            self.declare_trace_extern("cranelisp_trace_format", 2, true, span)?;

        // Leak the function name bytes -- valid for the program lifetime.
        let name_bytes: Box<[u8]> = tf.name.as_bytes().to_vec().into_boxed_slice();
        let name_len = name_bytes.len() as i64;
        let name_ptr = Box::into_raw(name_bytes) as *mut u8 as i64;

        // Leak a Box<Type> for each parameter and for the result.
        // These are embedded as `iconst` in the wrapper and remain valid for program lifetime.
        let param_type_ptrs: Vec<i64> = tf
            .param_types
            .iter()
            .map(|ty| Box::into_raw(Box::new(ty.clone())) as i64)
            .collect();
        let result_type_ptr = Box::into_raw(Box::new(tf.result_type.clone())) as i64;

        // Build and compile the wrapper IR.
        {
            let mut wrapper_func = cranelift::codegen::ir::Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, wrapper_func_id.as_u32()),
                sig.clone(),
            );
            let mut wrapper_ctx = FunctionBuilderContext::new();
            let mut wb = FunctionBuilder::new(&mut wrapper_func, &mut wrapper_ctx);

            let entry = wb.create_block();
            wb.append_block_params_for_function_params(entry);
            wb.switch_to_block(entry);
            wb.seal_block(entry);

            let args: Vec<Value> = wb.block_params(entry).to_vec();

            // Declare externs inside the wrapper function.
            let format_ref = self.module.declare_func_in_func(format_id, wb.func);
            let enter_ref = self.module.declare_func_in_func(enter_id, wb.func);

            // Format each parameter using cranelisp_trace_format(val, type_ptr).
            let arity = tf.arity;
            let mut param_str_ptrs: Vec<Value> = Vec::with_capacity(arity);
            for (i, &type_ptr) in param_type_ptrs.iter().enumerate() {
                let arg_val = args[i];
                let type_ptr_val = wb.ins().iconst(types::I64, type_ptr);
                let fmt_call = wb.ins().call(format_ref, &[arg_val, type_ptr_val]);
                param_str_ptrs.push(wb.inst_results(fmt_call)[0]);
            }

            // Store formatted param string pointers in a stack slot (if arity > 0),
            // then pass the slot address to cranelisp_trace_enter.
            let (params_count_val, array_ptr_val) = if arity > 0 {
                let slot = wb.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    (arity * 8) as u32,
                    3, // 2^3 = 8 byte alignment
                ));
                for (i, &str_ptr) in param_str_ptrs.iter().enumerate() {
                    wb.ins().stack_store(str_ptr, slot, (i * 8) as i32);
                }
                let count = wb.ins().iconst(types::I64, arity as i64);
                let ptr = wb.ins().stack_addr(types::I64, slot, 0i32);
                (count, ptr)
            } else {
                // No params: pass count=0, ptr=null (runtime won't dereference).
                let count = wb.ins().iconst(types::I64, 0i64);
                let ptr = wb.ins().iconst(types::I64, 0i64);
                (count, ptr)
            };

            // cranelisp_trace_enter(name_ptr, name_len, params_count, array_ptr)
            let name_ptr_val = wb.ins().iconst(types::I64, name_ptr);
            let name_len_val = wb.ins().iconst(types::I64, name_len);
            wb.ins().call(
                enter_ref,
                &[name_ptr_val, name_len_val, params_count_val, array_ptr_val],
            );

            // Build call signature for the original function.
            let mut orig_sig = self.module.make_signature();
            for _ in 0..tf.arity {
                orig_sig.params.push(AbiParam::new(types::I64));
            }
            orig_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = wb.import_signature(orig_sig);

            // Call original via embedded code_ptr (bypasses the swapped GOT).
            let code_ptr_val = wb.ins().iconst(types::I64, tf.code_ptr);
            let orig_call = wb.ins().call_indirect(sig_ref, code_ptr_val, &args);
            let orig_result = wb.inst_results(orig_call)[0];

            // Format the result using cranelisp_trace_format(orig_result, result_type_ptr).
            let format_ref2 = self.module.declare_func_in_func(format_id, wb.func);
            let result_type_ptr_val = wb.ins().iconst(types::I64, result_type_ptr);
            let result_fmt_call =
                wb.ins()
                    .call(format_ref2, &[orig_result, result_type_ptr_val]);
            let result_str = wb.inst_results(result_fmt_call)[0];

            // cranelisp_trace_exit(orig_result, result_str) -> final result
            let exit_ref = self.module.declare_func_in_func(exit_id, wb.func);
            let exit_call = wb.ins().call(exit_ref, &[orig_result, result_str]);
            let final_result = wb.inst_results(exit_call)[0];

            wb.ins().return_(&[final_result]);
            wb.seal_all_blocks();
            wb.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(wrapper_func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!(
                        "failed to define trace wrapper for '{}': {}",
                        tf.name, e
                    ),
                    location: ErrorLocation::from_span(span),
                })?;
        }

        Ok(wrapper_func_id)
    }

} // impl FnCompiler — trace codegen
