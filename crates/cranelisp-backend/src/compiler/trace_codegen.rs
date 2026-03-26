//! Trace form codegen: `compile_trace` and `compile_run_tests` methods for `FnCompiler`.
//!
//! Implements `(trace body)` -- GOT-swap wrapper around a body expression,
//! returning a `Trace` ADT representing the call tree.
//!
//! Implements `(run-tests init pass-fn fail-fn)` -- REPL-only special form that
//! discovers test functions, runs each with GOT-swap tracing, and folds results
//! via user-supplied pass/fail closures.
//!
//! Wrappers format parameter values and return values using
//! `cranelisp_trace_format` (backed by the REPL's `format_result_value`).
//! The TypeChecker pointer is set via the integration layer before evaluation.

use cranelift::codegen::ir::{StackSlotData, StackSlotKind};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_types::{CranelispError, Expr, Span, Symbol};

use crate::heap::{self, HeapAdt};

use super::{FnCompiler, TracedFnInfo};

/// Groups trace runtime function IDs used during `run-tests` iteration.
///
/// These are extern functions declared once and passed to each test iteration,
/// handling GOT swap/restore and trace collection.
struct TraceRuntimeFns {
    /// `cranelisp_trace_swap_got(got_ptr, originals_ptr, wrappers_ptr, count) -> ()`
    swap_id: FuncId,
    /// `cranelisp_trace_restore_got(got_ptr, originals_ptr) -> ()`
    restore_id: FuncId,
    /// `cranelisp_collect_trace() -> Trace`
    collect_id: FuncId,
    /// `cranelisp_trace_first_child_nanos(trace) -> Int`
    nanos_id: FuncId,
}

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Discard a body result by decrementing its RC if it is heap-allocated.
    /// Used by both `compile_trace` and `compile_trace_no_swap` to drop the
    /// body value (the trace result is the Trace ADT, not the body's value).
    fn emit_body_discard(&mut self, body_val: Value, body_span: Span) {
        if let Some(ty) = self.ctx.expr_types.get(&body_span).cloned()
            && self.is_heap_type(&ty)
            && let Some(dealloc) = self.ctx.dealloc_func_id
        {
            crate::heap::emit_rc_dec(
                &mut self.builder,
                self.module,
                body_val,
                dealloc,
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
        // In batch mode there is no per-module GOT, so tracing is unavailable.
        // Fall back to evaluating the body and returning an empty TraceCall.
        if self.ctx.got_slots.is_none() {
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
        self.emit_body_discard(body_result, body.span());

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
        self.emit_body_discard(body_result, body.span());

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
                span,
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
                span,
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
                    span,
                })?;
        }

        Ok(wrapper_func_id)
    }

    // ── run-tests codegen ─────────────────────────────────────────────────

    /// Compile a `(run-tests init pass-fn fail-fn)` expression.
    ///
    /// Discovers all `test-*` zero-arg functions in the traced functions list,
    /// runs each with full GOT-swap tracing, and folds results:
    /// - pass: `(pass-fn acc test-name nanos) -> acc`
    /// - fail: `(fail-fn acc test-name nanos reason trace) -> acc`
    ///
    /// Returns the final accumulator value.
    /// In batch mode (no per-module GOT), returns `init` unchanged.
    pub(crate) fn compile_run_tests(
        &mut self,
        _modules: &[Symbol],
        init: &Expr,
        pass_fn: &Expr,
        fail_fn: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Batch mode: no GOT available, return init unchanged.
        if self.ctx.got_slots.is_none() {
            return self.compile_expr(init);
        }

        // Get all traced functions from the compile context.
        let traced = match self.ctx.traced_fns {
            Some(fns) if !fns.is_empty() => fns,
            _ => return self.compile_expr(init),
        };

        // Declare trace runtime externs.
        let trace_fns = TraceRuntimeFns {
            swap_id: self
                .declare_trace_extern("cranelisp_trace_swap_got", 4, true, span)?,
            restore_id: self
                .declare_trace_extern("cranelisp_trace_restore_got", 2, false, span)?,
            collect_id: self
                .declare_trace_extern("cranelisp_collect_trace", 0, true, span)?,
            nanos_id: self
                .declare_trace_extern("cranelisp_trace_first_child_nanos", 1, true, span)?,
        };

        // Compile trace wrappers for ALL traced fns (not just test fns).
        let all_wrappers = self.compile_all_trace_wrappers(traced, span)?;

        // Identify test functions: zero-arg fns whose bare name starts with "test-".
        // Names may be module-qualified (e.g. "user/test-one"), so extract the
        // last segment after any '/' for the prefix check.
        let test_fns: Vec<(String, FuncId)> = all_wrappers
            .iter()
            .filter(|(tf, _)| {
                let bare = tf.name.rsplit('/').next().unwrap_or(&tf.name);
                bare.starts_with("test-") && tf.arity == 0
            })
            .map(|(tf, wrapper_id)| (tf.name.clone(), *wrapper_id))
            .collect();

        if test_fns.is_empty() {
            return self.compile_expr(init);
        }

        // Prepare GOT group data (compile-time arrays + JIT-runtime func_addr stores).
        let got_group_data = self.prepare_got_groups(&all_wrappers, span)?;

        // Compile fold expressions (not in tail position).
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let mut current_acc = self.compile_expr(init)?;
        let pass_fn_val = self.compile_expr(pass_fn)?;
        let fail_fn_val = self.compile_expr(fail_fn)?;
        self.in_tail_position = saved_tail;

        // Allocate test name strings (one per test, reused across iterations).
        let test_name_vals: Vec<Value> = test_fns
            .iter()
            .map(|(name, _)| self.compile_string_lit(name, span))
            .collect::<Result<Vec<_>, _>>()?;

        // Per-test unrolled loop.
        for (i, (_test_name, test_wrapper_id)) in test_fns.iter().enumerate() {
            current_acc = self.emit_single_test_iteration(
                current_acc,
                pass_fn_val,
                fail_fn_val,
                test_name_vals[i],
                *test_wrapper_id,
                &got_group_data,
                &trace_fns,
                span,
            )?;
        }

        // Cleanup: dec pass_fn and fail_fn closures (consuming convention).
        self.emit_closure_dec(pass_fn_val, span);
        self.emit_closure_dec(fail_fn_val, span);

        // Dec all test name strings (each was inc'd before closure calls,
        // consuming closure dec'd it back to RC=1; final dec frees it).
        if let Some(dealloc) = self.ctx.dealloc_func_id {
            for &tname_val in &test_name_vals {
                crate::heap::emit_rc_dec(
                    &mut self.builder,
                    self.module,
                    tname_val,
                    dealloc,
                    None,
                );
            }
        }

        Ok(current_acc)
    }

    /// Compile trace wrappers for all traced functions.
    /// Returns a list of (TracedFnInfo, wrapper FuncId) pairs.
    fn compile_all_trace_wrappers<'b>(
        &mut self,
        traced: &'b [TracedFnInfo],
        span: Span,
    ) -> Result<Vec<(&'b TracedFnInfo, FuncId)>, CranelispError> {
        let mut all_wrappers = Vec::with_capacity(traced.len());
        for tf in traced {
            let wrapper_id = self.compile_trace_wrapper_fn(tf, span)?;
            all_wrappers.push((tf, wrapper_id));
        }
        Ok(all_wrappers)
    }

    /// Prepare GOT group data: group traced fns by GOT base, allocate
    /// compile-time arrays, and emit JIT-runtime `func_addr` stores.
    fn prepare_got_groups(
        &mut self,
        all_wrappers: &[(&TracedFnInfo, FuncId)],
        _span: Span,
    ) -> Result<Vec<GotGroupData>, CranelispError> {
        // Group wrapper indices by GOT base address.
        let mut groups: Vec<(i64, Vec<usize>)> = Vec::new();
        for (idx, (tf, _)) in all_wrappers.iter().enumerate() {
            if let Some(grp) = groups.iter_mut().find(|(b, _)| *b == tf.got_base) {
                grp.1.push(idx);
            } else {
                groups.push((tf.got_base, vec![idx]));
            }
        }

        let mut result = Vec::with_capacity(groups.len());
        for (got_base, indices) in &groups {
            let n = indices.len();

            // Leak a u32 slots array (valid for program lifetime).
            let slots: Box<[u32]> = indices
                .iter()
                .map(|&i| all_wrappers[i].0.got_slot as u32)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            let slots_ptr = Box::into_raw(slots) as *mut u32 as i64;

            // Leak a wrappers buffer (filled at JIT runtime via func_addr).
            let wrappers_buf: Box<[i64]> = vec![0i64; n].into_boxed_slice();
            let wrappers_buf_ptr = Box::into_raw(wrappers_buf) as *mut i64 as i64;

            // Emit func_addr stores into the wrappers buffer.
            let buf_addr_val = self.builder.ins().iconst(types::I64, wrappers_buf_ptr);
            for (j, &idx) in indices.iter().enumerate() {
                let wrapper_id = all_wrappers[idx].1;
                let func_ref = self
                    .module
                    .declare_func_in_func(wrapper_id, self.builder.func);
                let wrapper_ptr_val = self.builder.ins().func_addr(types::I64, func_ref);
                self.builder.ins().store(
                    MemFlags::trusted(),
                    wrapper_ptr_val,
                    buf_addr_val,
                    (j * 8) as i32,
                );
            }

            result.push(GotGroupData {
                got_base: *got_base,
                n,
                slots_ptr,
                wrappers_buf_ptr,
            });
        }
        Ok(result)
    }

    /// Emit GOT swaps for all groups, returning saved state for later restore.
    fn emit_got_swaps(
        &mut self,
        groups: &[GotGroupData],
        swap_id: FuncId,
    ) -> Vec<(i64, Value)> {
        let mut saved_vals = Vec::with_capacity(groups.len());
        for gg in groups {
            let swap_ref = self
                .module
                .declare_func_in_func(swap_id, self.builder.func);
            let got_base_val = self.builder.ins().iconst(types::I64, gg.got_base);
            let n_val = self.builder.ins().iconst(types::I64, gg.n as i64);
            let slots_val = self.builder.ins().iconst(types::I64, gg.slots_ptr);
            let wrappers_val = self.builder.ins().iconst(types::I64, gg.wrappers_buf_ptr);
            let call = self.builder.ins().call(
                swap_ref,
                &[got_base_val, n_val, slots_val, wrappers_val],
            );
            let saved = self.builder.inst_results(call)[0];
            saved_vals.push((gg.got_base, saved));
        }
        saved_vals
    }

    /// Emit GOT restores in reverse order from saved state.
    fn emit_got_restores(
        &mut self,
        saved_vals: &[(i64, Value)],
        restore_id: FuncId,
    ) {
        let restore_ref = self
            .module
            .declare_func_in_func(restore_id, self.builder.func);
        for (got_base, saved) in saved_vals.iter().rev() {
            let got_base_val = self.builder.ins().iconst(types::I64, *got_base);
            self.builder
                .ins()
                .call(restore_ref, &[got_base_val, *saved]);
        }
    }

    /// Emit IR for a single test iteration within the unrolled run-tests loop.
    ///
    /// Performs: GOT swap -> call test wrapper -> GOT restore -> collect trace ->
    /// extract nanos -> branch on pass/fail -> fold acc via closure call -> merge.
    #[allow(clippy::too_many_arguments)]
    fn emit_single_test_iteration(
        &mut self,
        current_acc: Value,
        pass_fn_val: Value,
        fail_fn_val: Value,
        tname_val: Value,
        test_wrapper_id: FuncId,
        got_groups: &[GotGroupData],
        trace_fns: &TraceRuntimeFns,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Swap all GOTs.
        let saved_vals = self.emit_got_swaps(got_groups, trace_fns.swap_id);

        // Call the test wrapper (zero args).
        let test_ref = self
            .module
            .declare_func_in_func(test_wrapper_id, self.builder.func);
        let test_call = self.builder.ins().call(test_ref, &[]);
        let raw_result = self.builder.inst_results(test_call)[0];

        // Restore all GOTs in reverse order.
        self.emit_got_restores(&saved_vals, trace_fns.restore_id);

        // Collect the trace tree.
        let collect_ref = self
            .module
            .declare_func_in_func(trace_fns.collect_id, self.builder.func);
        let collect_call = self.builder.ins().call(collect_ref, &[]);
        let trace_adt = self.builder.inst_results(collect_call)[0];

        // Extract timing: nanos of first child of root trace frame.
        let nanos_ref = self
            .module
            .declare_func_in_func(trace_fns.nanos_id, self.builder.func);
        let nanos_call = self.builder.ins().call(nanos_ref, &[trace_adt]);
        let nanos = self.builder.inst_results(nanos_call)[0];

        // Branch: None (pass, raw_result == 0) vs Some(reason) (fail).
        let pass_block = self.builder.create_block();
        let fail_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        let is_none = self.builder.ins().icmp_imm(IntCC::Equal, raw_result, 0);
        self.builder
            .ins()
            .brif(is_none, pass_block, &[], fail_block, &[]);

        // Pass block.
        self.emit_test_pass_block(
            pass_block,
            merge_block,
            pass_fn_val,
            current_acc,
            tname_val,
            nanos,
            trace_adt,
            span,
        )?;

        // Fail block.
        self.emit_test_fail_block(
            fail_block,
            merge_block,
            fail_fn_val,
            current_acc,
            tname_val,
            nanos,
            raw_result,
            trace_adt,
            span,
        )?;

        // Merge block: new acc from whichever branch executed.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Emit the pass block for a single test iteration.
    ///
    /// Inc tname (protect from consuming call), dec trace (pass_fn doesn't receive it),
    /// call pass_fn(acc, tname, nanos), jump to merge.
    #[allow(clippy::too_many_arguments)]
    fn emit_test_pass_block(
        &mut self,
        pass_block: Block,
        merge_block: Block,
        pass_fn_val: Value,
        current_acc: Value,
        tname_val: Value,
        nanos: Value,
        trace_adt: Value,
        span: Span,
    ) -> Result<(), CranelispError> {
        self.builder.switch_to_block(pass_block);
        self.builder.seal_block(pass_block);

        // Inc tname: protect from pass_fn's consuming dec.
        heap::emit_rc_inc(&mut self.builder, tname_val);

        // Dec trace: pass_fn doesn't receive it.
        if let Some(dealloc) = self.ctx.dealloc_func_id {
            heap::emit_rc_dec(
                &mut self.builder,
                self.module,
                trace_adt,
                dealloc,
                None, // no drop glue; Trace fields are RC'd independently
            );
        }

        // Call pass_fn(acc, tname, nanos) via closure call.
        let pass_acc = self.compile_closure_call(
            pass_fn_val,
            &[current_acc, tname_val, nanos],
            span,
        )?;

        self.builder.ins().jump(merge_block, &[pass_acc]);
        Ok(())
    }

    /// Emit the fail block for a single test iteration.
    ///
    /// Extract reason from Some, inc tname and reason (protect from consuming call),
    /// call fail_fn(acc, tname, nanos, reason, trace), dec the Some shell,
    /// jump to merge.
    #[allow(clippy::too_many_arguments)]
    fn emit_test_fail_block(
        &mut self,
        fail_block: Block,
        merge_block: Block,
        fail_fn_val: Value,
        current_acc: Value,
        tname_val: Value,
        nanos: Value,
        raw_result: Value,
        trace_adt: Value,
        span: Span,
    ) -> Result<(), CranelispError> {
        self.builder.switch_to_block(fail_block);
        self.builder.seal_block(fail_block);

        // Extract reason string from Some(reason).
        // Some layout: [rc_header(16) | tag(16) | reason(24)]
        let reason_str = heap::heap_load(
            &mut self.builder,
            raw_result,
            HeapAdt::field_offset(0), // offset 24: the reason string field
        );

        // Inc reason (extracted from Some, need own reference for consuming call).
        heap::emit_rc_inc(&mut self.builder, reason_str);

        // Inc tname: protect from fail_fn's consuming dec.
        heap::emit_rc_inc(&mut self.builder, tname_val);

        // Call fail_fn(acc, tname, nanos, reason, trace) via closure call.
        // trace_adt ownership transfers to fail_fn (no dec here).
        let fail_acc = self.compile_closure_call(
            fail_fn_val,
            &[current_acc, tname_val, nanos, reason_str, trace_adt],
            span,
        )?;

        // Dec the Some shell (reason was inc'd, so it survives).
        if let Some(dealloc) = self.ctx.dealloc_func_id {
            heap::emit_rc_dec(
                &mut self.builder,
                self.module,
                raw_result,
                dealloc,
                None,
            );
        }

        self.builder.ins().jump(merge_block, &[fail_acc]);
        Ok(())
    }
}

/// Compile-time data for a GOT group (one per module).
struct GotGroupData {
    got_base: i64,
    n: usize,
    slots_ptr: i64,
    wrappers_buf_ptr: i64,
}
