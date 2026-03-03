//! Trace form codegen: `compile_trace` and `compile_run_tests` methods for `FnCompiler`.
//!
//! Implements `(trace [modules] body)` — GOT-swap wrapper around a body expression,
//! returning a `Trace` ADT representing the call tree.
//!
//! Implements `(run-tests init pass-fn fail-fn)` — discovers all `test-*` functions in
//! `.test` modules, runs each with full GOT-swap tracing, and folds results via two
//! user-supplied functions. REPL-only (batch mode returns `init` unchanged).
//!
//! Phase 2: wrappers format parameter values and return values using
//! `cranelisp_trace_format` (backed by the REPL's `format_result_value`).
//! The TypeChecker pointer is set via `crate::jit::set_trace_tc` before evaluation.

use cranelift::codegen::ir::{BlockArg, StackSlotData, StackSlotKind};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use crate::ast::Expr;
use crate::error::{CranelispError, Span};
use crate::module::{DefCodegen, DefKind, ModuleEntry};
use crate::types::Type;

use super::{CallMode, FnCompiler};

/// Info about a single traced function collected from the module table.
struct TracedFn {
    name: String,
    /// Short module name (key in `tc.modules`), e.g. `"test"` for a `.test` module.
    module_short: String,
    got_base: i64,
    got_slot: usize,
    arity: usize,
    /// Code pointer for the ORIGINAL implementation (not the wrapper).
    /// Embedded as `iconst` in the wrapper so it calls the original, not itself.
    code_ptr: i64,
    /// Static parameter types (from function's type scheme), used to generate format calls.
    param_types: Vec<Type>,
    /// Static return type (from function's type scheme), used to generate result format call.
    result_type: Type,
}

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Compile a `(trace [modules] body)` expression.
    ///
    /// Returns a `Value` that is a heap pointer to a `Trace` ADT.
    pub(crate) fn compile_trace(
        &mut self,
        modules: &[String],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // In batch mode there is no per-module GOT, so tracing is unavailable.
        // Fall back to evaluating the body and returning an empty TraceCall.
        if matches!(self.call_mode, CallMode::Direct { .. }) {
            return self.compile_trace_no_swap(body, span);
        }

        // Collect user-defined functions from nominated modules (or all, if empty).
        let traced = self.collect_traced_fns(modules);

        if traced.is_empty() {
            return self.compile_trace_no_swap(body, span);
        }

        // Group by GOT base address (each module has its own GOT table).
        let mut got_groups: Vec<(i64, Vec<TracedFn>)> = Vec::new();
        for tf in traced {
            if let Some(grp) = got_groups.iter_mut().find(|(addr, _)| *addr == tf.got_base) {
                grp.1.push(tf);
            } else {
                got_groups.push((tf.got_base, vec![tf]));
            }
        }

        // Declare trace runtime functions in the module (idempotent for Import linkage).
        let swap_id =
            self.declare_trace_extern("cranelisp_trace_swap_got", 4, true, span)?;
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
            let call =
                self.builder
                    .ins()
                    .call(swap_ref, &[got_base_val, n_val, slots_val, wrappers_val]);
            let saved_got_val = self.builder.inst_results(call)[0];
            swap_results.push((*got_base, saved_got_val));
        }

        // Compile body with in_trace_body = true (disables lenient eval auto-sparking).
        let prev = self.in_trace_body;
        self.in_trace_body = true;
        let body_result = self.compile_expr(body)?;
        self.in_trace_body = prev;

        // Discard body result (dec RC if it is heap-allocated).
        let body_span = body.span();
        if let Some(body_ty) = self.expr_types.get(&body_span).cloned() {
            self.emit_dec(body_result, &body_ty);
        }

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

        // Call cranelisp_collect_trace() → Trace ADT heap ptr.
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
        let prev = self.in_trace_body;
        self.in_trace_body = true;
        let body_result = self.compile_expr(body)?;
        self.in_trace_body = prev;

        // Discard body result.
        let body_span = body.span();
        if let Some(body_ty) = self.expr_types.get(&body_span).cloned() {
            self.emit_dec(body_result, &body_ty);
        }

        // Return empty trace from collect_trace (handles empty stack gracefully).
        let collect_id =
            self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;
        let collect_ref = self
            .module
            .declare_func_in_func(collect_id, self.builder.func);
        let call = self.builder.ins().call(collect_ref, &[]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Collect all user-defined functions from nominated modules.
    ///
    /// If `nominated_modules` is empty, collects from all non-synthetic modules.
    /// Excludes synthetic modules (`primitives`, `macros`).
    /// Extracts parameter types and return type from each function's type scheme.
    fn collect_traced_fns(&self, nominated_modules: &[String]) -> Vec<TracedFn> {
        const SYNTHETIC: &[&str] = &["primitives", "macros"];
        let mut result = Vec::new();

        for (mod_path, cm) in self.modules {
            let short = mod_path.short_name();
            if SYNTHETIC.contains(&short) {
                continue;
            }
            if !nominated_modules.is_empty()
                && !nominated_modules.iter().any(|m| m == short)
            {
                continue;
            }
            let got_base = match cm.got_table_addr() {
                Some(addr) => addr,
                None => continue,
            };
            for (sym, entry) in &cm.symbols {
                if let ModuleEntry::Def {
                    scheme,
                    kind:
                        DefKind::UserFn {
                            codegen:
                                DefCodegen {
                                    got_slot: Some(slot),
                                    code_ptr: Some(ptr),
                                    param_count: Some(arity),
                                    ..
                                },
                            ..
                        },
                    ..
                } = entry
                {
                    if (*ptr).is_null() {
                        continue;
                    }
                    // Extract param/return types for format call generation.
                    let (param_types, result_type) = match &scheme.ty {
                        Type::Fn(params, ret) => (params.clone(), *ret.clone()),
                        _ => (vec![], Type::Int),
                    };
                    result.push(TracedFn {
                        name: sym.to_string(),
                        module_short: short.to_string(),
                        got_base,
                        got_slot: *slot,
                        arity: *arity,
                        code_ptr: *ptr as i64,
                        param_types,
                        result_type,
                    });
                }
            }
        }
        result
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
    /// The original code ptr is embedded as an `iconst` — calls bypass the GOT and
    /// call the original implementation directly. Recursive calls inside the original
    /// go through the (swapped) GOT, naturally building the call tree.
    ///
    /// Type pointers are leaked `Box<Type>` values, valid for the program lifetime.
    /// The TypeChecker pointer (read by `cranelisp_trace_format`) must be set via
    /// `crate::jit::set_trace_tc` before executing any trace expression.
    fn compile_trace_wrapper_fn(
        &mut self,
        tf: &TracedFn,
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

        // Leak the function name bytes — valid for the program lifetime.
        let name_bytes: Box<[u8]> = tf.name.as_bytes().to_vec().into_boxed_slice();
        let name_len = name_bytes.len() as i64;
        let name_ptr = Box::into_raw(name_bytes) as *mut u8 as i64;

        // Leak a Box<Type> for each parameter and for the result.
        // These are embedded as `iconst` in the wrapper and remain valid for program lifetime.
        let param_type_ptrs: Vec<i64> = tf.param_types.iter()
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
            wb.ins().call(enter_ref, &[name_ptr_val, name_len_val, params_count_val, array_ptr_val]);

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
            // We need a fresh format_ref for this block.
            let format_ref2 = self.module.declare_func_in_func(format_id, wb.func);
            let result_type_ptr_val = wb.ins().iconst(types::I64, result_type_ptr);
            let result_fmt_call = wb.ins().call(format_ref2, &[orig_result, result_type_ptr_val]);
            let result_str = wb.inst_results(result_fmt_call)[0];

            // cranelisp_trace_exit(orig_result, result_str) → final result
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

    /// Compile a `(run-tests init pass-fn fail-fn)` expression.
    ///
    /// Discovers all `test-*` zero-arg functions in `.test` modules (short name "test"),
    /// runs each with full GOT-swap tracing, and folds results:
    /// - pass: `(pass-fn acc test-name nanos) -> acc`
    /// - fail: `(fail-fn acc test-name nanos reason trace) -> acc`
    ///
    /// Returns the final accumulator value.
    /// In batch mode (no per-module GOT), returns `init` unchanged.
    pub(crate) fn compile_run_tests(
        &mut self,
        modules: &[String],
        init: &Expr,
        pass_fn: &Expr,
        fail_fn: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Batch mode: no GOT, so fall back to returning init unchanged.
        if matches!(self.call_mode, CallMode::Direct { .. }) {
            return self.compile_expr(init);
        }

        // Collect all user-defined functions for GOT swap.
        let traced = self.collect_traced_fns(modules);
        if traced.is_empty() {
            return self.compile_expr(init);
        }

        // Declare trace runtime externs (idempotent).
        let swap_id =
            self.declare_trace_extern("cranelisp_trace_swap_got", 4, true, span)?;
        let restore_id =
            self.declare_trace_extern("cranelisp_trace_restore_got", 2, false, span)?;
        let collect_id =
            self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;
        let nanos_id =
            self.declare_trace_extern("cranelisp_trace_first_child_nanos", 1, true, span)?;

        // Compile trace wrappers for all traced functions.
        let mut all_wrappers: Vec<(TracedFn, FuncId)> = Vec::new();
        for tf in traced {
            let wrapper_id = self.compile_trace_wrapper_fn(&tf, span)?;
            all_wrappers.push((tf, wrapper_id));
        }

        // Group by GOT base address.
        let mut got_groups: Vec<(i64, Vec<usize>)> = Vec::new();
        for (idx, (tf, _)) in all_wrappers.iter().enumerate() {
            if let Some(grp) = got_groups.iter_mut().find(|(b, _)| *b == tf.got_base) {
                grp.1.push(idx);
            } else {
                got_groups.push((tf.got_base, vec![idx]));
            }
        }

        // Identify test functions: zero-arg fns in "test" module with name "test-*".
        // `.test` modules have short name "test" in tc.modules.
        let test_fns: Vec<(String, FuncId)> = all_wrappers
            .iter()
            .filter(|(tf, _)| {
                tf.module_short == "test"
                    && tf.name.starts_with("test-")
                    && tf.arity == 0
            })
            .map(|(tf, wrapper_id)| (tf.name.clone(), *wrapper_id))
            .collect();

        if test_fns.is_empty() {
            return self.compile_expr(init);
        }

        // For each GOT group: allocate the slots array and wrappers buffer at compile time
        // (Rust host heap), then emit `func_addr` stores at JIT runtime to fill code ptrs.
        struct GotGroupData {
            got_base: i64,
            n: usize,
            slots_ptr: i64,
            wrappers_buf_ptr: i64,
        }
        let mut got_group_data: Vec<GotGroupData> = Vec::new();
        for (got_base, indices) in &got_groups {
            let n = indices.len();
            let slots: Box<[u32]> = indices
                .iter()
                .map(|&i| all_wrappers[i].0.got_slot as u32)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            let slots_ptr = Box::into_raw(slots) as *mut u32 as i64;

            let wrappers_buf: Box<[i64]> = vec![0i64; n].into_boxed_slice();
            let wrappers_buf_ptr = Box::into_raw(wrappers_buf) as *mut i64 as i64;

            // At JIT runtime, fill the wrappers buffer with actual code ptrs.
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

            got_group_data.push(GotGroupData {
                got_base: *got_base,
                n,
                slots_ptr,
                wrappers_buf_ptr,
            });
        }

        // Compile init, pass_fn, fail_fn expressions.
        let mut current_acc = self.compile_expr(init)?;
        let pass_fn_val = self.compile_expr(pass_fn)?;
        let fail_fn_val = self.compile_expr(fail_fn)?;

        let trace_ty = Type::ADT("Trace".to_string(), vec![]);

        // For each test function (unrolled IR loop):
        //   swap GOTs → call wrapper → restore GOTs → collect trace → fold result
        for (test_name, test_wrapper_id) in &test_fns {
            // a. Swap all GOTs, collecting saved indices for later restore.
            let mut saved_vals: Vec<(i64, Value)> = Vec::new();
            for gg in &got_group_data {
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

            // b. Call the test function's trace wrapper (zero args).
            //    The wrapper calls trace_enter, calls the original, then trace_exit.
            let test_ref = self
                .module
                .declare_func_in_func(*test_wrapper_id, self.builder.func);
            let test_call = self.builder.ins().call(test_ref, &[]);
            let raw_result = self.builder.inst_results(test_call)[0];

            // c. Restore all GOTs in reverse order.
            for (got_base, saved) in saved_vals.iter().rev() {
                let restore_ref = self
                    .module
                    .declare_func_in_func(restore_id, self.builder.func);
                let got_base_val = self.builder.ins().iconst(types::I64, *got_base);
                self.builder.ins().call(restore_ref, &[got_base_val, *saved]);
            }

            // d. Collect the trace tree.
            let collect_ref = self
                .module
                .declare_func_in_func(collect_id, self.builder.func);
            let collect_call = self.builder.ins().call(collect_ref, &[]);
            let trace_adt = self.builder.inst_results(collect_call)[0];

            // e. Extract timing: nanos of the test fn = first child of the root trace frame.
            let nanos_ref = self
                .module
                .declare_func_in_func(nanos_id, self.builder.func);
            let nanos_call = self.builder.ins().call(nanos_ref, &[trace_adt]);
            let nanos = self.builder.inst_results(nanos_call)[0];

            // f. Allocate the test name as a cranelisp heap string (compile-time host alloc).
            //    RC starts at 1; we emit_inc before each fn call so the fn's consuming dec
            //    brings RC back to 1 (string stays alive for lifetime of run-tests fn).
            let tname_heap =
                cranelisp_runtime::primitives::alloc_string(test_name.as_bytes());
            let tname_val = self.builder.ins().iconst(types::I64, tname_heap);

            // g. Branch: None (pass) vs Some(reason) (fail).
            let pass_block = self.builder.create_block();
            let fail_block = self.builder.create_block();
            let merge_block = self.builder.create_block();
            self.builder.append_block_param(merge_block, types::I64);

            let is_none = self.builder.ins().icmp_imm(IntCC::Equal, raw_result, 0);
            self.builder
                .ins()
                .brif(is_none, pass_block, &[], fail_block, &[]);

            // ── Pass block ──────────────────────────────────────────────────
            self.builder.switch_to_block(pass_block);
            self.builder.seal_block(pass_block);
            // Inc tname so pass_fn's consuming dec doesn't free the static string.
            self.emit_inc(tname_val, &Type::String);
            // Dec trace (pass_fn does not receive it; controlled-leak of inner fields).
            self.emit_dec(trace_adt, &trace_ty);
            let pass_acc =
                self.compile_closure_call(pass_fn_val, &[current_acc, tname_val, nanos]);
            self.builder
                .ins()
                .jump(merge_block, &[BlockArg::Value(pass_acc)]);

            // ── Fail block ──────────────────────────────────────────────────
            self.builder.switch_to_block(fail_block);
            self.builder.seal_block(fail_block);
            // Extract reason string from Some(val): Some heap = [tag=1, str_ptr].
            // We load the str_ptr (offset 8). The Some shell is a controlled leak.
            let reason_str = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), raw_result, 8);
            // Inc tname so fail_fn's consuming dec doesn't free the static string.
            self.emit_inc(tname_val, &Type::String);
            // fail_fn receives and owns trace_adt.
            let fail_acc = self.compile_closure_call(
                fail_fn_val,
                &[current_acc, tname_val, nanos, reason_str, trace_adt],
            );
            self.builder
                .ins()
                .jump(merge_block, &[BlockArg::Value(fail_acc)]);

            // ── Merge block ─────────────────────────────────────────────────
            self.builder.switch_to_block(merge_block);
            self.builder.seal_block(merge_block);
            current_acc = self.builder.block_params(merge_block)[0];
        }

        // Release pass_fn and fail_fn closures.
        if let Some(ty) = self.expr_types.get(&pass_fn.span()).cloned() {
            self.emit_dec(pass_fn_val, &ty);
        }
        if let Some(ty) = self.expr_types.get(&fail_fn.span()).cloned() {
            self.emit_dec(fail_fn_val, &ty);
        }

        Ok(current_acc)
    }
}
