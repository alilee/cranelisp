// Control flow, binding, and closure codegen.
//
// compile_if, compile_let, compile_lambda

use std::collections::HashSet;

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CompileMode, CranelispError, Expr, HeapCategory, ResolvedCall, Span, Symbol, Type};

use crate::heap::{self, HeapClosure};
use crate::operators;

use super::FnCompiler;

impl<'a, M: Module> FnCompiler<'a, M> {
    // --- Let expression ---

    pub(crate) fn compile_let(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Check if lenient evaluation applies.
        // Skip sparkability analysis inside trace bodies — trace must
        // execute sequentially to produce deterministic trace trees.
        if !*LENIENT_DISABLED && !self.in_trace_body {
            // Collect known constructor names to exclude from sparking.
            let constructors: HashSet<Symbol> = self
                .ctx
                .constructor_to_type
                .keys()
                .cloned()
                .collect();
            let sparkable = find_sparkable_bindings(bindings, &constructors);
            if sparkable.len() >= 2 {
                return self.compile_let_lenient(bindings, body, &sparkable, span);
            }
        }

        self.compile_let_sequential(bindings, body, span)
    }

    /// Compile a let expression sequentially (no lenient evaluation).
    fn compile_let_sequential(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        _span: Span,
    ) -> Result<Value, CranelispError> {
        // Push a new scope frame.
        self.push_scope();

        // Compile each binding.
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        for (name, val_expr) in bindings {
            // Record the binding's type from the typechecker's expr_types map.
            if let Some(ty) = self.ctx.expr_types.get(&val_expr.span()) {
                self.variable_types.insert(name.clone(), ty.clone());
            }

            let val = self.compile_expr(val_expr)?;

            // If compile_expr produced a closure with drop glue, record it.
            if let Some(glue_id) = self.pending_closure_drop_glue.take() {
                self.closure_drop_glue.insert(name.clone(), glue_id);
            }

            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(name.clone());
        }

        // Body inherits tail position.
        self.in_tail_position = saved_tail;

        // Determine which variable (if any) is the return value — its
        // ownership transfers to the caller, so skip dec for it.
        let skip_var = Self::return_var_in_scope(body, self.scope_stack.last());

        let result = self.compile_expr(body)?;

        // Protect the return value from scope cleanup if skip_var didn't
        // identify a specific variable to preserve (non-trivial body).
        self.protect_return_value(&skip_var, result, body);

        // Pop the scope frame, emitting rc_dec for heap-typed bindings
        // except the return value.
        self.pop_scope_with_cleanup(skip_var.as_ref());

        Ok(result)
    }

    /// Compile a let expression with lenient evaluation (parallel sparkable bindings).
    ///
    /// See design/backend/lenient-eval.md §4.2 for the algorithm.
    fn compile_let_lenient(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        sparkable: &[usize],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let sparkable_set: HashSet<usize> = sparkable.iter().copied().collect();

        self.push_scope();
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Phase 1: Create and spark IVars for sparkable bindings.
        let mut ivar_map: std::collections::HashMap<usize, Value> = std::collections::HashMap::new();

        for &idx in sparkable {
            let (_name, val_expr) = &bindings[idx];

            // Wrap the value expression in a zero-arg lambda (thunk).
            let thunk_expr = Expr::Lambda {
                params: vec![],
                param_annotations: vec![],
                body: Box::new(val_expr.clone()),
                span: val_expr.span(),
            };
            let thunk_val = self.compile_expr(&thunk_expr)?;

            // Call cranelisp_ivar_create(thunk_ptr) -> ivar_ptr
            let ivar_val = self.emit_extern_call_1(
                "cranelisp_ivar_create", thunk_val, span,
            )?;

            // Call cranelisp_ivar_spark(ivar_ptr)
            let _spark_result = self.emit_extern_call_1(
                "cranelisp_ivar_spark", ivar_val, span,
            )?;

            ivar_map.insert(idx, ivar_val);
        }

        // Phase 2: Process all bindings in order.
        for (i, (name, val_expr)) in bindings.iter().enumerate() {
            if let Some(ty) = self.ctx.expr_types.get(&val_expr.span()) {
                self.variable_types.insert(name.clone(), ty.clone());
            }

            let val = if sparkable_set.contains(&i) {
                // Force the IVar and dec our reference.
                let ivar_val = ivar_map[&i];
                let forced_val = self.emit_extern_call_1(
                    "cranelisp_ivar_force", ivar_val, span,
                )?;

                // Dec the IVar (main thread's reference).
                // The IVar has atomic RC; the spark task also dec's.
                self.emit_rc_dec_for_ivar(ivar_val, span)?;

                forced_val
            } else {
                // Non-sparkable: compile normally.
                self.compile_expr(val_expr)?
            };

            if let Some(glue_id) = self.pending_closure_drop_glue.take() {
                self.closure_drop_glue.insert(name.clone(), glue_id);
            }

            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(name.clone());
        }

        // Phase 3: Compile body.
        self.in_tail_position = saved_tail;
        let skip_var = Self::return_var_in_scope(body, self.scope_stack.last());
        let result = self.compile_expr(body)?;
        self.protect_return_value(&skip_var, result, body);
        self.pop_scope_with_cleanup(skip_var.as_ref());

        Ok(result)
    }

    /// Emit a call to an extern "C" function with one i64 argument, returning i64.
    fn emit_extern_call_1(
        &mut self,
        name: &str,
        arg: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern function '{name}': {e}"),
                span,
            })?;

        let local_func = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(local_func, &[arg]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Emit an inline RC dec for an IVar pointer.
    ///
    /// IVars use atomic RC at offset +8. When dec brings RC to 0,
    /// call heap_dealloc to free. This is a simplified version of
    /// the general emit_rc_dec that doesn't need drop glue (IVars
    /// have no recursive heap fields to clean up).
    fn emit_rc_dec_for_ivar(&mut self, ivar_val: Value, span: Span) -> Result<(), CranelispError> {
        // Load current RC from ivar + 8
        let rc_offset = self.builder.ins().iconst(types::I64, 8);
        let rc_addr = self.builder.ins().iadd(ivar_val, rc_offset);

        // atomic_rmw sub 1 -> old_rc
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::new(),
            cranelift::codegen::ir::AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // If old_rc == 1, free the IVar.
        let free_block = self.builder.create_block();
        let cont_block = self.builder.create_block();

        let one_val = self.builder.ins().iconst(types::I64, 1);
        let is_last = self.builder.ins().icmp(IntCC::Equal, old_rc, one_val);
        self.builder
            .ins()
            .brif(is_last, free_block, &[], cont_block, &[]);

        // Free block: call heap_dealloc(ivar_ptr).
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);

        // Acquire fence before reading object fields (not needed here since
        // we don't read fields, but consistent with Decision 13).
        self.builder.ins().fence();

        let _dealloc_result = self
            .emit_extern_call_1("runtime/dealloc", ivar_val, span)?;
        self.builder.ins().jump(cont_block, &[]);

        // Continue.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        Ok(())
    }

    /// Compile an `Expr::ParBind` — sequential fallback until continuation
    /// closure infrastructure is ready.
    ///
    /// ParBind bindings are semantically independent (no binding references
    /// another), but true parallel IO dispatch requires a continuation closure
    /// that receives results from the trampoline. Until that infrastructure
    /// exists, we compile ParBind identically to a sequential let.
    ///
    /// The previous implementation (Sprint 25 Wave 3) emitted a Par node
    /// (heap allocation with tag/count/branches) but had no continuation to
    /// consume it, causing a leak. Removed per review finding B1+I1.
    ///
    /// TODO(Sprint 26): Compile a proper continuation closure that receives
    /// results_ptr from the trampoline, enabling full IO-level parallelism
    /// end-to-end. At that point, re-introduce Par node emission here.
    ///
    /// See design/backend/io-scheduling.md §4 for the target algorithm.
    pub(crate) fn compile_par_bind(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Delegate to sequential compilation. ParBind bindings are independent
        // so sequential order is safe (just not yet parallel).
        self.compile_let_sequential(bindings, body, span)
    }

    // --- If expression ---

    pub(crate) fn compile_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;

        // Condition is never in tail position.
        self.in_tail_position = false;
        let cond_val = self.compile_expr(cond)?;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        self.builder
            .ins()
            .brif(cond_val, then_block, &[], else_block, &[]);

        // Then branch.
        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        self.in_tail_position = saved_tail;
        let then_val = self.compile_expr(then_branch)?;
        self.builder.ins().jump(merge_block, &[then_val]);

        // Else branch.
        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        self.in_tail_position = saved_tail;
        let else_val = self.compile_expr(else_branch)?;
        self.builder.ins().jump(merge_block, &[else_val]);

        // Merge block.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        Ok(self.builder.block_params(merge_block)[0])
    }

    // --- Lambda expression (Ring 1: closures with captures) ---

    /// Compile a lambda expression.
    ///
    /// Strategy:
    /// 1. Determine which variables are captured from the enclosing scope.
    /// 2. Compile an inner function with signature (env_ptr, params...) -> i64
    ///    that loads captured values from the environment.
    /// 3. At the lambda site, allocate a closure: [header | code_ptr | captures...]
    /// 4. Store the inner function pointer and captured values.
    pub(crate) fn compile_lambda(
        &mut self,
        params: &[Symbol],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    span,
                })?;

        // Determine captured variables: free variables in the body that are
        // bound in the enclosing scope (not the lambda's own params).
        // Sorted by name for deterministic layout (ring1-checklist section 5.8).
        let free_vars = find_free_vars(body, params);
        let mut captures: Vec<Symbol> = free_vars
            .into_iter()
            .filter(|name| self.variables.contains_key(name))
            .collect();
        captures.sort();

        // Compile the inner function as a separate function definition.
        // Signature: (env_ptr: i64, param_0: i64, ..., param_n: i64) -> i64
        let inner_name = format!(
            "__lambda_{}_{}__",
            span.start, span.end
        );

        let inner_param_count = 1 + params.len(); // env_ptr + user params
        let mut sig = self.module.make_signature();
        for _ in 0..inner_param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let inner_func_id = self
            .module
            .declare_function(&inner_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare lambda function: {e}"),
                span,
            })?;

        // Compile the inner function body using a new Cranelift context.
        self.compile_lambda_body(
            inner_func_id,
            params,
            &captures,
            body,
            span,
        )?;

        // At the lambda site: allocate closure [header | code_ptr | captures...]
        let payload_size = HeapClosure::payload_size(captures.len()) as i64;
        let base_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            payload_size,
        );

        // Get the inner function address.
        let inner_func_ref = self
            .module
            .declare_func_in_func(inner_func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, inner_func_ref);

        // Store code_ptr at HeapClosure::CODE_PTR_OFFSET (16).
        heap::heap_store(
            &mut self.builder,
            code_ptr,
            base_ptr,
            HeapClosure::CODE_PTR_OFFSET,
        );

        // Build closure drop glue and store pointer at DROP_GLUE_PTR_OFFSET (24).
        // Must be built BEFORE storing captures (build_closure_drop_glue needs
        // self.module which is borrowed mutably during function definition).
        let drop_glue = self.build_closure_drop_glue(&captures, span)?;
        let drop_glue_val = if let Some(glue_id) = drop_glue {
            let glue_ref = self
                .module
                .declare_func_in_func(glue_id, self.builder.func);
            self.builder.ins().func_addr(types::I64, glue_ref)
        } else {
            self.builder.ins().iconst(types::I64, 0)
        };
        heap::heap_store(
            &mut self.builder,
            drop_glue_val,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );
        self.pending_closure_drop_glue = drop_glue;

        // Store each captured value at HeapClosure::capture_offset(i).
        // For heap-typed captures, emit rc_inc so the closure env holds
        // its own reference (the enclosing scope retains its reference
        // independently and will dec it at scope exit).
        for (i, cap_name) in captures.iter().enumerate() {
            if let Some(var) = self.variables.get(cap_name) {
                let cap_val = self.builder.use_var(*var);
                heap::heap_store(
                    &mut self.builder,
                    cap_val,
                    base_ptr,
                    HeapClosure::capture_offset(i),
                );

                // Inc heap-typed captures: the closure env needs its own reference.
                if let Some(ty) = self.variable_types.get(cap_name) {
                    let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
                    match category {
                        HeapCategory::AlwaysHeap => {
                            heap::emit_rc_inc(&mut self.builder, cap_val);
                        }
                        HeapCategory::Mixed => {
                            heap::emit_rc_inc_guarded(&mut self.builder, cap_val);
                        }
                        HeapCategory::NeverHeap => {}
                    }
                }
            }
        }

        Ok(base_ptr)
    }

    /// Build a closure drop glue function: `(ptr: i64) -> ()`.
    ///
    /// For each heap-typed capture, loads the value from the closure env
    /// at its known offset and emits `rc_dec` (with guard for Mixed types).
    /// Returns `None` if no captures are heap-typed.
    fn build_closure_drop_glue(
        &mut self,
        captures: &[Symbol],
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/dealloc not declared (need declare_intrinsics)".into(),
                span,
            }
        })?;

        // Collect (capture_index, type, heap_category) for heap-typed captures.
        let heap_captures: Vec<(usize, Type, HeapCategory)> = captures
            .iter()
            .enumerate()
            .filter_map(|(i, cap_name)| {
                let ty = self.variable_types.get(cap_name)?;
                let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
                match category {
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed => {
                        Some((i, ty.clone(), category))
                    }
                    HeapCategory::NeverHeap => None,
                }
            })
            .collect();

        if heap_captures.is_empty() {
            return Ok(None);
        }

        // Build the drop glue function.
        let glue_name = format!(
            "runtime/closure_drop_glue_{}_{}",
            span.start, span.end
        );

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // closure ptr

        let glue_func_id = self
            .module
            .declare_function(&glue_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare closure drop glue fn: {e}"),
                span,
            })?;

        let mut ctx = self.module.make_context();
        let mut func_ctx = FunctionBuilderContext::new();
        ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let closure_ptr = builder.block_params(entry)[0];

        // For each heap-typed capture, load from its offset and dec.
        for (cap_idx, _cap_ty, category) in &heap_captures {
            let cap_val = heap::heap_load(
                &mut builder,
                closure_ptr,
                HeapClosure::capture_offset(*cap_idx),
            );
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_dec(
                        &mut builder,
                        self.module,
                        cap_val,
                        dealloc_id,
                        None,
                    );
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_dec_guarded(
                        &mut builder,
                        self.module,
                        cap_val,
                        dealloc_id,
                        None,
                        true,
                    );
                }
                HeapCategory::NeverHeap => {} // unreachable, filtered above
            }
        }

        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(glue_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define closure drop glue fn: {e}"),
                span,
            })?;

        Ok(Some(glue_func_id))
    }

    /// Compile the body of a lambda as a separate JIT function.
    ///
    /// The inner function has signature (env_ptr, params...) -> i64.
    /// Captured values are loaded from the environment.
    fn compile_lambda_body(
        &mut self,
        func_id: cranelift_module::FuncId,
        params: &[Symbol],
        captures: &[Symbol],
        body: &Expr,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Build the inner function using a separate codegen context.
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();

        // Signature: (env_ptr, params...) -> i64
        let total_params = 1 + params.len();
        for _ in 0..total_params {
            inner_ctx.func.signature.params.push(AbiParam::new(types::I64));
        }
        inner_ctx.func.signature.returns.push(AbiParam::new(types::I64));

        let mut builder = FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let block_params = builder.block_params(entry_block).to_vec();
        let env_ptr = block_params[0];

        let last_uses = heap::compute_last_uses(body);
        let mut inner_compiler = FnCompiler::inner(
            builder,
            self.module,
            self.ctx,
            params.len(),
            last_uses,
        );

        // Bind captured variables from the environment.
        for (i, cap_name) in captures.iter().enumerate() {
            let cap_val = heap::heap_load(
                &mut inner_compiler.builder,
                env_ptr,
                HeapClosure::capture_offset(i),
            ); // capture_i: i64
            let var = inner_compiler.fresh_variable();
            inner_compiler.builder.declare_var(var, types::I64);
            inner_compiler.builder.def_var(var, cap_val);
            inner_compiler.variables.insert(cap_name.clone(), var);
        }

        // Look up the lambda's inferred type to get parameter types.
        // This is essential for unused parameters: derive_param_type scans
        // use sites, so unused params (e.g., `_s` in `(fn [_s] 42)`) would
        // have no type recorded and scope cleanup would skip their RC dec.
        let lambda_param_types: Vec<Option<Type>> = if let Some(Type::Fn(param_types, _)) =
            inner_compiler.ctx.expr_types.get(&span)
        {
            param_types.iter().map(|t| Some(t.clone())).collect()
        } else {
            vec![None; params.len()]
        };

        // Bind lambda parameters from function params (after env_ptr).
        // Add params to scope_stack and variable_types so that
        // pop_scope_with_cleanup will emit rc_dec for heap-typed params.
        // This implements the consuming calling convention for closure bodies:
        // the closure owns its parameters and must dec them at exit.
        // Without this, unused params (e.g., `_` in `(fn [_] b)`) leak.
        for (i, param_name) in params.iter().enumerate() {
            let val = block_params[i + 1]; // skip env_ptr
            let var = inner_compiler.fresh_variable();
            inner_compiler.builder.declare_var(var, types::I64);
            inner_compiler.builder.def_var(var, val);
            inner_compiler.variables.insert(param_name.clone(), var);
            inner_compiler
                .scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(param_name.clone());

            // Use the lambda's inferred param type (from expr_types) first.
            // Fall back to derive_param_type (use-site inference) if the
            // lambda type isn't available.
            if let Some(Some(ty)) = lambda_param_types.get(i) {
                inner_compiler.variable_types.insert(param_name.clone(), ty.clone());
            } else if let Some(ty) = inner_compiler.derive_param_type(param_name) {
                inner_compiler.variable_types.insert(param_name.clone(), ty);
            }
        }

        // Mark captured variables so they are not eligible for last-use transfer.
        for cap_name in captures {
            inner_compiler.captured_vars.insert(cap_name.clone());
        }

        // Compile the body with scope cleanup for parameters.
        // This mirrors compile_body: identify the return value variable (if any),
        // protect it from scope cleanup, then dec all other heap-typed params.
        let skip_var = Self::return_var_in_scope(body, inner_compiler.scope_stack.last());
        let result = inner_compiler.compile_expr(body)?;
        inner_compiler.protect_return_value(&skip_var, result, body);
        inner_compiler.pop_scope_with_cleanup(skip_var.as_ref());

        inner_compiler.builder.ins().return_(&[result]);
        inner_compiler.builder.seal_all_blocks();
        inner_compiler.builder.finalize();

        // Define the function in the JIT module.
        self.module
            .define_function(func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define lambda function: {e}"),
                span,
            })?;

        Ok(())
    }

    // --- Named function as value ---

    /// Check if a name is a known top-level function (eligible for wrapping).
    pub(crate) fn is_known_function(&self, name: &Symbol) -> bool {
        self.ctx.func_ids.contains_key(name)
            || self
                .ctx
                .got_slots
                .is_some_and(|slots| slots.contains_key(name))
    }

    /// Wrap a named top-level function as a zero-capture closure.
    ///
    /// Generates a wrapper function with signature `(env_ptr, params...) -> i64`
    /// that ignores env_ptr and calls the real function directly.
    /// Allocates a closure `[header | code_ptr]` with zero captures.
    pub(crate) fn compile_fn_as_value(
        &mut self,
        name: &Symbol,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    span,
                })?;

        let arity = self.ctx.func_arities.get(name).copied().ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!("unknown arity for function: {name}"),
                span,
            }
        })?;

        // Compile the wrapper function.
        let wrapper_name = format!("__wrap_{name}_{}_{}__", span.start, span.end);
        let wrapper_param_count = 1 + arity; // env_ptr + user params
        let mut sig = self.module.make_signature();
        for _ in 0..wrapper_param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_function(&wrapper_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare wrapper function: {e}"),
                span,
            })?;

        self.compile_fn_wrapper_body(wrapper_func_id, name, arity, span)?;

        // Allocate a closure with zero captures: [header | code_ptr].
        let payload_size = HeapClosure::payload_size(0) as i64;
        let base_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            payload_size,
        );

        // Store the wrapper function pointer.
        let wrapper_ref = self
            .module
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, wrapper_ref);
        heap::heap_store(
            &mut self.builder,
            code_ptr,
            base_ptr,
            HeapClosure::CODE_PTR_OFFSET,
        );

        // Store zero drop glue pointer (no captures to drop).
        let zero = self.builder.ins().iconst(types::I64, 0);
        heap::heap_store(
            &mut self.builder,
            zero,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        Ok(base_ptr)
    }

    /// Compile a wrapper function body: (env_ptr, params...) -> i64.
    /// Ignores env_ptr and calls the real function with the params.
    fn compile_fn_wrapper_body(
        &mut self,
        func_id: cranelift_module::FuncId,
        target_name: &Symbol,
        arity: usize,
        span: Span,
    ) -> Result<(), CranelispError> {
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();

        // Signature: (env_ptr, params...) -> i64
        for _ in 0..1 + arity {
            inner_ctx.func.signature.params.push(AbiParam::new(types::I64));
        }
        inner_ctx.func.signature.returns.push(AbiParam::new(types::I64));

        let mut builder =
            FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let block_params = builder.block_params(entry_block).to_vec();
        let user_params: Vec<Value> = block_params[1..].to_vec(); // skip env_ptr

        let result = self.emit_wrapper_call(
            &mut builder, target_name, &user_params, span,
        )?;

        builder.ins().return_(&[result]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define wrapper function: {e}"),
                span,
            })?;

        Ok(())
    }

    /// Emit the call instruction inside a wrapper function body.
    ///
    /// Batch/Release: direct `call` via FuncId.
    /// Interactive: GOT-indirect `call_indirect`.
    fn emit_wrapper_call(
        &mut self,
        builder: &mut FunctionBuilder,
        target_name: &Symbol,
        user_params: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        match self.ctx.mode {
            CompileMode::Batch | CompileMode::Release => {
                let target_id =
                    self.ctx.func_ids.get(target_name).ok_or_else(|| {
                        CranelispError::CodegenError {
                            message: format!("undefined function: {target_name}"),
                            span,
                        }
                    })?;
                let target_ref =
                    self.module.declare_func_in_func(*target_id, builder.func);
                let call = builder.ins().call(target_ref, user_params);
                Ok(builder.inst_results(call)[0])
            }
            CompileMode::Interactive => {
                // Use resolve_got_entry to check both local and cross-module GOT,
                // matching the lookup strategy used by compile_direct_call.
                let (got_base, slot) = self.resolve_got_entry(target_name, span)?;

                let slot_offset = (slot * 8) as i64;
                let base_val = builder.ins().iconst(types::I64, got_base);
                let slot_addr = builder.ins().iadd_imm(base_val, slot_offset);
                let func_ptr = builder.ins().load(
                    types::I64, MemFlags::trusted(), slot_addr, 0,
                );

                let mut sig = self.module.make_signature();
                for _ in user_params {
                    sig.params.push(AbiParam::new(types::I64));
                }
                sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = builder.import_signature(sig);

                let call = builder.ins().call_indirect(sig_ref, func_ptr, user_params);
                Ok(builder.inst_results(call)[0])
            }
        }
    }

    /// Emit the call to the auto-curry target inside a wrapper function body.
    ///
    /// When the target is a trait method or builtin, this emits the appropriate
    /// inline IR or extern call directly, instead of trying to call by name
    /// (which fails for inline builtins like `add-i64` that have no JIT symbol).
    fn emit_curry_target_call(
        &mut self,
        builder: &mut FunctionBuilder,
        target_name: &Symbol,
        all_args: &[Value],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
    ) -> Result<Value, CranelispError> {
        if let Some(resolved) = trait_resolution {
            match resolved {
                ResolvedCall::TraitMethod {
                    trait_name,
                    method_name,
                    impl_type,
                    mangled_name,
                } => {
                    // Check if this maps to an inline primitive (e.g., add-i64 → iadd).
                    if let Some(prim_name) =
                        operators::primitive_for_trait_method(trait_name, method_name, impl_type)
                    {
                        if is_extern_primitive_in_wrapper(prim_name) {
                            return emit_extern_call_in_wrapper(
                                builder, self.module, prim_name, all_args, span,
                            );
                        }

                        // neq-string: call str-eq (extern) and negate the result.
                        if prim_name == "neq-string" {
                            let eq_result = emit_extern_call_in_wrapper(
                                builder, self.module, "str-eq", all_args, span,
                            )?;
                            return Ok(builder.ins().bxor_imm(eq_result, 1));
                        }

                        // Inline builtin (e.g., add-i64 → iadd).
                        return operators::emit_builtin_op(
                            builder, prim_name, all_args, span,
                            self.module, self.ctx.panic_func_id,
                        );
                    }

                    // Not a primitive: user-defined trait method — call by mangled name.
                    let sym = Symbol::from(mangled_name.as_ref());
                    return self.emit_wrapper_call(builder, &sym, all_args, span);
                }
                ResolvedCall::BuiltinFn { name: jit_name } => {
                    // Named builtin resolved by the typechecker.
                    if is_extern_primitive_in_wrapper(jit_name) {
                        return emit_extern_call_in_wrapper(
                            builder, self.module, jit_name, all_args, span,
                        );
                    }
                    if operators::is_known_builtin(jit_name) {
                        return operators::emit_builtin_op(
                            builder, jit_name, all_args, span,
                            self.module, self.ctx.panic_func_id,
                        );
                    }
                    // Unknown builtin: treat as extern.
                    return emit_extern_call_in_wrapper(
                        builder, self.module, jit_name, all_args, span,
                    );
                }
                _ => {} // SigDispatch, AutoCurry — fall through to emit_wrapper_call
            }
        }

        // No trait resolution, or resolution didn't match — call by name.
        self.emit_wrapper_call(builder, target_name, all_args, span)
    }

    // --- Auto-curry codegen ---

    /// Compile an auto-curried partial application.
    ///
    /// Produces a closure that captures the applied arguments and, when called
    /// with the remaining arguments, forwards all to the target function.
    ///
    /// Layout: `[rc_header | code_ptr | drop_glue_ptr | cap_0 ... cap_n]`
    #[allow(clippy::too_many_arguments)] // Curry context requires all parameters
    pub(crate) fn compile_auto_curry(
        &mut self,
        target_name: &Symbol,
        applied_vals: &[Value],
        applied_count: usize,
        total_count: usize,
        args: &[Expr],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    span,
                })?;

        let remaining_count = total_count - applied_count;

        // Classify each applied arg's heap category for RC management.
        let arg_categories: Vec<HeapCategory> = args
            .iter()
            .map(|arg| {
                self.ctx
                    .expr_types
                    .get(&arg.span())
                    .map(|ty| HeapCategory::classify(ty, Some(self.ctx.type_defs)))
                    .unwrap_or(HeapCategory::NeverHeap)
            })
            .collect();

        // 1. Compile the wrapper function.
        let wrapper_func_id = self.compile_auto_curry_wrapper(
            target_name,
            applied_count,
            remaining_count,
            &arg_categories,
            span,
            trait_resolution,
        )?;

        // 2. Build drop glue for heap-typed captures.
        let drop_glue_id = self.build_auto_curry_drop_glue(
            &arg_categories,
            span,
        )?;

        // 3. Allocate closure env.
        let payload_size = HeapClosure::payload_size(applied_count) as i64;
        let base_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            payload_size,
        );

        // Store wrapper code_ptr at CODE_PTR_OFFSET (16).
        let wrapper_ref = self
            .module
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, wrapper_ref);
        heap::heap_store(
            &mut self.builder,
            code_ptr,
            base_ptr,
            HeapClosure::CODE_PTR_OFFSET,
        );

        // Store drop glue pointer at DROP_GLUE_PTR_OFFSET (24).
        let drop_glue_val = if let Some(glue_id) = drop_glue_id {
            let glue_ref = self
                .module
                .declare_func_in_func(glue_id, self.builder.func);
            self.builder.ins().func_addr(types::I64, glue_ref)
        } else {
            self.builder.ins().iconst(types::I64, 0)
        };
        heap::heap_store(
            &mut self.builder,
            drop_glue_val,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        // 4. Store applied args as captures, with RC inc for heap-typed values.
        for (i, &val) in applied_vals.iter().enumerate() {
            heap::heap_store(
                &mut self.builder,
                val,
                base_ptr,
                HeapClosure::capture_offset(i),
            );

            // Inc heap-typed captures: closure env needs its own reference.
            match arg_categories[i] {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, val);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut self.builder, val);
                }
                HeapCategory::NeverHeap => {}
            }
        }

        Ok(base_ptr)
    }

    /// Compile the wrapper function for auto-curry.
    ///
    /// Signature: `(env_ptr, remaining_0, ..., remaining_k) -> i64`
    /// Body: load captures from env, inc heap captures, call target with all args.
    fn compile_auto_curry_wrapper(
        &mut self,
        target_name: &Symbol,
        applied_count: usize,
        remaining_count: usize,
        arg_categories: &[HeapCategory],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
    ) -> Result<cranelift_module::FuncId, CranelispError> {
        let wrapper_name = format!(
            "__curry_{target_name}_{}_{}__",
            span.start, span.end
        );

        // Signature: (env_ptr, remaining_0..remaining_k) -> i64
        let param_count = 1 + remaining_count; // env_ptr + remaining args
        let mut sig = self.module.make_signature();
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_function(&wrapper_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare auto-curry wrapper: {e}"),
                span,
            })?;

        // Build the wrapper body in a separate codegen context.
        let mut ctx = self.module.make_context();
        let mut func_ctx = FunctionBuilderContext::new();
        ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let block_params = builder.block_params(entry).to_vec();
        let env_ptr = block_params[0];
        let remaining_args: Vec<Value> = block_params[1..].to_vec();

        // Load captured args from env and inc heap-typed captures.
        // The wrapper must inc before passing to the consuming callee,
        // so the closure env's reference stays intact across calls.
        let mut all_args = Vec::with_capacity(applied_count + remaining_count);
        for (i, category) in arg_categories.iter().enumerate().take(applied_count) {
            let cap_val = heap::heap_load(
                &mut builder,
                env_ptr,
                HeapClosure::capture_offset(i),
            );
            // Inc heap-typed captures before passing to consuming callee.
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut builder, cap_val);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut builder, cap_val);
                }
                HeapCategory::NeverHeap => {}
            }
            all_args.push(cap_val);
        }
        all_args.extend_from_slice(&remaining_args);

        // Call the target function. For trait methods resolved to inline
        // builtins (e.g., + → add-i64), emit the IR directly in the wrapper.
        // For extern primitives, emit an extern call. For user functions,
        // use emit_wrapper_call (handles Batch/Interactive modes).
        let result = self.emit_curry_target_call(
            &mut builder,
            target_name,
            &all_args,
            span,
            trait_resolution,
        )?;

        builder.ins().return_(&[result]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(wrapper_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define auto-curry wrapper: {e}"),
                span,
            })?;

        Ok(wrapper_func_id)
    }

    /// Build drop glue for an auto-curry closure's captured arguments.
    ///
    /// For each heap-typed capture, loads from the closure env at its offset
    /// and emits `rc_dec`. Returns `None` if no captures are heap-typed.
    fn build_auto_curry_drop_glue(
        &mut self,
        arg_categories: &[HeapCategory],
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/dealloc not declared (need declare_intrinsics)".into(),
                span,
            }
        })?;

        // Collect indices of heap-typed captures.
        let heap_indices: Vec<(usize, HeapCategory)> = arg_categories
            .iter()
            .enumerate()
            .filter_map(|(i, cat)| match cat {
                HeapCategory::AlwaysHeap | HeapCategory::Mixed => Some((i, *cat)),
                HeapCategory::NeverHeap => None,
            })
            .collect();

        if heap_indices.is_empty() {
            return Ok(None);
        }

        let glue_name = format!(
            "runtime/curry_drop_glue_{}_{}",
            span.start, span.end
        );

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // closure ptr

        let glue_func_id = self
            .module
            .declare_function(&glue_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare auto-curry drop glue: {e}"),
                span,
            })?;

        let mut ctx = self.module.make_context();
        let mut func_ctx = FunctionBuilderContext::new();
        ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let closure_ptr = builder.block_params(entry)[0];

        // For each heap-typed capture, load and dec.
        for (cap_idx, category) in &heap_indices {
            let cap_val = heap::heap_load(
                &mut builder,
                closure_ptr,
                HeapClosure::capture_offset(*cap_idx),
            );
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_dec(
                        &mut builder,
                        self.module,
                        cap_val,
                        dealloc_id,
                        None,
                    );
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_dec_guarded(
                        &mut builder,
                        self.module,
                        cap_val,
                        dealloc_id,
                        None,
                        true,
                    );
                }
                HeapCategory::NeverHeap => {} // unreachable, filtered above
            }
        }

        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(glue_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define auto-curry drop glue: {e}"),
                span,
            })?;

        Ok(Some(glue_func_id))
    }
}

/// Find free variables in an expression (variables not bound by local let/lambda/match).
fn find_free_vars(expr: &Expr, bound: &[Symbol]) -> Vec<Symbol> {
    let mut free = Vec::new();
    let mut seen = HashSet::new();
    let bound_set: HashSet<_> = bound.iter().cloned().collect();
    collect_free_vars(expr, &bound_set, &mut free, &mut seen);
    free
}

/// Recursive helper for free variable collection.
fn collect_free_vars(
    expr: &Expr,
    bound: &HashSet<Symbol>,
    free: &mut Vec<Symbol>,
    seen: &mut HashSet<Symbol>,
) {
    match expr {
        Expr::Var { name, .. } => {
            if !bound.contains(name) && !seen.contains(name) {
                seen.insert(name.clone());
                free.push(name.clone());
            }
        }
        Expr::Let { bindings, body, .. } => {
            let mut extended = bound.clone();
            for (name, val_expr) in bindings {
                collect_free_vars(val_expr, &extended, free, seen);
                extended.insert(name.clone());
            }
            collect_free_vars(body, &extended, free, seen);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            collect_free_vars(cond, bound, free, seen);
            collect_free_vars(then_branch, bound, free, seen);
            collect_free_vars(else_branch, bound, free, seen);
        }
        Expr::Lambda { params, body, .. } => {
            let mut extended = bound.clone();
            for p in params {
                extended.insert(p.clone());
            }
            collect_free_vars(body, &extended, free, seen);
        }
        Expr::Apply { callee, args, .. } => {
            collect_free_vars(callee, bound, free, seen);
            for arg in args {
                collect_free_vars(arg, bound, free, seen);
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            collect_free_vars(scrutinee, bound, free, seen);
            for arm in arms {
                let mut arm_bound = bound.clone();
                match &arm.pattern {
                    cranelisp_types::Pattern::Var { name, .. } => {
                        arm_bound.insert(name.clone());
                    }
                    cranelisp_types::Pattern::Constructor { bindings, .. } => {
                        for b in bindings {
                            arm_bound.insert(b.clone());
                        }
                    }
                    cranelisp_types::Pattern::Wildcard { .. } => {}
                }
                collect_free_vars(&arm.body, &arm_bound, free, seen);
            }
        }
        Expr::Annotate { expr, .. } => {
            collect_free_vars(expr, bound, free, seen);
        }
        Expr::VecLit { elements, .. } => {
            for e in elements {
                collect_free_vars(e, bound, free, seen);
            }
        }
        Expr::Trace { body, .. } => {
            collect_free_vars(body, bound, free, seen);
        }
        Expr::RunTests { init, pass_fn, fail_fn, .. } => {
            collect_free_vars(init, bound, free, seen);
            collect_free_vars(pass_fn, bound, free, seen);
            collect_free_vars(fail_fn, bound, free, seen);
        }
        Expr::ParBind { bindings, body, .. } => {
            // Same as Let: each binding may reference earlier ones
            let mut extended = bound.clone();
            for (name, val_expr) in bindings {
                collect_free_vars(val_expr, &extended, free, seen);
                extended.insert(name.clone());
            }
            collect_free_vars(body, &extended, free, seen);
        }
        Expr::StringLit { .. }
        | Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. } => {}
    }
}

/// Check if a primitive name is an extern (call-based) primitive,
/// mirroring the `is_extern_primitive` function in apply.rs.
/// Used by the auto-curry wrapper which compiles in a separate context.
fn is_extern_primitive_in_wrapper(name: &str) -> bool {
    matches!(
        name,
        "str-concat"
            | "str-eq"
            | "str-len"
            | "string-identity"
            | "int-to-string"
            | "float-to-string"
            | "bool-to-string"
            | "parse-int"
            | "sconcat"
            | "quote-sexp"
            | "substring"
            | "char-at"
            | "split"
            | "join"
            | "replace"
            | "trim"
            | "starts-with?"
            | "ends-with?"
            | "contains?"
            | "to-upper"
            | "to-lower"
            | "cranelisp_trace_name"
            | "cranelisp_trace_params"
            | "cranelisp_trace_result"
            | "cranelisp_trace_children"
            | "cranelisp_trace_nanos"
            | "cranelisp_trace_first_child_nanos"
    )
}

/// Emit an extern function call inside a wrapper function body.
/// Used by auto-curry wrappers to call extern primitives like `str-eq`.
fn emit_extern_call_in_wrapper(
    builder: &mut FunctionBuilder,
    module: &mut dyn Module,
    name: &str,
    arg_vals: &[Value],
    span: Span,
) -> Result<Value, CranelispError> {
    let mut sig = module.make_signature();
    for _ in arg_vals {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));

    let func_id = module
        .declare_function(name, Linkage::Import, &sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare extern function '{name}' in wrapper: {e}"),
            span,
        })?;

    let local_func = module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(local_func, arg_vals);
    Ok(builder.inst_results(call)[0])
}

// --- Sparkability analysis for lenient evaluation ---
//
// See design/backend/lenient-eval.md §2 for the algorithm.

/// Whether lenient evaluation is disabled via CRANELISP_NO_LENIENT=1.
static LENIENT_DISABLED: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| {
        std::env::var("CRANELISP_NO_LENIENT").is_ok_and(|v| v == "1")
    });

/// Known-cheap builtins that are not worth sparking.
/// Single-instruction or near-single-instruction at the hardware level.
const CHEAP_BUILTINS: &[&str] = &[
    "+", "-", "*", "/", "=", "<", ">", "<=", ">=", "not", "and", "or",
];

/// Find indices of sparkable bindings in a `let` block.
///
/// A binding is sparkable if:
/// 1. Its free variables do not reference any earlier binding in the same block.
/// 2. It is a non-trivial function call (not a cheap builtin, literal,
///    constructor, or var ref).
///
/// `constructors` is the set of known ADT constructor names.
///
/// Returns an empty vec if fewer than 2 sparkable bindings are found.
pub(crate) fn find_sparkable_bindings(
    bindings: &[(Symbol, Expr)],
    constructors: &HashSet<Symbol>,
) -> Vec<usize> {
    let mut bound_names: HashSet<Symbol> = HashSet::new();
    let mut sparkable: Vec<usize> = Vec::new();

    // Use the canonical free_vars_expr from cranelisp-types (I4 review finding:
    // eliminates duplicate free-variable traversal).
    let empty_globals = HashSet::new();
    for (i, (name, val_expr)) in bindings.iter().enumerate() {
        let fv = cranelisp_types::free_vars_expr(val_expr, &empty_globals);
        // Filter to only those free vars that are bound by earlier bindings
        // in this let block (not globals or outer scope).
        let depends_on_earlier = fv.iter().any(|v| bound_names.contains(v));

        if !depends_on_earlier && is_worth_sparking(val_expr, constructors) {
            sparkable.push(i);
        }

        bound_names.insert(name.clone());
    }

    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}

/// Check if an expression is worth sparking (non-trivial function call).
///
/// Excludes: cheap builtins (+, -, etc.), data constructors (Some, Cons),
/// literals, variable references.
fn is_worth_sparking(expr: &Expr, constructors: &HashSet<Symbol>) -> bool {
    match expr {
        Expr::Apply { callee, .. } => {
            if let Expr::Var { name, .. } = callee.as_ref() {
                // Cheap builtins and constructors are not worth sparking.
                !CHEAP_BUILTINS.contains(&name.as_ref())
                    && !constructors.contains(name)
            } else {
                // Non-variable callee (computed function) — conservatively spark.
                true
            }
        }
        // Non-Apply expressions are not worth sparking.
        _ => false,
    }
}
