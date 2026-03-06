// Control flow, binding, and closure codegen.
//
// compile_if, compile_let, compile_lambda

use std::collections::HashSet;

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CompileMode, CranelispError, Expr, Span, Symbol};

use crate::heap::{self, HeapClosure};

use super::FnCompiler;

impl<'a> FnCompiler<'a> {
    // --- Let expression ---

    pub(crate) fn compile_let(
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

        // Store each captured value at HeapClosure::capture_offset(i).
        for (i, cap_name) in captures.iter().enumerate() {
            if let Some(var) = self.variables.get(cap_name) {
                let cap_val = self.builder.use_var(*var);
                heap::heap_store(
                    &mut self.builder,
                    cap_val,
                    base_ptr,
                    HeapClosure::capture_offset(i),
                );
            }
        }

        Ok(base_ptr)
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

        // Bind lambda parameters from function params (after env_ptr).
        for (i, param_name) in params.iter().enumerate() {
            let val = block_params[i + 1]; // skip env_ptr
            let var = inner_compiler.fresh_variable();
            inner_compiler.builder.declare_var(var, types::I64);
            inner_compiler.builder.def_var(var, val);
            inner_compiler.variables.insert(param_name.clone(), var);
        }

        // Compile the body.
        let result = inner_compiler.compile_expr(body)?;
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
                let got_slots = self.ctx.got_slots.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "Interactive mode requires GOT".into(),
                        span,
                    }
                })?;
                let got_base = self.ctx.got_base_ptr.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "Interactive mode requires GOT base".into(),
                        span,
                    }
                })?;
                let slot = got_slots.get(target_name).ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: format!("no GOT slot for: {target_name}"),
                        span,
                    }
                })?;

                let slot_offset = (*slot * 8) as i64;
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
        Expr::StringLit { .. }
        | Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. } => {}
    }
}
