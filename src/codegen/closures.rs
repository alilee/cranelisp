use std::collections::HashMap;

use cranelift::codegen::ir::Function;
use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use crate::ast::Expr;
use crate::captures;
use crate::error::CranelispError;

use super::{AccessorInfoCg, CallMode, FnCompiler};

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Compile a lambda expression: free-var analysis, anonymous fn, closure allocation.
    pub(crate) fn compile_lambda(
        &mut self,
        params: &[String],
        body: &Expr,
        expr: &Expr,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        // Compute captures for this lambda
        let free = captures::free_vars(expr, &self.globals);
        let capture_names: Vec<String> = free.into_iter().collect();

        // Build signature: (env_ptr: i64, params...) -> i64
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr
        for _ in params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        // Declare anonymous function
        let func_id = self.module.declare_anonymous_function(&sig).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to declare lambda: {}", e),
                span,
            }
        })?;

        // Compile lambda body in a fresh Function
        {
            let mut lambda_func = Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
                sig.clone(),
            );
            let mut lambda_func_ctx = FunctionBuilderContext::new();
            let mut lambda_builder = FunctionBuilder::new(&mut lambda_func, &mut lambda_func_ctx);

            let entry_block = lambda_builder.create_block();
            lambda_builder.append_block_params_for_function_params(entry_block);
            lambda_builder.switch_to_block(entry_block);
            lambda_builder.seal_block(entry_block);

            let inner_call_mode = match &self.call_mode {
                CallMode::Direct { func_ids } => CallMode::Direct {
                    func_ids: func_ids.clone(),
                },
                CallMode::Indirect { fn_slots } => CallMode::Indirect { fn_slots },
            };

            let mut inner = FnCompiler {
                builder: lambda_builder,
                module: self.module,
                variables: HashMap::new(),
                call_mode: inner_call_mode,
                alloc_func_id: self.alloc_func_id,
                globals: self.globals.clone(),
                method_resolutions: self.method_resolutions,
                fn_specific_resolutions: self.fn_specific_resolutions,
                builtin_methods: self.builtin_methods,
                modules: self.modules,
                type_defs: self.type_defs,
                constructor_to_type: self.constructor_to_type,
                panic_func_id: self.panic_func_id,
                expr_types: self.expr_types,
                free_func_id: self.free_func_id,
                variable_types: HashMap::new(),
                scope_stack: vec![vec![]],
                drop_fn_cache: HashMap::new(),
                current_fn_name: None,
                tail_loop_block: None,
                in_tail_position: false,
                fn_param_count: 0,
            };

            // Block params: [env_ptr, p0, p1, ...]
            let block_params: Vec<Value> = inner.builder.block_params(entry_block).to_vec();
            let env_ptr_val = block_params[0];

            // Bind lambda parameters (after env_ptr)
            for (i, param_name) in params.iter().enumerate() {
                let val = block_params[i + 1]; // +1 to skip env_ptr
                let var = inner.fresh_var(types::I64);
                inner.builder.def_var(var, val);
                inner.variables.insert(param_name.clone(), var);
            }

            // Load captures from env_ptr
            // Layout: [code_ptr, cap0, cap1, ...]
            // cap_i is at offset (i + 1) * 8
            for (i, cap_name) in capture_names.iter().enumerate() {
                let offset = ((i + 1) * 8) as i32;
                let cap_val =
                    inner
                        .builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), env_ptr_val, offset);
                let var = inner.fresh_var(types::I64);
                inner.builder.def_var(var, cap_val);
                inner.variables.insert(cap_name.clone(), var);
            }

            let result = inner.compile_expr(body)?;
            inner.pop_scope_for_value(result);
            inner.builder.ins().return_(&[result]);
            inner.builder.seal_all_blocks();
            inner.builder.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(lambda_func);
            self.module
                .define_function(func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define lambda: {}", e),
                    span,
                })?;
        }

        // Allocate closure: [code_ptr, cap0, cap1, ...]
        let closure_size = ((1 + capture_names.len()) * 8) as i64;
        let closure_ptr = self.compile_alloc(closure_size, span)?;

        // Store code_ptr at offset 0
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, func_ref);
        self.builder
            .ins()
            .store(MemFlags::trusted(), code_ptr, closure_ptr, 0);

        // Store captures at offsets 8, 16, ...
        for (i, cap_name) in capture_names.iter().enumerate() {
            let cap_val = if let Some(var) = self.variables.get(cap_name) {
                self.builder.use_var(*var)
            } else if self.is_known_function(cap_name) {
                // A captured name that's a top-level function —
                // this shouldn't happen since globals are excluded from captures.
                return Err(CranelispError::CodegenError {
                    message: format!("unexpected capture of global function: {}", cap_name),
                    span,
                });
            } else {
                return Err(CranelispError::CodegenError {
                    message: format!("undefined capture: {}", cap_name),
                    span,
                });
            };
            let offset = ((i + 1) * 8) as i32;
            self.builder
                .ins()
                .store(MemFlags::trusted(), cap_val, closure_ptr, offset);

            // RC inc: capturing creates an additional reference to this value
            if let Some(ty) = self.variable_types.get(cap_name).cloned() {
                self.emit_inc(cap_val, &ty);
            }
        }

        Ok(closure_ptr)
    }

    /// Wrap a data constructor as a first-class closure value.
    /// Generates an anonymous function that allocates the ADT and stores tag + fields.
    pub(crate) fn compile_constructor_as_closure(
        &mut self,
        _name: &str,
        tag: usize,
        field_count: usize,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        // Build signature: (env_ptr: i64, field0: i64, ...) -> i64
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr (ignored)
        for _ in 0..field_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self.module.declare_anonymous_function(&sig).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to declare constructor wrapper: {}", e),
                span,
            }
        })?;

        // Compile wrapper body
        {
            let mut wrapper_func = Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
                sig.clone(),
            );
            let mut wrapper_ctx = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut wrapper_func, &mut wrapper_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            let block_params: Vec<Value> = builder.block_params(entry_block).to_vec();
            // block_params[0] = env_ptr (ignored), block_params[1..] = fields

            // Allocate heap: [tag, field0, field1, ...]
            let size = ((1 + field_count) * 8) as i64;
            let alloc_ref = self
                .module
                .declare_func_in_func(self.alloc_func_id, builder.func);
            let size_val = builder.ins().iconst(types::I64, size);
            let call = builder.ins().call(alloc_ref, &[size_val]);
            let ptr = builder.inst_results(call)[0];

            // Store tag
            let tag_val = builder.ins().iconst(types::I64, tag as i64);
            builder.ins().store(MemFlags::trusted(), tag_val, ptr, 0);

            // Store fields
            for i in 0..field_count {
                let field_val = block_params[i + 1]; // skip env_ptr
                let offset = ((i + 1) * 8) as i32;
                builder
                    .ins()
                    .store(MemFlags::trusted(), field_val, ptr, offset);
            }

            builder.ins().return_(&[ptr]);
            builder.seal_all_blocks();
            builder.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define constructor wrapper: {}", e),
                    span,
                })?;
        }

        // Wrap as closure: [code_ptr] (no captures)
        let closure_ptr = self.compile_alloc(8, span)?;
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, func_ref);
        self.builder
            .ins()
            .store(MemFlags::trusted(), code_ptr, closure_ptr, 0);

        Ok(closure_ptr)
    }

    /// Wrap a field accessor as a first-class closure value.
    /// Generates an anonymous function with sig `(env_ptr: i64, adt: i64) -> i64`
    /// that loads the field at the correct offset.
    pub(crate) fn compile_accessor_as_closure(
        &mut self,
        name: &str,
        acc: &AccessorInfoCg,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        // Build signature: (env_ptr: i64, adt: i64) -> i64
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr (ignored)
        sig.params.push(AbiParam::new(types::I64)); // adt value
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self.module.declare_anonymous_function(&sig).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to declare accessor wrapper for '{}': {}", name, e),
                span,
            }
        })?;

        // Compile wrapper body
        {
            let mut wrapper_func = Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
                sig.clone(),
            );
            let mut wrapper_ctx = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut wrapper_func, &mut wrapper_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            let block_params: Vec<Value> = builder.block_params(entry_block).to_vec();
            // block_params[0] = env_ptr (ignored), block_params[1] = adt value
            let adt_val = block_params[1];

            if acc.is_product {
                // Total accessor: just load field
                let offset = ((acc.field_index + 1) * 8) as i32;
                let result = builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), adt_val, offset);
                builder.ins().return_(&[result]);
            } else {
                // Partial accessor: check tag, panic on mismatch
                let tag_val = builder.ins().iconst(types::I64, acc.tag as i64);
                let loaded_tag = builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), adt_val, 0);
                let cmp = builder.ins().icmp(IntCC::Equal, loaded_tag, tag_val);

                let ok_block = builder.create_block();
                let panic_block = builder.create_block();

                builder.ins().brif(cmp, ok_block, &[], panic_block, &[]);

                // OK block: load field
                builder.switch_to_block(ok_block);
                builder.seal_block(ok_block);
                let offset = ((acc.field_index + 1) * 8) as i32;
                let field_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), adt_val, offset);
                builder.ins().return_(&[field_val]);

                // Panic block
                builder.switch_to_block(panic_block);
                builder.seal_block(panic_block);
                if let Some(panic_func_id) = self.panic_func_id {
                    let msg = format!("accessor '{}' called on wrong constructor", name);
                    let msg_bytes = msg.as_bytes();
                    let size = (8 + msg_bytes.len()) as i64;
                    let alloc_ref = self
                        .module
                        .declare_func_in_func(self.alloc_func_id, builder.func);
                    let size_val = builder.ins().iconst(types::I64, size);
                    let call = builder.ins().call(alloc_ref, &[size_val]);
                    let ptr = builder.inst_results(call)[0];
                    let len_val = builder.ins().iconst(types::I64, msg_bytes.len() as i64);
                    builder.ins().store(MemFlags::trusted(), len_val, ptr, 0);
                    for (bi, &byte) in msg_bytes.iter().enumerate() {
                        let byte_val = builder.ins().iconst(types::I64, byte as i64);
                        builder
                            .ins()
                            .istore8(MemFlags::trusted(), byte_val, ptr, (8 + bi) as i32);
                    }
                    let panic_ref = self
                        .module
                        .declare_func_in_func(panic_func_id, builder.func);
                    builder.ins().call(panic_ref, &[ptr]);
                }
                // Unreachable after panic, but cranelift needs a terminator
                let zero = builder.ins().iconst(types::I64, 0);
                builder.ins().return_(&[zero]);
            }

            builder.seal_all_blocks();
            builder.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define accessor wrapper for '{}': {}", name, e),
                    span,
                })?;
        }

        // Wrap as closure: [code_ptr] (no captures)
        let closure_ptr = self.compile_alloc(8, span)?;
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, func_ref);
        self.builder
            .ins()
            .store(MemFlags::trusted(), code_ptr, closure_ptr, 0);

        Ok(closure_ptr)
    }

    /// Compile auto-curry: generates a closure that captures applied args
    /// and forwards remaining args to the target function.
    pub(crate) fn compile_auto_curry(
        &mut self,
        target_name: &str,
        applied_vals: &[Value],
        applied_count: usize,
        total_count: usize,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        let remaining_count = total_count - applied_count;

        // Build wrapper signature: (env_ptr: i64, remaining_params...) -> i64
        let mut wrapper_sig = self.module.make_signature();
        wrapper_sig.params.push(AbiParam::new(types::I64)); // env_ptr
        for _ in 0..remaining_count {
            wrapper_sig.params.push(AbiParam::new(types::I64));
        }
        wrapper_sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_anonymous_function(&wrapper_sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare auto-curry wrapper: {}", e),
                span,
            })?;

        // Compile the wrapper body
        {
            let mut wrapper_func = Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, wrapper_func_id.as_u32()),
                wrapper_sig.clone(),
            );
            let mut wrapper_func_ctx = FunctionBuilderContext::new();
            let mut wrapper_builder =
                FunctionBuilder::new(&mut wrapper_func, &mut wrapper_func_ctx);

            let entry_block = wrapper_builder.create_block();
            wrapper_builder.append_block_params_for_function_params(entry_block);
            wrapper_builder.switch_to_block(entry_block);
            wrapper_builder.seal_block(entry_block);

            let block_params: Vec<Value> = wrapper_builder.block_params(entry_block).to_vec();
            let env_ptr = block_params[0];
            let remaining_args = &block_params[1..];

            // Load captured args from env_ptr
            // Layout: [code_ptr, cap0, cap1, ...]
            let mut all_args = Vec::new();
            for i in 0..applied_count {
                let offset = ((i + 1) * 8) as i32;
                let val =
                    wrapper_builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), env_ptr, offset);
                all_args.push(val);
            }
            all_args.extend_from_slice(remaining_args);

            // Call the target function
            let result = if let Some(&builtin_fid) = self.builtin_methods.get(target_name) {
                // Builtin operator (e.g., "+") — call via registered FuncId
                let local_func = self
                    .module
                    .declare_func_in_func(builtin_fid, wrapper_builder.func);
                let call = wrapper_builder.ins().call(local_func, &all_args);
                wrapper_builder.inst_results(call)[0]
            } else {
                match &self.call_mode {
                    CallMode::Direct { func_ids } => {
                        let func_id = func_ids[target_name];
                        let local_func = self
                            .module
                            .declare_func_in_func(func_id, wrapper_builder.func);
                        let call = wrapper_builder.ins().call(local_func, &all_args);
                        wrapper_builder.inst_results(call)[0]
                    }
                    CallMode::Indirect { fn_slots } => {
                        let fn_slot = &fn_slots[target_name];
                        let mut sig = self.module.make_signature();
                        for _ in 0..fn_slot.param_count {
                            sig.params.push(AbiParam::new(types::I64));
                        }
                        sig.returns.push(AbiParam::new(types::I64));
                        let sig_ref = wrapper_builder.import_signature(sig);

                        let base = fn_slot.emit_got_base(&mut wrapper_builder, self.module);
                        let offset = wrapper_builder
                            .ins()
                            .iconst(types::I64, (fn_slot.slot * 8) as i64);
                        let ptr_addr = wrapper_builder.ins().iadd(base, offset);
                        let fn_ptr = wrapper_builder.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            ptr_addr,
                            0,
                        );
                        let call = wrapper_builder
                            .ins()
                            .call_indirect(sig_ref, fn_ptr, &all_args);
                        wrapper_builder.inst_results(call)[0]
                    }
                }
            };

            wrapper_builder.ins().return_(&[result]);
            wrapper_builder.seal_all_blocks();
            wrapper_builder.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(wrapper_func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define auto-curry wrapper: {}", e),
                    span,
                })?;
        }

        // Allocate closure: [code_ptr, applied_arg0, applied_arg1, ...]
        let closure_size = ((1 + applied_count) * 8) as i64;
        let closure_ptr = self.compile_alloc(closure_size, span)?;

        // Store wrapper code ptr at offset 0
        let wrapper_ref = self
            .module
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let wrapper_addr = self.builder.ins().func_addr(types::I64, wrapper_ref);
        self.builder
            .ins()
            .store(MemFlags::trusted(), wrapper_addr, closure_ptr, 0);

        // Store captured applied args
        for (i, val) in applied_vals.iter().enumerate() {
            let offset = ((i + 1) * 8) as i32;
            self.builder
                .ins()
                .store(MemFlags::trusted(), *val, closure_ptr, offset);
        }

        Ok(closure_ptr)
    }

    /// Create a closure for a named top-level function used as a value.
    /// Generates a wrapper function with (env_ptr, params...) signature,
    /// then allocates [wrapper_code_ptr].
    pub(crate) fn compile_func_as_closure(
        &mut self,
        name: &str,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        // We need to know param_count. In Direct mode, we look it up from the program.
        // In Indirect mode, from fn_slots.
        let param_count = match &self.call_mode {
            CallMode::Direct { func_ids } => {
                let orig_func_id =
                    *func_ids
                        .get(name)
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: format!("undefined function: {}", name),
                            span,
                        })?;

                let orig_sig = self.module.declarations().get_function_decl(orig_func_id);
                orig_sig.signature.params.len()
            }
            CallMode::Indirect { fn_slots, .. } => {
                let fn_slot = fn_slots
                    .get(name)
                    .ok_or_else(|| CranelispError::CodegenError {
                        message: format!("undefined function: {}", name),
                        span,
                    })?;
                fn_slot.param_count
            }
        };

        // Declare a wrapper function: (env_ptr: i64, params...) -> i64
        let mut wrapper_sig = self.module.make_signature();
        wrapper_sig.params.push(AbiParam::new(types::I64)); // env_ptr (ignored)
        for _ in 0..param_count {
            wrapper_sig.params.push(AbiParam::new(types::I64));
        }
        wrapper_sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_anonymous_function(&wrapper_sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare wrapper for '{}': {}", name, e),
                span,
            })?;

        // Compile the wrapper body
        {
            let mut wrapper_func = Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, wrapper_func_id.as_u32()),
                wrapper_sig.clone(),
            );
            let mut wrapper_func_ctx = FunctionBuilderContext::new();
            let mut wrapper_builder =
                FunctionBuilder::new(&mut wrapper_func, &mut wrapper_func_ctx);

            let entry_block = wrapper_builder.create_block();
            wrapper_builder.append_block_params_for_function_params(entry_block);
            wrapper_builder.switch_to_block(entry_block);
            wrapper_builder.seal_block(entry_block);

            // Get block params: [env_ptr, p0, p1, ...]
            // Skip env_ptr (index 0), pass p0..pN to the real function
            let block_params: Vec<Value> = wrapper_builder.block_params(entry_block).to_vec();
            let real_args = &block_params[1..]; // skip env_ptr

            // Call the real function
            let result = match &self.call_mode {
                CallMode::Direct { func_ids } => {
                    let orig_func_id = func_ids[name];
                    let local_func = self
                        .module
                        .declare_func_in_func(orig_func_id, wrapper_builder.func);
                    let call = wrapper_builder.ins().call(local_func, real_args);
                    wrapper_builder.inst_results(call)[0]
                }
                CallMode::Indirect { fn_slots } => {
                    let fn_slot = &fn_slots[name];
                    let mut sig = self.module.make_signature();
                    for _ in 0..fn_slot.param_count {
                        sig.params.push(AbiParam::new(types::I64));
                    }
                    sig.returns.push(AbiParam::new(types::I64));
                    let sig_ref = wrapper_builder.import_signature(sig);

                    let base = fn_slot.emit_got_base(&mut wrapper_builder, self.module);
                    let offset = wrapper_builder
                        .ins()
                        .iconst(types::I64, (fn_slot.slot * 8) as i64);
                    let ptr_addr = wrapper_builder.ins().iadd(base, offset);
                    let fn_ptr =
                        wrapper_builder
                            .ins()
                            .load(types::I64, MemFlags::trusted(), ptr_addr, 0);
                    let call = wrapper_builder
                        .ins()
                        .call_indirect(sig_ref, fn_ptr, real_args);
                    wrapper_builder.inst_results(call)[0]
                }
            };

            wrapper_builder.ins().return_(&[result]);
            wrapper_builder.seal_all_blocks();
            wrapper_builder.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(wrapper_func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define wrapper for '{}': {}", name, e),
                    span,
                })?;
        }

        // Allocate closure [wrapper_code_ptr]
        let closure_ptr = self.compile_alloc(8, span)?;
        let wrapper_ref = self
            .module
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let wrapper_addr = self.builder.ins().func_addr(types::I64, wrapper_ref);
        self.builder
            .ins()
            .store(MemFlags::trusted(), wrapper_addr, closure_ptr, 0);
        Ok(closure_ptr)
    }

    /// Create a closure for a builtin function used as a value.
    /// Generates a wrapper with (env_ptr, params...) -> i64 that calls the builtin directly.
    pub(crate) fn compile_builtin_as_closure(
        &mut self,
        builtin_func_id: FuncId,
        param_count: usize,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        // Wrapper signature: (env_ptr: i64, params...) -> i64
        let mut wrapper_sig = self.module.make_signature();
        wrapper_sig.params.push(AbiParam::new(types::I64)); // env_ptr (ignored)
        for _ in 0..param_count {
            wrapper_sig.params.push(AbiParam::new(types::I64));
        }
        wrapper_sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_anonymous_function(&wrapper_sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare builtin wrapper: {}", e),
                span,
            })?;

        // Compile wrapper body: ignore env_ptr, forward args to builtin
        {
            let mut wrapper_func = Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, wrapper_func_id.as_u32()),
                wrapper_sig.clone(),
            );
            let mut wrapper_func_ctx = FunctionBuilderContext::new();
            let mut wrapper_builder =
                FunctionBuilder::new(&mut wrapper_func, &mut wrapper_func_ctx);

            let entry_block = wrapper_builder.create_block();
            wrapper_builder.append_block_params_for_function_params(entry_block);
            wrapper_builder.switch_to_block(entry_block);
            wrapper_builder.seal_block(entry_block);

            let block_params: Vec<Value> = wrapper_builder.block_params(entry_block).to_vec();
            let real_args = &block_params[1..]; // skip env_ptr

            let local_func = self
                .module
                .declare_func_in_func(builtin_func_id, wrapper_builder.func);
            let call = wrapper_builder.ins().call(local_func, real_args);
            let result = wrapper_builder.inst_results(call)[0];

            wrapper_builder.ins().return_(&[result]);
            wrapper_builder.seal_all_blocks();
            wrapper_builder.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(wrapper_func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define builtin wrapper: {}", e),
                    span,
                })?;
        }

        // Allocate closure [wrapper_code_ptr]
        let closure_ptr = self.compile_alloc(8, span)?;
        let wrapper_ref = self
            .module
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let wrapper_addr = self.builder.ins().func_addr(types::I64, wrapper_ref);
        self.builder
            .ins()
            .store(MemFlags::trusted(), wrapper_addr, closure_ptr, 0);
        Ok(closure_ptr)
    }
}
