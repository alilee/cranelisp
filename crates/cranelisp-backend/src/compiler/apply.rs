// Function application codegen.
//
// compile_apply, compile_direct_call, compile_tail_self_call,
// compile_data_constructor_call, compile_extern_call,
// compile_closure_call

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{CompileMode, CranelispError, Expr, ResolvedCall, Span, Symbol};

use crate::heap::{self, HeapAdt, HeapClosure};
use crate::operators;

use super::FnCompiler;

impl<'a> FnCompiler<'a> {
    // --- Function application ---

    pub(crate) fn compile_apply(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // TCO check: self-recursive call in tail position -> jump to loop header.
        if self.in_tail_position
            && let Expr::Var { name, .. } = callee
            && let Some(ref fn_name) = self.current_fn_name
            && *name == *fn_name
            && self.tail_loop_block.is_some()
            && args.len() == self.fn_param_count
        {
            return self.compile_tail_self_call(args);
        }

        // CRITICAL: Args are never in tail position.
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Check for resolved call (builtin, trait method, sig-dispatch, auto-curry).
        if let Some(resolved) = self.ctx.method_resolutions.get(&span) {
            return self.compile_resolved_call(resolved.clone(), args, span, saved_tail);
        }

        // Regular function call: callee must be a Var referring to a known function,
        // a data constructor, or a local variable holding a closure.
        if let Expr::Var {
            name,
            span: var_span,
        } = callee
        {
            return self.compile_var_apply(name, *var_span, callee, args, span, saved_tail);
        }

        // Callee is not a variable -- could be a closure call (Ring 1).
        // Compile as closure call: load code_ptr from the closure, call_indirect.
        let callee_val = self.compile_expr(callee)?;
        let arg_vals = self.compile_arg_list(args)?;
        self.in_tail_position = saved_tail;

        self.compile_closure_call(callee_val, &arg_vals, span)
    }

    /// Compile a call to a resolved callee (builtin, trait method, sig-dispatch,
    /// or auto-curry). Handles the four `ResolvedCall` variants.
    fn compile_resolved_call(
        &mut self,
        resolved: ResolvedCall,
        args: &[Expr],
        span: Span,
        saved_tail: bool,
    ) -> Result<Value, CranelispError> {
        match resolved {
            ResolvedCall::BuiltinFn { name: ref op_name } => {
                // Vec operations: intercept and compile inline.
                if is_vec_primitive(op_name) {
                    let arg_vals = self.compile_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    if let Some(val) = self.compile_vec_op(op_name, args, &arg_vals, span)? {
                        return Ok(val);
                    }
                    // Fall through to extern if compile_vec_op returned None.
                    return self.compile_extern_call(op_name, &arg_vals, span);
                }

                if is_extern_primitive(op_name) {
                    let arg_vals = self.compile_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    return self.compile_extern_call(op_name, &arg_vals, span);
                }

                let arg_vals = self.compile_arg_list(args)?;
                self.in_tail_position = saved_tail;

                operators::emit_builtin_op(&mut self.builder, op_name, &arg_vals, span)
            }
            ResolvedCall::TraitMethod {
                ref trait_name,
                ref method_name,
                ref impl_type,
                ref mangled_name,
            } => {
                // Check if this is a known primitive trait method (inline IR).
                if let Some(prim_name) =
                    operators::primitive_for_trait_method(trait_name, method_name, impl_type)
                {
                    // Extern primitives (e.g. str-eq for Eq.=.String).
                    if is_extern_primitive(prim_name) {
                        let arg_vals = self.compile_arg_list(args)?;
                        self.in_tail_position = saved_tail;
                        return self.compile_extern_call(prim_name, &arg_vals, span);
                    }

                    let arg_vals = self.compile_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    return operators::emit_builtin_op(
                        &mut self.builder, prim_name, &arg_vals, span,
                    );
                }

                // Not a primitive: compile as a normal function call to mangled name.
                let sym = Symbol::from(mangled_name.as_ref());
                let arg_vals = self.compile_arg_list(args)?;
                self.in_tail_position = saved_tail;
                self.compile_direct_call(&sym, &arg_vals, span)
            }
            ResolvedCall::SigDispatch { mangled_name } => {
                Err(CranelispError::CodegenError {
                    message: format!(
                        "multi-sig dispatch not supported in Ring 1: {mangled_name}"
                    ),
                    span,
                })
            }
            ResolvedCall::AutoCurry { target_name, .. } => {
                Err(CranelispError::CodegenError {
                    message: format!("auto-curry not supported in Ring 1: {target_name}"),
                    span,
                })
            }
        }
    }

    /// Compile a function application where the callee is a Var.
    /// Dispatches between data constructor, local closure, and direct call.
    fn compile_var_apply(
        &mut self,
        name: &Symbol,
        var_span: Span,
        callee: &Expr,
        args: &[Expr],
        span: Span,
        saved_tail: bool,
    ) -> Result<Value, CranelispError> {
        // Check if this is a data constructor call.
        if let Some((tag, field_count)) = self.data_constructor_info(name) {
            if args.len() != field_count {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "constructor '{name}' expects {field_count} args, got {}",
                        args.len()
                    ),
                    span,
                });
            }

            let arg_vals = self.compile_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_data_constructor_call(tag, &arg_vals, span);
        }

        // Check if the callee is a local variable (holding a closure value).
        if self.variables.contains_key(name) {
            let callee_val = self.compile_expr(callee)?;
            let arg_vals = self.compile_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_closure_call(callee_val, &arg_vals, span);
        }

        // Not a local variable: try direct function call.
        let arg_vals = self.compile_arg_list(args)?;
        self.in_tail_position = saved_tail;
        self.compile_direct_call(name, &arg_vals, var_span)
    }

    /// Compile a list of argument expressions into Cranelift values.
    fn compile_arg_list(&mut self, args: &[Expr]) -> Result<Vec<Value>, CranelispError> {
        args.iter()
            .map(|a| self.compile_expr(a))
            .collect::<Result<_, _>>()
    }

    /// Compile a call to a named function.
    ///
    /// In Batch/Release mode: emits a direct `call` instruction.
    /// In Interactive mode: loads the function pointer from the GOT slot
    /// and emits a `call_indirect` instruction.
    pub(crate) fn compile_direct_call(
        &mut self,
        name: &Symbol,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        match self.ctx.mode {
            CompileMode::Batch | CompileMode::Release => {
                // Direct call: look up FuncId and emit `call`.
                let func_id = self.ctx.func_ids.get(name).ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: format!("undefined function: {name}"),
                        span,
                    }
                })?;

                let local_func = self
                    .module
                    .declare_func_in_func(*func_id, self.builder.func);
                let call = self.builder.ins().call(local_func, arg_vals);
                Ok(self.builder.inst_results(call)[0])
            }
            CompileMode::Interactive => {
                // GOT-indirect call: load function pointer from GOT slot.
                let got_slots = self.ctx.got_slots.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "Interactive mode requires GOT slot assignments".into(),
                        span,
                    }
                })?;
                let got_base = self.ctx.got_base_ptr.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "Interactive mode requires GOT base pointer".into(),
                        span,
                    }
                })?;
                let slot = got_slots.get(name).ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: format!("no GOT slot for function: {name}"),
                        span,
                    }
                })?;

                // Compute the address of the GOT slot: got_base + slot * 8
                let slot_offset = (*slot * 8) as i64;
                let base_val = self.builder.ins().iconst(types::I64, got_base);
                let slot_addr = self.builder.ins().iadd_imm(base_val, slot_offset);

                // Load the function pointer from the GOT slot.
                let func_ptr = self.builder.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    slot_addr,
                    0,
                );

                // Build the signature for call_indirect: all params and return are i64.
                let mut sig = self.module.make_signature();
                for _ in arg_vals {
                    sig.params.push(AbiParam::new(types::I64));
                }
                sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = self.builder.import_signature(sig);

                // Emit call_indirect.
                let call = self.builder.ins().call_indirect(sig_ref, func_ptr, arg_vals);
                Ok(self.builder.inst_results(call)[0])
            }
        }
    }

    /// Compile a tail self-recursive call as a jump to the loop header.
    fn compile_tail_self_call(&mut self, args: &[Expr]) -> Result<Value, CranelispError> {
        // CRITICAL: Args are not in tail position.
        self.in_tail_position = false;

        // Compile all arguments.
        let arg_vals: Vec<Value> = args
            .iter()
            .map(|a| self.compile_expr(a))
            .collect::<Result<_, _>>()?;

        // Jump to loop header with new argument values.
        let loop_block = self.tail_loop_block.unwrap_or_else(|| {
            unreachable!("invariant: tail_loop_block is Some when compile_tail_self_call is called")
        });
        self.builder.ins().jump(loop_block, &arg_vals);

        // Create a dead block for subsequent code (unreachable, Cranelift eliminates it).
        let dead_block = self.builder.create_block();
        self.builder.switch_to_block(dead_block);
        self.builder.seal_block(dead_block);

        // Return dummy value -- this code is unreachable.
        Ok(self.builder.ins().iconst(types::I64, 0))
    }

    /// Compile a data constructor call: allocate heap, store tag + fields.
    fn compile_data_constructor_call(
        &mut self,
        tag: usize,
        field_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    span,
                })?;

        let payload_size = HeapAdt::payload_size(field_vals.len()) as i64;
        let base_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            payload_size,
        );

        // Store tag at HeapAdt::TAG_OFFSET (16).
        let tag_val = self.builder.ins().iconst(types::I64, tag as i64);
        heap::heap_store(&mut self.builder, tag_val, base_ptr, HeapAdt::TAG_OFFSET);

        // Store each field at HeapAdt::field_offset(i).
        for (i, &field_val) in field_vals.iter().enumerate() {
            heap::heap_store(
                &mut self.builder,
                field_val,
                base_ptr,
                HeapAdt::field_offset(i),
            );
        }

        Ok(base_ptr)
    }

    /// Compile a call to an extern primitive (declared as an imported JIT function).
    fn compile_extern_call(
        &mut self,
        name: &str,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Declare the extern function as an import in the JIT module.
        let mut sig = self.module.make_signature();
        for _ in arg_vals {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, cranelift_module::Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern function '{name}': {e}"),
                span,
            })?;

        let local_func = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(local_func, arg_vals);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Compile a closure call: load code_ptr from the closure, then call_indirect
    /// with the closure pointer as the first argument (env_ptr).
    fn compile_closure_call(
        &mut self,
        closure_val: Value,
        arg_vals: &[Value],
        _span: Span,
    ) -> Result<Value, CranelispError> {
        // Load code_ptr from offset HeapClosure::CODE_PTR_OFFSET (16).
        let code_ptr = heap::heap_load(
            &mut self.builder,
            closure_val,
            HeapClosure::CODE_PTR_OFFSET,
        ); // code_ptr: i64

        // Build signature: (env_ptr, params...) -> i64
        let mut sig = self.module.make_signature();
        // env_ptr (the closure base pointer itself)
        sig.params.push(AbiParam::new(types::I64));
        for _ in arg_vals {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = self.builder.import_signature(sig);

        // Build call args: [closure_ptr, arg_0, ..., arg_n]
        let mut call_args = vec![closure_val];
        call_args.extend_from_slice(arg_vals);

        let call = self
            .builder
            .ins()
            .call_indirect(sig_ref, code_ptr, &call_args);
        Ok(self.builder.inst_results(call)[0])
    }
}

/// Check if a builtin name is an extern primitive (requires a call, not inline IR).
fn is_extern_primitive(name: &str) -> bool {
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
    )
}

/// Check if a builtin name is a Vec primitive (compiled inline by vec_codegen).
fn is_vec_primitive(name: &str) -> bool {
    matches!(name, "vec-get" | "vec-set" | "vec-push" | "vec-len")
}
