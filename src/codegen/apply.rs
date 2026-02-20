use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::Module;

use crate::ast::Expr;
use crate::error::CranelispError;
use crate::names::resolve_bare_name;

use super::{CallMode, FnCompiler};

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Compile a function application expression.
    pub(crate) fn compile_apply(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        span: &crate::error::Span,
    ) -> Result<Value, CranelispError> {
        // TCO check: self-recursive call in tail position → jump to loop header
        if self.in_tail_position {
            if let Expr::Var { name, .. } = callee {
                if let Some(ref fn_name) = self.current_fn_name {
                    if name == fn_name
                        && self.tail_loop_block.is_some()
                        && args.len() == self.fn_param_count
                    {
                        return self.compile_tail_self_call(args);
                    }
                }
            }
        }

        // Args are never in tail position
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Compile arguments first
        let arg_vals: Vec<Value> = args
            .iter()
            .map(|a| self.compile_expr(a))
            .collect::<Result<_, _>>()?;

        self.in_tail_position = saved_tail;

        // Data constructor call: allocate heap, store tag + fields
        if let Expr::Var { name, .. } = callee {
            if let Some(ctor_info) = self.data_constructor_info(name) {
                let tag = ctor_info.tag;
                let field_count = ctor_info.fields.len();
                let size = ((1 + field_count) * 8) as i64;
                let ptr = self.compile_alloc(size, *span)?;
                let tag_val = self.builder.ins().iconst(types::I64, tag as i64);
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), tag_val, ptr, 0);
                for (i, arg_val) in arg_vals.iter().enumerate() {
                    let offset = ((i + 1) * 8) as i32;
                    self.builder
                        .ins()
                        .store(MemFlags::trusted(), *arg_val, ptr, offset);
                }
                return Ok(ptr);
            }
        }

        // Accessor call: (field_name adt_value) → load field from heap
        if let Expr::Var { name, .. } = callee {
            if !self.variables.contains_key(name) {
                if let Some(acc) = self.accessor_info(name) {
                    let adt_val = arg_vals[0];
                    if acc.is_product {
                        // Total accessor: just load field
                        let offset = ((acc.field_index + 1) * 8) as i32;
                        return Ok(self.builder.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            adt_val,
                            offset,
                        ));
                    } else {
                        // Partial accessor: check tag, panic on mismatch
                        let tag_val = self.builder.ins().iconst(types::I64, acc.tag as i64);
                        let loaded_tag =
                            self.builder
                                .ins()
                                .load(types::I64, MemFlags::trusted(), adt_val, 0);
                        let cmp = self.builder.ins().icmp(IntCC::Equal, loaded_tag, tag_val);

                        let ok_block = self.builder.create_block();
                        let panic_block = self.builder.create_block();
                        let merge_block = self.builder.create_block();
                        self.builder.append_block_param(merge_block, types::I64);

                        self.builder
                            .ins()
                            .brif(cmp, ok_block, &[], panic_block, &[]);

                        // OK block: load field
                        self.builder.switch_to_block(ok_block);
                        self.builder.seal_block(ok_block);
                        let offset = ((acc.field_index + 1) * 8) as i32;
                        let field_val = self.builder.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            adt_val,
                            offset,
                        );
                        self.builder
                            .ins()
                            .jump(merge_block, &[BlockArg::Value(field_val)]);

                        // Panic block
                        self.builder.switch_to_block(panic_block);
                        self.builder.seal_block(panic_block);
                        if let Some(panic_func_id) = self.panic_func_id {
                            let msg = format!("accessor '{}' called on wrong constructor", name);
                            let msg_bytes = msg.as_bytes();
                            let size = (8 + msg_bytes.len()) as i64;
                            let ptr = self.compile_alloc(size, *span)?;
                            let len_val = self
                                .builder
                                .ins()
                                .iconst(types::I64, msg_bytes.len() as i64);
                            self.builder
                                .ins()
                                .store(MemFlags::trusted(), len_val, ptr, 0);
                            for (bi, &byte) in msg_bytes.iter().enumerate() {
                                let byte_val = self.builder.ins().iconst(types::I64, byte as i64);
                                self.builder.ins().istore8(
                                    MemFlags::trusted(),
                                    byte_val,
                                    ptr,
                                    (8 + bi) as i32,
                                );
                            }
                            let panic_ref = self
                                .module
                                .declare_func_in_func(panic_func_id, self.builder.func);
                            self.builder.ins().call(panic_ref, &[ptr]);
                        }
                        let zero = self.builder.ins().iconst(types::I64, 0);
                        self.builder
                            .ins()
                            .jump(merge_block, &[BlockArg::Value(zero)]);

                        self.builder.switch_to_block(merge_block);
                        self.builder.seal_block(merge_block);
                        return Ok(self.builder.block_params(merge_block)[0]);
                    }
                }
            }
        }

        // Check for resolved call (trait method, sig dispatch, or auto-curry)
        // fn_specific_resolutions (from monomorphisation) takes priority
        let resolved = self
            .fn_specific_resolutions
            .and_then(|m| m.get(span))
            .or_else(|| self.method_resolutions.get(span));
        if let Some(resolved) = resolved {
            match resolved {
                crate::typechecker::ResolvedCall::TraitMethod { mangled_name } => {
                    // Try inline primitive first (zero-cost for +$Int, -$Int, etc.)
                    if let Some(val) = self.compile_inline_primitive(mangled_name, &arg_vals) {
                        return Ok(val);
                    }
                    // Fall through to direct call (e.g., show$Int from prelude)
                    return self.compile_direct_call(mangled_name, &arg_vals, *span);
                }
                crate::typechecker::ResolvedCall::SigDispatch { mangled_name } => {
                    return self.compile_direct_call(mangled_name, &arg_vals, *span);
                }
                crate::typechecker::ResolvedCall::AutoCurry {
                    target_name,
                    applied_count,
                    total_count,
                } => {
                    return self.compile_auto_curry(
                        target_name,
                        &arg_vals,
                        *applied_count,
                        *total_count,
                        *span,
                    );
                }
                crate::typechecker::ResolvedCall::BuiltinFn(fq) => {
                    // Prefer builtin_methods lookup (works for both JIT and ObjectModule)
                    let user_name = fq.symbol.as_ref();
                    if let Some(&func_id) = self.builtin_methods.get(user_name) {
                        let local =
                            self.module.declare_func_in_func(func_id, self.builder.func);
                        let call = self.builder.ins().call(local, &arg_vals);
                        return Ok(self.builder.inst_results(call)[0]);
                    }
                    // Fallback: look up the func_id from the module entry
                    if let Some(cm) = self.modules.get(&fq.module) {
                        if let Some(crate::module::ModuleEntry::Def {
                            kind:
                                crate::module::DefKind::Primitive {
                                    func_id: Some(fid), ..
                                },
                            ..
                        }) = cm.get(fq.symbol.as_ref())
                        {
                            let local =
                                self.module.declare_func_in_func(*fid, self.builder.func);
                            let call = self.builder.ins().call(local, &arg_vals);
                            return Ok(self.builder.inst_results(call)[0]);
                        }
                    }
                    // Fall through to existing dispatch if func_id not yet populated
                }
            }
        }

        // Optimization: direct call for known top-level functions (bypasses closure convention)
        if let Expr::Var { name, .. } = callee {
            let bare = resolve_bare_name(name);
            if !self.variables.contains_key(bare) {
                // Inline primitive (add-i64, etc.) — zero-overhead
                if let Some(val) = self.compile_inline_primitive(bare, &arg_vals) {
                    return Ok(val);
                }

                // Operator wrapper fallback (e.g., operators used via builtin_methods)
                if let Some(&func_id) = self.builtin_methods.get(bare) {
                    let local = self.module.declare_func_in_func(func_id, self.builder.func);
                    let call = self.builder.ins().call(local, &arg_vals);
                    return Ok(self.builder.inst_results(call)[0]);
                }

                // Known top-level function
                if self.is_known_function(bare) {
                    return self.compile_direct_call(bare, &arg_vals, *span);
                }
            }
        }

        // General case: callee is a closure value
        let callee_val = self.compile_expr(callee)?;
        let result = self.compile_closure_call(callee_val, &arg_vals);
        Ok(result)
    }

    /// Compile a tail self-recursive call as a jump to the loop header.
    /// Reuses the current stack frame, converting recursion into iteration.
    fn compile_tail_self_call(&mut self, args: &[Expr]) -> Result<Value, CranelispError> {
        // Not in tail position for arg sub-expressions
        self.in_tail_position = false;

        // Compile all arguments (fresh SSA values)
        let arg_vals: Vec<Value> = args
            .iter()
            .map(|a| self.compile_expr(a))
            .collect::<Result<_, _>>()?;

        // Dec all heap-typed bindings in scope before jumping
        self.emit_scope_cleanup_for_tco();

        // Jump to loop header with new arg values
        let loop_block = self.tail_loop_block.unwrap();
        let block_args: Vec<BlockArg> = arg_vals.iter().map(|v| BlockArg::Value(*v)).collect();
        self.builder.ins().jump(loop_block, &block_args);

        // Create a dead block for subsequent code (unreachable, Cranelift eliminates it)
        let dead_block = self.builder.create_block();
        self.builder.switch_to_block(dead_block);
        self.builder.seal_block(dead_block);

        // Return dummy value — this code is unreachable
        Ok(self.builder.ins().iconst(types::I64, 0))
    }

    /// Compile a direct call to a known named function.
    pub(crate) fn compile_direct_call(
        &mut self,
        name: &str,
        arg_vals: &[Value],
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        match &self.call_mode {
            CallMode::Direct { func_ids } => {
                let func_id = *func_ids
                    .get(name)
                    .ok_or_else(|| CranelispError::CodegenError {
                        message: format!("undefined function: {}", name),
                        span,
                    })?;
                let local_func = self.module.declare_func_in_func(func_id, self.builder.func);
                let call = self.builder.ins().call(local_func, arg_vals);
                Ok(self.builder.inst_results(call)[0])
            }
            CallMode::Indirect { fn_slots } => {
                let fn_slot = fn_slots
                    .get(name)
                    .ok_or_else(|| CranelispError::CodegenError {
                        message: format!("undefined function: {}", name),
                        span,
                    })?;
                let param_count = fn_slot.param_count;
                let slot = fn_slot.slot;

                let mut sig = self.module.make_signature();
                for _ in 0..param_count {
                    sig.params.push(AbiParam::new(types::I64));
                }
                sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = self.builder.import_signature(sig);

                let base = fn_slot.emit_got_base(&mut self.builder, self.module);
                let offset = self.builder.ins().iconst(types::I64, (slot * 8) as i64);
                let ptr_addr = self.builder.ins().iadd(base, offset);
                let fn_ptr = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), ptr_addr, 0);

                let call = self.builder.ins().call_indirect(sig_ref, fn_ptr, arg_vals);
                Ok(self.builder.inst_results(call)[0])
            }
        }
    }

    /// Compile a closure call: load code_ptr from closure[0], call_indirect(code_ptr, [closure, args...]).
    pub(crate) fn compile_closure_call(&mut self, callee_val: Value, arg_vals: &[Value]) -> Value {
        // Build signature: (env_ptr: i64, params...) -> i64
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr
        for _ in arg_vals {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = self.builder.import_signature(sig);

        // Load code_ptr from closure[0]
        let code_ptr = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), callee_val, 0);

        // Build args: [callee_val (as env_ptr), arg_vals...]
        let mut all_args = vec![callee_val];
        all_args.extend_from_slice(arg_vals);

        let call = self
            .builder
            .ins()
            .call_indirect(sig_ref, code_ptr, &all_args);
        self.builder.inst_results(call)[0]
    }
}
