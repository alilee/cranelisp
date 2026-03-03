//! Inline Vec codegen with element RC tracking and COW (copy-on-write).
//!
//! vec-get, vec-set, vec-push are intercepted at compile time and generate
//! inline Cranelift IR instead of calling extern "C" functions. This enables:
//! - Element RC: inc on get, inc copies on set/push (via fn ptr to externs)
//! - COW: mutate in place when is_last_use + runtime rc==1

use cranelift::codegen::ir::{types, AtomicRmwOp, MemFlags};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};
use std::collections::HashMap;

use crate::ast::Expr;
use crate::codegen::{classify_heap_type, mangle_type_for_drop, FnCompiler, HeapCategory};
use crate::error::{CranelispError, Span};
use crate::names::resolve_bare_name;
use crate::types::Type;

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Try to compile a Vec operation inline. Returns Some(val) if handled, None to fall through.
    /// `arg_vals` are the pre-compiled argument values from compile_apply.
    pub(crate) fn compile_vec_op(
        &mut self,
        name: &str,
        args: &[Expr],
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Option<Value>, CranelispError> {
        match name {
            "vec-get" if args.len() == 2 => {
                Ok(Some(self.compile_vec_get_inline(&args[0], arg_vals[0], arg_vals[1], span)?))
            }
            "vec-set" if args.len() == 3 => {
                Ok(Some(self.compile_vec_set_inline(args, arg_vals, span)?))
            }
            "vec-push" if args.len() == 2 => {
                Ok(Some(self.compile_vec_push_inline(args, arg_vals, span)?))
            }
            _ => Ok(None),
        }
    }

    /// Extract the element type from a Vec expression's type.
    fn vec_elem_type(&self, vec_expr: &Expr) -> Option<Type> {
        if let Some(Type::ADT(name, args)) = self.expr_types.get(&vec_expr.span()) {
            if name == "Vec" && args.len() == 1 {
                return Some(args[0].clone());
            }
        }
        None
    }

    /// Resolve or generate a standalone inc function for the given element type.
    /// Returns a Cranelift Value containing the function pointer (or iconst(0) for NeverHeap).
    fn resolve_elem_inc_fn_ptr(&mut self, elem_type: &Type, _span: Span) -> Value {
        let category = classify_heap_type(elem_type, self.type_defs);
        if matches!(category, HeapCategory::NeverHeap) {
            return self.builder.ins().iconst(types::I64, 0);
        }

        let mangled = format!("vec_elem_inc${}", mangle_type_for_drop(elem_type));
        let func_id = if let Some(&fid) = self.vec_elem_inc_cache.get(&mangled) {
            fid
        } else {
            let fid = build_elem_inc_fn(self.module, elem_type, self.type_defs, &category);
            self.vec_elem_inc_cache.insert(mangled, fid);
            fid
        };

        let local = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        self.builder.ins().func_addr(types::I64, local)
    }

    /// Handle RC for a new value being stored into a Vec.
    /// Same pattern as constructor Var arg inc (apply.rs:66-83):
    ///   Var + last-use → mark consumed (ownership transfer, no inc)
    ///   Var + not last-use → emit_inc (Vec gets a new reference)
    ///   Temp expression → nothing (fresh rc=1, ownership transfers to Vec)
    fn emit_stored_value_rc(&mut self, val: Value, val_expr: &Expr, elem_type: &Type) {
        // Borrowed temp being stored creates a new reference — needs inc
        if self.is_borrowed_temp(val) && elem_type.is_heap_type() {
            self.emit_inc(val, elem_type);
            return;
        }
        if matches!(val_expr, Expr::Var { .. }) {
            if elem_type.is_heap_type() {
                if self.is_last_use(val_expr) {
                    if let Expr::Var { name, .. } = val_expr {
                        let bare = resolve_bare_name(name);
                        if let Some(&src_var) = self.variables.get(bare) {
                            self.mark_consumed(src_var);
                        }
                    }
                } else {
                    self.emit_inc(val, elem_type);
                    // Another reference → no longer unique
                    if let Expr::Var { name, .. } = val_expr {
                        let bare = resolve_bare_name(name);
                        if let Some(&src_var) = self.variables.get(bare) {
                            self.remove_unique(src_var);
                        }
                    }
                }
            }
        }
    }

    // ---- vec-get inline ----

    /// Inline vec-get: bounds check + load + emit_inc for heap-typed elements.
    fn compile_vec_get_inline(
        &mut self,
        vec_arg: &Expr,
        vec_val: Value,
        idx_val: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let elem_type = self.vec_elem_type(vec_arg).unwrap_or(Type::Int);

        // Bounds check: load len, check 0 <= idx < len
        let len = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), vec_val, 0);

        let panic_block = self.builder.create_block();
        let load_block = self.builder.create_block();

        // Check idx < 0 || idx >= len
        let zero = self.builder.ins().iconst(types::I64, 0);
        let neg = self
            .builder
            .ins()
            .icmp(IntCC::SignedLessThan, idx_val, zero);
        let oob = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, idx_val, len);
        let bad = self.builder.ins().bor(neg, oob);
        self.builder
            .ins()
            .brif(bad, panic_block, &[], load_block, &[]);

        // Panic block
        self.builder.switch_to_block(panic_block);
        self.builder.seal_block(panic_block);
        self.emit_panic_with_message("vec-get: index out of bounds", span)?;
        self.builder.ins().trap(TrapCode::user(1).unwrap());

        // Load block
        self.builder.switch_to_block(load_block);
        self.builder.seal_block(load_block);

        let data_ptr = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), vec_val, 16);
        let eight = self.builder.ins().iconst(types::I64, 8);
        let offset = self.builder.ins().imul(idx_val, eight);
        let elem_addr = self.builder.ins().iadd(data_ptr, offset);
        let elem = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), elem_addr, 0);

        // Inc the element: caller gets a new reference
        // UNLESS owner is unique and element is heap-typed → borrow (skip inc)
        let owner_is_unique = if elem_type.is_heap_type() {
            if let Expr::Var { name, .. } = vec_arg {
                let bare = resolve_bare_name(name);
                self.branch_depth == 0 && self.is_var_unique(bare)
            } else {
                false
            }
        } else {
            false
        };
        if owner_is_unique {
            self.mark_borrowed_temp(elem);
        } else {
            self.emit_inc(elem, &elem_type);
        }

        Ok(elem)
    }

    // ---- vec-set inline ----

    fn compile_vec_set_inline(
        &mut self,
        args: &[Expr],
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_arg = &args[0];
        let val_arg = &args[2];

        let elem_type = self.vec_elem_type(vec_arg).unwrap_or(Type::Int);
        let vec_type = Type::ADT("Vec".to_string(), vec![elem_type.clone()]);

        let vec_val = arg_vals[0];
        let idx_val = arg_vals[1];
        let new_val = arg_vals[2];

        // Handle new_val RC (same as constructor Var arg inc)
        self.emit_stored_value_rc(new_val, val_arg, &elem_type);

        let is_last = self.is_last_use(vec_arg);

        // Check if owner is statically known-unique (skip runtime rc check)
        let owner_is_unique = if let Expr::Var { name, .. } = vec_arg {
            let bare = resolve_bare_name(name);
            self.is_var_unique(bare)
        } else {
            false
        };

        if is_last && owner_is_unique {
            // Static COW: known unique + last use → mutate in place unconditionally
            if let Expr::Var { name, .. } = vec_arg {
                let bare = resolve_bare_name(name);
                if let Some(&var) = self.variables.get(bare) {
                    self.mark_consumed(var);
                }
            }

            // Bounds check
            let len = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), vec_val, 0);
            let panic_block = self.builder.create_block();
            let do_block = self.builder.create_block();

            let zero = self.builder.ins().iconst(types::I64, 0);
            let neg = self
                .builder
                .ins()
                .icmp(IntCC::SignedLessThan, idx_val, zero);
            let oob = self
                .builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, idx_val, len);
            let bad = self.builder.ins().bor(neg, oob);
            self.builder
                .ins()
                .brif(bad, panic_block, &[], do_block, &[]);

            self.builder.switch_to_block(panic_block);
            self.builder.seal_block(panic_block);
            self.emit_panic_with_message("vec-set: index out of bounds", span)?;
            self.builder.ins().trap(TrapCode::user(1).unwrap());

            self.builder.switch_to_block(do_block);
            self.builder.seal_block(do_block);

            // Load data_ptr, compute element address
            let data_ptr = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), vec_val, 16);
            let eight = self.builder.ins().iconst(types::I64, 8);
            let elem_offset = self.builder.ins().imul(idx_val, eight);
            let elem_addr = self.builder.ins().iadd(data_ptr, elem_offset);

            // Dec old element at index
            let old_elem = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), elem_addr, 0);
            self.emit_dec(old_elem, &elem_type);

            // Store new value
            self.builder
                .ins()
                .store(MemFlags::trusted(), new_val, elem_addr, 0);

            // Return same Vec pointer (still unique for the caller)
            Ok(vec_val)
        } else if is_last {
            // Mark consumed — skip scope-exit dec regardless of COW or copy
            if let Expr::Var { name, .. } = vec_arg {
                let bare = resolve_bare_name(name);
                if let Some(&var) = self.variables.get(bare) {
                    self.mark_consumed(var);
                }
            }

            // Merge block receives the result
            let merge_block = self.builder.create_block();
            self.builder
                .append_block_param(merge_block, types::I64);

            let cow_block = self.builder.create_block();
            let copy_block = self.builder.create_block();

            // Runtime rc check
            let eight = self.builder.ins().iconst(types::I64, 8);
            let rc_addr = self.builder.ins().isub(vec_val, eight);
            let rc = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), rc_addr, 0);
            let one = self.builder.ins().iconst(types::I64, 1);
            let is_unique = self.builder.ins().icmp(IntCC::Equal, rc, one);
            self.builder
                .ins()
                .brif(is_unique, cow_block, &[], copy_block, &[]);

            // COW block: mutate in place
            self.builder.switch_to_block(cow_block);
            self.builder.seal_block(cow_block);
            {
                // Bounds check
                let len = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), vec_val, 0);
                let panic_block = self.builder.create_block();
                let cow_do_block = self.builder.create_block();

                let zero = self.builder.ins().iconst(types::I64, 0);
                let neg = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, idx_val, zero);
                let oob = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, idx_val, len);
                let bad = self.builder.ins().bor(neg, oob);
                self.builder
                    .ins()
                    .brif(bad, panic_block, &[], cow_do_block, &[]);

                self.builder.switch_to_block(panic_block);
                self.builder.seal_block(panic_block);
                self.emit_panic_with_message("vec-set: index out of bounds", span)?;
                self.builder.ins().trap(TrapCode::user(1).unwrap());

                self.builder.switch_to_block(cow_do_block);
                self.builder.seal_block(cow_do_block);

                // Load data_ptr, compute element address
                let data_ptr = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), vec_val, 16);
                let eight = self.builder.ins().iconst(types::I64, 8);
                let elem_offset = self.builder.ins().imul(idx_val, eight);
                let elem_addr = self.builder.ins().iadd(data_ptr, elem_offset);

                // Dec old element at index
                let old_elem = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), elem_addr, 0);
                self.emit_dec(old_elem, &elem_type);

                // Store new value
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), new_val, elem_addr, 0);

                // Return same Vec pointer
                self.builder.ins().jump(
                    merge_block,
                    &[cranelift::codegen::ir::BlockArg::Value(vec_val)],
                );
            }

            // Copy block: call vec-set-rc with inc_fn, then dec old vec
            self.builder.switch_to_block(copy_block);
            self.builder.seal_block(copy_block);
            {
                let inc_fn = self.resolve_elem_inc_fn_ptr(&elem_type, span);

                let set_rc_id = *self
                    .builtin_methods
                    .get("vec-set-rc")
                    .expect("vec-set-rc not registered");
                let set_rc_ref = self
                    .module
                    .declare_func_in_func(set_rc_id, self.builder.func);
                let call = self
                    .builder
                    .ins()
                    .call(set_rc_ref, &[vec_val, idx_val, new_val, inc_fn]);
                let result = self.builder.inst_results(call)[0];

                // Dec old vec (we consumed the caller's reference but rc > 1)
                self.emit_dec(vec_val, &vec_type);

                self.builder.ins().jump(
                    merge_block,
                    &[cranelift::codegen::ir::BlockArg::Value(result)],
                );
            }

            self.builder.switch_to_block(merge_block);
            self.builder.seal_block(merge_block);
            Ok(self.builder.block_params(merge_block)[0])
        } else {
            // Not last-use — always copy
            let inc_fn = self.resolve_elem_inc_fn_ptr(&elem_type, span);

            let set_rc_id = *self
                .builtin_methods
                .get("vec-set-rc")
                .expect("vec-set-rc not registered");
            let set_rc_ref = self
                .module
                .declare_func_in_func(set_rc_id, self.builder.func);
            let call = self
                .builder
                .ins()
                .call(set_rc_ref, &[vec_val, idx_val, new_val, inc_fn]);
            Ok(self.builder.inst_results(call)[0])
        }
    }

    // ---- vec-push inline ----

    fn compile_vec_push_inline(
        &mut self,
        args: &[Expr],
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_arg = &args[0];
        let val_arg = &args[1];

        let elem_type = self.vec_elem_type(vec_arg).unwrap_or(Type::Int);
        let vec_type = Type::ADT("Vec".to_string(), vec![elem_type.clone()]);

        let vec_val = arg_vals[0];
        let new_val = arg_vals[1];

        // Handle new_val RC (same as constructor Var arg inc)
        self.emit_stored_value_rc(new_val, val_arg, &elem_type);

        let is_last = self.is_last_use(vec_arg);

        // Check if owner is statically known-unique (skip runtime rc check)
        let owner_is_unique = if let Expr::Var { name, .. } = vec_arg {
            let bare = resolve_bare_name(name);
            self.is_var_unique(bare)
        } else {
            false
        };

        if is_last && owner_is_unique {
            // Static COW: known unique + last use → mutate in place unconditionally
            if let Expr::Var { name, .. } = vec_arg {
                let bare = resolve_bare_name(name);
                if let Some(&var) = self.variables.get(bare) {
                    self.mark_consumed(var);
                }
            }

            // Capacity check: len < cap → in-place, else grow
            let len = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), vec_val, 0);
            let cap = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), vec_val, 8);

            let inplace_block = self.builder.create_block();
            let grow_block = self.builder.create_block();
            let merge_block = self.builder.create_block();
            self.builder
                .append_block_param(merge_block, types::I64);

            let has_room = self
                .builder
                .ins()
                .icmp(IntCC::SignedLessThan, len, cap);
            self.builder
                .ins()
                .brif(has_room, inplace_block, &[], grow_block, &[]);

            // In-place push (capacity available)
            self.builder.switch_to_block(inplace_block);
            self.builder.seal_block(inplace_block);
            {
                let data_ptr = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), vec_val, 16);
                let eight = self.builder.ins().iconst(types::I64, 8);
                let offset = self.builder.ins().imul(len, eight);
                let elem_addr = self.builder.ins().iadd(data_ptr, offset);
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), new_val, elem_addr, 0);
                let new_len = self.builder.ins().iadd_imm(len, 1);
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), new_len, vec_val, 0);
                self.builder.ins().jump(
                    merge_block,
                    &[cranelift::codegen::ir::BlockArg::Value(vec_val)],
                );
            }

            // Grow path: call vec-push-cow-grow extern
            self.builder.switch_to_block(grow_block);
            self.builder.seal_block(grow_block);
            {
                let grow_id = *self
                    .builtin_methods
                    .get("vec-push-cow-grow")
                    .expect("vec-push-cow-grow not registered");
                let grow_ref = self
                    .module
                    .declare_func_in_func(grow_id, self.builder.func);
                let call = self.builder.ins().call(grow_ref, &[vec_val, new_val]);
                let result = self.builder.inst_results(call)[0];
                self.builder.ins().jump(
                    merge_block,
                    &[cranelift::codegen::ir::BlockArg::Value(result)],
                );
            }

            self.builder.switch_to_block(merge_block);
            self.builder.seal_block(merge_block);
            Ok(self.builder.block_params(merge_block)[0])
        } else if is_last {
            // Mark consumed
            if let Expr::Var { name, .. } = vec_arg {
                let bare = resolve_bare_name(name);
                if let Some(&var) = self.variables.get(bare) {
                    self.mark_consumed(var);
                }
            }

            let merge_block = self.builder.create_block();
            self.builder
                .append_block_param(merge_block, types::I64);

            let cow_block = self.builder.create_block();
            let copy_block = self.builder.create_block();

            // Runtime rc check
            let eight = self.builder.ins().iconst(types::I64, 8);
            let rc_addr = self.builder.ins().isub(vec_val, eight);
            let rc = self
                .builder
                .ins()
                .load(types::I64, MemFlags::trusted(), rc_addr, 0);
            let one = self.builder.ins().iconst(types::I64, 1);
            let is_unique = self.builder.ins().icmp(IntCC::Equal, rc, one);
            self.builder
                .ins()
                .brif(is_unique, cow_block, &[], copy_block, &[]);

            // COW block
            self.builder.switch_to_block(cow_block);
            self.builder.seal_block(cow_block);
            {
                let len = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), vec_val, 0);
                let cap = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), vec_val, 8);

                let inplace_block = self.builder.create_block();
                let grow_block = self.builder.create_block();

                let has_room = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, len, cap);
                self.builder
                    .ins()
                    .brif(has_room, inplace_block, &[], grow_block, &[]);

                // In-place push (capacity available)
                self.builder.switch_to_block(inplace_block);
                self.builder.seal_block(inplace_block);
                {
                    let data_ptr = self
                        .builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), vec_val, 16);
                    let eight = self.builder.ins().iconst(types::I64, 8);
                    let offset = self.builder.ins().imul(len, eight);
                    let elem_addr = self.builder.ins().iadd(data_ptr, offset);
                    self.builder
                        .ins()
                        .store(MemFlags::trusted(), new_val, elem_addr, 0);
                    let new_len = self.builder.ins().iadd_imm(len, 1);
                    self.builder
                        .ins()
                        .store(MemFlags::trusted(), new_len, vec_val, 0);
                    self.builder.ins().jump(
                        merge_block,
                        &[cranelift::codegen::ir::BlockArg::Value(vec_val)],
                    );
                }

                // Grow path: call vec-push-cow-grow extern
                self.builder.switch_to_block(grow_block);
                self.builder.seal_block(grow_block);
                {
                    let grow_id = *self
                        .builtin_methods
                        .get("vec-push-cow-grow")
                        .expect("vec-push-cow-grow not registered");
                    let grow_ref = self
                        .module
                        .declare_func_in_func(grow_id, self.builder.func);
                    let call = self.builder.ins().call(grow_ref, &[vec_val, new_val]);
                    let result = self.builder.inst_results(call)[0];
                    self.builder.ins().jump(
                        merge_block,
                        &[cranelift::codegen::ir::BlockArg::Value(result)],
                    );
                }
            }

            // Copy block
            self.builder.switch_to_block(copy_block);
            self.builder.seal_block(copy_block);
            {
                let inc_fn = self.resolve_elem_inc_fn_ptr(&elem_type, span);

                let push_rc_id = *self
                    .builtin_methods
                    .get("vec-push-rc")
                    .expect("vec-push-rc not registered");
                let push_rc_ref = self
                    .module
                    .declare_func_in_func(push_rc_id, self.builder.func);
                let call = self
                    .builder
                    .ins()
                    .call(push_rc_ref, &[vec_val, new_val, inc_fn]);
                let result = self.builder.inst_results(call)[0];

                // Dec old vec (we consumed the caller's reference but rc > 1)
                self.emit_dec(vec_val, &vec_type);

                self.builder.ins().jump(
                    merge_block,
                    &[cranelift::codegen::ir::BlockArg::Value(result)],
                );
            }

            self.builder.switch_to_block(merge_block);
            self.builder.seal_block(merge_block);
            Ok(self.builder.block_params(merge_block)[0])
        } else {
            // Not last-use — always copy
            let inc_fn = self.resolve_elem_inc_fn_ptr(&elem_type, span);

            let push_rc_id = *self
                .builtin_methods
                .get("vec-push-rc")
                .expect("vec-push-rc not registered");
            let push_rc_ref = self
                .module
                .declare_func_in_func(push_rc_id, self.builder.func);
            let call = self
                .builder
                .ins()
                .call(push_rc_ref, &[vec_val, new_val, inc_fn]);
            Ok(self.builder.inst_results(call)[0])
        }
    }
}

/// Build a standalone Cranelift function that increments the RC of a single
/// element value. Follows the same pattern as drop functions.
fn build_elem_inc_fn<M: Module>(
    module: &mut M,
    _elem_type: &Type,
    _type_defs: Option<&HashMap<String, crate::codegen::TypeDefInfoCg>>,
    category: &HeapCategory,
) -> FuncId {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let func_id = module
        .declare_anonymous_function(&sig)
        .expect("failed to declare vec elem inc function");

    {
        let mut func = cranelift::codegen::ir::Function::with_name_signature(
            cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
            sig,
        );
        let mut func_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut func_ctx);

        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let val = builder.block_params(entry)[0];

        match category {
            HeapCategory::NeverHeap => {
                // Should never be called, but return 0 for safety
            }
            HeapCategory::AlwaysHeap => {
                // Direct inc: load rc at val-8, atomic add 1
                let eight = builder.ins().iconst(types::I64, 8);
                let rc_addr = builder.ins().isub(val, eight);
                let one = builder.ins().iconst(types::I64, 1);
                builder.ins().atomic_rmw(
                    types::I64,
                    MemFlags::new(),
                    AtomicRmwOp::Add,
                    rc_addr,
                    one,
                );
            }
            HeapCategory::Mixed => {
                // Guard: skip if val < 1024 (nullary tag)
                let inc_block = builder.create_block();
                let ret_block = builder.create_block();

                let threshold = builder.ins().iconst(types::I64, 1024);
                let is_low =
                    builder
                        .ins()
                        .icmp(IntCC::UnsignedLessThan, val, threshold);
                builder
                    .ins()
                    .brif(is_low, ret_block, &[], inc_block, &[]);

                builder.switch_to_block(inc_block);
                builder.seal_block(inc_block);
                let eight = builder.ins().iconst(types::I64, 8);
                let rc_addr = builder.ins().isub(val, eight);
                let one = builder.ins().iconst(types::I64, 1);
                builder.ins().atomic_rmw(
                    types::I64,
                    MemFlags::new(),
                    AtomicRmwOp::Add,
                    rc_addr,
                    one,
                );
                builder.ins().jump(ret_block, &[]);

                builder.switch_to_block(ret_block);
                builder.seal_block(ret_block);
            }
        }

        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[zero]);
        builder.finalize();

        let mut ctx = cranelift::codegen::Context::new();
        ctx.func = func;
        module
            .define_function(func_id, &mut ctx)
            .expect("failed to define vec elem inc function");
    }

    func_id
}
