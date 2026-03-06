// Vec codegen: VecLit compilation and inline vec-get/vec-set/vec-push/vec-len.
//
// compile_vec_lit: allocate a Vec via runtime/vec_new, store each element
// compile_vec_get: bounds-checked element access with RC inc for heap elements
// compile_vec_set: COW inline + extern fallback
// compile_vec_push: COW inline + extern fallback
// compile_vec_len: inline load of len field
//
// Element inc/dec function generation for Vec copy-path externs.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{
    CranelispError, Expr, HeapCategory, HeapHeader, Span, Type,
};

use crate::heap::{self, HeapVec, NULLARY_THRESHOLD_I64};

use super::FnCompiler;

impl<'a> FnCompiler<'a> {
    /// Compile a Vec literal: `[e1 e2 e3]` → allocate Vec, store elements.
    pub(crate) fn compile_vec_lit(
        &mut self,
        elements: &[Expr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_new_id = self.ctx.vec_new_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/vec_new not declared (need declare_intrinsics)".into(),
                span,
            }
        })?;

        let len = elements.len() as i64;

        // Compile all element expressions first.
        let elem_vals: Vec<Value> = elements
            .iter()
            .map(|e| self.compile_expr(e))
            .collect::<Result<_, _>>()?;

        // Call runtime/vec_new(len) — allocates Vec struct + data buffer with len capacity.
        let len_val = self.builder.ins().iconst(types::I64, len);
        let vec_new_ref = self
            .module
            .declare_func_in_func(vec_new_id, self.builder.func);
        let call = self.builder.ins().call(vec_new_ref, &[len_val]);
        let vec_ptr = self.builder.inst_results(call)[0];

        // Load data_ptr from the Vec struct.
        let data_ptr = heap::heap_load(
            &mut self.builder,
            vec_ptr,
            HeapVec::DATA_PTR_OFFSET,
        ); // data_ptr: i64 (ptr-width)

        // Store each element into the data buffer at data_ptr + i * 8.
        for (i, &val) in elem_vals.iter().enumerate() {
            let offset = (i * 8) as i32;
            heap::heap_store(&mut self.builder, val, data_ptr, offset);
        }

        // Set len = number of elements.
        let len_i64 = self.builder.ins().iconst(types::I64, len);
        heap::heap_store(&mut self.builder, len_i64, vec_ptr, HeapVec::LEN_OFFSET);

        Ok(vec_ptr)
    }

    /// Try to compile a Vec operation inline. Returns Some(val) if handled.
    ///
    /// Called from compile_apply when the callee is a known Vec primitive name.
    /// `args` are the original expressions (for last-use analysis).
    /// `arg_vals` are the pre-compiled argument Cranelift values.
    pub(crate) fn compile_vec_op(
        &mut self,
        name: &str,
        args: &[Expr],
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Option<Value>, CranelispError> {


        match name {
            "vec-get" if args.len() == 2 => {
                let result = self.compile_vec_get(
                    &args[0], arg_vals[0], arg_vals[1], span,
                )?;
                Ok(Some(result))
            }
            "vec-set" if args.len() == 3 => {
                let result = self.compile_vec_set(
                    &args[0], arg_vals, span,
                )?;
                Ok(Some(result))
            }
            "vec-push" if args.len() == 2 => {
                let result = self.compile_vec_push(
                    &args[0], arg_vals, span,
                )?;
                Ok(Some(result))
            }
            "vec-len" if args.len() == 1 => {
                let result = self.compile_vec_len(arg_vals[0]);
                Ok(Some(result))
            }
            _ => Ok(None),
        }
    }

    /// Compile `vec-len`: inline load of len field at HeapVec::LEN_OFFSET.
    fn compile_vec_len(&mut self, vec_val: Value) -> Value {
        heap::heap_load(&mut self.builder, vec_val, HeapVec::LEN_OFFSET) // len: i64
    }

    /// Compile `vec-get`: bounds-checked element access.
    ///
    /// 1. Load len, check idx >= 0 && idx < len, trap on out-of-bounds
    /// 2. Load data_ptr, load element at data_ptr + idx * 8
    /// 3. If element type is heap, call emit_rc_inc on loaded value
    fn compile_vec_get(
        &mut self,
        vec_expr: &Expr,
        vec_val: Value,
        idx_val: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let panic_id = self.ctx.panic_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/panic not declared".into(),
                span,
            }
        })?;

        // Load len from Vec.
        let len = heap::heap_load(&mut self.builder, vec_val, HeapVec::LEN_OFFSET);

        // Bounds check: idx < 0 || idx >= len → panic.
        let zero = self.builder.ins().iconst(types::I64, 0);
        let neg_check = self
            .builder
            .ins()
            .icmp(IntCC::SignedLessThan, idx_val, zero);
        let bounds_check = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, idx_val, len);
        let out_of_bounds = self.builder.ins().bor(neg_check, bounds_check);

        let ok_block = self.builder.create_block();
        let panic_block = self.builder.create_block();

        self.builder
            .ins()
            .brif(out_of_bounds, panic_block, &[], ok_block, &[]);

        // Panic path: call runtime/panic with error message.
        self.builder.switch_to_block(panic_block);
        self.builder.seal_block(panic_block);
        emit_vec_bounds_panic(&mut self.builder, self.module, panic_id, span)?;

        // OK path: load element.
        self.builder.switch_to_block(ok_block);
        self.builder.seal_block(ok_block);

        // Load data_ptr.
        let data_ptr = heap::heap_load(
            &mut self.builder,
            vec_val,
            HeapVec::DATA_PTR_OFFSET,
        ); // data_ptr: i64

        // Compute element address: data_ptr + idx * 8.
        let eight = self.builder.ins().iconst(types::I64, 8);
        let byte_offset = self.builder.ins().imul(idx_val, eight);
        let elem_addr = self.builder.ins().iadd(data_ptr, byte_offset);

        // Load element value.
        let elem = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), elem_addr, 0);

        // If element type is heap, emit RC inc on the loaded value.
        if let Some(elem_type) = self.vec_elem_type(vec_expr) {
            let category = HeapCategory::classify(&elem_type, Some(self.ctx.type_defs));
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, elem);
                }
                HeapCategory::Mixed => {
                    emit_guarded_rc_inc(&mut self.builder, elem);
                }
                HeapCategory::NeverHeap => {}
            }
        }

        Ok(elem)
    }

    /// Compile `vec-set`: COW inline + extern fallback.
    ///
    /// arg_vals: [vec_val, idx_val, new_val]
    fn compile_vec_set(
        &mut self,
        vec_expr: &Expr,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_val = arg_vals[0];
        let idx_val = arg_vals[1];
        let new_val = arg_vals[2];

        let elem_type = self.vec_elem_type(vec_expr);
        let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;

        // Check if vec is at last use (compile-time).
        let is_last = self.is_vec_last_use(vec_expr);

        if is_last {
            // Runtime COW: check rc == 1.
            self.compile_vec_set_cow(vec_val, idx_val, new_val, inc_fn_ptr, &elem_type, span)
        } else {
            // Copy path: call vec-set-copy extern.
            self.compile_vec_set_copy_call(vec_val, idx_val, new_val, inc_fn_ptr, span)
        }
    }

    /// Compile vec-set COW inline path with runtime RC check fallback to copy.
    fn compile_vec_set_cow(
        &mut self,
        vec_val: Value,
        idx_val: Value,
        new_val: Value,
        inc_fn_ptr: Value,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/dealloc not declared".into(),
                span,
            }
        })?;

        // Load RC and check if == 1 (unique owner).
        let rc = heap::heap_load(
            &mut self.builder,
            vec_val,
            HeapHeader::RC_OFFSET,
        ); // rc: i64
        let one = self.builder.ins().iconst(types::I64, 1);
        let is_unique = self.builder.ins().icmp(IntCC::Equal, rc, one);

        let mutate_block = self.builder.create_block();
        let copy_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        self.builder
            .ins()
            .brif(is_unique, mutate_block, &[], copy_block, &[]);

        // Mutate-in-place path: dec old element, store new, return same vec.
        self.builder.switch_to_block(mutate_block);
        self.builder.seal_block(mutate_block);

        // Load data_ptr and old element.
        let data_ptr = heap::heap_load(
            &mut self.builder,
            vec_val,
            HeapVec::DATA_PTR_OFFSET,
        );
        let eight = self.builder.ins().iconst(types::I64, 8);
        let byte_off = self.builder.ins().imul(idx_val, eight);
        let elem_addr = self.builder.ins().iadd(data_ptr, byte_off);
        let old_elem = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), elem_addr, 0);

        // Dec the old element (if heap type).
        if let Some(ty) = &elem_type {
            let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_dec(
                        &mut self.builder,
                        self.module,
                        old_elem,
                        dealloc_id,
                        None,
                    );
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_dec_guarded(
                        &mut self.builder,
                        self.module,
                        old_elem,
                        dealloc_id,
                        None,
                        true,
                    );
                }
                HeapCategory::NeverHeap => {}
            }
        }

        // Inc the new value (if heap type) — the vec needs its own reference.
        // The caller retains its reference; the vec is gaining one.
        if let Some(ty) = &elem_type {
            let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, new_val);
                }
                HeapCategory::Mixed => {
                    emit_guarded_rc_inc(&mut self.builder, new_val);
                }
                HeapCategory::NeverHeap => {}
            }
        }

        // Store new value.
        self.builder
            .ins()
            .store(MemFlags::trusted(), new_val, elem_addr, 0);

        self.builder.ins().jump(merge_block, &[vec_val]);

        // Copy path: call vec-set-copy extern.
        self.builder.switch_to_block(copy_block);
        self.builder.seal_block(copy_block);
        let copy_result = self.emit_extern_call_4(
            "vec-set-copy", vec_val, idx_val, new_val, inc_fn_ptr, span,
        )?;
        self.builder.ins().jump(merge_block, &[copy_result]);

        // Merge.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Compile vec-set copy path (non-last-use, always copies).
    fn compile_vec_set_copy_call(
        &mut self,
        vec_val: Value,
        idx_val: Value,
        new_val: Value,
        inc_fn_ptr: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        self.emit_extern_call_4("vec-set-copy", vec_val, idx_val, new_val, inc_fn_ptr, span)
    }

    /// Compile `vec-push`: COW inline + extern fallback.
    ///
    /// arg_vals: [vec_val, new_val]
    fn compile_vec_push(
        &mut self,
        vec_expr: &Expr,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_val = arg_vals[0];
        let new_val = arg_vals[1];

        let elem_type = self.vec_elem_type(vec_expr);
        let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;

        let is_last = self.is_vec_last_use(vec_expr);

        if is_last {
            self.compile_vec_push_cow(vec_val, new_val, inc_fn_ptr, span)
        } else {
            // Copy path: call vec-push-copy extern.
            self.emit_extern_call_3("vec-push-copy", vec_val, new_val, inc_fn_ptr, span)
        }
    }

    /// Compile vec-push COW inline path with runtime RC check.
    fn compile_vec_push_cow(
        &mut self,
        vec_val: Value,
        new_val: Value,
        inc_fn_ptr: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Load RC.
        let rc = heap::heap_load(
            &mut self.builder,
            vec_val,
            HeapHeader::RC_OFFSET,
        );
        let one = self.builder.ins().iconst(types::I64, 1);
        let is_unique = self.builder.ins().icmp(IntCC::Equal, rc, one);

        let unique_block = self.builder.create_block();
        let copy_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        self.builder
            .ins()
            .brif(is_unique, unique_block, &[], copy_block, &[]);

        // Unique path: check if len < cap.
        self.builder.switch_to_block(unique_block);
        self.builder.seal_block(unique_block);

        let len = heap::heap_load(
            &mut self.builder,
            vec_val,
            HeapVec::LEN_OFFSET,
        );
        let cap = heap::heap_load(
            &mut self.builder,
            vec_val,
            HeapVec::CAP_OFFSET,
        );
        let has_capacity = self
            .builder
            .ins()
            .icmp(IntCC::SignedLessThan, len, cap);

        let fast_block = self.builder.create_block();
        let grow_block = self.builder.create_block();

        self.builder
            .ins()
            .brif(has_capacity, fast_block, &[], grow_block, &[]);

        // Fast path: store at data[len], increment len.
        self.builder.switch_to_block(fast_block);
        self.builder.seal_block(fast_block);

        let data_ptr = heap::heap_load(
            &mut self.builder,
            vec_val,
            HeapVec::DATA_PTR_OFFSET,
        );
        let eight = self.builder.ins().iconst(types::I64, 8);
        let byte_off = self.builder.ins().imul(len, eight);
        let elem_addr = self.builder.ins().iadd(data_ptr, byte_off);
        self.builder
            .ins()
            .store(MemFlags::trusted(), new_val, elem_addr, 0);

        // Increment len.
        let new_len = self.builder.ins().iadd_imm(len, 1);
        heap::heap_store(&mut self.builder, new_len, vec_val, HeapVec::LEN_OFFSET);

        self.builder.ins().jump(merge_block, &[vec_val]);

        // Grow path: call vec-push-grow extern.
        self.builder.switch_to_block(grow_block);
        self.builder.seal_block(grow_block);
        let grow_result = self.emit_extern_call_2("vec-push-grow", vec_val, new_val, span)?;
        self.builder.ins().jump(merge_block, &[grow_result]);

        // Copy path: call vec-push-copy extern.
        self.builder.switch_to_block(copy_block);
        self.builder.seal_block(copy_block);
        let copy_result = self.emit_extern_call_3(
            "vec-push-copy", vec_val, new_val, inc_fn_ptr, span,
        )?;
        self.builder.ins().jump(merge_block, &[copy_result]);

        // Merge.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    // --- Helpers ---

    /// Extract the element type from a Vec expression's type in expr_types.
    fn vec_elem_type(&self, vec_expr: &Expr) -> Option<Type> {
        if let Some(Type::ADT(name, args)) = self.ctx.expr_types.get(&vec_expr.span()) {
            if name.as_ref() == "Vec" && args.len() == 1 {
                return Some(args[0].clone());
            }
        }
        None
    }

    /// Check if a Vec expression is at its last use (for COW eligibility).
    fn is_vec_last_use(&self, vec_expr: &Expr) -> bool {
        if let Expr::Var { name, span } = vec_expr {
            self.is_last_use(name, *span)
        } else {
            // Temporary expression: ownership transfers, treat as unique.
            true
        }
    }

    /// Resolve or generate a per-element-type inc function pointer.
    ///
    /// Returns iconst(0) for NeverHeap types (runtime skips the call).
    /// Returns a Cranelift func_addr for AlwaysHeap and Mixed types.
    fn resolve_elem_inc_fn_ptr(
        &mut self,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            // Unknown element type: assume NeverHeap (safe default).
            return Ok(self.builder.ins().iconst(types::I64, 0));
        };

        let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
        match category {
            HeapCategory::NeverHeap => Ok(self.builder.ins().iconst(types::I64, 0)),
            HeapCategory::AlwaysHeap => {
                let func_id = self.build_elem_inc_fn(false, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
            HeapCategory::Mixed => {
                let func_id = self.build_elem_inc_fn(true, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
        }
    }

    /// Resolve or generate a per-element-type dec function pointer.
    ///
    /// Returns iconst(0) for NeverHeap types (runtime skips the call).
    /// Used by Vec drop glue (when integrated with scope-exit RC emission).
    #[allow(dead_code)]
    fn resolve_elem_dec_fn_ptr(
        &mut self,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            return Ok(self.builder.ins().iconst(types::I64, 0));
        };

        let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
        match category {
            HeapCategory::NeverHeap => Ok(self.builder.ins().iconst(types::I64, 0)),
            HeapCategory::AlwaysHeap => {
                let func_id = self.build_elem_dec_fn(false, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
            HeapCategory::Mixed => {
                let func_id = self.build_elem_dec_fn(true, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
        }
    }

    /// Build a standalone inc function: `(val: i64) -> i64`.
    ///
    /// If `guarded` is true, guards against bare nullary tags.
    fn build_elem_inc_fn(
        &mut self,
        guarded: bool,
        span: Span,
    ) -> Result<cranelift_module::FuncId, CranelispError> {
        let suffix = if guarded { "mixed" } else { "heap" };
        let name = format!("runtime/vec_elem_inc_{suffix}");

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare elem inc fn: {e}"),
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

        let val = builder.block_params(entry)[0];

        if guarded {
            // Guard: skip inc if val < NULLARY_TAG_THRESHOLD.
            let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
            let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, val, threshold);
            let inc_block = builder.create_block();
            let ret_block = builder.create_block();

            builder.ins().brif(is_tag, ret_block, &[], inc_block, &[]);

            builder.switch_to_block(inc_block);
            builder.seal_block(inc_block);
            heap::emit_rc_inc(&mut builder, val);
            builder.ins().jump(ret_block, &[]);

            builder.switch_to_block(ret_block);
            builder.seal_block(ret_block);
        } else {
            heap::emit_rc_inc(&mut builder, val);
        }

        builder.ins().return_(&[val]);
        builder.finalize();

        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define elem inc fn: {e}"),
                span,
            })?;

        Ok(func_id)
    }

    /// Build a standalone dec function: `(val: i64) -> i64`.
    ///
    /// If `guarded` is true, guards against bare nullary tags.
    /// Used by Vec drop glue (when integrated with scope-exit RC emission).
    #[allow(dead_code)]
    fn build_elem_dec_fn(
        &mut self,
        guarded: bool,
        span: Span,
    ) -> Result<cranelift_module::FuncId, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/dealloc not declared".into(),
                span,
            }
        })?;

        let suffix = if guarded { "mixed" } else { "heap" };
        let name = format!("runtime/vec_elem_dec_{suffix}");

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare elem dec fn: {e}"),
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

        let val = builder.block_params(entry)[0];

        heap::emit_rc_dec_guarded(
            &mut builder,
            self.module,
            val,
            dealloc_id,
            None,
            guarded,
        );

        builder.ins().return_(&[val]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define elem dec fn: {e}"),
                span,
            })?;

        Ok(func_id)
    }

    /// Emit an extern call with 2 i64 args, returning i64.
    fn emit_extern_call_2(
        &mut self,
        name: &str,
        a: Value,
        b: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern '{name}': {e}"),
                span,
            })?;
        let func_ref = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(func_ref, &[a, b]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Emit an extern call with 3 i64 args, returning i64.
    fn emit_extern_call_3(
        &mut self,
        name: &str,
        a: Value,
        b: Value,
        c: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern '{name}': {e}"),
                span,
            })?;
        let func_ref = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(func_ref, &[a, b, c]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Emit an extern call with 4 i64 args, returning i64.
    fn emit_extern_call_4(
        &mut self,
        name: &str,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern '{name}': {e}"),
                span,
            })?;
        let func_ref = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(func_ref, &[a, b, c, d]);
        Ok(self.builder.inst_results(call)[0])
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// Emit guarded RC inc: skip if value is a bare nullary tag.
fn emit_guarded_rc_inc(builder: &mut FunctionBuilder, val: Value) {
    let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
    let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, val, threshold);

    let inc_block = builder.create_block();
    let cont_block = builder.create_block();

    builder.ins().brif(is_tag, cont_block, &[], inc_block, &[]);

    builder.switch_to_block(inc_block);
    builder.seal_block(inc_block);
    heap::emit_rc_inc(builder, val);
    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

/// Emit a bounds-check panic for vec-get.
fn emit_vec_bounds_panic(
    builder: &mut FunctionBuilder,
    module: &mut cranelift_jit::JITModule,
    panic_func_id: cranelift_module::FuncId,
    span: Span,
) -> Result<(), CranelispError> {
    // runtime/panic(msg_ptr, msg_len) — never returns.
    // We store the error message in a data section.
    let msg = b"vec-get: index out of bounds";
    let data_id = module
        .declare_anonymous_data(false, false)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare panic data: {e}"),
            span,
        })?;
    let mut desc = cranelift_module::DataDescription::new();
    desc.define(msg.to_vec().into_boxed_slice());
    module
        .define_data(data_id, &desc)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define panic data: {e}"),
            span,
        })?;

    let gv = module.declare_data_in_func(data_id, builder.func);
    let msg_ptr = builder.ins().global_value(types::I64, gv);
    let msg_len = builder.ins().iconst(types::I64, msg.len() as i64);

    let panic_ref = module.declare_func_in_func(panic_func_id, builder.func);
    builder.ins().call(panic_ref, &[msg_ptr, msg_len]);

    // Panic never returns, but Cranelift needs a terminator.
    builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(
        super::MATCH_EXHAUSTION_TRAP,
    ));

    Ok(())
}
