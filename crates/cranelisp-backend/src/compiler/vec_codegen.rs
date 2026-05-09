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

use cranelisp_types::{ErrorLocation, 
    CranelispError, Expr, HeapCategory, HeapHeader, Span, Type,
};

use crate::heap::{self, HeapAdt, HeapVec, NULLARY_THRESHOLD_I64};

use super::{collect_var_ids_from_type, substitute_type_inline, FnCompiler};

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Compile a Vec literal: `[e1 e2 e3]` → allocate Vec, store elements.
    pub(crate) fn compile_vec_lit(
        &mut self,
        elements: &[Expr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_new_id = self.ctx.vec_new_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/vec_new not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
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
                // Drop temporary Vec after read — it's consumed but not returned.
                self.emit_vec_drop_if_temporary(&args[0], arg_vals[0], span)?;
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
                // Drop temporary Vec after read — it's consumed but not returned.
                self.emit_vec_drop_if_temporary(&args[0], arg_vals[0], span)?;
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
                location: ErrorLocation::from_span(span),
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
            let category = HeapCategory::classify(&elem_type, Some(self.ctx.symbol_tables));
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
        let dealloc_id = self.ctx.dealloc_func_id;

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
            let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
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
            let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
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

    /// Extract the element type from a Vec expression's inferred type.
    fn vec_elem_type(&self, vec_expr: &Expr) -> Option<Type> {
        if let Some(Type::ADT(fqtn, args)) = vec_expr.inferred_type()
            && fqtn.name.as_ref() == "Vec" && args.len() == 1 {
                return Some(args[0].clone());
            }
        None
    }

    /// Check if a Vec expression is at its last use (for COW eligibility).
    fn is_vec_last_use(&self, vec_expr: &Expr) -> bool {
        if let Expr::Var { name, span, .. } = vec_expr {
            self.is_last_use(name, *span)
        } else {
            // Temporary expression: ownership transfers, treat as unique.
            true
        }
    }

    /// Emit `vec_drop(vec_val, elem_dec_fn_ptr)` if the Vec expression is a
    /// temporary (not a named variable). Named variables are cleaned up at
    /// scope exit; temporaries have no scope entry and would leak.
    fn emit_vec_drop_if_temporary(
        &mut self,
        vec_expr: &Expr,
        vec_val: Value,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Named variables are handled by scope cleanup — skip.
        if matches!(vec_expr, Expr::Var { .. }) {
            return Ok(());
        }

        let vec_drop_id = self.ctx.vec_drop_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/vec_drop not declared".into(),
                location: ErrorLocation::from_span(span),
            }
        })?;

        let elem_type = self.vec_elem_type(vec_expr);
        let dec_fn_ptr = self.resolve_elem_dec_fn_ptr(&elem_type, span)?;

        let vec_drop_ref = self
            .module
            .declare_func_in_func(vec_drop_id, self.builder.func);
        self.builder.ins().call(vec_drop_ref, &[vec_val, dec_fn_ptr]);

        Ok(())
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

        let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
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
    /// For ADT element types with heap fields, builds a drop glue function
    /// so that fields are dec'd when the element reaches rc=0.
    fn resolve_elem_dec_fn_ptr(
        &mut self,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            return Ok(self.builder.ins().iconst(types::I64, 0));
        };

        let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
        match category {
            HeapCategory::NeverHeap => Ok(self.builder.ins().iconst(types::I64, 0)),
            HeapCategory::AlwaysHeap => {
                let func_id = self.build_elem_dec_fn(false, ty, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
            HeapCategory::Mixed => {
                let func_id = self.build_elem_dec_fn(true, ty, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
        }
    }

    /// Emit an RC dec on a Vec value using the proper vec_drop teardown path.
    ///
    /// When the Vec reaches rc=0, calls `runtime/vec_drop(vec, elem_dec_fn)`
    /// instead of `runtime/dealloc(vec)`. This ensures:
    ///   - each element has its RC dec'd (via `elem_dec_fn`)
    ///   - the data buffer is freed
    ///   - the Vec struct itself is freed
    ///
    /// Without this path, dec'ing a Vec field inside an ADT's drop glue or
    /// at scope exit leaks the elements (their RCs are never dropped) and the
    /// data buffer, causing the allocator to eventually reuse slots that are
    /// still tracked as live by other code — the "alloc-slot reuse + stale
    /// pointer dec" pattern documented in the Sprint 59/60 RC traces.
    pub(crate) fn emit_vec_aware_rc_dec(
        &mut self,
        vec_val: Value,
        elem_type: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        let vec_drop_id = self.ctx.vec_drop_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/vec_drop not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            }
        })?;

        // Build per-element dec fn (or null for NeverHeap elements).
        let elem_dec_fn_ptr = self.resolve_elem_dec_fn_ptr(&Some(elem_type.clone()), span)?;

        emit_vec_rc_dec_with_drop(
            &mut self.builder,
            self.module,
            vec_val,
            vec_drop_id,
            elem_dec_fn_ptr,
        );
        Ok(())
    }

    /// Build a standalone inc function: `(val: i64) -> i64`.
    ///
    /// If `guarded` is true, guards against bare nullary tags.
    /// Returns a cached FuncId if this function was already built.
    fn build_elem_inc_fn(
        &mut self,
        guarded: bool,
        span: Span,
    ) -> Result<cranelift_module::FuncId, CranelispError> {
        let suffix = if guarded { "mixed" } else { "heap" };
        let name = format!("runtime/vec_elem_inc_{suffix}");

        // Check if this function was already built (e.g., by a previous module).
        // declare_function is idempotent — it returns the existing FuncId if the
        // signature matches. We only need to skip define_function to avoid the
        // DuplicateDefinition error from Cranelift.
        if let Some(cranelift_module::FuncOrDataId::Func(existing_id)) =
            self.module.get_name(&name)
        {
            return Ok(existing_id);
        }

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare elem inc fn: {e}"),
                location: ErrorLocation::from_span(span),
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
                location: ErrorLocation::from_span(span),
            })?;

        Ok(func_id)
    }

    /// Build a standalone dec function: `(val: i64) -> i64`.
    ///
    /// If `guarded` is true, guards against bare nullary tags.
    /// If `elem_type` is an ADT with heap-typed fields, a drop glue function
    /// is built and passed to `emit_rc_dec_guarded` so that fields are dec'd
    /// before the ADT itself is freed.
    /// Returns a cached FuncId if this function was already built.
    fn build_elem_dec_fn(
        &mut self,
        guarded: bool,
        elem_type: &Type,
        span: Span,
    ) -> Result<cranelift_module::FuncId, CranelispError> {
        let suffix = if guarded { "mixed" } else { "heap" };
        let type_suffix = match elem_type {
            Type::ADT(fqtn, _) => format!("_{}", fqtn.name),
            _ => String::new(),
        };
        let name = format!("runtime/vec_elem_dec_{suffix}{type_suffix}");

        // Check if this function was already built (e.g., by a previous module).
        if let Some(cranelift_module::FuncOrDataId::Func(existing_id)) =
            self.module.get_name(&name)
        {
            return Ok(existing_id);
        }

        let dealloc_id = self.ctx.dealloc_func_id;

        // Build drop glue for ADT element types with heap fields.
        let drop_glue_id = self.build_adt_drop_glue_fn(elem_type, dealloc_id, span)?;

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare elem dec fn: {e}"),
                location: ErrorLocation::from_span(span),
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
            drop_glue_id,
            guarded,
        );

        builder.ins().return_(&[val]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define elem dec fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(func_id)
    }

    /// Build a standalone ADT drop glue function: `(ptr: i64) -> ()`.
    ///
    /// For each data constructor, loads each heap-typed field and dec's it.
    /// Returns None if the type is not an ADT or has no heap-typed fields.
    fn build_adt_drop_glue_fn(
        &mut self,
        ty: &Type,
        dealloc_id: cranelift_module::FuncId,
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let fqtn = match ty {
            Type::ADT(fqtn, _) => fqtn.clone(),
            _ => return Ok(None),
        };

        let type_def = match self.ctx.lookup_type_def(&fqtn) {
            Some(td) => td,
            None => return Ok(None),
        };

        let concrete_args = match ty {
            Type::ADT(_, args) => args.clone(),
            _ => return Ok(None),
        };

        // Build substitution from Var ids to concrete types.
        let mut unique_var_ids: Vec<cranelisp_types::TypeId> = Vec::new();
        for c in &type_def.constructors {
            for field in &c.fields {
                collect_var_ids_from_type(&field.ty, &mut unique_var_ids);
            }
        }
        let subst: std::collections::HashMap<cranelisp_types::TypeId, Type> = unique_var_ids
            .iter()
            .zip(concrete_args.iter())
            .map(|(&id, arg)| (id, arg.clone()))
            .collect();

        // Collect data constructors with fields.
        let data_ctors: Vec<_> = type_def
            .constructors
            .iter()
            .filter(|c| !c.fields.is_empty())
            .collect();

        if data_ctors.is_empty() {
            return Ok(None);
        }

        // Check if any data constructor has heap-typed fields.
        let has_heap_fields = data_ctors.iter().any(|ctor| {
            ctor.fields.iter().any(|f| {
                let resolved = substitute_type_inline(&f.ty, &subst);
                matches!(
                    HeapCategory::classify(&resolved, Some(self.ctx.symbol_tables)),
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed
                )
            })
        });

        if !has_heap_fields {
            return Ok(None);
        }

        // Build the drop glue function.
        let glue_name = format!("runtime/drop_glue_{}", fqtn.name);

        // Check if this drop glue was already built (e.g., by a previous module).
        if let Some(cranelift_module::FuncOrDataId::Func(existing_id)) =
            self.module.get_name(&glue_name)
        {
            return Ok(Some(existing_id));
        }

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // ptr

        let glue_func_id = self
            .module
            .declare_function(&glue_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare drop glue fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let mut ctx = self.module.make_context();
        let mut func_ctx = FunctionBuilderContext::new();
        ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let adt_val = builder.block_params(entry)[0];

        // Drop glue is only called from the free path of emit_rc_dec_guarded,
        // so the value is guaranteed to be a heap pointer (not a bare tag).
        // No mixed guard needed here.

        if data_ctors.len() == 1 {
            let ctor = data_ctors[0];
            self.emit_standalone_field_decs(
                &mut builder,
                adt_val,
                ctor,
                &subst,
                dealloc_id,
                span,
            )?;
        } else {
            // Multiple data constructors: load tag, branch to correct handler.
            let heap_tag = heap::heap_load(&mut builder, adt_val, HeapAdt::TAG_OFFSET);
            let done_block = builder.create_block();

            // Collect data_ctors into owned Vec so `self` isn't borrowed across
            // the iteration body (we need `&mut self` inside the loop to call
            // `emit_standalone_field_decs`).
            let data_ctors_owned: Vec<cranelisp_types::ConstructorInfo> =
                data_ctors.iter().map(|c| (*c).clone()).collect();

            for (idx, ctor) in data_ctors_owned.iter().enumerate() {
                let ctor_block = builder.create_block();
                let next_block = if idx + 1 < data_ctors_owned.len() {
                    builder.create_block()
                } else {
                    done_block
                };

                let tag_val = builder.ins().iconst(types::I64, ctor.tag as i64);
                let cmp = builder.ins().icmp(IntCC::Equal, heap_tag, tag_val);
                builder.ins().brif(cmp, ctor_block, &[], next_block, &[]);

                builder.switch_to_block(ctor_block);
                builder.seal_block(ctor_block);

                self.emit_standalone_field_decs(
                    &mut builder,
                    adt_val,
                    ctor,
                    &subst,
                    dealloc_id,
                    span,
                )?;
                builder.ins().jump(done_block, &[]);

                if idx + 1 < data_ctors_owned.len() {
                    builder.switch_to_block(next_block);
                    builder.seal_block(next_block);
                }
            }

            builder.switch_to_block(done_block);
            builder.seal_block(done_block);
        }

        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(glue_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define drop glue fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(Some(glue_func_id))
    }

    /// Emit rc_dec for each heap-typed field of a constructor (standalone).
    ///
    /// Unlike `emit_field_decs` on FnCompiler, this operates on a bare
    /// FunctionBuilder without the FnCompiler's scope state. Takes `&mut self`
    /// so it can build per-element dec functions when a field is a Vec —
    /// Vec fields cannot use the generic `emit_rc_dec → dealloc` path because
    /// that leaks the elements and the data buffer.
    ///
    /// For nested ADT fields (non-Vec) we build the nested ADT's drop glue
    /// and pass it to `emit_rc_dec_guarded` so heap sub-fields release at
    /// rc=0. This mirrors `emit_field_decs`'s recursive handling in
    /// `compiler/mod.rs`.
    fn emit_standalone_field_decs(
        &mut self,
        builder: &mut FunctionBuilder,
        adt_val: Value,
        ctor: &cranelisp_types::ConstructorInfo,
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc_id: cranelift_module::FuncId,
        span: Span,
    ) -> Result<(), CranelispError> {
        let vec_drop_id = self.ctx.vec_drop_func_id;
        for (i, field) in ctor.fields.iter().enumerate() {
            let resolved_ty = substitute_type_inline(&field.ty, subst);
            let category = HeapCategory::classify(&resolved_ty, Some(self.ctx.symbol_tables));
            match category {
                HeapCategory::AlwaysHeap => {
                    let field_val =
                        heap::heap_load(builder, adt_val, HeapAdt::field_offset(i));

                    // Vec-typed fields must route through vec_drop, not dealloc,
                    // so element RCs and the data buffer are released.
                    if let Some(elem_ty) = vec_element_type(&resolved_ty) {
                        let vdrop = vec_drop_id.ok_or_else(|| {
                            CranelispError::CodegenError {
                                message: "runtime/vec_drop not declared for drop-glue Vec field".into(),
                                location: ErrorLocation::from_span(span),
                            }
                        })?;
                        // Build per-element dec fn (needs &mut self; outer
                        // `builder` is a separate FunctionBuilder owned by
                        // the drop-glue function ctx — safe to nest).
                        let elem_dec_fn_ptr = self
                            .resolve_elem_dec_fn_ptr_into(&Some(elem_ty.clone()), builder, span)?;
                        emit_vec_rc_dec_with_drop(
                            builder,
                            self.module,
                            field_val,
                            vdrop,
                            elem_dec_fn_ptr,
                        );
                    } else if matches!(resolved_ty, Type::ADT(_, _)) {
                        // Nested ADT fields (non-Vec) need their own drop glue
                        // so that the nested ADT's heap sub-fields are released
                        // when the nested ADT reaches rc=0. Without this, a
                        // Grid-of-Wrapper-of-String would only run Wrapper's
                        // dealloc and leak the inner String's RC.
                        let nested_glue_id = self
                            .build_adt_drop_glue_fn(&resolved_ty, dealloc_id, span)?;
                        heap::emit_rc_dec_guarded(
                            builder,
                            self.module,
                            field_val,
                            dealloc_id,
                            nested_glue_id,
                            false,
                        );
                    } else {
                        heap::emit_rc_dec(builder, self.module, field_val, dealloc_id, None);
                    }
                }
                HeapCategory::Mixed => {
                    let field_val =
                        heap::heap_load(builder, adt_val, HeapAdt::field_offset(i));
                    // Mixed ADT fields (nullary + data constructors) need drop
                    // glue when the data variants carry heap sub-fields. The
                    // guard in emit_rc_dec_guarded skips bare nullary tags;
                    // the drop glue runs only on heap values at rc=0.
                    let nested_glue_id = if matches!(resolved_ty, Type::ADT(_, _)) {
                        self.build_adt_drop_glue_fn(&resolved_ty, dealloc_id, span)?
                    } else {
                        None
                    };
                    heap::emit_rc_dec_guarded(
                        builder,
                        self.module,
                        field_val,
                        dealloc_id,
                        nested_glue_id,
                        true,
                    );
                }
                HeapCategory::NeverHeap => {}
            }
        }
        Ok(())
    }

    /// Resolve or generate a per-element-type dec function pointer into a
    /// specific builder (for use inside nested drop-glue function codegen).
    ///
    /// Unlike `resolve_elem_dec_fn_ptr` which emits into `self.builder`,
    /// this takes an explicit `&mut FunctionBuilder` so it can be used from
    /// `emit_standalone_field_decs` (which is building a different function).
    fn resolve_elem_dec_fn_ptr_into(
        &mut self,
        elem_type: &Option<Type>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            return Ok(builder.ins().iconst(types::I64, 0));
        };

        let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
        match category {
            HeapCategory::NeverHeap => Ok(builder.ins().iconst(types::I64, 0)),
            HeapCategory::AlwaysHeap => {
                let func_id = self.build_elem_dec_fn(false, ty, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                Ok(builder.ins().func_addr(types::I64, func_ref))
            }
            HeapCategory::Mixed => {
                let func_id = self.build_elem_dec_fn(true, ty, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                Ok(builder.ins().func_addr(types::I64, func_ref))
            }
        }
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
                location: ErrorLocation::from_span(span),
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
                location: ErrorLocation::from_span(span),
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
                location: ErrorLocation::from_span(span),
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

/// If `ty` is a `Vec T`, return the element type `T`.
///
/// Vec is a built-in heap type with its own struct layout (len/cap/data_ptr)
/// and a dedicated `runtime/vec_drop` teardown path. When a Vec value reaches
/// rc=0, it cannot be freed via the generic `dealloc(ptr)` — that would leak
/// the elements and the data buffer. Callers must detect Vec-typed values and
/// route through `emit_vec_aware_rc_dec` instead.
pub(crate) fn vec_element_type(ty: &Type) -> Option<&Type> {
    if let Type::ADT(fqtn, args) = ty
        && fqtn.name.as_ref() == "Vec"
        && args.len() == 1
    {
        return Some(&args[0]);
    }
    None
}

/// Emit an RC dec on a Vec value that properly tears down the Vec on rc=0.
///
/// Unlike `heap::emit_rc_dec` (which calls `runtime/dealloc` on the Vec struct,
/// leaking the data buffer and element refs), this emits:
///
///     old_rc = atomic_rmw(Sub, vec + RC_OFFSET, 1, Release)
///     if old_rc == 1:
///         fence(Acquire)
///         vec_drop(vec, elem_dec_fn_ptr)   // dec each element + free data buffer + dealloc
///
/// `elem_dec_fn_ptr` is an i64 Value — either `func_addr` of a per-element
/// dec function (for AlwaysHeap/Mixed elements) or iconst(0) (for NeverHeap).
pub(crate) fn emit_vec_rc_dec_with_drop<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    vec_drop_func_id: cranelift_module::FuncId,
    elem_dec_fn_ptr: Value,
) {
    use cranelift_codegen::ir::AtomicRmwOp;

    let cont_block = builder.create_block();

    // Atomic dec RC.
    let rc_addr = builder
        .ins()
        .iadd_imm(vec_val, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = builder.ins().atomic_rmw(
        types::I64,
        MemFlags::trusted(),
        AtomicRmwOp::Sub,
        rc_addr,
        one,
    );

    // Branch: if old_rc == 1 (last reference), call vec_drop.
    let cmp = builder.ins().icmp(IntCC::Equal, old_rc, one);
    let drop_block = builder.create_block();
    builder
        .ins()
        .brif(cmp, drop_block, &[], cont_block, &[]);

    // Drop path: Acquire fence, then vec_drop(vec, elem_dec_fn_ptr).
    builder.switch_to_block(drop_block);
    builder.seal_block(drop_block);
    builder.ins().fence();

    let vec_drop_ref = module.declare_func_in_func(vec_drop_func_id, builder.func);
    builder.ins().call(vec_drop_ref, &[vec_val, elem_dec_fn_ptr]);

    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

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
fn emit_vec_bounds_panic<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
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
            location: ErrorLocation::from_span(span),
        })?;
    let mut desc = cranelift_module::DataDescription::new();
    desc.define(msg.to_vec().into_boxed_slice());
    module
        .define_data(data_id, &desc)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define panic data: {e}"),
            location: ErrorLocation::from_span(span),
        })?;

    let gv = module.declare_data_in_func(data_id, builder.func);
    let msg_ptr = builder.ins().global_value(types::I64, gv);
    let msg_len = builder.ins().iconst(types::I64, msg.len() as i64);

    let panic_ref = module.declare_func_in_func(panic_func_id, builder.func);
    builder.ins().call(panic_ref, &[msg_ptr, msg_len]);

    // runtime_panic sets a thread-local error flag and returns.
    // Return a dummy 0 value — the caller checks take_runtime_error().
    let dummy = builder.ins().iconst(types::I64, 0);
    builder.ins().return_(&[dummy]);

    Ok(())
}
