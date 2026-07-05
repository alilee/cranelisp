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
    ConcreteType, CranelispError, HeapHeader, MonoExpr, Span, Type,
};

use crate::heap::{self, HeapAdt, HeapCategory, HeapVec, RcAtomicity, NULLARY_THRESHOLD_I64};

use super::control_flow::emit_extern_call_in_wrapper;
use super::{collect_var_ids_from_type, signature_heap_category, substitute_type_inline, CtorMeta, FnCompiler};

/// Bundled operands for [`emit_vec_set_cow_core`] (argument-count budget — the
/// successor of the former `VecSetElem` bundle after the COW core was
/// builder-parameterized for the §12.7 wrapper emission).
///
/// The new-element consuming inc is the CALLER's decision (static sites gate on
/// `element_consuming_inc`; wrapper params arrive owned and transfer) — it is
/// NOT carried here and NOT emitted by the core.
pub(crate) struct VecSetCow {
    pub vec_val: Value,
    pub idx_val: Value,
    pub new_val: Value,
    /// Per-element-type RC inc fn pointer for the runtime copy helper's
    /// retained-element incs (iconst 0 for NeverHeap).
    pub inc_fn_ptr: Value,
    /// The OLD element's heap category (drives the mutate-in-place dec).
    pub old_elem_category: Option<HeapCategory>,
    pub dealloc_id: cranelift_module::FuncId,
    /// The consumed-source RC polarity (§13.3 Ruling 2) — whether the copy
    /// branch must release an owned reference to the source Vec.
    pub source_ownership: SourceOwnership,
}

/// Consumed-source RC polarity for the shared COW cores
/// (`design/backend/ownership-codegen.md` §13.3 Ruling 2).
///
/// A COW op has three runtime branches: **mutate** (rc==1, `vec-set`) /
/// **grow** (rc==1, `vec-push`) return the *same* Vec pointer, so the consumed
/// source reference transfers into the returned value — nothing to release; the
/// **copy** branch (rc>1) allocates a *new* Vec and returns it, so any owned
/// reference to the source that the op consumed becomes unreachable at the call
/// and MUST be released there or it leaks (FIXME 0474).
///
/// This is a *contract* (Principle 18), not a spot dec: every call site states
/// its truth explicitly, so a new call-site shape cannot silently re-open the
/// leak. It is a leak-only class — the polarity errs on the retain side, never
/// a UAF/double-free.
pub(crate) enum SourceOwnership {
    /// The caller handed the core an owned reference the op consumes — wrapper
    /// and curry bodies whose params arrive owned under the consuming-closure
    /// protocol. The copy branch rc-checked-decs the source via `vec_drop`
    /// (freeing struct + data buffer + retained-element refs only at rc==1).
    /// Carries the teardown materials the release needs.
    Owned {
        vec_drop_func_id: cranelift_module::FuncId,
        elem_dec_fn_ptr: Value,
    },
    /// The source reference is owned elsewhere (a live scope binding / borrow):
    /// the caller's arg compilation emitted no consuming inc, so the copy branch
    /// releases nothing (scope cleanup dec's the binding). Static in-place COW
    /// sites (`compile_vec_set` / `compile_vec_push` last-use arm) pass this.
    Borrowed,
}

/// Emit the copy-branch consumed-source release for a COW core (§13.3 Ruling 2).
/// No-op for `Borrowed`; rc-checked `vec_drop` for `Owned`. Called AFTER the
/// copy extern (which reads + retains the shared source elements), so a
/// last-reference source teardown cannot free elements the new copy still holds.
fn release_consumed_source<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    source_ownership: &SourceOwnership,
) {
    if let SourceOwnership::Owned {
        vec_drop_func_id,
        elem_dec_fn_ptr,
    } = source_ownership
    {
        emit_vec_rc_dec_with_drop(builder, module, vec_val, *vec_drop_func_id, *elem_dec_fn_ptr);
    }
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Compile a Vec literal: `[e1 e2 e3]` → allocate Vec, store elements.
    pub(crate) fn compile_vec_lit(
        &mut self,
        elements: &[MonoExpr],
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
        args: &[MonoExpr],
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
                    &args[0], &args[2], arg_vals, span,
                )?;
                Ok(Some(result))
            }
            "vec-push" if args.len() == 2 => {
                let result = self.compile_vec_push(
                    &args[0], &args[1], arg_vals, span,
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
    /// Delegates to the shared [`emit_vec_get_core`] (single source with the
    /// §12.7 fn-as-value wrapper emission — Principle 7); this method computes
    /// the element heap category from the Vec expression's concrete type.
    fn compile_vec_get(
        &mut self,
        vec_expr: &MonoExpr,
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
        let elem_category = self
            .vec_elem_type(vec_expr)
            .map(|t| signature_heap_category(&t, Some(self.ctx.symbol_tables)));
        // §3.3 in-frame projection elision
        // (`design/backend/ownership-codegen.md` §3.3): elide the heap-element inc
        // when the CONSUMER of this exact `vec-get` requested it — the moded arg
        // path (`compile_consuming_arg_list_moded`) sets `elide_vecget_span` to
        // this node's span iff the read is a projection (site fact `provenance`)
        // being passed DIRECTLY into a `Borrowed` parameter. That is the sole
        // provably-safe elision: the borrowed element is consumed in-place by the
        // callee's borrow and never escapes the enclosing expression nor outlives
        // the root's fork-join-guaranteed liveness (the F1 machinery-tax collapse).
        // `None` (analysis off, or any read the consumer did not request) ⇒ inc
        // verbatim — byte-identical-off (§2.2).
        let elide_elem_inc = self.elide_vecget_span == Some(span);
        emit_vec_get_core(
            &mut self.builder,
            self.module,
            panic_id,
            elem_category,
            vec_val,
            idx_val,
            span,
            elide_elem_inc,
        )
    }

    /// Compile `vec-set`: COW inline + extern fallback.
    ///
    /// arg_vals: [vec_val, idx_val, new_val]
    ///
    /// DEF-3 (FIXME 0417 — symmetric with `vec-push` / DEF-2): the new element
    /// follows the same consuming-Var rule as `vec-push` — the Vec gains a
    /// reference iff the element is a heap-typed **Var** (still owned by the
    /// enclosing scope, which dec's it at scope exit). A **temporary** element
    /// transfers its rc=1 reference into the Vec and MUST NOT be inc'd.
    ///
    /// The consuming inc is emitted **up-front in codegen** (gated by the shared
    /// `element_consuming_inc` predicate), exactly as `compile_vec_push` does —
    /// `vec_set_copy` does NOT inc the new `val` (it inc's only retained
    /// copied-over elements). This is the single division of labour: codegen
    /// owns the new-element consuming inc, the runtime owns the retained-element
    /// incs. (Prior to FIXME 0417 the COW path gated the inc here while the copy
    /// path relied on the runtime's unconditional inc + a codegen compensation
    /// dec — two opposite labour splits for one operation, now unified.)
    fn compile_vec_set(
        &mut self,
        vec_expr: &MonoExpr,
        elem_arg: &MonoExpr,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_val = arg_vals[0];
        let idx_val = arg_vals[1];
        let new_val = arg_vals[2];

        let elem_type = self.vec_elem_type(vec_expr);
        let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;

        // Consuming inc for the new element, emitted up-front (mirrors
        // compile_vec_push). A heap-typed Var element forwarded into vec-set
        // (e.g. `c` in `(vec-set (cells-of g) idx c)`) is still owned by its
        // enclosing scope, which dec's it at scope exit; the Vec also stores a
        // reference. Without a caller-side inc the two race against the SAME
        // single reference. A temporary element transfers its rc=1 reference
        // into the Vec — no inc. Gated by the shared `element_consuming_inc`
        // decision (Principle 7), identical to vec-push (DEF-2).
        if let Some(elem_ty) = &elem_type {
            let category = signature_heap_category(elem_ty, Some(self.ctx.symbol_tables));
            match element_consuming_inc(elem_arg, category) {
                Some(HeapCategory::AlwaysHeap) => {
                    heap::emit_rc_inc(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::Mixed) => {
                    emit_guarded_rc_inc(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::NeverHeap) | None => {}
            }
        }

        // Check if vec is at last use (compile-time).
        let is_last = self.is_vec_last_use(vec_expr);

        if is_last {
            // Runtime COW: check rc == 1. Shared core with the §12.7 wrapper
            // emission (Principle 7).
            let old_elem_category = elem_type
                .as_ref()
                .map(|t| signature_heap_category(t, Some(self.ctx.symbol_tables)));
            emit_vec_set_cow_core(
                &mut self.builder,
                self.module,
                VecSetCow {
                    vec_val,
                    idx_val,
                    new_val,
                    inc_fn_ptr,
                    old_elem_category,
                    dealloc_id: self.ctx.dealloc_func_id,
                    // Static in-place site: the Vec arg was compiled by
                    // `compile_arg_list` (no consuming inc), so this reference
                    // is owned by the live scope binding (or is a transferring
                    // temporary) — the scope dec's it. Copy branch releases
                    // nothing (§13.3 Ruling 2, static-site polarity).
                    source_ownership: SourceOwnership::Borrowed,
                },
                span,
            )
        } else {
            // Copy path (non-last-use Vec): call vec-set-copy extern. The runtime
            // inc's only the retained copied-over elements; the new `val`'s
            // consuming inc was already emitted up-front above.
            self.emit_extern_call(
                "vec-set-copy", &[vec_val, idx_val, new_val, inc_fn_ptr], span,
            )
        }
    }

    /// Compile `vec-push`: COW inline + extern fallback.
    ///
    /// arg_vals: [vec_val, new_val]
    fn compile_vec_push(
        &mut self,
        vec_expr: &MonoExpr,
        elem_arg: &MonoExpr,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_val = arg_vals[0];
        let new_val = arg_vals[1];

        let elem_type = self.vec_elem_type(vec_expr);
        let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;

        // DEF-2: a heap-typed Var element forwarded into vec-push (e.g. the `x`
        // parameter of `(defn push2 [v x] (vec-push v x))`) is still owned by its
        // enclosing scope, which dec's it at scope exit. vec-push stores `new_val`
        // into the Vec WITHOUT inc'ing on the fast/grow/copy paths (the Vec takes
        // ownership of one reference). Without a caller-side consuming inc here, the
        // Vec's stored reference and the scope's dec race against the SAME single
        // reference — under-counting the element by 1 (COW then mutates an aliased
        // backing → over-count on read-back). Mirrors compile_consuming_arg_list
        // (Decision 24 §3.1): inc heap-typed Var args, transfer temporaries.
        if let Some(elem_ty) = &elem_type {
            let category = signature_heap_category(elem_ty, Some(self.ctx.symbol_tables));
            match element_consuming_inc(elem_arg, category) {
                Some(HeapCategory::AlwaysHeap) => {
                    heap::emit_rc_inc(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::Mixed) => {
                    emit_guarded_rc_inc(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::NeverHeap) | None => {}
            }
        }

        let is_last = self.is_vec_last_use(vec_expr);

        if is_last {
            // Shared core with the §12.7 wrapper emission (Principle 7).
            emit_vec_push_cow_core(
                &mut self.builder,
                self.module,
                vec_val,
                new_val,
                inc_fn_ptr,
                // Static in-place site: source owned by scope (or transferring
                // temporary) — copy branch releases nothing (§13.3 Ruling 2).
                SourceOwnership::Borrowed,
                span,
            )
        } else {
            // Copy path: call vec-push-copy extern.
            self.emit_extern_call("vec-push-copy", &[vec_val, new_val, inc_fn_ptr], span)
        }
    }

    // --- Helpers ---

    /// Extract the element type from a Vec expression's concrete type.
    ///
    /// `pub(crate)`: also read by `control_flow::fn_as_value::compile_auto_curry`
    /// to recover the element type from the applied Vec argument on the
    /// curried-vec-query path (§12.7).
    pub(crate) fn vec_elem_type(&self, vec_expr: &MonoExpr) -> Option<Type> {
        if let ConcreteType::ADT(fqtn, args) = vec_expr.ty()
            && fqtn.name.as_ref() == "Vec" && args.len() == 1 {
                return Some(args[0].to_type());
            }
        None
    }

    /// Check if a Vec expression is at its last use (for COW eligibility).
    fn is_vec_last_use(&self, vec_expr: &MonoExpr) -> bool {
        if let MonoExpr::Var { name, span, .. } = vec_expr {
            self.is_last_use(name, *span)
        } else {
            // Temporary expression: ownership transfers, treat as unique.
            true
        }
    }

    /// Release a temporary Vec expression's reference after an inline Vec op
    /// (vec-get / vec-len) consumed it. Named variables are cleaned up at scope
    /// exit; temporaries have no scope entry and would leak.
    ///
    /// The release is **rc-checked** (`emit_vec_rc_dec_with_drop`), NOT an
    /// unconditional `vec_drop`. A temporary Vec expression is not always the
    /// sole owner: when it is a borrowed ADT field — e.g. `(vec-get (gcells g) 0)`
    /// where `gcells` returns the inner Vec still owned by the live Grid `g` —
    /// the Vec's rc is > 1, and an unconditional `vec_drop` would free the data
    /// buffer + struct out from under the still-reachable Grid, corrupting the
    /// heap on the next write through the now-dangling pointer (the S97
    /// nested-ADT-wrapping-Vec double-use soundness defect; ring2-rc.md §5.5).
    /// The rc-checked dec frees only when this was the last reference (rc==1) —
    /// byte-identical to the old behaviour for a genuinely fresh rc==1 temporary,
    /// and correct (no free) for a shared borrowed-field temporary.
    fn emit_vec_drop_if_temporary(
        &mut self,
        vec_expr: &MonoExpr,
        vec_val: Value,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Named variables are handled by scope cleanup — skip.
        if matches!(vec_expr, MonoExpr::Var { .. }) {
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

        emit_vec_rc_dec_with_drop(
            &mut self.builder,
            self.module,
            vec_val,
            vec_drop_id,
            dec_fn_ptr,
        );

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

        let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
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

        let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
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
        atomicity: RcAtomicity,
    ) -> Result<(), CranelispError> {
        let vec_drop_id = self.ctx.vec_drop_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/vec_drop not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            }
        })?;

        // Build per-element dec fn (or null for NeverHeap elements).
        let elem_dec_fn_ptr = self.resolve_elem_dec_fn_ptr(&Some(elem_type.clone()), span)?;

        // B3.3 (§5.2): the Vec-header dec goes non-atomic on a Confined vec
        // cell (the one shared vec-inventory item that IS per-site-emitted).
        emit_vec_rc_dec_with_drop_atomicity(
            &mut self.builder,
            self.module,
            vec_val,
            vec_drop_id,
            elem_dec_fn_ptr,
            atomicity,
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
            heap::emit_rc_inc(&mut builder, self.module, val);
            builder.ins().jump(ret_block, &[]);

            builder.switch_to_block(ret_block);
            builder.seal_block(ret_block);
        } else {
            heap::emit_rc_inc(&mut builder, self.module, val);
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

        // Reconstruct constructor metadata (S70 ctor-as-Def).
        let all_ctors = self.ctx.constructor_metas(&type_def);

        // Build substitution from Var ids to concrete types.
        let mut unique_var_ids: Vec<cranelisp_types::TypeId> = Vec::new();
        for c in &all_ctors {
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
        let data_ctors: Vec<CtorMeta> = all_ctors
            .into_iter()
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
                    signature_heap_category(&resolved, Some(self.ctx.symbol_tables)),
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
            let ctor = &data_ctors[0];
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

            // `data_ctors` is already owned (Vec<CtorMeta>); clone for the loop
            // so `self` isn't borrowed across the body (we need `&mut self`
            // inside the loop to call `emit_standalone_field_decs`).
            let data_ctors_owned: Vec<CtorMeta> = data_ctors.clone();

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
        ctor: &CtorMeta,
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc_id: cranelift_module::FuncId,
        span: Span,
    ) -> Result<(), CranelispError> {
        let vec_drop_id = self.ctx.vec_drop_func_id;
        for (i, field) in ctor.fields.iter().enumerate() {
            let resolved_ty = substitute_type_inline(&field.ty, subst);
            let category = signature_heap_category(&resolved_ty, Some(self.ctx.symbol_tables));
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
    /// Build the `SourceOwnership::Owned` release descriptor for a COW core
    /// emitted into a wrapper/curry body (§13.3 Ruling 2): the source Vec's
    /// teardown func id + its per-element dec fn ptr. The op consumes an owned
    /// reference here (consuming-closure protocol), so the copy branch releases
    /// it via `vec_drop` (rc-checked). Mirrors the vec-get arm's teardown setup.
    fn owned_source_release(
        &mut self,
        elem_type: &Option<Type>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<SourceOwnership, CranelispError> {
        let vec_drop_func_id = self.ctx.vec_drop_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/vec_drop not declared".into(),
                location: ErrorLocation::from_span(span),
            }
        })?;
        let elem_dec_fn_ptr = self.resolve_elem_dec_fn_ptr_into(elem_type, builder, span)?;
        Ok(SourceOwnership::Owned {
            vec_drop_func_id,
            elem_dec_fn_ptr,
        })
    }

    fn resolve_elem_dec_fn_ptr_into(
        &mut self,
        elem_type: &Option<Type>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            return Ok(builder.ins().iconst(types::I64, 0));
        };

        let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
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

    /// Resolve or generate a per-element-type inc function pointer into a
    /// specific builder (for wrapper-body emission — the mirror of
    /// `resolve_elem_dec_fn_ptr_into`, and the `_into` sibling of
    /// `resolve_elem_inc_fn_ptr`, which emits into `self.builder`).
    fn resolve_elem_inc_fn_ptr_into(
        &mut self,
        elem_type: &Option<Type>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            return Ok(builder.ins().iconst(types::I64, 0));
        };

        let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
        match category {
            HeapCategory::NeverHeap => Ok(builder.ins().iconst(types::I64, 0)),
            HeapCategory::AlwaysHeap => {
                let func_id = self.build_elem_inc_fn(false, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                Ok(builder.ins().func_addr(types::I64, func_ref))
            }
            HeapCategory::Mixed => {
                let func_id = self.build_elem_inc_fn(true, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                Ok(builder.ins().func_addr(types::I64, func_ref))
            }
        }
    }

    /// Inline-emit a vec-query op (`vec-get` / `vec-set` / `vec-push`) into a
    /// GENERATED WRAPPER body (fn-as-value / auto-curry / trait-method-value —
    /// `control_flow::fn_as_value`). These primitives-table entries are
    /// `PrimitiveBody::Inline` — inline-dispatched with **no GOT slot** by
    /// construction (S102 FIXME 0476: no extern body can exist because a single
    /// monomorphic body cannot know the element's heap category), so the wrapper
    /// MUST synthesize this inline emission rather than dispatch through a slot
    /// (`design/backend/ownership-codegen.md` §12.7 — the S100 SIGSEGV defect).
    ///
    /// RC polarity: every wrapper param arrives OWNED (consuming closure
    /// protocol), so the emission takes the owned-temporary polarity uniformly:
    ///
    /// - `vec-get` — bounds check + element load + element inc (per element
    ///   heap category), then a vec-aware rc-checked release of the consumed
    ///   Vec (the temporary branch of `emit_vec_drop_if_temporary`).
    /// - `vec-set` / `vec-push` — the element's reference TRANSFERS into the
    ///   Vec with NO consuming inc (the temporary branch of
    ///   `element_consuming_inc`), and the Vec is trivially at last use, so
    ///   the COW rc==1 path applies (the shared cores).
    ///
    /// `elem_type` is the per-site element type plumbed from the value-use
    /// site's concrete `Fn` type (or from the applied Vec argument on the
    /// auto-curry path). `None` degrades to the no-elem-RC-ops shape — the
    /// same safe default as `resolve_elem_inc_fn_ptr`'s unknown-type arm.
    pub(crate) fn emit_vec_query_into(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &str,
        params: &[Value],
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let elem_category = elem_type
            .as_ref()
            .map(|t| signature_heap_category(t, Some(self.ctx.symbol_tables)));
        match (name, params.len()) {
            ("vec-get", 2) => {
                let panic_id = self.ctx.panic_func_id.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "runtime/panic not declared".into(),
                        location: ErrorLocation::from_span(span),
                    }
                })?;
                let vec_drop_id = self.ctx.vec_drop_func_id.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "runtime/vec_drop not declared".into(),
                        location: ErrorLocation::from_span(span),
                    }
                })?;
                let dec_fn_ptr =
                    self.resolve_elem_dec_fn_ptr_into(elem_type, builder, span)?;
                let elem = emit_vec_get_core(
                    builder,
                    self.module,
                    panic_id,
                    elem_category,
                    params[0],
                    params[1],
                    span,
                    // Value-use wrapper body: the projection ALWAYS materializes
                    // (the closure protocol owes a fresh owned value), and the Vec
                    // arrives owned and is released below — never a borrowed
                    // projection. So the element inc is never elided here (§3.3).
                    false,
                )?;
                // Release the consumed (owned) Vec — rc-checked, and AFTER the
                // element inc inside the core, so the element survives a
                // last-reference Vec teardown.
                emit_vec_rc_dec_with_drop(
                    builder,
                    self.module,
                    params[0],
                    vec_drop_id,
                    dec_fn_ptr,
                );
                Ok(elem)
            }
            ("vec-set", 3) => {
                let inc_fn_ptr =
                    self.resolve_elem_inc_fn_ptr_into(elem_type, builder, span)?;
                // Wrapper / curry body: params arrive OWNED (consuming-closure
                // protocol), so the copy branch must release the source Vec's
                // owned reference (§13.3 Ruling 2 — the FIXME-0474 cure). The
                // vec-get arm's release above is the precedent.
                let source_ownership =
                    self.owned_source_release(elem_type, builder, span)?;
                emit_vec_set_cow_core(
                    builder,
                    self.module,
                    VecSetCow {
                        vec_val: params[0],
                        idx_val: params[1],
                        new_val: params[2],
                        inc_fn_ptr,
                        old_elem_category: elem_category,
                        dealloc_id: self.ctx.dealloc_func_id,
                        source_ownership,
                    },
                    span,
                )
            }
            ("vec-push", 2) => {
                let inc_fn_ptr =
                    self.resolve_elem_inc_fn_ptr_into(elem_type, builder, span)?;
                // Wrapper / curry body: params arrive owned — release the source
                // on the copy branch (§13.3 Ruling 2).
                let source_ownership =
                    self.owned_source_release(elem_type, builder, span)?;
                emit_vec_push_cow_core(
                    builder,
                    self.module,
                    params[0],
                    params[1],
                    inc_fn_ptr,
                    source_ownership,
                    span,
                )
            }
            _ => Err(CranelispError::CodegenError {
                message: format!(
                    "vec-query wrapper: unexpected op/arity {name}/{}",
                    params.len()
                ),
                location: ErrorLocation::from_span(span),
            }),
        }
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

/// Shared emission core for `vec-get`: bounds check (trap via `runtime/panic`)
/// + element load + element RC inc per `elem_category`.
///
/// Builder-parameterized (the `emit_adt_construct_into` precedent) so ONE body
/// serves both the statically-resolved inline site (`compile_vec_get`, over
/// `self.builder`) and the §12.7 fn-as-value / auto-curry wrapper bodies
/// (`emit_vec_query_into`), which build in a separate Cranelift context.
/// Consuming the Vec (the temporary/owned release) is the CALLER's decision —
/// not emitted here.
#[allow(clippy::too_many_arguments)] // +1 for the §3.3 elide_elem_inc gate
pub(crate) fn emit_vec_get_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic_id: cranelift_module::FuncId,
    elem_category: Option<HeapCategory>,
    vec_val: Value,
    idx_val: Value,
    span: Span,
    // §3.3 in-frame projection elision
    // (`design/backend/ownership-codegen.md` §3.3): when `true` the heap-element
    // materialization inc is SKIPPED — the read is a borrowed projection rooted
    // in a live root (the enclosing `Apply`'s `provenance` fact). `false` ⇒ the
    // inc is emitted verbatim (byte-identical-off, and the value-use wrapper path
    // which always materializes).
    elide_elem_inc: bool,
) -> Result<Value, CranelispError> {
    // Load len from Vec.
    let len = heap::heap_load(builder, vec_val, HeapVec::LEN_OFFSET);

    // Bounds check: idx < 0 || idx >= len → panic.
    let zero = builder.ins().iconst(types::I64, 0);
    let neg_check = builder.ins().icmp(IntCC::SignedLessThan, idx_val, zero);
    let bounds_check = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, idx_val, len);
    let out_of_bounds = builder.ins().bor(neg_check, bounds_check);

    let ok_block = builder.create_block();
    let panic_block = builder.create_block();

    builder
        .ins()
        .brif(out_of_bounds, panic_block, &[], ok_block, &[]);

    // Panic path: call runtime/panic with error message.
    builder.switch_to_block(panic_block);
    builder.seal_block(panic_block);
    emit_vec_bounds_panic(builder, module, panic_id, span)?;

    // OK path: load element.
    builder.switch_to_block(ok_block);
    builder.seal_block(ok_block);

    // Load data_ptr.
    let data_ptr = heap::heap_load(builder, vec_val, HeapVec::DATA_PTR_OFFSET);

    // Compute element address: data_ptr + idx * 8.
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_offset = builder.ins().imul(idx_val, eight);
    let elem_addr = builder.ins().iadd(data_ptr, byte_offset);

    // Load element value.
    let elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);

    // If element type is heap, emit RC inc on the loaded value — UNLESS this read
    // is a borrowed projection (§3.3): then the element is a view into the still-
    // live root and its inc is elided (the F1 machinery-tax collapse). The root's
    // owner keeps the element alive; a consuming use of the projection
    // materializes it (`borrowed_projection_root`).
    if !elide_elem_inc {
        match elem_category {
            Some(HeapCategory::AlwaysHeap) => {
                heap::emit_rc_inc(builder, module, elem);
            }
            Some(HeapCategory::Mixed) => {
                emit_guarded_rc_inc(builder, module, elem);
            }
            Some(HeapCategory::NeverHeap) | None => {}
        }
    }

    Ok(elem)
}

/// Shared emission core for the `vec-set` COW path: rc==1 → mutate-in-place
/// (dec old element, store new, return the same Vec); rc>1 → `vec-set-copy`
/// extern (the runtime inc's only the retained copied-over elements).
///
/// Builder-parameterized single source (Principle 7) for the static
/// `compile_vec_set` last-use arm and the §12.7 wrapper emission. The
/// new-element consuming inc is the CALLER's decision (static sites gate on
/// `element_consuming_inc`; wrapper params arrive owned and transfer) — both
/// sub-paths store `new_val` WITHOUT an additional inc.
pub(crate) fn emit_vec_set_cow_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    op: VecSetCow,
    span: Span,
) -> Result<Value, CranelispError> {
    let VecSetCow {
        vec_val,
        idx_val,
        new_val,
        inc_fn_ptr,
        old_elem_category,
        dealloc_id,
        source_ownership,
    } = op;

    // Load RC and check if == 1 (unique owner).
    let rc = heap::heap_load(builder, vec_val, HeapHeader::RC_OFFSET);
    let one = builder.ins().iconst(types::I64, 1);
    let is_unique = builder.ins().icmp(IntCC::Equal, rc, one);

    let mutate_block = builder.create_block();
    let copy_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    builder
        .ins()
        .brif(is_unique, mutate_block, &[], copy_block, &[]);

    // Mutate-in-place path: dec old element, store new, return same vec.
    builder.switch_to_block(mutate_block);
    builder.seal_block(mutate_block);

    // Load data_ptr and old element.
    let data_ptr = heap::heap_load(builder, vec_val, HeapVec::DATA_PTR_OFFSET);
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_off = builder.ins().imul(idx_val, eight);
    let elem_addr = builder.ins().iadd(data_ptr, byte_off);
    let old_elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);

    // Dec the old element (if heap type).
    match old_elem_category {
        Some(HeapCategory::AlwaysHeap) => {
            heap::emit_rc_dec(builder, module, old_elem, dealloc_id, None);
        }
        Some(HeapCategory::Mixed) => {
            heap::emit_rc_dec_guarded(builder, module, old_elem, dealloc_id, None, true);
        }
        Some(HeapCategory::NeverHeap) | None => {}
    }

    // Store new value (the consuming inc was the caller's decision — none here).
    builder
        .ins()
        .store(MemFlags::trusted(), new_val, elem_addr, 0);

    builder.ins().jump(merge_block, &[vec_val]);

    // Copy path: call vec-set-copy extern.
    builder.switch_to_block(copy_block);
    builder.seal_block(copy_block);
    let copy_result = emit_extern_call_in_wrapper(
        builder,
        module,
        "vec-set-copy",
        &[vec_val, idx_val, new_val, inc_fn_ptr],
        span,
    )?;
    // §13.3 Ruling 2: the copy branch returns a NEW Vec, so release the
    // consumed source's owned reference here (iff Owned). AFTER the copy extern
    // so its retained-element incs land before a last-reference source teardown.
    release_consumed_source(builder, module, vec_val, &source_ownership);
    builder.ins().jump(merge_block, &[copy_result]);

    // Merge.
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    Ok(builder.block_params(merge_block)[0])
}

/// Shared emission core for the `vec-push` COW path: rc==1 → len<cap fast
/// store / `vec-push-grow` extern; rc>1 → `vec-push-copy` extern.
///
/// Builder-parameterized single source (Principle 7) for the static
/// `compile_vec_push` last-use arm and the §12.7 wrapper emission. The
/// new-element consuming inc is the CALLER's decision — not emitted here.
pub(crate) fn emit_vec_push_cow_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    new_val: Value,
    inc_fn_ptr: Value,
    source_ownership: SourceOwnership,
    span: Span,
) -> Result<Value, CranelispError> {
    // Load RC.
    let rc = heap::heap_load(builder, vec_val, HeapHeader::RC_OFFSET);
    let one = builder.ins().iconst(types::I64, 1);
    let is_unique = builder.ins().icmp(IntCC::Equal, rc, one);

    let unique_block = builder.create_block();
    let copy_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    builder
        .ins()
        .brif(is_unique, unique_block, &[], copy_block, &[]);

    // Unique path: check if len < cap.
    builder.switch_to_block(unique_block);
    builder.seal_block(unique_block);

    let len = heap::heap_load(builder, vec_val, HeapVec::LEN_OFFSET);
    let cap = heap::heap_load(builder, vec_val, HeapVec::CAP_OFFSET);
    let has_capacity = builder.ins().icmp(IntCC::SignedLessThan, len, cap);

    let fast_block = builder.create_block();
    let grow_block = builder.create_block();

    builder
        .ins()
        .brif(has_capacity, fast_block, &[], grow_block, &[]);

    // Fast path: store at data[len], increment len.
    builder.switch_to_block(fast_block);
    builder.seal_block(fast_block);

    let data_ptr = heap::heap_load(builder, vec_val, HeapVec::DATA_PTR_OFFSET);
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_off = builder.ins().imul(len, eight);
    let elem_addr = builder.ins().iadd(data_ptr, byte_off);
    builder
        .ins()
        .store(MemFlags::trusted(), new_val, elem_addr, 0);

    // Increment len.
    let new_len = builder.ins().iadd_imm(len, 1);
    heap::heap_store(builder, new_len, vec_val, HeapVec::LEN_OFFSET);

    builder.ins().jump(merge_block, &[vec_val]);

    // Grow path: call vec-push-grow extern.
    builder.switch_to_block(grow_block);
    builder.seal_block(grow_block);
    let grow_result =
        emit_extern_call_in_wrapper(builder, module, "vec-push-grow", &[vec_val, new_val], span)?;
    builder.ins().jump(merge_block, &[grow_result]);

    // Copy path: call vec-push-copy extern.
    builder.switch_to_block(copy_block);
    builder.seal_block(copy_block);
    let copy_result = emit_extern_call_in_wrapper(
        builder,
        module,
        "vec-push-copy",
        &[vec_val, new_val, inc_fn_ptr],
        span,
    )?;
    // §13.3 Ruling 2: copy branch returns a NEW Vec — release the consumed
    // source's owned reference here (iff Owned), after the copy's retained incs.
    release_consumed_source(builder, module, vec_val, &source_ownership);
    builder.ins().jump(merge_block, &[copy_result]);

    // Merge.
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    Ok(builder.block_params(merge_block)[0])
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
    emit_vec_rc_dec_with_drop_atomicity(
        builder, module, vec_val, vec_drop_func_id, elem_dec_fn_ptr, RcAtomicity::Atomic,
    );
}

/// Vec-aware RC dec with per-site [`RcAtomicity`] (B3.3, §5.2 — the one shared
/// vec-inventory item that IS per-site-emitted, so it CAN be gated). `Atomic`
/// is byte-identical to the pre-B3.3 path; `NonAtomic` emits the plain
/// load/`isub`/store count update (sound only on a Confined vec cell). The
/// `old == 1` → `vec_drop` free path (element decs + buffer free + dealloc) is
/// unchanged in both arms.
pub(crate) fn emit_vec_rc_dec_with_drop_atomicity<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    vec_drop_func_id: cranelift_module::FuncId,
    elem_dec_fn_ptr: Value,
    atomicity: RcAtomicity,
) {
    use cranelift_codegen::ir::AtomicRmwOp;

    let cont_block = builder.create_block();

    // Dec RC — atomic_rmw, or the non-atomic plain load/isub/store arm on a
    // Confined vec cell (B3.3). The pre-decrement value stands in for the
    // atomic_rmw's returned old value in the non-atomic arm.
    let rc_addr = builder
        .ins()
        .iadd_imm(vec_val, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = if crate::heap::use_nonatomic_arm(atomicity) {
        let cur = builder.ins().load(types::I64, MemFlags::trusted(), rc_addr, 0);
        let new = builder.ins().isub(cur, one);
        builder.ins().store(MemFlags::trusted(), new, rc_addr, 0);
        cur
    } else {
        builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        )
    };

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
///
/// `module` is threaded for the S99 RC-op instrumentation gate (see
/// `heap::emit_rc_inc`); inert with the gate off.
fn emit_guarded_rc_inc<M: Module>(builder: &mut FunctionBuilder, module: &mut M, val: Value) {
    let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
    let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, val, threshold);

    let inc_block = builder.create_block();
    let cont_block = builder.create_block();

    builder.ins().brif(is_tag, cont_block, &[], inc_block, &[]);

    builder.switch_to_block(inc_block);
    builder.seal_block(inc_block);
    heap::emit_rc_inc(builder, module, val);
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

/// Decide whether a Vec-mutating primitive's new element argument needs a
/// caller-side consuming RC inc, and of which form. Shared by `vec-push`
/// (DEF-2) and `vec-set` (DEF-3) — the single source of the consuming-Var rule
/// for Vec element ownership (Principle 7).
///
/// Under the uniform consuming convention (Decision 24 / ring2-rc.md §3.1), a
/// `vec-push` / `vec-set` stores `new_val` into the Vec, transferring one
/// reference to the Vec's ownership (the Vec's drop glue dec's the element when
/// the Vec dies). For a **temporary** element expression (e.g. `(Box i)`) that
/// started at rc=1, this transfer is balanced — no caller action. But for a
/// **Var** element (e.g. the `x` parameter inside `(defn push2 [v x] (vec-push
/// v x))`, or `c` in `(vec-set (cells-of g) idx c)`) the Var is still owned by
/// its enclosing scope, which dec's it at scope exit; without a caller-side inc
/// the Vec's stored reference and the scope's dec race against the SAME single
/// reference:
///
///   - DEF-2 (`vec-push`): under-count by 1 — the heap element is freed too
///     early / read stale (a Var forwarded through a wrapper). The fix ADDS the
///     inc for the Var case.
///   - DEF-3 (`vec-set`): the prior code inc'd UNCONDITIONALLY, so a
///     **temporary** element (which transfers rc=1) got a permanent extra
///     reference the Vec never drops — a leak. The fix makes the inc
///     conditional, REMOVING it for temporaries while keeping it for Vars.
///
/// Both defects converge on the same end state: inc iff the element is a
/// heap-typed **Var**. This mirrors `compile_consuming_arg_list` exactly: inc
/// heap-typed Var arguments, leave temporaries to transfer. `NeverHeap`
/// elements (Int) and non-Var element expressions return `None` (no inc) —
/// which is why the scalar control and the direct-temporary path are unaffected.
///
/// Returns `Some(category)` (AlwaysHeap or Mixed) when the element is a heap-typed
/// Var that must be inc'd; `None` otherwise.
fn element_consuming_inc(
    elem_arg: &MonoExpr,
    elem_category: HeapCategory,
) -> Option<HeapCategory> {
    match elem_arg {
        MonoExpr::Var { .. } => match elem_category {
            HeapCategory::AlwaysHeap => Some(HeapCategory::AlwaysHeap),
            HeapCategory::Mixed => Some(HeapCategory::Mixed),
            HeapCategory::NeverHeap => None,
        },
        // Temporaries (constructor calls, function results, literals, …) start at
        // rc=1 and transfer their single reference into the Vec — no caller inc.
        _ => None,
    }
}

#[cfg(test)]
mod vec_push_rc_tests;

#[cfg(test)]
mod vec_set_rc_tests;

#[cfg(test)]
mod cow_polarity_tests;

#[cfg(test)]
mod temp_drop_rc_tests;

#[cfg(test)]
mod tests;
