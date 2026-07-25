// Dependent-binding spark thunk emission (lenient-eval.md §4.5, FIXME 0424
// limit #2).
//
// A *dependent* sparkable `let` binding — one whose RHS references an earlier
// *sparked* binding — is sparked as an IVar whose dependency references are
// forced on demand. The current lenient `let` (§4.2) creates+sparks all IVars
// in Phase 1 *before* any binding value is bound (Phase 2), so at the moment a
// dependent thunk is built its dependency `a` is not yet a `Value` in scope — it
// is an unforced IVar. The thunk therefore captures `a`'s **IVar pointer** and
// forces it on demand inside its body (`cranelisp_ivar_force`, idempotent under
// the CAS+spin state machine, so concurrent forcing from this thunk and Phase
// 2's own force of `a` is safe — work conservation).
//
// The inner fn is built **manually** (à la `par_bind.rs`'s continuation), NOT
// via `compile_expr(Lambda)`: the dependency name is not in `self.variables` at
// Phase 1, so the generic capture path cannot reach it. We capture the IVar
// pointer under a layout slot and emit a force+bind prologue that binds the
// dependency NAME to the forced value, then compile the **unmodified** RHS whose
// `Var(dep)` resolves to that value — no new `MonoExpr` variant, no boundary
// type change (arch R5: backend-only, no public-API impact).

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, MonoExpr, Span, Symbol, Type};

use crate::compiler::signature_heap_category;
use crate::heap::{self, HeapCategory, HeapClosure};

use super::{FnCompiler, find_free_vars};

/// RC_OFFSET for an IVar cell (base-pointer convention, +8). IVars carry an
/// atomic RC at the same offset as every heap object.
const IVAR_RC_OFFSET: i64 = 8;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Build the zero-arg thunk closure for a DEPENDENT sparkable `let` binding
    /// (lenient-eval.md §4.5). `deps` are the binding's earlier *sparked*
    /// dependencies as `(dependency name, its IVar pointer `Value`, the
    /// dependency's value type)`. Returns the thunk closure base pointer
    /// (`rc=1`), ready to hand to `cranelisp_ivar_create`.
    ///
    /// Capture layout: `[ordinary captures … , dependency IVar pointers …]`.
    /// Ordinary captures follow the standard closure rules (`lambda.rs`). Each
    /// dependency IVar pointer is `emit_rc_inc`'d at the closure site (the env
    /// holds its own reference) and dec'd by the thunk's drop glue via the
    /// IVar-aware dealloc — the one new RC rule (§4.5).
    pub(crate) fn compile_dependent_thunk(
        &mut self,
        val_expr: &MonoExpr,
        deps: &[(Symbol, Value, Type)],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        // Ordinary captures: in-scope free vars of the RHS, excluding the
        // dependency names (those come from the captured IVar pointers, not
        // `self.variables`). Sorted for deterministic layout (as `lambda.rs`).
        let dep_names: std::collections::HashSet<Symbol> =
            deps.iter().map(|(n, _, _)| n.clone()).collect();
        let mut ord_captures: Vec<Symbol> = find_free_vars(val_expr, &[])
            .into_iter()
            .filter(|v| !dep_names.contains(v) && self.variables.contains_key(v))
            .collect();
        ord_captures.sort();

        // Inner-fn name: keyed off the RHS span (each binding's RHS has a
        // distinct span, so two dependent thunks in one `let` never collide) with
        // a distinct prefix (so it never collides with the simple-lambda thunk
        // path's `__lambda_…`) plus the mono/gate discriminator (so the same span
        // compiled across create-gate arms or monomorphic instances stays
        // unique — `inner_fn_discriminator`).
        let body_span = val_expr.span();
        let inner_name = format!(
            "__dep_thunk_{}{}_{}__",
            self.inner_fn_discriminator(),
            body_span.start,
            body_span.end
        );

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr
        sig.returns.push(AbiParam::new(types::I64));

        let inner_func_id = self
            .module
            .declare_function(&inner_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare dependent thunk fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        self.define_dependent_thunk_body(
            inner_func_id,
            &inner_name,
            &ord_captures,
            deps,
            val_expr,
            sig,
            span,
        )?;

        // ---- Closure site allocation ----
        let total_caps = ord_captures.len() + deps.len();
        let payload_size = HeapClosure::payload_size(total_caps) as i64;
        let base_ptr = heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size);

        // code_ptr at offset 16.
        let inner_ref = self
            .module
            .declare_func_in_func(inner_func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, inner_ref);
        heap::heap_store(
            &mut self.builder,
            code_ptr,
            base_ptr,
            HeapClosure::CODE_PTR_OFFSET,
        );

        // drop_glue_ptr at offset 24 (custom: ordinary heap caps dec via plain
        // dealloc, IVar caps dec via the IVar-aware dealloc).
        let glue_id = self.build_dependent_thunk_drop_glue(&ord_captures, deps.len(), body_span)?;
        let glue_val = if let Some(id) = glue_id {
            let gref = self.module.declare_func_in_func(id, self.builder.func);
            self.builder.ins().func_addr(types::I64, gref)
        } else {
            self.builder.ins().iconst(types::I64, 0)
        };
        heap::heap_store(
            &mut self.builder,
            glue_val,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        // Store ordinary captures (inc heap-typed ones — the env holds its own
        // reference, exactly as `compile_lambda`).
        for (i, cap) in ord_captures.iter().enumerate() {
            if let Some(var) = self.variables.get(cap) {
                let cap_val = self.builder.use_var(*var);
                heap::heap_store(
                    &mut self.builder,
                    cap_val,
                    base_ptr,
                    HeapClosure::capture_offset(i),
                );
                if let Some(ty) = self.variable_types.get(cap) {
                    let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
                    self.emit_capture_inc(category, cap_val);
                }
            }
        }

        // Store dependency IVar pointers and inc each (AlwaysHeap — the IVar cell
        // is a heap object with an atomic RC at +8; the inc keeps it alive for
        // this thunk past Phase 2's own dec of the main-thread reference, §4.5).
        for (j, (_name, ivar_val, _ty)) in deps.iter().enumerate() {
            let cap_idx = ord_captures.len() + j;
            heap::heap_store(
                &mut self.builder,
                *ivar_val,
                base_ptr,
                HeapClosure::capture_offset(cap_idx),
            );
            // IVars are unconditionally heap (no nullary-tag guard).
            heap::emit_rc_inc(&mut self.builder, self.module, *ivar_val);
        }

        Ok(base_ptr)
    }

    /// Define the dependent thunk's inner function in a separate Cranelift
    /// context. Loads ordinary captures, then emits the **force prologue** — per
    /// dependency: load its captured IVar pointer, `cranelisp_ivar_force` it, and
    /// bind the dependency NAME to the forced (borrowed) value — and finally
    /// compiles the unmodified RHS, whose `Var(dep)` now resolves to the forced
    /// value.
    #[allow(clippy::too_many_arguments)] // +inner_name seeds the body's discriminator
    fn define_dependent_thunk_body(
        &mut self,
        func_id: cranelift_module::FuncId,
        inner_name: &str,
        ord_captures: &[Symbol],
        deps: &[(Symbol, Value, Type)],
        val_expr: &MonoExpr,
        sig: cranelift::codegen::ir::Signature,
        span: Span,
    ) -> Result<(), CranelispError> {
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();
        inner_ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);
        let env_ptr = builder.block_params(entry_block)[0];

        let last_uses = heap::compute_last_uses(val_expr);
        let mut inner = FnCompiler::inner(builder, self.module, self.ctx.clone(), 0, last_uses);
        // Seed the discriminator so any inner functions emitted within the RHS
        // (nested lambdas, etc.) get uniquely-prefixed names (as `lambda.rs`).
        inner.current_fn_name = Some(Symbol::from(inner_name));
        // Gate 5 (`design/backend/ownership-codegen.md` §4.3; FIXME 0525): this
        // whole inner compiler IS a spark-thunk body — the backend relocated the
        // dependent binding's RHS here, and this thunk frame pops at the join while
        // the parent consumes the forced value. Decline stack allocation for every
        // construction in the RHS (its slot would dangle — hard UAF). The DEPENDENT
        // path deliberately does not use `compile_spark_thunk` (the §4.5
        // capture-by-borrow carve-out), so gate 5 is set directly here.
        inner.in_spark_thunk = true;

        // Load ordinary captures from the env. Treated as captures (borrowed):
        // recorded in `variable_types` (so consuming calls inc them) + marked in
        // `captured_vars` (not eligible for last-use transfer, not on
        // `scope_stack` so not dec'd at body exit — the env's drop glue owns the
        // dec).
        for (i, cap) in ord_captures.iter().enumerate() {
            let cap_val =
                heap::heap_load(&mut inner.builder, env_ptr, HeapClosure::capture_offset(i));
            let var = inner.fresh_variable();
            inner.builder.declare_var(var, types::I64);
            inner.builder.def_var(var, cap_val);
            inner.variables.insert(cap.clone(), var);
            if let Some(ty) = self.variable_types.get(cap) {
                inner.variable_types.insert(cap.clone(), ty.clone());
            }
            inner.captured_vars.insert(cap.clone());
        }

        // Force prologue: per dependency, load its captured IVar pointer, force
        // it (the SAME extern the Phase-2 barrier emits), and bind the dependency
        // NAME to the forced value. The forced value is BORROWED — it is owned by
        // the IVar cell / the dependency's own Phase-2 binding — so the dep is
        // treated exactly like a capture (consuming calls inc; no scope dec).
        for (j, (dep_name, _ivar_val, dep_ty)) in deps.iter().enumerate() {
            let cap_idx = ord_captures.len() + j;
            let ivar_cap = heap::heap_load(
                &mut inner.builder,
                env_ptr,
                HeapClosure::capture_offset(cap_idx),
            );
            let forced = inner.emit_extern_call("cranelisp_ivar_force", &[ivar_cap], span)?;
            let var = inner.fresh_variable();
            inner.builder.declare_var(var, types::I64);
            inner.builder.def_var(var, forced);
            inner.variables.insert(dep_name.clone(), var);
            inner
                .variable_types
                .insert(dep_name.clone(), dep_ty.clone());
            inner.captured_vars.insert(dep_name.clone());
        }

        // Compile the unmodified RHS. The initial `scope_stack` frame
        // (`FnCompiler::inner`) is the body frame; captures/deps are NOT on it.
        let skip_var = FnCompiler::<M>::return_var_in_scope(val_expr, inner.scope_stack.last());
        let result = inner.compile_expr(val_expr)?;
        inner.protect_return_value(&skip_var, result, val_expr);
        inner.pop_scope_with_cleanup(skip_var.as_ref());

        inner.builder.ins().return_(&[result]);
        inner.builder.seal_all_blocks();
        inner.builder.finalize();

        self.module
            .define_function(func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define dependent thunk fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(())
    }

    /// Build the dependent thunk's drop glue `(closure_ptr) -> ()`.
    ///
    /// Ordinary heap captures dec via the standard plain-`dealloc` path
    /// (`build_closure_drop_glue` semantics). The dependency IVar captures dec
    /// via the **IVar-aware** dealloc (`cranelisp_ivar_dealloc`) so that, when a
    /// dependency cell's last reference goes here, its ferried error String (a
    /// panicked dependency's message, §5) is freed too — a plain `dealloc` would
    /// leak it. This is the one new RC rule for limit #2 (§4.5): the per-thunk
    /// capture inc is balanced by this dec, keeping the dependency cell alive
    /// past Phase 2's own dec.
    fn build_dependent_thunk_drop_glue(
        &mut self,
        ord_captures: &[Symbol],
        dep_count: usize,
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id;

        // Ordinary heap captures: (capture index, heap category).
        let heap_caps: Vec<(usize, HeapCategory)> = ord_captures
            .iter()
            .enumerate()
            .filter_map(|(i, cap)| {
                let ty = self.variable_types.get(cap)?;
                let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
                match category {
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed => Some((i, category)),
                    HeapCategory::NeverHeap | HeapCategory::Value => None,
                }
            })
            .collect();

        // `compile_dependent_thunk` only calls this when there is ≥1 dependency
        // (a dependent binding by definition), so the IVar caps always need a
        // dec and glue is always emitted.
        debug_assert!(dep_count >= 1, "dependent thunk must have ≥1 dependency");

        let glue_name = format!(
            "runtime/dep_thunk_drop_glue_{}{}_{}",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // closure ptr

        let glue_func_id = self
            .module
            .declare_function(&glue_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare dependent thunk drop glue: {e}"),
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
        let closure_ptr = builder.block_params(entry)[0];

        // Ordinary heap captures: standard dec.
        for (cap_idx, category) in &heap_caps {
            let cap_val = heap::heap_load(
                &mut builder,
                closure_ptr,
                HeapClosure::capture_offset(*cap_idx),
            );
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_dec(&mut builder, self.module, cap_val, dealloc_id, None);
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
                HeapCategory::NeverHeap | HeapCategory::Value => {} // filtered above
            }
        }

        // Dependency IVar captures: IVar-aware dec.
        for j in 0..dep_count {
            let cap_idx = ord_captures.len() + j;
            let ivar_val = heap::heap_load(
                &mut builder,
                closure_ptr,
                HeapClosure::capture_offset(cap_idx),
            );
            emit_ivar_dec_into(&mut builder, self.module, ivar_val, span)?;
        }

        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(glue_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define dependent thunk drop glue: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(Some(glue_func_id))
    }
}

/// Emit an IVar RC dec into a borrowed builder (the dependent thunk's drop glue
/// builds in its own Cranelift context, so it cannot use the `&mut self`
/// `emit_rc_dec_for_ivar`). Atomic sub at +8; on RC-to-0, fence + call
/// `cranelisp_ivar_dealloc` (which frees the ferried error String, if any, then
/// the cell — mirrors `let_if.rs::emit_rc_dec_for_ivar`).
fn emit_ivar_dec_into<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    ivar_val: Value,
    span: Span,
) -> Result<(), CranelispError> {
    let rc_addr = builder.ins().iadd_imm(ivar_val, IVAR_RC_OFFSET);
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = builder.ins().atomic_rmw(
        types::I64,
        MemFlags::new(),
        cranelift::codegen::ir::AtomicRmwOp::Sub,
        rc_addr,
        one,
    );

    let free_block = builder.create_block();
    let cont_block = builder.create_block();

    let one_val = builder.ins().iconst(types::I64, 1);
    let is_last = builder.ins().icmp(IntCC::Equal, old_rc, one_val);
    builder
        .ins()
        .brif(is_last, free_block, &[], cont_block, &[]);

    builder.switch_to_block(free_block);
    builder.seal_block(free_block);
    builder.ins().fence();

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let dealloc_id = module
        .declare_function("cranelisp_ivar_dealloc", Linkage::Import, &sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare cranelisp_ivar_dealloc: {e}"),
            location: ErrorLocation::from_span(span),
        })?;
    let dealloc_ref = module.declare_func_in_func(dealloc_id, builder.func);
    builder.ins().call(dealloc_ref, &[ivar_val]);
    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);

    Ok(())
}
