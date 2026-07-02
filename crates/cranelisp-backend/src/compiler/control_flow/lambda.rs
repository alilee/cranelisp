// Lambda / closure compilation.
//
// Closure site allocation, the inner-fn body, drop glue, and the
// capture-return inc rule (`design/backend/ring2-rc.md`). `build_closure_drop_glue`
// is called by `compile_lambda` and by `par_bind.rs`'s continuation closure
// (cross-module via the shared `impl FnCompiler`).

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, MonoExpr, Span, Symbol, Type};

use crate::heap::{self, HeapCategory, HeapClosure};

use crate::compiler::signature_heap_category;
use super::{find_free_vars, FnCompiler};

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
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
        body: &MonoExpr,
        span: Span,
        lambda_type: Option<&Type>,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
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
        //
        // The name is span-derived AND monomorphisation-discriminated
        // (FIXME 0347 defect 1): when the enclosing fn is monomorphised, N mono
        // instances share this lambda's span, so the enclosing-fn discriminator
        // keeps the N emitted symbols distinct (else the 2nd define_function
        // collides — `Duplicate definition of identifier: __lambda_…__`).
        let inner_name = format!(
            "__lambda_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
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
                location: ErrorLocation::from_span(span),
            })?;

        // Compile the inner function body using a new Cranelift context.
        self.compile_lambda_body(
            inner_func_id,
            &inner_name,
            params,
            &captures,
            body,
            span,
            lambda_type,
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
                //
                // Capture-by-borrow (S99, FIXME 0461; ring2-rc.md §5.5.2): when
                // this closure is a structurally-joined spark thunk
                // (`spark_capture_borrow` raised by the apply-arg / independent-
                // `let` emission site, toggle-gated), the capture is a BORROW —
                // the joined parent frame outlives the spark, so the parent's own
                // scope-cleanup dec is the single dec accounting for the cell.
                // Skip the inc here AND the matching drop-glue dec
                // (`build_closure_drop_glue`), symmetrically. Skipping only one
                // would leak (skip dec only) or UAF (skip inc only).
                if !self.spark_capture_borrow
                    && let Some(ty) = self.variable_types.get(cap_name)
                {
                    let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
                    self.emit_capture_inc(category, cap_val);
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
    ///
    /// `pub(crate)` because `par_bind.rs`'s continuation-closure allocation
    /// calls it cross-module on the shared `impl FnCompiler`.
    pub(crate) fn build_closure_drop_glue(
        &mut self,
        captures: &[Symbol],
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        // Capture-by-borrow (S99, FIXME 0461; ring2-rc.md §5.5.2): a
        // structurally-joined spark thunk borrows ALL its captures (rc-
        // invisible), so it owns none of them — no drop glue. Return `None`
        // symmetrically with the skipped capture-store inc (`compile_lambda` /
        // `alloc_par_cont_closure`). The joined parent frame's own cleanup dec
        // is the single dec accounting for every borrowed cell. This is
        // reachable only from the flag-raising joined sites; the detached
        // `LaunchContinue` path never raises the flag, so its drop glue is
        // emitted as before.
        if self.spark_capture_borrow {
            return Ok(None);
        }

        let dealloc_id = self.ctx.dealloc_func_id;

        // Collect (capture_index, type, heap_category) for heap-typed captures.
        let heap_captures: Vec<(usize, Type, HeapCategory)> = captures
            .iter()
            .enumerate()
            .filter_map(|(i, cap_name)| {
                let ty = self.variable_types.get(cap_name)?;
                let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
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
        //
        // The name is span-derived AND monomorphisation-discriminated
        // (FIXME 0350, follow-on to 0347 defect 1): when the enclosing fn is
        // monomorphised, N mono instances share this lambda's span, so each
        // emits its own drop-glue copy. The enclosing-fn discriminator keeps
        // the N emitted symbols distinct (else the 2nd define_function
        // collides — `Duplicate definition of identifier:
        // runtime/closure_drop_glue_…`). This MUST use the same
        // `inner_fn_discriminator()` scheme as the lambda body name above so
        // the body+drop-glue symbol pair stay paired per mono instance.
        let glue_name = format!(
            "runtime/closure_drop_glue_{}{}_{}",
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
                message: format!("failed to declare closure drop glue fn: {e}"),
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
                location: ErrorLocation::from_span(span),
            })?;

        Ok(Some(glue_func_id))
    }

    /// Emit `rc_inc` on the lambda body's return value when that value is a
    /// bare reference to a captured heap variable.
    ///
    /// See `design/backend/slice-4-21-hello-io-investigation.md §4d/§4e` for
    /// the investigation history, and `design/backend/ring2-rc.md` (new
    /// **capture-return inc** rule, sibling of §5.5) for the normative
    /// description.
    ///
    /// ## Invariant
    ///
    /// A captured heap variable returned as the lambda body value requires
    /// an explicit `rc_inc` before `return`, because:
    ///
    /// 1. The `scope_stack` deliberately excludes captures (see
    ///    `compile_lambda_body` where captures are bound WITHOUT being
    ///    pushed onto the scope frame — captures are the closure env's
    ///    responsibility, not the body scope's).
    /// 2. `protect_return_value` guards its inc-on-return behind
    ///    `has_cleanup_targets`, which examines `scope_stack` only. For a
    ///    `(fn [_] b)` shape where `_` is non-heap and `b` is a capture,
    ///    `has_cleanup_targets` is false and `protect_return_value` emits
    ///    no inc.
    /// 3. The closure's drop-glue (see `build_closure_drop_glue`) WILL dec
    ///    the capture after the body returns, because a fresh one-shot
    ///    closure is consumed via `consume_closure` by the IO trampoline
    ///    (and other fresh-closure call sites) after invocation.
    ///
    /// Without the inc, the value returned to the caller points at a node
    /// the drop-glue is about to dec to zero, producing a use-after-free
    /// in whatever the caller does next (in the observed case, the IO
    /// trampoline reads the pointer as the new `current` frame and
    /// dereferences freed memory).
    ///
    /// This helper is additive: `protect_return_value`'s scope-stack logic
    /// is unchanged for all other callers and all other return paths
    /// within lambda bodies. Only the `Var{captured_heap}` shape triggers
    /// this new inc.
    fn emit_capture_return_inc(&mut self, body: &MonoExpr, body_val: Value) {
        // Only trigger for a direct reference to a captured variable.
        let MonoExpr::Var { name, .. } = body else {
            return;
        };
        if !self.captured_vars.contains(name) {
            return;
        }
        // Look up the capture's type (seeded by `compile_lambda_body` from
        // the enclosing scope). Non-heap captures need no inc.
        let Some(ty) = self.variable_types.get(name).cloned() else {
            return;
        };
        let category = signature_heap_category(&ty, Some(self.ctx.symbol_tables));
        self.emit_capture_inc(category, body_val);
    }

    /// Compile the body of a lambda as a separate JIT function.
    ///
    /// The inner function has signature (env_ptr, params...) -> i64.
    /// Captured values are loaded from the environment.
    #[allow(clippy::too_many_arguments)] // +inner_name seeds the body compiler's discriminator
    fn compile_lambda_body(
        &mut self,
        func_id: cranelift_module::FuncId,
        inner_name: &str,
        params: &[Symbol],
        captures: &[Symbol],
        body: &MonoExpr,
        span: Span,
        lambda_type: Option<&Type>,
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
            self.ctx.clone(),
            params.len(),
            last_uses,
        );

        // Seed the inner compiler's discriminator with this lambda's
        // globally-unique name. Inner functions emitted within the body
        // (nested lambdas, spark thunks, fn-as-value/gate wrappers) are named by
        // `inner_fn_discriminator()`, which keys off `current_fn_name`. Without a
        // seed the inner compiler resets it to `None`, so the same source span
        // reached via two distinct compilation paths — e.g. the create-gate
        // (lenient-eval.md §3.6.2) compiles the same subexpression on BOTH arms,
        // and each gate arm's all-lenient thunk descent re-enters fresh inner
        // compilers — would re-emit identical module-global names and the second
        // `define_function` would collide (`Duplicate definition of identifier`).
        // Seeding with the unique lambda name makes every name within the body
        // uniquely prefixed. TCO self-call detection is unaffected: inner
        // compilers have `tail_loop_block = None`, which gates the self-call fast
        // path regardless of `current_fn_name`.
        inner_compiler.current_fn_name = Some(Symbol::from(inner_name));

        // Bind captured variables from the environment.
        //
        // Record each capture's type in the inner compiler's `variable_types`
        // so that consuming calling convention inside the body emits the
        // required `rc_inc` on captured heap values before passing them to
        // consuming callees. Captures are NOT pushed onto `scope_stack` —
        // they are borrowed references whose release is the closure env's
        // drop-glue responsibility, not the body scope's.
        //
        // Prior bug (S60 Wave 2 Round 2 α): captures had no type recorded,
        // so `compile_consuming_arg_list` skipped the caller-side inc.
        // Consuming callees (e.g., `(cell-at g 0)` inside a spark thunk)
        // then dec'd the capture at their scope exit, underflowing the
        // captured value's RC. When the thunk's drop-glue ran afterwards,
        // the same capture was dec'd a second time → double-free.
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
            // Copy the capture's type from the enclosing scope so the body
            // can correctly RC-inc captured heap values for consuming calls.
            if let Some(ty) = self.variable_types.get(cap_name) {
                inner_compiler
                    .variable_types
                    .insert(cap_name.clone(), ty.clone());
            }
        }

        // Look up the lambda's inferred type to get parameter types.
        // This is essential for unused parameters: derive_param_type scans
        // use sites, so unused params (e.g., `_s` in `(fn [_s] 42)`) would
        // have no type recorded and scope cleanup would skip their RC dec.
        let lambda_param_types: Vec<Option<Type>> = if let Some(Type::Fn(param_types, _)) =
            lambda_type
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

            // Use the lambda's inferred param type first.
            // Fall back to derive_param_type_from_body (use-site inference) if the
            // lambda type isn't available.
            if let Some(Some(ty)) = lambda_param_types.get(i) {
                inner_compiler.variable_types.insert(param_name.clone(), ty.clone());
            } else if let Some(ty) = Self::derive_param_type_from_body(body, param_name) {
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
        // Capture-return inc (Slice 4 / ring2-rc.md "capture-return inc"
        // rule — sibling of §5.5 borrowed_vars). When the lambda body
        // returns a captured heap variable directly (e.g. `(fn [_] b)`
        // where `b` is a heap-typed capture), emit `rc_inc` on the
        // returned value so the closure's drop-glue dec (run by the
        // trampoline's `consume_closure`) is balanced and the caller
        // receives a live reference. `protect_return_value` does NOT
        // cover this case because captures are not on `scope_stack`.
        inner_compiler.emit_capture_return_inc(body, result);
        inner_compiler.pop_scope_with_cleanup(skip_var.as_ref());

        inner_compiler.builder.ins().return_(&[result]);
        inner_compiler.builder.seal_all_blocks();
        inner_compiler.builder.finalize();

        // Define the function in the JIT module.
        self.module
            .define_function(func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define lambda function: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(())
    }
}
