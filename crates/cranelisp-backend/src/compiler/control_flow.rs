// Control flow, binding, and closure codegen.
//
// compile_if, compile_let, compile_lambda

use std::collections::HashSet;

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{ErrorLocation, CranelispError, Expr, ResolvedCall, Span, Symbol, Type};
use crate::heap::HeapCategory;

use crate::heap::{self, HeapAdt, HeapClosure};
use crate::primitives_inline;

use super::FnCompiler;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // --- Let expression ---

    pub(crate) fn compile_let(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Check if lenient evaluation applies.
        // Skip sparkability analysis inside trace bodies — trace must
        // execute sequentially to produce deterministic trace trees.
        if !*LENIENT_DISABLED && !self.in_trace_body {
            // Collect known constructor names to exclude from sparking.
            // Collect constructor names from the current module's symbol table.
            let constructors: HashSet<Symbol> = self
                .ctx
                .symbol_tables
                .get(&self.ctx.current_module)
                .map(|table| {
                    table.symbols.iter()
                        .filter(|(_, entry)| matches!(
                            entry,
                            cranelisp_types::ModuleEntry::Def {
                                kind, ..
                            } if matches!(**kind, cranelisp_types::DefKind::Constructor { .. })
                        ))
                        .map(|(name, _)| name.clone())
                        .collect()
                })
                .unwrap_or_default();
            let sparkable = find_sparkable_bindings(bindings, &constructors);
            if sparkable.len() >= 2 {
                return self.compile_let_lenient(bindings, body, &sparkable, span);
            }
        }

        self.compile_let_sequential(bindings, body, span)
    }

    /// Compile a let expression sequentially (no lenient evaluation).
    fn compile_let_sequential(
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
            // Record the binding's type from the expression's inferred_type.
            if let Some(ty) = val_expr.inferred_type() {
                self.variable_types.insert(name.clone(), ty.clone());
            }

            let val = self.compile_expr(val_expr)?;

            // If compile_expr produced a closure with drop glue, record it.
            if let Some(glue_id) = self.pending_closure_drop_glue.take() {
                self.closure_drop_glue.insert(name.clone(), glue_id);
            }

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

    /// Compile a let expression with lenient evaluation (parallel sparkable bindings).
    ///
    /// See design/backend/lenient-eval.md §4.2 for the algorithm.
    fn compile_let_lenient(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        sparkable: &[usize],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let sparkable_set: HashSet<usize> = sparkable.iter().copied().collect();

        self.push_scope();
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Phase 1: Create and spark IVars for sparkable bindings.
        let mut ivar_map: std::collections::HashMap<usize, Value> = std::collections::HashMap::new();

        for &idx in sparkable {
            let (_name, val_expr) = &bindings[idx];

            // Wrap the value expression in a zero-arg lambda (thunk).
            let thunk_expr = Expr::Lambda {
                params: vec![],
                body: Box::new(val_expr.clone()),
                span: val_expr.span(),
                inferred_type: None,
            };
            let thunk_val = self.compile_expr(&thunk_expr)?;

            // Call cranelisp_ivar_create(thunk_ptr) -> ivar_ptr
            let ivar_val = self.emit_extern_call_1(
                "cranelisp_ivar_create", thunk_val, span,
            )?;

            // Call cranelisp_ivar_spark(ivar_ptr)
            let _spark_result = self.emit_extern_call_1(
                "cranelisp_ivar_spark", ivar_val, span,
            )?;

            ivar_map.insert(idx, ivar_val);
        }

        // Phase 2: Process all bindings in order.
        for (i, (name, val_expr)) in bindings.iter().enumerate() {
            if let Some(ty) = val_expr.inferred_type() {
                self.variable_types.insert(name.clone(), ty.clone());
            }

            let val = if sparkable_set.contains(&i) {
                // Force the IVar and dec our reference.
                let ivar_val = ivar_map[&i];
                let forced_val = self.emit_extern_call_1(
                    "cranelisp_ivar_force", ivar_val, span,
                )?;

                // Dec the IVar (main thread's reference).
                // The IVar has atomic RC; the spark task also dec's.
                self.emit_rc_dec_for_ivar(ivar_val, span)?;

                forced_val
            } else {
                // Non-sparkable: compile normally.
                self.compile_expr(val_expr)?
            };

            if let Some(glue_id) = self.pending_closure_drop_glue.take() {
                self.closure_drop_glue.insert(name.clone(), glue_id);
            }

            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(name.clone());
        }

        // Phase 3: Compile body.
        self.in_tail_position = saved_tail;
        let skip_var = Self::return_var_in_scope(body, self.scope_stack.last());
        let result = self.compile_expr(body)?;
        self.protect_return_value(&skip_var, result, body);
        self.pop_scope_with_cleanup(skip_var.as_ref());

        Ok(result)
    }

    /// Emit a call to an extern "C" function with one i64 argument, returning i64.
    fn emit_extern_call_1(
        &mut self,
        name: &str,
        arg: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern function '{name}': {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let local_func = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(local_func, &[arg]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Emit an inline RC dec for an IVar pointer.
    ///
    /// IVars use atomic RC at offset +8. When dec brings RC to 0, call
    /// `cranelisp_ivar_dealloc` to free — that intrinsic frees the IVar cell
    /// AND any ferried error String stashed in its `error` field by the
    /// fork-join error-slot ferry (a panicked thunk's message). Plain
    /// `runtime/dealloc` would leak that String; `cranelisp_ivar_dealloc` is the
    /// IVar-aware drop path (`ivar.rs`, test-discovery.md §6).
    fn emit_rc_dec_for_ivar(&mut self, ivar_val: Value, span: Span) -> Result<(), CranelispError> {
        // Load current RC from ivar + 8
        let rc_offset = self.builder.ins().iconst(types::I64, 8);
        let rc_addr = self.builder.ins().iadd(ivar_val, rc_offset);

        // atomic_rmw sub 1 -> old_rc
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::new(),
            cranelift::codegen::ir::AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // If old_rc == 1, free the IVar.
        let free_block = self.builder.create_block();
        let cont_block = self.builder.create_block();

        let one_val = self.builder.ins().iconst(types::I64, 1);
        let is_last = self.builder.ins().icmp(IntCC::Equal, old_rc, one_val);
        self.builder
            .ins()
            .brif(is_last, free_block, &[], cont_block, &[]);

        // Free block: call cranelisp_ivar_dealloc(ivar_ptr) — frees the cell
        // and any ferried error String (test-discovery.md §6).
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);

        // Acquire fence before the IVar-aware dealloc reads the error field
        // (consistent with Decision 13).
        self.builder.ins().fence();

        let _dealloc_result = self
            .emit_extern_call_1("cranelisp_ivar_dealloc", ivar_val, span)?;
        self.builder.ins().jump(cont_block, &[]);

        // Continue.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        Ok(())
    }

    /// Compile an `Expr::ParBind` — emit Par node + continuation closure + Bind node.
    ///
    /// ParBind bindings are semantically independent (no binding references
    /// another). This method compiles them into an IO tree structure:
    ///
    /// 1. Compile each binding's IO expression → IO tree pointers
    /// 2. Allocate a Par node containing all branch pointers
    /// 3. Build a continuation closure that unpacks results and evaluates body
    /// 4. Allocate a Bind node linking Par → continuation
    ///
    /// The trampoline dispatches Par branches concurrently (with resource token
    /// serialization), collects results into an alloc_with_rc buffer, and calls
    /// the continuation with the buffer pointer.
    ///
    /// RC lifecycle follows constructor convention (Decision 20): ownership
    /// transfer, no inc on store. IO expressions at rc=1 transfer into Par;
    /// continuation at rc=1 transfers into Bind.
    ///
    /// See design/backend/io-scheduling.md §4 for the full algorithm.
    pub(crate) fn compile_par_bind(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        let n = bindings.len();
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Phase 1: Compile each IO binding expression.
        let mut io_vals = Vec::with_capacity(n);
        for (_name, val_expr) in bindings {
            let io_val = self.compile_expr(val_expr)?;
            io_vals.push(io_val);
        }

        // Phase 2: Allocate Par node.
        // Layout: [header(16) | tag=3(8) | count(8) | branch_0(8) | ... | branch_{N-1}(8)]
        // Payload size = tag(8) + count(8) + N*8
        let par_payload_size = (8 + 8 + n * 8) as i64;
        let par_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            par_payload_size,
        );

        // Store tag=3 (IO_TAG_PAR) at offset 16.
        let tag_val = self.builder.ins().iconst(types::I64, 3);
        heap::heap_store(&mut self.builder, tag_val, par_ptr, HeapAdt::TAG_OFFSET);

        // Store count at offset 24.
        let count_val = self.builder.ins().iconst(types::I64, n as i64);
        heap::heap_store(&mut self.builder, count_val, par_ptr, HeapAdt::field_offset(0));

        // Store branch IO pointers at offsets 32, 40, 48, ...
        // No RC inc — ownership transfer (constructor convention, Decision 20).
        for (i, &io_val) in io_vals.iter().enumerate() {
            heap::heap_store(
                &mut self.builder,
                io_val,
                par_ptr,
                HeapAdt::field_offset(1 + i),
            );
        }

        // Phase 3: Build continuation closure.
        let cont_ptr = self.compile_par_bind_continuation(bindings, body, span)?;

        // Phase 4: Allocate Bind node.
        // Layout: [header(16) | tag=2(8) | inner(8) | cont(8)]
        let bind_payload_size = HeapAdt::payload_size(2) as i64; // tag + 2 fields = 24
        let bind_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            bind_payload_size,
        );

        // Store tag=2 (IO_TAG_BIND).
        let bind_tag = self.builder.ins().iconst(types::I64, 2);
        heap::heap_store(&mut self.builder, bind_tag, bind_ptr, HeapAdt::TAG_OFFSET);

        // Store par_ptr at field_offset(0) (24).
        heap::heap_store(&mut self.builder, par_ptr, bind_ptr, HeapAdt::field_offset(0));

        // Store cont_ptr at field_offset(1) (32).
        heap::heap_store(&mut self.builder, cont_ptr, bind_ptr, HeapAdt::field_offset(1));

        // No RC inc on par_ptr or cont_ptr — ownership transfer (Decision 20).

        self.in_tail_position = saved_tail;
        Ok(bind_ptr)
    }

    /// Build the continuation closure for a ParBind expression.
    ///
    /// The continuation is a closure with signature:
    ///   `extern "C" fn(env_ptr: i64, results_ptr: i64) -> i64`
    ///
    /// It loads N results from results_ptr (an alloc_with_rc buffer) at
    /// offsets FIELD_0_OFFSET + i*8 (24, 32, 40, ...), binds them to the
    /// corresponding names, compiles the body, dec's the results buffer,
    /// and returns the body result (an IO tree pointer).
    ///
    /// Returns the closure base pointer (rc=1).
    fn compile_par_bind_continuation(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        // Compute captures: free variables of the body that are NOT among
        // the binding names and ARE in scope in the enclosing function.
        let binding_names: HashSet<Symbol> = bindings.iter().map(|(n, _)| n.clone()).collect();
        let body_free = find_free_vars(body, &[]);
        let mut captures: Vec<Symbol> = body_free
            .into_iter()
            .filter(|v| !binding_names.contains(v) && self.variables.contains_key(v))
            .collect();
        captures.sort(); // deterministic layout

        // Declare the continuation function.
        // Signature: (env_ptr: i64, results_ptr: i64) -> i64
        // Mono-discriminated span name (FIXME 0347 defect 1).
        let cont_name = format!(
            "__par_cont_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr
        sig.params.push(AbiParam::new(types::I64)); // results_ptr
        sig.returns.push(AbiParam::new(types::I64));

        let cont_func_id = self
            .module
            .declare_function(&cont_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare par-bind continuation: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Compile the continuation body using a separate Cranelift context.
        {
            let mut inner_ctx = self.module.make_context();
            let mut inner_func_ctx = FunctionBuilderContext::new();

            // Signature: (env_ptr, results_ptr) -> i64
            inner_ctx.func.signature = sig;

            let mut builder = FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);
            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            let block_params = builder.block_params(entry_block).to_vec();
            let env_ptr = block_params[0];
            let results_ptr = block_params[1];

            let last_uses = heap::compute_last_uses(body);
            let mut inner = FnCompiler::inner(
                builder,
                self.module,
                self.ctx.clone(),
                0, // fn_param_count=0: binding names come from results buffer
                last_uses,
            );

            // Load captured variables from env_ptr at CAPTURES_START + i*8.
            for (i, cap_name) in captures.iter().enumerate() {
                let cap_val = heap::heap_load(
                    &mut inner.builder,
                    env_ptr,
                    HeapClosure::capture_offset(i),
                );
                let var = inner.fresh_variable();
                inner.builder.declare_var(var, types::I64);
                inner.builder.def_var(var, cap_val);
                inner.variables.insert(cap_name.clone(), var);
            }

            // Mark captures so they are not eligible for last-use transfer.
            for cap_name in &captures {
                inner.captured_vars.insert(cap_name.clone());
            }

            // Load N results from results_ptr at FIELD_0_OFFSET + i*8.
            // The results_ptr is an alloc_with_rc buffer: [header(16) | result_0(8) | result_1(8) | ...]
            // Results start at offset 16 (HeapHeader::SIZE), which is HeapAdt::TAG_OFFSET.
            // But per Q2 decision, results are at FIELD_0_OFFSET + i*8 (offsets 24, 32, 40, ...).
            // Actually, the buffer is alloc_with_rc(N*8), so payload starts at offset 16.
            // The trampoline stores results at payload offsets 0, 8, 16, ...
            // which means absolute offsets 16, 24, 32, ...
            // But the sprint says "FIELD_0_OFFSET + i*8 (offsets 24, 32, 40...)".
            // FIELD_0_OFFSET = 24. So the trampoline must store at offsets 24+i*8 from base.
            // That means payload layout: [padding_8(8) | result_0(8) | result_1(8) | ...]
            // with payload_size = 8 + N*8.
            //
            // Let's use HeapAdt::field_offset(i) = 24 + i*8 to be consistent with the decision.
            inner.push_scope();
            for (i, (name, val_expr)) in bindings.iter().enumerate() {
                let result_val = heap::heap_load(
                    &mut inner.builder,
                    results_ptr,
                    HeapAdt::field_offset(i),
                );
                let var = inner.fresh_variable();
                inner.builder.declare_var(var, types::I64);
                inner.builder.def_var(var, result_val);
                inner.variables.insert(name.clone(), var);
                inner
                    .scope_stack
                    .last_mut()
                    .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                    .push(name.clone());

                // Track type for RC — unwrap IO(T) to get inner T.
                if let Some(ty) = val_expr.inferred_type() {
                    let inner_ty = match ty {
                        Type::ADT(fqtn, args) if fqtn.name.as_ref() == "IO" && !args.is_empty() => {
                            args[0].clone()
                        }
                        _ => ty.clone(),
                    };
                    inner.variable_types.insert(name.clone(), inner_ty);
                }
            }

            // Compile the body.
            let skip_var = FnCompiler::<M>::return_var_in_scope(body, inner.scope_stack.last());
            let result = inner.compile_expr(body)?;
            inner.protect_return_value(&skip_var, result, body);
            inner.pop_scope_with_cleanup(skip_var.as_ref());

            // Dec the results buffer. It's an alloc_with_rc allocation —
            // emit_rc_dec with no drop glue (results are plain i64 values,
            // their RC is managed by the binding variables above).
            heap::emit_rc_dec(
                &mut inner.builder,
                inner.module,
                results_ptr,
                inner.ctx.dealloc_func_id,
                None,
            );

            inner.builder.ins().return_(&[result]);
            inner.builder.seal_all_blocks();
            inner.builder.finalize();

            self.module
                .define_function(cont_func_id, &mut inner_ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define par-bind continuation: {e}"),
                    location: ErrorLocation::from_span(span),
                })?;
        }

        // Allocate the continuation closure at the call site.
        // Layout: [header(16) | code_ptr(8) | drop_glue_ptr(8) | cap_0(8) | ...]
        let closure_payload_size = HeapClosure::payload_size(captures.len()) as i64;
        let closure_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            closure_payload_size,
        );

        // Store code_ptr.
        let cont_func_ref = self
            .module
            .declare_func_in_func(cont_func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, cont_func_ref);
        heap::heap_store(
            &mut self.builder,
            code_ptr,
            closure_ptr,
            HeapClosure::CODE_PTR_OFFSET,
        );

        // Build and store drop glue for heap-typed captures.
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
            closure_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        // Store captured values and inc RC for heap-typed captures.
        for (i, cap_name) in captures.iter().enumerate() {
            if let Some(var) = self.variables.get(cap_name) {
                let cap_val = self.builder.use_var(*var);
                heap::heap_store(
                    &mut self.builder,
                    cap_val,
                    closure_ptr,
                    HeapClosure::capture_offset(i),
                );

                // Inc heap-typed captures: the closure env needs its own reference.
                if let Some(ty) = self.variable_types.get(cap_name) {
                    let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
                    match category {
                        HeapCategory::AlwaysHeap => {
                            heap::emit_rc_inc(&mut self.builder, cap_val);
                        }
                        HeapCategory::Mixed => {
                            heap::emit_rc_inc_guarded(&mut self.builder, cap_val);
                        }
                        HeapCategory::NeverHeap => {}
                    }
                }
            }
        }

        Ok(closure_ptr)
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
                if let Some(ty) = self.variable_types.get(cap_name) {
                    let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
                    match category {
                        HeapCategory::AlwaysHeap => {
                            heap::emit_rc_inc(&mut self.builder, cap_val);
                        }
                        HeapCategory::Mixed => {
                            heap::emit_rc_inc_guarded(&mut self.builder, cap_val);
                        }
                        HeapCategory::NeverHeap => {}
                    }
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
    fn build_closure_drop_glue(
        &mut self,
        captures: &[Symbol],
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id;

        // Collect (capture_index, type, heap_category) for heap-typed captures.
        let heap_captures: Vec<(usize, Type, HeapCategory)> = captures
            .iter()
            .enumerate()
            .filter_map(|(i, cap_name)| {
                let ty = self.variable_types.get(cap_name)?;
                let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
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
    fn emit_capture_return_inc(&mut self, body: &Expr, body_val: Value) {
        // Only trigger for a direct reference to a captured variable.
        let Expr::Var { name, .. } = body else {
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
        let category = HeapCategory::classify(&ty, Some(self.ctx.symbol_tables));
        match category {
            HeapCategory::AlwaysHeap => {
                heap::emit_rc_inc(&mut self.builder, body_val);
            }
            HeapCategory::Mixed => {
                heap::emit_rc_inc_guarded(&mut self.builder, body_val);
            }
            HeapCategory::NeverHeap => {}
        }
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

    // --- Named function as value ---

    /// Check if a name is a known top-level function (eligible for wrapping).
    pub(crate) fn is_known_function(&self, name: &Symbol) -> bool {
        self.ctx.func_ids.contains_key(name)
            || crate::compiler::resolve_got_target(
                self.ctx.symbol_tables,
                self.ctx.module_aliases,
                &self.ctx.current_module,
                name,
            )
            .is_some()
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
                    location: ErrorLocation::from_span(span),
                })?;

        let arity = self.ctx.func_arities.get(name).copied()
            .or_else(|| crate::compiler::resolve_func_arity(
                self.ctx.symbol_tables,
                self.ctx.module_aliases,
                &self.ctx.current_module,
                name,
            ))
            .ok_or_else(|| {
                CranelispError::CodegenError {
                    message: format!("unknown arity for function: {name}"),
                    location: ErrorLocation::from_span(span),
                }
            })?;

        // Compile the wrapper function. Span-derived + mono-discriminated name
        // (FIXME 0347 defect 1) so monomorphic copies of the enclosing fn do not
        // collide on a shared fn-as-value wrapper symbol.
        let wrapper_name = format!(
            "__wrap_{name}_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );
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
                location: ErrorLocation::from_span(span),
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

        // Store zero drop glue pointer (no captures to drop).
        let zero = self.builder.ins().iconst(types::I64, 0);
        heap::heap_store(
            &mut self.builder,
            zero,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        Ok(base_ptr)
    }

    /// Emit a value-position trait-method reference as a zero-capture
    /// dispatch-wrapper closure (spec §7.6 — trait methods as first-class
    /// values).
    ///
    /// This is the **zero-args-applied analogue of auto-curry**: where
    /// `compile_auto_curry` captures some applied args and forwards them plus
    /// the remaining args to the resolved target, the value-position case
    /// captures nothing and forwards all `arity` args. The wrapper signature is
    /// `(env_ptr, arg_0, ..., arg_{arity-1}) -> i64`; the body ignores `env_ptr`
    /// and calls `emit_curry_target_call` with the typecheck-supplied
    /// `resolved_call` so the SAME dispatch path is used as direct application.
    ///
    /// Per Decision 43, backend has no trait knowledge: typecheck already
    /// resolved the value-position `Expr::Var` to a concrete target
    /// (`BuiltinFn { name }` for primitive-implemented methods like `str-eq` /
    /// `add-f64` / `eq-i64` / `int-to-string`, or `TraitMethod { mangled_name }`
    /// otherwise). Backend just emits a call to that name. This **replaces** the
    /// hard-coded-Int `compile_operator_as_value` path (which unconditionally
    /// dispatched `=`→`eq-i64`, `+`→`add-i64` regardless of operand type — the
    /// source of Symptom B: String `=`→`false`, Float `+`→`inf.0`).
    ///
    /// `arity` is the param count of the Var's `inferred_type`
    /// (`Type::Fn(params, _)`), supplied by the caller (`compile_var`).
    pub(crate) fn compile_trait_method_as_value(
        &mut self,
        resolved: &ResolvedCall,
        arity: usize,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        // The callable name carried by the resolution — used only for a stable,
        // unique wrapper symbol name. The actual dispatch target is chosen by
        // `emit_curry_target_call` from `resolved`.
        let target_name: Symbol = match resolved {
            ResolvedCall::TraitMethod { mangled_name, .. } => {
                Symbol::from(mangled_name.as_ref())
            }
            ResolvedCall::BuiltinFn { name, .. } => Symbol::from(name.as_ref()),
            // Other variants are not produced for value-position trait methods
            // by typecheck; emit_curry_target_call falls through to a by-name
            // call, which would fail loudly. Use a placeholder name.
            _ => Symbol::from("__trait_method_value__"),
        };

        // Compile the wrapper function: (env_ptr, arg_0..arg_{arity-1}) -> i64.
        // Mono-discriminated span name (FIXME 0347 defect 1).
        let wrapper_name = format!(
            "__wrap_tmv_{target_name}_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );
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
                message: format!("failed to declare trait-method-value wrapper: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Build the wrapper body in a separate codegen context.
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();
        inner_ctx.func.signature = sig;

        let mut builder =
            FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let block_params = builder.block_params(entry).to_vec();
        let user_args: Vec<Value> = block_params[1..].to_vec(); // skip env_ptr

        // Dispatch through the SAME path direct application uses.
        let result = self.emit_curry_target_call(
            &mut builder,
            &target_name,
            &user_args,
            span,
            Some(resolved),
        )?;

        builder.ins().return_(&[result]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(wrapper_func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define trait-method-value wrapper: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Allocate a closure with zero captures: [header | code_ptr | drop_glue(0)].
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

        // Store zero drop glue pointer (no captures to drop).
        let zero = self.builder.ins().iconst(types::I64, 0);
        heap::heap_store(
            &mut self.builder,
            zero,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
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
                location: ErrorLocation::from_span(span),
            })?;

        Ok(())
    }

    /// Emit the call instruction inside a wrapper function body.
    ///
    /// Prefers a direct `call` via FuncId when the target is in the current
    /// unit's `func_ids` map. Otherwise emits a GOT-indirect `call_indirect`
    /// using the uniform `__cranelisp_got_{module}` data-symbol strategy
    /// (design/backend/compile-to-module.md §12).
    fn emit_wrapper_call(
        &mut self,
        builder: &mut FunctionBuilder,
        target_name: &Symbol,
        user_params: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // If the function is declared in the current compilation unit, emit a
        // direct call — cheaper and avoids an unnecessary GOT dereference.
        if let Some(target_id) = self.ctx.func_ids.get(target_name) {
            let target_ref =
                self.module.declare_func_in_func(*target_id, builder.func);
            let call = builder.ins().call(target_ref, user_params);
            return Ok(builder.inst_results(call)[0]);
        }

        // Otherwise: GOT-indirect call via __cranelisp_got_{module} data sym.
        let (module_path, slot) = self.resolve_got_entry(target_name, span)?;
        let got_sym = crate::compiler::got_data_symbol_name(&module_path);
        let data_id = self
            .module
            .declare_data(&got_sym, cranelift_module::Linkage::Import, false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare GOT data '{}': {e}", got_sym),
                location: ErrorLocation::from_span(span),
            })?;

        // Decision 23 (Wave 2 follow-on): the symbol address IS the slab base
        // — no extra pointer-cell deref. One load reaches the slot.
        let gv = self.module.declare_data_in_func(data_id, builder.func);
        let slab_base = builder.ins().global_value(types::I64, gv);
        let slot_offset = (slot * 8) as i64;
        let slot_addr = builder.ins().iadd_imm(slab_base, slot_offset);
        let func_ptr = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), slot_addr, 0);

        let mut sig = self.module.make_signature();
        for _ in user_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = builder.import_signature(sig);

        let call = builder.ins().call_indirect(sig_ref, func_ptr, user_params);
        Ok(builder.inst_results(call)[0])
    }

    /// Emit the call to the auto-curry target inside a wrapper function body.
    ///
    /// When the target is a trait method or builtin, this emits the appropriate
    /// inline IR or extern call directly, instead of trying to call by name
    /// (which fails for inline builtins like `add-i64` that have no JIT symbol).
    fn emit_curry_target_call(
        &mut self,
        builder: &mut FunctionBuilder,
        target_name: &Symbol,
        all_args: &[Value],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
    ) -> Result<Value, CranelispError> {
        if let Some(resolved) = trait_resolution {
            match resolved {
                ResolvedCall::TraitMethod {
                    mangled_name,
                    ..
                } => {
                    // Per Decision 43 + FIXME 0185: backend has no trait
                    // knowledge. Dispatch goes via the trait-impl's mangled
                    // name uniformly; the pre-D43 (TraitName, Symbol,
                    // TypeName) intercept that mapped primitive-implemented
                    // trait methods to inline IR is deleted. See the parallel
                    // call site in `compiler/apply.rs::compile_apply` for
                    // the design context — FIXME 0185 tracks the typecheck
                    // migration that restores inline optimisation by having
                    // typecheck emit `BuiltinFn { name: "add-i64" }` for
                    // primitive-implemented trait methods directly.
                    let sym = Symbol::from(mangled_name.as_ref());
                    return self.emit_wrapper_call(builder, &sym, all_args, span);
                }
                ResolvedCall::BuiltinFn { name: jit_name } => {
                    // Named builtin resolved by the typechecker.
                    if is_extern_primitive_in_wrapper(jit_name) {
                        return emit_extern_call_in_wrapper(
                            builder, self.module, jit_name, all_args, span,
                        );
                    }
                    if primitives_inline::is_known_builtin(jit_name) {
                        match primitives_inline::try_emit_inline_primitive(
                            builder, jit_name, all_args, span,
                            self.module, self.ctx.panic_func_id,
                        ) {
                            Some(result) => return result,
                            None => {
                                // Drift between is_known_builtin and the
                                // inline table — fall through to wrapper
                                // GOT-indirect call.
                                let sym = Symbol::from(jit_name.as_ref());
                                return self.emit_wrapper_call(builder, &sym, all_args, span);
                            }
                        }
                    }
                    // Unknown builtin: treat as extern.
                    return emit_extern_call_in_wrapper(
                        builder, self.module, jit_name, all_args, span,
                    );
                }
                _ => {} // SigDispatch, AutoCurry — fall through to emit_wrapper_call
            }
        }

        // No trait resolution, or resolution didn't match — call by name.
        self.emit_wrapper_call(builder, target_name, all_args, span)
    }

    // --- Auto-curry codegen ---

    /// Compile an auto-curried partial application.
    ///
    /// Produces a closure that captures the applied arguments and, when called
    /// with the remaining arguments, forwards all to the target function.
    ///
    /// Layout: `[rc_header | code_ptr | drop_glue_ptr | cap_0 ... cap_n]`
    #[allow(clippy::too_many_arguments)] // Curry context requires all parameters
    pub(crate) fn compile_auto_curry(
        &mut self,
        target_name: &Symbol,
        applied_vals: &[Value],
        applied_count: usize,
        total_count: usize,
        args: &[Expr],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        let remaining_count = total_count - applied_count;

        // Classify each applied arg's heap category for RC management.
        let arg_categories: Vec<HeapCategory> = args
            .iter()
            .map(|arg| {
                arg.inferred_type()
                    .map(|ty| HeapCategory::classify(ty, Some(self.ctx.symbol_tables)))
                    .unwrap_or(HeapCategory::NeverHeap)
            })
            .collect();

        // 1. Compile the wrapper function.
        let wrapper_func_id = self.compile_auto_curry_wrapper(
            target_name,
            applied_count,
            remaining_count,
            &arg_categories,
            span,
            trait_resolution,
        )?;

        // 2. Build drop glue for heap-typed captures.
        let drop_glue_id = self.build_auto_curry_drop_glue(
            &arg_categories,
            span,
        )?;

        // 3. Allocate closure env.
        let payload_size = HeapClosure::payload_size(applied_count) as i64;
        let base_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            payload_size,
        );

        // Store wrapper code_ptr at CODE_PTR_OFFSET (16).
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

        // Store drop glue pointer at DROP_GLUE_PTR_OFFSET (24).
        let drop_glue_val = if let Some(glue_id) = drop_glue_id {
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

        // 4. Store applied args as captures, with RC inc for heap-typed values.
        for (i, &val) in applied_vals.iter().enumerate() {
            heap::heap_store(
                &mut self.builder,
                val,
                base_ptr,
                HeapClosure::capture_offset(i),
            );

            // Inc heap-typed captures: closure env needs its own reference.
            match arg_categories[i] {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, val);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut self.builder, val);
                }
                HeapCategory::NeverHeap => {}
            }
        }

        Ok(base_ptr)
    }

    /// Compile the wrapper function for auto-curry.
    ///
    /// Signature: `(env_ptr, remaining_0, ..., remaining_k) -> i64`
    /// Body: load captures from env, inc heap captures, call target with all args.
    fn compile_auto_curry_wrapper(
        &mut self,
        target_name: &Symbol,
        applied_count: usize,
        remaining_count: usize,
        arg_categories: &[HeapCategory],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
    ) -> Result<cranelift_module::FuncId, CranelispError> {
        // Mono-discriminated span name (FIXME 0347 defect 1).
        let wrapper_name = format!(
            "__curry_{target_name}_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );

        // Signature: (env_ptr, remaining_0..remaining_k) -> i64
        let param_count = 1 + remaining_count; // env_ptr + remaining args
        let mut sig = self.module.make_signature();
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_function(&wrapper_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare auto-curry wrapper: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Build the wrapper body in a separate codegen context.
        let mut ctx = self.module.make_context();
        let mut func_ctx = FunctionBuilderContext::new();
        ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let block_params = builder.block_params(entry).to_vec();
        let env_ptr = block_params[0];
        let remaining_args: Vec<Value> = block_params[1..].to_vec();

        // Load captured args from env and inc heap-typed captures.
        // The wrapper must inc before passing to the consuming callee,
        // so the closure env's reference stays intact across calls.
        let mut all_args = Vec::with_capacity(applied_count + remaining_count);
        for (i, category) in arg_categories.iter().enumerate().take(applied_count) {
            let cap_val = heap::heap_load(
                &mut builder,
                env_ptr,
                HeapClosure::capture_offset(i),
            );
            // Inc heap-typed captures before passing to consuming callee.
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut builder, cap_val);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut builder, cap_val);
                }
                HeapCategory::NeverHeap => {}
            }
            all_args.push(cap_val);
        }
        all_args.extend_from_slice(&remaining_args);

        // Call the target function. For trait methods resolved to inline
        // builtins (e.g., + → add-i64), emit the IR directly in the wrapper.
        // For extern primitives, emit an extern call. For user functions,
        // use emit_wrapper_call (handles Batch/Interactive modes).
        let result = self.emit_curry_target_call(
            &mut builder,
            target_name,
            &all_args,
            span,
            trait_resolution,
        )?;

        builder.ins().return_(&[result]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(wrapper_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define auto-curry wrapper: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(wrapper_func_id)
    }

    /// Build drop glue for an auto-curry closure's captured arguments.
    ///
    /// For each heap-typed capture, loads from the closure env at its offset
    /// and emits `rc_dec`. Returns `None` if no captures are heap-typed.
    fn build_auto_curry_drop_glue(
        &mut self,
        arg_categories: &[HeapCategory],
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id;

        // Collect indices of heap-typed captures.
        let heap_indices: Vec<(usize, HeapCategory)> = arg_categories
            .iter()
            .enumerate()
            .filter_map(|(i, cat)| match cat {
                HeapCategory::AlwaysHeap | HeapCategory::Mixed => Some((i, *cat)),
                HeapCategory::NeverHeap => None,
            })
            .collect();

        if heap_indices.is_empty() {
            return Ok(None);
        }

        let glue_name = format!(
            "runtime/curry_drop_glue_{}_{}",
            span.start, span.end
        );

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // closure ptr

        let glue_func_id = self
            .module
            .declare_function(&glue_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare auto-curry drop glue: {e}"),
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

        // For each heap-typed capture, load and dec.
        for (cap_idx, category) in &heap_indices {
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
                message: format!("failed to define auto-curry drop glue: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(Some(glue_func_id))
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
            for (p, _) in params {
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
        Expr::ParBind { bindings, body, .. } => {
            // Same as Let: each binding may reference earlier ones
            let mut extended = bound.clone();
            for (name, val_expr) in bindings {
                collect_free_vars(val_expr, &extended, free, seen);
                extended.insert(name.clone());
            }
            collect_free_vars(body, &extended, free, seen);
        }
        Expr::ConstrADT { fields, .. } => {
            for f in fields {
                collect_free_vars(f, bound, free, seen);
            }
        }
        Expr::StringLit { .. }
        | Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. } => {}
    }
}

/// Check if a primitive name is an extern (call-based) primitive,
/// mirroring the `is_extern_primitive` function in apply.rs.
/// Used by the auto-curry wrapper which compiles in a separate context.
fn is_extern_primitive_in_wrapper(name: &str) -> bool {
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
            | "sconcat"
            | "quote-sexp"
            | "substring"
            | "char-at"
            | "split"
            | "join"
            | "replace"
            | "trim"
            | "starts-with?"
            | "ends-with?"
            | "contains?"
            | "to-upper"
            | "to-lower"
            | "cranelisp_trace_name"
            | "cranelisp_trace_params"
            | "cranelisp_trace_result"
            | "cranelisp_trace_children"
            | "cranelisp_trace_nanos"
            | "cranelisp_trace_first_child_nanos"
    )
}

/// Emit an extern function call inside a wrapper function body.
/// Used by auto-curry wrappers to call extern primitives like `str-eq`.
fn emit_extern_call_in_wrapper(
    builder: &mut FunctionBuilder,
    module: &mut dyn Module,
    name: &str,
    arg_vals: &[Value],
    span: Span,
) -> Result<Value, CranelispError> {
    let mut sig = module.make_signature();
    for _ in arg_vals {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));

    let func_id = module
        .declare_function(name, Linkage::Import, &sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare extern function '{name}' in wrapper: {e}"),
            location: ErrorLocation::from_span(span),
        })?;

    let local_func = module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(local_func, arg_vals);
    Ok(builder.inst_results(call)[0])
}

// --- Sparkability analysis for lenient evaluation ---
//
// See design/backend/lenient-eval.md §2 for the algorithm.

/// Whether lenient evaluation is disabled via CRANELISP_NO_LENIENT=1.
static LENIENT_DISABLED: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| {
        std::env::var("CRANELISP_NO_LENIENT").is_ok_and(|v| v == "1")
    });

/// Known-cheap builtins that are not worth sparking.
/// Single-instruction or near-single-instruction at the hardware level.
const CHEAP_BUILTINS: &[&str] = &[
    "+", "-", "*", "/", "=", "<", ">", "<=", ">=", "not", "and", "or",
];

/// Find indices of sparkable bindings in a `let` block.
///
/// A binding is sparkable if:
/// 1. Its free variables do not reference any earlier binding in the same block.
/// 2. It is a non-trivial function call (not a cheap builtin, literal,
///    constructor, or var ref).
///
/// `constructors` is the set of known ADT constructor names.
///
/// Returns an empty vec if fewer than 2 sparkable bindings are found.
pub(crate) fn find_sparkable_bindings(
    bindings: &[(Symbol, Expr)],
    constructors: &HashSet<Symbol>,
) -> Vec<usize> {
    let mut bound_names: HashSet<Symbol> = HashSet::new();
    let mut sparkable: Vec<usize> = Vec::new();

    // Use the canonical free_vars_expr from cranelisp-types (I4 review finding:
    // eliminates duplicate free-variable traversal).
    let empty_globals = HashSet::new();
    for (i, (name, val_expr)) in bindings.iter().enumerate() {
        let fv = cranelisp_types::free_vars_expr(val_expr, &empty_globals);
        // Filter to only those free vars that are bound by earlier bindings
        // in this let block (not globals or outer scope).
        let depends_on_earlier = fv.iter().any(|v| bound_names.contains(v));

        if !depends_on_earlier && is_worth_sparking(val_expr, constructors) {
            sparkable.push(i);
        }

        bound_names.insert(name.clone());
    }

    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}

/// Check if an expression is worth sparking (non-trivial function call).
///
/// Excludes: cheap builtins (+, -, etc.), data constructors (Some, Cons),
/// literals, variable references.
fn is_worth_sparking(expr: &Expr, constructors: &HashSet<Symbol>) -> bool {
    match expr {
        Expr::Apply { callee, .. } => {
            if let Expr::Var { name, .. } = callee.as_ref() {
                // Cheap builtins and constructors are not worth sparking.
                !CHEAP_BUILTINS.contains(&name.as_ref())
                    && !constructors.contains(name)
            } else {
                // Non-variable callee (computed function) — conservatively spark.
                true
            }
        }
        // Non-Apply expressions are not worth sparking.
        _ => false,
    }
}

#[cfg(test)]
mod sparkability_tests {
    // ===== FIXME 0135 harvest (backend part): the sparkability-analysis
    // assertions from the quarantined `tests/legacy/lenient.rs`. The
    // spark-*execution* parts of that file (value-correctness via
    // `repl_eval`, the `CRANELISP_NO_LENIENT` process-global env-var, IO
    // scheduling) need the int worker/session and remain in 0135's
    // 0109-adjacent remainder. These tests exercise the pure
    // `find_sparkable_bindings` analysis pass directly — no session, no
    // runtime, no env-var — per `memory/project_test_strategy.md`. =====

    use super::find_sparkable_bindings;
    use cranelisp_types::{Expr, Span, Symbol};
    use std::collections::HashSet;

    fn sym(s: &str) -> Symbol {
        Symbol::from(s)
    }

    fn span() -> Span {
        Span::new(0, 0)
    }

    /// A function-call binding `(f arg)` against a named callee.
    fn call(callee: &str) -> Expr {
        Expr::Apply {
            callee: Box::new(Expr::var(sym(callee), span())),
            args: vec![],
            span: span(),
            resolved_call: None,
            inferred_type: None,
        }
    }

    /// A function-call binding that references `dep_var` as an argument, so
    /// it depends on any earlier binding named `dep_var`.
    fn call_with_arg(callee: &str, dep_var: &str) -> Expr {
        Expr::Apply {
            callee: Box::new(Expr::var(sym(callee), span())),
            args: vec![Expr::var(sym(dep_var), span())],
            span: span(),
            resolved_call: None,
            inferred_type: None,
        }
    }

    // spec: design/backend/lenient-eval.md §2 — two independent calls are sparkable
    //
    // Two data-independent non-trivial function calls clear the
    // min-2-sparkable threshold and are both returned.
    #[test]
    fn two_independent_calls_are_sparkable() {
        let bindings = vec![(sym("a"), call("compute")), (sym("b"), call("derive"))];
        let ctors = HashSet::new();
        assert_eq!(find_sparkable_bindings(&bindings, &ctors), vec![0, 1]);
    }

    // spec: design/backend/lenient-eval.md §2 — below the min-2 threshold yields nothing
    //
    // A single sparkable binding (the other is a cheap builtin) is below the
    // threshold; the analysis returns an empty set (sequential codegen).
    #[test]
    fn single_sparkable_below_threshold_returns_empty() {
        let bindings = vec![(sym("a"), call("compute")), (sym("b"), call("+"))];
        let ctors = HashSet::new();
        assert!(find_sparkable_bindings(&bindings, &ctors).is_empty());
    }

    // spec: design/backend/lenient-eval.md §2 — dependent bindings are not sparkable
    //
    // The second binding references the first (`b` uses `a`), so it depends on
    // an earlier binding and is excluded — leaving fewer than 2, so empty.
    #[test]
    fn dependent_binding_is_not_sparkable() {
        let bindings = vec![
            (sym("a"), call("compute")),
            (sym("b"), call_with_arg("derive", "a")),
        ];
        let ctors = HashSet::new();
        assert!(
            find_sparkable_bindings(&bindings, &ctors).is_empty(),
            "a dependent binding must drop the set below the spark threshold"
        );
    }

    // spec: design/backend/lenient-eval.md §2 — cheap builtins are not worth sparking
    //
    // Negative guard: arithmetic/comparison builtins (`+`, `<`, ...) are
    // single-instruction and excluded even when there are two of them.
    #[test]
    fn cheap_builtins_are_not_sparkable() {
        let bindings = vec![(sym("a"), call("+")), (sym("b"), call("<"))];
        let ctors = HashSet::new();
        assert!(
            find_sparkable_bindings(&bindings, &ctors).is_empty(),
            "cheap builtins must not be sparked"
        );
    }

    // spec: design/backend/lenient-eval.md §2 — ADT constructors are not worth sparking
    //
    // Negative guard: calls whose callee is a known constructor name are
    // excluded (alloc+tag, not real work). With both bindings being
    // constructors, nothing is sparkable.
    #[test]
    fn constructors_are_not_sparkable() {
        let mut ctors = HashSet::new();
        ctors.insert(sym("Some"));
        ctors.insert(sym("Cons"));
        let bindings = vec![(sym("a"), call("Some")), (sym("b"), call("Cons"))];
        assert!(
            find_sparkable_bindings(&bindings, &ctors).is_empty(),
            "constructor calls must not be sparked"
        );
    }

    // spec: design/backend/lenient-eval.md §2 — literals and var-refs are not sparkable
    //
    // Negative guard: non-Apply expressions (literals, bare variable
    // references) are never sparkable regardless of count.
    #[test]
    fn literals_and_var_refs_are_not_sparkable() {
        let bindings = vec![
            (sym("a"), Expr::IntLit { value: 1, span: span(), inferred_type: None }),
            (sym("b"), Expr::var(sym("x"), span())),
        ];
        let ctors = HashSet::new();
        assert!(find_sparkable_bindings(&bindings, &ctors).is_empty());
    }

    // spec: design/backend/lenient-eval.md §2 — independence is positional, not global
    //
    // A later binding that does NOT reference an earlier one stays sparkable;
    // mixing a sparkable independent pair around a dependent middle binding
    // returns exactly the independent indices.
    #[test]
    fn mixed_independent_and_dependent_returns_only_independent() {
        let bindings = vec![
            (sym("a"), call("compute")),
            (sym("b"), call_with_arg("derive", "a")), // depends on a → excluded
            (sym("c"), call("evaluate")),             // independent → sparkable
        ];
        let ctors = HashSet::new();
        // a (idx 0) and c (idx 2) are independent + non-trivial → both sparked.
        assert_eq!(find_sparkable_bindings(&bindings, &ctors), vec![0, 2]);
    }
}

#[cfg(test)]
mod par_codegen_tests {
    // ===== FIXME 0135 harvest (backend IO-scheduling slice): the Par-node
    // CLIF-emission kernel of the quarantined `tests/legacy/lenient.rs`
    // `test_io_schedule_*` GAP tests. Those 5 legacy tests assert RUNTIME
    // scheduling behaviour (commutative pair → concurrent dispatch; Sequential
    // → ordered; data-dependent → no Par; ResourceSerial same/diff token) which
    // is **not e2e-witnessable without the test-capture commutative /
    // ResourceSerial DLL fixture** — that runtime-dispatch slice is the
    // `cranelisp-platform` co-owner's (per `s82-harvest-trace_lenient_jit.md`).
    // The BACKEND-portable kernel is the **Par-node CLIF emission**: when an
    // `Expr::ParBind` reaches codegen, `compile_par_bind` must emit the
    // documented IO-tree structure (a `IO_TAG_PAR=3` node holding N branch
    // pointers, wrapped by a `IO_TAG_BIND=2` node). This guard pins that
    // structure at the CLIF layer — independent of the trampoline / DLL.
    //
    // The complementary decision pass — whether a `bind!` chain BECOMES a
    // `ParBind` (scheduling-class + data-independence analysis) — runs upstream
    // of backend (frontend/typecheck build the node), so it is not a backend
    // unit; the backend's contract is "given a ParBind, emit a Par node".

    use crate::jit::Jit;
    use cranelisp_types::{Defn, DefnVariant, Expr, Span, Symbol, Type, Visibility};
    use std::collections::HashMap;

    /// Compile a zero-arg `defn` whose body is the given `Expr`, returning the
    /// emitted CLIF-IR text. Branches need only be structurally valid for
    /// `compile_expr` (we use int literals as stand-in IO-tree pointers — the
    /// guard is the emitted Par-node SHAPE, not its runtime IO semantics).
    fn clif_of_body(body: Expr) -> String {
        let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
        jit.declare_intrinsics().expect("intrinsics declare");

        let name = Symbol::from("par_codegen_probe");
        let defn = Defn {
            name: name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body,
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };

        let func_ids = jit.declare_functions(&[&defn]).expect("declare");
        let func_arities: HashMap<Symbol, usize> = HashMap::new();
        let symbol_tables: dashmap::DashMap<
            cranelisp_types::ModuleFullPath,
            cranelisp_types::SymbolTable,
        > = dashmap::DashMap::new();
        let module_path = cranelisp_types::ModuleFullPath::from("user");
        symbol_tables.insert(
            module_path.clone(),
            cranelisp_types::SymbolTable::new(module_path.clone()),
        );
        let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
        let compile_ctx = jit.build_compile_context(
            &func_ids,
            &func_arities,
            &symbol_tables,
            &module_aliases,
            module_path,
        );
        jit.compile_defn(&defn, compile_ctx)
            .expect("compile")
            .clif_ir
    }

    fn int_lit(v: i64) -> Expr {
        Expr::IntLit {
            value: v,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        }
    }

    // spec: spec/10-io.md §10.12.1 + design/backend/io-scheduling.md §4 —
    //       an `Expr::ParBind` with N independent bindings emits a Par node
    //       (IO_TAG_PAR=3) carrying N branch pointers, wrapped by a Bind node
    //       (IO_TAG_BIND=2). Backend kernel of the legacy
    //       `test_io_schedule_commutative_pair_par` reg-guard.
    #[test]
    fn par_bind_emits_par_node_with_branch_count() {
        let body = Expr::ParBind {
            bindings: vec![
                (Symbol::from("a"), int_lit(10)),
                (Symbol::from("b"), int_lit(20)),
            ],
            body: Box::new(int_lit(0)),
            span: Span::SYNTHETIC,
            inferred_type: None,
        };
        let clif = clif_of_body(body);

        // The Par node stores tag=3 and count=2 (two branches). The Bind
        // wrapper stores tag=2. We assert the structural constants are emitted
        // (iconst.i64 3 for the Par tag, iconst.i64 2 for the Bind tag /
        // branch count). The exact CLIF formatting is `v_ = iconst.i64 N`.
        assert!(
            clif.contains("iconst.i64 3"),
            "ParBind codegen must emit the IO_TAG_PAR=3 marker; CLIF:\n{clif}"
        );
        assert!(
            clif.contains("iconst.i64 2"),
            "ParBind codegen must emit the IO_TAG_BIND=2 / branch-count=2 \
             marker; CLIF:\n{clif}"
        );
        // The Par node allocates payload (tag + count + N branches) and the
        // continuation closure — at least two heap allocations are emitted.
        let alloc_calls = clif.matches("call ").count();
        assert!(
            alloc_calls >= 2,
            "ParBind codegen must emit Par-node + continuation allocations \
             (>=2 calls); found {alloc_calls}. CLIF:\n{clif}"
        );
    }

    // spec: spec/10-io.md §10.12.1 + design/backend/io-scheduling.md §4 —
    //       the Par node's branch count tracks the number of bindings. A
    //       three-binding ParBind emits count=3. Pins that the count store is
    //       binding-driven, not a constant — guards against a regression that
    //       hard-codes a 2-branch Par.
    #[test]
    fn par_bind_branch_count_tracks_bindings() {
        let body = Expr::ParBind {
            bindings: vec![
                (Symbol::from("a"), int_lit(1)),
                (Symbol::from("b"), int_lit(2)),
                (Symbol::from("c"), int_lit(3)),
            ],
            body: Box::new(int_lit(0)),
            span: Span::SYNTHETIC,
            inferred_type: None,
        };
        let clif = clif_of_body(body);
        // count=3 stored as the Par node's first field.
        assert!(
            clif.contains("iconst.i64 3"),
            "three-binding ParBind must store branch count=3; CLIF:\n{clif}"
        );
    }

    // spec: spec/10-io.md §10.12.2 + design/backend/io-scheduling.md §4 —
    //       NEGATIVE guard. A plain sequential `let` (an `Expr::Let`, NOT an
    //       `Expr::ParBind`) must NOT emit an IO_TAG_PAR=3 Par node — its
    //       bindings are evaluated in source order with no concurrent dispatch.
    //       This is the backend-portable kernel of the legacy
    //       `test_io_schedule_sequential_no_par` GAP: for a `Sequential`-class
    //       chain the scheduler builds an ordinary `Let`, and the backend's
    //       contract is that ordinary `Let` codegen carries no Par marker.
    //       (The scheduling *decision* — which class becomes a `ParBind` — is
    //       upstream of backend; this guard pins that the no-Par INPUT yields
    //       no-Par OUTPUT.) Int-literal bindings are used so the sparkability
    //       analysis is a no-op (literals are never sparkable) and the path is
    //       deterministically `compile_let_sequential`.
    #[test]
    fn sequential_let_emits_no_par_node() {
        let body = Expr::Let {
            bindings: vec![
                (Symbol::from("a"), int_lit(10)),
                (Symbol::from("b"), int_lit(20)),
            ],
            body: Box::new(int_lit(0)),
            span: Span::SYNTHETIC,
            inferred_type: None,
        };
        let clif = clif_of_body(body);
        // IO_TAG_PAR=3 is the Par-node tag. A sequential `let` must never
        // store it. (Other `iconst.i64 3` could in principle arise from an
        // unrelated constant, but with int-literal bindings of 10/20/0 the
        // only way `3` appears is a Par tag — none should be emitted.)
        assert!(
            !clif.contains("iconst.i64 3"),
            "a sequential `let` must NOT emit an IO_TAG_PAR=3 Par node; CLIF:\n{clif}"
        );
    }
}
