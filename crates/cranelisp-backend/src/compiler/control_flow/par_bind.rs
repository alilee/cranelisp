// Par-bind codegen: IO scheduling node emission.
//
// Compiles an `Expr::ParBind` into the documented IO-tree structure (a Par
// node holding N branch pointers, wrapped by a Bind node linking Par to a
// continuation closure). The continuation closure is built here and nowhere
// else. See `design/backend/io-scheduling.md §4`.

use std::collections::HashSet;

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{ConcreteType, CranelispError, ErrorLocation, MonoExpr, Span, Symbol};

use crate::heap::{self, HeapAdt, HeapClosure};

use crate::compiler::signature_heap_category;
use super::{find_free_vars, FnCompiler};

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
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
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
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
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
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

        // Define the continuation function body.
        self.define_par_cont_body(cont_func_id, &captures, bindings, body, sig, span)?;

        // Allocate the continuation closure at the call site.
        self.alloc_par_cont_closure(cont_func_id, &captures, span)
    }

    /// Define the par-bind continuation function body in a separate Cranelift
    /// context. Loads captures from `env_ptr`, loads the N results from
    /// `results_ptr` and binds them to the binding names, compiles `body`, decs
    /// the results buffer, and returns the body result.
    fn define_par_cont_body(
        &mut self,
        cont_func_id: cranelift_module::FuncId,
        captures: &[Symbol],
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
        sig: cranelift::codegen::ir::Signature,
        span: Span,
    ) -> Result<(), CranelispError> {
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
            for cap_name in captures {
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
                let inner_ty = match val_expr.ty() {
                    ConcreteType::ADT(fqtn, args)
                        if fqtn.name.as_ref() == "IO" && !args.is_empty() =>
                    {
                        args[0].to_type()
                    }
                    other => other.to_type(),
                };
                inner.variable_types.insert(name.clone(), inner_ty);
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

        Ok(())
    }

    /// Allocate the par-bind continuation closure at the call site, storing the
    /// code pointer, drop glue, and the captured values (inc'ing heap-typed
    /// captures). Returns the closure base pointer (rc=1).
    ///
    /// `pub(crate)` so the sibling `launch.rs` continuation builder reuses the
    /// identical closure-site emission (Principle 7) — the launch continuation is
    /// a standard bind continuation closure differing only in its body.
    pub(crate) fn alloc_par_cont_closure(
        &mut self,
        cont_func_id: cranelift_module::FuncId,
        captures: &[Symbol],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

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
        let drop_glue = self.build_closure_drop_glue(captures, span)?;
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
                    let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
                    self.emit_capture_inc(category, cap_val);
                }
            }
        }

        Ok(closure_ptr)
    }
}
