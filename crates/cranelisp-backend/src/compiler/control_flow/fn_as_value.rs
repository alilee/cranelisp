// First-class-function lowering.
//
// Every path that turns a *name* or a *partial application* into a heap closure
// with a generated wrapper: named-fn / trait-method value-position wrappers,
// the wrapper-call emission tail, and auto-curry (the "some-args-applied"
// sibling of the "zero-args-applied" fn-as-value case). The wrapper-context
// extern helpers live here alongside their sole caller, `emit_curry_target_call`.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, MonoExpr, ResolvedCall, Span, Symbol};

use crate::heap::{self, HeapCategory, HeapClosure};
use crate::primitives_inline;

use super::{emit_capture_inc_into, FnCompiler};

#[cfg(test)]
mod ctor_value_tests;

/// Borrowed-builder form of `FnCompiler::emit_adt_construct` (apply.rs): emit an
/// ADT construction (`alloc` + tag + field stores) onto an arbitrary `builder`,
/// used to inline-construct a data constructor inside a generated wrapper body
/// (which builds in a separate Cranelift context, not `self.builder`). Single
/// source of the construction shape — RC-identical: fields arrive owned and are
/// stored with no inc, exactly as `emit_adt_construct`.
fn emit_adt_construct_into<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    alloc_id: cranelift_module::FuncId,
    tag: usize,
    field_vals: &[Value],
    _span: Span,
) -> Result<Value, CranelispError> {
    use crate::heap::HeapAdt;

    if field_vals.is_empty() {
        // Nullary constructor: bare tag, no heap allocation.
        return Ok(builder.ins().iconst(types::I64, tag as i64));
    }

    let payload_size = HeapAdt::payload_size(field_vals.len()) as i64;
    let base_ptr = heap::emit_alloc(builder, module, alloc_id, payload_size);

    let tag_val = builder.ins().iconst(types::I64, tag as i64);
    heap::heap_store(builder, tag_val, base_ptr, HeapAdt::TAG_OFFSET);

    for (i, &field_val) in field_vals.iter().enumerate() {
        heap::heap_store(builder, field_val, base_ptr, HeapAdt::field_offset(i));
    }

    Ok(base_ptr)
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
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
        // direct call — cheaper and avoids an unnecessary GOT dereference. User
        // ADT constructors have a compiled constructor function here, so this
        // arm covers `(let [f Box] (f 7))` for user types.
        if let Some(target_id) = self.ctx.func_ids.get(target_name) {
            let target_ref =
                self.module.declare_func_in_func(*target_id, builder.func);
            let call = builder.ins().call(target_ref, user_params);
            return Ok(builder.inst_results(call)[0]);
        }

        // Data constructor as a first-class value with NO callable function in
        // this unit — e.g. a PRIMITIVE constructor (`Some` / `None` from the
        // primitives bootstrap), whose GOT slot is NOT a callable constructor
        // body. Calling through it (the GOT-indirect path below) jumps to a
        // non-function and SIGSEGVs. Instead, inline-construct the ADT directly
        // in the wrapper body — `(let [f Some] (f 42))` (spec §5.2.7 "data
        // constructors are functions"). This is RC-identical to direct
        // construction (`emit_adt_construct`): the wrapper's params arrive owned
        // (consuming convention) and are stored into the new ADT with no inc.
        if let Some((_fqtn, ctor_info)) = self.ctx.lookup_constructor(target_name.as_ref()) {
            let alloc_id =
                self.ctx
                    .alloc_func_id
                    .ok_or_else(|| CranelispError::CodegenError {
                        message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                        location: ErrorLocation::from_span(span),
                    })?;
            return emit_adt_construct_into(
                builder,
                self.module,
                alloc_id,
                ctor_info.tag,
                user_params,
                span,
            );
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
        args: &[MonoExpr],
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
            .map(|arg| HeapCategory::classify(arg.ty(), Some(self.ctx.symbol_tables)))
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
            self.emit_capture_inc(arg_categories[i], val);
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
            emit_capture_inc_into(&mut builder, self.module, *category, cap_val);
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
