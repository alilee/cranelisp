// First-class-function lowering.
//
// Every path that turns a *name* or a *partial application* into a heap closure
// with a generated wrapper: named-fn / trait-method value-position wrappers,
// the wrapper-call emission tail, and auto-curry (the "some-args-applied"
// sibling of the "zero-args-applied" fn-as-value case). The wrapper-context
// extern helpers live here alongside their sole caller, `emit_curry_target_call`.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{
    ConcreteType, CranelispError, ErrorLocation, FQSymbol, ModuleFullPath, MonoExpr, ResolvedCall,
    Span, Symbol, Type,
};

use crate::compiler::entry_convention::{EntryConvention, ParamKind};
use crate::heap::{self, HeapCategory, HeapClosure};
use crate::primitives_inline;

use super::{CaptureRelease, CaptureReleaseKind, FnCompiler, emit_capture_inc_into};

/// If `fn_type` is a `Fn` whose first parameter is `(Vec t)`, return `t`.
///
/// The per-site element-type recovery for the vec-query wrapper emission
/// (`design/backend/ownership-codegen.md` §12.7): a value-position `Var`
/// naming `vec-get`/`vec-set`/`vec-push` carries a concrete post-mono
/// `inferred_type` (S84 ruling) like `(Fn [(Vec Int) Int] Int)`, whose first
/// param names the element type the wrapper's RC emission needs — exactly the
/// knowledge a primitives-crate extern body cannot have (why the entries'
/// GOT slots are NULL and the wrapper is the fix location).
fn vec_query_elem_from_fn_type(fn_type: Option<&Type>) -> Option<Type> {
    if let Some(Type::Fn(params, _)) = fn_type
        && let Some(Type::ADT(fqtn, args)) = params.first()
        && fqtn.name.as_ref() == "Vec"
        && args.len() == 1
    {
        return Some(args[0].clone());
    }
    None
}

#[cfg(test)]
mod ctor_value_tests;

// (The auto-curry drop-glue naming-identity test folded into the ONE
// consolidated `resolution::tests::drop_glue_naming_identity_*` battery at
// S111 R6 §4.4 — the naming fns now live in `resolution.rs`, their identity
// home.)

// Relocated crate-root fn-as-value + value-use tests (FIXME 0495 step 1).
#[cfg(test)]
mod value_use_tests;

#[cfg(test)]
mod keyed_miss_tests;

#[cfg(test)]
mod entry_adaptation_tests;

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
    ///
    /// S110 W2 (S12): the resolver gate (`resolve_is_callable_target`) is replaced
    /// by a keyed [`CompileContext::is_callable_target_at`] read off the Var's
    /// carrier, plus the current-unit `func_ids` fast-path (a local map, not a
    /// resolver). `is_callable_target` (FIXME 0476) covers both slot-dispatched
    /// callables AND inline-dispatched vec-query primitives (`PrimitiveBody::
    /// Inline`, no slot), so a bare inline vec primitive as a value is still a
    /// known function. A `None` carrier (a genuinely-unresolved name, or a
    /// slot-less generic template) reports `false` — the caller falls to the 0585
    /// backstop / undefined-variable arm (Rev-2, no scan fallback).
    pub(crate) fn is_known_function(&self, name: &Symbol, target_fq: Option<&FQSymbol>) -> bool {
        self.ctx.func_ids.contains_key(name)
            || target_fq.is_some_and(|fq| self.ctx.is_callable_target_at(fq))
    }

    /// Wrap a named top-level function as a zero-capture closure.
    ///
    /// Generates a wrapper function with signature `(env_ptr, params...) -> i64`
    /// that ignores env_ptr and calls the real function directly.
    /// Allocates a closure `[header | code_ptr]` with zero captures.
    ///
    /// `fn_type` is the value-use site's concrete `Fn` type (the Var's
    /// `inferred_type`) — consumed only to recover the vec-query element type
    /// for the §12.7 wrapper emission; `None` elsewhere is harmless.
    pub(crate) fn compile_fn_as_value(
        &mut self,
        name: &Symbol,
        span: Span,
        fn_type: Option<&Type>,
        // S110 W2 (§4): the Var's terminal STORAGE key — drives the S14 arity
        // read and the S10/S15/S16/S17 wrapper-body keyed reads.
        target_fq: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        // S110 W2 (S14): arity read off the carrier's fetched entry
        // (`param_names.len()`), replacing `resolve_func_arity`. The current-unit
        // `func_arities` map stays as the fast-path (a local map, not a resolver).
        let arity = self
            .ctx
            .func_arities
            .get(name)
            .copied()
            .or_else(|| target_fq.and_then(|fq| self.ctx.arity_at(fq)))
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("unknown arity for function: {name}"),
                location: ErrorLocation::from_span(span),
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

        let vec_elem = vec_query_elem_from_fn_type(fn_type);
        let ctor_result = fn_type
            .and_then(|ty| ConcreteType::from_type(ty).ok())
            .and_then(|ty| match ty {
                ConcreteType::Fn(_, result) => Some(*result),
                _ => None,
            });
        self.compile_fn_wrapper_body(
            wrapper_func_id,
            name,
            arity,
            span,
            vec_elem.as_ref(),
            ctor_result.as_ref(),
            target_fq,
        )?;

        // Allocate a closure with zero captures: [header | code_ptr].
        let payload_size = HeapClosure::payload_size(0) as i64;
        let base_ptr = heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size);

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
        fn_type: Option<&Type>,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        // The callable name carried by the resolution — used only for a stable,
        // unique wrapper symbol name. The actual dispatch target is chosen by
        // `emit_curry_target_call` from `resolved`.
        let target_name: Symbol = match resolved {
            ResolvedCall::TraitMethod { mangled_name, .. } => Symbol::from(mangled_name.as_ref()),
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

        let mut builder = FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let block_params = builder.block_params(entry).to_vec();
        let user_args: Vec<Value> = block_params[1..].to_vec(); // skip env_ptr

        // Dispatch through the SAME path direct application uses. S110 W2: the
        // TraitMethod / BuiltinFn arms self-derive their carrier from `resolved`
        // (the mangled entry's `impl_module`; a primitive's `primitives` home), so
        // no plain-fn carrier is threaded here (`None`).
        let vec_elem = vec_query_elem_from_fn_type(fn_type);
        let result = self.emit_curry_target_call(
            &mut builder,
            &target_name,
            &user_args,
            span,
            Some(resolved),
            vec_elem.as_ref(),
            None,
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
        let base_ptr = heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size);

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
    ///
    /// `vec_elem` is the vec-query element type recovered from the value-use
    /// site (`vec_query_elem_from_fn_type`), threaded to `emit_wrapper_call`'s
    /// vec-query arm (§12.7).
    fn compile_fn_wrapper_body(
        &mut self,
        func_id: cranelift_module::FuncId,
        target_name: &Symbol,
        arity: usize,
        span: Span,
        vec_elem: Option<&Type>,
        ctor_result: Option<&ConcreteType>,
        // S110 W2 (§4): the target's STORAGE key — drives `emit_wrapper_call`'s
        // S10/S15/S16/S17 keyed reads.
        target_fq: Option<&FQSymbol>,
    ) -> Result<(), CranelispError> {
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();

        // Signature: (env_ptr, params...) -> i64
        for _ in 0..1 + arity {
            inner_ctx
                .func
                .signature
                .params
                .push(AbiParam::new(types::I64));
        }
        inner_ctx
            .func
            .signature
            .returns
            .push(AbiParam::new(types::I64));

        let mut builder = FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let block_params = builder.block_params(entry_block).to_vec();
        let user_params: Vec<Value> = block_params[1..].to_vec(); // skip env_ptr

        let result = self.emit_wrapper_call(
            &mut builder,
            target_name,
            &user_params,
            span,
            vec_elem,
            ctor_result,
            target_fq,
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

    /// §3.4 adaptation algebra (`design/backend/ownership-codegen.md` §3.4): emit
    /// the per-edge delta between the closure-protocol Decision-24 convention
    /// (every param arrives owned/consumed, result is Fresh/owned) and the
    /// target's derived [`EntryConvention`], onto a wrapper's borrowed `builder`
    /// AFTER the target call returns. ONE helper, reached by every wrapper
    /// target call — [`Self::emit_wrapper_call`] (the fn-as-value /
    /// trait-method-value wrapper bodies and the auto-curry GOT arm) and the
    /// auto-curry direct-extern arms — no per-site reinvention (Principle 7), no
    /// stacked adapters.
    ///
    /// - a `Borrow` param ⇒ **post-call dec** of the received-owned arg: the
    ///   wrapper owns its params (closure protocol) but the callee borrowed (did
    ///   not dec) that position, so the wrapper releases it. Only a compiled
    ///   body derives `Borrow`; an extern shim consumes, whatever it declares.
    /// - every other position ⇒ pass-through.
    ///
    /// Guarded RC ops throughout (layout-safe for AlwaysHeap and Mixed alike).
    /// With analysis off no body carries a non-conservative summary, so nothing
    /// is emitted and the wrapper body is byte-identical (§2.2).
    ///
    /// **No result materialization inc (FIXME 0522 reconcile, option B).** A
    /// moded callee ALWAYS returns its `ProjectionOf`/`AliasOf` result carrying an
    /// owned reference — its own `vec-get` inc, an accessor call, or
    /// `protect_return_value` (`return_is_fresh_by_summary` keeps the protect for
    /// every non-`Fresh` result; the §3.3 in-frame elision is confined to the
    /// consumer seam and never crosses a function-return boundary, so a returned
    /// projection is never un-inc'd). The wrapper therefore owes NO result inc: the
    /// callee's materialization is the single owned reference, and the FIXME 0522
    /// double-count (callee-protect AND wrapper-adaptation both inc'ing a
    /// `ProjectionOf` result) can no longer arise. The prior wrapper inc — dormant
    /// but a latent over-retain, and mis-ordered against the Borrowed decs — is
    /// removed. The result already owns a reference, so the Borrowed-param decs
    /// below (which may release the root the result projects into) cannot dangle
    /// it — the FIXME's ordering hazard dissolves with the inc.
    fn emit_d24_adaptation(
        &mut self,
        builder: &mut FunctionBuilder,
        convention: &EntryConvention,
        args: &[Value],
    ) {
        let dealloc_id = self.ctx.dealloc_func_id;
        for (i, &arg) in args.iter().enumerate() {
            match convention.param(i) {
                ParamKind::Borrow => {
                    heap::emit_rc_dec_guarded(builder, self.module, arg, dealloc_id, None, true)
                }
                ParamKind::Consume | ParamKind::NoReference => {}
            }
        }
    }

    /// Call the extern `name` from a wrapper body by name and adapt the call
    /// against the derived convention of its `{primitives, name}` entry; an
    /// absent entry consumes.
    fn emit_adapted_extern_call_in_wrapper(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &str,
        args: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let convention = self.ctx.entry_convention_at(Some(&FQSymbol {
            module: ModuleFullPath::from("primitives"),
            symbol: Symbol::from(name),
        }));
        let result = emit_extern_call_in_wrapper(builder, self.module, name, args, span)?;
        self.emit_d24_adaptation(builder, &convention, args);
        Ok(result)
    }

    /// Emit the call instruction inside a wrapper function body.
    ///
    /// Prefers a direct `call` via FuncId when the target is in the current
    /// unit's `func_ids` map. Otherwise emits a GOT-indirect `call_indirect`
    /// using the uniform `__cranelisp_got_{module}` data-symbol strategy
    /// (design/backend/compile-to-module.md §12).
    ///
    /// §3.5 R2 wrapper coupling: the target call is adapted with
    /// [`Self::emit_d24_adaptation`] against the target's derived entry
    /// convention, so the closure-reachable code pointer (this wrapper) is
    /// Decision-24 conformant. THE INVARIANT: every code pointer reachable from
    /// a closure value targets a Decision-24-conformant entry; a moded body is
    /// reachable ONLY through statically-resolved call sites (§3.1) and these
    /// adapter wrapper bodies — its address never escapes into a closure
    /// unadapted. A consuming target (every extern shim, and a body with no
    /// borrowed parameter) needs no adaptation, so nothing is emitted.
    fn emit_wrapper_call(
        &mut self,
        builder: &mut FunctionBuilder,
        target_name: &Symbol,
        user_params: &[Value],
        span: Span,
        vec_elem: Option<&Type>,
        ctor_result: Option<&ConcreteType>,
        // S110 W2 (§4): the target's STORAGE key — drives the S15 summary, S16
        // ctor-as-value, S17 vec-query, and S10 GOT-entry keyed reads. `None` for
        // a target with no carrier (the current-unit `func_ids` fast-path below
        // covers same-unit fns; a `None` reaching the S10 GOT fallback hard-errors
        // — Rev-2, no name-resolver fallback).
        target_fq: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        // §3.5 / S110 W2 (S15): the target's derived entry convention, keyed off
        // the carrier. The call arms below adapt against it.
        let convention = self.ctx.entry_convention_at(target_fq);

        // If the function is declared in the current compilation unit, emit a
        // direct call — cheaper and avoids an unnecessary GOT dereference. User
        // ADT constructors have a compiled constructor function here, so this
        // arm covers `(let [f Box] (f 7))` for user types.
        if let Some(target_id) = self.ctx.func_ids.get(target_name) {
            let target_ref = self.module.declare_func_in_func(*target_id, builder.func);
            let call = builder.ins().call(target_ref, user_params);
            let result = builder.inst_results(call)[0];
            self.emit_d24_adaptation(builder, &convention, user_params);
            return Ok(result);
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
        // S110 W2 (S16): keyed `ctor_meta_at` read off the carrier, replacing the
        // `lookup_constructor` chain-follow — the recorder records the canonical
        // `member_key` for a ctor value ref (§1.1.2), so the direct read HITS.
        if let Some((fqtn, ctor_info)) = target_fq.and_then(|fq| self.ctx.ctor_meta_at(fq)) {
            // R5 (§7.1): a value-flattened single-ctor type constructs by a
            // bare-word move of its single field — no alloc. MUST match the
            // use-site (`compile_var_apply`) and synthetic-body
            // (`compile_constr_adt`) flattening, or a `Cell`-as-value produced
            // here (heap pointer) would be mis-read by a flattening match
            // (`cval`) as a bare word — the representation split that returns a
            // garbage pointer. `value_construct` is `None` off-toggle /
            // non-`Value` ⇒ the heap `emit_adt_construct_into` below.
            let adt_ty = ctor_result
                .cloned()
                .unwrap_or_else(|| ConcreteType::ADT(fqtn.clone(), vec![]));
            if let Some(v) = self.value_construct(&adt_ty, user_params) {
                return Ok(v);
            }
            let alloc_id = self
                .ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;
            let emitted_fields = crate::compiler::apply::append_runtime_ctor_fields(
                builder,
                self.module,
                self.glue,
                self.ctx.symbol_tables,
                &fqtn,
                ctor_info.tag,
                &adt_ty,
                user_params,
                false,
                span,
            )?;
            return emit_adt_construct_into(
                builder,
                self.module,
                alloc_id,
                ctor_info.tag,
                &emitted_fields,
                span,
            );
        }

        // Inline Vec primitives (including vec-len) have no GOT slot. Their
        // wrappers own the incoming Vec, so release needs the per-site element
        // type. The resolved entry's kind selects this path, not its spelling.
        if let Some(fq) = target_fq
            && self.ctx.is_inline_primitive_at(fq)
        {
            let elem = vec_elem.cloned();
            return self.emit_vec_query_into(builder, fq.symbol.as_ref(), user_params, &elem, span);
        }

        // Otherwise: GOT-indirect call via __cranelisp_got_{module} data sym.
        // S110 W2 (S10): keyed `got_entry_at` read off the carrier, replacing
        // `resolve_got_entry`/`resolve_got_target`. A `None` carrier or an
        // entry-miss / slot-less entry here is a hard `CodegenError` (Rev-2, no
        // fall-through to the retired name-resolver scan; §1.2).
        let (module_path, slot) = target_fq
            .and_then(|fq| self.ctx.got_entry_at(fq))
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!(
                    "fn-as-value wrapper for '{target_name}' reached codegen with \
                     no GOT-slot carrier (S110 W2 keyed read; \
                     backend-keyed-consumer.md §1.2/§10)"
                ),
                location: ErrorLocation::from_span(span),
            })?;
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
        let result = builder.inst_results(call)[0];
        // §3.5: adapt the target call so this wrapper (the closure-reachable
        // code pointer) is Decision-24 conformant. Auto-curry composes here
        // directly (it reaches this arm through `emit_curry_target_call`) — one
        // adapter, never stacked.
        self.emit_d24_adaptation(builder, &convention, user_params);
        Ok(result)
    }

    /// Emit the call to the auto-curry target inside a wrapper function body.
    ///
    /// When the target is a trait method or builtin, this emits the appropriate
    /// inline IR or extern call directly, instead of trying to call by name
    /// (which fails for inline builtins like `add-i64` that have no JIT symbol).
    #[allow(clippy::too_many_arguments)] // +1 for the S110 W2 carrier
    fn emit_curry_target_call(
        &mut self,
        builder: &mut FunctionBuilder,
        target_name: &Symbol,
        all_args: &[Value],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
        vec_elem: Option<&Type>,
        // S110 W2 (§4): the plain-fn target's STORAGE key (the auto-curry Apply
        // carrier / the fn-as-value Var carrier), used for the
        // `_ =>`/no-resolution fall-throughs. The TraitMethod and BuiltinFn arms
        // derive their OWN carrier from the resolution product (the mangled entry
        // lives in `impl_module`; a vec-query primitive lives in `primitives`),
        // so they do not consult this.
        target_fq: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        if let Some(resolved) = trait_resolution {
            match resolved {
                ResolvedCall::TraitMethod {
                    mangled_name,
                    impl_module,
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
                    //
                    // S110 W2 (S10/S15): the mangled method's STORAGE key is
                    // `{impl_module, mangled}` (the resolution PRODUCT — W0.1b
                    // §1.1.1: the mangle lives in the impl-WRITER's module), keyed
                    // into `emit_wrapper_call`'s summary + GOT reads.
                    let sym = Symbol::from(mangled_name.as_ref());
                    let method_fq = FQSymbol {
                        module: impl_module.clone(),
                        symbol: sym.clone(),
                    };
                    return self.emit_wrapper_call(
                        builder,
                        &sym,
                        all_args,
                        span,
                        vec_elem,
                        None,
                        Some(&method_fq),
                    );
                }
                ResolvedCall::BuiltinFn { name: jit_name } => {
                    // Vec query family (§12.7 — the CURRY seam): the vec family
                    // is NOT in `primitives_inline`, so without this arm a
                    // curried `(vec-get v)` falls to the unknown-builtin extern
                    // Import below and dies at JIT-finalize
                    // ("can't resolve symbol vec-get"). Inline-emit instead,
                    // element type recovered from the applied Vec argument.
                    //
                    // S110 W2 (S18): keyed inline-primitive discrimination off the
                    // synthesized `{primitives, jit_name}` FQ (the vec trio live in
                    // `primitives`; §1.4 synthesized-name precedent), replacing
                    // `resolve_vec_query_primitive`. typecheck already resolved
                    // precedence when it emitted `BuiltinFn` (a user shadow would
                    // have produced a `UserFn` resolution, not this arm).
                    let vq_fq = FQSymbol {
                        module: ModuleFullPath::from("primitives"),
                        symbol: Symbol::from(jit_name.as_ref()),
                    };
                    if self.ctx.is_inline_primitive_at(&vq_fq) {
                        let elem = vec_elem.cloned();
                        return self.emit_vec_query_into(
                            builder,
                            jit_name.as_ref(),
                            all_args,
                            &elem,
                            span,
                        );
                    }
                    // Named builtin resolved by the typechecker.
                    if is_extern_primitive_in_wrapper(jit_name) {
                        return self.emit_adapted_extern_call_in_wrapper(
                            builder, jit_name, all_args, span,
                        );
                    }
                    if primitives_inline::is_known_builtin(jit_name) {
                        match primitives_inline::try_emit_inline_primitive(
                            builder,
                            jit_name,
                            all_args,
                            span,
                            self.module,
                            self.ctx.panic_func_id,
                        ) {
                            Some(result) => return result,
                            None => {
                                // Drift between is_known_builtin and the inline
                                // table — fall through to a GOT-indirect call
                                // against the primitive's `{primitives, jit_name}`
                                // slot (S10 keyed read).
                                let sym = Symbol::from(jit_name.as_ref());
                                let prim_fq = FQSymbol {
                                    module: ModuleFullPath::from("primitives"),
                                    symbol: sym.clone(),
                                };
                                return self.emit_wrapper_call(
                                    builder,
                                    &sym,
                                    all_args,
                                    span,
                                    vec_elem,
                                    None,
                                    Some(&prim_fq),
                                );
                            }
                        }
                    }
                    // Unknown builtin: treat as extern.
                    return self
                        .emit_adapted_extern_call_in_wrapper(builder, jit_name, all_args, span);
                }
                _ => {} // SigDispatch, AutoCurry — fall through to emit_wrapper_call
            }
        }

        // No trait resolution, or resolution didn't match — call by name via the
        // plain-fn carrier (S10/S15).
        self.emit_wrapper_call(
            builder,
            target_name,
            all_args,
            span,
            vec_elem,
            None,
            target_fq,
        )
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
        // S110 W2 (§4; row 17): the Apply-span carrier — the plain-fn curry
        // target's STORAGE key (callee-span transport, W0.1b). Threaded to the
        // wrapper's `_ =>`/no-resolution GOT read; the TraitMethod/BuiltinFn arms
        // self-derive their own.
        target_fq: Option<&FQSymbol>,
        // FIXME 0705 (S115 W3 change-set 3): the CLOSURE-VALUE target — `Some`
        // for the `ApplyRef::ViaCallee` carrier state, where the curry target is
        // a scope-stack closure value, not a table symbol. It is captured
        // ALONGSIDE the applied args (at capture slot `applied_count`, so the
        // applied captures keep their indices) and the wrapper dispatches through
        // its embedded `CODE_PTR` instead of a GOT slot.
        target_closure: Option<Value>,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
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

        // Vec-query element type for the §12.7 curry seam: a partial
        // application of `vec-get`/`vec-set`/`vec-push` always includes the
        // Vec as the first applied argument, whose concrete type names the
        // element. Harmless `Some` for non-vec-query targets whose first
        // applied arg happens to be a Vec — consumed only by the vec-query
        // arm in `emit_curry_target_call`.
        let vec_elem = args.first().and_then(|a| self.vec_elem_type(a));

        // 1. Compile the wrapper function.
        let wrapper_func_id = self.compile_auto_curry_wrapper(
            target_name,
            applied_count,
            remaining_count,
            &arg_categories,
            span,
            trait_resolution,
            vec_elem.as_ref(),
            target_fq,
            target_closure.is_some(),
        )?;

        // 2. Build drop glue for heap-typed captures.
        let arg_types: Vec<&ConcreteType> = args.iter().map(MonoExpr::ty).collect();
        let drop_glue_id = self.build_auto_curry_drop_glue(
            &arg_categories,
            &arg_types,
            target_closure.is_some().then_some(applied_count),
            span,
        )?;

        // 3. Allocate closure env. One extra capture slot when the target is a
        // closure VALUE (FIXME 0705) — it rides at index `applied_count`.
        let capture_count = applied_count + usize::from(target_closure.is_some());
        let payload_size = HeapClosure::payload_size(capture_count) as i64;
        let base_ptr = heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size);

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
            let glue_ref = self.module.declare_func_in_func(glue_id, self.builder.func);
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

        // 4. Store applied args as captures. The closure env's own reference was
        // ALREADY established by the apply site: the `ResolvedCall::AutoCurry`
        // arm compiles the applied args with `compile_consuming_arg_list`, which
        // inc's a heap-typed Var (the enclosing scope keeps its independent
        // reference, dec'd at scope exit) and transfers a temporary's rc=1
        // outright — exactly the "closure env gains one reference" rule (the
        // lambda-capture precedent, `lambda.rs`). A second `emit_capture_inc`
        // here would DOUBLE-count that reference: +1 for a Var (the drop glue
        // dec's only once → the source leaks one alloc), and +1 for a temporary
        // (which owns no scope binding to dec the surplus). Removed — the applied
        // values arrive with correct ownership; just store them. (FIXME 0474 /
        // the S102 `vec_cow_value_use` curry-capture residue; a leak-only class.)
        for (i, &val) in applied_vals.iter().enumerate() {
            heap::heap_store(
                &mut self.builder,
                val,
                base_ptr,
                HeapClosure::capture_offset(i),
            );
        }
        // The closure-value target rides the LAST capture slot (FIXME 0705). Its
        // reference was established by the caller (`compile_consuming_arg_list`
        // over the callee expression: a live-`Var` target is inc'd, a computed
        // temporary transfers) — exactly as for the applied args above.
        if let Some(target_val) = target_closure {
            heap::heap_store(
                &mut self.builder,
                target_val,
                base_ptr,
                HeapClosure::capture_offset(applied_count),
            );
        }

        Ok(base_ptr)
    }

    /// Compile the wrapper function for auto-curry.
    ///
    /// Signature: `(env_ptr, remaining_0, ..., remaining_k) -> i64`
    /// Body: load captures from env, inc heap captures, call target with all args.
    #[allow(clippy::too_many_arguments)] // Curry context requires all parameters
    fn compile_auto_curry_wrapper(
        &mut self,
        target_name: &Symbol,
        applied_count: usize,
        remaining_count: usize,
        arg_categories: &[HeapCategory],
        span: Span,
        trait_resolution: Option<&ResolvedCall>,
        vec_elem: Option<&Type>,
        // S110 W2 (§4; row 17): the plain-fn curry target's carrier.
        target_fq: Option<&FQSymbol>,
        // FIXME 0705: the target is a CLOSURE VALUE captured at slot
        // `applied_count`; dispatch through its embedded `CODE_PTR` rather than
        // a table symbol.
        target_is_closure_capture: bool,
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
            let cap_val = heap::heap_load(&mut builder, env_ptr, HeapClosure::capture_offset(i));
            // Inc heap-typed captures before passing to consuming callee.
            emit_capture_inc_into(&mut builder, self.module, *category, cap_val);
            all_args.push(cap_val);
        }
        all_args.extend_from_slice(&remaining_args);

        // Call the target. FIXME 0705 — when the target is a captured CLOSURE
        // VALUE (the `ApplyRef::ViaCallee` + `VarRef::Local` carrier state) there
        // is no table symbol and no GOT slot to dispatch through: load the
        // captured closure and call its embedded `CODE_PTR` with the closure
        // itself as the env pointer. This is the auto-curry analogue of
        // `compile_closure_call` (the FULL-application locals-first path in
        // `compile_var_apply`), extended from full to PARTIAL application.
        //
        // The captured target is NOT inc'd here: calling a closure does not
        // consume it (`compile_closure_call` emits no inc/dec either), and the
        // curry env's own reference is released by the drop glue.
        let result = if target_is_closure_capture {
            let target_val = heap::heap_load(
                &mut builder,
                env_ptr,
                HeapClosure::capture_offset(applied_count),
            );
            let code_ptr = heap::heap_load(&mut builder, target_val, HeapClosure::CODE_PTR_OFFSET);
            let mut call_sig = self.module.make_signature();
            call_sig.params.push(AbiParam::new(types::I64)); // env ptr
            for _ in &all_args {
                call_sig.params.push(AbiParam::new(types::I64));
            }
            call_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = builder.import_signature(call_sig);
            let mut call_args = vec![target_val];
            call_args.extend_from_slice(&all_args);
            let call = builder.ins().call_indirect(sig_ref, code_ptr, &call_args);
            builder.inst_results(call)[0]
        } else {
            self.emit_curry_target_call(
                &mut builder,
                target_name,
                &all_args,
                span,
                trait_resolution,
                vec_elem,
                target_fq,
            )?
        };

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

    /// Build drop glue for an auto-curry closure's captured arguments (S111 R6
    /// §4.2). Supplies only the capture layout (`heap_indices`) + the naming
    /// identity; the shared envelope (`emit_capture_dec_glue`) owns idempotency +
    /// declare/build/define + the flat capture-dec loop.
    fn build_auto_curry_drop_glue(
        &mut self,
        arg_categories: &[HeapCategory],
        // The applied args' concrete types, positionally paired with
        // `arg_categories` — a `Fn`-typed applied arg is a closure box that owns
        // its own captures (FIXME 0749).
        arg_types: &[&ConcreteType],
        // FIXME 0705: `Some(slot)` when a closure-VALUE target rides capture
        // `slot`; it is heap by construction (a closure is always a heap box) and
        // the curry env owns one reference to it, so the glue must release it or
        // the curried closure leaks its target.
        target_closure_slot: Option<usize>,
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        // Collect indices of heap-typed captures — the capture layout specific.
        // S118 slice S4 (§7.4 / FIXME 0796): the auto-curry env is a
        // compiler-SYNTHESISED capture set reaching the identical seam, so it
        // requests the same canonical glue the explicit-`fn` mirror does. The
        // two differ only in who supplies the capture list — which is why
        // "fix the `fn` path" was never a scoping option.
        let mut heap_indices: Vec<(usize, CaptureRelease)> = Vec::new();
        for (i, cat) in arg_categories.iter().enumerate() {
            let is_fn = matches!(arg_types.get(i), Some(ConcreteType::Fn(..)));
            let Some(kind) = CaptureReleaseKind::classify(*cat, is_fn) else {
                continue;
            };
            match kind {
                CaptureReleaseKind::ClosureBox => {
                    heap_indices.push((i, CaptureRelease::ClosureBox));
                }
                CaptureReleaseKind::Glue => {
                    let Some(ty) = arg_types.get(i) else { continue };
                    if let Some(id) = self.request_capture_glue(&ty.to_type())? {
                        heap_indices.push((i, CaptureRelease::Glue(id)));
                    }
                }
            }
        }
        if let Some(slot) = target_closure_slot {
            // A closure BY CONSTRUCTION — released through its embedded drop
            // glue, or its own captures are stranded when the curry env is the
            // last owner (FIXME 0749 mechanism (b); measured 301/201 before).
            heap_indices.push((slot, CaptureRelease::ClosureBox));
        }

        // Naming identity (ledger item 25): fold `inner_fn_discriminator()` +
        // span IDENTICALLY to the sibling `__curry_…` wrapper so glue identity
        // tracks wrapper identity (else two distinct monos of one span with
        // different `arg_categories` collide on a span-only glue name and
        // silently mis-drop captures). Composed by the ONE naming fn (S111 R6
        // §4.1, `resolution::curry_drop_glue_name`).
        let glue_name = crate::compiler::curry_drop_glue_name(&self.inner_fn_discriminator(), span);
        self.emit_capture_dec_glue(&glue_name, span, &heap_indices)
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
/// Used by auto-curry wrappers to call extern primitives like `str-eq` (through
/// `FnCompiler::emit_adapted_extern_call_in_wrapper`, which adapts the call to
/// the entry's derived convention), and by
/// the vec-query COW emission cores (`vec_codegen`) for the
/// `vec-set-copy`/`vec-push-copy`/`vec-push-grow` runtime externs when emitting
/// into a borrowed builder (wrapper bodies build in a separate Cranelift
/// context, so `FnCompiler::emit_extern_call` over `self.builder` cannot serve).
pub(crate) fn emit_extern_call_in_wrapper(
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
