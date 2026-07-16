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

use crate::heap::{self, HeapCategory, HeapClosure};
use crate::primitives_inline;

use super::{emit_capture_inc_into, FnCompiler};

/// Linker name for an auto-curry closure's capture drop glue.
///
/// Keyed by `disc` (`FnCompiler::inner_fn_discriminator()` — the mono instance +
/// create-gate arm) and `span`, IDENTICALLY to its sibling wrapper name
/// `__curry_{target}_{disc}{span}__` (F2, P7/P8: wrapper + drop glue must share
/// one identity). Span alone under-keys: two monomorphizations of one span with
/// different capture `HeapCategory`s produce distinct wrappers but would collide
/// on a span-only glue name, silently mis-dropping captures. Folding `disc` makes
/// glue identity track wrapper identity.
pub(crate) fn curry_drop_glue_name(disc: &str, span: Span) -> String {
    format!("runtime/curry_drop_glue_{}{}_{}", disc, span.start, span.end)
}

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

#[cfg(test)]
mod curry_glue_name_tests;

// Relocated crate-root fn-as-value + value-use tests (FIXME 0495 step 1).
#[cfg(test)]
mod value_use_tests;

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
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        // S110 W2 (S14): arity read off the carrier's fetched entry
        // (`param_names.len()`), replacing `resolve_func_arity`. The current-unit
        // `func_arities` map stays as the fast-path (a local map, not a resolver).
        let arity = self.ctx.func_arities.get(name).copied()
            .or_else(|| target_fq.and_then(|fq| self.ctx.arity_at(fq)))
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

        let vec_elem = vec_query_elem_from_fn_type(fn_type);
        self.compile_fn_wrapper_body(
            wrapper_func_id, name, arity, span, vec_elem.as_ref(), target_fq,
        )?;

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
        fn_type: Option<&Type>,
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
        // S110 W2 (§4): the target's STORAGE key — drives `emit_wrapper_call`'s
        // S10/S15/S16/S17 keyed reads.
        target_fq: Option<&FQSymbol>,
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
            &mut builder, target_name, &user_params, span, vec_elem, target_fq,
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
    /// target's moded [`ModeSummary`], onto a wrapper's borrowed `builder` AFTER
    /// the target call returns. ONE helper, and the sole consumers all reach it
    /// through [`Self::emit_wrapper_call`] (the fn-as-value / trait-method-value
    /// wrapper bodies and the auto-curry target call) — no per-site reinvention
    /// (Principle 7), no stacked adapters.
    ///
    /// - param `Owned→Borrowed` ⇒ **post-call dec** of the received-owned arg:
    ///   the wrapper owns its params (closure protocol) but the moded callee
    ///   borrowed (did not dec) the `Borrowed` positions, so the wrapper releases
    ///   them.
    /// - result `ProjectionOf→Fresh` ⇒ **materialization inc**: the moded callee
    ///   returned a borrowed view rooted in a param, but the closure protocol
    ///   owes the caller a fresh owned value.
    /// - everything else (Owned/Copy params, `AliasOf`/`Fresh` result) ⇒
    ///   pass-through.
    ///
    /// Guarded RC ops throughout (layout-safe for AlwaysHeap and Mixed alike).
    /// Reached ONLY for a non-ABI-conservative summary, so with analysis off it
    /// never runs — the wrapper body is byte-identical to today (§2.2).
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
        summary: &cranelisp_types::ModeSummary,
        args: &[Value],
        _result: Value,
    ) {
        let dealloc_id = self.ctx.dealloc_func_id;
        for (i, &arg) in args.iter().enumerate() {
            if summary.param_mode(i) == cranelisp_types::Mode::Borrowed {
                heap::emit_rc_dec_guarded(builder, self.module, arg, dealloc_id, None, true);
            }
        }
    }

    /// Emit the call instruction inside a wrapper function body.
    ///
    /// Prefers a direct `call` via FuncId when the target is in the current
    /// unit's `func_ids` map. Otherwise emits a GOT-indirect `call_indirect`
    /// using the uniform `__cranelisp_got_{module}` data-symbol strategy
    /// (design/backend/compile-to-module.md §12).
    ///
    /// §3.5 R2 wrapper coupling: when the resolved call target carries a
    /// **non-trivial** ownership summary (any param non-`Owned`, or result
    /// non-`Fresh`), the moded-body call is wrapped with [`Self::emit_d24_adaptation`]
    /// so the closure-reachable code pointer (this wrapper) is Decision-24
    /// conformant. THE INVARIANT: every code pointer reachable from a closure
    /// value targets a Decision-24-conformant entry; a moded body is reachable
    /// ONLY through statically-resolved call sites (§3.1) and these adapter
    /// wrapper bodies — its address never escapes into a closure unadapted.
    /// A summary-trivial (or absent) target synthesizes directly over the body
    /// call as today (zero new emission — byte-identical-off).
    fn emit_wrapper_call(
        &mut self,
        builder: &mut FunctionBuilder,
        target_name: &Symbol,
        user_params: &[Value],
        span: Span,
        vec_elem: Option<&Type>,
        // S110 W2 (§4): the target's STORAGE key — drives the S15 summary, S16
        // ctor-as-value, S17 vec-query, and S10 GOT-entry keyed reads. `None` for
        // a target with no carrier (the current-unit `func_ids` fast-path below
        // covers same-unit fns; a `None` reaching the S10 GOT fallback hard-errors
        // — Rev-2, no name-resolver fallback).
        target_fq: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        // §3.5 / S110 W2 (S15): the target's summary, kept only when
        // non-ABI-conservative — the moded-body arms below adapt against it.
        // Keyed read off the carrier (`callee_summary_at`) replacing
        // `resolve_callee_summary`. `None` for every summary-trivial or
        // non-summary target (constructors, inline vec primitives, unanalysed
        // fns), so those arms emit exactly today's shape.
        let target_summary = target_fq
            .and_then(|fq| self.ctx.callee_summary_at(fq))
            .filter(|s| !s.is_abi_conservative());

        // If the function is declared in the current compilation unit, emit a
        // direct call — cheaper and avoids an unnecessary GOT dereference. User
        // ADT constructors have a compiled constructor function here, so this
        // arm covers `(let [f Box] (f 7))` for user types.
        if let Some(target_id) = self.ctx.func_ids.get(target_name) {
            let target_ref =
                self.module.declare_func_in_func(*target_id, builder.func);
            let call = builder.ins().call(target_ref, user_params);
            let result = builder.inst_results(call)[0];
            if let Some(ref summary) = target_summary {
                self.emit_d24_adaptation(builder, summary, user_params, result);
            }
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
        if let Some((fqtn, ctor_info)) =
            target_fq.and_then(|fq| self.ctx.ctor_meta_at(fq))
        {
            // R5 (§7.1): a value-flattened single-ctor type constructs by a
            // bare-word move of its single field — no alloc. MUST match the
            // use-site (`compile_var_apply`) and synthetic-body
            // (`compile_constr_adt`) flattening, or a `Cell`-as-value produced
            // here (heap pointer) would be mis-read by a flattening match
            // (`cval`) as a bare word — the representation split that returns a
            // garbage pointer. `value_construct` is `None` off-toggle /
            // non-`Value` ⇒ the heap `emit_adt_construct_into` below.
            let adt_ty = ConcreteType::ADT(fqtn, vec![]);
            if let Some(v) = self.value_construct(&adt_ty, user_params) {
                return Ok(v);
            }
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

        // Vec query family (`vec-get`/`vec-set`/`vec-push`) as a first-class
        // value: these primitives-table entries are `PrimitiveBody::Inline` —
        // inline-dispatched, no GOT slot by construction (S102 FIXME 0476: no
        // extern body can exist, since a single monomorphic body cannot know
        // the element's heap category, so callability is a *kind*, not a
        // NULL-slot proxy). The GOT-indirect fallback below has no slot to
        // dispatch through; inline-emit the op into the wrapper instead — the
        // `emit_adt_construct_into` precedent — using the per-site element
        // type plumbed from the value-use site. The resolver is
        // precedence-faithful (a user fn shadowing the name resolves first and
        // keeps the GOT path); `vec-len` is excluded (real extern shim,
        // populated slot — the working control path). Re-keys off the inline
        // kind (§13.2 B1-be — the S101 name-list retired).
        // S110 W2 (S17): keyed inline-primitive discrimination off the carrier,
        // replacing `resolve_vec_query_primitive`. A user fn shadowing the name
        // resolves to a non-inline entry (the carrier is the resolved storage FQ),
        // so it keeps the GOT path below — precedence-faithful by construction.
        // The canonical bare name the wrapper inline-emits is `fq.symbol`.
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
        // §3.5: adapt the moded-body call so this wrapper (the closure-reachable
        // code pointer) is Decision-24 conformant. `None` ⇒ no emission (today's
        // shape). Auto-curry composes here directly (it reaches this arm through
        // `emit_curry_target_call`) — one adapter, never stacked.
        if let Some(ref summary) = target_summary {
            self.emit_d24_adaptation(builder, summary, user_params, result);
        }
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
        // carrier / the fn-as-value Var carrier), used for the summary-trivial
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
                        builder, &sym, all_args, span, vec_elem, Some(&method_fq),
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
                                    builder, &sym, all_args, span, vec_elem,
                                    Some(&prim_fq),
                                );
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

        // No trait resolution, or resolution didn't match — call by name via the
        // plain-fn carrier (S10/S15).
        self.emit_wrapper_call(builder, target_name, all_args, span, vec_elem, target_fq)
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
            vec_elem,
            target_fq,
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
                HeapCategory::NeverHeap | HeapCategory::Value => None,
            })
            .collect();

        if heap_indices.is_empty() {
            return Ok(None);
        }

        // Key the drop glue IDENTICALLY to its sibling `__curry_…` wrapper —
        // fold in `inner_fn_discriminator()` (the mono/gate-arm discriminator),
        // NOT span alone (F2, P7/P8: a closure wrapper and its drop glue MUST
        // share one identity). The wrapper name `__curry_{target}_{disc}{span}__`
        // already folds the disc; the glue previously used span alone, so two
        // DISTINCT monomorphizations of the same span with DIFFERENT
        // `arg_categories` (a capture position's `HeapCategory` differing across
        // instantiations) produced distinct wrapper names but a COLLIDING glue
        // name — and the `get_name` idempotency skip below would then hand the
        // 2nd mono the 1st mono's glue → wrong capture-drop (dec a non-heap
        // capture / skip a heap one → corruption or leak), silently. Folding the
        // disc makes glue identity track wrapper identity: distinct monos get
        // distinct glue; the two arms of ONE create-gate (same disc + span,
        // identical `arg_categories` by construction) still share one glue.
        let glue_name = curry_drop_glue_name(&self.inner_fn_discriminator(), span);

        // `declare_function` is idempotent (returns the existing FuncId on a
        // name match), but `define_function` is NOT — a second definition of the
        // same identifier is a hard `Duplicate definition` codegen error. When a
        // create-gate compiles the SAME auto-curry expression on BOTH its lenient
        // and sequential arms (ledger item 25), the glue is declared once but the
        // second arm's `define_function` would die `Duplicate definition`. Skip
        // re-definition when this glue was already built — with the disc-keyed
        // name a `get_name` hit means the SAME mono instance at the SAME span, so
        // `arg_categories` are identical by construction and sharing one glue
        // definition is sound (the `build_elem_dec_fn` / `build_adt_drop_glue_fn`
        // idempotency precedent, vec_codegen.rs).
        if let Some(cranelift_module::FuncOrDataId::Func(existing_id)) =
            self.module.get_name(&glue_name)
        {
            return Ok(Some(existing_id));
        }

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
                HeapCategory::NeverHeap | HeapCategory::Value => {} // unreachable, filtered above
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
/// Used by auto-curry wrappers to call extern primitives like `str-eq`, and by
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
