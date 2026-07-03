// Literal and variable reference codegen.
//
// compile_int_lit, compile_float_lit, compile_bool_lit, compile_string_lit,
// compile_var

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{ErrorLocation, CranelispError, ResolvedCall, Span, Symbol, Type};

use super::FnCompiler;
use crate::heap::{self, HeapClosure};

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // --- Literal codegen ---

    pub(crate) fn compile_int_lit(&mut self, value: i64) -> Result<Value, CranelispError> {
        Ok(self.builder.ins().iconst(types::I64, value))
    }

    pub(crate) fn compile_float_lit(&mut self, value: f64) -> Result<Value, CranelispError> {
        // Store f64 bits as i64 -- all values are i64 at runtime.
        let bits = value.to_bits() as i64;
        Ok(self.builder.ins().iconst(types::I64, bits))
    }

    pub(crate) fn compile_bool_lit(&mut self, value: bool) -> Result<Value, CranelispError> {
        let val = if value { 1i64 } else { 0i64 };
        Ok(self.builder.ins().iconst(types::I64, val))
    }

    /// Compile a string literal.
    ///
    /// Stores the UTF-8 bytes in a Cranelift data section, then at runtime
    /// calls `runtime/alloc_string(data_ptr, len)` to allocate the HeapString.
    pub(crate) fn compile_string_lit(
        &mut self,
        value: &str,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_string_id =
            self.ctx
                .alloc_string_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc_string not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        let bytes = value.as_bytes();
        let len = bytes.len() as i64;

        if bytes.is_empty() {
            // Empty string: call alloc_string with null ptr and 0 length.
            let null_ptr = self.builder.ins().iconst(types::I64, 0);
            let len_val = self.builder.ins().iconst(types::I64, 0);
            let alloc_ref = self
                .module
                .declare_func_in_func(alloc_string_id, self.builder.func);
            let call = self.builder.ins().call(alloc_ref, &[null_ptr, len_val]);
            return Ok(self.builder.inst_results(call)[0]);
        }

        // Store bytes in a JIT data section.
        let data_id = self
            .module
            .declare_anonymous_data(false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare string data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let mut data_desc = cranelift_module::DataDescription::new();
        data_desc.define(bytes.to_vec().into_boxed_slice());

        self.module
            .define_data(data_id, &data_desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define string data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Get the data pointer as a Cranelift value.
        let data_gv = self
            .module
            .declare_data_in_func(data_id, self.builder.func);
        let data_ptr = self
            .builder
            .ins()
            .global_value(types::I64, data_gv);

        let len_val = self.builder.ins().iconst(types::I64, len);

        // Call runtime/alloc_string(data_ptr, len) to allocate the HeapString.
        let alloc_ref = self
            .module
            .declare_func_in_func(alloc_string_id, self.builder.func);
        let call = self.builder.ins().call(alloc_ref, &[data_ptr, len_val]);

        Ok(self.builder.inst_results(call)[0])
    }

    // --- Variable reference ---

    pub(crate) fn compile_var(
        &mut self,
        name: &Symbol,
        span: Span,
        resolved_call: Option<&ResolvedCall>,
        inferred_type: Option<&Type>,
    ) -> Result<Value, CranelispError> {
        // Local variable takes priority.
        if let Some(var) = self.variables.get(name) {
            return Ok(self.builder.use_var(*var));
        }

        // Value-position trait-method reference (spec §7.6). Typecheck
        // annotates a bare `Expr::Var` that names a trait method used in value
        // position with its resolved dispatch target (`resolved_call`) and the
        // concrete `Fn` type (`inferred_type`). Emit a zero-capture
        // dispatch-wrapper closure that calls the resolved name with the right
        // arity — the zero-args-applied analogue of auto-curry.
        //
        // This REPLACES the hard-coded-Int `compile_operator_as_value` path
        // (below) for any operator/method typecheck resolved: that path mapped
        // `=`→`eq-i64`, `+`→`add-i64` unconditionally regardless of operand
        // type, producing the wrong impl for String/Float values (Symptom B).
        // With a carried resolution we dispatch to the correct impl
        // (`str-eq` / `add-f64` / `int-to-string` / mangled trait impl) chosen
        // by typecheck. No trait knowledge in backend (Decision 43).
        if let Some(resolved) = resolved_call {
            let arity = match inferred_type {
                Some(Type::Fn(params, _)) => params.len(),
                _ => {
                    return Err(CranelispError::CodegenError {
                        message: format!(
                            "value-position trait method '{name}' has a \
                             resolved_call but no Fn inferred_type to supply \
                             arity"
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
            };
            return self.compile_trait_method_as_value(resolved, arity, span, inferred_type);
        }

        // Nullary constructor reference (e.g. `None`, `Red`): fold to a bare
        // tag via the single core emitter (§2.6.1 Path-1 nullary fold). The
        // `lookup_constructor` recognition stays; the emission routes through
        // `emit_adt_construct(tag, &[], span)`.
        if let Some(tag) = self.nullary_constructor_tag(name) {
            return self.emit_adt_construct(tag, &[], span);
        }

        // NOTE: data constructors are NO LONGER special-cased here. Per
        // `design/backend/compile-to-module.md` §2.6.1 (constructors-like-
        // primitives, Decision 48), a data-constructor reference falls through
        // to `is_known_function` → `compile_fn_as_value` over the got-slotted
        // constructor `Def` — the same GOT/fn-as-value mechanism
        // `compile_operator_as_value` uses for primitives. The bespoke
        // as-value closure was deleted in S75 W4. Backend EXPECTS the
        // constructor's GOT slot to be populated (typecheck got-slot + int
        // batch — S77 §2.6.5); it does not produce it, exactly as it assumes
        // the primitive's slot.

        // Operator symbol as value: wrap the primitive in a closure.
        // This implements spec §7.6 — trait methods (operators) as first-class values.
        // Must be checked before is_known_function because operators may appear
        // in TC symbol tables (via env) but need their dedicated wrappers.
        //
        // Per Decision 43 + FIXME 0183: operator-as-value resolves through the
        // standard GOT-indirect path against the primitives module — identical
        // shape to any other primitive call. The wrapper closure shape is
        // unchanged; only the load mechanism (GOT slab + slot) differs from
        // the pre-D43 `Linkage::Import` extern-name relocation.
        if let Some(primitive_name) = Self::operator_primitive_name(name) {
            return self.compile_operator_as_value(primitive_name, span);
        }

        // Named function as value: wrap in a zero-capture closure. The
        // inferred `Fn` type rides along so the vec-query wrapper arm can
        // recover the per-site element type (§12.7).
        if self.is_known_function(name) {
            return self.compile_fn_as_value(name, span, inferred_type);
        }

        Err(CranelispError::CodegenError {
            message: format!("undefined variable: {name}"),
            location: ErrorLocation::from_span(span),
        })
    }

    /// Look up the tag value for a nullary constructor.
    ///
    /// Supports module-qualified names (e.g. `macros/SNil`):
    /// lookup_constructor handles qualified name resolution.
    pub(crate) fn nullary_constructor_tag(&self, name: &Symbol) -> Option<usize> {
        let (_fqtn, ctor_info) = self.ctx.lookup_constructor(name.as_ref())?;
        if ctor_info.fields.is_empty() {
            Some(ctor_info.tag)
        } else {
            None
        }
    }

    /// Look up the tag and field count for a data constructor.
    ///
    /// Supports module-qualified names (e.g. `macros/SexpInt`): strips the module
    /// prefix for registry lookups which store unqualified names.
    pub(crate) fn data_constructor_info(
        &self,
        name: &Symbol,
    ) -> Option<(usize, usize)> {
        let (_fqtn, ctor_info) = self.ctx.lookup_constructor(name.as_ref())?;
        if ctor_info.fields.is_empty() {
            None
        } else {
            Some((ctor_info.tag, ctor_info.fields.len()))
        }
    }

    // --- Operator-as-value support (spec §7.6) ---

    /// Map an operator symbol to the canonical Ring 0 primitive name in the
    /// synthetic `primitives` module.
    ///
    /// Per Decision 43 + FIXME 0183: operator-as-value resolves through the
    /// standard GOT-indirect dispatch path. The mapping below is the
    /// Int-typed canonical wrapper (matching the pre-D43 `cranelisp_op_*`
    /// shape, which itself was integer-only). A type-aware mappable-path
    /// resolution belongs at typecheck (`ResolvedCall::TraitMethod`) — the
    /// backend's operator-as-value path is the type-erased fallback for the
    /// remaining bare-symbol uses.
    ///
    /// Returns None if the symbol is not a known operator.
    fn operator_primitive_name(name: &Symbol) -> Option<&'static str> {
        match name.as_ref() {
            "+" => Some("add-i64"),
            "-" => Some("sub-i64"),
            "*" => Some("mul-i64"),
            "/" => Some("div-i64"),
            "=" => Some("eq-i64"),
            "!=" => Some("neq-i64"),
            "<" => Some("lt-i64"),
            ">" => Some("gt-i64"),
            "<=" => Some("le-i64"),
            ">=" => Some("ge-i64"),
            _ => None,
        }
    }

    /// Wrap a Ring 0 primitive as a zero-capture closure for operator-as-value.
    ///
    /// Per FIXME 0183 + `facades/backend.md` §"REV-5 audit": the wrapper
    /// function `(env_ptr, a, b) -> i64` resolves the primitive through the
    /// standard GOT-indirect path — `resolve_got_target` for the primitive
    /// name yields `(primitives, slot)`, then emit `global_value` against
    /// `__cranelisp_got_primitives` + `load(slab_base + slot * 8)` + `call_indirect`.
    /// The closure shape is unchanged; only the load mechanism shifts from
    /// pre-D43 `Linkage::Import` + extern-name to the uniform dispatch path.
    fn compile_operator_as_value(
        &mut self,
        primitive_name: &str,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        // Resolve the primitive to its GOT slot. The primitive lives in the
        // synthetic `primitives` module's symbol table; resolution walks
        // import chains starting from current_module per the standard path.
        let prim_sym = Symbol::from(primitive_name);
        let (target_module, slot) = crate::compiler::resolve_got_target(
            self.ctx.symbol_tables,
            self.ctx.module_aliases,
            &self.ctx.current_module,
            &prim_sym,
        )
        .ok_or_else(|| CranelispError::CodegenError {
            message: format!(
                "operator-as-value: no GOT slot for primitive '{primitive_name}'"
            ),
            location: ErrorLocation::from_span(span),
        })?;

        // Declare the GOT data symbol for the primitive's owning module.
        // The data symbol's address IS the slab base (per Decision 23).
        let got_sym = crate::compiler::got_data_symbol_name(&target_module);
        let got_data_id = self
            .module
            .declare_data(&got_sym, cranelift_module::Linkage::Import, false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare GOT data '{}': {e}", got_sym),
                location: ErrorLocation::from_span(span),
            })?;

        // Create a wrapper function: (env_ptr, a, b) -> i64
        // The wrapper ignores env_ptr and calls the primitive via GOT-indirect.
        // Span-derived + mono-discriminated name (FIXME 0347 defect 1) so
        // monomorphic copies of the enclosing fn do not collide on a shared
        // operator-as-value wrapper symbol.
        let wrapper_name = format!(
            "__wrap_op_{primitive_name}_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );
        let mut wrapper_sig = self.module.make_signature();
        wrapper_sig.params.push(AbiParam::new(types::I64)); // env_ptr (ignored)
        wrapper_sig.params.push(AbiParam::new(types::I64)); // a
        wrapper_sig.params.push(AbiParam::new(types::I64)); // b
        wrapper_sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_function(&wrapper_name, Linkage::Local, &wrapper_sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare operator wrapper: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Compile wrapper body: ignore env_ptr, resolve primitive via
        // GOT-indirect, call_indirect with (a, b).
        {
            let mut inner_ctx = self.module.make_context();
            let mut inner_func_ctx = FunctionBuilderContext::new();

            // Signature: (env_ptr, a, b) -> i64
            for _ in 0..3 {
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
            // block_params[0] = env_ptr (ignored), [1] = a, [2] = b
            let a = block_params[1];
            let b = block_params[2];

            // GOT-indirect: slab_base = global_value(got_data_id);
            //               fn_ptr = load(slab_base + slot * 8);
            //               call_indirect(fn_ptr, [a, b]).
            let gv = self
                .module
                .declare_data_in_func(got_data_id, builder.func);
            let slab_base = builder.ins().global_value(types::I64, gv);
            let slot_addr =
                builder.ins().iadd_imm(slab_base, (slot * 8) as i64);
            let fn_ptr = builder.ins().load(
                types::I64,
                MemFlags::trusted(),
                slot_addr,
                0,
            );

            // Build call_indirect signature: (i64, i64) -> i64.
            let mut prim_sig = self.module.make_signature();
            prim_sig.params.push(AbiParam::new(types::I64));
            prim_sig.params.push(AbiParam::new(types::I64));
            prim_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = builder.import_signature(prim_sig);

            let call = builder.ins().call_indirect(sig_ref, fn_ptr, &[a, b]);
            let result = builder.inst_results(call)[0];

            builder.ins().return_(&[result]);
            builder.seal_all_blocks();
            builder.finalize();

            self.module
                .define_function(wrapper_func_id, &mut inner_ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define operator wrapper: {e}"),
                    location: ErrorLocation::from_span(span),
                })?;
        }

        // Allocate a closure with zero captures: [header | code_ptr | drop_glue_ptr(0)].
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

        // Store zero drop glue pointer (no captures).
        let zero = self.builder.ins().iconst(types::I64, 0);
        heap::heap_store(
            &mut self.builder,
            zero,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        Ok(base_ptr)
    }
}
