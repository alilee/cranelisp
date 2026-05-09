// Literal and variable reference codegen.
//
// compile_int_lit, compile_float_lit, compile_bool_lit, compile_string_lit,
// compile_var

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{ErrorLocation, CranelispError, Span, Symbol};

use super::FnCompiler;
use crate::heap::{self, HeapAdt, HeapClosure};

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
    ) -> Result<Value, CranelispError> {
        // Local variable takes priority.
        if let Some(var) = self.variables.get(name) {
            return Ok(self.builder.use_var(*var));
        }

        // Nullary constructor: return tag as i64.
        if let Some(tag) = self.nullary_constructor_tag(name) {
            return Ok(self.builder.ins().iconst(types::I64, tag as i64));
        }

        // Data constructor as value: wrap in a closure that allocates the ADT.
        // e.g. `(let [f Some] (f 42))` — `Some` becomes a closure `(env, val) -> ADT`.
        if let Some((tag, field_count)) = self.data_constructor_info(name) {
            return self.compile_data_constructor_as_value(name, tag, field_count, span);
        }

        // Operator symbol as value: wrap the operator extern function in a closure.
        // This implements spec §7.6 — trait methods (operators) as first-class values.
        // Must be checked before is_known_function because operators may appear
        // in TC symbol tables (via env) but need their dedicated extern wrappers.
        if let Some(op_extern_name) = Self::operator_extern_name(name) {
            return self.compile_operator_as_value(op_extern_name, span);
        }

        // Named function as value: wrap in a zero-capture closure.
        if self.is_known_function(name) {
            return self.compile_fn_as_value(name, span);
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

    /// Wrap a data constructor as a first-class value (closure).
    ///
    /// Generates a wrapper function `(env_ptr, field0, field1, ...) -> i64`
    /// that allocates the ADT on the heap, stores the tag and fields, and
    /// returns the heap pointer. Wraps it in a zero-capture closure.
    ///
    /// Implements spec §5.5: constructors as first-class values.
    fn compile_data_constructor_as_value(
        &mut self,
        name: &Symbol,
        tag: usize,
        field_count: usize,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        // Declare the wrapper function: (env_ptr, fields...) -> i64
        let wrapper_name = format!("__ctor_wrap_{name}_{}_{}__", span.start, span.end);
        let wrapper_param_count = 1 + field_count; // env_ptr + fields
        let mut sig = self.module.make_signature();
        for _ in 0..wrapper_param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_function(&wrapper_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare constructor wrapper: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Compile the wrapper body.
        self.compile_ctor_wrapper_body(wrapper_func_id, tag, field_count, alloc_id, span)?;

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

    /// Compile the body of a constructor wrapper function.
    ///
    /// The wrapper allocates a heap ADT, stores the tag and fields from
    /// its parameters, and returns the heap pointer.
    fn compile_ctor_wrapper_body(
        &mut self,
        func_id: cranelift_module::FuncId,
        tag: usize,
        field_count: usize,
        alloc_id: cranelift_module::FuncId,
        span: Span,
    ) -> Result<(), CranelispError> {
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();

        // Signature: (env_ptr, field0, field1, ...) -> i64
        for _ in 0..1 + field_count {
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
        let field_vals: Vec<Value> = block_params[1..].to_vec(); // skip env_ptr

        // Allocate the ADT on the heap.
        let payload_size = HeapAdt::payload_size(field_count) as i64;
        let base_ptr = heap::emit_alloc(
            &mut builder,
            self.module,
            alloc_id,
            payload_size,
        );

        // Store tag at HeapAdt::TAG_OFFSET.
        let tag_val = builder.ins().iconst(types::I64, tag as i64);
        heap::heap_store(&mut builder, tag_val, base_ptr, HeapAdt::TAG_OFFSET);

        // Store each field.
        for (i, &field_val) in field_vals.iter().enumerate() {
            heap::heap_store(
                &mut builder,
                field_val,
                base_ptr,
                HeapAdt::field_offset(i),
            );
        }

        builder.ins().return_(&[base_ptr]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define constructor wrapper: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(())
    }

    // --- Operator-as-value support (spec §7.6) ---

    /// Map an operator symbol to its extern "C" wrapper function name.
    /// Returns None if the symbol is not a known operator.
    fn operator_extern_name(name: &Symbol) -> Option<&'static str> {
        match name.as_ref() {
            "+" => Some("cranelisp_op_add"),
            "-" => Some("cranelisp_op_sub"),
            "*" => Some("cranelisp_op_mul"),
            "/" => Some("cranelisp_op_div"),
            "=" => Some("cranelisp_op_eq"),
            "!=" => Some("cranelisp_op_neq"),
            "<" => Some("cranelisp_op_lt"),
            ">" => Some("cranelisp_op_gt"),
            "<=" => Some("cranelisp_op_le"),
            ">=" => Some("cranelisp_op_ge"),
            _ => None,
        }
    }

    /// Wrap an operator extern "C" function as a zero-capture closure.
    ///
    /// Declares the extern function in the JIT module, creates a wrapper
    /// function with signature `(env_ptr, a, b) -> i64` that ignores env_ptr
    /// and forwards to the operator, then allocates a HeapClosure pointing
    /// to the wrapper.
    fn compile_operator_as_value(
        &mut self,
        op_extern_name: &str,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        // Declare the operator extern function: (i64, i64) -> i64
        let mut op_sig = self.module.make_signature();
        op_sig.params.push(AbiParam::new(types::I64));
        op_sig.params.push(AbiParam::new(types::I64));
        op_sig.returns.push(AbiParam::new(types::I64));

        let op_func_id = self
            .module
            .declare_function(op_extern_name, Linkage::Import, &op_sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare operator '{op_extern_name}': {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Create a wrapper function: (env_ptr, a, b) -> i64
        // The wrapper ignores env_ptr and calls the operator function.
        let wrapper_name = format!("__wrap_op_{op_extern_name}_{}_{}__", span.start, span.end);
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

        // Compile wrapper body: ignore env_ptr, forward (a, b) to operator.
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

            let op_ref = self
                .module
                .declare_func_in_func(op_func_id, builder.func);
            let call = builder.ins().call(op_ref, &[a, b]);
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
