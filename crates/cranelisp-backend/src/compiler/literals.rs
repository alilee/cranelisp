// Literal and variable reference codegen.
//
// compile_int_lit, compile_float_lit, compile_bool_lit, compile_string_lit,
// compile_var

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{CranelispError, Span, Symbol};

use super::{FnCompiler, bare_ctor_name};

impl<'a> FnCompiler<'a> {
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
                    span,
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
                span,
            })?;

        let mut data_desc = cranelift_module::DataDescription::new();
        data_desc.define(bytes.to_vec().into_boxed_slice());

        self.module
            .define_data(data_id, &data_desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define string data: {e}"),
                span,
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

        // Named function as value: wrap in a zero-capture closure.
        if self.is_known_function(name) {
            return self.compile_fn_as_value(name, span);
        }

        Err(CranelispError::CodegenError {
            message: format!("undefined variable: {name}"),
            span,
        })
    }

    /// Look up the tag value for a nullary constructor.
    ///
    /// Supports module-qualified names (e.g. `macros/SNil`): strips the module
    /// prefix for registry lookups which store unqualified names.
    pub(crate) fn nullary_constructor_tag(&self, name: &Symbol) -> Option<usize> {
        let bare = bare_ctor_name(name);
        let type_name = self.ctx.constructor_to_type.get(bare)?;
        let type_def = self.ctx.type_defs.get(type_name)?;
        let ctor = type_def.constructors.iter().find(|c| c.name.as_ref() == bare)?;
        if ctor.fields.is_empty() {
            Some(ctor.tag)
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
        let bare = bare_ctor_name(name);
        let type_name = self.ctx.constructor_to_type.get(bare)?;
        let type_def = self.ctx.type_defs.get(type_name)?;
        let ctor = type_def.constructors.iter().find(|c| c.name.as_ref() == bare)?;
        if ctor.fields.is_empty() {
            None
        } else {
            Some((ctor.tag, ctor.fields.len()))
        }
    }
}
