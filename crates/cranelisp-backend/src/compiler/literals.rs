// Literal and variable reference codegen.
//
// compile_int_lit, compile_float_lit, compile_bool_lit, compile_var

use cranelift::prelude::*;

use cranelisp_types::{CranelispError, Span, Symbol};

use super::FnCompiler;

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

        // In Batch mode, a top-level function used as a value is not supported
        // in Ring 0 (no closures). Return an error.
        Err(CranelispError::CodegenError {
            message: format!("undefined variable: {name}"),
            span,
        })
    }

    /// Look up the tag value for a nullary constructor.
    fn nullary_constructor_tag(&self, name: &Symbol) -> Option<usize> {
        let type_name = self.ctx.constructor_to_type.get(name)?;
        let type_def = self.ctx.type_defs.get(type_name)?;
        let ctor = type_def.constructors.iter().find(|c| c.name == *name)?;
        if ctor.fields.is_empty() {
            Some(ctor.tag)
        } else {
            None
        }
    }
}
