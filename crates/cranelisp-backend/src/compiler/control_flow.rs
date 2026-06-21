// Control flow, binding, and closure codegen — module hub.
//
// The cohesive codegen clusters live in sibling sub-modules, each an
// `impl FnCompiler` block on the shared struct:
//   - `let_if`       — sequential + lenient `let` binding and `if` branch-merge
//   - `par_bind`     — IO ParBind node + continuation closure emission
//   - `lambda`       — closure compilation: site alloc, inner-fn body, drop glue
//   - `fn_as_value`  — named-fn / trait-method value wrappers + auto-curry
//   - `free_vars`    — pure free-variable analysis over `MonoExpr`
//   - `sparkability` — lenient-eval decision pass
//   - `capture_rc`   — the single-source capture-RC-inc helper
//
// This hub keeps only the shared `emit_extern_call_1` IVar-plumbing helper and
// the cross-submodule bridge re-exports.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, Span};

use super::FnCompiler;

mod capture_rc;
mod fn_as_value;
mod free_vars;
mod lambda;
mod let_if;
mod par_bind;
mod sparkability;

// Cross-submodule bridges: these names are referenced by the sub-modules via
// `super::…` (children can reach a parent's private `use` items). Re-exported
// `pub(crate)` so the hub is a single resolution point and the imports are not
// flagged unused.
pub(crate) use capture_rc::emit_capture_inc_into;
pub(crate) use free_vars::find_free_vars;
// Only the `sparkability_tests` sibling reaches this via `super::`.
#[cfg(test)]
pub(crate) use sparkability::find_sparkable_bindings;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{

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
}

#[cfg(test)]
mod sparkability_tests;

#[cfg(test)]
mod par_codegen_tests;
