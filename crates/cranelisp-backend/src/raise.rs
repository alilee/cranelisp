//! The one emitter of a runtime panic (`design/backend/backend.md` §7).
//!
//! A raise places its message, calls `runtime/panic(msg_ptr, msg_len)` and
//! ends the block with a trap. `runtime/panic` never returns, so the trap
//! never executes; it is there so no emitted code follows the call.
//!
//! The declared `runtime/panic` travels only as a [`PanicHandle`], which this
//! module alone constructs and only [`emit_raise`] opens, so code outside
//! `raise` holds no value from which to build the call. The residual is a
//! by-name re-declaration, which Cranelift answers with the same id; the
//! census `raise::tests::panic_symbol_is_named_only_in_raise` keeps the name
//! out of every other production source (safety register R13).

use cranelift::prelude::*;
use cranelift_module::{DataDescription, FuncId, Module};

use cranelisp_types::{CranelispError, ErrorLocation, Span};

/// The intrinsic catalog's name for the panic funnel. No other production
/// source spells it.
const PANIC_SYMBOL: &str = "runtime/panic";

/// The trap code on a raise's terminator. Reaching it means `runtime/panic`
/// returned, which its contract forbids; the process stops there rather than
/// resuming the caller.
const RAISE_RETURNED: TrapCode = TrapCode::unwrap_user(1);

/// A panic condition the emitted code checks, with its spec §12.7.2.1 message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PanicSource {
    /// A match whose arms all failed.
    MatchFailed,
    /// A zero divisor.
    DivisionByZero,
    /// A `vec-get` or `vec-set` index below zero or not below the length.
    VecIndexOutOfBounds,
}

impl PanicSource {
    fn message(self) -> &'static [u8] {
        match self {
            PanicSource::MatchFailed => b"match failed",
            PanicSource::DivisionByZero => b"division by zero",
            PanicSource::VecIndexOutOfBounds => b"vec-get: index out of bounds",
        }
    }
}

/// The declared `runtime/panic`. Its id is private to this module.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PanicHandle(FuncId);

/// Wrap the intrinsic declaration loop's entry when it is `runtime/panic`.
///
/// The loop calls this for every catalog entry and keeps a claimed entry out
/// of its by-name map, so no compile's `func_ids` yields the panic id.
pub(crate) fn claim(name: &str, id: FuncId) -> Option<PanicHandle> {
    (name == PANIC_SYMBOL).then_some(PanicHandle(id))
}

/// The declared `runtime/panic`, or the located codegen error for a module
/// that lacks it.
pub(crate) fn declared(
    panic: Option<PanicHandle>,
    span: Span,
) -> Result<PanicHandle, CranelispError> {
    panic.ok_or_else(|| CranelispError::CodegenError {
        message: "runtime/panic not declared".into(),
        location: ErrorLocation::from_span(span),
    })
}

/// Raise `source`'s message, placed in an anonymous data object, from the
/// current block and end the block.
///
/// The builder is left in a filled block: the caller switches to another
/// block before emitting anything else.
pub(crate) fn emit_raise<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic: PanicHandle,
    source: PanicSource,
    span: Span,
) -> Result<(), CranelispError> {
    let bytes = source.message();
    let codegen_error =
        |what: &str, e: cranelift_module::ModuleError| CranelispError::CodegenError {
            message: format!("failed to {what} panic data: {e}"),
            location: ErrorLocation::from_span(span),
        };
    let data_id = module
        .declare_anonymous_data(false, false)
        .map_err(|e| codegen_error("declare", e))?;
    let mut desc = DataDescription::new();
    desc.define(bytes.to_vec().into_boxed_slice());
    module
        .define_data(data_id, &desc)
        .map_err(|e| codegen_error("define", e))?;
    let gv = module.declare_data_in_func(data_id, builder.func);
    let msg_ptr = builder.ins().global_value(types::I64, gv);
    let msg_len = builder.ins().iconst(types::I64, bytes.len() as i64);
    let panic_ref = module.declare_func_in_func(panic.0, builder.func);
    builder.ins().call(panic_ref, &[msg_ptr, msg_len]);
    builder.ins().trap(RAISE_RETURNED);
    Ok(())
}

#[cfg(test)]
impl PanicHandle {
    /// Declare `runtime/panic` alone, with its catalog signature, for a
    /// fixture that renders a raise without the whole intrinsic catalog.
    pub(crate) fn declare_alone<M: Module>(module: &mut M) -> Self {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        let id = module
            .declare_function(PANIC_SYMBOL, cranelift_module::Linkage::Import, &sig)
            .expect("declare runtime/panic");
        PanicHandle(id)
    }

    /// The id, for a fixture that locates the call in rendered CLIF.
    pub(crate) fn func_id(self) -> FuncId {
        self.0
    }
}

#[cfg(test)]
mod tests;
