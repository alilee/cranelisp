//! The one emitter of a runtime panic (`design/backend/backend.md` §7).
//!
//! A raise places its message, calls `runtime/panic(msg_ptr, msg_len)` and
//! ends the block with a trap. `runtime/panic` never returns, so the trap
//! never executes; it is there so no emitted code follows the call. Every
//! panic site emits through [`emit_raise`], which is the only place in the
//! crate that makes a `FuncRef` for `runtime/panic` (census:
//! `raise::tests::raise_helper_is_the_only_panic_call_emitter`).

use cranelift::prelude::*;
use cranelift_module::{DataDescription, FuncId, Module};

use cranelisp_types::{CranelispError, ErrorLocation, Span};

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

/// Where a raise's message bytes come from.
pub(crate) enum RaiseMessage {
    /// A panic source's message, placed in an anonymous data object.
    Source(PanicSource),
    /// Bytes at a host address baked into the code. The caller keeps them
    /// alive for as long as the code may run.
    Baked { ptr: *const u8, len: usize },
}

/// The declared `runtime/panic`, or the located codegen error for a module
/// that lacks it.
pub(crate) fn declared(
    panic_func_id: Option<FuncId>,
    span: Span,
) -> Result<FuncId, CranelispError> {
    panic_func_id.ok_or_else(|| CranelispError::CodegenError {
        message: "runtime/panic not declared".into(),
        location: ErrorLocation::from_span(span),
    })
}

/// Raise `message` from the current block and end the block.
///
/// The builder is left in a filled block: the caller switches to another
/// block before emitting anything else.
pub(crate) fn emit_raise<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic_func_id: FuncId,
    message: RaiseMessage,
    span: Span,
) -> Result<(), CranelispError> {
    let (msg_ptr, msg_len) = match message {
        RaiseMessage::Source(source) => {
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
            let ptr = builder.ins().global_value(types::I64, gv);
            let len = builder.ins().iconst(types::I64, bytes.len() as i64);
            (ptr, len)
        }
        RaiseMessage::Baked { ptr, len } => (
            builder.ins().iconst(types::I64, ptr as i64),
            builder.ins().iconst(types::I64, len as i64),
        ),
    };
    let panic_ref = module.declare_func_in_func(panic_func_id, builder.func);
    builder.ins().call(panic_ref, &[msg_ptr, msg_len]);
    builder.ins().trap(RAISE_RETURNED);
    Ok(())
}

#[cfg(test)]
mod tests;
