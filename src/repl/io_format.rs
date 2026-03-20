// IO forcing and trampoline: execute IO trees and format results.

use std::collections::HashMap;
use std::io::Write;

use cranelisp_backend::display;
use cranelisp_types::{ModuleFullPath, Type, TypeDefInfo, TypeName};

/// Force an IO tree via the trampoline and format the inner result.
///
/// Side effects (printing, etc.) execute during the trampoline run and are
/// flushed to stdout before this function returns the display string.
/// The trampoline is wrapped in `catch_unwind` so a malformed IO tree
/// does not crash the REPL session.
///
/// Returns a display string for the inner value with the full IO type
/// annotation, wrapping the formatted value in `(IO.Pure ...)`,
/// e.g. `:(IO primitives/Int) (IO.Pure 42)`.
pub(crate) fn force_io_and_format(
    io_value: i64,
    io_ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
    stdout: &mut impl Write,
) -> String {
    // Flush stdout before trampolining so any prior output appears first,
    // and side-effect output (e.g., print) appears in order.
    let _ = stdout.flush();

    let trampoline_result = std::panic::catch_unwind(|| {
        // SAFETY: io_value is a valid IO tree pointer produced by JIT code.
        // The IO tree remains live because the caller holds the ReplResult
        // which owns the i64 value, and the trampoline processes it
        // synchronously before returning.
        cranelisp_runtime::run_io_trampoline(io_value)
    });

    let inner_ty = io_ty.io_inner_type();
    let type_str = display::format_type_qualified(io_ty, type_modules);

    match trampoline_result {
        Ok(inner_val) => {
            let val_str = display::format_value(inner_val, &inner_ty, type_defs, type_modules);
            format!(":{type_str} (IO.Pure {val_str})")
        }
        Err(_) => {
            format!(":{type_str} <IO trampoline panicked>")
        }
    }
}
