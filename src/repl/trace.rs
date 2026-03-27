// Trace support: display state, expression analysis, and compilation
// for `(trace ...)` special form in the REPL.
//
// The trace formatter needs access to type definitions and module mappings
// that live in ReplSession. We use a thread-local Cell to pass this state
// to the JIT-callable `repl_trace_format` function.

use std::cell::Cell;
use std::collections::HashMap;

use cranelisp_backend::display;
use cranelisp_types::{
    Expr, ModuleFullPath, Type, TypeDefInfo, TypeName,
};

// ── Trace value formatting ────────────────────────────────────────────────────

/// Display state for trace formatting. Holds references to the type definitions
/// and type-to-module mappings needed by `format_value`.
///
/// SAFETY: The raw pointer is valid for the duration of a single `execute_expr`
/// call -- set before JIT execution and cleared immediately after. The struct it
/// points to borrows from the ReplSession which does not move during execution.
pub(crate) struct TraceDisplayState {
    pub(crate) type_defs: *const HashMap<TypeName, TypeDefInfo>,
    pub(crate) type_modules: *const HashMap<TypeName, ModuleFullPath>,
}

// TraceDisplayState is only accessed via a thread-local Cell (never crosses
// thread boundaries), so Send/Sync are not required.

thread_local! {
    /// Thread-local pointer to the active display state, used by
    /// `repl_trace_format`. Set before JIT evaluation, cleared after.
    static TRACE_DISPLAY_STATE: Cell<*const TraceDisplayState> =
        const { Cell::new(std::ptr::null()) };
}

/// Set the trace display state before evaluating a trace expression.
pub(crate) fn set_trace_display_state(state: &TraceDisplayState) {
    TRACE_DISPLAY_STATE.with(|c| c.set(state as *const _));
}

/// Clear the trace display state after evaluation completes.
pub(crate) fn clear_trace_display_state() {
    TRACE_DISPLAY_STATE.with(|c| c.set(std::ptr::null()));
}

/// JIT-callable function: format a runtime value for trace display.
///
/// Reads the type pointer (a leaked `Box<Type>`) and the display state
/// (type_defs, type_modules) from thread-local storage, then calls
/// `display::format_value` to produce a formatted string.
///
/// Falls back to `"?"` if the display state has not been set.
///
/// Registered as an extra JIT symbol to override the runtime's fallback
/// `cranelisp_trace_format` when compiling trace expressions.
pub(crate) extern "C" fn repl_trace_format(val: i64, type_ptr: i64) -> i64 {
    TRACE_DISPLAY_STATE.with(|c| {
        let state_ptr = c.get();
        let s = if state_ptr.is_null() {
            "?".to_string()
        } else {
            // SAFETY: state_ptr was set by set_trace_display_state and
            // points to a valid TraceDisplayState on the caller's stack.
            // The Type pointer was leaked by trace_codegen (valid for program lifetime).
            let state = unsafe { &*state_ptr };
            let type_defs = unsafe { &*state.type_defs };
            let type_modules = unsafe { &*state.type_modules };
            let ty = unsafe { &*(type_ptr as *const Type) };
            display::format_value(val, ty, type_defs, type_modules)
        };
        cranelisp_runtime::alloc_string(s.as_bytes()) as i64
    })
}

// ── Trace expression analysis ─────────────────────────────────────────────────

/// Check if an expression tree contains a `(trace ...)` form anywhere.
///
/// Used to decide whether to build traced_fns and set up the trace display
/// state before compilation. This avoids the overhead for non-trace expressions.
pub(crate) fn expr_contains_trace(expr: &Expr) -> bool {
    match expr {
        Expr::Trace { .. } => true,
        Expr::Apply { callee, args, .. } => {
            // trace is a module-scoped special form (arch Principle 10).
            // It arrives as Apply(Var("trace"), [body]) -- detect it here.
            if let Expr::Var { name, .. } = callee.as_ref()
                && &**name == "trace"
            {
                return true;
            }
            expr_contains_trace(callee) || args.iter().any(expr_contains_trace)
        }
        Expr::Let { bindings, body, .. } => {
            bindings.iter().any(|(_, e)| expr_contains_trace(e))
                || expr_contains_trace(body)
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            expr_contains_trace(cond)
                || expr_contains_trace(then_branch)
                || expr_contains_trace(else_branch)
        }
        Expr::Lambda { body, .. } => expr_contains_trace(body),
        Expr::Match { scrutinee, arms, .. } => {
            expr_contains_trace(scrutinee)
                || arms.iter().any(|arm| expr_contains_trace(&arm.body))
        }
        Expr::Annotate { expr, .. } => expr_contains_trace(expr),
        Expr::VecLit { elements, .. } => elements.iter().any(expr_contains_trace),
        // ParBind is semantically like Let — check bindings and body for trace.
        Expr::ParBind { bindings, body, .. } => {
            bindings.iter().any(|(_, e)| expr_contains_trace(e))
                || expr_contains_trace(body)
        }
        // RunTests itself needs traced_fns for test discovery (GOT-swap tracing),
        // so it always triggers trace infrastructure, even without a nested (trace ...).
        Expr::RunTests { .. } => true,
        Expr::IntLit { .. }
        | Expr::BoolLit { .. }
        | Expr::FloatLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => false,
    }
}

