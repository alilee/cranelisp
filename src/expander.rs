//! Macro expansion: trait-based resolution and recursive expansion.
//!
//! Provides the `MacroResolver` trait for macro lookup during expansion,
//! and free functions for clause matching, invocation, and span rewriting.
//! Lives in the binary crate because it wires typecheck + backend.

use cranelisp_types::{ErrorLocation, 
    CranelispError, MacroParam, Sexp, Span, Symbol,
    NULLARY_TAG_THRESHOLD,
};

use crate::marshal;

/// Maximum recursion depth for macro expansion.
pub(crate) const EXPANSION_DEPTH_LIMIT: usize = 100;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A compiled macro clause with its function pointer.
pub(crate) struct MacroClauseEntry {
    /// JIT-compiled function: extern "C" fn(i64) -> i64.
    /// The i64 parameter is a pointer to an (SList Sexp) of marshalled args.
    pub(crate) func_ptr: *const u8,
    /// Fixed parameter patterns (for clause matching).
    pub(crate) params: Vec<MacroParam>,
    /// Rest parameter name, if variadic.
    pub(crate) rest_param: Option<Symbol>,
}

/// A registered macro with all its compiled clauses.
pub(crate) struct MacroEntry {
    pub(crate) clauses: Vec<MacroClauseEntry>,
    #[allow(dead_code)] // Reserved for REPL introspection (/doc command)
    pub(crate) docstring: Option<String>,
}

// ---------------------------------------------------------------------------
// MacroResolver trait
// ---------------------------------------------------------------------------

/// Trait for resolving macro names to compiled entries during expansion.
///
/// Implementations look up the symbol table, follow import chains, and
/// optionally compile macros on demand. The `&mut self` receiver allows
/// on-demand compilation (the `SymbolTableMacroResolver` in worker.rs
/// compiles macro clauses the first time they are referenced).
pub(crate) trait MacroResolver {
    /// Resolve a name to a compiled macro entry, if one exists.
    ///
    /// Returns:
    /// - `Ok(Some(entry))` — name is a macro, here are its compiled clauses
    /// - `Ok(None)` — name is not a macro (or not visible in the current scope)
    /// - `Err(...)` — lookup or on-demand compilation failed
    fn resolve_macro(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<MacroEntry>, CranelispError>;
}

// ---------------------------------------------------------------------------
// Clause matching
// ---------------------------------------------------------------------------

/// Check whether a clause's parameter pattern matches the given arguments.
///
/// - If clause has rest_param: args.len() >= clause.params.len()
/// - If no rest_param: args.len() == clause.params.len()
/// - Bracket params must receive Sexp::Bracket arguments
pub(crate) fn clause_matches(clause: &MacroClauseEntry, args: &[Sexp]) -> bool {
    let fixed_count = clause.params.len();
    if clause.rest_param.is_some() {
        if args.len() < fixed_count {
            return false;
        }
    } else if args.len() != fixed_count {
        return false;
    }

    // Check bracket params match Sexp::Bracket arguments.
    for (i, param) in clause.params.iter().enumerate() {
        if let MacroParam::Bracket { fixed, rest } = param {
            if i >= args.len() {
                return false;
            }
            if let Sexp::Bracket(items, _) = &args[i] {
                // Check element count compatibility.
                if rest.is_some() {
                    if items.len() < fixed.len() {
                        return false;
                    }
                } else if items.len() != fixed.len() {
                    return false;
                }
            } else {
                return false; // Bracket param requires Bracket arg
            }
        }
    }

    true
}

/// Find the first matching clause for the given arguments.
pub(crate) fn find_matching_clause<'a>(
    clauses: &'a [MacroClauseEntry],
    args: &[Sexp],
) -> Option<&'a MacroClauseEntry> {
    clauses.iter().find(|c| clause_matches(c, args))
}

// ---------------------------------------------------------------------------
// Clause invocation
// ---------------------------------------------------------------------------

/// Marshal arguments, invoke a clause's function pointer, and unmarshal the result.
pub(crate) fn invoke_clause(
    clause: &MacroClauseEntry,
    args: &[Sexp],
    span: Span,
) -> Result<Sexp, CranelispError> {
    // Marshal each argument to a runtime Sexp ADT value.
    let marshalled: Vec<i64> = args.iter().map(marshal::sexp_to_runtime).collect();

    // Bump RC on each marshalled Sexp element. The compiled macro function
    // uses a consuming calling convention: it decrements RC on its args
    // parameter (SList) via drop glue, which also decrements each Sexp
    // element inside. Without this extra inc, elements extracted from the
    // args and stored in the result would be freed during parameter cleanup.
    for &val in &marshalled {
        marshal::rc_inc(val);
    }

    // Package all args as an (SList Sexp).
    let args_slist = marshal::build_runtime_slist(&marshalled);

    // Invoke the compiled function with signal protection.
    // JIT code may trigger hardware traps (e.g., division by zero -> SIGFPE,
    // illegal instruction -> SIGILL). We install temporary signal handlers
    // that convert these signals to Rust panics, then use catch_unwind
    // to turn them into clean CranelispError results.
    let result_i64 = invoke_jit_protected(clause.func_ptr, args_slist, span)?;

    // Validate the result is a heap pointer (all Sexp constructors are data).
    if result_i64 < NULLARY_TAG_THRESHOLD as i64 {
        return Err(CranelispError::MacroError {
            message: format!(
                "macro returned invalid value {result_i64} (expected heap pointer)"
            ),
            location: ErrorLocation::from_span(span),
        });
    }

    // Unmarshal the result back to a compiler Sexp.
    Ok(marshal::runtime_to_sexp(result_i64))
}

/// Invoke a JIT function pointer with crash protection.
///
/// Uses `catch_unwind` to catch Rust panics from `runtime_panic`. Also
/// installs signal handlers for SIGFPE/SIGILL/SIGBUS that use
/// `sigsetjmp`/`siglongjmp` to recover from hardware traps without
/// unwinding through the JIT code frames.
///
/// On macOS/aarch64, division by zero in JIT code raises SIGFPE. The signal
/// handler `siglongjmp`s back to the recovery point, avoiding the problem
/// of unwinding through `extern "C"` frames.
fn invoke_jit_protected(
    func_ptr: *const u8,
    args_slist: i64,
    span: Span,
) -> Result<i64, CranelispError> {
    use std::panic::{catch_unwind, AssertUnwindSafe};

    // catch_unwind handles Rust panics from runtime_panic.
    let result = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: We use sigsetjmp/siglongjmp (declared below via raw FFI)
        // to recover from hardware traps. sigsetjmp saves the execution
        // context; if a signal handler calls siglongjmp, control returns
        // to the sigsetjmp call with a non-zero value (the signal number).
        unsafe {
            // Set up the jump buffer for signal recovery.
            let sig = sigsetjmp(JMP_BUF.with(|buf| buf.get()), 1);
            if sig != 0 {
                // Got here via siglongjmp from signal handler.
                return Err(sig);
            }

            // Install signal handlers that siglongjmp back on trap.
            let old_handlers = install_signal_handlers();

            let func: extern "C" fn(i64) -> i64 = std::mem::transmute(func_ptr);
            // Clear any stale error before the JIT call.
            let _ = cranelisp_runtime::panic::take_runtime_error();
            let result_i64 = func(args_slist);

            // Restore original signal handlers.
            restore_signal_handlers(old_handlers);

            Ok(result_i64)
        }
    }));

    // Check thread-local error flag (set by runtime_panic in JIT code).
    if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
        return Err(CranelispError::MacroError {
            message: format!("runtime error during macro expansion: {msg}"),
            location: ErrorLocation::from_span(span),
        });
    }

    match result {
        Ok(Ok(val)) => Ok(val),
        Ok(Err(sig)) => {
            // Signal caught via siglongjmp.
            let message = match sig {
                libc::SIGFPE => "runtime error during macro expansion: arithmetic exception (division by zero)".to_string(),
                libc::SIGILL => "runtime error during macro expansion: illegal instruction".to_string(),
                libc::SIGBUS => "runtime error during macro expansion: bus error".to_string(),
                _ => format!("runtime error during macro expansion: signal {sig}"),
            };
            Err(CranelispError::MacroError { message, location: ErrorLocation::from_span(span) })
        }
        Err(panic_payload) => {
            // Rust panic caught (e.g., from runtime_panic).
            let message = if let Some(s) = panic_payload.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic_payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else {
                "unknown runtime error during macro expansion".to_string()
            };
            Err(CranelispError::MacroError { message, location: ErrorLocation::from_span(span) })
        }
    }
}

// ---------------------------------------------------------------------------
// sigsetjmp/siglongjmp FFI (not in the `libc` crate)
// ---------------------------------------------------------------------------

// On macOS/aarch64, sigjmp_buf is 196 bytes (jmp_buf + signal mask).
// We use a conservatively sized array. The exact layout is opaque.
#[cfg(target_os = "macos")]
type SigJmpBuf = [u8; 196];

#[cfg(not(target_os = "macos"))]
type SigJmpBuf = [u8; 256]; // Conservative fallback for other platforms

unsafe extern "C" {
    /// POSIX sigsetjmp: save execution context and optionally signal mask.
    /// Returns 0 on direct call, non-zero value (from siglongjmp) on return.
    fn sigsetjmp(env: *mut SigJmpBuf, savesigs: libc::c_int) -> libc::c_int;

    /// POSIX siglongjmp: restore execution context saved by sigsetjmp.
    fn siglongjmp(env: *mut SigJmpBuf, val: libc::c_int) -> !;
}

// Thread-local jump buffer for signal recovery during JIT macro execution.
// Only accessed by the signal handler and invoke_jit_protected on the same
// thread. Signal delivery for SIGFPE/SIGILL/SIGBUS is synchronous (delivered
// to the thread that caused the trap).
std::thread_local! {
    static JMP_BUF: std::cell::UnsafeCell<SigJmpBuf> =
        const { std::cell::UnsafeCell::new([0u8; std::mem::size_of::<SigJmpBuf>()]) };
}

/// Signal handler for SIGFPE/SIGILL/SIGBUS during JIT macro execution.
///
/// Uses siglongjmp to jump back to the sigsetjmp point, bypassing the
/// JIT code frames entirely. This avoids the problem of unwinding through
/// `extern "C"` frames (which would be UB).
extern "C" fn signal_handler_longjmp(sig: libc::c_int) {
    unsafe {
        // Reset to default handler to prevent infinite signal loops.
        libc::signal(sig, libc::SIG_DFL);
        // Jump back to sigsetjmp, passing the signal number.
        siglongjmp(JMP_BUF.with(|buf| buf.get() as *mut SigJmpBuf), sig);
    }
}

/// Saved signal handler state for restoration after JIT call.
struct SavedSignalHandlers {
    fpe: libc::sighandler_t,
    ill: libc::sighandler_t,
    bus: libc::sighandler_t,
}

/// Install signal handlers that siglongjmp on SIGFPE/SIGILL/SIGBUS.
/// Returns the previously installed handlers for later restoration.
fn install_signal_handlers() -> SavedSignalHandlers {
    unsafe {
        let handler = signal_handler_longjmp as *const () as libc::sighandler_t;
        let fpe = libc::signal(libc::SIGFPE, handler);
        let ill = libc::signal(libc::SIGILL, handler);
        let bus = libc::signal(libc::SIGBUS, handler);
        SavedSignalHandlers { fpe, ill, bus }
    }
}

/// Restore previously saved signal handlers.
fn restore_signal_handlers(saved: SavedSignalHandlers) {
    unsafe {
        libc::signal(libc::SIGFPE, saved.fpe);
        libc::signal(libc::SIGILL, saved.ill);
        libc::signal(libc::SIGBUS, saved.bus);
    }
}

// ---------------------------------------------------------------------------
// Span rewriting
// ---------------------------------------------------------------------------

/// Recursively replace all spans in a Sexp tree with unique synthetic spans.
///
/// Each node gets a fresh span from the global synthetic span counter. This
/// prevents span collisions when the same macro parameter appears multiple
/// times in the expansion — downstream maps keyed by span (expr_types,
/// method_resolutions, last_uses) would otherwise overwrite each other.
pub(crate) fn rewrite_spans(sexp: &mut Sexp, _call_site_span: Span) {
    rewrite_spans_unique(sexp);
}

/// Assign a unique synthetic span to every node in the Sexp tree.
fn rewrite_spans_unique(sexp: &mut Sexp) {
    match sexp {
        Sexp::Symbol(_, s)
        | Sexp::Int(_, s)
        | Sexp::Float(_, s)
        | Sexp::Bool(_, s)
        | Sexp::Str(_, s) => *s = cranelisp_frontend::next_synthetic_span(),
        Sexp::List(children, s) | Sexp::Bracket(children, s) => {
            for child in children {
                rewrite_spans_unique(child);
            }
            *s = cranelisp_frontend::next_synthetic_span();
        }
        Sexp::Comment(_, s) => *s = cranelisp_frontend::next_synthetic_span(),
    }
}

// ---------------------------------------------------------------------------
// Recursive expansion
// ---------------------------------------------------------------------------

/// Recursively expand macro calls in a Sexp tree.
///
/// Handles:
/// - List forms where head is a known macro -> dispatch and re-expand result
/// - Bare symbols that are zero-arg macros
/// - Recursive children expansion
pub(crate) fn expand_sexp_recursive(
    sexp: Sexp,
    resolver: &mut dyn MacroResolver,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    if depth > EXPANSION_DEPTH_LIMIT {
        return Err(CranelispError::MacroError {
            message: format!(
                "macro expansion depth limit ({EXPANSION_DEPTH_LIMIT}) exceeded"
            ),
            location: ErrorLocation::from_span(sexp.span()),
        });
    }

    match sexp {
        Sexp::List(ref children, span) if !children.is_empty() => {
            // Check if head is a macro name.
            if let Sexp::Symbol(ref name, sym_span) = children[0]
                && let Some(entry) = resolver.resolve_macro(name, sym_span)? {
                    let args = &children[1..];
                    return expand_macro_call_with_entry(
                        name, args, span, &entry, resolver, depth,
                    );
                }
            // Not a macro call — recurse into children.
            let Sexp::List(children, span) = sexp else {
                unreachable!("invariant: sexp matched Sexp::List in outer arm");
            };
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp_recursive(c, resolver, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(expanded, span))
        }
        Sexp::Symbol(ref name, span) => {
            // Bare symbol: check for zero-arg macro.
            if let Some(entry) = resolver.resolve_macro(name, span)? {
                return expand_macro_call_with_entry(
                    name, &[], span, &entry, resolver, depth,
                );
            }
            Ok(sexp)
        }
        Sexp::Bracket(children, span) => {
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp_recursive(c, resolver, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(expanded, span))
        }
        _ => Ok(sexp),
    }
}

/// Expand a single macro call given a resolved entry, then re-expand the result.
pub(crate) fn expand_macro_call_with_entry(
    name: &str,
    args: &[Sexp],
    span: Span,
    entry: &MacroEntry,
    resolver: &mut dyn MacroResolver,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    let clause = find_matching_clause(&entry.clauses, args).ok_or_else(|| {
        CranelispError::MacroError {
            message: format!(
                "no matching clause for macro '{name}' with {} arguments",
                args.len()
            ),
            location: ErrorLocation::from_span(span),
        }
    })?;

    let mut result = invoke_clause(clause, args, span)?;
    rewrite_spans(&mut result, span);

    // Re-expand the result (may contain further macro calls).
    expand_sexp_recursive(result, resolver, depth + 1)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Span;

    // spec: 09-macros.md section 9.7 — marshal round-trip via expand
    #[test]
    fn test_marshal_roundtrip_all_variants() {
        // Test all Sexp variants through marshal round-trip.
        let cases: Vec<Sexp> = vec![
            Sexp::Int(42, Span::SYNTHETIC),
            Sexp::Int(-1, Span::SYNTHETIC),
            Sexp::Float(2.5, Span::SYNTHETIC),
            Sexp::Bool(true, Span::SYNTHETIC),
            Sexp::Bool(false, Span::SYNTHETIC),
            Sexp::Str("hello world".to_string(), Span::SYNTHETIC),
            Sexp::Symbol("my-var".to_string(), Span::SYNTHETIC),
            Sexp::List(
                vec![Sexp::Int(1, Span::SYNTHETIC), Sexp::Int(2, Span::SYNTHETIC)],
                Span::SYNTHETIC,
            ),
            Sexp::Bracket(
                vec![Sexp::Symbol("x".to_string(), Span::SYNTHETIC)],
                Span::SYNTHETIC,
            ),
        ];

        for case in &cases {
            let rt = marshal::sexp_to_runtime(case);
            let back = marshal::runtime_to_sexp(rt);
            match (case, &back) {
                (Sexp::Int(a, _), Sexp::Int(b, _)) => assert_eq!(a, b),
                (Sexp::Float(a, _), Sexp::Float(b, _)) => {
                    assert!((a - b).abs() < f64::EPSILON);
                }
                (Sexp::Bool(a, _), Sexp::Bool(b, _)) => assert_eq!(a, b),
                (Sexp::Str(a, _), Sexp::Str(b, _)) => assert_eq!(a, b),
                (Sexp::Symbol(a, _), Sexp::Symbol(b, _)) => assert_eq!(a, b),
                (Sexp::List(a, _), Sexp::List(b, _)) => assert_eq!(a.len(), b.len()),
                (Sexp::Bracket(a, _), Sexp::Bracket(b, _)) => assert_eq!(a.len(), b.len()),
                _ => panic!(
                    "variant mismatch: {:?} vs {:?}",
                    std::mem::discriminant(case),
                    std::mem::discriminant(&back)
                ),
            }
        }
    }

    // spec: 09-macros.md section 9.7 — SList round-trip
    #[test]
    fn test_slist_roundtrip() {
        let items = vec![
            marshal::sexp_to_runtime(&Sexp::Int(1, Span::SYNTHETIC)),
            marshal::sexp_to_runtime(&Sexp::Symbol("x".to_string(), Span::SYNTHETIC)),
            marshal::sexp_to_runtime(&Sexp::Str("hello".to_string(), Span::SYNTHETIC)),
        ];
        let _slist = marshal::build_runtime_slist(&items);

        // Read back by wrapping in a SexpList and reading.
        let wrapped = Sexp::List(
            vec![
                Sexp::Int(1, Span::SYNTHETIC),
                Sexp::Symbol("x".to_string(), Span::SYNTHETIC),
                Sexp::Str("hello".to_string(), Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let rt = marshal::sexp_to_runtime(&wrapped);
        let back = marshal::runtime_to_sexp(rt);
        if let Sexp::List(children, _) = back {
            assert_eq!(children.len(), 3);
            assert!(matches!(&children[0], Sexp::Int(1, _)));
            assert!(matches!(&children[1], Sexp::Symbol(s, _) if s == "x"));
            assert!(matches!(&children[2], Sexp::Str(s, _) if s == "hello"));
        } else {
            panic!("expected List");
        }
    }
}
