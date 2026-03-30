//! Macro expansion environment and free functions.
//!
//! Owns compiled macro function pointers and performs expansion.
//! Lives in the binary crate because it wires typecheck + backend.

use std::collections::HashMap;
use std::sync::RwLock;

use cranelisp_types::{
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

/// Macro environment: name -> compiled macro.
///
/// Wrapped in `RwLock` internally so that concurrent `compile_unit` calls
/// can expand macros (read lock) while `compile_macro` takes a write lock.
pub struct MacroEnv {
    macros: RwLock<HashMap<Symbol, MacroEntry>>,
}

// SAFETY: MacroEntry contains *const u8 (JIT function pointers) which are
// valid for the lifetime of the Jit instance. These pointers are only read
// (called) during macro expansion, never mutated. The RwLock provides the
// necessary synchronization for concurrent access to the HashMap.
unsafe impl Send for MacroEnv {}
unsafe impl Sync for MacroEnv {}

impl MacroEnv {
    /// Create a new macro environment with no registered macros.
    pub fn new() -> Self {
        MacroEnv {
            macros: RwLock::new(HashMap::new()),
        }
    }

    /// Remove a macro from the environment.
    ///
    /// Used during module hot-reload to clear old macros before
    /// recompiling the module that defined them.
    pub fn remove_macro(&mut self, name: &str) {
        self.macros.write()
            .expect("macro env write lock poisoned")
            .remove(name);
    }

    /// Check whether a name is a known macro.
    pub fn is_macro(&self, name: &str) -> bool {
        self.macros.read()
            .expect("macro env read lock poisoned")
            .contains_key(name)
    }

    /// Compile a macro from a parsed DefmacroInfo and register it.
    ///
    /// For each clause:
    /// 1. Expand quasiquotes in the body Sexp
    /// 2. Call `synthesize_macro_clause_defn` to produce a defn Sexp
    /// 3. Parse the defn Sexp through the frontend (build_program)
    /// 4. Typecheck the resulting program
    /// 5. Compile via backend and extract the function pointer
    /// 6. Store the compiled clause in the MacroEnv
    pub fn compile_macro(
        &mut self,
        info: &cranelisp_frontend::DefmacroInfo,
        tc: &mut cranelisp_typecheck::TypeChecker,
        jit: &mut cranelisp_backend::jit::Jit,
    ) -> Result<(), CranelispError> {
        let mut compiled_clauses = Vec::new();

        for (clause_idx, clause) in info.clauses.iter().enumerate() {
            let func_ptr = compile_single_clause(
                &info.name,
                clause_idx,
                clause,
                info.span,
                self,
                tc,
                jit,
            )?;

            compiled_clauses.push(MacroClauseEntry {
                func_ptr,
                params: clause.fixed_params.clone(),
                rest_param: clause.rest_param.clone(),
            });
        }

        self.macros.write()
            .expect("macro env write lock poisoned")
            .insert(
                info.name.clone(),
                MacroEntry {
                    clauses: compiled_clauses,
                    docstring: info.docstring.clone(),
                },
            );

        Ok(())
    }

    /// Recursively expand a Sexp tree, replacing macro calls with their expansions.
    ///
    /// Walks the tree looking for list forms whose head is a known macro name.
    /// Also handles bare symbols that are zero-arg macros.
    /// Depth limit prevents infinite expansion.
    pub fn expand_sexp(&self, sexp: Sexp) -> Result<Sexp, CranelispError> {
        let macros = self.macros.read()
            .expect("macro env read lock poisoned");
        expand_sexp_recursive(sexp, &macros, 0)
    }
}

impl Default for MacroEnv {
    fn default() -> Self {
        Self::new()
    }
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
            span,
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
            span,
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
            Err(CranelispError::MacroError { message, span })
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
            Err(CranelispError::MacroError { message, span })
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
    macros: &HashMap<Symbol, MacroEntry>,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    if depth > EXPANSION_DEPTH_LIMIT {
        return Err(CranelispError::MacroError {
            message: format!(
                "macro expansion depth limit ({EXPANSION_DEPTH_LIMIT}) exceeded"
            ),
            span: sexp.span(),
        });
    }

    match sexp {
        Sexp::List(ref children, span) if !children.is_empty() => {
            // Check if head is a macro name.
            if let Sexp::Symbol(ref name, _) = children[0]
                && macros.contains_key(name.as_str())
            {
                let args = &children[1..];
                return expand_macro_call(name, args, span, macros, depth);
            }
            // Not a macro call — recurse into children.
            let Sexp::List(children, span) = sexp else {
                unreachable!("invariant: sexp matched Sexp::List in outer arm");
            };
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp_recursive(c, macros, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(expanded, span))
        }
        Sexp::Symbol(ref name, span) => {
            // Bare symbol: check for zero-arg macro.
            if macros.contains_key(name.as_str()) {
                return expand_macro_call(name, &[], span, macros, depth);
            }
            Ok(sexp)
        }
        Sexp::Bracket(children, span) => {
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp_recursive(c, macros, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(expanded, span))
        }
        _ => Ok(sexp),
    }
}

/// Expand a single macro call, then re-expand the result.
pub(crate) fn expand_macro_call(
    name: &str,
    args: &[Sexp],
    span: Span,
    macros: &HashMap<Symbol, MacroEntry>,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    let entry = macros.get(name).ok_or_else(|| {
        CranelispError::MacroError {
            message: format!("unknown macro '{name}'"),
            span,
        }
    })?;

    let clause = find_matching_clause(&entry.clauses, args).ok_or_else(|| {
        CranelispError::MacroError {
            message: format!(
                "no matching clause for macro '{name}' with {} arguments",
                args.len()
            ),
            span,
        }
    })?;

    let mut result = invoke_clause(clause, args, span)?;
    rewrite_spans(&mut result, span);

    // Re-expand the result.
    expand_sexp_recursive(result, macros, depth + 1)
}

// ---------------------------------------------------------------------------
// Single clause compilation
// ---------------------------------------------------------------------------

/// Compile a single macro clause through the full pipeline.
///
/// 1. Synthesize a defn Sexp from the clause
/// 2. Expand quasiquotes in the synthesized Sexp
/// 3. Build AST via the frontend (using the current expander for inner macro calls)
/// 4. Typecheck the resulting program
/// 5. Compile and extract the function pointer
pub(crate) fn compile_single_clause(
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    macro_env: &MacroEnv,
    tc: &mut cranelisp_typecheck::TypeChecker,
    jit: &mut cranelisp_backend::jit::Jit,
) -> Result<*const u8, CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(),
        clause_idx,
        clause,
        span,
    );

    // Step 2: Expand quasiquotes in the synthesized Sexp.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 2b: Expand any macro calls in the body (e.g., a macro clause
    // that uses an earlier macro like `(defmacro id2 [x] (id x))`).
    // Previously the CraneliftExpander was passed to build_program for
    // inline expansion; now we expand at the Sexp level before AST building.
    let expanded_sexp = macro_env.expand_sexp(expanded_sexp)?;

    // Step 3: Build AST from the fully-expanded sexp.
    let program = cranelisp_frontend::build_program(&[expanded_sexp])?;

    // Step 4: Typecheck.
    let ctx = cranelisp_types::CompileContext {
        module: tc.current_module_path().clone(),
        codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
    };
    let check = tc.check(&program, &ctx, cranelisp_types::ModuleStrategy::Additive)?;

    // Step 5: Compile.
    // Extract the single defn from the program.
    let defn = program
        .iter()
        .find_map(|tl| match tl {
            cranelisp_types::TopLevel::Defn(d) => Some(d),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!("macro clause {clause_idx} for '{macro_name}' produced no defn"),
            span,
        })?;

    // Declare the function in the JIT.
    let func_ids = jit.declare_functions(&[defn])?;
    let func_arities: HashMap<Symbol, usize> =
        func_ids.keys().map(|n| (n.clone(), defn.params().len())).collect();

    // Build compile context and compile.
    // Disable dealloc so no rc_dec is emitted: macro functions build
    // throwaway Sexp trees that are marshalled back to the compiler.
    // All allocations are leaked by design (see marshal.rs header).
    // Without this override, scope cleanup dec's match-extracted Sexp
    // values whose pointers are stored in the newly-built result tree,
    // causing use-after-free on unmarshal.
    let mut compile_ctx = jit.build_compile_context(
        &check,
        &func_ids,
        &func_arities,
        None,
        None,
        None,
    );
    compile_ctx.dealloc_func_id = None;
    jit.compile_defn(defn, compile_ctx)?;

    // Finalize and get the function pointer.
    let ptr = jit.finalize_and_get_ptr(&defn.name, defn.params().len())?;

    Ok(ptr)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Span;

    /// Helper: create a fresh TypeChecker and Jit for testing.
    fn setup() -> (cranelisp_typecheck::TypeChecker, cranelisp_backend::jit::Jit) {
        let tc = cranelisp_typecheck::TypeChecker::new();
        let mut jit = cranelisp_backend::jit::Jit::new().unwrap();
        jit.declare_intrinsics().unwrap();
        (tc, jit)
    }

    /// Helper: parse source text into a single Sexp.
    fn parse_one(src: &str) -> Sexp {
        let sexps = cranelisp_frontend::parse(src).expect("parse failed");
        assert_eq!(sexps.len(), 1, "expected exactly one sexp");
        sexps.into_iter().next().unwrap()
    }

    // spec: 09-macros.md section 9.2 — simple identity macro compile and expand
    #[test]
    fn test_identity_macro() {
        let (mut tc, mut jit) = setup();
        let mut macro_env = MacroEnv::new();

        // Parse and compile: (defmacro id [x] x)
        let sexp = parse_one("(defmacro id [x] x)");
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        macro_env.compile_macro(&info, &mut tc, &mut jit).unwrap();

        // Expand: (id 42) should produce 42
        let call_sexp = parse_one("(id 42)");
        let result = macro_env.expand_sexp(call_sexp).unwrap();
        assert!(
            matches!(result, Sexp::Int(42, _)),
            "expected Int(42), got {:?}",
            result
        );
    }

    // spec: 09-macros.md section 9.4.2 — quasiquote macro compile and expand
    #[test]
    fn test_quasiquote_macro() {
        let (mut tc, mut jit) = setup();
        let mut macro_env = MacroEnv::new();

        // Parse and compile: (defmacro wrap [x] `(+ 1 ~x))
        let sexp = parse_one("(defmacro wrap [x] `(+ 1 ~x))");
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        macro_env.compile_macro(&info, &mut tc, &mut jit).unwrap();

        // Expand: (wrap 42) should produce (+ 1 42)
        let call_sexp = parse_one("(wrap 42)");
        let result = macro_env.expand_sexp(call_sexp).unwrap();
        if let Sexp::List(children, _) = &result {
            assert_eq!(children.len(), 3, "expected 3 children in (+ 1 42)");
            assert!(matches!(&children[0], Sexp::Symbol(s, _) if s == "+"));
            assert!(matches!(&children[1], Sexp::Int(1, _)));
            assert!(matches!(&children[2], Sexp::Int(42, _)));
        } else {
            panic!("expected List, got {:?}", result);
        }
    }

    // spec: 09-macros.md section 9.2.6 — multi-clause dispatch
    #[test]
    fn test_multi_clause_dispatch() {
        let (mut tc, mut jit) = setup();
        let mut macro_env = MacroEnv::new();

        // Two clauses: 1-arg returns arg, 2-arg returns first arg
        let sexp = parse_one(
            "(defmacro pick ([x] x) ([x y] x))"
        );
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        macro_env.compile_macro(&info, &mut tc, &mut jit).unwrap();

        // 1-arg call
        let call1 = parse_one("(pick 42)");
        let result1 = macro_env.expand_sexp(call1).unwrap();
        assert!(
            matches!(result1, Sexp::Int(42, _)),
            "1-arg: expected Int(42), got {:?}",
            result1
        );

        // 2-arg call should return first arg
        let call2 = parse_one("(pick 10 20)");
        let result2 = macro_env.expand_sexp(call2).unwrap();
        assert!(
            matches!(result2, Sexp::Int(10, _)),
            "2-arg: expected Int(10), got {:?}",
            result2
        );
    }

    // spec: 09-macros.md section 9.2 — is_macro predicate
    #[test]
    fn test_is_macro_predicate() {
        let (mut tc, mut jit) = setup();
        let mut macro_env = MacroEnv::new();

        assert!(!macro_env.is_macro("id"));

        let sexp = parse_one("(defmacro id [x] x)");
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        macro_env.compile_macro(&info, &mut tc, &mut jit).unwrap();

        assert!(macro_env.is_macro("id"));
        assert!(!macro_env.is_macro("nonexistent"));
    }

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

    // spec: 09-macros.md section 9.4.2 — quasiquote macro with bracket
    #[test]
    fn test_quasiquote_bracket_macro() {
        let (mut tc, mut jit) = setup();
        let mut macro_env = MacroEnv::new();

        // Parse and compile: (defmacro my-let [n v body] `(let [~n ~v] ~body))
        let sexp = parse_one("(defmacro my-let [n v body] `(let [~n ~v] ~body))");
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        macro_env.compile_macro(&info, &mut tc, &mut jit).unwrap();

        // Expand: (my-let x 10 (add-i64 x 5))
        let call_sexp = parse_one("(my-let x 10 (add-i64 x 5))");
        let result = macro_env.expand_sexp(call_sexp).unwrap();
        // Should produce (let [x 10] (add-i64 x 5))
        if let Sexp::List(children, _) = &result {
            assert_eq!(children.len(), 3, "expected 3 children: let, bracket, body");
            assert!(matches!(&children[0], Sexp::Symbol(s, _) if s == "let"),
                "head should be 'let', got {:?}", children[0]);
            assert!(matches!(&children[1], Sexp::Bracket(_, _)),
                "second should be Bracket, got {:?}", children[1]);
            if let Sexp::Bracket(inner, _) = &children[1] {
                assert_eq!(inner.len(), 2, "bracket should have 2 elements");
            }
        } else {
            panic!("expected List, got {:?}", result);
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
