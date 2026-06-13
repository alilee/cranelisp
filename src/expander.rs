//! Macro expansion: the int-side **execution** half of the two-jobs split
//! (`design/arch/macro-expansion-ownership.md` §2.3).
//!
//! Per the S76 W-Macro LOCKED decision (`macro-availability-model.md` §0.7),
//! macro **recognition** is a `cranelisp-types` query
//! (`cranelisp_types::resolve_macro_head` over a caller-chosen [`View`]) and
//! macro **execution** is int's capability. This module provides:
//!
//! - [`JitMacroExpander`] — the int implementation of
//!   [`cranelisp_types::MacroExpander`] over the surviving invocation core
//!   (signal-protected JIT call + `Sexp`↔heap marshal). This is the only
//!   crate that may touch the JIT + runtime + `libc`.
//! - The invocation core (`find_matching_clause`, `invoke_clause`,
//!   `invoke_jit_protected`, `rewrite_spans`) that the impl wraps.
//!
//! ## Status (S76 W-Macro, fire B)
//!
//! Recognition is now the LOCKED `cranelisp_types::resolve_macro_head` query
//! (via [`recognize_macro_head`]); execution is the single
//! [`JitMacroExpander`] boundary impl. The in-place walk
//! ([`expand_sexp_recursive`]) survives as the live driver (the orchestrator's
//! Pass-1 three-pass loop with just-in-time dependency compilation is the
//! target shape — `macro-availability-model.md` §0.4 — but the as-built live
//! path is the worker-loop walk, not the dead `cluster::process_cluster`
//! scaffold). The walk's [`MacroResolver`] now does recognition + on-demand
//! clause compilation only; **all execution flows through `JitMacroExpander`**,
//! so there is exactly one executor (no `MacroEntry`-based parallel path).
//!
//! [`View`]: cranelisp_types::View

use cranelisp_types::{ErrorLocation,
    CranelispError, FQSymbol, MacroExpander, MacroInvokeError, MacroParam,
    ModuleAliases, ModuleEntry, ModuleFullPath, Sexp, Span, Symbol, View,
    DefKind, NULLARY_TAG_THRESHOLD,
};

use crate::code::Code;
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

// ---------------------------------------------------------------------------
// JitMacroExpander — int's cranelisp_types::MacroExpander implementation
// ---------------------------------------------------------------------------

/// int's implementation of [`cranelisp_types::MacroExpander`] — the
/// **execution** half of the macro two-jobs split.
///
/// Recognition (is this head a macro? which `FQSymbol`?) is done by the
/// orchestrator via `cranelisp_types::resolve_macro_head` over a committed
/// [`View`]; the orchestrator then calls [`MacroExpander::invoke`] with the
/// recognized macro's `fq`, the call's argument `Sexp`s, and the call span.
/// This impl:
///
/// 1. reads the macro's `clauses_meta` from `symbol_tables[fq.module][fq.symbol]`
///    (the `DefKind::Macro` entry),
/// 2. selects the matching clause by arity/bracket-shape,
/// 3. loads the matched clause's JIT'd code pointer from its GOT slot
///    (clause functions are normal per-module GOT fns named
///    `__macro_{name}_clause_{idx}`),
/// 4. marshals the args, invokes under signal protection, unmarshals the
///    result, and rewrites every node's span to a fresh synthetic span.
///
/// It holds only `cranelisp-types` collections (`&SymbolTables` is the
/// committed code+GOT store); `Send + Sync` is satisfied because the borrows
/// are shared-read and the invocation core isolates per-call signal state in
/// thread-locals.
pub(crate) struct JitMacroExpander<'a> {
    /// Committed per-module symbol tables — clause `clauses_meta` + GOT-stored
    /// clause code pointers are read from here.
    pub(crate) symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
}

impl MacroExpander for JitMacroExpander<'_> {
    fn invoke(
        &self,
        fq: &FQSymbol,
        args: &[Sexp],
        call_span: Span,
    ) -> Result<Sexp, MacroInvokeError> {
        // 1. Read the macro entry's clause metadata from its home module.
        let clauses_meta = self.macro_clauses(fq).ok_or_else(|| {
            MacroInvokeError::Aborted {
                fq: fq.clone(),
                message: format!(
                    "macro `{}/{}` has no compiled clauses in its home module \
                     (orchestrator-sequencing bug — clause not in memory)",
                    fq.module, fq.symbol
                ),
                span: call_span,
            }
        })?;

        // 2. Build compiled clause entries (clause-meta + GOT code ptr).
        let mut compiled: Vec<MacroClauseEntry> = Vec::with_capacity(clauses_meta.len());
        for (idx, meta) in clauses_meta.iter().enumerate() {
            let clause_name = Symbol::from(format!("__macro_{}_clause_{}", fq.symbol, idx));
            let func_ptr = self
                .clause_code_ptr(&fq.module, &clause_name)
                .ok_or_else(|| MacroInvokeError::Aborted {
                    fq: fq.clone(),
                    message: format!(
                        "macro `{}/{}` clause {} is not in memory \
                         (orchestrator-sequencing bug)",
                        fq.module, fq.symbol, idx
                    ),
                    span: call_span,
                })?;
            compiled.push(MacroClauseEntry {
                func_ptr,
                params: meta.params.clone(),
                rest_param: meta.rest_param.clone(),
            });
        }

        // 3. Select the matching clause by arity/bracket shape.
        let clause = find_matching_clause(&compiled, args).ok_or_else(|| {
            MacroInvokeError::Malformed {
                fq: fq.clone(),
                message: format!(
                    "no matching clause for macro `{}/{}` with {} argument(s)",
                    fq.module,
                    fq.symbol,
                    args.len()
                ),
                span: call_span,
            }
        })?;

        // 4. Marshal + signal-protected invoke + unmarshal + span-rewrite.
        execute_matched_clause(clause, args, call_span)
            .map_err(|e| macro_error_to_invoke_error(fq, call_span, e))
    }
}

/// The shared single-invocation core: marshal args, call the matched clause
/// under signal protection, unmarshal, and rewrite spans to fresh synthetic
/// ones. [`JitMacroExpander::invoke`] (the locked-decision boundary) executes
/// through this one function — there is no second executor; the legacy walk
/// also reaches it via `JitMacroExpander`.
pub(crate) fn execute_matched_clause(
    clause: &MacroClauseEntry,
    args: &[Sexp],
    span: Span,
) -> Result<Sexp, CranelispError> {
    let mut result = invoke_clause(clause, args, span)?;
    rewrite_spans(&mut result, span);
    Ok(result)
}

impl JitMacroExpander<'_> {
    /// Read the `clauses_meta` from the macro's home-module `DefKind::Macro`
    /// entry. The `fq` is expected to address the canonical entry directly
    /// (the orchestrator resolved it via `resolve_macro_head`, which
    /// chain-follows to the home module), so a single direct lookup suffices.
    fn macro_clauses(&self, fq: &FQSymbol) -> Option<Vec<cranelisp_types::MacroClauseInfo>> {
        let table = self.symbol_tables.get(&fq.module)?;
        match table.get(fq.symbol.as_ref())? {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::Macro { clauses_meta } => Some(clauses_meta.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Load a clause function's compiled code pointer from its per-module GOT
    /// slot. Returns `None` if the entry is absent or its GOT slot is empty.
    fn clause_code_ptr(&self, module: &ModuleFullPath, clause_name: &Symbol) -> Option<*const u8> {
        let table = self.symbol_tables.get(module)?;
        let ModuleEntry::Def { code: Some(_), got_slot: Some(slot), .. } =
            table.get(clause_name.as_ref())?
        else {
            return None;
        };
        let ptr = table.got.load_slot(*slot);
        if ptr.is_null() { None } else { Some(ptr) }
    }
}

/// Project the int-internal `CranelispError` an invocation can produce onto the
/// `cranelisp-types` boundary `MacroInvokeError`. A `MacroError` (the variant
/// `invoke_clause` raises for runtime traps / malformed results) maps to
/// `Aborted`; anything else is also surfaced as `Aborted` with its display.
fn macro_error_to_invoke_error(fq: &FQSymbol, span: Span, e: CranelispError) -> MacroInvokeError {
    let message = match &e {
        CranelispError::MacroError { message, .. } => message.clone(),
        other => other.to_string(),
    };
    MacroInvokeError::Aborted { fq: fq.clone(), message, span }
}

/// Construct a committed first-hop [`View`] over the live current-module table,
/// for the orchestrator's Pass-1 recognition call to
/// `cranelisp_types::resolve_macro_head`. Returns `None` when the current
/// module has no table yet (no macros are recognizable from an absent module).
///
/// This is the int-side glue for the locked recognition mechanism: the caller
/// passes the returned view to `resolve_macro_head` together with
/// `symbol_tables` + `module_aliases`. Kept here (next to the executor) so the
/// recognition + execution glue lives in one place.
pub(crate) fn committed_view<'a>(
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: &ModuleFullPath,
) -> Option<dashmap::mapref::one::Ref<'a, ModuleFullPath, crate::code::SessionSymbolTable>> {
    let _ = symbol_tables.get(current_module)?;
    symbol_tables.get(current_module)
}

/// The prelude module name — the implicit OUTER SCOPE consulted on a bare-name
/// inner-table miss when a module's `PreludeFallback` bit is ON (S78 §2).
const PRELUDE_MODULE: &str = "prelude";

/// Recognize a macro head from the committed tables, per the LOCKED decision
/// (`macro-availability-model.md` §0.7): a `cranelisp_types::resolve_macro_head`
/// query over a `View::single(live)` first-hop. Returns the macro's `FQSymbol`
/// when `name` resolves to a `DefKind::Macro` entry, `Ok(None)` for a non-macro
/// or forward (pre-`defmacro`) reference, `Err` only for hard resolution
/// failures (private, unknown qualified module).
///
/// **Prelude outer-scope fallback (S78 §2).** Since the prelude is no longer
/// flattened into each module's inner table, prelude-provided macros (`cond`,
/// `when`, `do`, `str`, `thread-first`, `case`, `vec`, …) are NOT in the current
/// module's table. When the first-hop recognition misses (`Ok(None)` — a bare
/// name unreachable from the current module) AND the module's
/// `prelude_fallback` bit is ON (and current ≠ `prelude`), recognition retries
/// `resolve_macro_head` against the `prelude` module's OWN view, rooted at
/// `prelude` (so prelude's `(export …)` re-exports chain-follow correctly).
///
/// **Public-only (the I-1 lesson).** Rooting the retry at `prelude` makes
/// `cranelisp_types`'s visibility check see `from_module = prelude`, and
/// `in_subtree(prelude, prelude)` is true — so a PRIVATE prelude macro would be
/// recognized. Reachability must instead be judged relative to the ORIGINAL
/// `current_module` (a user module is never in prelude's subtree), so the retry
/// hit is post-filtered on the canonical entry's `is_public()`: a private
/// prelude macro is treated as NOT a macro head (`Ok(None)`) and must not leak.
/// Only PUBLIC prelude macros (and the chain-follow through public re-exports)
/// reach a user module.
///
/// A FQ (`mod/macro`) reference never falls back — it names its module directly,
/// and `resolve_macro_head`'s qualified branch resolves it (or surfaces
/// `QualifiedModuleUnknown`, an `Err`, which short-circuits before any retry).
///
/// Mostly zero int→typecheck dependency: recognition is a `cranelisp-types`
/// query; the fallback bit is the session-side `PreludeFallback` companion map.
pub(crate) fn recognize_macro_head(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    current_module: &ModuleFullPath,
    name: &str,
    span: Span,
) -> Result<Option<FQSymbol>, CranelispError> {
    // A `:`-prefixed symbol is a TYPE ANNOTATION (`:Int`, `:primitives/Int`,
    // `:core.option/Option`), never a macro head. It must not be fed to
    // `resolve_macro_head`: that primitive splits a qualified name on `/` and
    // would treat `:primitives` as a module qualifier, surfacing a spurious
    // `QualifiedModuleUnknown` hard error (`module ':primitives' referenced by
    // ':primitives/Int' is not loaded`) that aborts the cluster before the
    // field type is ever resolved. The sibling `qualify_expanded_sexp` guards
    // this same case; mirror it here at the recognition seam (FIXME 0322).
    if name.starts_with(':') {
        return Ok(None);
    }
    let first = {
        let Some(table_ref) = committed_view(symbol_tables, current_module) else {
            return Ok(None);
        };
        let view: View<'_, Code, ()> = View::single(&table_ref);
        cranelisp_types::resolve_macro_head(
            symbol_tables,
            module_aliases,
            &view,
            current_module,
            name,
            span,
        )
        .map_err(CranelispError::from)?
    };
    if first.is_some() {
        return Ok(first);
    }

    // First-hop inner-table miss. Consult the prelude OUTER SCOPE iff the bit is
    // ON for this module (and the module is not prelude itself — a module never
    // falls back onto itself). Absence-is-OFF (§2.7.1).
    if current_module.as_ref() == PRELUDE_MODULE
        || !prelude_fallback.get(current_module).map(|b| *b).unwrap_or(false)
    {
        return Ok(None);
    }
    let prelude_module = ModuleFullPath::from(PRELUDE_MODULE);
    let Some(prelude_ref) = committed_view(symbol_tables, &prelude_module) else {
        return Ok(None);
    };
    let prelude_view: View<'_, Code, ()> = View::single(&prelude_ref);
    let prelude_hit = cranelisp_types::resolve_macro_head(
        symbol_tables,
        module_aliases,
        &prelude_view,
        // Root the retry at `prelude` so the chain-follow + terminal `home` are
        // correct. Visibility is re-judged below relative to the ORIGINAL user
        // module via the public-only filter (the I-1 lesson).
        &prelude_module,
        name,
        span,
    )
    .map_err(CranelispError::from)?;
    match prelude_hit {
        Some(fq) if prelude_macro_public(symbol_tables, &fq) => Ok(Some(fq)),
        // A private prelude macro is NOT reachable as a bare name from a user
        // module (the I-1 public-only discipline) — treat it as not-a-macro-head
        // so it does not leak and does not shadow.
        _ => Ok(None),
    }
}

/// Whether the canonical macro entry `fq` (resolved through the prelude retry)
/// is PUBLIC. A user module is never in the prelude subtree, so only public
/// prelude bindings are reachable through the implicit outer scope (S78 §2 /
/// `/review` I-1). A missing entry is treated as not-public (not reachable).
fn prelude_macro_public(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    fq: &FQSymbol,
) -> bool {
    symbol_tables
        .get(&fq.module)
        .and_then(|table| table.get(fq.symbol.as_ref()).map(|e| e.is_public()))
        .unwrap_or(false)
}

// ---------------------------------------------------------------------------
// MacroResolver trait
// ---------------------------------------------------------------------------

/// Recognition driver for the legacy in-place expansion walk
/// (`expand_sexp_recursive`).
///
/// **Recognition** uses the LOCKED types primitive
/// (`cranelisp_types::resolve_macro_head`, `macro-availability-model.md` §0.7)
/// — each impl's `recognize` is a thin caller of `recognize_macro_head`. The
/// `&mut self` receiver lets an impl additionally **ensure the clause code is
/// in memory** as a side effect of recognition (the worker's
/// `SymbolTableMacroResolver` compiles macro clauses the first time they are
/// referenced; the read-only `/expand` resolver does not).
///
/// **Execution** is uniform: once `recognize` returns the macro's `FQSymbol`,
/// the walk executes through the single [`JitMacroExpander`] (the locked
/// `cranelisp_types::MacroExpander` boundary impl) — there is no per-resolver
/// executor. `expander()` hands the walk the `&SymbolTables` to build it over.
pub(crate) trait MacroResolver {
    /// Recognize `name` as a macro head; return its `FQSymbol` if so.
    ///
    /// Returns:
    /// - `Ok(Some(fq))` — `name` is a macro; its clauses are (or have just been
    ///   made) in memory, addressable by `fq`.
    /// - `Ok(None)` — not a macro, or a forward / not-yet-visible reference.
    /// - `Err(...)` — hard resolution failure or on-demand compilation failure.
    fn recognize(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<FQSymbol>, CranelispError>;

    /// The committed symbol tables to execute recognized macros over.
    fn symbol_tables(
        &self,
    ) -> &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>;
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
            let _ = cranelisp_intrinsics::panic::take_runtime_error();
            let result_i64 = func(args_slist);

            // Restore original signal handlers.
            restore_signal_handlers(old_handlers);

            Ok(result_i64)
        }
    }));

    // Check thread-local error flag (set by runtime_panic in JIT code).
    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
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
    ///
    /// On glibc/musl `sigsetjmp` is a header macro, not a linkable symbol — the
    /// real function is `__sigsetjmp(env, savemask)` (same signature). macOS
    /// exports a real `sigsetjmp`, so the redirect is Linux-only.
    #[cfg_attr(target_os = "linux", link_name = "__sigsetjmp")]
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
                && let Some(fq) = resolver.recognize(name, sym_span)? {
                    let args = &children[1..];
                    return expand_recognized_macro(fq, args, span, resolver, depth);
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
            if let Some(fq) = resolver.recognize(name, span)? {
                return expand_recognized_macro(fq, &[], span, resolver, depth);
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

/// Execute one recognized macro call through the [`JitMacroExpander`]
/// (`cranelisp_types::MacroExpander`) boundary, then re-expand the result to
/// fixpoint. The walk recognized `fq` via the LOCKED types primitive and the
/// resolver ensured its clause code is in memory; execution is uniform.
fn expand_recognized_macro(
    fq: FQSymbol,
    args: &[Sexp],
    span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    let result = {
        let expander = JitMacroExpander { symbol_tables: resolver.symbol_tables() };
        expander
            .invoke(&fq, args, span)
            .map_err(|e| CranelispError::MacroError {
                message: e.to_string(),
                location: ErrorLocation::from_span(span),
            })?
    };
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
    use cranelisp_types::{DefKind, MacroClauseInfo, ModuleAliases, Scheme, Type, Visibility};
    use std::collections::HashMap;

    fn empty_scheme() -> Scheme {
        Scheme { type_vars: vec![], constraints: HashMap::new(), ty: Type::Int }
    }

    /// Build a one-module symbol table set with `name` registered as a macro
    /// (a `DefKind::Macro` entry with `clause_count` clauses).
    fn tables_with_macro(
        module: &str,
        name: &str,
        clause_count: usize,
    ) -> dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
        let path = ModuleFullPath::from(module);
        let tables = dashmap::DashMap::new();
        let mut st = crate::code::SessionSymbolTable::new_with_params(path.clone());
        let clauses_meta: Vec<MacroClauseInfo> = (0..clause_count)
            .map(|_| MacroClauseInfo { params: vec![], rest_param: None })
            .collect();
        let entry = ModuleEntry::def(empty_scheme(), DefKind::Macro { clauses_meta })
            .visibility(Visibility::Public)
            .build();
        st.insert(Symbol::from(name), entry);
        tables.insert(path, st);
        tables
    }

    // spec: macro-availability-model.md §0.7 — recognition is the types primitive
    // (`resolve_macro_head` over a committed View::single(live)).
    #[test]
    fn recognize_macro_head_finds_local_macro() {
        let tables = tables_with_macro("user", "twice", 1);
        let aliases = ModuleAliases::default();
        let pf = cranelisp_typecheck::PreludeFallback::default();
        let module = ModuleFullPath::from("user");
        let fq = recognize_macro_head(&tables, &aliases, &pf, &module, "twice", Span::SYNTHETIC)
            .expect("no hard error")
            .expect("twice is a macro head");
        assert_eq!(fq.symbol, Symbol::from("twice"));
        assert_eq!(fq.module, ModuleFullPath::from("user"));
    }

    // spec: macro-availability-model.md §0.2 — a forward (pre-defmacro) reference
    // is NOT a macro head: Ok(None), flows on as an ordinary reference.
    #[test]
    fn recognize_macro_head_forward_reference_is_none() {
        let tables = tables_with_macro("user", "twice", 1);
        let aliases = ModuleAliases::default();
        let pf = cranelisp_typecheck::PreludeFallback::default();
        let module = ModuleFullPath::from("user");
        let r = recognize_macro_head(&tables, &aliases, &pf, &module, "not-yet-defined", Span::SYNTHETIC)
            .expect("no hard error");
        assert!(r.is_none(), "an undefined name is not a macro head");
    }

    // spec: macro-availability-model.md §0.7 — recognition over an absent
    // current module yields Ok(None) (no macros recognizable from nothing).
    #[test]
    fn recognize_macro_head_absent_module_is_none() {
        let tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let aliases = ModuleAliases::default();
        let pf = cranelisp_typecheck::PreludeFallback::default();
        let module = ModuleFullPath::from("ghost");
        let r = recognize_macro_head(&tables, &aliases, &pf, &module, "anything", Span::SYNTHETIC)
            .expect("no hard error");
        assert!(r.is_none());
    }

    // spec: macro-expansion-ownership.md §2.3 — JitMacroExpander surfaces a clear
    // Aborted diagnostic when a recognized macro's clause code is not in memory
    // (an orchestrator-sequencing condition), rather than misbehaving silently.
    #[test]
    fn jit_macro_expander_absent_clause_code_is_clear_abort() {
        // The macro entry exists (recognition succeeds) but its clause function
        // was never JIT-compiled, so its GOT slot is empty.
        let tables = tables_with_macro("user", "twice", 1);
        let expander = JitMacroExpander { symbol_tables: &tables };
        let fq = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("twice"),
        };
        let err = expander
            .invoke(&fq, &[Sexp::Int(1, Span::SYNTHETIC)], Span::SYNTHETIC)
            .expect_err("clause code is absent");
        match err {
            MacroInvokeError::Aborted { message, .. } => {
                assert!(
                    message.contains("not in memory"),
                    "diagnostic names the in-memory condition: {message}"
                );
            }
            other => panic!("expected Aborted, got {other:?}"),
        }
    }

    // spec: macro-availability-model.md §0.7 — a name resolving to a non-macro
    // entry is not a macro head (the head flows on as an ordinary call).
    #[test]
    fn recognize_non_macro_entry_is_none() {
        let path = ModuleFullPath::from("user");
        let tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let mut st = crate::code::SessionSymbolTable::new_with_params(path.clone());
        let entry = ModuleEntry::def(
            empty_scheme(),
            DefKind::UserFn { constrained_fn: None },
        )
        .visibility(Visibility::Public)
        .build();
        st.insert(Symbol::from("plain-fn"), entry);
        tables.insert(path, st);
        let aliases = ModuleAliases::default();
        let pf = cranelisp_typecheck::PreludeFallback::default();
        let module = ModuleFullPath::from("user");
        let r = recognize_macro_head(&tables, &aliases, &pf, &module, "plain-fn", Span::SYNTHETIC)
            .expect("no hard error");
        assert!(r.is_none(), "a regular fn is not a macro head");
    }

    /// Build a one-module symbol table set with `name` registered as a macro
    /// with the given `visibility` (for prelude-fallback public-only tests).
    fn tables_with_macro_vis(
        module: &str,
        name: &str,
        visibility: cranelisp_types::Visibility,
    ) -> dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
        use cranelisp_types::MacroClauseInfo;
        let path = ModuleFullPath::from(module);
        let tables = dashmap::DashMap::new();
        let mut st = crate::code::SessionSymbolTable::new_with_params(path.clone());
        let clauses_meta = vec![MacroClauseInfo { params: vec![], rest_param: None }];
        let entry = ModuleEntry::def(empty_scheme(), DefKind::Macro { clauses_meta })
            .visibility(visibility)
            .build();
        st.insert(Symbol::from(name), entry);
        tables.insert(path, st);
        tables
    }

    // spec: design/int/s78-entry-module.md §2 — a PUBLIC prelude-provided macro
    // is recognized from a user module via the implicit outer scope when the
    // module's prelude_fallback bit is ON (the §2 regression fix).
    #[test]
    fn recognize_macro_head_falls_back_to_public_prelude_macro() {
        let tables = tables_with_macro_vis("prelude", "when", cranelisp_types::Visibility::Public);
        // The user module exists but has no `when` in its inner table.
        let user = ModuleFullPath::from("user");
        tables.insert(user.clone(), crate::code::SessionSymbolTable::new_with_params(user.clone()));
        let aliases = ModuleAliases::default();
        let pf = cranelisp_typecheck::PreludeFallback::default();
        pf.insert(user.clone(), true);
        let fq = recognize_macro_head(&tables, &aliases, &pf, &user, "when", Span::SYNTHETIC)
            .expect("no hard error")
            .expect("public prelude macro is recognized via the outer scope");
        assert_eq!(fq.symbol, Symbol::from("when"));
        assert_eq!(fq.module, ModuleFullPath::from("prelude"));
    }

    // spec: design/int/s78-entry-module.md §2 / /review I-1 — a PRIVATE prelude
    // macro must NOT be recognized from a user module through the implicit outer
    // scope (public-only). It is treated as not-a-macro-head and does not leak.
    #[test]
    fn recognize_macro_head_does_not_leak_private_prelude_macro() {
        let tables = tables_with_macro_vis("prelude", "secret", cranelisp_types::Visibility::Private);
        let user = ModuleFullPath::from("user");
        tables.insert(user.clone(), crate::code::SessionSymbolTable::new_with_params(user.clone()));
        let aliases = ModuleAliases::default();
        let pf = cranelisp_typecheck::PreludeFallback::default();
        pf.insert(user.clone(), true);
        let r = recognize_macro_head(&tables, &aliases, &pf, &user, "secret", Span::SYNTHETIC)
            .expect("no hard error");
        assert!(r.is_none(), "a private prelude macro must not leak to a user module");
    }

    // spec: design/int/s78-entry-module.md §2.7.1 — absence-is-OFF: with the bit
    // OFF for the module, NO prelude fallback fires (the name stays unbound).
    #[test]
    fn recognize_macro_head_no_fallback_when_bit_off() {
        let tables = tables_with_macro_vis("prelude", "when", cranelisp_types::Visibility::Public);
        let user = ModuleFullPath::from("user");
        tables.insert(user.clone(), crate::code::SessionSymbolTable::new_with_params(user.clone()));
        let aliases = ModuleAliases::default();
        // Bit absent ⇒ OFF.
        let pf = cranelisp_typecheck::PreludeFallback::default();
        let r = recognize_macro_head(&tables, &aliases, &pf, &user, "when", Span::SYNTHETIC)
            .expect("no hard error");
        assert!(r.is_none(), "no fallback when the prelude_fallback bit is OFF");
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
