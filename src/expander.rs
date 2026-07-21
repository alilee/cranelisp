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
    ModuleAliases, ModuleEntry, ModuleFullPath, ResolutionScope, Sexp, Span, Symbol, View,
    DefKind, NULLARY_TAG_THRESHOLD,
};

use std::collections::HashSet;

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

        // 3. Select the matching clause by arity/bracket shape. On no match,
        //    surface the user-call span (threaded down as `call_span` — the
        //    ORIGINAL top-level invocation, not a synthetic recursive-expansion
        //    offset; FIXME 0485) plus the clause set's accepted arities.
        let clause = find_matching_clause(&compiled, args)
            .ok_or_else(|| no_matching_clause_error(fq, &compiled, args, call_span))?;

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

/// Build the `no matching clause` diagnostic for a multi-clause macro whose
/// arguments matched no clause, anchored at the user-call span (`call_span`)
/// with the clause set's accepted arities surfaced (FIXME 0485).
///
/// `call_span` is the span threaded down the expansion recursion — the ORIGINAL
/// top-level user call, not the synthetic recursive-expansion offset, so the
/// inner [`MacroInvokeError`] `Display` renders a real source position. The
/// arity hint is derived from the actual [`MacroClauseEntry`] shapes (see
/// [`describe_clause_arities`]), so it is correct for ANY multi-clause macro,
/// not just `cond`.
fn no_matching_clause_error(
    fq: &FQSymbol,
    clauses: &[MacroClauseEntry],
    args: &[Sexp],
    call_span: Span,
) -> MacroInvokeError {
    MacroInvokeError::Malformed {
        fq: fq.clone(),
        message: format!(
            "no matching clause for macro `{}/{}` with {} argument(s); \
             clauses accept {} argument(s)",
            fq.module,
            fq.symbol,
            args.len(),
            describe_clause_arities(clauses),
        ),
        span: call_span,
    }
}

/// Describe the argument arities a macro's clause set accepts, derived from the
/// actual [`MacroClauseEntry`] shapes: each clause's fixed parameter count, with
/// a trailing `+` when a `rest_param` makes the clause variadic ("N or more").
/// Duplicate arities are collapsed and the distinct descriptions joined for
/// display (e.g. `"1 or 2+"`, `"0, 1 or 3+"`, `"2"`).
///
/// General over any multi-clause macro — nothing here is `cond`-specific.
fn describe_clause_arities(clauses: &[MacroClauseEntry]) -> String {
    let mut descs: Vec<String> = Vec::new();
    for c in clauses {
        let n = c.params.len();
        let desc = if c.rest_param.is_some() {
            format!("{n}+")
        } else {
            format!("{n}")
        };
        if !descs.contains(&desc) {
            descs.push(desc);
        }
    }
    match descs.len() {
        0 => "no".to_string(),
        1 => descs.pop().unwrap_or_default(),
        _ => {
            let last = descs.pop().unwrap_or_default();
            format!("{} or {}", descs.join(", "), last)
        }
    }
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
                DefKind::Macro { clauses_meta, .. } => Some(clauses_meta.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Load a clause function's compiled code pointer from its per-module GOT
    /// slot. Returns `None` if the entry is absent or its GOT slot is empty.
    fn clause_code_ptr(&self, module: &ModuleFullPath, clause_name: &Symbol) -> Option<*const u8> {
        let table = self.symbol_tables.get(module)?;
        let entry = table.get(clause_name.as_ref())?;
        let ModuleEntry::Def { code: Some(_), .. } = entry else {
            return None;
        };
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        let slot = entry.callable_got_slot()?;
        let ptr = table.got.load_slot(slot);
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
    // S108 Wave-G CS2: the resolve → prelude-fallback → public-only-filter →
    // macro-head projection all live intrinsic to `ResolutionScope` (the fallback
    // is decided ONCE at scope construction, never re-decided per call).  int's
    // job is only (1) build the committed first-hop view, (2) derive the scope's
    // `prelude: Option` from the session-side `prelude_fallback` bit, and (3) call
    // the scope's `resolve_macro_head` projection.  The former hand-rolled
    // free-fn fallback call + kind-discriminator match are gone (the projection IS
    // `ResolutionScope::resolve_macro_head`).
    let Some(table_ref) = committed_view(symbol_tables, current_module) else {
        return Ok(None);
    };
    let view: View<'_, Code, ()> = View::single(&table_ref);

    // Fallback ON iff the module's bit is set and it is not prelude itself
    // (absence-is-OFF, §2.7.1; never self-fallback — `ResolutionScope::new` also
    // collapses a self-fallback defensively). When OFF, the scope reduces to a
    // bare first-hop resolve.
    let prelude_module = ModuleFullPath::from(PRELUDE_MODULE);
    let prelude = if current_module.as_ref() != PRELUDE_MODULE
        && prelude_fallback.get(current_module).map(|b| *b).unwrap_or(false)
    {
        Some(&prelude_module)
    } else {
        None
    };

    // The I-1 public-only filter on the prelude terminal and the not-found-class
    // → `Ok(None)` collapse are both intrinsic to `resolve_macro_head`; only a
    // hard failure (private, unknown qualified module) surfaces as `Err`.
    let scope = ResolutionScope::new(symbol_tables, module_aliases, &view, current_module, prelude);
    scope.resolve_macro_head(name, span).map_err(CranelispError::from)
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
    // Marshal each argument to a runtime Sexp ADT value. Deep protection is now
    // applied at every allocation site inside the marshaller (`protect_marshalled_cell`,
    // FIXME 0638): every marshalled cell — top-level, interior, SList spine, and
    // HeapString — is born at RC ≥ 2, accounting the reference the marshaller
    // retains. The former bespoke top-level-only protect loop here is REMOVED (it
    // covered only the top of each arg, leaving interiors at RC = 1 → the
    // interior-alias double-free); the marshaller now owns the protection,
    // co-located with the allocation whose retention it accounts for.
    let marshalled: Vec<i64> = args.iter().map(marshal::sexp_to_runtime).collect();

    // Package all args as an (SList Sexp). The spine SCons cells are protected on
    // build too (`alloc_scons`), so the whole args tree is uniformly RC ≥ 2.
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
///
/// `origin_span` carries the ORIGINAL user-call span down the recursion so a
/// diagnostic raised while expanding a macro's OWN output (a recursive macro
/// like `cond`, whose expansion re-invokes itself with synthetic
/// expansion-buffer spans) is anchored at the source position the user typed,
/// not the internal offset (FIXME 0485). At the top-level entry it is `None`,
/// and each recognized invocation uses the form's real span; once inside an
/// expansion result it is `Some(user_span)` and every nested invocation
/// inherits it.
pub(crate) fn expand_sexp_recursive(
    sexp: Sexp,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
) -> Result<Sexp, CranelispError> {
    // Public entry: no lexical scope yet, so no shadowed names.
    expand_scoped(sexp, resolver, depth, origin_span, &HashSet::new())
}

/// The reader-quote head the [`expand_scoped`] shield recognizes at the top of a
/// non-empty list arm (`design/int/quote-shield.md` §3).
pub(crate) enum QuoteHead {
    /// `(quote X)` — fully verbatim, no descent (Rule Q).
    Quote,
    /// `(quasiquote T)` — descend only into live unquotes, tracking depth (Rule QQ).
    Quasiquote,
    /// `(unquote X)` / `(unquote-splicing X)` — an escape back to expression
    /// position; live or nested according to the walker's `qq_depth`.
    Unquote,
}

/// Structural recognition of the reader-quote family — bare-symbol head +
/// `len() == 2`, consulting neither `shadows` nor any resolver (the SAME test
/// the frontend fold applies in `quasiquote.rs::is_quote`/`is_quasiquote`).
///
/// **Single source for BOTH int-side scope-aware walks** (Principle 7): the
/// expander shield here (`expand_scoped` / [`shield_qq`]) and the qualify shield
/// in `process_form::macro_resolution::qualify_scoped` (S115, FIXME 0718 /
/// `expansion-qualification-scope.md` §2.4). If the two tests ever diverge a
/// subtree gets double-desugared or mis-qualified — so neither walk may keep a
/// private copy. (The frontend fold's own predicates are crate-private in
/// `cranelisp-frontend`; collapsing all three onto one exported predicate is
/// FIXME 0789, `target: /arch`.)
pub(crate) fn quote_head(children: &[Sexp]) -> Option<QuoteHead> {
    if children.len() != 2 {
        return None;
    }
    match &children[0] {
        Sexp::Symbol(h, _) if h == "quote" => Some(QuoteHead::Quote),
        Sexp::Symbol(h, _) if h == "quasiquote" => Some(QuoteHead::Quasiquote),
        Sexp::Symbol(h, _) if h == "unquote" || h == "unquote-splicing" => {
            Some(QuoteHead::Unquote)
        }
        _ => None,
    }
}

/// Is `head` a `defmacro`/`defmacro-` head? The CS-D1 shield's structural test,
/// shared with the qualify walk's §2.6 shield (FIXME 0718) so the two stay in
/// lockstep. Deliberately NOT folded into [`is_binding_form`]: that predicate
/// gates `expand_binding_form`/`qualify_binding_form`, whose arms do not cover
/// `defmacro`, and the expander's shield over it is narrower (head + name).
pub(crate) fn is_defmacro_head(head: &str) -> bool {
    matches!(head, "defmacro" | "defmacro-")
}

/// The quasiquote template walker (Rule QQ, `design/int/quote-shield.md` §4).
///
/// Holds every node of a `quasiquote` template verbatim EXCEPT the body of a
/// **live** `unquote`/`unquote-splicing` (one at the matching nesting depth),
/// which is an ordinary expression position handed back to [`expand_scoped`] for
/// normal macro expansion (§9.4.2). `qq_depth` mirrors the frontend
/// `expand_qq_template`/`expand_qq_list` depth math EXACTLY (`quasiquote.rs`):
/// the body is walked at `qq_depth = 0`; `unquote`/`unquote-splicing` are live at
/// depth 0; a nested `(quasiquote …)` increments the depth; an `(unquote …)`/
/// `(unquote-splicing …)` under a nested quasiquote decrements it. Keeping shield
/// and fold byte-identical on which unquotes are live is the durable coupling
/// (§5). The reader-quote family is recognized STRUCTURALLY (bare-symbol head +
/// `len() == 2`), consulting neither `shadows` nor the resolver.
///
/// `depth` (the macro expansion-limit counter) is threaded untouched into the
/// `expand_scoped` re-entry so the depth guard still fires for macros inside a
/// live unquote — it is distinct from `qq_depth` (§4 note).
#[allow(clippy::too_many_arguments)]
fn shield_qq(
    node: Sexp,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
    qq_depth: usize,
) -> Result<Sexp, CranelispError> {
    match node {
        Sexp::List(children, span) if !children.is_empty() => {
            {
                // unquote / unquote-splicing share ONE arm — the shield never
                // errors on `~@` at qq_depth 0 (that is the fold's diagnostic);
                // it expands the body and hands the tree on (§4 note).
                // Recognition via the shared `quote_head` classifier (P7).
                match quote_head(&children) {
                    // unquote / unquote-splicing.
                    Some(QuoteHead::Unquote) => {
                        let mut children = children;
                        let body = children.pop().expect("len == 2: unquote body");
                        let head_sym = children.pop().expect("len == 2: unquote head");
                        let inner = if qq_depth == 0 {
                            // LIVE unquote — ordinary expression position: expand.
                            expand_scoped(body, resolver, depth, origin_span, shadows)?
                        } else {
                            // Nested: decrement, stay shielded.
                            shield_qq(body, resolver, depth, origin_span, shadows, qq_depth - 1)?
                        };
                        return Ok(Sexp::List(vec![head_sym, inner], span));
                    }
                    // Nested quasiquote — increment depth, stay shielded.
                    Some(QuoteHead::Quasiquote) => {
                        let mut children = children;
                        let body = children.pop().expect("len == 2: quasiquote body");
                        let head_sym = children.pop().expect("len == 2: quasiquote head");
                        let inner =
                            shield_qq(body, resolver, depth, origin_span, shadows, qq_depth + 1)?;
                        return Ok(Sexp::List(vec![head_sym, inner], span));
                    }
                    // A nested `(quote …)` is NOT short-circuited here (§5.1) —
                    // it falls through to structural recursion at the same depth
                    // so inner live unquotes are still found.
                    Some(QuoteHead::Quote) | None => {}
                }
            }
            // Ordinary list under quasiquote (INCLUDING a nested `(quote …)`, §5.1
            // — do NOT short-circuit quote here): recurse structurally at the SAME
            // depth so inner live unquotes are still found.
            let mapped: Vec<Sexp> = children
                .into_iter()
                .map(|c| shield_qq(c, resolver, depth, origin_span, shadows, qq_depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(mapped, span))
        }
        Sexp::Bracket(children, span) => {
            // Brackets can't head an unquote but CAN contain live unquotes (`[~x]`).
            let mapped: Vec<Sexp> = children
                .into_iter()
                .map(|c| shield_qq(c, resolver, depth, origin_span, shadows, qq_depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(mapped, span))
        }
        // Atoms, the empty list, and comments are held verbatim.
        other => Ok(other),
    }
}

/// The scope-aware expansion core.
///
/// `shadows` is the set of names lexically bound by an enclosing `let` / `fn` /
/// `defn` / `match` scope. Per §8.6.3 a local binding shadows a module-scope
/// name of the same spelling, so a bound name must NOT be macro-expanded — not
/// in its BINDER position (else a zero-arg `def`-macro binder `g` rewrites to
/// `(g-def)` and fails `ast_builder::expect_symbol`) and not in a READ within
/// the scope (else `g` in the body resolves to the top-level macro instead of
/// the local). A name that is NOT lexically bound still expands normally — a
/// free `g` read genuinely refers to the module-scope macro (do not over-shield).
fn expand_scoped(
    sexp: Sexp,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
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
        Sexp::List(children, span) if !children.is_empty() => {
            // 0. SHIELD (reader-quote family) — hold quoted DATA out of Pass-1
            //    macro expansion, so a macro-call-shaped list living inside quoted
            //    data reaches `build_form` intact and is desugared by the frontend
            //    fold (never macro-expanded first). Matched STRUCTURALLY — bare
            //    `quote`/`quasiquote` head + `len() == 2`, the SAME test the fold
            //    uses (`quasiquote.rs::is_quote`/`is_quasiquote`); the shield
            //    consults neither `shadows` nor the resolver, keeping the two in
            //    lockstep (`design/int/quote-shield.md` §§2–5). Placed FIRST: a
            //    reader-quote head is handled by the shield and nothing else.
            {
                match quote_head(&children) {
                    // Rule Q — quoted data is pure structural quotation; never
                    // expanded, no descent (mirrors `expand_quote_template`).
                    Some(QuoteHead::Quote) => return Ok(Sexp::List(children, span)),
                    // Rule QQ — the body is walked at qq_depth 0; only the body of
                    // a LIVE unquote/unquote-splicing is re-entered for expansion.
                    Some(QuoteHead::Quasiquote) => {
                        let mut children = children;
                        let body = children.pop().expect("len == 2: quasiquote body");
                        let head_sym = children.pop().expect("len == 2: quasiquote head");
                        let inner =
                            shield_qq(body, resolver, depth, origin_span, shadows, 0)?;
                        return Ok(Sexp::List(vec![head_sym, inner], span));
                    }
                    // A bare `(unquote X)` outside any quasiquote is not shielded
                    // here — it stays an ordinary list (the fold diagnoses it).
                    Some(QuoteHead::Unquote) | None => {}
                }
            }
            // 1. Binding special forms establish a lexical scope (§8.6.3). Handle
            //    them BEFORE macro-head recognition so binder positions are held
            //    verbatim and body reads of a bound name resolve to the local.
            if let Sexp::Symbol(head, _) = &children[0]
                && is_binding_form(head)
            {
                let head = head.clone();
                return expand_binding_form(
                    &head, &children, span, resolver, depth, origin_span, shadows,
                );
            }
            // 2. Check if head is a macro name — unless it is lexically shadowed.
            if let Sexp::Symbol(name, sym_span) = &children[0] {
                let sym_span = *sym_span;
                if !shadows.contains(name.as_str())
                    && let Some(fq) = resolver.recognize(name, sym_span)?
                {
                    let args = &children[1..];
                    // Anchor errors at the original user call when we are inside
                    // an expansion; otherwise this form IS the user call.
                    let call_span = origin_span.unwrap_or(span);
                    return expand_recognized_macro(
                        fq, args, call_span, resolver, depth, shadows,
                    );
                }
            }
            // 3. Not a macro call — recurse into children.
            //
            // `(defmacro name …)` shield (S102 CS-D1): the NAME position of a
            // `defmacro` form is a binder, never an expression — expanding it
            // would rewrite a zero-arg macro's own (re)definition name into its
            // expansion (`(defmacro x …)` → `(defmacro (x-def) …)`), which then
            // fails `parse_defmacro` with "defmacro name must be a symbol".
            // The shape arises whenever a macro-defining macro's expansion
            // output redefines a name that is ALREADY a registered macro
            // (poisoned-regen co-load, or a cache-preloaded table during the
            // restart recompile). Hold the head + name verbatim; the clauses
            // are recursed normally.
            let is_defmacro_form = matches!(
                children.first(),
                Some(Sexp::Symbol(head, _)) if is_defmacro_head(head)
            );
            let hold_verbatim = if is_defmacro_form { 2 } else { 0 };
            let expanded: Vec<Sexp> = children
                .into_iter()
                .enumerate()
                .map(|(i, c)| {
                    if i < hold_verbatim {
                        Ok(c)
                    } else {
                        expand_scoped(c, resolver, depth, origin_span, shadows)
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(expanded, span))
        }
        Sexp::Symbol(ref name, span) => {
            // Bare symbol: check for zero-arg macro — unless lexically shadowed
            // (a `let`/`fn`/`match`-bound local of the same name, §8.6.3).
            if !shadows.contains(name.as_str())
                && let Some(fq) = resolver.recognize(name, span)?
            {
                let call_span = origin_span.unwrap_or(span);
                return expand_recognized_macro(fq, &[], call_span, resolver, depth, shadows);
            }
            Ok(sexp)
        }
        Sexp::Bracket(children, span) => {
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_scoped(c, resolver, depth, origin_span, shadows))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(expanded, span))
        }
        _ => Ok(sexp),
    }
}

/// Is `head` a binding special form whose binder positions establish a lexical
/// scope the expander must shield (§8.6.3)? `defmacro`/`defmacro-` are excluded
/// — their NAME position keeps the narrower CS-D1 verbatim shield above.
///
/// **Shared binder-slot enumeration (FIXME 0670).** This predicate and its
/// siblings (`is_annotation_symbol`/`starts_uppercase`/`params_scope`/
/// `pattern_binders`) are the ONE value-level binder-slot enumeration, consumed
/// by BOTH scope-aware walks over expansion output: `expand_scoped` (this file)
/// and `qualify_expanded_sexp` (`process_form/macro_resolution.rs`). A second
/// private copy in the qualify pass would be the P7 mirror the 0670 fix removes
/// — a future binder-form addition must update this one enumeration and both
/// walks stay in lockstep (`expansion-qualification-scope.md` §2.3).
pub(crate) fn is_binding_form(head: &str) -> bool {
    matches!(head, "let" | "fn" | "lambda" | "defn" | "defn-" | "match")
}

/// Is `s` a `:Type`/`:Trait` annotation symbol (reader-macro-like, binds the
/// following form)? Such symbols are held verbatim in binder brackets.
pub(crate) fn is_annotation_symbol(s: &Sexp) -> bool {
    matches!(s, Sexp::Symbol(n, _) if n.starts_with(':'))
}

/// Does `s` begin with an uppercase letter (a constructor name, not a binder)?
pub(crate) fn starts_uppercase(s: &str) -> bool {
    s.chars().next().is_some_and(|c| c.is_uppercase())
}

/// Generic child recursion used as the defensive fall-back when a binding form
/// does not match its expected shape (the AST builder reports the arity error).
fn expand_children_clone(
    children: &[Sexp],
    span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    let expanded: Vec<Sexp> = children
        .iter()
        .map(|c| expand_scoped(c.clone(), resolver, depth, origin_span, shadows))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Sexp::List(expanded, span))
}

/// The binder names introduced by a param bracket `[:Int x y]` — every bare
/// (non-annotation) symbol. Returns `shadows ∪ params`. Shared with the qualify
/// pass (FIXME 0670; see `is_binding_form`).
pub(crate) fn params_scope(param_items: &[Sexp], shadows: &HashSet<String>) -> HashSet<String> {
    let mut scope = shadows.clone();
    for item in param_items {
        if let Sexp::Symbol(n, _) = item
            && !n.starts_with(':')
        {
            scope.insert(n.clone());
        }
    }
    scope
}

/// The variable binders a match pattern introduces: a bare lowercase symbol
/// (`g`), or the non-head symbols of a constructor pattern (`(Box g)` → `g`).
/// A wildcard `_`, a nullary constructor (uppercase), and the constructor head
/// itself bind nothing. Shared with the qualify pass (FIXME 0670; see
/// `is_binding_form`).
pub(crate) fn pattern_binders(pattern: &Sexp) -> Vec<String> {
    match pattern {
        Sexp::Symbol(n, _) => {
            if n == "_" || starts_uppercase(n) {
                vec![]
            } else {
                vec![n.clone()]
            }
        }
        Sexp::List(items, _) => items
            .iter()
            .skip(1)
            .filter_map(|s| match s {
                Sexp::Symbol(n, _) if n != "_" => Some(n.clone()),
                _ => None,
            })
            .collect(),
        _ => vec![],
    }
}

/// Dispatch a binding special form to its scope-aware expander.
fn expand_binding_form(
    head: &str,
    children: &[Sexp],
    span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    match head {
        "let" => expand_let(children, span, resolver, depth, origin_span, shadows),
        "fn" | "lambda" => expand_fn(children, span, resolver, depth, origin_span, shadows),
        "defn" | "defn-" => expand_defn(children, span, resolver, depth, origin_span, shadows),
        "match" => expand_match(children, span, resolver, depth, origin_span, shadows),
        _ => unreachable!("invariant: is_binding_form gates expand_binding_form"),
    }
}

/// `(let [name val …] body)` — each binding NAME is a binder held verbatim
/// (never macro-expanded), each VALUE is expanded in the scope accumulated so
/// far (sequential `let*` semantics), and the body is expanded with every bound
/// name shadowing the module scope (§8.6.3).
fn expand_let(
    children: &[Sexp],
    span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    if children.len() != 3 {
        return expand_children_clone(children, span, resolver, depth, origin_span, shadows);
    }
    let Sexp::Bracket(bind_items, bracket_span) = &children[1] else {
        return expand_children_clone(children, span, resolver, depth, origin_span, shadows);
    };
    let mut scope = shadows.clone();
    let mut new_items: Vec<Sexp> = Vec::with_capacity(bind_items.len());
    let mut i = 0;
    while i < bind_items.len() {
        // Binding NAME — a fresh local binder; held verbatim, never expanded.
        let binder = match &bind_items[i] {
            Sexp::Symbol(n, _) => Some(n.clone()),
            _ => None,
        };
        new_items.push(bind_items[i].clone());
        i += 1;
        // Optional `:Type` annotations on the value are held verbatim.
        while i < bind_items.len() && is_annotation_symbol(&bind_items[i]) {
            new_items.push(bind_items[i].clone());
            i += 1;
        }
        // The value expression is expanded in the scope so far (the binder is
        // NOT yet in scope for its own RHS — sequential `let`).
        if i < bind_items.len() {
            let v = expand_scoped(bind_items[i].clone(), resolver, depth, origin_span, &scope)?;
            new_items.push(v);
            i += 1;
        }
        // The binder now shadows subsequent bindings and the body.
        if let Some(b) = binder {
            scope.insert(b);
        }
    }
    let body = expand_scoped(children[2].clone(), resolver, depth, origin_span, &scope)?;
    Ok(Sexp::List(
        vec![children[0].clone(), Sexp::Bracket(new_items, *bracket_span), body],
        span,
    ))
}

/// `(fn [params] body)` / `(lambda [params] body)` — the param bracket is held
/// verbatim (binder names, never expanded) and the body is expanded with the
/// params shadowing the module scope (§8.6.3).
fn expand_fn(
    children: &[Sexp],
    span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    if children.len() != 3 {
        return expand_children_clone(children, span, resolver, depth, origin_span, shadows);
    }
    let Sexp::Bracket(param_items, _) = &children[1] else {
        return expand_children_clone(children, span, resolver, depth, origin_span, shadows);
    };
    let scope = params_scope(param_items, shadows);
    let body = expand_scoped(children[2].clone(), resolver, depth, origin_span, &scope)?;
    Ok(Sexp::List(
        vec![children[0].clone(), children[1].clone(), body],
        span,
    ))
}

/// `(defn name "doc"? [params] body…)` (single arity) or
/// `(defn name "doc"? ([params] body) …)` (multi arity) — the head, name, and
/// optional docstring are held verbatim; each variant's params are held
/// verbatim and its body expanded with the params shadowing the module scope.
fn expand_defn(
    children: &[Sexp],
    span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    if children.len() < 3 {
        return expand_children_clone(children, span, resolver, depth, origin_span, shadows);
    }
    let mut out: Vec<Sexp> = Vec::with_capacity(children.len());
    out.push(children[0].clone()); // defn / defn-
    out.push(children[1].clone()); // name (a binder — verbatim)
    // S115 (FIXME 0718 / `expansion-qualification-scope.md` §2.5): the defn NAME
    // is in scope inside its own body — a self-call is a reference to THIS
    // definition. Seed it into the body scope so the walk honours the §2.3
    // enumeration's defn-name binder slot. `qualify_defn` carries the identical
    // seeding (P7 — one binder model, two walks).
    let shadows = &match &children[1] {
        Sexp::Symbol(n, _) => {
            let mut s = shadows.clone();
            s.insert(n.clone());
            s
        }
        _ => shadows.clone(),
    };
    let mut idx = 2;
    if let Some(Sexp::Str(..)) = children.get(idx) {
        out.push(children[idx].clone()); // docstring
        idx += 1;
    }
    match children.get(idx) {
        // Single arity: [params] followed by the body form(s).
        Some(Sexp::Bracket(param_items, _)) => {
            let scope = params_scope(param_items, shadows);
            out.push(children[idx].clone()); // params verbatim
            for c in &children[idx + 1..] {
                out.push(expand_scoped(c.clone(), resolver, depth, origin_span, &scope)?);
            }
        }
        // Multi arity: each remaining child is a `([params] body)` variant.
        Some(Sexp::List(..)) => {
            for c in &children[idx..] {
                out.push(expand_defn_variant(c, resolver, depth, origin_span, shadows)?);
            }
        }
        // Unexpected shape — recurse generically (the AST builder reports it).
        _ => {
            for c in &children[idx..] {
                out.push(expand_scoped(c.clone(), resolver, depth, origin_span, shadows)?);
            }
        }
    }
    Ok(Sexp::List(out, span))
}

/// A single multi-arity `defn` variant `([params] body)` — params verbatim,
/// body expanded with the params shadowing the module scope.
fn expand_defn_variant(
    sexp: &Sexp,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    let Sexp::List(items, vspan) = sexp else {
        return expand_scoped(sexp.clone(), resolver, depth, origin_span, shadows);
    };
    let Some(Sexp::Bracket(param_items, _)) = items.first() else {
        return expand_scoped(sexp.clone(), resolver, depth, origin_span, shadows);
    };
    if items.len() != 2 {
        return expand_scoped(sexp.clone(), resolver, depth, origin_span, shadows);
    }
    let scope = params_scope(param_items, shadows);
    let body = expand_scoped(items[1].clone(), resolver, depth, origin_span, &scope)?;
    Ok(Sexp::List(vec![items[0].clone(), body], *vspan))
}

/// `(match scrutinee… [pat body pat body …])` — the scrutinee is expanded in
/// the current scope; each arm's PATTERN is held verbatim (its variables are
/// binders, not reads) and its BODY expanded with those pattern variables
/// shadowing the module scope (§8.6.3). The arms bracket is the last child.
fn expand_match(
    children: &[Sexp],
    span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    origin_span: Option<Span>,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    if children.len() < 3 {
        return expand_children_clone(children, span, resolver, depth, origin_span, shadows);
    }
    let last = children.len() - 1;
    let Sexp::Bracket(arm_items, arms_span) = &children[last] else {
        return expand_children_clone(children, span, resolver, depth, origin_span, shadows);
    };
    let mut out: Vec<Sexp> = Vec::with_capacity(children.len());
    out.push(children[0].clone()); // match
    // Scrutinee region (possibly a `:Type form` pair) — ordinary reads.
    for c in &children[1..last] {
        out.push(expand_scoped(c.clone(), resolver, depth, origin_span, shadows)?);
    }
    if !arm_items.len().is_multiple_of(2) {
        // Malformed arms — recurse generically (the AST builder reports it).
        let expanded: Vec<Sexp> = arm_items
            .iter()
            .map(|c| expand_scoped(c.clone(), resolver, depth, origin_span, shadows))
            .collect::<Result<Vec<_>, _>>()?;
        out.push(Sexp::Bracket(expanded, *arms_span));
        return Ok(Sexp::List(out, span));
    }
    let mut new_arms: Vec<Sexp> = Vec::with_capacity(arm_items.len());
    let mut i = 0;
    while i + 1 < arm_items.len() {
        let pattern = &arm_items[i];
        let body = &arm_items[i + 1];
        let mut scope = shadows.clone();
        scope.extend(pattern_binders(pattern));
        new_arms.push(pattern.clone()); // pattern verbatim (binders, not reads)
        new_arms.push(expand_scoped(body.clone(), resolver, depth, origin_span, &scope)?);
        i += 2;
    }
    out.push(Sexp::Bracket(new_arms, *arms_span));
    Ok(Sexp::List(out, span))
}

/// Execute one recognized macro call through the [`JitMacroExpander`]
/// (`cranelisp_types::MacroExpander`) boundary, then re-expand the result to
/// fixpoint. The walk recognized `fq` via the LOCKED types primitive and the
/// resolver ensured its clause code is in memory; execution is uniform.
///
/// `call_span` is the user-call span to attribute this invocation to — the
/// original top-level call, not the synthetic offset of a recursive-expansion
/// self-call (FIXME 0485). The result's nested calls inherit it via
/// `origin_span = Some(call_span)`.
fn expand_recognized_macro(
    fq: FQSymbol,
    args: &[Sexp],
    call_span: Span,
    resolver: &mut dyn MacroResolver,
    depth: usize,
    shadows: &HashSet<String>,
) -> Result<Sexp, CranelispError> {
    let result = {
        let expander = JitMacroExpander { symbol_tables: resolver.symbol_tables() };
        expander
            .invoke(&fq, args, call_span)
            .map_err(|e| CranelispError::MacroError {
                message: e.to_string(),
                location: ErrorLocation::from_span(call_span),
            })?
    };
    // Re-expand the result (may contain further macro calls); nested calls in
    // the expansion inherit the user-call span as their error-attribution origin.
    // The expansion is spliced into the current position, so it stays under the
    // enclosing lexical scope (`shadows`).
    expand_scoped(result, resolver, depth + 1, Some(call_span), shadows)
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
        let entry = ModuleEntry::def(
            empty_scheme(),
            DefKind::Macro {
                clauses_meta,
                macro_sexp: cranelisp_types::Sexp::List(vec![], Span::SYNTHETIC),
            },
        )
        .visibility(Visibility::Public)
        .build();
        st.insert(Symbol::from(name), entry);
        tables.insert(path, st);
        tables
    }

    /// Recognition stub that recognizes exactly one zero-arg macro name and
    /// records every name the walk asked about (the shield assertions read it).
    struct RecognizeOneStub {
        tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        macro_name: &'static str,
        asked: Vec<String>,
    }
    impl MacroResolver for RecognizeOneStub {
        fn recognize(
            &mut self,
            name: &str,
            _span: Span,
        ) -> Result<Option<FQSymbol>, CranelispError> {
            self.asked.push(name.to_string());
            if name == self.macro_name {
                Ok(Some(FQSymbol {
                    module: ModuleFullPath::from("user"),
                    symbol: Symbol::from(name),
                }))
            } else {
                Ok(None)
            }
        }
        fn symbol_tables(
            &self,
        ) -> &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
            &self.tables
        }
    }

    // spec: repl/spec.md §15.1 (round-trip) / design/int/s102-defect-wave.md §4.2
    // — the NAME position of a `(defmacro …)` form is a binder, never an
    // expression: the walk MUST NOT expand it even when that name is currently
    // registered as a zero-arg macro. This is the D1 co-load shape (a
    // macro-defining macro's output redefines a name that is already a macro —
    // poisoned-regen reload, or the cache-preloaded table during a restart
    // recompile); without the shield the name rewrites to its expansion and
    // `parse_defmacro` dies with "defmacro name must be a symbol".
    #[test]
    fn expand_defmacro_name_position_shielded_from_zero_arg_macro() {
        let mut resolver = RecognizeOneStub {
            tables: dashmap::DashMap::new(),
            macro_name: "x",
            asked: Vec::new(),
        };
        let form = cranelisp_frontend::parse("(defmacro x [] 1)")
            .unwrap()
            .remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("shielded name position must not attempt macro invocation");
        assert_eq!(
            expanded.format_flat(),
            form.format_flat(),
            "the defmacro form must round-trip unchanged"
        );
        assert!(
            !resolver.asked.contains(&"x".to_string()),
            "the walk must not even ASK about the name position: asked={:?}",
            resolver.asked
        );
    }

    // Negative twin: outside the shielded positions the walk still expands —
    // a bare zero-arg macro symbol in an ordinary list IS recognized (and here
    // fails at invocation, since the stub's tables hold no clause code) —
    // pinning that the shield is defmacro-name-scoped, not a blanket skip.
    // spec: design/int/s102-defect-wave.md §4.2
    #[test]
    fn expand_zero_arg_macro_outside_defmacro_name_still_recognized() {
        let mut resolver = RecognizeOneStub {
            tables: dashmap::DashMap::new(),
            macro_name: "x",
            asked: Vec::new(),
        };
        let form = cranelisp_frontend::parse("(add-i64 x 1)").unwrap().remove(0);
        let result = expand_sexp_recursive(form, &mut resolver, 0, None);
        assert!(
            resolver.asked.contains(&"x".to_string()),
            "a bare symbol in an ordinary argument position is still walked: asked={:?}",
            resolver.asked
        );
        assert!(
            result.is_err(),
            "recognition led to invocation (which fails without clause code) — \
             the walk did not skip it"
        );
    }

    // --- §8.6.3 lexical-shadow shield (S103 Defect 2) ---

    fn shadow_stub(macro_name: &'static str) -> RecognizeOneStub {
        RecognizeOneStub {
            tables: dashmap::DashMap::new(),
            macro_name,
            asked: Vec::new(),
        }
    }

    // spec: spec/08-modules.md §8.6.3 — a `let` binding named `g` lexically
    // shadows a top-level zero-arg `def`-macro `g`. Neither the BINDER `g` nor
    // the body READ `g` (which resolves to the local) may be macro-expanded; the
    // form round-trips unchanged and the walk never even attempts to invoke `g`.
    #[test]
    fn let_binder_and_body_shadow_zero_arg_macro() {
        let mut resolver = shadow_stub("g");
        let form = cranelisp_frontend::parse("(let [g 7] g)").unwrap().remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("a lexically-shadowed g must not be macro-invoked");
        assert_eq!(expanded.format_flat(), form.format_flat());
        assert!(
            !resolver.asked.contains(&"g".to_string()),
            "a shadowed binder/read must not be recognized: asked={:?}",
            resolver.asked
        );
    }

    // spec: spec/08-modules.md §8.6.3 — a `fn`/`defn` PARAMETER named `g` shadows
    // the top-level macro `g` in the body. The param binder (with its `:Int`
    // annotation) and the body read are both held; the form round-trips.
    #[test]
    fn defn_param_shadows_zero_arg_macro() {
        let mut resolver = shadow_stub("g");
        let form = cranelisp_frontend::parse("(defn f [:Int g] g)").unwrap().remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("a shadowing param g must not be macro-invoked");
        assert_eq!(expanded.format_flat(), form.format_flat());
        assert!(!resolver.asked.contains(&"g".to_string()), "asked={:?}", resolver.asked);
    }

    // spec: spec/08-modules.md §8.6.3 — a `match` PATTERN variable `g` shadows the
    // top-level macro `g` in the arm body. The pattern `(Box g)` is held verbatim
    // (its `g` is a binder, not a read) and the arm body `g` resolves to the local.
    #[test]
    fn match_pattern_var_shadows_zero_arg_macro() {
        let mut resolver = shadow_stub("g");
        let form = cranelisp_frontend::parse("(match b [(Box g) g])").unwrap().remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("a shadowing pattern var g must not be macro-invoked");
        assert_eq!(expanded.format_flat(), form.format_flat());
        assert!(!resolver.asked.contains(&"g".to_string()), "asked={:?}", resolver.asked);
    }

    // spec: spec/08-modules.md §8.6.3 — the defn NAME is in scope inside its own
    // body (a self-call is a reference to THIS definition), so a module-scope
    // zero-arg macro whose name collides with the `defn` being defined does NOT
    // expand in that body. `expansion-qualification-scope.md` §2.5 rules that
    // BOTH scope-aware walks seed the name; this is the EXPANDER half of that
    // mirror (`qualify_defn`'s half is pinned by
    // `macro_resolution::tests::qualify_seeds_defn_name_into_its_body_scope`).
    //
    // On this side the seeded set gates macro EXPANSION, so the seeding is a real
    // behaviour change and needs its own standing guard: reverting the expander
    // half alone left the whole suite green (FIXME 0792).
    //
    // Fail-on-revert: without the seeding, `(g)` in the body is recognized, the
    // walk attempts invocation, and the stub (which holds no clause code) makes
    // `expand_sexp_recursive` return `Err` — the `.expect` below fires.
    //
    // Discriminating control IN CELL: the free, unshadowed `h` in the same body
    // IS still asked about, so a blanket "skip the whole defn body" regression
    // cannot pass this cell (it would be rescued only by sibling cells otherwise).
    #[test]
    fn defn_name_shadows_zero_arg_macro_in_its_own_body() {
        let mut resolver = shadow_stub("g");
        let form = cranelisp_frontend::parse("(defn g [] (add-i64 (g) h))")
            .unwrap()
            .remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("the defn's own name must not be macro-invoked inside its body");
        assert_eq!(expanded.format_flat(), form.format_flat());
        assert!(
            !resolver.asked.contains(&"g".to_string()),
            "the defn self-name must not even be recognized in its own body: asked={:?}",
            resolver.asked
        );
        assert!(
            resolver.asked.contains(&"h".to_string()),
            "control: a free symbol in the SAME body is still walked — the seeding \
             is defn-name-scoped, not a blanket body skip: asked={:?}",
            resolver.asked
        );
    }

    // spec: spec/08-modules.md §8.6.3 — multi-arity variant bodies share the same
    // defn self-name scope (`expansion-qualification-scope.md` §2.5; the twin of
    // `macro_resolution::tests::qualify_seeds_defn_name_into_multi_arity_variant_bodies`).
    // Same fail-on-revert and same in-cell control as the single-arity cell.
    #[test]
    fn defn_name_shadows_zero_arg_macro_in_multi_arity_variant_bodies() {
        let mut resolver = shadow_stub("g");
        let form = cranelisp_frontend::parse("(defn g ([] (g)) ([x] (add-i64 (g) h)))")
            .unwrap()
            .remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("multi-arity variant bodies must also see the defn self-name");
        assert_eq!(expanded.format_flat(), form.format_flat());
        assert!(
            !resolver.asked.contains(&"g".to_string()),
            "the defn self-name must not be recognized in any variant body: asked={:?}",
            resolver.asked
        );
        assert!(
            resolver.asked.contains(&"h".to_string()),
            "control: a free symbol in a variant body is still walked: asked={:?}",
            resolver.asked
        );
    }

    // Negative twin (don't over-shield reads): a `g` in VALUE position — a `let`
    // binding whose VALUE reads `g` (a genuine read of the module-scope macro,
    // NOT shadowed by the unrelated binder `h`) — IS still recognized and
    // expanded. Recognition leads to invocation, which fails without clause code.
    // spec: spec/08-modules.md §8.6.3
    #[test]
    fn free_read_in_let_value_still_expands() {
        let mut resolver = shadow_stub("g");
        let form = cranelisp_frontend::parse("(let [h g] h)").unwrap().remove(0);
        let result = expand_sexp_recursive(form, &mut resolver, 0, None);
        assert!(
            resolver.asked.contains(&"g".to_string()),
            "a free (unshadowed) read of g must still be recognized: asked={:?}",
            resolver.asked
        );
        assert!(
            result.is_err(),
            "recognition of the free g led to invocation (fails without clause code)"
        );
    }

    // --- §9.4 quote shield (S111, design/int/quote-shield.md) ---

    // spec: spec/09-macros.md §9.4.4 — Rule Q: a `(quote …)` form is pure data
    // held FULLY verbatim, with NO descent. A macro-call-shaped list inside the
    // quoted datum must NOT be recognized (the corruption `'(m x)` would suffer
    // without the shield); the form round-trips unchanged and the walk never
    // even ASKS about the quoted `m`.
    #[test]
    fn quote_form_held_verbatim_shields_inner_macro() {
        let mut resolver = shadow_stub("m");
        let form = cranelisp_frontend::parse("(quote (m x))").unwrap().remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("quoted data must not be expanded");
        assert_eq!(expanded.format_flat(), form.format_flat(), "quote round-trips verbatim");
        assert!(
            !resolver.asked.contains(&"m".to_string()),
            "a macro under quote must not be recognized: asked={:?}",
            resolver.asked
        );
    }

    // spec: spec/09-macros.md §9.4.4 — Rule QQ, template data: a macro-call-shaped
    // list under `quasiquote` OUTSIDE any unquote is template data, held verbatim
    // — `m` is not recognized.
    #[test]
    fn quasiquote_template_data_shields_macro() {
        let mut resolver = shadow_stub("m");
        let form = cranelisp_frontend::parse("(quasiquote (m x))").unwrap().remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("quasiquote template data must not be expanded");
        assert_eq!(expanded.format_flat(), form.format_flat(), "template data round-trips");
        assert!(
            !resolver.asked.contains(&"m".to_string()),
            "a macro in template data must not be recognized: asked={:?}",
            resolver.asked
        );
    }

    // spec: spec/09-macros.md §9.4.2 — Rule QQ, LIVE unquote: the body of an
    // `unquote` at the matching depth is an ordinary expression position, re-
    // entered through `expand_scoped`. The walk DOES recognize the macro `m`
    // there (and here fails at invocation without clause code — proving the
    // shield descended, not that it over-shielded).
    #[test]
    fn quasiquote_live_unquote_expands_macro() {
        let mut resolver = shadow_stub("m");
        let form = cranelisp_frontend::parse("(quasiquote (a (unquote (m))))")
            .unwrap()
            .remove(0);
        let result = expand_sexp_recursive(form, &mut resolver, 0, None);
        assert!(
            resolver.asked.contains(&"m".to_string()),
            "a macro under a LIVE unquote must be recognized: asked={:?}",
            resolver.asked
        );
        assert!(
            result.is_err(),
            "recognition led to invocation (fails without clause code) — the shield descended"
        );
    }

    // spec: spec/09-macros.md §9.4.4 (depth guard) — the shield tracks nesting
    // depth exactly: an `unquote` inside a NESTED quasiquote belongs to the inner
    // template (qq_depth 1 for the outer), so it stays shielded at outer
    // processing — the macro `m` is NOT recognized.
    #[test]
    fn nested_quasiquote_depth_shields_inner_unquote() {
        let mut resolver = shadow_stub("m");
        let form =
            cranelisp_frontend::parse("(quasiquote (a (quasiquote (b (unquote (m x))))))")
                .unwrap()
                .remove(0);
        let expanded = expand_sexp_recursive(form.clone(), &mut resolver, 0, None)
            .expect("an inner-quasiquote unquote stays shielded at the outer level");
        assert_eq!(expanded.format_flat(), form.format_flat(), "nested template round-trips");
        assert!(
            !resolver.asked.contains(&"m".to_string()),
            "a depth-1 unquote must not expand at the outer level: asked={:?}",
            resolver.asked
        );
    }

    // spec: spec/09-macros.md §9.4.4 — a `(quote …)` encountered WHILE shielding a
    // quasiquote is an ORDINARY list (§5.1): shield_qq keeps walking its children
    // at the same depth, so a live unquote inside it is still found (`` `(quote ~(m)) ``
    // — the `~(m)` is live). The macro IS recognized (proving no quote
    // short-circuit inside shield_qq).
    #[test]
    fn quote_under_active_quasiquote_is_ordinary_list() {
        let mut resolver = shadow_stub("m");
        let form = cranelisp_frontend::parse("(quasiquote (quote (unquote (m))))")
            .unwrap()
            .remove(0);
        let result = expand_sexp_recursive(form, &mut resolver, 0, None);
        assert!(
            resolver.asked.contains(&"m".to_string()),
            "a live unquote inside a quoted list under quasiquote must be found: asked={:?}",
            resolver.asked
        );
        assert!(result.is_err(), "recognition led to invocation (fails without clause code)");
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

    /// Hand-build a `MacroClauseEntry` with the given fixed-param count and
    /// variadic flag; the `func_ptr` is never dereferenced by the diagnostic
    /// path (clause matching + message building read only `params`/`rest_param`).
    fn clause(fixed: usize, variadic: bool) -> MacroClauseEntry {
        MacroClauseEntry {
            func_ptr: std::ptr::null(),
            params: (0..fixed)
                .map(|i| MacroParam::Name(Symbol::from(format!("p{i}"))))
                .collect(),
            rest_param: variadic.then(|| Symbol::from("rest")),
        }
    }

    // spec: spec/09-macros.md §9.4 (multi-clause defmacro) + CLAUDE.md §Design
    // Principles (self-documenting REPL) — the clause-exhaustion diagnostic
    // anchors at the USER-CALL span (threaded down the expansion recursion, NOT
    // a synthetic ≥1_000_000 expansion-buffer offset) and surfaces the accepted
    // clause arities derived from the actual clause set. Guards FIXME 0485.
    #[test]
    fn no_matching_clause_error_reports_user_span_and_clause_arities() {
        // A `cond`-shaped clause set: `([] …)` (0, no rest) + `([t b &rest] …)`
        // (2, variadic) → accepted arities "0 or 2+".
        let clauses = vec![clause(0, false), clause(2, true)];
        let fq = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("mycond"),
        };
        // The user typed the call at a REAL source position, not synthetic.
        let user_span = Span::new(42, 63);
        // 1 argument matches neither clause (the recursion bottom).
        let args = [Sexp::Bool(false, Span::SYNTHETIC)];
        let err = no_matching_clause_error(&fq, &clauses, &args, user_span);
        match err {
            MacroInvokeError::Malformed { message, span, fq: efq } => {
                // (a) span IS the user-call span, never a synthetic offset.
                assert_eq!(span, user_span, "must carry the user-call span");
                assert!(
                    span.start < 1_000_000 && span.end < 1_000_000,
                    "must not be a synthetic expansion-buffer span: {span}"
                );
                // (b) arity hint derived from the clause set.
                assert!(
                    message.contains("0 or 2+"),
                    "arity hint from the clause set: {message}"
                );
                assert!(message.contains("1 argument(s)"), "the call's grain: {message}");
                assert_eq!(efq.symbol, Symbol::from("mycond"));
            }
            other => panic!("expected Malformed, got {other:?}"),
        }
    }

    // spec: spec/09-macros.md §9.4 — the arity description is derived from the
    // MacroClauseEntry shapes for ANY multi-clause macro, not a cond-hardcoded
    // string: fixed count, `+` for variadic, dedup, joined for display.
    #[test]
    fn describe_clause_arities_is_general_not_cond_specific() {
        // Single fixed-arity clause.
        assert_eq!(describe_clause_arities(&[clause(2, false)]), "2");
        // Single variadic clause.
        assert_eq!(describe_clause_arities(&[clause(1, true)]), "1+");
        // cond shape: 0 fixed + 2-variadic → "0 or 2+".
        assert_eq!(
            describe_clause_arities(&[clause(0, false), clause(2, true)]),
            "0 or 2+"
        );
        // A different multi-clause macro: 1, 2, 3+.
        assert_eq!(
            describe_clause_arities(&[clause(1, false), clause(2, false), clause(3, true)]),
            "1, 2 or 3+"
        );
        // Duplicate arities collapse.
        assert_eq!(
            describe_clause_arities(&[clause(2, false), clause(2, false)]),
            "2"
        );
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
            DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
            },
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
        let entry = ModuleEntry::def(
            empty_scheme(),
            DefKind::Macro {
                clauses_meta,
                macro_sexp: cranelisp_types::Sexp::List(vec![], Span::SYNTHETIC),
            },
        )
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
