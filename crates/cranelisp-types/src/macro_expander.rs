//! `MacroExpander` — the callback boundary by which `cranelisp-typecheck`
//! executes a single JIT-compiled macro invocation without depending on the
//! integration layer.
//!
//! ## Why this trait exists
//!
//! Macro *recognition* (walk a form, find a macro head, look up its entry) is
//! pure structural + symbol-table work — it belongs in typecheck, which
//! already walks every cluster form and resolves every head symbol
//! (`design/arch/bounded-contexts.md` §2). Macro *execution* (marshal the
//! argument `Sexp`s into runtime ADT values, transmute the JIT'd clause's GOT
//! address to `extern "C" fn(i64) -> i64`, call it under
//! `sigsetjmp`/`siglongjmp` signal protection, unmarshal the result) needs the
//! allocator, the runtime panic slot, and `libc` — capabilities that live in
//! the integration layer (`src/expander.rs` + `src/marshal.rs`) and that
//! neither `cranelisp-typecheck` nor `cranelisp-frontend` may depend on
//! (Principle 3 — the dependency graph flows toward stability; typecheck
//! depends only on `cranelisp-types`).
//!
//! A direct `typecheck → int` call is forbidden (int depends on typecheck;
//! the reverse edge is a cycle). So execution is **injected**: `int` — the
//! orchestrator that already calls `check_forms` — supplies an implementor of
//! this trait, and typecheck calls back through it for each macro invocation
//! it recognises. The trait lives here in `cranelisp-types` because it crosses
//! the typecheck ↔ int boundary, and only boundary contracts live in this
//! crate (Principle 15). `int` implements it over its existing invocation core
//! (`src/expander.rs::invoke_clause` + `src/marshal.rs`); typecheck holds a
//! `&dyn MacroExpander` for the duration of a `check_forms` call.
//!
//! Replaces the REJECTED `cranelisp-marshal` bridge-crate option from
//! FIXME 0175 (user-arbitrated, S76 Phase 2). A new crate would have had to
//! re-export the allocator + signal machinery across a types-stable surface;
//! the callback achieves the same separation with no new crate and no
//! dependency widening of frontend or typecheck.
//!
//! ## Contract
//!
//! - The expander receives the macro's fully-qualified identity, the
//!   already-expanded argument `Sexp`s (children of the call form, head
//!   excluded), and the call-site `Span`.
//! - It guarantees the clause is in memory before it is called: the
//!   orchestrator's `handle_gap` discipline (priority-boost + `wait_for_inmem`)
//!   runs before `check_forms` is (re)entered, so by the time typecheck calls
//!   back, the GOT slot for the matched clause is populated. The expander
//!   panics (never silently misbehaves) if asked to invoke a macro whose code
//!   is absent — that is an orchestrator-sequencing bug, not a user error.
//! - It returns the macro's output `Sexp` with **freshly-allocated unique
//!   synthetic spans** on every node (span-rewrite is part of the invocation
//!   core), so downstream span-keyed maps do not collide.
//! - It is `Send + Sync`: multiple typecheck workers may call back
//!   concurrently with disjoint inputs (the invocation core installs
//!   per-call thread-local signal state).
//!
//! The result is a **raw `Sexp`**, deliberately not a richer classified
//! product: typecheck re-walks the returned tree itself (nested-macro
//! fixpoint + structural-form re-classification). See
//! `design/typecheck/macro-recognition.md` §"Structural-form re-entry" for why
//! the raw-`Sexp` return is correct and a classified return would invert the
//! boundary.

use crate::{FQSymbol, Sexp, Span};

/// The error a macro invocation can surface back to typecheck.
///
/// `#[non_exhaustive]` so the integration layer may add carrier detail
/// (e.g., a captured backtrace) without breaking the typecheck consumer.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum MacroInvokeError {
    /// The macro body panicked, raised a hardware trap (SIGFPE/SIGILL/SIGBUS),
    /// or set the runtime error slot during execution. The message is the
    /// human-readable diagnostic the integration layer recovered; the `span`
    /// is the call site.
    Aborted {
        fq: FQSymbol,
        message: String,
        span: Span,
    },
    /// The macro returned a value that is not a well-formed `Sexp` ADT
    /// (e.g., a non-heap-pointer where a constructor was expected).
    Malformed {
        fq: FQSymbol,
        message: String,
        span: Span,
    },
}

impl std::fmt::Display for MacroInvokeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MacroInvokeError::Aborted { fq, message, span } => {
                write!(f, "macro `{fq}` aborted at {span}: {message}")
            }
            MacroInvokeError::Malformed { fq, message, span } => {
                write!(f, "macro `{fq}` returned malformed sexp at {span}: {message}")
            }
        }
    }
}

impl std::error::Error for MacroInvokeError {}

/// Injected capability: execute one JIT-compiled macro invocation.
///
/// Implemented by the integration layer (`int`) over its invocation core;
/// held by `cranelisp-typecheck` as `&dyn MacroExpander` for the duration of a
/// `check_forms` call. See the module-level rustdoc for the boundary rationale
/// and `design/typecheck/macro-recognition.md` for the typecheck-side
/// algorithm.
///
/// `Send + Sync` supertraits: concurrent typecheck workers may invoke macros
/// in parallel (Decision 38 — per-symbol parallelism); the implementor's
/// invocation core is responsible for per-call signal-handler isolation.
pub trait MacroExpander: Send + Sync {
    /// Invoke the macro clause matching `args` and return its output form.
    ///
    /// # Parameters
    /// - `fq` — the macro's fully-qualified identity (used for clause lookup,
    ///   GOT dispatch, and error attribution).
    /// - `args` — the already-expanded argument `Sexp`s (the call form's
    ///   children with the head removed). The implementor selects the matching
    ///   clause by arity/pattern, marshals these to runtime ADT values, and
    ///   passes them to the JIT'd clause.
    /// - `call_span` — the source span of the macro call, for span attribution
    ///   in errors and (via the implementor) the synthetic-span seed.
    ///
    /// # Returns
    /// The macro's output `Sexp` with unique synthetic spans on every node, or
    /// a [`MacroInvokeError`] if the body aborted or returned a malformed
    /// value.
    fn invoke(
        &self,
        fq: &FQSymbol,
        args: &[Sexp],
        call_span: Span,
    ) -> Result<Sexp, MacroInvokeError>;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cond_fq() -> FQSymbol {
        FQSymbol {
            module: "control".into(),
            symbol: "cond".into(),
        }
    }

    // The user-facing Display of a macro-invocation error must name the macro
    // by its `module/symbol` form (FQSymbol's own Display), never leak the
    // struct's `Debug` shape. Guards FIXME 0485.
    #[test]
    fn malformed_display_uses_fq_display_not_debug() {
        let err = MacroInvokeError::Malformed {
            fq: cond_fq(),
            message: "not a heap pointer".into(),
            span: Span::new(3, 7),
        };
        let rendered = format!("{err}");
        assert!(
            rendered.contains("control/cond"),
            "expected `control/cond`, got: {rendered}"
        );
        assert!(
            !rendered.contains("FQSymbol {"),
            "Debug FQSymbol leaked into user-facing text: {rendered}"
        );
    }

    // Sibling arm on the same diagnostic path — must render identically.
    #[test]
    fn aborted_display_uses_fq_display_not_debug() {
        let err = MacroInvokeError::Aborted {
            fq: cond_fq(),
            message: "body panicked".into(),
            span: Span::new(3, 7),
        };
        let rendered = format!("{err}");
        assert!(
            rendered.contains("control/cond"),
            "expected `control/cond`, got: {rendered}"
        );
        assert!(
            !rendered.contains("FQSymbol {"),
            "Debug FQSymbol leaked into user-facing text: {rendered}"
        );
    }
}
