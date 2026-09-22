//! `MacroExpander` — the execution half of macro expansion: run one compiled
//! macro invocation and return its output form.
//!
//! Expansion is split into two jobs (`design/arch/macro-expansion-ownership.md`
//! §1). *Recognition* — is this head a macro, and which canonical `FQSymbol`?
//! — is the resolution query [`ResolutionScope::resolve_macro_head`].
//! *Execution* needs the compiled clause, runtime marshalling and signal
//! protection, which only the binary may reach; it sits behind this trait.
//!
//! The binary both implements the trait and calls it. Its Pass-1 expansion
//! loop recognises each head, invokes the expander, re-expands the result to
//! fixpoint and only then hands fully expanded, macro-free forms to
//! typecheck. Typecheck holds no expander and never sees a macro invocation.
//! The trait lives in this crate as the named boundary contract; it adds no
//! dependency edge (Principle 03 — Dependency flows toward stability).
//!
//! The result is a raw [`Sexp`], not a classified form: the caller must
//! re-walk it anyway because it may contain further macro calls at any depth.
//!
//! [`ResolutionScope::resolve_macro_head`]: crate::ResolutionScope::resolve_macro_head

use crate::{FQSymbol, Sexp, Span};

/// Why a macro invocation produced no output form.
///
/// Every variant carries the macro's identity, a human-readable diagnostic and
/// the call span; `Display` renders all three. Callers report the error rather
/// than branch on the variant. `#[non_exhaustive]` so the implementor may add
/// failure classes without breaking consumers.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum MacroInvokeError {
    /// The invocation could not run to completion: the macro has no executable
    /// clause, or the clause panicked, raised a hardware trap
    /// (SIGFPE/SIGILL/SIGBUS) or set the runtime error slot. `span` is the
    /// call span passed to [`MacroExpander::invoke`].
    Aborted {
        fq: FQSymbol,
        message: String,
        span: Span,
    },
    /// The call or its result does not fit the macro: no clause matches the
    /// arguments, or the clause returned a value that is not a well-formed
    /// `Sexp`. `span` is the call span passed to [`MacroExpander::invoke`].
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
                write!(
                    f,
                    "macro `{fq}` returned malformed sexp at {span}: {message}"
                )
            }
        }
    }
}

impl std::error::Error for MacroInvokeError {}

/// Injected capability: execute one JIT-compiled macro invocation.
///
/// Implemented by the binary over the committed session tables and called by
/// its own Pass-1 expansion loop; see the module documentation for the split.
///
/// `Send + Sync`: expansion workers may invoke concurrently; the implementor
/// isolates per-call signal state.
pub trait MacroExpander: Send + Sync {
    /// Invoke the clause of macro `fq` that matches `args` and return its
    /// output form.
    ///
    /// # Parameters
    /// - `fq` — the macro's canonical identity, as returned by
    ///   `ResolutionScope::resolve_macro_head`. The implementor reads the
    ///   declaration stored at exactly this key.
    /// - `args` — the call form's argument `Sexp`s, head excluded, passed to
    ///   the clause as given. The implementor does not expand them; the Pass-1
    ///   caller passes them unexpanded and re-expands the result.
    /// - `call_span` — the span every error is attributed to. Inside a nested
    ///   expansion the caller passes the original user call's span.
    ///
    /// # Returns
    /// The output `Sexp`, every node carrying a fresh, unique synthetic span
    /// so span-keyed maps downstream cannot collide.
    ///
    /// # Errors
    /// A [`MacroInvokeError`] when no clause matches or the invocation fails.
    /// The caller invokes only macros whose clauses have been published (the
    /// macro availability model); asked for one with no executable clause,
    /// the implementor returns [`MacroInvokeError::Aborted`] and never calls
    /// absent code.
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
