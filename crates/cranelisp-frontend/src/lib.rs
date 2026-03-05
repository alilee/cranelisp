//! cranelisp-frontend: reader (source -> Sexp) and AST builder (Sexp -> Expr/TopLevel).
//!
//! Two-phase pipeline:
//!   1. Reader: source text -> Vec<Sexp>
//!   2. AST builder: Vec<Sexp> -> Vec<TopLevel> (batch) or ReplInput (REPL)
//!
//! The macro expander trait is defined in cranelisp-types for dependency inversion.
//! Ring 0 uses NoOpExpander (no macros).

pub mod reader;
pub mod ast_builder;

use cranelisp_types::{CranelispError, MacroExpander, Program, ReplInput, Sexp};

/// Parse source text into a sequence of S-expressions.
#[must_use = "parsing produces a result that should be checked for errors"]
pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError> {
    reader::parse(source)
}

/// Build a batch program from parsed S-expressions.
///
/// Each sexp must be a top-level form (defn, deftype, etc.).
/// The expander is consulted for macro calls; Ring 0 passes `NoOpExpander`.
pub fn build_program(
    sexps: &[Sexp],
    expander: &mut dyn MacroExpander,
) -> Result<Program, CranelispError> {
    ast_builder::build_program(sexps, expander)
}

/// Build REPL input from a single S-expression.
///
/// Accepts top-level forms and bare expressions.
/// The expander is consulted for macro calls; Ring 0 passes `NoOpExpander`.
pub fn build_repl_input(
    sexp: &Sexp,
    expander: &mut dyn MacroExpander,
) -> Result<ReplInput, CranelispError> {
    ast_builder::build_repl_input(sexp, expander)
}
