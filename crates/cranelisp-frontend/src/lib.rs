//! cranelisp-frontend: reader (source -> Sexp) and AST builder (Sexp -> Expr/TopLevel).
//!
//! Three-phase pipeline:
//!   1. Reader: source text -> Vec<Sexp>
//!   2. Macro expansion: quasiquote desugaring, defmacro parsing (Ring 3)
//!   3. AST builder: Vec<Sexp> -> Vec<TopLevel> (batch) or ReplInput (REPL)
//!
//! The macro expander trait is defined in cranelisp-types for dependency inversion.
//! Ring 0 uses NoOpExpander (no macros).

pub mod reader;
pub mod ast_builder;
pub mod module_extract;
pub mod quasiquote;
pub mod defmacro;

use cranelisp_types::{CranelispError, MacroExpander, Program, ReplInput, Sexp};

pub use module_extract::extract_module_declarations;
pub use quasiquote::{expand_quasiquotes, next_synthetic_span};
pub use defmacro::{
    is_defmacro, is_begin, flatten_begin, parse_defmacro, parse_macro_params,
    synthesize_macro_clause_defn, DefmacroInfo, MacroClause,
};

/// Parse source text into a sequence of S-expressions.
#[must_use = "parsing produces a result that should be checked for errors"]
pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError> {
    reader::parse(source)
}

/// Parse source text, preserving comments as `Sexp::Comment` nodes.
#[must_use = "parsing produces a result that should be checked for errors"]
pub fn parse_preserving_comments(source: &str) -> Result<Vec<Sexp>, CranelispError> {
    reader::parse_preserving_comments(source)
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

/// Build REPL input from a sequence of S-expressions.
///
/// Handles top-level annotation expressions where `:Type expr` parses as
/// two separate sexps. Falls through to single-sexp handling otherwise.
pub fn build_repl_input_from_sexps(
    sexps: &[Sexp],
    expander: &mut dyn MacroExpander,
) -> Result<ReplInput, CranelispError> {
    ast_builder::build_repl_input_from_sexps(sexps, expander)
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
