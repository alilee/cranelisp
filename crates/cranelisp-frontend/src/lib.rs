//! cranelisp-frontend: reader (source -> Sexp) and AST builder (Sexp -> Expr/TopLevel).
//!
//! Three-phase pipeline:
//!   1. Reader: source text -> Vec<Sexp>
//!   2. Macro expansion: quasiquote desugaring, defmacro parsing (Ring 3)
//!   3. AST builder: Vec<Sexp> -> Vec<TopLevel> (both batch and REPL)
//!
//! Macro expansion must happen BEFORE calling the AST builder. If an unexpanded
//! macro call reaches the AST builder, it is treated as a regular function
//! application (which will fail at typecheck).

pub mod reader;
pub mod ast_builder;
pub mod expand;
pub mod module_extract;
pub mod quasiquote;
pub mod defmacro;

use cranelisp_types::{CranelispError, Program, Sexp, TopLevel};

pub use expand::ExpansionError;
// Re-export `ResolutionGap` for ergonomics — frontend originates the
// `MacroInMem` variant per the facade contract (FIXME 0098 Phase 2 step 1).
pub use cranelisp_types::ResolutionGap;
pub use module_extract::extract_module_declarations;
pub use module_extract::ExtractedDeclarations;
pub use module_extract::{
    parse_import_sexp, parse_export_sexp, parse_mod_sexp, parse_platform_sexp,
};
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
/// Callers must expand macros before calling this function.
pub fn build_program(
    sexps: &[Sexp],
) -> Result<Program, CranelispError> {
    ast_builder::build_program(sexps)
}

/// Build REPL input from a sequence of S-expressions.
///
/// Handles top-level annotation expressions where `:Type expr` parses as
/// two separate sexps. Falls through to single-sexp handling otherwise.
/// Callers must expand macros before calling this function.
pub fn build_repl_input_from_sexps(
    sexps: &[Sexp],
) -> Result<TopLevel, CranelispError> {
    ast_builder::build_repl_input_from_sexps(sexps)
}

/// Build REPL input from a single S-expression.
///
/// Accepts top-level forms and bare expressions.
/// Callers must expand macros before calling this function.
pub fn build_repl_input(
    sexp: &Sexp,
) -> Result<TopLevel, CranelispError> {
    ast_builder::build_repl_input(sexp)
}
