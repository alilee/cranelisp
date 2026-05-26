//! cranelisp-frontend: reader (source -> Sexp), per-form AST builder
//! (Sexp -> ParsedEntry/Expr), and macro expansion.
//!
//! Post-FIXME-0156 (Sprint 66 Wave 3a-β) the public boundary is four free
//! functions used by `int::process_cluster` (`facades/int.md`):
//!   1. Reader: `parse(source: &str) -> Vec<Sexp>` / `parse_preserving_comments`.
//!   2. Module-decl extraction: `extract_module_declarations(path, sexps)`
//!      peels `mod`/`mod-`/`import`/`export`/`platform` and normalises
//!      `super`.
//!   3. Per-form build: `build_form(sexp) -> Vec<ParsedEntry>` plus
//!      `build_expr(sexp) -> Expr` for bare REPL expressions.
//!   4. Macro expansion: `expand(sexp, &symbol_tables) -> Sexp` —
//!      structural pass that returns `ExpansionError::Gap(...)` for any
//!      unresolved macro head (FIXME 0175 tracks the invocation gap; the
//!      live invocation path remains in `src/expander.rs` until /arch
//!      resolves dep-layer access).
//!
//! Macro expansion MUST run BEFORE `build_form` / `build_expr`. Unexpanded
//! macro calls reaching the AST builder become silent generic applications
//! and fail later with confusing diagnostics.

pub mod reader;
pub mod ast_builder;
pub mod expand;
pub mod module_extract;
pub mod quasiquote;
pub mod defmacro;

use cranelisp_types::{CranelispError, Sexp};

// `build_form` and `build_expr` are mode-agnostic. `(trace ...)` in `--link`
// standalone-binary mode fails at link time via the architecture's natural
// missing-symbol detection (the trace runtime is not bundled into the staticlib
// produced by exe-bundle); no frontend pre-pass check is needed. See
// spec/04-expressions.md §4.12.9.
pub use ast_builder::{build_expr, build_form};
pub use expand::{expand, ExpansionError, EXPANSION_DEPTH_LIMIT};
// Re-export `ResolutionGap` for ergonomics — `ExpansionError::Gap` consumers
// always need `ResolutionGap` in scope. Per the facade §"Types originated
// here": narrow ergonomic exception to Principle 15.
//
// `SymbolTables` and `ModuleAliases` are NOT re-exported here per F2's
// /arch disposition — consumers import directly from `cranelisp-types`
// (Principle 15 placement clarity; type aliases lack the
// enum-variant-pattern-match justification of `ResolutionGap`).
pub use cranelisp_types::ResolutionGap;
pub use module_extract::extract_module_declarations;
pub use module_extract::ExtractedDeclarations;
pub use quasiquote::{expand_quasiquotes, expand_quote_template, next_synthetic_span};
pub use defmacro::{
    is_defmacro, is_begin, flatten_begin, parse_defmacro,
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
