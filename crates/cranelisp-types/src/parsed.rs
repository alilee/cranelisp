//! Parse-time-only transient types — produced by
//! `cranelisp_frontend::build_form` and consumed by
//! `cranelisp_typecheck::check_form`.
//!
//! `ParsedEntry` and `DefmacroInfo` are NOT persisted to the cache and
//! NEVER land in `SymbolTable`. The lifecycle is bounded by one orchestrator
//! iteration: `parse → ParsedEntry → check_form → Vec<(Symbol,
//! ModuleEntry)> → SymbolTable.insert`. The SymbolTable invariant ("if it's
//! in the table, it's checked") is preserved.
//!
//! Per FIXME 0156 resolution (Sprint 66 Phase 3).

use crate::{
    ConstructorDef, DefnVariant, FieldDef, MacroParam, Sexp, Span, Symbol, TraitDecl, TraitImpl,
    TypeName, Visibility,
};

/// Parse-time-only transient. Carries only what the parser knows;
/// resolved-stage fields (type, scheme, callees, code, got_slot) are
/// populated by `check_form` downstream and end up on `ModuleEntry`.
/// NEVER lands in `SymbolTable`.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum ParsedEntry {
    /// Parsed `(defn name (params) body)` form. Pre-typecheck — types are
    /// `TypeExpr`, no `Scheme`.
    Def {
        name: Symbol,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        docstring: Option<String>,
        span: Span,
    },
    /// Parsed `(deftype Name … | (Variant fields...))` form.
    /// Yields the type itself plus per-constructor entries downstream.
    TypeDef {
        name: TypeName,
        type_params: Vec<TypeName>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        docstring: Option<String>,
        span: Span,
    },
    /// Parsed `(deftrait Name … (method sig)*)` form.
    TraitDecl { decl: TraitDecl },
    /// Parsed `(impl Trait Type method-defns…)` form.
    TraitImpl { impl_: TraitImpl },
    /// Parsed `(defmacro name clauses…)` form. Each clause downstream becomes
    /// a `Def { kind: UserFn }` body under the mangled name
    /// `{macro-name}$clause-{N}` (via `synthesize_macro_clause_defn`), with a
    /// parent `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }`
    /// holding metadata only. See `DefKind::Macro` rustdoc in this file
    /// for the unified shape; the prior sibling `ModuleEntry::Macro` variant
    /// retires in the S69 concurrency-cluster /dev brief.
    Macro { info: DefmacroInfo },
    /// Synthetic per-constructor entry — emitted by `build_form` for each
    /// constructor of a `TypeDef`. Pre-typecheck shape; `check_form` lifts
    /// to a `ModuleEntry::Def` with primitive-kind constructor metadata.
    Constructor {
        name: Symbol,
        of_type: TypeName,
        fields: Vec<FieldDef>,
        span: Span,
    },
}

/// Parsed defmacro components (before compilation).
///
/// Moved from `cranelisp-frontend` to `cranelisp-types` per FIXME 0156
/// resolution — `int`'s post-`build_form` consumption path needs to name
/// the type uniformly. The frontend retains the parsing functions
/// (`parse_defmacro`, `synthesize_macro_clause_defn`) which now read/write
/// this canonical shape.
///
/// Carries `body_sexp` per clause because the frontend's
/// `synthesize_macro_clause_defn` consumes it after parsing to produce the
/// per-clause `defn` Sexp. The canonical resolved-stage shape (after macro
/// codegen) is `Def { kind: DefKind::Macro { clauses_meta: Vec<MacroClauseInfo>,
/// sexp, source } }` parent + N `Def { kind: UserFn }` clause bodies under
/// `{macro-name}$clause-{N}` names — `MacroClauseInfo` carries no body because
/// each clause body lives as its own GOT-dispatched Def. See `design/arch/bounded-contexts.md` §7
/// §"DefKind" `DefKind::Macro` for the unified shape; the prior sibling
/// `ModuleEntry::Macro` variant retires in the S69 concurrency-cluster /dev brief.
#[non_exhaustive]
#[derive(Clone, Debug)]
pub struct DefmacroInfo {
    pub name: Symbol,
    pub is_private: bool,
    pub docstring: Option<String>,
    pub clauses: Vec<MacroClause>,
    pub span: Span,
}

impl DefmacroInfo {
    /// Construct a `DefmacroInfo` from its parts. Required by `#[non_exhaustive]`
    /// (cross-crate construction must go through a constructor).
    pub fn new(
        name: Symbol,
        is_private: bool,
        docstring: Option<String>,
        clauses: Vec<MacroClause>,
        span: Span,
    ) -> Self {
        Self {
            name,
            is_private,
            docstring,
            clauses,
            span,
        }
    }
}

/// A single parsed macro clause (params + body sexp). Parse-time only —
/// the body sexp is consumed by `synthesize_macro_clause_defn` to produce
/// the per-clause defn. Not persisted.
#[derive(Clone, Debug)]
pub struct MacroClause {
    pub fixed_params: Vec<MacroParam>,
    pub rest_param: Option<Symbol>,
    pub body_sexp: Sexp,
}
