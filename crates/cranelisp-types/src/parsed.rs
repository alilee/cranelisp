//! Parse-time-only transient types — produced by
//! `cranelisp_frontend::build_form` and consumed by
//! `cranelisp_typecheck::check_form`.
//!
//! `ParsedEntry` and `DefmacroInfo` are NOT persisted to the cache and
//! NEVER land in `SymbolTable`. The lifecycle is bounded by one orchestrator
//! iteration: `parse → ParsedEntry → check_form → checked Binding recipes →
//! SymbolTable funnels`. The SymbolTable invariant ("if it's in the table,
//! it's checked") is preserved.
//!
//! Per FIXME 0156 resolution (Sprint 66 Phase 3).

use crate::{
    ConstructorDef, DefnVariant, FieldDef, MacroParam, Sexp, Span, Symbol, TraitDecl, TraitImpl,
    TypeName, Visibility,
};

/// Parse-time-only transient. Carries only what the parser knows;
/// resolved-stage fields (type, scheme, callees, code, got_slot) are
/// populated by `check_form` downstream and end up on a checked [`crate::Binding`].
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
    ///
    /// **`type_params: Vec<Symbol>`** — type parameters are binders
    /// (introduce a fresh name into scope; parallel to value-level
    /// let-bindings). Per spec §5.2 EBNF: `type_var = symbol (* lowercase
    /// by convention *)` — type parameters are *symbols*, not type names.
    /// The newtype-discipline rule (`lib.rs` §"String Newtypes",
    /// `design/arch/CLAUDE.md §"String Newtypes"`) maps lowercase
    /// identifiers (locals, binders) to `Symbol` and uppercase identifiers
    /// (ADT / builtin / constructor names) to `TypeName`. Using `TypeName`
    /// here was a category error fixed in S70 Phase 3. Sibling sites
    /// already correct: `TopLevel::TypeDef.type_params: Vec<Symbol>`
    /// (`ast.rs`), `TraitDecl.type_params: Vec<Symbol>` (`ast.rs`),
    /// `TypeDefInfo.type_params: Vec<Symbol>` (`check.rs`). This narrow
    /// removes the prior marshalling churn at the `ast_builder` producer +
    /// `form` consumer that converted `Symbol ↔ TypeName` round-trip.
    TypeDef {
        name: TypeName,
        type_params: Vec<Symbol>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        docstring: Option<String>,
        span: Span,
    },
    /// Parsed `(deftrait Name … (method sig)*)` form.
    TraitDecl { decl: TraitDecl },
    /// Parsed `(impl Trait Type method-defns…)` form.
    TraitImpl { impl_: TraitImpl },
    /// Parsed `(defmacro name clauses…)` form. Downstream checking uses
    /// temporary local names to reuse the ordinary body checker, then publishes
    /// one `Decl::Macro` whose ordered clauses own those checked callable arms.
    /// The temporary names never enter the module symbol table or cache.
    Macro { info: DefmacroInfo },
    /// Synthetic per-constructor entry — emitted by `build_form` for each
    /// constructor of a `TypeDef`. Pre-typecheck shape; `check_form` lifts
    /// to a callable with `CallableOrigin::Ctor` metadata.
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
/// `synthesize_macro_clause_defn` consumes it after parsing to produce a
/// temporary per-clause `defn` Sexp. After checking, the canonical resolved
/// shape is one `Decl::Macro` with ordered `MacroClause` records, each owning
/// its executable `CallableArm`; only the authored macro name is a module
/// binding. See `design/arch/bounded-contexts.md` §7.
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
