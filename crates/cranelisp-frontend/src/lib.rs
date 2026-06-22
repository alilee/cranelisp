//! `cranelisp-frontend` — source text → S-expressions → AST, with
//! quasiquote desugaring as the only syntactic-rewrite step.
//!
//! # Bounded context
//!
//! Source text becomes structured data. The frontend reads source bytes
//! into S-expressions, desugars quasiquotes, and builds the AST. It is
//! purely structural: it does not know types, code, or semantics — only
//! shape. Post-S76 (the W-Macro re-architecture) the frontend performs
//! **no macro recognition and no macro execution**: recognition is a
//! `cranelisp-types` query (`resolve_macro_head`) driven by typecheck +
//! int; execution is int's, behind `cranelisp_types::MacroExpander`.
//! The frontend's only remaining macro-adjacent role is quasiquote
//! desugaring, which is syntactic.
//! This narrows the contract the rest of the pipeline depends on: every
//! downstream stage consumes the same well-formed tree shape, regardless
//! of whether the input came from a file, the REPL, or another macro.
//! See `design/arch/bounded-contexts.md` §1 for the canonical statement
//! and §7 for the types crate (`SymbolTables`, `ModuleAliases`, multi-legged
//! authoring) that this crate consumes from.
//!
//! # Public surface — the form-by-form boundary
//!
//! Post-FIXME-0156 (Sprint 66 Wave 3a-β) the public boundary is a set of
//! free functions used by `int::process_cluster`. Per the architecture's
//! per-form discipline (no AST union enum): parse and structural extraction
//! are separate calls; AST building is per-form (one entry for `Defn`
//! shapes, one for `Expr`). The compilation worker invokes them once per
//! source form; REPL eval invokes them once per parsed input form.
//!
//! ```ignore
//! pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError>;
//!
//! pub fn extract_module_declarations(
//!     containing_module: &ModuleFullPath,
//!     sexps: &[Sexp],
//! ) -> Result<(ExtractedDeclarations, Vec<Sexp>), CranelispError>;
//!
//! pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>;
//!
//! pub fn build_forms(sexps: &[Sexp]) -> Result<Vec<TopLevel>, CranelispError>;
//!
//! pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>;
//!
//! pub fn parse_type_expr(source: &str) -> Result<TypeExpr, CranelispError>;
//! ```
//!
//! Quasiquote desugaring runs before `build_form`; macro expansion is
//! performed by int/typecheck before the expanded forms reach
//! `build_form`. Unexpanded macro calls reaching the AST builder become
//! silent generic applications and fail later with confusing diagnostics.
//!
//! ## Why the shape
//!
//! - `parse` produces a flat `Vec<Sexp>` — pure source-to-sexp lowering,
//!   no structural-decl harvesting. The reusable building block.
//! - [`extract_module_declarations`] is the post-parse pass that walks
//!   the form vector once, peels off `(import …)` / `(export …)` /
//!   `(mod …)` / `(platform …)` declarations into an
//!   [`ExtractedDeclarations`] bundle, and returns the residual
//!   non-structural form vector. The two-call shape lets `parse` stay
//!   reusable for non-orchestration consumers (REPL slash commands,
//!   comment-preserving variants — see [`parse_preserving_comments`])
//!   without forcing them to construct a structural-decl store they'll
//!   never use.
//! - [`build_form`] accepts the full top-level form vocabulary
//!   (`defn`, `deftype`, `deftrait`, `impl`, `defmacro`) and returns
//!   `Vec<ParsedEntry>` because some shapes (notably `defmacro` with
//!   multiple clauses, and `deftype` whose constructors register
//!   independently) yield more than one entry per source form.
//!   Internally `build_form` dispatches to per-shape `pub(crate)` helpers
//!   (`parse_defn`, `parse_deftype`, `parse_deftrait`, `parse_impl`,
//!   `parse_defmacro`); the dispatcher is the single public entry.
//!   `import`/`export`/`mod`/`platform` continue to be peeled off by
//!   [`extract_module_declarations`] before `build_form` runs — they
//!   never reach `build_form`.
//! - [`build_forms`] is the **form-sequence boundary** (S81, BC §1
//!   invariant 9): it lifts the `:Type`-binds-the-following-form pairing to
//!   the top-level form SEQUENCE. A leading `:Type` sexp pairs with the
//!   following form into an `Expr::Annotate` surfaced as a `TopLevel::Expr`;
//!   every other sexp is delegated per-form (top-level forms through
//!   [`build_form`], bare expressions through [`build_expr`]). The
//!   orchestrator (`int`) calls this instead of driving a per-sexp loop, so
//!   that top-level `:Type` pairing lives ENTIRELY in the frontend — the
//!   single owning seam. Macro / Constructor entries are dropped (handled by
//!   the macro pipeline + ADT-constructor synthesis), and a trailing `:Type`
//!   with nothing to bind is a parse error.
//! - [`build_expr`] is the per-form expression builder for bare REPL
//!   expression evals and the recursion target inside the per-shape
//!   parsers when lowering bodies. A bare `:Type` symbol in expression
//!   position is a parse error (`annotation missing expression`) — the
//!   `colon_prefix` token is an annotation introducer, never a `Var`
//!   (spec §1.4.5; §2.3.8).
//! - [`parse_type_expr`] parses a single type-expression form (string in,
//!   one `TypeExpr` out) for callers that have a type-signature string in
//!   hand (e.g. a DLL descriptor). It reuses the reader + the existing
//!   type-expression production in [`ast_builder`]; it returns the
//!   syntactic `TypeExpr`, never a resolved `Type` (resolution is
//!   typecheck's).
//!
//! ## Build is mode-agnostic
//!
//! `build_form` and `build_expr` take no `CodegenBehaviour` parameter.
//! `(trace ...)` in `--link` standalone-binary mode fails at link time
//! via the architecture's natural missing-symbol detection: backend emits
//! `cranelisp_collect_trace` as `Linkage::Import`, and the system linker
//! errors with "undefined symbol cranelisp_collect_trace" because the
//! trace runtime is not bundled into the staticlib produced by exe-bundle.
//! The earlier `link_mode::validate_*` pre-pass validator (Sprint 67
//! Wave 4) and its successor inline `build_trace` rejection were both
//! retired in the Sprint 67 Wave 4 follow-up subtraction — the
//! architecture rejects naturally, so no frontend pre-pass check is
//! needed. See `spec/04-expressions.md` §4.12.9.
//!
//! # Module layout
//!
//! The crate's public module structure mirrors its functional
//! decomposition:
//!
//! | Module | Contains | Root re-exports |
//! |---|---|---|
//! | [`reader`] | [`parse`], [`parse_preserving_comments`] — source-text to `Vec<Sexp>` lowering | yes |
//! | [`ast_builder`] | [`build_form`], [`build_forms`], [`build_expr`], [`parse_type_expr`] — per-form + form-sequence AST construction | yes |
//! | [`module_extract`] | [`extract_module_declarations`], [`ExtractedDeclarations`] — structural-decl peeling | yes |
//! | [`preamble`] | [`capture_module_preamble`] — leading comment-block module preamble (spec §8.16) | yes |
//! | [`defmacro`] | [`parse_defmacro`], [`is_defmacro`], [`is_begin`], [`flatten_begin`], [`synthesize_macro_clause_defn`] plus the [`DefmacroInfo`] / [`MacroClause`] re-exports from `cranelisp-types` | yes |
//! | [`quasiquote`] | [`expand_quasiquotes`], [`expand_quote_template`], [`next_synthetic_span`] | yes |
//!
//! The qualified `module::` paths are the canonical homes; the crate-root
//! re-exports exist so the boundary entry point reads as
//! `cranelisp_frontend::{parse, build_form, build_expr,
//! extract_module_declarations}` in one import. The double-naming
//! is **intentional surface duplication** — both
//! `cranelisp_frontend::ExtractedDeclarations` and
//! `cranelisp_frontend::module_extract::ExtractedDeclarations` are
//! pub-api lines. Tooling that audits public-API drift
//! (`cargo public-api`) reports both; the boundary endorses the
//! duplication for ergonomics.
//!
//! `SymbolTables<C, L>` and `ModuleAliases` aliases are consumed from
//! [`cranelisp_types`] (S69 cascade — types-crate is the canonical home);
//! the frontend does **not** re-export them (see "Re-export policy" below).
//!
//! # Macro-resolver helpers — internal-but-exposed
//!
//! The integration-layer cluster orchestrator consumes a small family of
//! shape-recognition + synthesis helpers used to drive defmacro
//! compilation:
//! [`parse_defmacro`], [`is_defmacro`], [`is_begin`], [`flatten_begin`],
//! [`synthesize_macro_clause_defn`] (in [`defmacro`]);
//! [`expand_quasiquotes`], [`expand_quote_template`],
//! [`next_synthetic_span`] (in [`quasiquote`]).
//!
//! These are pub at the crate root (and from `defmacro::` / `quasiquote::`
//! respectively). They are **internal-but-exposed** — not part of the
//! form-by-form surface. The defmacro-shape helpers are *syntactic shape
//! recognition + synthesis*, not recognition-of-a-macro-head against the
//! symbol table; `int::process_cluster` consumes them to build per-clause
//! `Defn`s (Decision 21). The quasiquote trio is the standing public
//! quasiquote API (used by user-authored macros at expansion time and by
//! REPL `/expand`). Post-S76 there is no in-crate macro-invocation path,
//! so there is no "narrow back to `pub(crate)` after invocation migrates"
//! framing — these helpers stand on their int consumers alone.
//!
//! # Types originated here
//!
//! Per Principle 15 — frontend's facade-originated types live here.
//! Post-S76 the frontend originates **zero** fully-own public types.
//! [`ExtractedDeclarations`] remains the one public DTO published by the
//! frontend, but it is structural sugar over `cranelisp-types` items
//! (every field is a `cranelisp-types` newtype or spec record); its
//! identity is "the bundle returned by [`extract_module_declarations`]"
//! rather than a domain concept.
//!
//! `Sexp`, `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr`,
//! `Program`, `ImportSpec`, `ExportSpec`, `ImportNames`,
//! `MacroClauseInfo`, `MacroParam`, `ModDecl`, `PlatformSpec`,
//! `ResolutionGap`, `ParsedEntry`, `DefmacroInfo`, `MacroClause` (per
//! FIXME 0156 resolution) are all multi-consumer types (frontend
//! produces; typecheck/backend/int consume) and live in `cranelisp-types`.
//!
//! # Re-export policy
//!
//! Per Principle 15 — narrow interfaces — frontend does NOT generally
//! re-export `cranelisp-types` items. Consumers import boundary types
//! directly from `cranelisp_types::*`. Two inline-justified exceptions
//! stand, each because the re-exported type is intrinsic to a frontend
//! public-surface signature and forcing two imports per call site is
//! friction with no compensating clarity:
//!
//! 1. **[`DefmacroInfo`] re-exported (per FIXME 0156).**
//!    [`parse_defmacro`] returns `Result<DefmacroInfo, CranelispError>`;
//!    the macro-resolver-helper call sites in `src/cluster.rs` always
//!    need both names. The type lives in
//!    `cranelisp_types::parsed::DefmacroInfo`.
//! 2. **[`MacroClause`] re-exported (per FIXME 0156).**
//!    [`synthesize_macro_clause_defn`] takes a `&MacroClause` parameter;
//!    same one-import argument as [`DefmacroInfo`]. Lives in
//!    `cranelisp_types::parsed::MacroClause`.
//!
//! These two re-exports + the [`ExtractedDeclarations`] qualified/root
//! parallel form are the totality of frontend's re-export licence. The
//! prior `ResolutionGap` re-export was retired at S76 (W-Macro): its
//! sole justification was `ExpansionError::Gap`, and `ExpansionError` is
//! gone — `ResolutionGap` now travels with `CheckError::Gap`, a
//! typecheck/types concern. New re-exports require explicit `/arch`
//! approval — adding "convenience" re-exports erodes the dependency-graph
//! clarity Principle 15 protects.
//!
//! `SymbolTables<C, L>` and `ModuleAliases` are **not** re-exported per
//! the S70 Phase B group α/β disposition — consumers import directly
//! from `cranelisp-types` (Principle 15 placement clarity; type aliases
//! lack the enum-variant-pattern-match justification the retired
//! `ResolutionGap` re-export once carried).
//!
//! # Consumed surface
//!
//! The frontend imports from:
//!
//! - **`cranelisp-types`** — `Sexp`, `Expr`, `TopLevel`, `Program`,
//!   `Defn`, `DefnVariant`, `Pattern`, `MatchArm`, `TypeExpr`, `Span`,
//!   `Visibility`, `ImportSpec`, `ExportSpec`, `NamedImport`,
//!   `NamedExport`, `ImportNames`, `PlatformSpec`, `ModDecl`,
//!   `MacroClauseInfo`, `MacroParam`, `ModuleFullPath`, `Symbol`,
//!   `TypeName`, `TraitName`, `ModuleName`, `FQTypeName`,
//!   `CranelispError`, `Warning`. (Post-S76: the symbol-table query
//!   surface — `SymbolTable`, `SymbolTables`, `ModuleAliases`,
//!   `ModuleEntry`, `DefKind`, `ResolutionGap`, `CodeStore`,
//!   `LinkerStore`, `FQSymbol` — was consumed only by the retired
//!   `expand` skeleton; the frontend no longer names them.)
//!
//! The frontend imports from no other workspace crate — not
//! `cranelisp-typecheck`, not `cranelisp-backend`, not
//! `cranelisp-primitives`, not `cranelisp-intrinsics`, not
//! `cranelisp-platform`. (Per Decision 43, `cranelisp-runtime` retired
//! into `cranelisp-primitives` + `cranelisp-intrinsics`; neither is a
//! frontend dependency.)
//!
//! # `#[non_exhaustive]` DTOs
//!
//! All public DTOs published by the frontend are `#[non_exhaustive]`:
//! [`ExtractedDeclarations`]. Types re-exported from `cranelisp-types`
//! are `#[non_exhaustive]` per the types-crate conventions.
//! `DefmacroInfo`, `MacroClause`, and `ParsedEntry` live in
//! `cranelisp-types` per FIXME 0156 resolution.
//!
//! # Sealed traits
//!
//! None implemented. The frontend does not implement traits from
//! `cranelisp-types`.
//!
//! # Bounded-context invariants
//!
//! These hold across sprints — the contract `cranelisp-frontend` makes
//! with the rest of the workspace:
//!
//! 1. **No type inference.** Types in the frontend are `TypeExpr`
//!    (syntactic), not `Type` (resolved). Type resolution is
//!    `cranelisp-typecheck`'s job. The frontend never names `Type`,
//!    `Scheme`, or `TypeId`. [`parse_type_expr`] returns the syntactic
//!    `TypeExpr`, never a resolved `Type`.
//! 2. **No code generation, no macro execution.** Macro bodies are AST
//!    nodes that `int` compiles via the backend; the frontend never
//!    invokes Cranelift and never names `cranelisp-backend`,
//!    `cranelisp-primitives`, or `cranelisp-intrinsics`. Post-S76
//!    W-Macro the frontend also performs no macro *recognition* or
//!    *execution* — it neither looks up macro entries nor calls JIT'd
//!    clause code. Recognition → typecheck (via the `cranelisp-types`
//!    `resolve_macro_head` primitive); execution → int (behind
//!    `cranelisp_types::MacroExpander`). That split is exactly what
//!    removed the former FIXME 0175 inconsistency — the frontend dep
//!    rule and the (former) `expand` contract no longer conflict
//!    because frontend no longer owns the conflicting capability.
//! 3. **`super` resolved at frontend.** Per
//!    `design/arch/super-import-arbitration.md`:
//!    `ImportSpec.module_path` NEVER contains the literal `"super"`
//!    past [`extract_module_declarations`]. All `super`-resolution
//!    happens at parse time against the parsing module's own path.
//! 4. **Synthetic spans are unique.** [`next_synthetic_span`] issues
//!    monotonically increasing spans for compiler-generated forms. No
//!    two synthetic spans collide within a session.
//! 5. *(Retired S76 W-Macro — the re-entrant-`expand` invariant moved
//!    to typecheck; the macro-expansion fixpoint + its depth bound are
//!    now typecheck's loop invariant. See `bounded-contexts.md` §2.)*
//! 6. *(Retired S76 W-Macro — the "`expand` surfaces `Gap` instead of
//!    blocking" invariant moved to typecheck, which surfaces the
//!    in-mem-macro need via `CheckError::Gap(ResolutionGap::MacroInMem)`
//!    and stays equally `Sess`/scheduler-free per Principle 3. See
//!    `bounded-contexts.md` §2.)*
//! 7. **`#[non_exhaustive]` DTOs.** Frontend's public DTO types remain
//!    `#[non_exhaustive]` so adding variants/fields is non-breaking.
//!    ([`ExtractedDeclarations`] is the one such DTO; `ExpansionError`
//!    retired with `expand` — the macro-execution error shape is now
//!    `cranelisp_types::MacroInvokeError`, also `#[non_exhaustive]`.)
//! 8. **Form-by-form, not pre-pass; defmacro-before-use.** There is NO
//!    defmacro pre-pass extraction. A macro must be defined before it is
//!    used, in source order (defmacro-before-use is normative —
//!    `design/arch/macro-availability-model.md` §0.2). The frontend
//!    itself does no macro recognition or expansion (those moved to
//!    typecheck + int); this invariant records the availability *model*
//!    the frontend's form-by-form output must be consistent with.
//!
//! # Deftype expander — ctor-as-Def synthesis
//!
//! The `(deftype ...)` expander produces, in addition to the `TypeDef`
//! `ModuleEntry`, **one synthesised `Defn` per constructor**. The Defn's
//! body expression is an `Expr::ConstrADT { type_name, tag, fields, span }`
//! node (see `crates/cranelisp-types/src/ast.rs` for the node shape and
//! `crates/cranelisp-types/src/module.rs` `DefKind::Constructor` rustdoc
//! plus `bounded-contexts.md` §7 "Multi-legged authoring" for the
//! ctor-as-Def shape and rejected alternatives). The resulting
//! `ModuleEntry::Def` carries
//! `kind: DefKind::Constructor { type_name, tag, field_count, internal }`
//! and a populated `got_slot`. The body's `Expr::ConstrADT` lowers
//! through standard backend codegen — no special path for constructors.
//!
//! `TypeDefInfo.constructors` is `Vec<Symbol>` (names only); per-constructor
//! metadata (tag, field count, type_name, internal) lives uniquely on each
//! ctor's `DefKind::Constructor`. Per-field names live on `Def.param_names`.
//! Per-field types fold into `Def.scheme`. No parallel storage of ctor
//! metadata.
//!
//! # See also
//!
//! - `design/arch/bounded-contexts.md` §1 — Frontend BC statement (canonical)
//! - `design/arch/bounded-contexts.md` §7 — Cross-crate types (the substrate)
//! - `design/arch/principles.md` — Principles 2, 13, 15, 17, 18
//! - `design/arch/macro-availability-model.md` §0 — defmacro-before-use; three-pass model (LOCKED)
//! - `design/arch/macro-expansion-ownership.md` — the W-Macro recognition→typecheck / execution→int split
//! - `design/frontend/s76-syntactic-only.md` — the S76 frontend target (W-Macro + `parse_type_expr`)
//! - `design/frontend/wave-3a-build-form.md` — per-form boundary detailed design
//! - `crates/cranelisp-frontend/public-api.txt` — authoritative surface enumeration

pub mod reader;
pub mod ast_builder;
pub mod module_extract;
pub mod preamble;
pub mod quasiquote;
pub mod defmacro;

use cranelisp_types::{CranelispError, Sexp};

// `build_form` and `build_expr` are mode-agnostic (see preamble §"Build is
// mode-agnostic"); they take no `CodegenBehaviour` parameter. The `(trace ...)`
// rejection in `--link` mode is the linker's natural missing-symbol
// detection, not a frontend pre-pass.
pub use ast_builder::{build_expr, build_form, build_forms, parse_type_expr};
// `SymbolTables`, `ModuleAliases`, and `ResolutionGap` are NOT re-exported
// here per the S70 Phase B group α/β disposition + the S76 W-Macro
// retirement — consumers import directly from `cranelisp-types` (Principle 15
// placement clarity). `ResolutionGap`'s sole prior re-export justification
// (`ExpansionError::Gap` consumers) evaporated with `ExpansionError`'s
// deletion; it now travels with `CheckError::Gap` (a typecheck/types concern).
pub use module_extract::extract_module_declarations;
pub use module_extract::ExtractedDeclarations;
// Module-preamble capture (spec §8.16) — pure `&str -> Option<String>` that
// reads the raw source head, orthogonal to structural-decl extraction. The int
// load seam calls this alongside `extract_module_declarations` to populate
// `SymbolTable.module_preamble` (wiring is int's, design §5).
pub use preamble::capture_module_preamble;
pub use quasiquote::{expand_quasiquotes, expand_quote_template, next_synthetic_span};
pub use defmacro::{
    is_defmacro, is_begin, flatten_begin, parse_defmacro,
    synthesize_macro_clause_defn, DefmacroInfo, MacroClause,
};

/// Parse source text into a sequence of S-expressions.
///
/// Produces a flat `Vec<Sexp>` — pure source-to-sexp lowering, no
/// structural-decl harvesting. The reusable building block: orchestration
/// consumers continue with [`extract_module_declarations`]; REPL slash
/// commands, comment-preserving variants, and test fixtures use the
/// flat result directly.
#[must_use = "parsing produces a result that should be checked for errors"]
pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError> {
    reader::parse(source)
}

/// Parse source text, preserving comments as `Sexp::Comment` nodes.
///
/// Used by REPL slash commands like `/source` that need to round-trip
/// the user's source text including comments.
#[must_use = "parsing produces a result that should be checked for errors"]
pub fn parse_preserving_comments(source: &str) -> Result<Vec<Sexp>, CranelispError> {
    reader::parse_preserving_comments(source)
}
