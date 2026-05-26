//! `cranelisp-frontend` — source text → S-expressions → AST, with macro
//! expansion as a frontend step.
//!
//! # Bounded context
//!
//! Source text becomes structured data. The frontend reads source bytes
//! into S-expressions, expands macros, and builds the AST. It is purely
//! structural: it does not know types, code, or semantics — only shape.
//! This narrows the contract the rest of the pipeline depends on: every
//! downstream stage consumes the same well-formed tree shape, regardless
//! of whether the input came from a file, the REPL, or another macro.
//! See `design/arch/bounded-contexts.md` §1 for the canonical statement
//! and §7 for the types crate (`SymbolTables`, `ModuleAliases`, multi-legged
//! authoring) that this crate consumes from.
//!
//! # Public surface — the form-by-form boundary
//!
//! Post-FIXME-0156 (Sprint 66 Wave 3a-β) the public boundary is **four
//! free functions** used by `int::process_cluster`. Per the architecture's
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
//! pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>;
//!
//! pub fn expand<C, L>(
//!     sexp: Sexp,
//!     symbol_tables: &SymbolTables<C, L>,
//!     module_aliases: &ModuleAliases,
//! ) -> Result<Sexp, ExpansionError>
//! where
//!     C: CodeStore,
//!     L: LinkerStore;
//! ```
//!
//! Macro expansion MUST run BEFORE `build_form` / `build_expr`. Unexpanded
//! macro calls reaching the AST builder become silent generic applications
//! and fail later with confusing diagnostics.
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
//! - [`build_expr`] is the per-form expression builder for bare REPL
//!   expression evals and the recursion target inside the per-shape
//!   parsers when lowering bodies.
//! - [`expand()`] performs Sexp-level macro expansion, returning a uniform
//!   [`ExpansionError::Gap`] for any macro-head it recognises but cannot
//!   currently invoke (see §"Expand and the FIXME 0175 invocation gap"
//!   below).
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
//! # Expand and the FIXME 0175 invocation gap
//!
//! [`expand()`] requires both `SymbolTables` and `ModuleAliases` because
//! spec §8.6.6 qualified-name resolution for a macro head
//! (`m.n.str/some-macro`) may need to traverse an import or export alias
//! on the way to the macro's defining module — the lookup is not just a
//! module-table get. The two tables are threaded as two parameters per
//! the narrow-interfaces principle (Principle 2).
//!
//! Per Decision 43's reframing of Principle 15 (legacy Decision 8
//! retracted), there is **no `MacroResolver` trait** mediating macro
//! lookup. `expand` looks up macros directly against the
//! `&SymbolTables<C, L>` parameter — the dependency-inversion shape used
//! in earlier rings is gone. Frontend's only collaborator for macro
//! lookup is the symbol-tables map itself; the JIT'd code address sits
//! on the matched clause's mangled-variant
//! `Def { kind: UserFn, code, got_slot, … }`, reached through the
//! standard `&SymbolTable` access path. The parent
//! `Def { kind: Macro, … }` entry holds metadata only (no own `code`);
//! per-clause bodies live one symbol-table-entry deeper, under the
//! `$clause-{N}` mangled names.
//!
//! **Status (FIXME 0175 — invocation is structurally deferred).** The
//! frontend [`expand()`] in `crates/cranelisp-frontend/src/expand.rs`
//! performs the structural traversal (children recursion, macro-head
//! detection, depth-limit enforcement, quasiquote expansion via
//! [`expand_quasiquotes`]) but does NOT call into the JIT'd macro body.
//! It returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))`
//! for every macro head encountered. The live invocation path remains
//! in `src/expander.rs` until `/arch` resolves FIXME 0175 (the
//! marshal-deps gap: `cranelisp_runtime::heap_alloc` + signal handling
//! cannot be reached from `cranelisp-frontend` under the current BC §1
//! dep-allowance, and the facade-target invocation requires them). When
//! `/arch` lands a resolution (likely option (a) — a new
//! `cranelisp-marshal` crate), `expand` gains the body call and the
//! `src/expander.rs` implementation deletes.
//!
//! ## Gap protocol — uniform single-variant
//!
//! When `expand` encounters an FQ symbol whose target isn't fully ready,
//! it CANNOT block or call the scheduler — frontend has no `Sess`
//! dependency (Principle 3). It surfaces the dependency uniformly via
//! `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` regardless
//! of whether the module is unregistered, typecheck is incomplete, or
//! code is missing. The orchestrator (`int::process_form`) translates
//! this into the right wait sequence and decides whether to wait for
//! code based on what the entry turns out to be:
//!
//! - `ensure_registered` + `wait_for_typecheck_symbol(fq)`. After
//!   typecheck completes, the orchestrator peeks at the entry:
//!     - If `entry.kind == DefKind::Macro` AND `entry.code.is_none()`
//!       → `priority_boost_jit(fq)` + `wait_for_inmem(fq)`.
//!     - Otherwise (it's a function, or it's a macro whose code is
//!       already loaded) → no further wait.
//! - Then retry `expand`. On the retry, expand sees the now-ready entry
//!   and either invokes the macro or leaves the form as a function call
//!   — no second gap.
//!
//! This is **one retry round-trip per FQ ref**, regardless of
//! macro-vs-fn — and the speculative `wait_for_inmem` is conditional,
//! never fired for functions. Expand stays uniform (one gap variant for
//! any FQ ref it can't fully resolve); the orchestrator owns the
//! macro-vs-fn discrimination because that decision depends on
//! scheduler-side knowledge.
//!
//! # Module layout
//!
//! The crate's public module structure mirrors its functional
//! decomposition:
//!
//! | Module | Contains | Root re-exports |
//! |---|---|---|
//! | [`reader`] | [`parse`], [`parse_preserving_comments`] — source-text to `Vec<Sexp>` lowering | yes |
//! | [`ast_builder`] | [`build_form`], [`build_expr`] — per-form AST construction | yes |
//! | [`module_extract`] | [`extract_module_declarations`], [`ExtractedDeclarations`] — structural-decl peeling | yes |
//! | [`defmacro`] | [`parse_defmacro`], [`is_defmacro`], [`is_begin`], [`flatten_begin`], [`synthesize_macro_clause_defn`] plus the [`DefmacroInfo`] / [`MacroClause`] re-exports from `cranelisp-types` | yes |
//! | [`quasiquote`] | [`expand_quasiquotes`], [`expand_quote_template`], [`next_synthetic_span`] | yes |
//! | [`mod@expand`] | [`expand()`], [`ExpansionError`], [`EXPANSION_DEPTH_LIMIT`] | yes |
//!
//! The qualified `module::` paths are the canonical homes; the crate-root
//! re-exports exist so the four-free-function boundary entry point reads
//! as `cranelisp_frontend::{parse, build_form, build_expr,
//! extract_module_declarations, expand}` in one import. The double-naming
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
//! The expander and the integration-layer cluster orchestrator share a
//! small family of shape-recognition + synthesis helpers used to drive
//! macro expansion + defmacro compilation:
//! [`parse_defmacro`], [`is_defmacro`], [`is_begin`], [`flatten_begin`],
//! [`synthesize_macro_clause_defn`] (in [`defmacro`]);
//! [`expand_quasiquotes`], [`expand_quote_template`],
//! [`next_synthetic_span`] (in [`quasiquote`]).
//!
//! These are pub at the crate root (and from `defmacro::` / `quasiquote::`
//! respectively). They are **internal-but-exposed** — not part of the
//! four-free-function form-by-form surface. Their consumers are the
//! in-tree `src/expander.rs` (until FIXME 0098 Phase 2 migrates the
//! invocation path) and `src/cluster.rs` (which builds clause `Defn`
//! instances for the backend per Decision 21).
//!
//! Disposition history. The Sprint 66 Wave 3a-β `build_form` shape pivot
//! opened these helpers to public visibility (a) so `src/expander.rs`
//! could continue to function while FIXME 0098 Phase 2 migrates the
//! JIT-invocation path into `cranelisp-frontend` (currently blocked on
//! FIXME 0175 — the marshal-deps gap), and (b) so
//! `src/cluster.rs::process_cluster` can build per-clause `Defn`s for
//! the backend per Decision 21 without rebuilding the shape-checking
//! logic outside the frontend. The expectation at FIXME 0098 Phase 2
//! close is that `parse_defmacro`, `is_defmacro`, `is_begin`,
//! `flatten_begin`, and `synthesize_macro_clause_defn` narrow back to
//! `pub(crate)` once `int` no longer calls them directly;
//! `expand_quote_template`, `expand_quasiquotes`, and
//! `next_synthetic_span` remain pub at root because they are the
//! standing public quasiquote API (used by user-authored macros at
//! expansion time and by REPL `/expand`).
//!
//! # Types originated here
//!
//! Per Principle 15 — frontend's facade-originated types live here. The
//! frontend originates exactly one type that is fully its own:
//! [`ExpansionError`]. [`ExtractedDeclarations`] is the second public DTO
//! published by the frontend, but it is structural sugar over
//! `cranelisp-types` items (every field is a `cranelisp-types` newtype
//! or spec record); its identity is "the bundle returned by
//! [`extract_module_declarations`]" rather than a domain concept.
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
//! directly from `cranelisp_types::*`. Three inline-justified exceptions
//! stand, each because the re-exported type is intrinsic to a frontend
//! public-surface signature and forcing two imports per call site is
//! friction with no compensating clarity:
//!
//! 1. **[`ResolutionGap`] re-exported (per FIXME 0098).**
//!    `ExpansionError::Gap(ResolutionGap)` is the dominant variant of
//!    the public error enum; consumers pattern-matching on it always
//!    need [`ResolutionGap`] in scope.
//!    `use cranelisp_frontend::{expand, ExpansionError, ResolutionGap}`
//!    works in one import.
//! 2. **[`DefmacroInfo`] re-exported (per FIXME 0156).**
//!    [`parse_defmacro`] returns `Result<DefmacroInfo, CranelispError>`;
//!    the macro-resolver-helper call sites in `src/cluster.rs` always
//!    need both names. The type lives in
//!    `cranelisp_types::parsed::DefmacroInfo`.
//! 3. **[`MacroClause`] re-exported (per FIXME 0156).**
//!    [`synthesize_macro_clause_defn`] takes a `&MacroClause` parameter;
//!    same one-import argument as [`DefmacroInfo`]. Lives in
//!    `cranelisp_types::parsed::MacroClause`.
//!
//! These three re-exports + the [`ExtractedDeclarations`] qualified/root
//! parallel form are the totality of frontend's re-export licence. New
//! re-exports require explicit `/arch` approval — adding "convenience"
//! re-exports erodes the dependency-graph clarity Principle 15 protects.
//!
//! `SymbolTables<C, L>` and `ModuleAliases` are **not** re-exported per
//! the S70 Phase B group α/β disposition — consumers import directly
//! from `cranelisp-types` (Principle 15 placement clarity; type aliases
//! lack the enum-variant-pattern-match justification of `ResolutionGap`).
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
//!   `TypeName`, `TraitName`, `ModuleName`, `FQSymbol`, `FQTypeName`,
//!   `CranelispError`, `Warning`, `SymbolTable`, `SymbolTables`,
//!   `ModuleAliases`, `ModuleAliasEntry`, `ModuleEntry`, `DefKind`,
//!   `ResolutionGap`.
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
//! [`ExtractedDeclarations`] and [`ExpansionError`]. Types re-exported
//! from `cranelisp-types` are `#[non_exhaustive]` per the types-crate
//! conventions. `DefmacroInfo`, `MacroClause`, and `ParsedEntry` live
//! in `cranelisp-types` per FIXME 0156 resolution.
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
//!    `Scheme`, or `TypeId`.
//! 2. **No code generation.** Macro bodies are AST nodes that `int`
//!    compiles via the backend; the frontend never invokes Cranelift
//!    and never names `cranelisp-backend`, `cranelisp-primitives`, or
//!    `cranelisp-intrinsics`.
//! 3. **`super` resolved at frontend.** Per
//!    `design/arch/super-import-arbitration.md`:
//!    `ImportSpec.module_path` NEVER contains the literal `"super"`
//!    past [`extract_module_declarations`]. All `super`-resolution
//!    happens at parse time against the parsing module's own path.
//! 4. **Synthetic spans are unique.** [`next_synthetic_span`] issues
//!    monotonically increasing spans for compiler-generated forms. No
//!    two synthetic spans collide within a session.
//! 5. **`expand` is re-entrant.** May invoke registered macros which
//!    may themselves expand further. The depth bound
//!    [`EXPANSION_DEPTH_LIMIT`] is an operational safeguard, not a
//!    contract.
//! 6. **`expand` is side-effect-free for dependency resolution.**
//!    When an FQ ref's target isn't ready, expand returns
//!    `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` — never
//!    calls the scheduler, never registers modules, never blocks. The
//!    frontend has no `Sess` / `CompileScheduler` dependency
//!    (Principle 3). The orchestrator (`int::process_form`) handles
//!    dispatch + retry.
//! 7. **`#[non_exhaustive]` DTOs include all error types.**
//!    [`ExpansionError`] is `#[non_exhaustive]` so adding new gap kinds
//!    or genuine error variants is non-breaking.
//! 8. **Form-by-form, not pre-pass.** Per FIXME
//!    `sprints/fixmes/0005-spec-macro-availability-form-by-form.md`:
//!    there is NO defmacro pre-pass extraction. Each form is processed
//!    in source order; macros become available to subsequent forms only
//!    after their `defmacro` form is itself processed.
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
//! - `design/arch/fixmes/0098-...migration.md` — ResolutionGap / CheckError / ExpansionError migration
//! - `design/arch/fixmes/0175-...invocation-gap.md` — marshal-deps gap on `expand` invocation path
//! - `design/frontend/wave-3a-build-form.md` — per-form boundary detailed design
//! - `crates/cranelisp-frontend/public-api.txt` — authoritative surface enumeration

pub mod reader;
pub mod ast_builder;
pub mod expand;
pub mod module_extract;
pub mod quasiquote;
pub mod defmacro;

use cranelisp_types::{CranelispError, Sexp};

// `build_form` and `build_expr` are mode-agnostic (see preamble §"Build is
// mode-agnostic"); they take no `CodegenBehaviour` parameter. The `(trace ...)`
// rejection in `--link` mode is the linker's natural missing-symbol
// detection, not a frontend pre-pass.
pub use ast_builder::{build_expr, build_form};
pub use expand::{expand, ExpansionError, EXPANSION_DEPTH_LIMIT};
// Re-export `ResolutionGap` for ergonomics — `ExpansionError::Gap` consumers
// always need `ResolutionGap` in scope. Per the preamble §"Re-export policy":
// narrow ergonomic exception to Principle 15.
//
// `SymbolTables` and `ModuleAliases` are NOT re-exported here per the
// S70 Phase B group α/β disposition — consumers import directly from
// `cranelisp-types` (Principle 15 placement clarity; type aliases lack the
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
