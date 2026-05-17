# Facade spec — `crates/cranelisp-frontend/`

**Bounded context citation.** Source text → S-expressions → AST. Owns reading, parsing, and macro expansion as a frontend step. Does not type-check or codegen. See `bounded-contexts.md` §1 — Frontend.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free functions — the form-by-form surface (per §2.1 — parse + extract + per-form build, no AST union)

The frontend boundary is four free functions used by `int`'s shared `process_form` entry point (see `facades/int.md`). Per §2.1 — no `AST` enum/union; parse and structural-extraction are separate calls; AST building is per-form (one entry for `Defn`, one for `Expr`). The compilation worker invokes them once per source form; REPL eval invokes them once per parsed input form.

```rust
pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError>;

pub fn extract_module_declarations(
    containing_module: &ModuleFullPath,
    forms: Vec<Sexp>,
) -> Result<(ExtractedDeclarations, Vec<Sexp>), CranelispError>;

pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>;

pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>;

pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>) -> Result<Sexp, ExpansionError>
where
    C: CodeStore,
    L: LinkerStore;
```

`extract_module_declarations` takes the containing module's path because BC §1 invariant 3 mandates `super` resolution at parse time — `ImportSpec.module_path` MUST never carry the literal `"super"` past the frontend boundary. Per spec §8.3.7, inside `a.b.c` the form `(import [super [...]])` resolves to `a.b`. The path is needed to do that rewrite.

`parse_import_sexp` is intentionally NOT in the public surface (per Principle 2 — narrow interfaces). Its only caller is `extract_module_declarations` internally; the REPL `/import` slash command parses through `extract_module_declarations` with a single-form input. The internal helper exists in the implementation but is `pub(crate)`.

`parse` produces a flat `Vec<Sexp>` — pure source-to-sexp lowering, no structural-decl harvesting. `extract_module_declarations` is the post-parse pass that walks the form vector once, peels off `(import …)` / `(export …)` / `(mod …)` / `(platform …)` declarations into an `ExtractedDeclarations` bundle, and returns the residual non-structural form vector. The two-call shape lets parse stay reusable for non-orchestration consumers (REPL slash commands, comment-preserving variants — see `parse_preserving_comments` below) without forcing them to construct a structural-decl store they'll never use.

`build_form` and `build_expr` are per-form constructors — one entry for top-level forms in the wide vocabulary (returning a list of `ParsedEntry` transients per FIXME 0156 resolution), one for inner expressions (returning `Expr`). No union AST enum bridges them. Callers know which one they want at the call site (the worker calls `build_form` for top-level forms; the REPL eval path calls `build_expr` directly for bare-expression evals).

`build_form` accepts the full top-level form vocabulary (`defn`, `deftype`, `deftrait`, `impl`, `defmacro`, `mod`, `import`, `export`, `platform`) and returns `Vec<ParsedEntry>` because some shapes (notably `defmacro` with multiple clauses, and `deftype` whose constructors register independently) yield more than one entry per source form. Internally `build_form` dispatches to per-shape `pub(crate)` helpers (`parse_defn`, `parse_deftype`, `parse_deftrait`, `parse_impl`, `parse_defmacro`); the dispatcher is the single public entry. `import`/`export`/`mod`/`platform` continue to be peeled off by `extract_module_declarations` before `build_form` runs — they never reach `build_form`.

`ParsedEntry` is a **transient** parse-time-only carrier defined in `cranelisp-types` (see `facades/types.md` §"Boundary types" — the `ParsedEntry` family). It carries only what the parser knows; resolved-stage fields (type, scheme, callees, code, got_slot) are populated downstream by the single-call typecheck surface `cranelisp_typecheck::check_forms` (per Decision 44's 2026-05-13 third amendment; the internal two-pass discipline lives inside `check_forms`'s frame). **`ParsedEntry` NEVER lands in `SymbolTable`.** Lifecycle: `parse` → `ParsedEntry` (transient) → orchestrator accumulates `Vec<ParsedEntry>` across the cluster → one `check_forms` call drives Pass 1 then Pass 2 internally, writing typed entries into orchestrator-handed staging → `int::insert_cluster` drains staging into the live table atomically on cluster success. The `SymbolTable` invariant — "if it's in the live table, it's checked AND committed" — holds because the post-Gap state contract (FIXME 0160 + Decision 44 third amendment) is structural: the orchestrator commits only on whole-cluster Ok and retries the whole `check_forms` call against a fresh staging frame on `Err(Gap)`.

`SymbolTables<C, L>` is the generic alias per Decision 32 — frontend stays C/L-blind so the same facade serves typecheck-only callers (`SymbolTables<(), ()>`) and integration-layer callers (`SymbolTables<Code, ()>`). The alias is structural; frontend does not depend on `int` to use it.

```rust
pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;
```

`ExtractedDeclarations` is the bundle (renamed from `StructuralDecls` in Sprint 67 W1 — the as-built name in `crates/cranelisp-frontend/src/module_extract.rs` is `ExtractedDeclarations`; the facade adopts the as-built name and retires the older `StructuralDecls` label):

```rust
#[non_exhaustive]
pub struct ExtractedDeclarations {
    pub path: ModuleFullPath,
    pub import_specs: Vec<ImportSpec>,
    pub export_specs: Vec<ExportSpec>,
    pub platform_specs: Vec<PlatformSpec>,
    pub mod_decls: Vec<ModDecl>,
}
```

The struct lives at `cranelisp_frontend::module_extract::ExtractedDeclarations` and is also re-exported at the crate root as `cranelisp_frontend::ExtractedDeclarations` for caller ergonomics (the integration-layer cluster orchestrator imports it from the root). Both names are public-surface; the qualified `module_extract::` form is the home-module canonical, the root re-export is the ergonomic alias. Per Principle 15's narrowness rule, this exception is justified because `ExtractedDeclarations` is the dominant return type of `extract_module_declarations` — itself one of the four free-function entries `int` calls per form — and callers always need both names in scope. Single-import readability is the same case as `ResolutionGap` (see below).

Fed directly into `SymbolTable::write_structural_decls` per Decision 33 — single source of truth for structural decls on `SymbolTable`, no parallel `ModuleStructure` store.

`expand` invokes registered macros via JIT'd code addresses found through `symbol_tables`. The actual call into the macro happens through the GOT slot per Decision 23 — the frontend does not know about JITs; it only knows that when an FQ macro reference resolves to a `ModuleEntry::Macro` with `code: Some(_)`, it can dispatch.

Per Decision 43's reframing of Principle 15 (legacy Decision 8 retracted), there is **no `MacroResolver` trait** mediating macro lookup. `expand` looks up macros directly against the `&SymbolTables<C, L>` parameter — the dependency-inversion shape used in earlier rings is gone. Frontend's only collaborator for macro lookup is the symbol-tables map itself; the JIT'd code address sits on `ModuleEntry::Macro.code`, reached through the standard `&SymbolTable` access path. Migration of the still-in-`src/expander.rs` implementation into `cranelisp-frontend` is tracked under FIXME 0098 Phase 2.

> **Status (S66 W3a-β → S67): invocation is structurally deferred per FIXME 0175.** The frontend `expand` in `crates/cranelisp-frontend/src/expand.rs` performs the structural traversal (children recursion, macro-head detection, depth-limit enforcement, quasiquote expansion via `expand_quasiquotes`) but does NOT call into the JIT'd macro body — it returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` for every macro head encountered. The real invocation path remains in `src/expander.rs` until `/arch` resolves FIXME 0175 (the marshal-deps gap: `cranelisp_runtime::heap_alloc` + signal handling cannot be reached from `cranelisp-frontend` under the current BC §1 dep-allowance, and the facade as written requires invocation). When `/arch` lands a resolution (likely option (a) — a new `cranelisp-marshal` crate), this paragraph drops and the in-tree implementation deletes. The signature and uniform-Gap contract above stand and need no revision.

When `expand` encounters an FQ symbol whose target isn't fully ready, it CANNOT block or call the scheduler — frontend has no `Sess` dependency (Principle 3). It surfaces the dependency uniformly via `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` regardless of whether the module is unregistered, typecheck is incomplete, or code is missing. The orchestrator (`int::process_form`) translates this into the right wait sequence and decides whether to wait for code based on what the entry turns out to be:

- `ensure_registered` + `wait_for_typecheck_symbol(fq)`. After typecheck completes, the orchestrator peeks at the entry:
  - If `entry.kind == DefKind::Macro` AND `entry.code.is_none()` → `priority_boost_jit(fq)` + `wait_for_inmem(fq)`.
  - Otherwise (it's a function, or it's a macro whose code is already loaded) → no further wait.
- Then retry `expand`. On the retry, expand sees the now-ready entry and either invokes the macro or leaves the form as a function call — no second gap.

This is **one retry round-trip per FQ ref**, regardless of macro-vs-fn — and the speculative `wait_for_inmem` is conditional, never fired for functions. Expand stays uniform (one gap variant for any FQ ref it can't fully resolve); the orchestrator owns the macro-vs-fn discrimination because that decision depends on scheduler-side knowledge (what the entry now contains after the typecheck wait).

```rust
#[non_exhaustive]
pub enum ExpansionError {
    /// Dependency-not-yet-ready signal — caller dispatches via int::process_form's handle_gap and retries.
    Gap(ResolutionGap),
    /// Genuine expansion failure — e.g. a macro body that can't be parsed back into a Sexp tree, or a malformed defmacro shape.
    Malformed { message: String, span: Span },
    /// A macro panicked or signalled an error during execution.
    MacroAborted { fq: FQSymbol, message: String, span: Span },
    /* … */
}
```

### Sub-parsers for structural forms — internal only

The per-form sub-parsers (`parse_import_sexp`, `parse_export_sexp`, `parse_mod_sexp`, `parse_platform_sexp`) exist in the implementation as `pub(crate)` helpers consumed by `extract_module_declarations`. They are intentionally NOT in the public surface. Direct callers (REPL `/import`, etc.) route through `extract_module_declarations` with a single-form input.

### Macro-resolver helpers — pub at root, internal-but-exposed

The expander and the integration-layer cluster orchestrator share a small family of shape-recognition + synthesis helpers used to drive macro expansion + defmacro compilation. These are pub at the crate root (and from `cranelisp_frontend::defmacro::` for the parsers, `cranelisp_frontend::quasiquote::` for the quasiquote pair). They are **internal-but-exposed** — facade documents them but they are not part of the four-free-function form-by-form surface. Their consumers are the in-tree `src/expander.rs` (until FIXME 0098 Phase 2 migrates the invocation path) and `src/cluster.rs` (which builds clause `Defn` instances for the backend per Decision 21).

```rust
// Defmacro shape parsing — pub at root and via `defmacro::`.
pub fn parse_defmacro(sexp: &Sexp) -> Result<DefmacroInfo, CranelispError>;
pub fn is_defmacro(sexp: &Sexp) -> bool;
pub fn synthesize_macro_clause_defn(
    name: &str,
    clause_idx: usize,
    clause: &MacroClause,
    span: Span,
) -> Sexp;

// `begin` flattening — pub at root and via `defmacro::`.
pub fn is_begin(sexp: &Sexp) -> bool;
pub fn flatten_begin(sexp: Sexp) -> Vec<Sexp>;

// Quasiquote expansion — pub at root and via `quasiquote::`.
pub fn expand_quasiquotes(sexp: &Sexp) -> Result<Sexp, CranelispError>;
pub fn expand_quote_template(template: &Sexp) -> Sexp;

// Synthetic span allocator — pub at root and via `quasiquote::`. Allocates
// monotonically-increasing synthetic spans for forms produced by macro
// expansion. Reused across the session — span uniqueness is a frontend
// invariant (see §"Bounded-context invariants" #4).
pub fn next_synthetic_span() -> Span;
```

Disposition history. The Sprint 66 Wave 3a-β `build_form` shape pivot opened these helpers to public visibility (a) so `src/expander.rs` could continue to function while FIXME 0098 Phase 2 migrates the JIT-invocation path into `cranelisp-frontend` (currently blocked on FIXME 0175 — the marshal-deps gap), and (b) so `src/cluster.rs::process_cluster` can build per-clause `Defn`s for the backend per Decision 21 without rebuilding the shape-checking logic outside the frontend. The expectation at FIXME 0098 Phase 2 close is that `parse_defmacro`, `is_defmacro`, `is_begin`, `flatten_begin`, and `synthesize_macro_clause_defn` narrow back to `pub(crate)` once `int` no longer calls them directly; `expand_quote_template`, `expand_quasiquotes`, and `next_synthetic_span` remain pub at root because they are the standing public quasiquote API (used by user-authored macros at expansion time and by REPL `/expand`). Until then, the public-surface inventory above is the binding facade statement.

`MacroClause`, `MacroClauseInfo`, `MacroParam`, and `DefmacroInfo` live in `cranelisp-types` (they cross the typecheck boundary). `DefmacroInfo` joined them per FIXME 0156 resolution. `synthesize_macro_clause_defn` takes a `&MacroClause` parameter — the type comes from `cranelisp_types::parsed::MacroClause`.

### Comment-preserving parse (REPL slash commands like `/source` need this)

```rust
pub fn parse_preserving_comments(source: &str) -> Result<Vec<Sexp>, CranelispError>;
```

### Public consts

```rust
pub const EXPANSION_DEPTH_LIMIT: usize;
```

Maximum recursion depth for nested macro expansion within a single `expand` call. The expander aborts with `ExpansionError::Malformed { message: "expansion depth limit exceeded", … }` rather than letting a pathological macro (mutual recursion, accidental fix-point) run the call stack out. The exact value is an implementation detail of `/dev`; the constant is published so test fixtures and the REPL `/expand` slash command can probe + report the limit without re-declaring it. Internal-but-exposed: the bounded-context invariant (BC #5 "`expand` is re-entrant") promises only that recursive expansion is supported; the depth bound is an operational safeguard, not a contract.

---

## Types originated here

Per Principle 15 — frontend's facade-originated types live here. The frontend originates exactly one type that is fully its own: `ExpansionError`. `ExtractedDeclarations` is the second public DTO published by the frontend, but it is structural sugar over `cranelisp-types` items (every field is a `cranelisp-types` newtype or spec record); its identity is "the bundle returned by `extract_module_declarations`" rather than a domain concept.

`Sexp`, `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr`, `Ast`, `Program`, `ImportSpec`, `ExportSpec`, `ImportNames`, `MacroClauseInfo`, `MacroParam`, `ModDecl`, `PlatformSpec`, `ResolutionGap`, `ParsedEntry`, `DefmacroInfo`, `MacroClause` (per FIXME 0156 resolution) are all multi-consumer types (frontend produces; typecheck/backend/int consume) and live in `cranelisp-types`.

Frontend is a pure transform from source text to AST: its public surface is the four free functions of the form-by-form boundary (`parse`, `extract_module_declarations`, `build_form`, `build_expr`) plus `expand`, `parse_preserving_comments`, the macro-resolver helpers (§"Macro-resolver helpers"), `EXPANSION_DEPTH_LIMIT`, and the DTOs `ExtractedDeclarations` + `ExpansionError`.

### Module layout

The crate's public module structure mirrors its functional decomposition:

| Module | Contains | Root re-exports |
|---|---|---|
| `cranelisp_frontend::reader` | `parse`, `parse_preserving_comments` — source-text to `Vec<Sexp>` lowering | yes (both fns re-exported at the crate root) |
| `cranelisp_frontend::ast_builder` | `build_form`, `build_expr` — per-form AST construction | yes (both fns re-exported at the crate root) |
| `cranelisp_frontend::module_extract` | `extract_module_declarations`, `ExtractedDeclarations` — structural-decl peeling | yes (both items re-exported at the crate root) |
| `cranelisp_frontend::defmacro` | `parse_defmacro`, `is_defmacro`, `is_begin`, `flatten_begin`, `synthesize_macro_clause_defn`, plus the `DefmacroInfo` and `MacroClause` re-exports from `cranelisp-types` | yes (fns and re-exports surfaced at the crate root) |
| `cranelisp_frontend::quasiquote` | `expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span` | yes (all three re-exported at the crate root) |
| `cranelisp_frontend::expand` | `expand`, `ExpansionError`, `EXPANSION_DEPTH_LIMIT`, `SymbolTables<C, L>` type alias | yes (`ExpansionError` re-exported at the crate root) |

The qualified `module::` paths are the canonical homes; the crate-root re-exports exist so the four-free-function boundary entry point reads as `cranelisp_frontend::{parse, build_form, build_expr, extract_module_declarations, expand}` in one import. The double-naming is **intentional surface duplication** — see `cranelisp_frontend::ExtractedDeclarations` vs `cranelisp_frontend::module_extract::ExtractedDeclarations`, both pub-api lines. Tooling that audits public-API drift (`cargo public-api`) will report both; the facade endorses the duplication for boundary ergonomics.

### Re-export policy

Per Principle 15 — narrow interfaces — frontend does NOT generally re-export `cranelisp-types` items. Consumers import boundary types directly from `cranelisp_types::*`. Three inline-justified exceptions stand, each because the re-exported type is intrinsic to a frontend public-surface signature and forcing two imports per call site is friction with no compensating clarity:

1. **`ResolutionGap` re-exported (per FIXME 0098).** `ExpansionError::Gap(ResolutionGap)` is the dominant variant of the public error enum; consumers pattern-matching on it always need `ResolutionGap` in scope. `use cranelisp_frontend::{expand, ExpansionError, ResolutionGap}` works in one import.

2. **`DefmacroInfo` re-exported (per FIXME 0156).** `parse_defmacro` returns `Result<DefmacroInfo, CranelispError>`; the macro-resolver-helper call sites in `src/cluster.rs` always need both names. The type itself lives in `cranelisp_types::parsed::DefmacroInfo` per /arch's W0 boundary-types work.

3. **`MacroClause` re-exported (per FIXME 0156).** `synthesize_macro_clause_defn` takes a `&MacroClause` parameter; same one-import argument as `DefmacroInfo`. The type lives in `cranelisp_types::parsed::MacroClause`.

These three re-exports + the `ExtractedDeclarations` qualified/root parallel form (see §"Free functions") are the totality of frontend's re-export licence. New re-exports require explicit `/arch` approval — adding "convenience" re-exports erodes the dependency-graph clarity Principle 15 protects.

(Optional ergonomic alias: `pub type Ast = cranelisp_types::TopLevel;` — a type alias, not a re-export, kept for readability at frontend call sites and consumer code.)

---

## Consumed surface

The frontend imports from:

- **`cranelisp-types`** — `Sexp`, `Expr`, `TopLevel`, `Program`, `Defn`, `DefnVariant`, `Pattern`, `MatchArm`, `TypeExpr`, `Span`, `Visibility`, `ImportSpec`, `ExportSpec`, `NamedImport`, `NamedExport`, `ImportNames`, `PlatformSpec`, `ModDecl`, `MacroClauseInfo`, `MacroParam`, `ModuleFullPath`, `Symbol`, `TypeName`, `TraitName`, `ModuleName`, `FQSymbol`, `FQTypeName`, `CranelispError`, `Warning`, `SymbolTable`, `ModuleEntry`, `DefKind`, `ResolutionGap`.

- **`cranelisp` (binary)** — `SymbolTables` type alias (or equivalent), provided as input to `expand`. Frontend does not depend on `cranelisp` as a crate (would invert the DAG); the type is structural — `DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>` for any compatible `C`, `L`. The `expand` signature accepts a generic alias so the frontend remains downstream of types only.

The frontend imports from no other workspace crate — not `cranelisp-typecheck`, not `cranelisp-backend`, not `cranelisp-primitives`, not `cranelisp-intrinsics`, not `cranelisp-platform`. (Per Decision 43, `cranelisp-runtime` retired into `cranelisp-primitives` + `cranelisp-intrinsics`; neither is a frontend dependency.)

---

## Sealed traits

None implemented. The frontend does not implement traits from `cranelisp-types`.

---

## `#[non_exhaustive]` DTOs

All public DTOs published by the frontend are `#[non_exhaustive]`:

- `ExtractedDeclarations`
- `ExpansionError`

(Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade. `DefmacroInfo`, `MacroClause`, and `ParsedEntry` live in `cranelisp-types` per FIXME 0156 resolution.)

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-frontend` makes with the rest of the workspace:

1. **No type inference.** Types in the frontend are `TypeExpr` (syntactic), not `Type` (resolved). Type resolution is `cranelisp-typecheck`'s job. The frontend never names `Type`, `Scheme`, or `TypeId`.
2. **No code generation.** Macro bodies are AST nodes that `int` compiles via the backend; the frontend never invokes Cranelift and never names `cranelisp-backend`, `cranelisp-primitives`, or `cranelisp-intrinsics`.
3. **`super` resolved at frontend.** Per `super-import-arbitration.md`: `ImportSpec.module_path` NEVER contains the literal `"super"` past `parse` (specifically past `parse_import_sexp`). All `super`-resolution happens at parse time against the parsing module's own path.
4. **Synthetic spans are unique.** `next_synthetic_span` issues monotonically increasing spans for compiler-generated forms. No two synthetic spans collide within a session.
5. **`expand` is re-entrant.** May invoke registered macros which may themselves expand further. Whether the implementation imposes a defensive depth limit (and what value) is `/dev`'s call — not a facade concern.
6. **`expand` is side-effect-free for dependency resolution.** When an FQ ref's target isn't ready, expand returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` — never calls the scheduler, never registers modules, never blocks. The frontend has no `Sess` / `CompileScheduler` dependency (Principle 3). The orchestrator (`int::process_form`) handles dispatch + retry.
7. **`#[non_exhaustive] DTOs include all error types.** `ExpansionError` is `#[non_exhaustive]` so adding new gap kinds or genuine error variants is non-breaking.
8. **Form-by-form, not pre-pass.** Per FIXME `sprints/fixmes/0005-spec-macro-availability-form-by-form.md`: there is NO defmacro pre-pass extraction. Each form is processed in source order; macros become available to subsequent forms only after their `defmacro` form is itself processed. The "module-wide availability" model in `spec/09-macros.md §9.3.4` is to be revised — until then, the frontend does not implement it.
