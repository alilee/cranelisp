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
) -> Result<(StructuralDecls, Vec<Sexp>), CranelispError>;

pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>;

pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>;

pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>) -> Result<Sexp, ExpansionError>
where
    C: CodeStore,
    L: LinkerStore;
```

`extract_module_declarations` takes the containing module's path because BC §1 invariant 3 mandates `super` resolution at parse time — `ImportSpec.module_path` MUST never carry the literal `"super"` past the frontend boundary. Per spec §8.3.7, inside `a.b.c` the form `(import [super [...]])` resolves to `a.b`. The path is needed to do that rewrite.

`parse_import_sexp` is intentionally NOT in the public surface (per Principle 2 — narrow interfaces). Its only caller is `extract_module_declarations` internally; the REPL `/import` slash command parses through `extract_module_declarations` with a single-form input. The internal helper exists in the implementation but is `pub(crate)`.

`parse` produces a flat `Vec<Sexp>` — pure source-to-sexp lowering, no structural-decl harvesting. `extract_module_declarations` is the post-parse pass that walks the form vector once, peels off `(import …)` / `(export …)` / `(mod …)` / `(platform …)` declarations into a `StructuralDecls` bundle, and returns the residual non-structural form vector. The two-call shape lets parse stay reusable for non-orchestration consumers (REPL slash commands, comment-preserving variants — see `parse_preserving_comments` below) without forcing them to construct a structural-decl store they'll never use.

`build_form` and `build_expr` are per-form constructors — one entry for top-level forms in the wide vocabulary (returning a list of `ParsedEntry` transients per FIXME 0156 resolution), one for inner expressions (returning `Expr`). No union AST enum bridges them. Callers know which one they want at the call site (the worker calls `build_form` for top-level forms; the REPL eval path calls `build_expr` directly for bare-expression evals).

`build_form` accepts the full top-level form vocabulary (`defn`, `deftype`, `deftrait`, `impl`, `defmacro`, `mod`, `import`, `export`, `platform`) and returns `Vec<ParsedEntry>` because some shapes (notably `defmacro` with multiple clauses, and `deftype` whose constructors register independently) yield more than one entry per source form. Internally `build_form` dispatches to per-shape `pub(crate)` helpers (`parse_defn`, `parse_deftype`, `parse_deftrait`, `parse_impl`, `parse_defmacro`); the dispatcher is the single public entry. `import`/`export`/`mod`/`platform` continue to be peeled off by `extract_module_declarations` before `build_form` runs — they never reach `build_form`.

`ParsedEntry` is a **transient** parse-time-only carrier defined in `cranelisp-types` (see `facades/types.md` §"Boundary types" — the `ParsedEntry` family). It carries only what the parser knows; resolved-stage fields (type, scheme, callees, code, got_slot) are populated downstream by the two-pass typecheck surface (`check_form_signatures` + `check_form_body`, per Decision 44). **`ParsedEntry` NEVER lands in `SymbolTable`.** Lifecycle: `parse` → `ParsedEntry` (transient) → both typecheck passes consume → return `Vec<(Symbol, ModuleEntry<C>)>` per pass → orchestrator stages and `int::insert_cluster` writes to the live table atomically on cluster success. The `SymbolTable` invariant — "if it's in the live table, it's checked AND committed" — holds because the post-Gap state contract for both passes (FIXME 0160 + Decision 44) is structural: the orchestrator commits only on whole-cluster Ok.

`SymbolTables<C, L>` is the generic alias per Decision 32 — frontend stays C/L-blind so the same facade serves typecheck-only callers (`SymbolTables<(), ()>`) and integration-layer callers (`SymbolTables<Code, ()>`). The alias is structural; frontend does not depend on `int` to use it.

```rust
pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;
```

`StructuralDecls` is the bundle:

```rust
#[non_exhaustive]
pub struct StructuralDecls {
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<PlatformSpec>,
    pub submodules: Vec<ModDecl>,
}
```

Fed directly into `SymbolTable::write_structural_decls` per Decision 33 — single source of truth for structural decls on `SymbolTable`, no parallel `ModuleStructure` store.

`expand` invokes registered macros via JIT'd code addresses found through `symbol_tables`. The actual call into the macro happens through the GOT slot per Decision 23 — the frontend does not know about JITs; it only knows that when an FQ macro reference resolves to a `ModuleEntry::Macro` with `code: Some(_)`, it can dispatch.

Per Decision 43's reframing of Principle 15 (legacy Decision 8 retracted), there is **no `MacroResolver` trait** mediating macro lookup. `expand` looks up macros directly against the `&SymbolTables<C, L>` parameter — the dependency-inversion shape used in earlier rings is gone. Frontend's only collaborator for macro lookup is the symbol-tables map itself; the JIT'd code address sits on `ModuleEntry::Macro.code`, reached through the standard `&SymbolTable` access path. Migration of the still-in-`src/expander.rs` implementation into `cranelisp-frontend` is tracked under FIXME 0098 Phase 2.

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

### Synthetic span allocator (used by macro expansion to attribute generated forms)

```rust
pub fn next_synthetic_span() -> Span;
```

Allocates monotonically-increasing synthetic spans for forms produced by macro expansion. Reused across the session.

### Defmacro shape parsing — internal only

```rust
pub(crate) fn parse_defmacro(sexp: &Sexp) -> Result<DefmacroInfo, CranelispError>;

pub fn synthesize_macro_clause_defn(info: &DefmacroInfo, clause_idx: usize) -> Defn;
```

Per FIXME 0156 resolution — `parse_defmacro` is `pub(crate)` (called from `build_form`'s dispatcher when the form-shape is a `defmacro`). `DefmacroInfo` itself moves from `cranelisp-frontend` to `cranelisp-types` (see `facades/types.md` §"Boundary types") because `int`'s post-`build_form` consumption path needs to name the type, and `MacroClauseInfo` / `MacroParam` already live in `cranelisp-types`. The parser dispatcher returns `DefmacroInfo` packaged inside one or more `ParsedEntry::Macro` variants per the standard `build_form` shape.

`synthesize_macro_clause_defn` remains public — it builds a `Defn` (one per clause) for compilation. Each clause is compiled as a separate normal `Defn`, then registered in the `ModuleEntry::Macro` clauses list per Decision 21 cross-reference.

`MacroClauseInfo` and `MacroParam` live in `cranelisp-types` (they cross the typecheck boundary). `DefmacroInfo` joins them per FIXME 0156 resolution.

### `begin` / `quasiquote` helpers (called from `expand` and from `parse_defmacro`)

```rust
pub fn is_defmacro(sexp: &Sexp) -> bool;
pub fn is_begin(sexp: &Sexp) -> bool;
pub fn flatten_begin(sexp: Sexp) -> Vec<Sexp>;
pub fn expand_quasiquotes(sexp: Sexp) -> Result<Sexp, CranelispError>;
```

### Comment-preserving parse (REPL slash commands like `/source` need this)

```rust
pub fn parse_preserving_comments(source: &str) -> Result<Vec<Sexp>, CranelispError>;
```

### Public consts

None.

---

## Types originated here

Per Principle 15 — frontend's facade-originated types live here. None currently: `Sexp`, `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr`, `Ast`, `Program`, `ImportSpec`, `ExportSpec`, `ImportNames`, `MacroClauseInfo`, `MacroParam`, `ModDecl`, `PlatformSpec`, `ResolutionGap`, `ParsedEntry`, `DefmacroInfo` (per FIXME 0156 resolution) are all multi-consumer types (frontend produces; typecheck/backend/int consume) and live in `cranelisp-types`.

Frontend is a pure transform from source text to AST: its public surface is the free functions (`parse`, `extract_module_declarations`, `build_form`, `build_expr`, `expand`, `parse_preserving_comments`) plus `StructuralDecls` and `ExpansionError`. No re-exports of `cranelisp-types` items per Principle 15 — consumers import boundary types directly from `cranelisp_types::*`.

**`ResolutionGap` re-exported (narrow ergonomic exception per FIXME 0098).** `ExpansionError::Gap(ResolutionGap)` is the dominant variant of the public error enum, and consumers pattern-matching on it always need `ResolutionGap` in scope. The frontend re-exports `cranelisp_types::ResolutionGap` from its `lib.rs` so `use cranelisp_frontend::{expand, ExpansionError, ResolutionGap}` works in one import. This is an inline-justified instance of Principle 15's narrowness — limited to the gap-orchestration retry loop's pattern-match readability; not a general license.

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

- `StructuralDecls`
- `ExpansionError`

(Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade. `DefmacroInfo` and `ParsedEntry` live in `cranelisp-types` per FIXME 0156 resolution.)

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
