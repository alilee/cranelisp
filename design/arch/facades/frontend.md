# Facade spec — `crates/cranelisp-frontend/`

**Bounded context citation.** Source text → S-expressions → AST. Owns reading, parsing, and macro expansion as a frontend step. Does not type-check or codegen. See `bounded-contexts.md` §1 — Frontend.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free functions — the form-by-form surface (per §2.1 — parse + extract + per-form build, no AST union)

The frontend boundary is four free functions used by `int`'s shared `process_form` entry point (see `facades/int.md`). Per §2.1 — no `AST` enum/union; parse and structural-extraction are separate calls; AST building is per-form (one entry for `Defn`, one for `Expr`). The compilation worker invokes them once per source form; REPL eval invokes them once per parsed input form.

```rust
pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError>;

pub fn extract_module_declarations(forms: Vec<Sexp>)
    -> Result<(StructuralDecls, Vec<Sexp>), CranelispError>;

pub fn build_ast(defn_sexp: &Sexp) -> Result<Defn, CranelispError>;

pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>;

pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>) -> Result<Sexp, ExpansionError>
where
    C: CodeStore,
    L: LinkerStore;
```

`parse` produces a flat `Vec<Sexp>` — pure source-to-sexp lowering, no structural-decl harvesting. `extract_module_declarations` is the post-parse pass that walks the form vector once, peels off `(import …)` / `(export …)` / `(mod …)` / `(platform …)` declarations into a `StructuralDecls` bundle, and returns the residual non-structural form vector. The two-call shape lets parse stay reusable for non-orchestration consumers (REPL slash commands, comment-preserving variants — see `parse_preserving_comments` below) without forcing them to construct a structural-decl store they'll never use.

`build_ast` and `build_expr` are per-form constructors — one entry for top-level `defn` forms (returning the typed `Defn` shape), one for inner expressions (returning `Expr`). No union enum bridges them; a top-level form's body is just an `Expr`. Callers know which one they want at the call site (the worker calls `build_ast` for top-level forms; the REPL eval path calls `build_expr` directly for bare-expression evals).

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

### Sub-parsers for structural forms (called from `parse` internally; exposed for direct callers)

```rust
pub fn parse_import_sexp(sexp: &Sexp) -> Result<ImportSpec, CranelispError>;
pub fn parse_export_sexp(sexp: &Sexp) -> Result<ExportSpec, CranelispError>;
pub fn parse_mod_sexp(sexp: &Sexp) -> Result<ModDecl, CranelispError>;
pub fn parse_platform_sexp(sexp: &Sexp) -> Result<PlatformSpec, CranelispError>;
```

### Synthetic span allocator (used by macro expansion to attribute generated forms)

```rust
pub fn next_synthetic_span() -> Span;
```

Allocates monotonically-increasing synthetic spans for forms produced by macro expansion. Reused across the session.

### Defmacro shape parsing

```rust
pub fn parse_defmacro(sexp: &Sexp) -> Result<DefmacroInfo, CranelispError>;

#[non_exhaustive]
pub struct DefmacroInfo {
    pub name: Symbol,
    pub clauses: Vec<MacroClauseInfo>,
    pub visibility: Visibility,
    pub docstring: Option<String>,
    pub span: Span,
}

pub fn synthesize_macro_clause_defn(info: &DefmacroInfo, clause_idx: usize) -> Defn;
```

`DefmacroInfo` is a frontend-shaped construct (per-clause macro structure derived from a `defmacro` Sexp). Each clause is compiled as a separate normal `Defn` via `synthesize_macro_clause_defn`, then registered in the `ModuleEntry::Macro` clauses list per Decision 21 cross-reference.

`MacroClauseInfo` and `MacroParam` themselves live in `cranelisp-types` (they cross the typecheck boundary).

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

## Re-exports from `cranelisp-types`

The frontend re-exports its alias types for caller ergonomics:

```rust
pub use cranelisp_types::{Sexp, TopLevel};                              // Ast = TopLevel
pub type Ast = cranelisp_types::TopLevel;
```

No other re-exports. Consumers import boundary types directly from `cranelisp_types::*`.

---

## Consumed surface

The frontend imports from:

- **`cranelisp-types`** — `Sexp`, `Expr`, `TopLevel`, `Program`, `Defn`, `DefnVariant`, `Pattern`, `MatchArm`, `TypeExpr`, `Span`, `Visibility`, `ImportSpec`, `ExportSpec`, `NamedImport`, `NamedExport`, `ImportNames`, `PlatformSpec`, `ModDecl`, `MacroClauseInfo`, `MacroParam`, `ModuleFullPath`, `Symbol`, `TypeName`, `TraitName`, `ModuleName`, `FQSymbol`, `FQTypeName`, `CranelispError`, `Warning`, `SymbolTable`, `ModuleEntry`, `DefKind`, `ResolutionGap`.

- **`cranelisp` (binary)** — `SymbolTables` type alias (or equivalent), provided as input to `expand`. Frontend does not depend on `cranelisp` as a crate (would invert the DAG); the type is structural — `DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>` for any compatible `C`, `L`. The `expand` signature accepts a generic alias so the frontend remains downstream of types only.

The frontend imports from no other workspace crate — not `cranelisp-typecheck`, not `cranelisp-backend`, not `cranelisp-runtime`, not `cranelisp-platform`.

---

## Sealed traits

None implemented. The frontend does not implement traits from `cranelisp-types`.

---

## `#[non_exhaustive]` DTOs

All public DTOs published by the frontend are `#[non_exhaustive]`:

- `ParseProduct`
- `DefmacroInfo`
- `ExpansionError`

(Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade.)

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-frontend` makes with the rest of the workspace:

1. **No type inference.** Types in the frontend are `TypeExpr` (syntactic), not `Type` (resolved). Type resolution is `cranelisp-typecheck`'s job. The frontend never names `Type`, `Scheme`, or `TypeId`.
2. **No code generation.** Macro bodies are AST nodes that `int` compiles via the backend; the frontend never invokes Cranelift and never names `cranelisp-backend` or `cranelisp-runtime`.
3. **`super` resolved at frontend.** Per `super-import-arbitration.md`: `ImportSpec.module_path` NEVER contains the literal `"super"` past `parse` (specifically past `parse_import_sexp`). All `super`-resolution happens at parse time against the parsing module's own path.
4. **Synthetic spans are unique.** `next_synthetic_span` issues monotonically increasing spans for compiler-generated forms. No two synthetic spans collide within a session.
5. **`expand` is re-entrant.** May invoke registered macros which may themselves expand further. Termination is the macro author's responsibility (no recursion-depth limit imposed by the frontend).
6. **`expand` is side-effect-free for dependency resolution.** When an FQ ref's target isn't ready, expand returns `Err(ExpansionError::Gap(ResolutionGap::SymbolInMemory(fq)))` — never calls the scheduler, never registers modules, never blocks. The frontend has no `Sess` / `CompileScheduler` dependency (Principle 3). The orchestrator (`int::process_form`) handles dispatch + retry.
7. **`#[non_exhaustive] DTOs include all error types.** `ExpansionError` is `#[non_exhaustive]` so adding new gap kinds or genuine error variants is non-breaking.
6. **Form-by-form, not pre-pass.** Per FIXME `sprints/fixmes/0005-spec-macro-availability-form-by-form.md`: there is NO defmacro pre-pass extraction. Each form is processed in source order; macros become available to subsequent forms only after their `defmacro` form is itself processed. The "module-wide availability" model in `spec/09-macros.md §9.3.4` is to be revised — until then, the frontend does not implement it.
