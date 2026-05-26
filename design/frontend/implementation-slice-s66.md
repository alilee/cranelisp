# Sprint 66 implementation slice — `cranelisp-frontend`

**Status.** draft
**Author.** /design (frontend), 2026-05-06
**Reads.** `crates/cranelisp-frontend/src/lib.rs` //! preamble + `bounded-contexts.md` §1 (post-S65 final-state target; post-S70 B3-C the canonical home — `facades/frontend.md` retired); `design/frontend/frontend.md` (master design); `crates/cranelisp-types/src/lib.rs` //! preamble (`facades/types.md` retired S69 Sub 42); `design/arch/facades/intrinsics.md`; `design/arch/facades/int.md` §"`process_form` — the gap-orchestration retry loop"; `design/arch/fixmes/0098-*.md` (Phase 1 — types; Phase 2 — frontend); `design/arch/decisions/{0030,0032,0038,0039,0043}.md`; `sprints/SPRINT.md` Wave Phase 4 W4a; `sprint-65-reshape-phase-2-review.md` §3 (slice template).

This slice enumerates the concrete delta between the post-S65 final-state frontend surface contract (then captured in `facades/frontend.md`, retired in S70 Phase B group B3-C with content folded into `crates/cranelisp-frontend/src/lib.rs` //! preamble + `bounded-contexts.md` §1) and the current `crates/cranelisp-frontend/src/` source. It is consumed by `/sprint` as input to S66's wave plan; it is not itself a wave allocation.

---

## 1. Scope from facade — delta table

Each row names one facade item, its current state in source, the target state, and the action class. Action classes:

- **rename** — symbol exists; signature/name changes
- **signature-change** — symbol exists with the right name but parameters/return type need adjustment
- **new** — symbol does not yet exist in the frontend crate; must be authored
- **migrate-in** — symbol exists in another crate (`src/`) and must be moved into the frontend crate
- **delete** — symbol exists and must be removed
- **verify** — facade and source already align; an `/arch`-level cross-check confirms the alignment; no source change

| # | Facade item | Source location(s) | FIXME closed | Action | Acceptance |
|---|---|---|---|---|---|
| 1 | `pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError>` | `crates/cranelisp-frontend/src/lib.rs:33`; delegates to `reader::parse` | — | verify | Source matches facade exactly; unit test exercising `parse("(defn f [] 1)")` passes against the unchanged signature |
| 2 | `pub fn parse_preserving_comments(source) -> Result<Vec<Sexp>, _>` | `lib.rs:39`; delegates to `reader::parse_preserving_comments` | — | verify | Unchanged; covered by existing unit tests |
| 3 | `pub fn extract_module_declarations(containing_module: &ModuleFullPath, forms: Vec<Sexp>) -> Result<(StructuralDecls, Vec<Sexp>), CranelispError>` | `module_extract.rs:28`; current return type is `(ExtractedDeclarations, Vec<Sexp>)` and first param is owned `ModuleFullPath` (not `&`) | 0098 Phase 2 | signature-change + rename | Caller passes `&ModuleFullPath`; return tuple's first element is `StructuralDecls` (rename + `#[non_exhaustive]`); existing unit tests retargeted to the new tuple shape |
| 4 | `#[non_exhaustive] pub struct StructuralDecls { imports, exports, platforms, submodules }` | `module_extract.rs:14` defines `ExtractedDeclarations { path, mod_decls, import_specs, export_specs, platform_specs }` | 0098 Phase 2 | rename + field-rename | New name `StructuralDecls`; field renames per facade (`mod_decls` → `submodules`, `import_specs` → `imports`, `export_specs` → `exports`, `platform_specs` → `platforms`); `path` field dropped (caller already supplies `containing_module`); `#[non_exhaustive]` on the struct |
| 5 | `pub fn build_ast(defn_sexp: &Sexp) -> Result<Defn, CranelispError>` | not present; today the public surface is `build_program(&[Sexp]) -> Program` and `build_repl_input{,_from_sexps}` (whole-input shape) | 0098 Phase 2 (per-form alignment) | new | New per-form entry returning `Defn`; existing whole-input `build_program` becomes thin shared-classifier driver around `build_ast` (target-state §3.2 item 5); unit test asserting `build_ast` on a single `(defn f [] 1)` sexp returns the expected `Defn` shape |
| 6 | `pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>` | not present; expression lowering exists internally inside `ast_builder.rs` but is not on the public surface | 0098 Phase 2 | new | New per-form entry returning `Expr`; REPL bare-expression eval path (today via `build_repl_input`) calls this directly when it sees a non-defn form; unit test on `(+ 1 2)` returns expected `Expr::Apply` |
| 7 | `pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>) -> Result<Sexp, ExpansionError>` where `C: CodeStore, L: LinkerStore` | NOT in frontend crate; lives in `src/expander.rs` as `pub(crate) fn expand_sexp_recursive(sexp, resolver: &mut dyn MacroResolver, depth) -> Result<Sexp, CranelispError>` | 0098 Phase 2 (largest single gap) | migrate-in + signature-change | New `crates/cranelisp-frontend/src/expand.rs`; signature is generic over `<C: CodeStore, L: LinkerStore>`, takes `&SymbolTables<C, L>` (NO `&mut dyn MacroResolver`); returns `Result<Sexp, ExpansionError>`; depth limit retained as defensive guard surfaced as `ExpansionError::Malformed { message: "expansion depth exceeded", span }` (frontend §5.2 reconciliation); unit test asserting gap return when FQ macro entry not in tables |
| 8 | `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>` | not present; today defined informally in `src/`'s session types | 0098 Phase 2 | new | Type alias authored in `lib.rs` (or `expand.rs`); generic over `<C: CodeStore, L: LinkerStore>` per Decision 32; consumers use `cranelisp_frontend::SymbolTables` rather than re-declaring; `Cargo.toml` adds `dashmap` dep if not already present |
| 9 | `#[non_exhaustive] pub enum ExpansionError { Gap(ResolutionGap), Malformed { message, span }, MacroAborted { fq, message, span } }` | not present in any crate | 0098 Phase 2 | new | New error type lands with `expand`'s migration; `#[non_exhaustive]`; serde derives via type-crate convention (the variants reference `cranelisp-types` items only, so no serde gymnastics) |
| 10 | `pub use cranelisp_types::ResolutionGap` (narrow ergonomic re-export per Principle 15 inline exception) | not present | 0098 Phase 2 | new | Single-line re-export in `lib.rs`; rustdoc comment cites the inline justification (gap-orchestration retry loop pattern-match readability) |
| 11 | `pub fn next_synthetic_span() -> Span` | `quasiquote.rs` `SYNTHETIC_SPAN_COUNTER` (atomic, base 1_000_000); re-exported from `lib.rs:25` | — | verify | Atomic backing satisfies invariant 4; cross-thread uniqueness test stays |
| 12 | `pub fn parse_defmacro(sexp: &Sexp) -> Result<DefmacroInfo, CranelispError>` | `defmacro.rs`; re-exported from `lib.rs:26` | — | verify | Already aligned |
| 13 | `pub fn synthesize_macro_clause_defn(info: &DefmacroInfo, clause_idx: usize) -> Defn` | `defmacro.rs`; re-exported | — | verify | Already aligned |
| 14 | `#[non_exhaustive] pub struct DefmacroInfo` | `defmacro.rs` | — | verify-then-attribute | Confirm `#[non_exhaustive]` is on the struct (audit pass during slice review); add the attribute if missing |
| 15 | `is_defmacro` / `is_begin` / `flatten_begin` / `expand_quasiquotes` | `defmacro.rs` + `quasiquote.rs`; re-exported | — | verify | Already aligned |
| 16 | `parse_import_sexp` / `parse_export_sexp` / `parse_mod_sexp` / `parse_platform_sexp` are `pub(crate)` (internal only) | currently `pub` and re-exported from `lib.rs:23` | 0098 Phase 2 | signature-change + scope-restrict | Demote each to `pub(crate)`; remove from `lib.rs` re-exports; downstream callers (REPL `/import` if any) route through `extract_module_declarations` with single-form input; `parse_import_sexp` already takes `containing_module: &ModuleFullPath` (`module_extract.rs:381`) so no signature work — only scope demotion |
| 17 | Drop `MacroResolver` trait (Decision 8 retraction; D43 reframes Principle 15) | `src/expander.rs:49` `pub(crate) trait MacroResolver`; impls on `worker.rs::SymbolTableMacroResolver` and `session_v4.rs::ReadOnlyMacroResolver` | 0098 Phase 2 | delete (frontend-side n/a; `int`-side coordinated with int slice) | Trait file location allows deletion when `expand` is migrated; `int` slice removes the impls; this row is the frontend-side acknowledgement that the trait does not appear in the frontend's public surface (it never did — `pub(crate)` in `src/`) |
| 18 | Crate-local `crates/cranelisp-frontend/CLAUDE.md` (audit MEDIUM-3 — surface implicit pipeline contracts) | not present | (audit MEDIUM-3) | new (out-of-band) | Authoring this file is `/dev`-narrow per master-design §3.3; the slice records the dependency but does not author it. Carries forward to a subsequent sprint if not picked up in S66's frontend wave |

**Total rows: 18.** By action class:
- **verify**: 6 rows (1, 2, 11, 12, 13, 15)
- **verify-then-attribute**: 1 row (14)
- **signature-change**: 1 standalone (3) + paired with rename (4) + paired with scope-restrict (16) = **3 rows**
- **rename + field-rename**: 1 row (4)
- **new**: 5 rows (5, 6, 8, 9, 10) + 1 out-of-band (18)
- **migrate-in + signature-change**: 1 row (7)
- **delete**: 1 row (17, frontend-side acknowledgement only — actual deletion lives in int slice)

Single-action distribution (counting compound action by primary verb): verify 7, new 6, signature-change 3, migrate-in 1, rename 1 (compound with #3), delete 1.

---

## 2. Ordering within the slice

The slice has internal ordering driven by Phase 1 (types) being a prerequisite for Phase 2 (frontend). Within the frontend's own work, ordering is:

1. **Prerequisite (NOT in this slice; lives in `cranelisp-types`)**: Phase 1 of FIXME 0098 — `ResolutionGap` and `CheckError` enums land in `cranelisp-types`. Frontend's `ExpansionError` (row 9) carries `ResolutionGap` from types, so types must build cleanly first. **This slice is blocked on the types slice.**
2. **`SymbolTables` alias + `ExpansionError` enum (rows 8, 9, 10)** — small, foundational; lands first.
3. **`expand` migration (row 7)** — the largest single change. Authors the new file; ports `expand_sexp_recursive` body; adapts the `MacroResolver` callsites to `&SymbolTables<C, L>` lookup against `ModuleEntry::Macro` entries. Pairs with `int`'s removal of the `MacroResolver` trait + impls (`SymbolTableMacroResolver`, `ReadOnlyMacroResolver`). The `int` slice's mirror entry (FIXME 0098 Phase 4) calls the new `cranelisp_frontend::expand` and pattern-matches on `ExpansionError::Gap(ResolutionGap)`.
4. **`StructuralDecls` rename + `extract_module_declarations` signature-change (rows 3, 4, 16)** — `ExtractedDeclarations` → `StructuralDecls`, field renames, `path` field drop, sub-parsers demoted to `pub(crate)`. Self-contained inside the frontend crate. Touches every existing call site of `extract_module_declarations` in `src/` (caller-side adapts to the new tuple element name + new field shape) and inside frontend's own unit tests.
5. **Per-form `build_ast` / `build_expr` (rows 5, 6)** — extracts the existing internal lowering into public per-form entries. The existing `build_program` and `build_repl_input` become thin classifier wrappers calling `build_ast`/`build_expr` (target-state §3.2 item 5 — shared classifier).
6. **`#[non_exhaustive]` audit pass (row 14)** — single-attribute touch on `DefmacroInfo` if missing.
7. **Verify-class rows (1, 2, 11, 12, 13, 15)** — no source changes; one cross-check pass during slice review confirming alignment.
8. **Out-of-band `crates/cranelisp-frontend/CLAUDE.md` authoring (row 18)** — independent of the rest; carries to a later sprint if not picked up.

Items 4 and 5 are independent and may proceed in parallel within `/dev`'s context budget. Item 3 is the centre of gravity and gates the rest of the migration's external shape (callers in `int` adapt to the new `expand` only after row 7 lands).

---

## 3. Estimated effort

**One full S66 wave for `/dev` (frontend).** The migration is substance, not redesign:

- Row 7 (`expand` migrate-in + signature-change) is ~520 LOC of source-port + adapter work — the bulk of the slice's effort. Includes new `expand.rs`, depth-limit reconciliation as `ExpansionError::Malformed`, `MacroResolver`-trait-to-direct-`&SymbolTables`-lookup rewrite, gap-return paths.
- Rows 3 + 4 + 16 (`extract_module_declarations` reshape) is ~1 day of mechanical rename + caller-adapter work; touches every internal frontend test + every external caller in `src/` (worker, session_v4, REPL).
- Rows 5 + 6 (per-form `build_ast`/`build_expr`) is ~1 day of refactor — lift the existing top-level dispatch out of `build_program`/`build_repl_input` into shared classifier shape per target-state §3.2 item 5.
- Rows 8, 9, 10, 14 are small (<200 LOC total) and land alongside row 7.
- Verify-class rows (1, 2, 11, 12, 13, 15) consume one cross-check pass; ~30 minutes.

Sized as **one S66 wave-equivalent** — comparable to S65 W3 in scope. Pairs sequentially with the `int` slice (which consumes the new `expand` shape); decoupled from typecheck slice (frontend has no `cranelisp-typecheck` dependency per Principle 3).

If the wave envelope is tight, the `build_ast`/`build_expr` per-form split (rows 5, 6) is the natural fissure — defer to a follow-up sprint while keeping the migration of `expand` and `extract_module_declarations` shape in S66. The facade tolerates this only if the deferral is recorded as a same-sprint /arch FIXME with rationale (per S65 Hard Constraint #1's tolerance commitment).

---

## 4. Dependencies on other crates' slices

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| Row 7 (`expand` body referring to `ResolutionGap` carried inside `ExpansionError::Gap`) | `ResolutionGap` enum landing in `cranelisp-types` | types slice (Phase 1 of FIXME 0098): land `ResolutionGap` + `CheckError` in `cranelisp-types/src/check.rs` (or `error.rs`) per `facades/types.md` lines 579–593 |
| Row 7 (`expand`'s `&SymbolTables<C, L>` parameter; `SymbolTables` is generic over `CodeStore`/`LinkerStore` markers) | `CodeStore` / `LinkerStore` marker traits exist in `cranelisp-types` | types slice: verify `CodeStore`/`LinkerStore` already exist per Decision 32 (legacy — embodied) — likely a verify row, not new work |
| Row 7 (looking up `ModuleEntry::Macro.code` to dispatch) | `ModuleEntry::Macro` carries `code: Option<C>` and the `clauses` list with per-clause `func_ptr` | types slice: confirm `ModuleEntry::Macro` shape stable; `int` slice: confirm worker's per-clause-fn JIT pipeline still populates the `code` field used by `expand`'s lookup |
| Row 7 (deletion of `MacroResolver` trait + `SymbolTableMacroResolver` + `ReadOnlyMacroResolver` impls) | `int` removes the trait file and the two impls | int slice (FIXME 0098 Phase 4): delete `src/expander.rs::MacroResolver`; delete `worker.rs::SymbolTableMacroResolver`; delete `session_v4.rs::ReadOnlyMacroResolver`; rewire callers to `cranelisp_frontend::expand` |
| Row 7 (gap pattern-match on caller side) | `int::process_form` pattern-matches `ExpansionError::Gap(ResolutionGap)` and dispatches to `handle_gap` | int slice (FIXME 0098 Phase 4): wire pattern-match per `facades/int.md` §"`process_form` — the gap-orchestration retry loop" lines 662–671 |
| Rows 3, 4 (`StructuralDecls` rename + field renames) | `int::register_module` Phase 0 reads the new struct's fields and feeds `SymbolTable::write_structural_decls` | int slice: adapt `register_module` to new field names (`submodules`/`imports`/`exports`/`platforms`); confirm `SymbolTable::write_structural_decls` accepts the rename per Decision 33 |
| Row 8 (`SymbolTables` type alias home) | This alias is **owned by frontend**; typecheck and int both consume it. | typecheck slice + int slice: import `cranelisp_frontend::SymbolTables` rather than declaring locally; eliminates parallel-store risk |
| Row 9 (`ExpansionError`) | Only referenced internally by frontend; consumers pattern-match on it | int slice consumes via re-export from frontend; no other crate touches |

**Cross-crate count: 7 distinct dependency rows naming 3 other slices** — types slice (3 rows), int slice (4 rows including `SymbolTables` consumer + 3 deletion / pattern-match rows), and a transversal note for the typecheck slice (1 row — `SymbolTables` consumer). All bilateral: each row identifies the corresponding entry in the other crate's slice.

The dependency graph is **straightforward**: frontend depends on types only (Phase 1 must land first); `int` depends on frontend's row 7; typecheck consumes the `SymbolTables` alias frontend authors but is otherwise independent. No cycle; no triad-cycle hazard. Per Principle 3 (dependency flows toward stability), frontend stays at the top of the DAG.

---

## 5. Test surface impact

### Existing frontend unit tests touched

The 234 unit tests in `crates/cranelisp-frontend/src/` largely cover `parse`, `extract_module_declarations`, `build_program`, `build_repl_input{,_from_sexps}`, `expand_quasiquotes`, `parse_defmacro`. The slice's source changes touch:

- **`module_extract.rs` tests** (lines 478, 601, 616, 629, 753, 764, 774, 825 currently call `extract_module_declarations(...)` and destructure `ExtractedDeclarations`) — all test bodies adapt to the new tuple element name (`StructuralDecls`), the new field names, and the new `&ModuleFullPath` parameter passing convention. **~10 test functions touched.**
- **`ast_builder.rs` tests** — once `build_program`/`build_repl_input` become thin classifier wrappers around `build_ast`/`build_expr`, existing tests against the wrapper shape continue to pass (the wrapper is a façade over the new per-form entries). **No test bodies change** unless we want to add `build_ast`/`build_expr`-specific narrow tests, which we should (acceptance criteria for rows 5, 6).
- **`lib.rs` integration tests** — the public-API tests at the `cranelisp-frontend::*` level. Re-export changes (rows 8, 9, 10, 16) require `use` line updates. **Mechanical.**

### New unit tests authored

- **`expand` gap-return contract** (acceptance for row 7): stub `SymbolTables<(), ()>` with no `ModuleEntry::Macro` entry for an FQ ref `m/macro-name`; assert `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))`. This test is structural — does not require a running scheduler, JIT, or typechecker. Per master-design §7.6, this is the structural testability the migration unblocks.
- **`expand` re-entrancy** (invariant 5): assert that an expansion result containing a further macro call is itself expanded (single test exercising two-deep macro nesting against a stubbed `SymbolTables`).
- **`expand` depth-limit surfaces as `ExpansionError::Malformed`** (frontend §5.2 reconciliation): synthetic infinite-recursion macro stub asserts `Err(ExpansionError::Malformed { message, span })` after limit reached — NOT a `Gap` and NOT a silent truncation.
- **`build_ast` on `(defn f [] 1)` returns expected `Defn`** (acceptance for row 5).
- **`build_expr` on `(+ 1 2)` returns expected `Expr::Apply`** (acceptance for row 6).
- **`StructuralDecls` field-rename smoke**: parse a small module with `(mod ...)`, `(import ...)`, `(export ...)`, `(platform ...)` and assert each lands in the renamed field with no `ExtractedDeclarations` shape leakage. (This catches partial-rename oversights.)

**~6 new unit tests authored inside the frontend crate** per the project test strategy (memory: unit tests with /dev). E2E coverage of the `expand` migration is `/qa`'s domain in `tests/`; this slice files a FIXME against `/qa` if the S66 test plan slice doesn't enumerate an end-to-end test exercising the gap-return + retry path through `int::process_form` (per `feedback_repros_join_suite.md`).

### Existing e2e tests touched

The E2E suite in `tests/` exercises the binary; the migration is internal-shape, so e2e behaviour SHOULD be invariant. Any e2e test that depends on `MacroResolver`-trait-based scaffolding (none expected) breaks; otherwise the suite passes through. Sprint `/qa` slice owns this confirmation.

---

## 6. Open questions

The facade is unambiguous on the migration's shape. The slice surfaces three narrow questions where authoring met an edge:

1. **Is the depth-limit reconciliation acceptable as `ExpansionError::Malformed`, or should a dedicated `ExpansionError::DepthLimitExceeded` variant be added?** The facade lists three explicit variants (`Gap`, `Malformed`, `MacroAborted`) plus the `#[non_exhaustive]` ellipsis `/* … */`. Master-design §5.2 reconciles depth-limit-as-diagnostic via `MacroError`-like surface; the facade doesn't pin which existing variant absorbs it. Treating it as `Malformed` is cheapest; a dedicated variant is more honest. **Slice's tentative choice: `Malformed`.** If `/arch` prefers the dedicated variant, file as a same-sprint `/arch` revision. Not blocking S66 wave authoring; record the choice in the migration commit.
2. **Should `parse_import_sexp` etc. be deleted entirely from the public surface or kept as `pub(crate)` only?** Facade §"Sub-parsers for structural forms — internal only" says `pub(crate)`. Slice row 16 plans for `pub(crate)` demotion. If a hidden non-test caller in `src/` exists that the slice has not surfaced (REPL `/import` slash command is mentioned in facade as routing through `extract_module_declarations` but the actual call path needs verification at adoption time), the demotion may be blocked. **Tentative: demote per facade; if a caller surfaces, route it through `extract_module_declarations` with single-form input rather than re-exposing.**
3. **Does `build_ast` accept ONLY top-level `defn`/`deftype`/`deftrait`/`impl`/`mod`/`import`/`export`/`platform` shapes, or any "top-level form" including `defmacro`?** Facade §"Free functions" line says *"one entry for top-level `defn` forms (returning the typed `Defn` shape)"* — narrowly `defn`. But the existing `build_program` accepts the full top-level form vocabulary and dispatches internally. **Slice's tentative interpretation: `build_ast` is the per-form entry for any single top-level form returning a `Defn` value (per master-design §3.2 item 5 — single classifier with thin wrappers); the residual non-defn top-level forms (deftype, deftrait, impl, defmacro) go through their own narrow constructors or are absorbed into the classifier's downstream output shape.** This needs `/arch` confirmation before row 5 work proceeds. **Filed tentatively as a question, not a FIXME** — pending whether `/arch` regards this as already implicit in the "per-form, no AST union" framing or as a substantive interpretation that warrants facade tightening.

If `/arch` regards any of these as substantive (i.e., not editorial), the slice files as `design/arch/fixmes/0152-name.md` (or 0153, 0154 — sequential allocation) targeting `/arch`. **Tentative count: 0–3 FIXMEs may be filed during S66 implementation depending on `/arch`'s read.** Per Principle 4 (uninvented answers), the slice does not unilaterally resolve; surfaces the question.

---

## 7. Cross-references

- `crates/cranelisp-frontend/src/lib.rs` //! preamble + `bounded-contexts.md` §1 — public-API contract (this slice's target; post-S70 B3-C the `facades/frontend.md` document is retired and source rustdoc is canonical)
- `crates/cranelisp-types/src/error.rs` rustdoc — `ResolutionGap` + `CheckError` (Phase 1 prerequisite; `facades/types.md` is retired per S69 Sub 42)
- `design/arch/facades/int.md` §"`process_form` — the gap-orchestration retry loop" — orchestrator's mirror entries
- `design/arch/fixmes/0098-*` — multi-crate migration; this slice executes Phase 2
- `design/arch/decisions/0030-*`, `0032-*`, `0038-*`, `0039-*`, `0043-*` — frontend-relevant Decisions
- `design/frontend/frontend.md` §3.1 (file partition), §5 (macro expander architecture), §7.6 (testability) — master design
- `sprints/SPRINT.md` Wave Phase 4 W4a — slice-authoring wave
- `design/arch/sprint-65-reshape-phase-2-review.md` §3 — slice template authority
- `crates/cranelisp-frontend/src/{lib,reader,ast_builder,module_extract,quasiquote,defmacro}.rs` — current source under reshape
- `src/expander.rs` — current home of `expand_sexp_recursive`; migrates per row 7
