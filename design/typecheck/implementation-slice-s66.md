# Sprint 66 implementation slice — `cranelisp-typecheck`

**Status.** draft
**Author.** /design (typecheck), 2026-05-06
**Reads.** `design/arch/facades/typecheck.md` (post-S65 W3 final-state target — note `check_form` signature is now `&SymbolTable<C, L>` per Decision 38 + FIXME 0008); `design/typecheck/typecheck.md` (master design); `design/arch/facades/types.md`; `design/arch/facades/frontend.md`; `design/arch/facades/int.md` §"`process_form` — the gap-orchestration retry loop"; `design/arch/fixmes/0098-*.md` (Phase 1 — types boundary set; Phase 3 — typecheck migrates `check_form` + adopts `CheckError`); `design/arch/fixmes/0008-*.md` (per-symbol mutability discipline); `design/arch/fixmes/0100-*.md` (Phase 1 — relocate single-consumer types out of `cranelisp-types` into typecheck); `design/arch/decisions/{0038,0039,0041}.md`; `audits/typecheck-20260423.md` (six prioritised remediations); `sprints/SPRINT.md` Wave Phase 4 W4a; `design/arch/sprint-65-reshape-phase-2-review.md §3` (slice template).

This slice enumerates the concrete delta between the post-S65 final-state `facades/typecheck.md` and the current `crates/cranelisp-typecheck/src/` source. It is consumed by `/sprint` as input to S66's wave plan; it is not itself a wave allocation.

The driving facts that define the slice's centre of gravity:

- The W3 facade revision shifted `check_form`'s `table` parameter from `&mut SymbolTable<Code, ()>` to `&SymbolTable<C, L>`. This is **non-trivial**: every internal mutation that today flows through a `&mut SymbolTable` (the `current_symbol_table_mut` ad-hoc guard pattern in `checker.rs`) must collapse onto `&self` per-entry inner-DashMap writes.
- FIXME 0098 Phase 3 simultaneously moves `check_form` from `TypeCheckEnv` method form to free-function form and switches the return type from `Result<FormCheckResult, CranelispError>` to `Result<CheckResult, CheckError>`.
- FIXME 0100 Phase 1 relocates `CheckResult`, `CheckError`, `ResolutionGap`, `FormCheckResult`, `CheckPass`, `CheckState`, `TypeCheckEnv`, `ModuleCheckAccumulator`, and `ReplSnapshot` out of `cranelisp-types` into `cranelisp-typecheck` per Principle 15. (`ResolutionGap` is the multi-consumer exception and stays in `cranelisp-types`.)
- The audit's six remediations are sequenced behind the migration: remediation #1 (consolidate duplicate `check_program*`/`check_repl_input*` paths in `program.rs`) is a load-bearing prerequisite for the free-function shape — until the duplicate paths are gone, the surviving path cannot collapse cleanly onto `check_form`.

---

## 1. Scope from facade — delta table

Action classes (same vocabulary as the frontend slice for cross-referencing):

- **rename** — symbol exists; signature/name changes
- **signature-change** — symbol exists with the right name but parameters/return type need adjustment
- **shape-pivot** — method form pivots to free-function form (the `check_form` headline)
- **mutability-pivot** — `&mut` parameter becomes `&` (Decision 38 / FIXME 0008)
- **new** — symbol does not yet exist; must be authored
- **migrate-in** — type or surface lives in `cranelisp-types` today and must move into `cranelisp-typecheck` (FIXME 0100 Phase 1)
- **delete** — symbol exists and must be removed
- **consolidate** — multiple parallel paths collapse to one
- **rustdoc** — pure documentation surface change
- **verify** — facade and source already align; cross-check confirms; no source change

| # | Facade item | Source location(s) | FIXME closed | Action | Acceptance |
|---|---|---|---|---|---|
| 1 | `pub fn check_form<C, L>(node: Ast, table: &SymbolTable<C, L>, symbol_tables: &SymbolTables<C, L>) -> Result<CheckResult, CheckError>` | `program.rs:527` (method `TypeCheckEnv::check_form(_module, form, pass, &mut state, &mut accumulator) -> Result<FormCheckResult, CranelispError>`); secondary `checker.rs:1830` | 0008, 0098 Phase 3 | shape-pivot + mutability-pivot + signature-change | Free function in `lib.rs` (or `program.rs`) takes `(Ast, &SymbolTable<C, L>, &SymbolTables<C, L>)` and returns `Result<CheckResult, CheckError>`; rolled-up two-pass + finalize internally; passes all existing per-form unit tests + new gap-return tests (§5) |
| 2 | `pub fn register_builtins<C, L>(table: &mut SymbolTable<C, L>)` taking ONE table | `builtins.rs:56` `register_builtins<C, L>(modules: &DashMap<ModuleFullPath, SymbolTable<C, L>>, next_id: &AtomicU32)` taking the whole map plus the type-var allocator | 0008 (paired pivot) | signature-change | Single-table input; allocator threaded internally (the function constructs its own AtomicU32 or accepts a `&CheckState`-bundled allocator if cleaner); idempotent on repeat calls; existing builtin-registration tests pass against the per-table shape |
| 3 | `CheckError` enum lives in `cranelisp-typecheck` (NOT `cranelisp-types`) | not yet present in either crate | 0098 Phase 1 + 0100 Phase 1 | new + migrate-in | Authored in a new `crates/cranelisp-typecheck/src/error.rs` (or co-located on `program.rs`); variants `Gap(ResolutionGap)`, `TypeError { message: String, location: ErrorLocation }`; `#[non_exhaustive]`; serde derives consistent with `cranelisp-types` convention; `pub use` from `lib.rs` |
| 4 | `ResolutionGap` STAYS in `cranelisp-types` (multi-consumer exception per Principle 15) | not yet present in `cranelisp-types` | 0098 Phase 1 | new (lives in types crate) | Phase 1 of 0098 lands the enum in `cranelisp-types`; this slice's contribution is verifying typecheck consumes it correctly via `pub use cranelisp_types::ResolutionGap` (single-line ergonomic re-export, parallel to frontend's row 10) and no parallel local variant grows |
| 5 | `ResolutionGap` rustdoc names which producer raises which variant | not yet present | 0098 Phase 1 + master-design §11 question 1 | rustdoc | Rustdoc on `SymbolTypechecked(FQSymbol)` — "produced by `cranelisp_typecheck::check_form`"; on `MacroInMem(FQSymbol)` — "produced exclusively by `cranelisp_frontend::expand`; never raised from typecheck"; on `Type(FQTypeName)` — "produced by `cranelisp_typecheck::check_form` for FQ type references". This is the documented disambiguation per the unified-enum option (b) from master-design §11 |
| 6 | `CheckResult` lives in `cranelisp-typecheck` | currently in `cranelisp-types` and re-exported from `cranelisp-typecheck::lib.rs:38` | 0100 Phase 1 | migrate-in | Move struct + impls; update `cranelisp-typecheck/src/lib.rs` `pub use` to point internally; update `int` callsites (handled by int slice) |
| 7 | `FormCheckResult`, `CheckPass`, `ModuleCheckAccumulator` live in `cranelisp-typecheck` | already here (`program.rs:231` `CheckPass`; `program.rs` various `FormCheckResult` etc.) — `pub use` from `lib.rs:32` | 0100 Phase 1 (verify-only) | verify | Confirm none of these accidentally referenced from `cranelisp-types`; no relocation source-side; remain `#[non_exhaustive]` |
| 8 | `CheckState`, `TypeCheckEnv` live in `cranelisp-typecheck` | already here (`checker.rs:52` `CheckState`; `checker.rs:134` `TypeCheckEnv<'a, C = (), L = ()>`) | 0100 Phase 1 (verify-only) | verify | Already aligned; ensure post-shape-pivot `TypeCheckEnv` becomes the thin internal wrapper described in master-design §3.2 item 4 (§5 below tracks the slim-down) |
| 9 | `ReplSnapshot` lives in `cranelisp-typecheck` | currently in `cranelisp-types` and re-exported from `cranelisp-typecheck::lib.rs:38` | 0100 Phase 1 | migrate-in | Move type + impls; `int` callsites updated by int slice |
| 10 | `TypeCheckEnv<'a, C, L>::new(table: &'a SymbolTable<C, L>, symbol_tables: &'a SymbolTables<C, L>) -> Self` | `checker.rs` `TypeCheckEnv::new(modules: &DashMap<…, SymbolTable<C, L>>, next_id: &AtomicU32)` plus assorted setter methods | 0008 | signature-change | Constructor takes a single owning `&SymbolTable` plus the cross-module `&SymbolTables`; type-var allocator becomes part of the per-call `CheckState` (already its natural home — `CheckState::new`); existing internal helpers that walk `modules` adapt to the single-table + `symbol_tables` split |
| 11 | `TypeCheckEnv` becomes a thin internal wrapper (master-design §3.2 item 4) — `#[non_exhaustive]`; not `int`'s production entry point | currently the de-facto entry point with ~30 helper methods; field defaults `<C = (), L = ()>` | (audit remediation #5 — `TypecheckIndexView`) | consolidate | Lookup helpers pulled behind `TypecheckIndexView` (audit remediation #5); the surviving public methods on `TypeCheckEnv` become the per-pass scaffolding called by `check_form`'s body (Pass-1 register + Pass-2 body + finalize); the `<C = (), L = ()>` defaults are pinned in the facade per master-design §11 question 3 (recommend confirming convention) |
| 12 | Free function `check_form` consumes `&SymbolTable` not `&mut SymbolTable` (mutation flows through inner-DashMap per-entry locks) | `current_symbol_table_mut` guards in `checker.rs`; some hold `RefMut` across non-trivial work | 0008 | mutability-pivot | All mutation paths in typecheck collapse to `SymbolTable::insert_or_update(&self, …)` or `install_import_bindings(&self, …)` per Decision 38; `&mut SymbolTable` removed from the typecheck crate's surface entirely (only `register_builtins` retains `&mut self` — row 2; `write_structural_decls` is an int-side concern not exposed here) |
| 13 | `CheckError::TypeError` carries `ErrorLocation`, NOT bare `Span` (Decision 39) | currently typecheck returns `CranelispError` with bare spans | 0098 Phase 3 + master-design §8 | signature-change + new | Producer policy per master-design §8.1: always populate `span` + `fq` (when known); leave `context` to formatter via `Introspection.source` lookup; `file` populated when caller passes via `TypeCheckEnv`; `line_col` left `None` typecheck-side |
| 14 | Audit remediation #1 — remove duplicate checking entry points | `program.rs:1786` `pub fn check_program` + sibling `check_repl_input*` paths (carry real registration / body / monomorphisation logic) | (audit Finding 1) | consolidate | One pipeline survives: `check_form` (per-form, public) + `check_inner` (the form-by-form driver used by tests via `check`/`check_program` shims). Deprecated `check_program` becomes a thin loop calling `check_form`; existing whole-program tests survive as shim-callers. **Prerequisite for row 1's clean shape.** |
| 15 | Audit remediation #2 — extract shared impl-method finalization | `traits.rs` `check_impl_method_with_sig` + `check_hkt_impl_method` share ~half their bodies (snapshot side maps → check body → resolve auto-curry → mangle → annotate → write `ModuleEntry::Def`) | (audit Finding 3) | consolidate | Shared finalization helper `finalize_impl_method(...)` extracted; type-resolution front halves stay separate; HKT path and non-HKT path both call the helper |
| 16 | Audit remediation #3 — shared `Expr` walker helpers | `apply_subst_to_expr`, `annotate_expr_from_maps`, `collect_constrained_calls`, `resolve_deferred_trait_calls` each re-walk all `Expr` variants independently | (audit Finding 2) | consolidate | One `walk_expr_children` (or visitor) helper carries the traversal; each existing function specialises only the per-node action; new `Expr` variants need touch ONE place to be carried, not five |
| 17 | Audit remediation #4 — `ModuleEntry::Def` builders | 132× manual `ModuleEntry::Def { … }` literal constructions across `builtins.rs`, `program.rs`, `traits.rs`, `infer.rs` | (audit Finding 4) | consolidate | Narrow constructors landed: `ModuleEntry::Def::primitive(...)`, `::user_placeholder(...)`, `::concrete(...)`, `::overloaded_placeholder(...)`, `::trait_method(...)`. Each call site collapses onto one builder; future `ModuleEntry::Def` field additions (e.g., `defn_order` per Decision 39) age all sites in one edit |
| 18 | Audit remediation #5 — `TypecheckIndexView` lookup facade | ~30 lookup helpers in `checker.rs` scan all loaded modules ad-hoc | (audit Finding 5) | consolidate | One `Index` view owns the scan-all-modules logic; specialised lookups read through it; per-call complexity unchanged (centralisation, not optimisation per Principle 6) |
| 19 | Audit remediation #6 — split heavyweight tests | `program.rs` 2,815 prod / 4,170 test; `infer.rs` 849 prod / 2,205 test; `checker.rs` 812 prod / 1,986 test | (audit Finding 6) | consolidate | Split tests into sibling `*_tests.rs` modules per file; sequenced LAST per the audit (after all other remediations) |
| 20 | `lib.rs` re-exports the post-relocation set per facade — drop the existing `pub use cranelisp_types::{CheckResult, CranelispError, ReplSnapshot, TopLevel}` block | `lib.rs:38` currently re-exports those four types from `cranelisp-types` | 0100 Phase 1 (per Principle 15) | delete + new | Remove the four-item block; add `pub use` for the relocated types from internal modules; `CranelispError` and `TopLevel` stay imported by callers from `cranelisp-types` directly (per FIXME 0100 §"Update int callsites") |
| 21 | Trace hooks (`install_symbol_table_ensure_hook`, …) re-exported from `trace.rs` | already aligned: `trace.rs:161`; `lib.rs:33` re-export | — | verify | Cross-check that the trace surface remains identical post-pivot; hook is registered by `int`'s observability layer at startup |
| 22 | `register_builtins` is idempotent (per facade §"Builtin registration") | currently uses `if !modules.contains_key(&primitives_path)` guards; structurally idempotent; not asserted by test | — | verify-then-test | Add narrow unit test asserting `register_builtins` called twice on a fresh table produces the same final state (no duplicate entries, no panics); harden the contract |
| 23 | Decision 38 (per-symbol mutability) embodied in source | partial — `current_symbol_table_mut` ad-hoc holds remain | 0008 (operational implication) | embodiment | After rows 1, 12 land: NO `&mut SymbolTable` lives anywhere in the typecheck crate's call graph except `register_builtins` (row 2) and the construction-time path in tests; per-form mutation is exclusively through inner-DashMap interior mutability |
| 24 | Decision 39 (per-defn source on `Introspection.source`; `defn_order: Vec<Symbol>` on `SymbolTable`; errors carry `ErrorLocation`) embodied in source | typecheck-side `ErrorLocation` portion not yet plumbed through error sites | 0098 Phase 3 + 0008 (paired) | embodiment | Every typecheck error site constructs `CheckError::TypeError { location: ErrorLocation { span, file, fq, line_col, context }, … }` per master-design §8.1 producer policy; `defn_order` field reads handled by `SymbolTable` layer (types crate concern); typecheck does not write `defn_order` directly |
| 25 | Decision 41 (`compile_to_module` per-symbol JIT; `Code` in `cranelisp-backend`) — peripheral to typecheck | n/a — typecheck does not reference `Code` | (peripheral) | verify | Confirm `register_builtins` and `check_form` work against `SymbolTable<C, L>` generic without naming `Code`; the facade's `SymbolTable<Code, ()>` mention in `register_builtins` is a documentation contract only (master-design §11 question 4); typecheck stays generic |
| 26 | Defer the three superseded subordinate docs (`check-form-api.md`, `dashmap-migration.md`, `stateless-tc-impl.md`) per master-design §10 | currently `Stale` per master-design §10 | (master-design §11 self-FIXME) | (out-of-band) | Once row 14 (audit remediation #1) lands, fold surviving algorithmic content from these three docs into `inference.md`/`traits.md`/`auto-curry.md` and archive. Carries forward to a subsequent sprint if not picked up in S66's typecheck wave; recorded here so `/design` (typecheck) does not lose track |
| 27 | Crate-local `crates/cranelisp-typecheck/CLAUDE.md` (audit-style implicit-contract surfacing — parallel to frontend slice row 18) | not present | (parallel to frontend audit MEDIUM-3) | new (out-of-band) | If `/dev` cycle has slack after the headline migration, author the crate-local CLAUDE.md surfacing pipeline contracts (per-form Pass-1/Pass-2 ordering, mutation discipline, gap-return contract); otherwise carries forward |

**Total rows: 27.** By action class:
- **verify**: 5 rows (4 Phase-1-prereq verify, 7, 8, 21, 25)
- **verify-then-test**: 1 row (22)
- **shape-pivot + mutability-pivot + signature-change** (compound): 1 row (1) — the headline change
- **signature-change** (standalone): 3 rows (2, 10, 13)
- **mutability-pivot** (standalone): 1 row (12)
- **migrate-in**: 2 rows (6, 9) + 1 paired with new (3)
- **new**: 1 row (3, paired) + 1 standalone-when-counting (5 rustdoc-as-new)
- **rustdoc**: 1 row (5)
- **delete + new**: 1 row (20)
- **consolidate**: 6 rows (11, 14, 15, 16, 17, 18, 19) — the audit's six remediations + the `TypeCheckEnv` slim-down
- **embodiment** (Decision integration verification): 2 rows (23, 24)
- **out-of-band**: 2 rows (26, 27) — carry-forward items

Single-action distribution (counting compound rows by primary verb): consolidate 7, verify 6, signature-change 4, migrate-in 3, new 2, mutability-pivot 1, shape-pivot 1, rustdoc 1, delete-and-new 1, embodiment 2, out-of-band 2.

---

## 2. Ordering within the slice

The slice has internal dependencies that bind the work order tightly. The audit's remediation #1 is a load-bearing prerequisite for the facade migration; FIXME 0098 Phase 1 is a hard external prerequisite (lives in the types slice).

1. **External prerequisite (NOT in this slice; lives in `cranelisp-types`)**: FIXME 0098 Phase 1 lands `ResolutionGap` in `cranelisp-types`. **This slice is blocked on the types slice for that one type.** (`CheckError`, `CheckResult`, `ReplSnapshot` move OUT of `cranelisp-types` per FIXME 0100 Phase 1 — the typecheck slice owns those moves and they happen alongside row 1's pivot.)

2. **Audit remediation #1 — consolidate duplicate checking entry points (row 14)**. **Prerequisite to row 1**. Until `check_program*` and `check_repl_input*` are gone (or shrunk to thin shims around `check_form`), the free-function pivot for `check_form` cannot land cleanly because three paths would need synchronised reshape. Land first.

3. **Audit remediations #2–#5 (rows 15–18)**. Independent of each other and of row 1; they reduce blast radius for the migration:
   - #2 (`finalize_impl_method` extraction) reduces the surface row 1's `&self` pivot must touch in `traits.rs`.
   - #3 (`walk_expr_children`) protects new `Expr` variants from drift during row 1's reshape.
   - #4 (`ModuleEntry::Def` builders) localises the per-entry write call sites — useful for row 12's mutability-pivot.
   - #5 (`TypecheckIndexView`) centralises cross-module reads — frontload before row 1 so the lookup helpers sitting under the `&SymbolTable`/`&SymbolTables` split land cleanly.

4. **Phase-1 type relocations + new types (rows 3, 5, 6, 9, 20)**. `CheckError` (new in typecheck), `ResolutionGap` rustdoc (in types — slice's contribution is the rustdoc text); `CheckResult` and `ReplSnapshot` migrate from `cranelisp-types` into typecheck; `lib.rs` re-export block surgery. Lands as one bundle — small, mechanical once the types crate is ready.

5. **Headline pivot — row 1 (`check_form` shape-pivot + mutability-pivot + signature-change)** + paired rows 2 (`register_builtins` signature-change), 10 (`TypeCheckEnv::new` signature-change), 12 (mutability-pivot), 13 (`ErrorLocation` plumbing). The bulk of `/dev`-narrow effort. Touches `program.rs`, `checker.rs`, `traits.rs`, `infer.rs`, `builtins.rs`. **Cannot land before steps 2–4.**

6. **Decision-embodiment verifications (rows 23, 24, 25)**. Cross-check pass after step 5: confirm no `&mut SymbolTable` survives the typecheck call graph (row 23); every error site uses `ErrorLocation` (row 24); typecheck stays `Code`-blind (row 25). Mostly grep-and-classify; ~half-day.

7. **`TypeCheckEnv` slim-down (row 11)**. Once `check_form` is the public entry, `TypeCheckEnv`'s job collapses — most of its ~30 lookup methods migrate behind `TypecheckIndexView` (row 18), the remaining surface becomes the per-pass scaffolding `check_form` uses internally. Sequenced AFTER step 5 so the post-pivot shape is clear; before step 8.

8. **Verify-class rows (4, 7, 8, 21, 22)**. No source changes; one cross-check pass during slice review confirming alignment. Row 22 adds one narrow idempotency test for `register_builtins`.

9. **Audit remediation #6 — split heavyweight tests (row 19)**. **Sequenced LAST per the audit's own ordering.** Touches `program.rs`/`infer.rs`/`checker.rs` test partition; mechanical; should not interleave with active mutation-discipline work because diff-noise would obscure the substantive pivot.

10. **Out-of-band (rows 26, 27)**. Optional — carries forward if not picked up in the S66 typecheck wave.

Steps 2 + 3 + 4 are parallelisable within `/dev`'s context budget (different files, different concerns). Step 5 is the centre of gravity and must serialise. Steps 6 + 7 + 8 are sequential after step 5 but small.

---

## 3. Estimated effort

**One-and-a-half S66 waves for `/dev` (typecheck), or two waves comfortably.** This is the largest single per-crate slice in the sprint by code volume (~20.4 KLOC production crate; 132 manual `ModuleEntry::Def` literals; 6,985-LOC `program.rs`).

Sizing breakdown:

- **Step 2 (audit remediation #1 — duplicate-pipeline consolidation, row 14)**: ~2–3 days. The duplicate `check_program*` / `check_repl_input*` paths in `program.rs` carry real logic (registration, body checking, monomorphisation, AST annotation). Identifying which path is canonical and collapsing the others to thin shims is non-trivial. Test surface large (~4,170 LOC of program.rs tests touch one or both paths).
- **Step 3 (audit remediations #2–#5, rows 15–18)**: ~3–4 days combined. #4 (132× `ModuleEntry::Def` builder migration) is mechanical-but-large; #5 (`TypecheckIndexView`) requires careful unification of ~30 ad-hoc lookups; #2 (impl-method tail) and #3 (`Expr` walker) are surgical. Parallelisable across two `/dev` cycles if context allows.
- **Step 4 (boundary-type relocation + rustdoc, rows 3, 5, 6, 9, 20)**: ~1 day. Mechanical move + import-rewrite + rustdoc-author pass. The rustdoc on `ResolutionGap` (row 5) is small and important — clarifies the multi-producer contract.
- **Step 5 (headline pivot, rows 1, 2, 10, 12, 13)**: ~3–4 days. The free-function shape lands first as a thin wrapper around the consolidated pipeline (post-step-2); then the mutability-pivot (row 12) adapts the internal call paths. `TypeCheckEnv::new` shape change (row 10) and `register_builtins` shape change (row 2) bundle. `ErrorLocation` plumbing (row 13) touches every error-construction site (~grep-able count: every `CranelispError::Type {...}` etc.).
- **Step 6 (Decision-embodiment cross-check, rows 23, 24, 25)**: ~half-day grep-and-classify.
- **Step 7 (`TypeCheckEnv` slim-down, row 11)**: ~1 day post-pivot — mostly moving methods between files now that the public entry is `check_form`.
- **Step 8 (verify-class + idempotency test, rows 4, 7, 8, 21, 22)**: ~2 hours.
- **Step 9 (audit remediation #6 — test split, row 19)**: ~1 day mechanical, but worth its own commit window.
- **Steps 10 (out-of-band, rows 26, 27)**: optional, deferrable.

**Total: ~11–15 working days = 1.5–2 S66 waves.** Comparable in scale to S65 W3 + S65 W4 combined. The audit's six remediations alone are wave-sized; the FIXME 0098 / FIXME 0008 migration on top is a second wave.

**Wave-fissure recommendation**: if the wave envelope is tight, split at step 4/5. Steps 2, 3, 4 (audit remediations + Phase-1 type relocations) form a coherent first wave — quality/maintainability work that is independent of the migration's external shape. Steps 5–9 (the migration itself) form a coherent second wave landing the post-FIXME-0008 + post-FIXME-0098-Phase-3 contract. This is the natural fissure — pre-S66 the typecheck crate's *internal* shape changes; mid-S66 the *boundary contract* changes.

If the sprint envelope tolerates one wave only, the irreducible minimum is steps 2 + 4 + 5 (consolidate, relocate, pivot). Audit remediations #2–#6 (steps 3 + 9) defer to a follow-up sprint with same-sprint `/arch` FIXMEs documenting the deferral rationale (per S65 Hard Constraint #1's tolerance commitment).

---

## 4. Dependencies on other crates' slices

Bilateral dependency table — each row identifies the corresponding entry in the depended-on crate's slice.

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| Row 1 (`check_form` returns `Result<CheckResult, CheckError>`) — `CheckError::Gap` carries `ResolutionGap` | `ResolutionGap` enum landing in `cranelisp-types` | types slice (FIXME 0098 Phase 1): land `ResolutionGap` in `cranelisp-types` per `facades/types.md` lines 579–593 — variants `SymbolTypechecked(FQSymbol)`, `MacroInMem(FQSymbol)`, `Type(FQTypeName)`; `#[non_exhaustive]` |
| Row 1 (`check_form`'s `&SymbolTables<C, L>` parameter) — `SymbolTables` is generic over `CodeStore`/`LinkerStore` markers | `CodeStore` / `LinkerStore` marker traits exist in `cranelisp-types`; `SymbolTables` type alias home | frontend slice row 8: `SymbolTables` alias is owned by the frontend crate — typecheck imports `cranelisp_frontend::SymbolTables` rather than declaring locally; no parallel-store risk per Principle 7 |
| Row 1 (`check_form` writes via `SymbolTable::insert_or_update(&self, …)` and `install_import_bindings(&self, …)`) | Per-symbol `&self` mutation discipline lands on `SymbolTable` in `cranelisp-types` | types slice (FIXME 0008 paired): confirm `install_import_bindings` is `&self`, not `&mut self`; confirm `insert_or_update` exists with `&self`; confirm `defn_order: Vec<Symbol>` field present per Decision 39 |
| Row 2 (`register_builtins(&mut SymbolTable<C, L>)`) — single-table input | `SymbolTable<C, L>::new_with_params` constructor stable | types slice: verify `SymbolTable` constructor surface unchanged; this is the one `&mut SymbolTable` operation typecheck retains, lives on initiator thread per Decision 38 |
| Row 13 (`CheckError::TypeError` carries `ErrorLocation`) | `ErrorLocation` exists in `cranelisp-types` per Decision 39 | types slice: verify `ErrorLocation { span, file, fq, line_col, context }` shape per Decision 39; this is legacy-embodied (S64 substance) but worth the verify pass |
| Row 6 (`CheckResult` migrates from `cranelisp-types` into `cranelisp-typecheck`) | `int` rewrites `use cranelisp_types::CheckResult` → `use cranelisp_typecheck::CheckResult` callsites | int slice (FIXME 0100 Phase 1 mirror): rewrite import paths in `src/worker.rs`, `src/session_v4.rs`, etc. for `CheckResult`, `CheckError`, `ReplSnapshot` (CRanelispError + TopLevel stay in cranelisp-types) |
| Row 9 (`ReplSnapshot` migrates) | `int` rewrites `use cranelisp_types::ReplSnapshot` → `use cranelisp_typecheck::ReplSnapshot` callsites | int slice (FIXME 0100 Phase 1 mirror): import-rewrite |
| Row 1 (gap pattern-match on caller side) | `int::process_form` pattern-matches `CheckError::Gap(ResolutionGap)` and dispatches to `handle_gap` | int slice (FIXME 0098 Phase 4): wire pattern-match per `facades/int.md` §"`process_form` — the gap-orchestration retry loop"; the orchestrator ensures `fq.module` is registered, calls `wait_for_typecheck_symbol(fq)` (or `wait_for_typecheck_type(fqt)` for `Type` gaps), retries `check_form` |
| Row 1 (`check_form` writes intermediate state on `CheckState`; on `Err`, caller restores via `ReplSnapshot`) | `int` (or REPL eval driver) takes the snapshot before `check_form` and restores on `Err` | int slice: confirm `process_form`'s eval-rollback path uses `TypeCheckEnv::snapshot` / `restore` per master-design §7.4; documented contract, not a new mechanism |
| Row 11 (`TypeCheckEnv` becomes thin internal wrapper; `int` does NOT construct it directly) | `int` calls `check_form` exclusively in production; `TypeCheckEnv` constructor is test-only-ish | int slice: verify `int` does not name `TypeCheckEnv` in `src/worker.rs` (today it likely does not — `check_form` is the per-form path; this is a drift-prevention check) |
| Row 5 (`ResolutionGap` rustdoc names producer per variant) | `cranelisp_frontend::expand` is the sole producer of `ResolutionGap::MacroInMem` | frontend slice row 7: confirm `expand` is the sole producer of `MacroInMem`; rustdoc text on the variant cites both producers (typecheck for `SymbolTypechecked` + `Type`; frontend for `MacroInMem`) |

**Cross-crate count: 11 distinct dependency rows naming 3 other slices** — types slice (5 rows: ResolutionGap landing, SymbolTable mutation discipline, register_builtins constructor, ErrorLocation, CodeStore/LinkerStore markers), int slice (5 rows: import-path rewrites for migrated types, gap pattern-match wiring, snapshot/restore, TypeCheckEnv non-construction verify), frontend slice (1 row: SymbolTables alias home, plus the cross-reference on ResolutionGap producer rustdoc).

The dependency graph is **dense but acyclic**: typecheck depends on types (Phase 1 must land first) and on frontend (only for the `SymbolTables` alias); `int` depends on typecheck's row 1 and on the migrated types from rows 6, 9. No cycle; no triad-cycle hazard. Per Principle 3 (dependency flows toward stability), typecheck sits below frontend in the DAG (frontend produces the AST; typecheck consumes) and below `int` (int orchestrates; typecheck is invoked).

**Wave sequencing implication for `/sprint`**: the types slice must land before this slice begins. The frontend slice (esp. row 8 — `SymbolTables` alias) lands in parallel or before. The int slice's mirror entries (rows 6/9 import rewrites + gap pattern-match) land AFTER this slice's row 1 + rows 6/9.

---

## 5. Test surface impact

### Existing typecheck unit tests touched

Co-located tests at ~12 KLOC. The slice's source changes touch:

- **`program.rs` tests** (~4,170 LOC): adapt to the consolidated single-pipeline shape (row 14). Tests that named `check_program` directly survive as shim-callers; tests that drove `TypeCheckEnv::check_form` via the method form retarget to the free-function `check_form`. **Significant volume; mechanical.**
- **`checker.rs` tests** (~1,986 LOC): adapt to `TypeCheckEnv::new` signature change (row 10) — the constructor now takes `(&SymbolTable, &SymbolTables)` instead of `(&DashMap<…, SymbolTable>, &AtomicU32)`. **~30–40 test functions touched** per the audit's count of constructor sites. Mechanical once the new shape is in place; conceptually one-line per test (instantiate one `SymbolTable` rather than a `DashMap` of them).
- **`infer.rs` tests** (~2,205 LOC): may need adapting where they construct deferred-resolution state directly; `walk_expr_children` consolidation (row 16) shouldn't change observable behaviour. **Verify-during-port; expect minimal churn.**
- **`traits.rs` tests** (~tail volume): `check_impl_method_with_sig` / `check_hkt_impl_method` consolidation (row 15) routes through the shared finalizer; tests assert the same observable outputs. **Verify-during-port.**
- **`builtins.rs` tests**: adapt to `register_builtins` single-table shape (row 2). **Few touches; mechanical.**

### New unit tests authored inside the typecheck crate

Per the project test strategy (memory: unit tests with /dev), narrow tests authored inside `crates/cranelisp-typecheck/src/`:

- **`check_form` raises `CheckError::Gap(ResolutionGap::SymbolTypechecked(fq))` for unresolved FQ value reference** (acceptance for row 1 + invariant 8; addresses master-design §11 coverage gap). Stub `SymbolTables<(), ()>` with no entry for `m2/foo`; assert `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(FQSymbol { module: "m2", symbol: "foo" })))`. Negative companion: bare-name resolution does NOT raise Gap (the symbol resolves locally or surfaces as `TypeError`, never as Gap).
- **`check_form` raises `CheckError::Gap(ResolutionGap::Type(fqt))` for unresolved FQ type reference** (acceptance for row 1 / invariant 8). `(deftype X (Some [:m2/SomeType val]))` against a `SymbolTables` lacking `m2`'s table → Gap returned.
- **`check_form` does NOT raise `CheckError::Gap(ResolutionGap::MacroInMem(fq))`** (invariant per master-design §7.3 + facade comment). Negative coverage: ensure no code path inside `check_form` constructs the `MacroInMem` variant. This is a structural test (grep-able assertion via `compile_error!` or runtime panic in the variant constructor), not a behavioural one — the variant exists in the unified enum but typecheck never produces it.
- **`check_form` returns `CheckError::TypeError` (NOT Gap) for genuine type errors** (acceptance for row 13). `(+ 1 "two")` → `TypeError { location: ErrorLocation { span: <known>, fq: <known when defn>, … } }`. Confirms producer policy per master-design §8.1.
- **`register_builtins` is idempotent** (acceptance for row 22). Call twice on a fresh `SymbolTable`; assert no duplicate entries, no panics, no extra GOT-slot allocations.
- **`check_form` writes intermediate state via `&self`-only paths** (acceptance for row 12 / row 23). Construct a `TypeCheckEnv` with `&SymbolTable`; run `check_form`; assert post-call symbol-table reads return committed entries. Negative: assert no `&mut SymbolTable` borrow is held across any `check_form` call interior (compile-time check via the borrow checker — by definition of taking `&SymbolTable`, this is structurally true; the test confirms the surface).
- **`check_form` snapshot-restore round-trip preserves type-var-pool state** (acceptance for invariant 7). Take snapshot → run failing `check_form` → restore → assert next `check_form` allocates the same fresh type-var IDs as if the failure hadn't happened.

**~7 new unit tests authored inside the typecheck crate.**

E2E coverage of the gap-return + retry path through `int::process_form` is `/qa`'s domain in `tests/`; this slice files a FIXME against `/qa` if the S66 test plan slice doesn't enumerate an end-to-end test exercising the typecheck-Gap → orchestrator-retry path (per `feedback_repros_join_suite.md`). Master-design §11 already proposed a `target: /qa` FIXME for narrow `check_form` gap-return tests; that proposal collapses into this slice's row-1 acceptance criteria — the unit tests above ARE the narrow coverage, authored by `/dev` (typecheck) per the test strategy memory. The /qa FIXME is therefore for the e2e layer only.

### Existing e2e tests touched

The E2E suite in `tests/` exercises the binary; the migration is internal-shape, so e2e behaviour SHOULD be invariant. Any e2e test that depends on typecheck error shapes (`CranelispError` variants vs `CheckError` variants surfacing in formatted output) will need its assertion adjusted — formatted error output should remain stable, but if any test asserts on `CranelispError::Type {...}`-string-shape it shifts to `CheckError::TypeError {...}`-string-shape. **Sprint `/qa` slice owns this confirmation.**

---

## 6. Open questions

The facade and master-design are unambiguous on the migration's contract. The slice surfaces four narrow questions where authoring met an edge:

1. **Is `ResolutionGap` documented per-variant in its rustdoc, or split into producer-specific enums?** Master-design §11's first proposed `target: /arch` FIXME asks this. The slice's tentative interpretation (row 5) is the unified-enum-with-rustdoc option (b) per Principle 2 (narrow interfaces — fewer boundary types preferred). If `/arch` prefers split enums (`FrontendGap`, `TypecheckGap`), the slice's row 3 (`CheckError::Gap`) wraps `TypecheckGap` instead of `ResolutionGap`. **Pending `/arch` confirmation; if substantive, file as `design/arch/fixmes/0152-name.md` targeting `/arch`.**

2. **`CheckError::Gap` post-Gap state contract — does `check_form` write to the symbol table BEFORE raising Gap, or only AFTER all FQ resolutions succeed?** Master-design §11's second proposed `target: /arch` FIXME asks this. The slice's tentative implementation: `check_form` MAY write intermediate state on Gap (the caller restores via `ReplSnapshot`). If `/arch` prefers a "no observable side effects on Gap-return" contract, row 1's implementation must defer writes until after every FQ has resolved — non-trivial because writes happen incrementally during inference. **Pending `/arch` confirmation; high-impact on row-1 implementation shape; file as `0153-name.md` if substantive.**

3. **`TypeCheckEnv` generic parameter convention in facade.** Master-design §11's third proposed `target: /arch` FIXME. Facade names `TypeCheckEnv<'a>` (no `<C, L>`); current source uses `TypeCheckEnv<'a, C = (), L = ()>`. The slice's tentative interpretation (row 11): keep the `<C = (), L = ()>` defaults; the facade's `TypeCheckEnv<'a>` is shorthand for the default-instantiated form. Doc-clarity item; **not blocking row-1 work**. File `0154-name.md` only if `/arch` regards the convention as substantive.

4. **`register_builtins` facade signature: `&mut SymbolTable<Code, ()>` or `&mut SymbolTable<C, L>`?** Master-design §11's fourth proposed `target: /arch` FIXME. Facade's literal type is `Code, ()`; the implementation must stay `Code`-blind (typecheck has no `cranelisp-backend` dependency). The slice's tentative interpretation (row 2): the facade-pin to `Code` is a documentation contract for *how int instantiates the symbol-table* — typecheck the crate works against `<C, L>` generic. **Pending `/arch` confirmation that this reading is correct;** if substantive, file as `0155-name.md`. Same lens applies to row 1's `check_form` parameter.

If `/arch` regards any of these as substantive (i.e., not editorial), the slice files as sequential FIXMEs (`0152`–`0155`) targeting `/arch`. **Tentative count: 0–4 FIXMEs may be filed during S66 implementation depending on `/arch`'s read.** Per Principle 4 (uninvented answers), the slice does not unilaterally resolve — it surfaces.

---

## 7. Cross-references

- `design/arch/facades/typecheck.md` — public-API contract (this slice's target; W3-revised post-Decision-38 shape)
- `design/arch/facades/types.md` §"Errors and warnings" — `ResolutionGap` (Phase 1 prerequisite); §"Symbol table" — `SymbolTable<C, L>` consumed surface
- `design/arch/facades/frontend.md` row 8 — `SymbolTables<C, L>` alias home (consumed by typecheck)
- `design/arch/facades/int.md` §"`process_form` — the gap-orchestration retry loop" — orchestrator's mirror entries
- `design/typecheck/typecheck.md` — master design (this slice's contract layer); §2.1 drift register; §3 internal architecture; §6 mutation discipline; §11 open questions
- `design/arch/fixmes/0008-typecheck-symboltable-per-symbol-mutability.md` — operative target shape for `check_form`'s mutability discipline
- `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md` — multi-crate migration; this slice executes Phase 3
- `design/arch/fixmes/0100-dev-relocate-single-consumer-types-to-originating-crates.md` — Phase 1: relocate `CheckResult`/`CheckError`/`ReplSnapshot` etc. into typecheck
- `design/arch/decisions/0038-*` — `SharedState` formal definition + per-symbol mutability
- `design/arch/decisions/0039-*` — per-defn source on `Introspection.source`; `defn_order: Vec<Symbol>`; errors carry `ErrorLocation`
- `design/arch/decisions/0041-*` — `Code` in `cranelisp-backend`; peripheral to typecheck (verify-only — row 25)
- `audits/typecheck-20260423.md` — current-state audit; six prioritised remediations (rows 14–19)
- `audits/typecheck-20260423-{current,target}-state.{mmd,svg}` — diagrams (note: target diagram predates Decisions 38/39 per master-design §3.2)
- `sprints/SPRINT.md` Wave Phase 4 W4a — slice-authoring wave
- `design/arch/sprint-65-reshape-phase-2-review.md §3` — slice template authority
- `design/frontend/implementation-slice-s66.md` — companion slice (frontend); cross-references with this slice on `SymbolTables` alias home and `ResolutionGap` producer rustdoc
- `crates/cranelisp-typecheck/src/{lib,program,checker,builtins,traits,infer,resolve,scheme,scope,unify,adt,trace}.rs` — current source under reshape
- `crates/cranelisp-types/src/` — Phase 1 prerequisite (FIXME 0098 `ResolutionGap` lands here) + Phase 1 source-of-types-relocating-out (FIXME 0100 `CheckResult`/`CheckError`/`ReplSnapshot` move out of here)
