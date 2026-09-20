# `cranelisp-typecheck` — master design

Owner: `/design` (per-crate triad). Audience: triad agents working the typecheck surface, plus `/arch` for cross-crate coherence.

This document is the **single source of design intent** for the typecheck crate. The contract it designs against is:

1. `design/arch/bounded-contexts.md` §2 — Typecheck (the bounded context — what the crate is responsible for)
2. The crate's **public surface itself** — `crates/cranelisp-typecheck/public-api.txt` (the checked baseline) + the `pub` item rustdoc (`lib.rs` re-exports: `CheckState`, `TypeCheckEnv`, `PreludeFallback`, `check_forms`, `CheckResult`). *(The former `design/arch/facades/typecheck.md` facade was retired at S72 Wave 5 — all nine facades retired, `design/arch/CLAUDE.md` facades row; the canonical surface is now source rustdoc + BC §2, not a separate facade doc.)*
3. `design/arch/CLAUDE.md` Decisions 30, 41 (active) and 1, 2, 6, 8, 9, 14, 19, 21, 22, 33, 38, 39 (legacy — embodied) — cross-crate decisions binding typecheck. Note: Decisions 15 and 17 have been retracted (per `design/arch/CLAUDE.md` Decisions section); their constraints are embodied in current code (Ring 0-1 builtin/trait coexistence in the resolution machinery; core traits live in `.cl` files, not in `register_builtins`)

[Result-context specialization](result-context-specialization.md) describes the
implemented complete-substitution identity and replay contract approved on
2026-09-07. It governs generic instance collection, minting and recursion; the
[S122 executable-identity packet](../arch/s122-overload-reorder-publication.md)
now governs key derivation. Concrete realization names derive from the authored
owner and full concrete function signature through
`InstanceLink::instance_key(&template_scheme)`, and replay reconstructs result-only
choices without live expression maps.

The document describes **how the crate fulfils that contract** — its internal architecture, mutation discipline, error model, and quality posture — and pins the implementation gaps where current source has not yet caught up to the contract. Where this doc and a subordinate doc disagree, this doc wins; subordinate docs are scoped elaborations.

---

## 1. Bounded context — what we own

> "Untyped AST becomes typed AST plus populated symbol tables. Typecheck infers types, resolves traits, classifies polymorphism, and analyses match exhaustiveness. Its results land in two places: directly on AST nodes (each node carries its inferred type and resolution choices), and in the per-module symbol-table view supplied by the caller. The crate carries no shared session state and no cadence; it is invoked synchronously, one form at a time, by the integration layer."
> — `bounded-contexts.md` §2

The BC is the contract. Restated as crate responsibilities:

**In-scope** (the "what we do" surface):

- Hindley-Milner inference over every `Expr`, `Pattern`, and `MatchArm` variant the spec defines.
- Trait declaration / impl recording / method resolution — including HKT (constructor variables) and the constrained-polymorphism / monomorphisation analysis that follows from generalisation.
- ADT typing — constructor schemes, pattern exhaustiveness, type-parameter instantiation.
- Per-symbol callee extraction — the `CheckResult.callees: Vec<FQSymbol>` list that feeds Decision 21's TC-sourced call graph and lands on `ModuleEntry::Def.callees`.
- Gap-return signalling — surfacing FQ name / FQ type dependencies as values via `CheckError::Gap(ResolutionGap::…)` for the integration layer to dispatch, rather than blocking on the scheduler (Principle 3 — dependency flows toward stability; the typecheck crate sits below the scheduler).
- `register_builtins` — seeding a fresh per-module `SymbolTable` with the synthetic `primitives` / `macros` module contents per `spec/08-modules.md §8.7`. Idempotent.

**Out of scope** (other crates' concerns):

- AST construction, macro expansion (`/frontend`).
- Code emission, RC discipline, Cranelift IR (`/backend`).
- Pipeline scheduling, REPL session, module loading, watcher cadence (`/int`).
- Runtime helpers, IO trampoline, allocator (`/runtime`).
- Boundary types — they live in `cranelisp-types` and are `/arch`-owned.

**Cadence**: none. The crate has no internal scheduler, no background work, no shared session state. It is invoked synchronously, one form at a time, by the integration layer's per-form pipeline (`int::process_form`).

---

## 2. Public surface

The canonical surface is **source rustdoc + `crates/cranelisp-typecheck/public-api.txt` + BC §2** (all nine `design/arch/facades/` docs retired S69–S81; the directory holds only S69/S70 audit records — `design/arch/CLAUDE.md` facades row). This section restates the *as-built* surface (verified against `public-api.txt` + `lib.rs` re-exports, S115); the crate-root `//!` in `lib.rs` is the per-item authority.

The entry surface is **one free function per cluster** (Decision 44, third amendment 2026-05-13 — the two-pass `check_form_signatures`/`check_form_body` facade split collapsed into one `check_forms`):

- `check_forms<C, L>(parsed: Vec<ParsedEntry>, ctx: &mut SymbolTableAccess<'_, C, L>, symbol_tables: &SymbolTables<C, L>, module_aliases, prelude_fallback) -> Result<CheckResult, CheckError>` (`form.rs:96`) — the cluster-atomic check `int` uses in production. Internal two-pass discipline (register / body) + finalize are internal to this call frame.
- `check_type_expr<C, L>(...) -> Result<Type, CheckError>` (`form.rs:356`) — the standalone `TypeExpr → Type` resolution entry (source-annotation / platform-sig contexts).
- `signature_matches_exact` / `signature_matches_partial` (`signature_match.rs`) — the Pillar-3 importable-symbol search predicates (`signature-match.md`).
- Scaffolding exposed for tests + advanced callers: `CheckState`, `TypeCheckEnv`, `PreludeFallback`, `advance_next_id_past_table` (`checker.rs`); `SymbolTableAccess`, `SymbolTableRead`, `SymbolTableMut` (`cluster.rs` — the Decision-44 staging accessor).
- Result/error types, crate-owned (NOT re-exported from `cranelisp-types`): `CheckResult`, `CheckError` (`#[non_exhaustive]`, variants `Gap(ResolutionGap)` + `TypeError { message, location }`), `DispatchGap`, `UnresolvedDispatchSite` (`result.rs`).
- Trace-hook re-exports (`trace.rs`) — observability surface for `/int`'s scheduler tracing (`design/int/` heisenbug-race closure).

The BC §2 cross-context invariants 1–10 (`bounded-contexts.md`) are the sprint-spanning contract; the crate is designed to keep them (§6/§7). Baseline discipline: any `public-api.txt` diff rides its source change per `design/arch/CLAUDE.md` §"Baseline-diff discipline" (`/dev` regenerates, `/design` updates this record + `lib.rs` rustdoc, `/review` confirms both in one diff).

### 2.1 Migration status — the S63-era drift closed

The `check_form`-free-function migration (former FIXME 0008) and the boundary-type migration (former FIXME 0098) that this section's earlier drift register tracked **have landed**: `check_forms` is the free function (not a `TypeCheckEnv` method returning `FormCheckResult`); it takes `&mut SymbolTableAccess` (the Decision-44 staging choke point) + `&SymbolTables`, never `&mut SymbolTable`; and `CheckError`/`CheckResult`/`DispatchGap` are crate-owned types in `result.rs` (the crate no longer returns `CranelispError` at its boundary). Neither FIXME 0008 nor 0098 exists in `design/arch/fixmes/` (0008 migrated to the legacy Decision register, commit `d2849a5a`). The mutation contract §6 describes the landed shape, not a target.

---

## 3. Internal architecture

### 3.1 Module layout (as-built, S115 — verified `find | wc -l`)

The crate is decomposed into purpose-named submodule directories (the S87 `traits/` cut, the S109 `program/` cut per `program-decomposition.md`, the S100–S102 `ownership/` staging). LOC includes co-located tests where a file has no sibling `tests.rs`; production-only figures cited for the watch-items.

| Unit | Prod LOC (approx) | Role | Health |
|---|---:|---|---|
| `program/` (`mod`, `register` 1,357, `finalize` 1,517, `mono_collect` 834, `body` 738, `support` 607, `callees` 328, `test_driver`) | ~5.7k | The cluster pipeline: register (Pass 1), body (Pass 2), finalize (post-passes + mono windows), callee harvest, mono collection | `finalize.rs` is the growth magnet (§4.2) |
| `traits/` (`monomorphise` 1,298, `impl_check` 1,165, `dispatch` 531, `registry` 412, `type_resolve` 229, `mod`) | ~3.6k | Trait decls, impl recording, method resolution/dispatch, mono spine, HKT | Clean post-S87 decomposition |
| `ownership/` (`transfer` 1,137, `fixpoint` 644, `uniqueness` 362, `confinement` 254, `classify` 175, `sites` 106, `publish`, `trace`, `mod`) | ~2.8k | The S100+ interprocedural ownership-inference pass (`ownership-inference.md`) | Staged; largest 1,137 |
| `checker.rs` | 3,180 | `TypeCheckEnv` + `CheckState` + cross-module lookup helpers + scope-resolve seam | **Largest production file; growth watch-item** (audit s114 §2.1) |
| `builtins.rs` | 2,472 | Builtin / primitive registration (the no-`cranelisp-primitives` fixture world) | Deliberate — the isolation price |
| `infer.rs` (+ `infer/tests.rs`) | 1,808 | Algorithm-W per-`Expr`-variant inference + `infer_var` resolution chokepoint | One-method-per-variant, clean |
| `adt.rs` | 1,066 | ADT registration, exhaustiveness, accessor synthesis | Clean |
| `form.rs` | 537 | `check_forms` / `check_type_expr` entry surface | Clean |
| `resolve.rs` | 384 | `TypeExprCtx` + the ONE `resolve_type_expr` (S110 four-mirror convergence, `5ed07d60`) + overload helpers | Clean (0590 converged) |
| `signature_match.rs` | 315 | Pillar-3 exact/partial signature-match predicates | Clean |
| `unify.rs` | 286 | Algorithm-W unification + occurs check + FQ error renderer | Clean |
| `cluster.rs` | 241 | `SymbolTableAccess` staging (Decision 44) | Clean |
| `result.rs` | 166 | `CheckResult` / `CheckError` / `DispatchGap` (crate-owned boundary types) | Clean |
| `scope.rs` 135 · `trace.rs` 91 · `scheme.rs` 63 | — | Scope stack; trace-hook installer; `Scheme` generalise/instantiate | Clean |

Total ~51k across production + co-located tests; ~20.7k production LOC (audit s114 §2.3).

### 3.2 Growth watch-items (from the rolling audit cycle)

There is no separate "target-state diagram" roadmap — the 2026-04-23 audit's target-state (`audits/typecheck-20260423-target-state.{mmd,svg}`) and its six remediations are **retired**: the duplicate-pipelines / duplicate-walkers / duplicate-impl-tails findings they headed are **resolved** (the `check_program*`/`check_repl_input*` shadow pipelines are gone — the names survive only as test-driver methods, `checker/test_support.rs`; the `check_forms` single path is as-built). Forward-looking maintainability is now driven by the rolling per-crate audit cycle (`audits/cranelisp-typecheck-s114.md`, `/audit`), whose live watch-items are:

- **`finalize.rs` 1,517 LOC** — +85% over its own S109 design estimate (~820) and over the ~1,200 ceiling, because the settlement machinery keeps landing there (the three harvest windows, `monomorphisation.md` §11.8.10). The window structure is the natural cut line; the re-budget is FIXME 0722 (audit R-3, this sprint's `/dev` item).
- **`checker.rs` 3,180 LOC** — the largest production file post-split; a watch-item, not yet over any stated budget.
- **`program/tests.rs` 10,576 LOC monolith** — the designed per-submodule test split (`program-decomposition.md` §3) shipped its production cut without the test cut; FIXME 0722 executes it this sprint.

### 3.3 Cross-module lookups (`checker.rs`)

`checker.rs` holds the cross-module lookup helpers (`lookup_type_def`, `lookup_constructor_type`, `all_type_defs`, `lookup_trait_decl`, `has_impl`, `get_implementing_types`, …). Short-name resolution is current-module-only with per-symbol chain-follow on `Import`/`Reexport` entries — **no universe scan** (`crates/cranelisp-typecheck/CLAUDE.md` §"Module-locality"; Principle 17); `resolve_terminal_entry_and_home` / `chain_follow_to_home` are the navigation primitives, staging-aware via `probe_module_entry_owned`. A centralised `Index` view was proposed by the 2026-04-23 audit purely as a maintainability bookkeeping step (never a perf optimisation, Principle 6); it is **not landed and not currently prioritised** — the per-symbol chain-follow is the operative model and the S108 Wave-G convergence (`scope_resolve` / `ResolutionScope`) is where the shared resolution logic already single-sources.

---

## 4. Quality attributes

### 4.1 Simplicity (Principle 6 — complexity has a budget)

The crate's *core* is simple: per-`Expr`-variant inference, Algorithm-W unification, generalise/instantiate. The three "HIGH" simplicity findings of the 2026-04-23 audit — **duplicate pipelines** (`check_program*`/`check_repl_input*` shadowing the real path), **duplicate `Expr` walkers**, **duplicate impl-method tails** — are **resolved**: the shadow pipelines are gone (only test-driver shims remain, `checker/test_support.rs`); `check_forms` is the single cluster path. The live simplicity concern is not duplication but **file growth at the settlement machinery** (`finalize.rs` §3.2), tracked by the rolling audit cycle, not a standing remediation list.

### 4.2 Maintainability

Forward-looking maintainability is driven by the rolling per-crate audit (`audits/cranelisp-typecheck-s114.md`), not the retired 2026-04-23 remediation roadmap. The live risks and their dispositions:

| Live risk (audit s114) | Disposition | Reference |
|---|---|---|
| `finalize.rs` over budget (settlement machinery accretes) | Re-budget at the harvest-window seams | FIXME 0722 (this sprint), §3.2 |
| `program/tests.rs` monolith (designed split not executed) | Per-submodule sibling test files | FIXME 0722, `program-decomposition.md` §3 |
| `checker.rs` largest post-split file | Watch-item, no budget breach yet | §3.2 |
| `.meta.json` carrier meaning changes (`callees`, `resolved_targets`) | Ride the `CACHE_SCHEMA_VERSION` bump in the SAME change-set | `crates/cranelisp-typecheck/CLAUDE.md` §"`Def.callees` completeness" |

`ModuleEntry::Def` field discipline (a former audit finding — the many manual struct literals) is now mediated by the builder API (`ModuleEntry::def(..).build()` and the mono/ctor registration seams) and the concrete-`codegen_view` population contract (`CLAUDE.md` §"Concrete-boundary `codegen_view`"); a field addition rides the builder, not N hand-edited literals.

### 4.3 Observability

`trace.rs` exposes `install_symbol_table_ensure_hook` for the integration layer to wire scheduler tracing. This is the documented mechanism (`design/int/heisenbug-race-closure.md §3d''`). No further observability surface is planned for this crate — the typecheck product (`CheckResult`) is itself the diagnostic artefact, and per-symbol introspection (`Introspection.clif_ir` etc.) is `/backend` + `/int`'s.

When typecheck errors surface, `ErrorLocation` (§7) carries enough metadata for the integration-layer formatter to render rich context without typecheck duplicating the source-snippet logic.

### 4.4 Concurrency-safety

Covered in §6. The headline: typecheck holds no shared state across calls; concurrency is handled by the SymbolTable mutation discipline (Decision 38 — landed; §6).

### 4.5 Performance

Cross-module resolution is per-symbol chain-follow (current-module probe + `Import`-chain follow), not a universe scan (§3.3). For current workloads this is fine; the `Index`-view centralisation is a bookkeeping step, not landed, not currently prioritised (Principle 6 — premature performance work forbidden). The cross-module read path (`check_forms` → `&SymbolTables` → shard-shared `.get(&other)`) contends per-entry with a concurrent insert from another worker only at microsecond scale (Decision 38 analysis). Algorithm-W's substitution-composition cost is well-understood; no spec criterion pins typecheck wall-time.

### 4.6 Testability (Principle 5 — testability is structural)

The crate is structurally testable: `check_forms` takes `(parsed, &mut SymbolTableAccess, &SymbolTables, …)`; unit tests drive it via `TestFixture` (`checker/test_support.rs`), which seeds the full synthetic world on `cranelisp-types` alone (no `cranelisp-primitives` dep — the isolation that makes `builtins.rs` a fixture world). The scaffolding (`CheckState`, `TypeCheckEnv`, `SymbolTableAccess`) is exposed precisely for this; `int` uses only `check_forms` in production. The live testability concern is file ergonomics — `program/tests.rs` at 10,576 lines is hard to navigate; the designed per-submodule split (FIXME 0722, `program-decomposition.md` §3) is this sprint's `/dev` item.

---

## 5. Pipeline structure inside the crate

`check_forms` is the cluster-atomic entry (Decision 44); internally it runs three stages over the cluster's `ParsedEntry` list, then finalises:

1. **Pass 1 — Register** (`program/register.rs::check_form_register`). Walks each form (`TypeDef | TraitDecl | TraitImpl | Defn | Expr`), installs each canonical declaration and exposes its unqualified module-scope candidate under §8.6.4, and populates the staging table with type defs, trait decls (+ methods), trait impls, and signature schemes. No body checking. Distinct canonical declarations sharing a spelling coexist; use-site selection is the proposed interior design in `use-site-candidate-selection.md`.

2. **Pass 2 — Body check** (`program/body.rs`). Algorithm-W checks each body against its ledger registration, retains the annotated AST and initial canonical callees in that exact checked record, and leaves active expression and resolution facts on `CheckState`. `FormCheckResult` carries only per-form products and warnings. Initial callee derivation uses `program/callees.rs::harvest_callees`; final late-edge union and atomic AST-plus-callee publication occur in `program/finalize.rs::finalize_annotations_and_publish` (`CLAUDE.md` §"`Def.callees` completeness").

3. **Finalize** (`program/finalize.rs::finalize_check_result_inner`). The post-passes: generalisation (the FIXME-0349 `regeneralize_defn_schemes` chain), overload resolution + the multi-sig back-flow drain (§5.1.2), monomorphisation (the three `pass4_monomorphise` harvest windows, `monomorphisation.md` §11.8.10), the ownership post-pass (`ownership/`, `ownership-inference.md`), and AST annotation — producing the rolled-up `CheckResult`.

All writes flow through `SymbolTableAccess` (`current_symbol_table_mut`), staging-aware and cluster-atomic (Decision 44); the cluster commits atomically. `int` invokes `check_forms` per cluster in the form-by-form scheduler loop.

---

## 6. Mutation discipline (Decision 38 — landed)

The load-bearing simplification of S63, now as-built. `check-form-api.md` assumes `&mut SymbolTable` and is superseded on signature by this contract (Decision 38); it is retained because `program/finalize/tests.rs` traces its result-identity cases to it.

### 6.1 The contract

`check_forms(parsed, &mut SymbolTableAccess, &SymbolTables, …) -> Result<CheckResult, CheckError>` — writes flow through `SymbolTableAccess` (Decision-44 staging), never a raw `&mut SymbolTable`.

The only `&mut SymbolTable` operations in the entire system are:

1. **Phase 0 setup** — `write_structural_decls(&mut self, decls: StructuralDecls)`, called once per module at parse time by `int::register_module`. Seeds `imports`, `exports`, `platforms`, `submodules` (per Decision 33), and seeds `defn_order: Vec<Symbol>` (per Decision 39) from the parser's declaration-order list of defn names.
2. **Per-REPL-eval `defn_order` append** — `append_defn_order(&mut self, sym: Symbol)`, called by `int` after a REPL-defined symbol commits. Brief integration-layer-only window.

Both operations live on the initiator thread. Workers never see `&mut SymbolTable`.

### 6.2 How writes happen during typecheck

`check_form` annotates `node` in place (the AST is owned by the caller, so this is local mutation, not symbol-table mutation). It does NOT call `insert_or_update` — committing the new `ModuleEntry::Def` is `int::insert_symbol`'s job (BC §2 invariant 2).

When typecheck logically needs to publish something to the symbol table (e.g., a synthesised mono-defn entry, or a Pass-1 signature), it does so via `SymbolTable::insert_or_update(&self, sym, entry)` — `&self`, writing through the inner `DashMap<Symbol, ModuleEntry<C>>`'s per-entry write lock per the per-symbol mutability discipline.

### 6.3 Why this matters mechanically

Two correctness payoffs (FIXME 0008 §"Operational implication"):

- **Per-symbol gap mechanism becomes mechanically sound.** A `Gap(SymbolTypechecked(m2/bar))` waker resumes and finds m2's symbol table queryable via shared shard access — no whole-module write lock to contend. This is what makes Decision 30's per-symbol gap kinds (`SymbolTypechecked(FQSymbol)`, `MacroInMem(FQSymbol)`) operationally usable.
- **Cross-module read contention disappears.** A second worker's `Sess.symbol_tables.get(&m1)` does not block behind the typecheck-in-progress worker's RefMut.

### 6.4 What the current source still does

`TypeCheckEnv` reads/writes through `SymbolTableAccess` (Decision 44), which selects staging-vs-live per module (`SymbolTableRead::Cluster` when the module is the cluster's own staging target, else `Live`). The `check_forms(…, &mut SymbolTableAccess, &SymbolTables, …)` free-function shape is as-built — no `&mut SymbolTable` crosses the boundary. This migration **landed** (former FIXME 0008); it is not sprint work that remains.

### 6.5 What this supersedes

- `check-form-api.md` — describes `check_form(ast, &mut SymbolTable, &SymbolTables)`. **Stale on signature**; the algorithm shape it describes (per-form Pass-1/Pass-2, accumulator) survives, and the doc is retained as the `// spec:` anchor for the `program/finalize` result-identity tests.
- The S47 DashMap-migration and S51 stateless-extraction records were **deleted at S122**. §7.5 carries the guard discipline the DashMap migration established, this section carries the mutation contract it was a step toward, and the `TypeCheckEnv` + `CheckState` split (no registries) is `design/typecheck/traits.md` §1.1. Git retains the records, and `design/typecheck/CLAUDE.md` §"Redirections" maps a citation to its destination.

---

## 7. Concurrency model

### 7.1 What the crate sees

`check_form` is invoked by an `int` worker. The worker holds:

- `&SymbolTable` for the worker's owning module (shard-shared lock on `shared.symbol_tables.get(&m)` — per the post-FIXME-0008 shape; under current source, a `RefMut` is held).
- `&SymbolTables` for cross-module FQ resolution (`.get(&other)` per remote module).
- `&mut CheckState` (per-call transient — owned by the worker).
- A mutable `Ast` (caller-owned; in-place annotation).

The crate does NOT read `Sess`, does NOT read `SharedState.scheduler`, does NOT call `wait_for_typecheck_*`. Per BC §2 invariant (dependency-gap return) / Principle 3 (dependency flows toward stability), dependencies surface as `CheckError::Gap` values.

### 7.2 Reframing of Decision 30

Decision 30 ("form-by-form scheduler; mutual imports deadlock") historically claimed single-worker-per-module as a **lock safety requirement**. Decision 38 reframes this to **scheduler ordering only**. Per-entry inner-DashMap locks make multi-worker mutation of one SymbolTable safe in principle. The single-worker-per-module invariant still helps the scheduler avoid dispatch races and simplifies form-by-form sequencing, but it is no longer required by the lock discipline. The mutual-import deadlock remains a scheduler-level constraint with the documented `discover-tests` workaround.

### 7.3 Gap-return contract

Per the gap-return pattern (the `int` orchestrator's per-form retry loop, `design/int/` + BC §6):

| Gap | When typecheck raises it | Caller response |
|---|---|---|
| `ResolutionGap::SymbolTypechecked(fq)` | FQ value reference whose module isn't typechecked | `int` ensures `fq.module` is registered, calls `wait_for_typecheck_symbol(fq)`, retries `check_form` |
| `ResolutionGap::Type(fqt)` | FQ type reference whose module isn't typechecked | `int` ensures `fqt.module` is registered, calls `wait_for_typecheck_type(fqt)`, retries |
| `ResolutionGap::MacroInMem(fq)` | (raised by `frontend::expand`, NOT `check_form`) | by the time `check_form` runs, expansion is complete |

Typecheck asks for `SymbolTypechecked` (not `SymbolInMemory`) for value references — it needs the entry's `Scheme`, not its compiled code. This is what makes the gap-return cheap: typecheck does not block on codegen.

The `MacroInMem` variant in the unified `ResolutionGap` enum is raised by frontend, not typecheck. This is an **intentional contract**: `ResolutionGap` is the unified gap-return type spanning frontend + typecheck producers, and each producer raises only its applicable subset (Principle 7 — single source of truth: the gap enum is one shared vocabulary, even though each call site uses only part of it). §11 raises this as a doc-clarity FIXME asking `/arch` whether the rustdoc should pin which producer raises which variant.

**Source status (landed):** `CheckError` is a **crate-owned** type in `result.rs` (`#[non_exhaustive]`, variants `Gap(ResolutionGap)` + `TypeError { message, location }`); `ResolutionGap` lives in `cranelisp-types`. `check_forms` returns `Result<CheckResult, CheckError>` at the boundary — the crate no longer returns `CranelispError`. The dependency-gap mechanism (`ResolutionGap` values surfaced as `CheckError::Gap`, orchestrated by `int`) is as-built.

### 7.4 Snapshot / restore

`check_form` may write intermediate state (type-var allocations, deferred resolutions in `CheckState`). On `Err`, the caller restores via `ReplSnapshot` per `pipeline-v4.md §6.2`. The crate provides the snapshot/restore primitive (`TypeCheckEnv::snapshot`, `TypeCheckEnv::restore`) but does not invoke it itself. (REPL eval rollback semantics depend on this — temporary closures from `(let [f add] f)` shapes do not commit until expression eval succeeds.)

### 7.5 Guard discipline — hold one table guard at a time

Every module table is reached through a lock. `SymbolTables::get` hands out a per-shard `DashMap` guard; cluster-mode staging hands out a `RefCell` runtime borrow (`SymbolTableRead::Cluster`). A lookup that must follow a chain — an `Import`/`Reexport` hop to another module, a trait reference to its defining module, an import collection feeding a write into the current module — **clones the entry out of the first guard, drops the guard, and only then takes the next one.**

Two distinct failures this avoids: two guards on the same `DashMap` shard where one is a write **deadlock the process**; a second borrow of the same staging table **panics** the `RefCell`. Both need a specific module pair or cluster shape to appear, so a passing suite is weak evidence — this is a **discipline asserted with a named falsifier**, not a structural guarantee: nothing in the types prevents holding two guards, and the falsifier is a hang or a borrow panic on a crossing that has not been exercised. `checker.rs::current_symbol_table`'s rustdoc carries the same rule at the seam where the guards are minted.

---

## 8. Error construction (Decision 39)

Every `CheckError::TypeError` carries an `ErrorLocation`:

```rust
pub struct ErrorLocation {
    pub span: Span,                 // always populated (SYNTHETIC for synthetic forms)
    pub file: Option<PathBuf>,      // populated when known (file-based modules)
    pub fq: Option<FQSymbol>,       // populated for post-parse errors — links to per-defn source on Introspection
    pub line_col: Option<LineColRange>,  // populated when source in hand at error-construction time (cheap)
    pub context: Option<String>,    // inline source snippet — typically deferred to formatter via fq lookup
}
```

### 8.1 Producer policy for `cranelisp-typecheck`

| Field | Typecheck's policy |
|---|---|
| `span` | Always populate from the offending AST node. |
| `file` | Populate if known (passed in by the caller via `TypeCheckEnv` — typically yes for file-based modules, no for REPL evals). |
| `fq` | Populate when the error is about a defn whose FQ name is determinable (the common case in body-pass errors). Links the error to `shared.introspection[fq].source` for downstream rich display. |
| `line_col` | Populate when the file source is in hand at error-construction time. Typecheck doesn't usually have it (the file string drops after parse) — leave `None` and let the formatter resolve via `fq` + `Introspection`. |
| `context` | Leave `None`. The integration-layer formatter reads `Introspection.source` for snippets; typecheck need not duplicate. |

### 8.2 Why this works

Production batch (no introspection) shows `file:line:col: type error: …` — the `Span` gives the offset, the file-mtime path gives `file:line:col` resolution. REPL / trace mode (`shared.introspection` present) uses `fq` to resolve the per-defn source snippet for inline display. Both modes get the same error structure; only the formatter changes.

The `Warning` shape mirrors `ErrorLocation` (`cranelisp-types` rustdoc). Typecheck warnings (e.g., shadowing, unused imports — none yet implemented) follow the same producer policy.

### 8.3 Type-name rendering inside error messages — FQ-qualification (S87 Stage A)

**Contract.** `repl/spec.md` §5.3 requires a type error to name BOTH the expected and the actual (inferred) type **fully qualified** — `primitives/Int`, not the bare `Int`; `user/Color`, not `Color`. The source-location requirement is already met; the FQ-naming requirement is the open gap.

**Root cause (the bare-vs-FQ divergence).** The type-mismatch message is built at `unify.rs:117`:

```rust
_ => Err(CranelispError::TypeError {
    message: format!("type mismatch: expected {t1}, got {t2}"),
    location: ErrorLocation::from_span(Span::SYNTHETIC),
}),
```

`{t1}` / `{t2}` invoke `Type`'s `Display` impl (`cranelisp-types/src/types.rs:108`). That impl renders the **primitive** variants **bare** — `Type::Int => "Int"`, `Type::String => "String"` — while it renders `Type::ADT(fqtn, …)` through `FQTypeName`'s Display (which IS `module/name`). So for the failing guard `(add-i64 1 "hello")` (expected `Int`, actual `String` — both primitive variants), the rendered message is `type mismatch: expected Int, got String`: the names appear but unqualified.

The **value-display path** (`src/display.rs::format_type_qualified_inner`, the binary crate) already does the right thing — it maps each primitive variant to its `primitives/…` string. The two paths diverged because they are different functions: the error renderer reuses the bare `Display` impl; the value-display path has its own qualified formatter. The renderer's message string flows through `checker.rs::unify` (line 1642) verbatim — only the `Span` is re-wrapped — so the bare names reach the REPL output unchanged. `unify.rs:117` is therefore the exact and sole seam.

**Why the value-display formatter cannot simply be reused.** `format_type_qualified_inner` lives in `src/display.rs` — the **binary crate**, which *depends on* `cranelisp-typecheck`, not vice versa (dependency flows toward stability, Principle 3). `cranelisp-typecheck` cannot call up into `src/`. The qualification mechanism the error renderer needs must therefore live at or below `cranelisp-typecheck`.

**Fix locus and mechanism — typecheck-local FQ renderer (preferred).** Add a small **private** FQ formatter inside `cranelisp-typecheck` — a free fn `format_type_fq(ty: &Type) -> String` in `unify.rs` (private to the crate; the only consumer is the unify error renderer). It is the structural twin of the existing bare renderers but maps the four primitive variants to their canonical `primitives/…` strings and renders ADT / Fn / args recursively through itself:

- `Type::Int → "primitives/Int"`, `Bool → "primitives/Bool"`, `String → "primitives/String"`, `Float → "primitives/Float"`.
- `Type::ADT(fqtn, args)` → `format!("{fqtn}")` already yields `module/name` via `FQTypeName`'s Display; recurse on `args` (parenthesised when non-empty, matching the existing Display shape).
- `Type::Fn(params, ret)` → `(Fn [<params…>] <ret>)`, recursing on each.
- `Type::Var(id) → "t{id}"`; `Type::TyConApp` → render as the existing Display does (vars are not the §5.3 FQ concern).

Then **call it at `unify.rs:117`** — replace the two `{t1}` / `{t2}` `Display` interpolations:

```rust
message: format!(
    "type mismatch: expected {}, got {}",
    format_type_fq(&t1),
    format_type_fq(&t2),
),
```

**Why typecheck-local, not promoted to `cranelisp-types`.** Two reasons, both binding:

1. **Boundary ownership.** `crates/cranelisp-types/` is `/arch`'s direct ownership — the triad (incl. `/dev`) does NOT narrow-deploy to it (`triad-shared.md`). Promoting the formatter into `cranelisp-types` would force a cross-skill FIXME `target: /arch` and serialize the Stage-A fix behind an /arch edit. A crate-private helper keeps the entire fix inside the `/dev`-deployable typecheck crate — the Stage-A guard flips green without a cross-crate dependency. (No `cranelisp-types` boundary change is needed: /arch's Phase-2 ruling already confirmed "no interface delta … the /typecheck fix changes `TypeError.message` content only.")
2. **The /arch advisory wants the paths kept distinct.** The binding Phase-2 advisory is "do not unify the two [renderers] in a way that changes REPL value-display output." A typecheck-local renderer is the *most* faithful reading: the error path and the value-display path remain entirely separate functions in separate crates, converging only on the shared *output convention* (FQ primitive names), never on a shared call. The small duplication of the primitive→`primitives/…` mapping (now in three places: `Type::Display` bare, `src/display.rs` value-display, and this typecheck-local error renderer) is the deliberate price of the keep-distinct constraint. It is logged as an adjacent-instance / consolidation candidate for the Stage-B audit (lens item i), NOT collapsed in Stage A.

**Why this cannot regress value-display.** The change adds a *new crate-private* formatter and rewires *only* the unify error-renderer call site. It does NOT touch `Type`'s `Display` impl, does NOT touch the shared `cranelisp-types::render_type(ty, PrimitiveNaming, VarNaming)` renderer (which `Type::Display` delegates to with `Bare`/`Numbered`), and does NOT touch `src/display.rs::format_type_qualified_inner` (the value-display path keeps its own separate function and its separate spec contract). Nothing the value-display path calls is modified — the keep-distinct constraint is honoured structurally. *(S87 update: the 0420 FQ-walk consolidation later folded these renderers onto the single `render_type` entry point — `format_type_fq` now also routes through `render_type` with `Qualified` primitive naming, and the now-removed `cranelisp-types::format_type_display` / `format_type_with_vars` were deleted as zero-consumer dead code. The keep-distinct *output contracts* are preserved by the `PrimitiveNaming`/`VarNaming` parameters rather than by separate functions; see `design/typecheck/s87-fq-walk-consolidation.md`.)*

**Adjacent instances (lens — METHOD §Phase-5 emergent / audit-backlog candidates).** The same bare-vs-FQ class appears in two further typecheck error renderers:

- `unify.rs:135` — `"infinite type: t{id} occurs in {ty}"` interpolates `{ty}` through bare `Display` (occurs-check failure). Same FQ-formatter swap applies.
- `traits.rs:1157` and `traits.rs:1804` — `"no impl of trait {} for type {}"` render the type via `concrete_type_name` (`traits.rs:2202`), which returns a bare `TypeName` and even strips an ADT's module (`Type::ADT(fqtn, _) => fqtn.name.clone()`). This is a *deeper* gap than the unify path: the bare name is produced before the message, so qualifying it needs the FQ name reconstructed (primitives → `primitives/…`; ADT → `fqtn` itself, not `fqtn.name`), not just a formatter swap at the interpolation site.

These are **not** in the S87 Stage-A guard scope (only the two `type_error_names_*` guards are). They are noted here as an audit-backlog candidate for the Stage-B typecheck pass (lens item i — duplicated rendering paths / consistency). If `/dev` finds the `unify.rs:135` fix trivially covered by the same new formatter while making the Stage-A change, it is an emergent-mandatory in-sprint tidy (it shares the exact mechanism); the `traits.rs` `no-impl` sites are a larger reconstruction and should be left to the audit backlog unless a guard demands them.

**Testability (the mandatory unit test — Principle 5).** The fix lands with a **`cranelisp-typecheck` unit test on the renderer**, distinct from the two e2e guards in `tests/repl_negative.rs`. The unit test is authored by `/dev` in `unify.rs`'s `#[cfg(test)] mod tests` (where `test_unify_different_primitives_fails` already lives, line 188). It calls `crate::unify::unify(&mut subst, &Type::Int, &Type::String)`, asserts the returned `Err`'s `.message()` contains `primitives/Int` AND `primitives/String` (and, for an ADT shape, `module/Name`) — pinning the FQ-qualification at the exact seam where the bug lived, independent of the REPL stack. This is the fastest re-break guard and answers a different question than the e2e (which proves the qualified name survives the whole pipeline to stdout). Assess-before-fix verdict: the bug is observable end-to-end (REPL output), so the existing two e2e guards are the right e2e coverage — they already exist (failing); no NEW e2e is warranted. The mandatory NEW artefact is the unit test.

**Module-layout impact.** `unify.rs` (§3.1, "Clean", 339 LOC) gains one crate-private free fn (`format_type_fq`), a one-call-site edit at line 117, and one unit test; its health classification is unchanged. No `cranelisp-types` edit, no facade-shape change, no new public surface (the formatter is crate-private). No structural change to the crate shape.

---

## 9. Trait + monomorphisation architecture

### Sprint 116 — one semantic method tail

`spec/07-traits.md` §7.1 now supplies exactly one unresolved method tail.
Typecheck, not frontend spelling, classifies it by a side-effect-free
try-resolution as either a required return type or a default body. The settled
design is `s116-method-signature-resolution.md`: one unresolved boundary
carrier, one closed classified method kind, inferred/annotated per-impl default
bodies, and one conformance/re-impl path. The old mandatory `ret_type` plus
optional `default_body` pair is not retained as parallel authority. This is a
coordinated `/arch`-owned types-carrier change in the schema-23 window; the
typecheck crate adds no public entry point.

The detailed designs live in subordinate docs (cited in §10). The shape this master doc commits to:

### Sprint 117 — canonical qualified trait references in `impl`

`impl` slot 1 is resolved once from its complete bare-or-qualified `TraitRef`
to a crate-private settled product containing `FQTraitName` and the matching
`TraitDeclInfo`. That carrier is mandatory through conventional and HKT kind
validation, pairing-head identity comparison, impl placement/keying,
explicit/default/HKT method minting, rollback, and enrollment. Later passes
consume the settled canonical method-symbol set; they do not reconstruct it
from the source `TopLevel::TraitImpl`. `deftrait` declaration binders remain a
separate frontend grammar concern and bare-only.

Detailed design and test matrix:
`design/typecheck/qualified-trait-impl.md`. The change is wholly internal to
`cranelisp-typecheck`: existing `FQTraitName` and `ModuleEntry::TraitImpl`
carriers suffice, so there is no public API, cache schema, or cross-crate
interface change (Principles 7, 18, 24, and 26).

**Landed; confirmed against source 2026-09-01** (`qualified-trait-impl.md` §7).
`ResolvedImplTrait` and `resolve_impl_trait_ref` exist at `impl_check.rs:19,:63`,
called once from `register_trait_impl` at `:106`; both method mints take
`fq_trait_name.name`, and `:728`'s rustdoc carries the invariant that the
as-written `impl_.trait_name` is never a mangle input. **FIXME 0794's central
claim — that a qualified `impl` head mints an uncallable method — is thereby
falsified at source**, and the S119 F2 citation of `impl_check.rs:1029` that
depended on it is corrected in `non-concrete-producer-obligations.md` §1.3. F2's
live defect (`scheme::mono` over a residual `fn_type`) is a different defect in
the same function and is unaffected.

### 9.1 Trait method dispatch — Decision 14

Typecheck always emits `ResolvedCall::TraitMethod` for trait-dispatched calls (operators included). The backend recognises known primitive impls (`Num.+$Int → iadd`, etc.) via a static lowering table. Typecheck stays clean of backend lowering choices.

### 9.2 Constraint propagation — Decision 19

`Scheme.constraints` is populated by `generalize` collecting trait constraints from active type variables. Non-empty constraints mark a constrained polymorphic function; concrete bodies are deferred to call-site monomorphisation.

### 9.3 Monomorphisation analysis

`CheckResult.mono_defns: Vec<MonoDefn>` carries the specialisation requests typecheck discovered at call sites. The integration layer commits these as `ModuleEntry::Def` entries under the canonical authored-owner/full-concrete-signature key for the backend to compile. Typecheck does NOT commit the mono-defn entries itself — see `auto-curry.md` for the historical machinery and `traits.md` for the trait-dispatch interaction.

**Monomorphisation from roots (structural slot-gate first) — `monomorphisation.md`.** The detailed design for the S84 Cluster A guarantee that **no `Type::Var` reaches codegen under any reachable instantiation** lives in the subordinate doc `monomorphisation.md`, **re-grounded mid-Phase-5 on the structural-slot-gate-first model** (user ruling 2026-06-16; resolved FIXME 0376). The **primary mechanism is the corrected GOT-slot-allocation gate**: a def's `fn_state` carries a slot ⟺ its finalised type is **fully concrete** (`Type::is_concrete()`, NOT `constraints.is_empty()` — the as-built leak; "concrete" ≠ "unconstrained"), per Principle 20 (S84 generalisation) + BC §7 "Callability is structural". A determined-but-non-concrete *unconstrained* generic def gets a new slot-less `UserFnState::Polymorphic` arm (sibling to `Constrained`; an additive `cranelisp-types` variant owned by /arch + a `CACHE_SCHEMA_VERSION` 5→6 bump owned by /backend — see `monomorphisation.md` §6 + FIXME 0377). The slot-less-ness makes a non-concrete def unconstructable as a codegen value (the SIGSEGV root). The doc pins: (1) the corrected gate (`constraints.is_empty()`→`is_concrete()` at `program.rs:947`/`:1143` + the demotion leg `:1312`; the scheme-writeback legs `:919`/`:1129` stay `constraints.is_empty()`, governing 0344 generalisation, not slot allocation); (2) the systematic reachable-instance worklist/fixpoint EXTENDING the landed Tier-1/1.5 `pass4_monomorphise` → `monomorphise_call` → `monomorphise_inner_parametric_hops` spine (no second entry point — /arch ruling, Principle 7), **Wave-0-narrowed to the `(Box a)`-field-carrying-`Type::Var`-through-HOF gap** (bare-`Int` HOF shapes already mono cleanly — GREEN-stay guards), cluster-level dedup keyed on the canonical concrete realization key; (3) the §3.11.1 **ambiguity check** (0373 part ii) **demoted to a SECONDARY backstop** — fired at the post-generalisation finalisation boundary before Pass 4 (`finalize_check_result_inner`, after the first `regeneralize_defn_schemes`), raising `CranelispError::TypeError` today / `CheckError::AmbiguousType` post-FIXME-0098 (both typecheck-internal). **Wave 2 (FIXME 0379/0380) makes this check POSITION-COMPLETE and predicate-shared**: it fires the per-node verdict on the resolved type at *every* codegen-reaching value position `for_each_child_expr` visits (match scrutinee, fn-call arg, vec element, ctor field, if-branch, `ParBind` binding, nested `let`, returns — not just `let` bindings), and the verdict comes from the shared `Type::is_representation_undetermined()` predicate (the local `is_ambiguous_codegen_reaching_type` heuristic is retired) — the SAME predicate the WIDENED backend 0375 RC-site backstop uses, so the typecheck error and the backend panic agree by construction (belt-and-braces, BC §3 invariant 9). The 0344/0349 fold-accumulator over-monomorphisation is the pinned risk. Termination is bounded by monomorphic-recursion enforcement (rank-1 HM). This master doc commits to the shape `monomorphisation.md` elaborates; that doc wins on detail.

**The non-concrete producer obligations (S119 Spine 1) — `non-concrete-producer-obligations.md`.** `design/backend/non-concrete-release-contract.md` rules that a frame whose parameter or result types are not fully concrete is **not a legal codegen target** (R-3) and that no producer may present a downstream gate with a type more concrete than what it knows (R-2 — Principle 25 on the type channel). **Five** sites in this crate violate it, all by bypassing the S84 slot gate rather than by lacking a mechanism: four frame-level hand-mints (`adt.rs:172-181` constructor slots, `adt.rs:617-637` product accessors, `impl_check.rs:1039-1043`+`:1078-1089` impl methods via `scheme::mono` over a residual `fn_type`, `monomorphise.rs:667`+`:680-697` mono instances) and one value-level fabrication (`MonoExpr::lenient_from_expr`'s `node_ty`, replacing any non-concrete node type with `ConcreteType::Int`). The subordinate doc rules all five: **P-1** — re-grounded S121 — the gate is C1's `settle_concrete` funnel, the sole constructor of `Life::Concrete`, so typecheck's obligation is *consumption*, not enforcement, and the four hand-mints are deleted rather than gated; **P-2** (a monomorphised product-accessor / trait-method instance is named by the ONE canonical context-bearing `InstanceLink::instance_key(&template_scheme)`, which projects its authored owner and complete concrete function signature; the FIXME's proposed `mangle_trait_method` key widening is **rejected as lossy** on the argument-supplied type parameter and would re-open the 0483/0508/0519 collision class); **A-MINT** (a polymorphic product-accessor instance is re-synthesis at concrete type arguments over the template's `SynthSpec` recipe, never a body re-check — its body is `Span::SYNTHETIC` and therefore outside span-keyed carrier transport); and the **defaulting step** for the lenient view (L-1/L-2/L-3 — default residual *parameter positions* under a preserved type constructor, never substitute the node's type; licensed only where the residual cannot occur in a declared parameter type; refused as a located error over a constrained variable; and self-checking because the strict builder must then accept the body). Closes FIXMEs **0924**, **0913** and **0935**; the former 0867 widening is retired by the product-only ruling; gates **0916**. Zero `cranelisp-types` delta and zero typecheck public-API delta from this obligation; the schema question S119 raised for `/arch` is **answered** by the S121 contract — one window, `CACHE_SCHEMA_VERSION` 24→25, in C1's change-set.

`MonoDefn` redundant side-maps (no live FIXME file — doc-tracked here; the former 0033 anchor is absent from `design/arch/fixmes/`) — **Step A done; Step B is the field-drop.** `MonoDefn` (`cranelisp-types::check`) carries two Span-keyed side maps, `resolutions: MethodResolutions` and `expr_types: HashMap<Span, Type>`, that were redundant once monomorphisation annotated the AST directly. Step A landed: `traits.rs::monomorphise_call` now annotates `mono_defn.defn` in place (via `annotate_defn_from_maps` + `apply_subst_to_defn`) and **constructs `MonoDefn` with `MethodResolutions::default()` + an empty `HashMap`** — the fields are no longer populated in production. The only surviving reads are `#[cfg(test)]` scaffolding in `cranelisp-backend` (`test_compile_program_and_run`, which merges `mono.resolutions` and falls back on `mono.expr_types`). Step B is the structural removal: drop both fields, making `MonoDefn` a `Defn` newtype (or a single-field wrapper); update the one backend test to read annotations off `mono.defn` directly. **Baseline impact:** removes three `cranelisp_types::MonoDefn::{expr_types, resolutions}` lines from `crates/cranelisp-types/public-api.txt` (regenerate per the baseline-diff discipline). The field-drop and the types-crate baseline regen are `/dev`-on-`cranelisp-types` work (the struct lives in the interface crate, `/arch`-adjacent); the backend test edit is `/dev`-on-`cranelisp-backend`. Coordinate as a small two-crate change.

### 9.4 ADT typing

`TypeDefInfo` + `ConstructorInfo` + `FieldInfo` describe the registered ADTs. Pattern matching infers via standard unification + nominal constructor-to-type resolution. Exhaustiveness is checked in `adt.rs`. Polymorphic ADTs with data-constructor fields fully supported (e.g., `(Some [:a val])`).

**Field-accessor `Type.field` (canonical) + impl-time collision (FIXME 0365, S91; INVERTED S91 Phase-5) — `fixme-0365-field-accessor-dotted.md`.** **Canonical/alias direction INVERTED by user ruling (2026-06-26, design-only pending user confirmation; supersedes the §1.5 visibility-by-arm rule, kept banner-marked).** **`Type.field` (`Box.v`) is the CANONICAL field accessor — always a real Public `Def`, the listed/displayed name (qualified-display convention, Principle 16); bare `field` (`v`) is a convenience `Import` alias → `Type.field`.** Ambiguity lives in the **alias**: one type owns `v` → bare `v` resolves; two share `v` → bare `v` is ambiguous (`Ambiguous` sentinel), while canonical `Box.v`/`Cup.v` keep working (no cliff). Synthesis (`adt.rs::synthesise_one_accessor`) registers the real `Def` under the canonical key + the `Import` alias under the bare key (the as-built reversed); the poison re-mint helper (`remint_first_accessor_under_qualified_key`) and the per-case visibility flip are **deleted** (net code reduction, Principle 6). Typing reads the canonical `Def.scheme` (`FieldType` = return arm); bare alias chain-follows to it — one scheme, one compiled function (duplicate-codegen fix preserved). Cross-module is **strictly better**: canonical `Box.v` uniformly Public → `m/Box.v` resolves in every case incl. contested (the as-built poison-must-be-Public worry, `resolve.rs:578`, disappears). The impl-time collision rule (§7.3.1) fires against the canonical key — a new pre-flight validation in `register_trait_impl` (`impl_check.rs`) enumerating the type's canonical accessor names via `committed_accessor_kind` (`adt.rs:677`), intersecting with the impl method names, raising a `TypeError` naming both sites before the impl registers (Principle 18; the contested-field enumeration simplifies — no `accessor_owning_types` consult needed since the canonical entry is unconditional). `/list`/`/exports` show the qualified canonical `Box.v` (every field, every case); bare alias not separately listed. **Zero `public-api.txt` / `cranelisp-types` movement** (internal relabeling of which key is `Def` vs `Import`). FIXMEs filed: `/spec` reframe of §5.2.6/§8.5.2 (bare-as-alias, `Type.field`-as-canonical); FIXME 0438 updated for the inverted listing question. See the subordinate doc §0/§1/§1.6/§2 for the inverted design, `/dev` rework, and `/qa` guards.

### 9.5 HKT — `hkt.md`

Constructor variables (e.g., `:Functor f`, where `f` is a type-constructor variable) supported via `Type::TyConApp` and a parallel impl-method check path (`check_hkt_impl_method`). The audit Finding 3 highlights this as the duplicate-tail risk; the resolution is to share the post-resolution finalization step, keeping only the type-resolution front halves separate (audit remediation #2).

### 9.6 Multi-sig dispatch + auto-curry

`DefnMulti` defns produce one `ModuleEntry::Def` per signature variant. Their private per-clause labels and generation-local `CallableTarget` selectors choose declarations; they are not canonical executable identity. Dispatch happens post-inference when concrete arg types match a variant, and a realized callable uses the authored family plus its full concrete function signature. Auto-curry (calling with fewer args than declared) interacts with multi-sig — this is the most subtle interaction in the crate. Documented in `auto-curry.md`. **S112 (leg a, FIXME 0642):** the settled §5.1.2 makes a multi-sig `defn` inference-equivalent to its clauses as separate mutually-recursive functions — sibling self-calls back-flow and pin clause params (the former "clause independence / no-back-flow" barrier is removed), and the once-"not supported" **multi-sig × constrained-poly** interaction is IMPLEMENTED (each constrained clause rides the standalone constrained-template / `pass4_monomorphise` path). Designed in `monomorphisation.md` §11 (supersedes §9's drifted posture).

`ResolvedCall::AutoCurry` total-count (no live FIXME file — doc-tracked here; the former 0043 anchor is absent from `design/arch/fixmes/`) — `AutoCurry` is missing `total_count` per the sketch; either extend the type or look up at codegen time. A `/design`(typecheck) ↔ `/design`(backend) coordination item; not currently scheduled.

### 9.7 Principle 26 carrier → pass → settlement-window classification (S113 SEED; full sweep needs its own slot)

Principle 26 "Record from settled state" (ratified S112) says every span/entry-keyed
producer carrier must be **derived once from settled state, never patched after record**.
The classification the sweep produces is, per carrier: (1) the PASS that produces it, (2)
the settlement WINDOW it must record from, (3) whether the as-built producer records at or
after that window. The S112 defect family is the empirical case FOR the principle — every
one of R2/D3/D1 is a carrier recorded (or read) OUTSIDE its settled window.

**W2-family seed (the carriers this sprint's mono/carrier fix touches).** Classified here
because the W2 design (`monomorphisation.md` §11.8; §7.0.1/§3.2/§7.0.2 in `traits.md`) IS
the worked P26 exemplar:

| Carrier | Producing pass | Settlement window (record-from) | As-built verdict |
|---|---|---|---|
| `MethodResolutions.resolved_calls` (`SigDispatch`) for a multi-sig-dispatch call in a mono/clause body | pass-4 mono recheck / drain | **post-drain**, after `finalize_multi_sig_variant_types` Phase-A concrete promotion | **VIOLATED** (R1/R2): recorded at pass-4, pre-drain — the overload set is not settled → carrier missing/`$Var`-mangled. §11.8 fix records post-settlement. |
| mono instance + its `SigDispatch` for a poly hop in a multi-sig CLAUSE body (`idpoly$Int`) | pass-4 `collect_mono_call_sites` | after clause bodies settle concrete (Phase A) | **VIOLATED** (D3): the clause body is never scanned (`collect_single_sig_defns` filter). §11.8 fix scans settled clause bodies. |
| `OverloadVariant.{param_types,ret_type,mangled_name}` | Pass 2.5 register + Phase-A finalize | post-drain (back-flow-pinned clause → Concrete) | OK (leg-a landed the two-pass ordering; §11.3(B)). |
| `ConstrainedFn`/template `Scheme.constraints` for a constrained multi-sig clause | body check (`body.rs:479`) | body-inference settlement | OK — it IS the settled record; **D1's display READS the wrong carrier** (bare `OverloadVariant`, not this scheme), an int-side read-target defect, not a record defect (`traits.md` §7.0.2). |
| `ResolvedCall::TraitMethod` for a method-only-import nullary cell | `try_resolve_trait_method` | method-home resolved once (P24) | **VIOLATED** (D2): rooted at trait-in-scope, so never recorded for the method-only-import cell; the home is resolved then discarded (`checker.rs:2415`). §7.0.1 fix roots at the home. |

**Full-surface sweep — SCOPED to its own slot, NOT completed here.** A P26
carrier→pass→window classification of the *entire* typecheck producer surface —
`resolved_targets`, `callees`/`user_fn_refs`, `codegen_view`, `unresolved_dispatch`,
`pattern_ctors`/`MonoMatchArm.resolved_ctor`, `deferred_self_call_dispatch`,
`pending_auto_curry`, the `defn_type_vars`/scheme writebacks, `TraitImpl.impl_module` —
is a substantial standing analysis (each carrier's settled window, its producing pass, and
a record-vs-window verdict), and it is the natural home for the RG-P24 register's typecheck
leg (`tests/plan/s111-principle24-register.md` leg 1, open) **and FIXME 0653** (the P24
corollary that surfaced from the S113 W2a D2 landing — "a resolution product carrying FQ
identity narrowed to its bare name, later re-resolved in ambient scope, is a defect marker";
three W2a instances shared that `(&CheckState, &bare-name)` shape). The sweep should adopt
0653's recommendation — audit typecheck's remaining bare-name+state helpers into
pre-resolution seams vs re-resolvers to delete — as an explicit axis. **The enumeration seed
for the sweep is the written-name-identity battery** (`tests/plan/s111-principle24-register.md`
§3, 7 rows) — start the carrier→pass→window classification from those seven written-name cells
rather than a blank surface scan. The W2-close instances already classified: the shared
`callee_has_keyed_carrier` guard (`monomorphisation.md` §11.8.8 — name is a TRIGGER, carrier is
the IDENTITY; 0653 second prong) and the `overload_homes` bare-name re-derivation
(`monomorphisation.md` §11.8.9 — 0632 tripwire, retire by carrying the storage base name as
resolved data). It deserves a dedicated
`/design`(typecheck) slot rather than a rider on the W2 defect dispatch — squeezing it in
would under-serve it (the S112 "design enumerates fewer cases than the spec/surface names"
wrinkle this very sprint adopts a guard against). **Recommendation to /sprint:** schedule
the full P26 typecheck-surface classification as a standalone Phase-1/3 /design slot (S114
candidate), seeded by this table; its findings append to the P24 register per
`tests/plan/s111-principle24-register.md` §2.3.

**S114 sequencing (binding).** The full P26 sweep + the 0653 helper-classification
sweep run **AFTER the carrier flip lands**, as its acceptance check — the flip
reshapes the very inventory they classify (`resolved_targets` → the total typed
`var_refs`/`apply_refs`), so classifying pre-reshape would misinventory. Sweeps are
**migration aids, never the enforcement mechanism** (P24 §Corollary prong 3 — an
interim gate patch a constructor obsoletes is the Principle-8 half-measure). The
carrier producer plan is `typed-resolution-carrier.md`; the sweep verifies at wave
close that (a) the inventory was classified post-reshape, (b) zero
keyed-read-else-resolver hybrids appear, (c) the two bare-name-helper camps
(legitimate pre-resolution seams vs re-resolvers to delete) are dispositioned.

**S114 W7 — DONE (post-flip acceptance sweep run over the CARRIER surface;
`typed-resolution-carrier.md` §14).** Results: the carrier surface is P26-clean —
8 producer write-populations classified, **6 IN-WINDOW**, **1 IN-WINDOW +
order-independent** (the `ApplyRef::ViaCallee` totality stamp, `infer.rs:63`, P26-safe
by the `or_insert`/`insert` monotone-lattice asymmetry `ViaCallee ⊑ Dispatch`),
**1 standing classified re-derivation** (`overload_homes`, §11.8.9 — sound-today,
0632-tripwired, named retirement, not a defect); zero out-of-window or
provisional-then-repair writes. **SW-1** (the `try_resolve_trait_method`
Err-disposition family): **CLOSED** — 4 callers propagate, 1 justified-benign-with-fence
(`mono_collect.rs:781` auto-curry re-attempt, evidenced by the F-D2-12 born-green
fences; the residual there is a SEPARATE `carrier-loss` defect, FIXME 0705, not the
swallow); zero unclassified swallows. **SW-2** (no producer writes `var_refs`/`apply_refs`
at `Span::SYNTHETIC`): **HOLDS** — recorded as a standing invariant with its
order-dependence rationale (a SYNTHETIC-key write would collide over the one shared
`Span{0,0}` key and mask the all-local carve-out; the sole licensed SYNTHETIC-key
population is `synthetic_local_from_expr`, which is not a map write). **0653 residuals:**
the `node_ty` `NotConcrete::Var(0)` sentinel is **retired-by-the-flip as a conflation**
(post-flip `from_expr` reads the resolution verdict BEFORE the type, so "unresolved" and
"un-typed" are now distinct `ViewBuildError` arms); the `{home}/{bare}$sig`
string-embedded mangle **stands-with-rationale, correctly homed at R4** (a keyed-identity
mangle, not a bare resolution product); the bare-name+state helper camps dispositioned.
The full-*surface* sweep (this §9.7 standing analysis over the ENTIRE producer surface,
beyond the carrier) remains the open RG-P24 register leg — the carrier-surface leg is now
classified.

---

## 9.8 Sprint 121 — the C3 lifecycle-consumption visit

**One visit, one interior change.** Sprint 121 allocates this crate a single
crate-shaped visit (`sprints/SPRINT.md` §Delivery streams, stream C3) covering
fifteen legacy filings **plus two cross-stream arms allocated by `arch` after the
visit first closed** — the FIXME-0869 written-trait-impl producer
(`design/arch/trait-impl-cache-carrier.md` §9) and one FIXME-0798 call-site flip
(`design/arch/module-alias-scoped-lookup.md` §5). Both are consumption of a
settled cross-crate contract, not new interior design; §9.8.1 records what they
bring and §9.8.2 places them in the order. This section is the visit's order, its
reservations and its handoffs; the substance lives in the subordinate docs named
per row. A later stream may not re-open what this visit releases.

The S122 filing reconciliation retires 0869 after its writer, restore and warm-cache
evidence landed. FIXME 0798 remains with its owning context.

### 9.8.1 What the visit consumes, and does not reopen

| Input | Owner | What C3 takes as settled |
|---|---|---|
| `design/arch/symbol-table-lifecycle.md` §§3–6 | C1 (`arch` + `cranelisp-types`) | `BindingBody::{Alias, Ambiguous, Decl}`; `Life::{Declared{prior}, Template, Concrete{slot, realization}, Inline, HostPromised, Broken}`; `CallableOrigin`; `Realization::{Body, ExternShim, Dll, FacadeOf}`; authoritative slot claims plus `retired_slots`; `MonoDemand` / `InstanceLink`; private `symbols` behind funnels. **No crate design may select a second lifecycle representation** — a missing state is a filing to `arch`, never a local vocabulary grown beside it. |
| [the one S121 schema and baseline window at checkpoint `dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md) §9 | C1 | `CACHE_SCHEMA_VERSION` 24→25 exactly once, in C1's change-set (the constant lives in `crates/cranelisp-backend/src/cache/mod.rs:391`); the single `cranelisp-types/public-api.txt` regeneration. C3 bumps nothing and creates no second window. |
| `design/frontend/s116-syntax-and-annotation.md` §3.1 | C2 | every spec §5.2.4 declaration-shape reject is frontend's and exclusive. **Typecheck adds no compensating check** (FIXME 0912 retired). Concrete named-type resolution stays typecheck's distinct §8.5 responsibility. |
| `spec/04-expressions.md` §4.6.3; `spec/03-types.md` §3.11 | `spec` | residual monotype variables remain in the same inference context and may be constrained by a use; variables still unresolved after inference reach the ordinary ambiguity rule. |
| `design/backend/non-concrete-release-contract.md` | `design`(backend) | R-2/R-3 and the five faces; the census instrument and its flip criterion. |
| `design/arch/trait-impl-cache-carrier.md` §§3–4, §8, §9 | `arch` (carrier landed S119 in `cranelisp-types`) | The producer seam is `register_trait_impl`, not the phantom `check_trait_impl`; the record is built from the **same** derived values as the shell and rides the **same** transaction; identity is `trait_impl_key`'s `(impl_type, trait_name)` pair and a same-key re-impl **upserts**; the checkable invariant is record ⟺ shell at every commit boundary; `trait_impl_key` is the one mint of the `impl$` storage key. §3–§4 are the complete interior design for the append — C3 states only *where in this crate's transaction* it sits (§9.8.2 CS-6, `traits.md` §3.0.1). |
| `design/arch/module-alias-scoped-lookup.md` §3.2, §4, §5 | `arch` (types half is C1's) | `substitute_module_alias` takes a `referring_module` and becomes a scoped segment walk of keyed probes; `module_alias_key` is the one key mint; typecheck's whole obligation is to pass the referring module it already holds. **Typecheck neither re-walks segments nor constructs an alias key** — a second walk or a hand-spelled `<owner>.<alias>` anywhere in this crate, fixtures included, is the contract's §7 falsifier. |

### 9.8.2 The order

Six change-sets, one wave. CS-1 and CS-2 land in the same wave even though they are
separate commits: CS-1 is the forcing function that makes CS-2's misses loud.

| # | Change-set | Design | Reserved paths |
|---|---|---|---|
| **CS-1** | Funnel consumption — delete the four hand-mints (`adt.rs:172-181`, `adt.rs:617-637`, `impl_check.rs:1078-1089`, `monomorphise.rs:680-697`); stop `scheme::mono` over a residual `fn_type`; delete the `ConstrainedFn` synthesis at `monomorphise.rs:1188-1197`; re-arm every `ModuleEntry`/`UserFnState` match in the crate onto `BindingBody`/`Life`; pass `state.current_module` as the referring module at the crate's one `substitute_module_alias` call (`checker.rs:1476`, in `normalize_self_qualified`) | `non-concrete-producer-obligations.md` §2.1, §7.1; `design/arch/module-alias-scoped-lookup.md` §3.2, §4 | `adt.rs`, `traits/impl_check.rs`, `traits/monomorphise.rs`, `program/finalize.rs`, `program/register/`, `checker.rs` (match re-arm + the one alias call-site flip) |
| **CS-2** | Coverage — one `MonoDemand` constructor for the three collector sites (0935); product-accessor A-MINT; the product/sum no-accessor boundary (0867 retired); the F2 `ApplyRef::Dispatch → Template` trigger | `non-concrete-producer-obligations.md` §2.3–§2.5, §4, §7.2; `fixme-0365-field-accessor-dotted.md` §1.6.7 | `adt.rs`, `program/mono_collect.rs`, `traits/monomorphise.rs` |
| **CS-3** | 0913 — `default_residual_parameters` at `build_concrete_codegen_view`'s `NotConcrete` arm, the strict re-run, and residual-root routing to template or located refusal; no duplicate view-refusal counter | `non-concrete-producer-obligations.md` §3, §5.2, §7.3 | `program/support.rs` |
| **CS-4** | Complete: the 0779 seam-level polarity cell and truthful source-census comment are live. The historical 0799 wrong-reject no longer reproduces; 0762 and the typecheck arm of 0929 are satisfied by their current guards. | `auto-curry.md` §2–§3; `ownership-inference.md` §18 | `program/mono_collect.rs` (unit + rustdoc census) |
| **CS-5** | 0553 — the `instantiate_demands` reload seed beside `check_forms`, with the M-3 outcome classification and the M-4 synthetic-site rule; the regenerated `public-api.txt` baseline line | `monomorphisation.md` §3.8 (facade `arch`-approved 2026-09-01) | `form.rs`, `lib.rs` (re-export + crate-root rustdoc), `program/mono_collect.rs` (seed entry), `public-api.txt` |
| **CS-6** | 0869 producer — upsert the `WrittenTraitImpl` record into the **writer's** table inside `register_trait_impl`'s existing retain-prior transaction, from the values the shell is built from; re-point the two hand-rolled `impl$` format sites onto `trait_impl_key`; correct the phantom `check_trait_impl` rustdoc citations in `crates/cranelisp-types/src/module.rs` | `traits.md` §3.0.1 (+ §3 step 5, §10 invariant 5a); governed by `design/arch/trait-impl-cache-carrier.md` §§3–4, §8, §9 | `traits/impl_check.rs`, `traits/dispatch.rs`, and the bounded rustdoc-only carve-out of §9.8.3 |

CS-4 shares `program/mono_collect.rs` with CS-2 and is therefore sequenced after it;
it is otherwise independent and may be split across the wave. CS-5 also touches
`program/mono_collect.rs` and follows CS-2 for the same reason; it otherwise depends only
on C1's `MonoDemand`, and it is the C3 half of the C1 → C3 → C6 ordering the 0553 driver
needs (`monomorphisation.md` §3.8.3) — C6 must not land the capture before CS-5 exists.
Wave placement is `sprint`'s.

**CS-6 lands after CS-1 and before C6's N3.** It needs nothing from C1 — the carrier,
the enrolment helper and `trait_impl_key` all landed S119 — so its only ordering
constraint inside C3 is that it shares `traits/impl_check.rs`, and specifically the
retain-prior/rollback arms, with CS-1's funnel conversion and match re-arm. Landing it
second means the record's staging and rollback are written once, in C1's funnel
vocabulary, rather than written raw and re-armed. Downstream it is C6's **H1 gate**
(`design/int/s121-c6-visit.md` §15): until CS-6 lands, C6's restore enrolment iterates a
permanently empty vector and cannot flip
`tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`. `sprint`
sequences C3 before C6 already; CS-6 makes that edge load-bearing rather than incidental.

The former 0799 and F1 observation gates are retired by the S122 current-state evidence
and the landed typed-demand/synthesis path. They must not be revived as implementation
work. The 0779 direct drain-polarity unit and census-comment repair are complete.

### 9.8.3 Source and module-test reservations

Reserved to C3 for the whole sprint; no other stream edits them.

`crates/cranelisp-typecheck/src/**` in its entirety, and specifically:
`adt.rs`, `infer.rs`, `checker.rs`, `checker/test_support.rs`, `scheme.rs`,
`form.rs`, `lib.rs`, `program/{support,mono_collect,finalize,body,register}.rs`,
`traits/{impl_check,monomorphise,dispatch}.rs`,
`ownership/{fixpoint,transfer}.rs`, plus every sibling `tests.rs` under those paths
per the crate `CLAUDE.md` test-home table. Module tests are `dev`'s and stay beside
their production submodule; a new cell goes in the home of the unit it exercises, and
a new shared fixture goes in `program/test_support.rs`, never a second copy.

The two cross-stream arms add no new production file. Their cells land in the homes
their units already have. The producer's three module cells go in
`traits/impl_check/tests.rs` — record ⟺ shell (present on a settled impl, **absent**
after the method-check arm rolls back), same-key re-impl upserts to one record, and the
record's five fields equal the shell's construction values; its fourth acceptance row is
the `format!("impl$…")` grep, a structural check with no cell. The dispatch-side mint
re-point is pinned in `traits/dispatch/tests.rs`, and the alias call-site flip in
`checker/tests.rs` over a `checker/test_support.rs` fixture. That fixture's
`ModuleAliases` is seeded **through `module_alias_key`** — a test that hand-spells
`<owner>.<alias>` is a second mint and a `review` reject exactly as a production site
would be (`design/arch/module-alias-scoped-lookup.md` §7).

**One bounded carve-out in C1's crate.** CS-6 edits
`crates/cranelisp-types/src/module.rs` at four rustdoc lines only — `:240`, `:884`,
`:1570` and `:1587`, each spelling a `check_trait_impl` seam that does not exist —
replacing the phantom with `register_trait_impl`. This is `arch`-approved and
explicitly rides C3's producer change-set (`trait-impl-cache-carrier.md` §9), because
`arch` owns the types crate's voice and a round-trip would stall the wave. It is
rustdoc text: no item, signature, field, serde shape or `public-api.txt` line moves
(§9.8.4). **`:1587` is a fourth occurrence the contract's enumeration does not name**;
it is the same phantom in the same doc comment family, so C3 corrects it with the other
three and reports the enumeration gap to `arch` (§9.8.6). Any edit to that file beyond
those four lines is out of the carve-out and is the §9.8.7 reject.

**Three source-hygiene corrections reserved to this visit** (each verified stale at
HEAD, each inside a file the visit already opens):

1. `checker/test_support.rs:547` — the rustdoc spells `(deftype Box [:a v])`, which
   spec §5.2.4 now makes **illegal**: the head is omitted, so it binds no
   type-variable name and a written `:a` field type has no parameter to resolve
   against. Correct to `(deftype (Box a) [:a v])`, matching what the function
   actually builds. *(The analogous comment in the types crate —
   `crates/cranelisp-types/src/heap/value_layout_tests.rs:323`,
   `// (deftype Box (Box [:a value]))` — is the same error in C1's surface and is a
   **handoff, not a C3 edit**; its sibling at `:383` is already correct.)*
2. `program/mono_collect.rs` — the drain census now points to `auto-curry.md` §1.2,
   which carries the enumerated set with its per-seam reason, instead of duplicating
   drifting file-and-line citations.
3. Two false claims found while verifying: `program/support.rs:273-276`'s *"Always
   returns `Some(view)`"* against a `Result<Option<_>, _>` signature whose callers
   branch on `None`, and `traits/monomorphise.rs:1154`'s `#[allow(dead_code)]` on a
   function called from `monomorphise.rs:91`.

### 9.8.4 Public API, schema and baseline effects

| Surface | Effect |
|---|---|
| `crates/cranelisp-typecheck/public-api.txt` | **one addition** — FIXME 0553's `instantiate_demands` reload seed (`monomorphisation.md` §3.8). **`arch`-approved 2026-09-01**; the contract is pinned at `design/arch/bounded-contexts.md` §2 and the regenerated baseline rides CS-5's change-set per `design/arch/CLAUDE.md` §Public-API discipline. Nothing else in the visit moves it. |
| `crates/cranelisp-types/public-api.txt` | **zero C3 delta.** Every carrier the visit needs is C1-published, including `substitute_module_alias`'s new signature and the added `module_alias_key`, which ride C1's single regeneration (`module-alias-scoped-lookup.md` §6). `WrittenTraitImpl`, `trait_impl_key` and `enrol_written_trait_impl` are already on the baseline from S119. Any future `MonoExpr::lenient_from_expr` deletion remains a separate C1/`arch` public-surface decision; typecheck's retired aggregate neither licenses nor blocks it. |
| `crates/cranelisp-types/` source | **rustdoc-only, four lines, `arch`-approved** — the §9.8.3 carve-out. No item, signature, field or serde shape moves, so the baseline is untouched and no regeneration is owed. Everything else in that crate stays C1's. |
| `CACHE_SCHEMA_VERSION` | **zero C3 delta.** C3's window is 24→25, C1's. (Sprint 121 later opened two further separately-approved windows outside this visit: 25→26 for result-context specialization, and 26→27 for the ownership-result correction — `ownership-inference.md` §19.9. Neither is C3's and neither reopens this row.) Both halves of the concreteness obligation are cache-visible meaning changes and are covered by that window's wholesale pre-25 invalidation. The 0869 producer takes **no further increment** — `written_trait_impls` is already serde-mandatory at 24 (`trait-impl-cache-carrier.md` §6) — and the 0798 cure has **no serde contact** at all, because `ModuleAliases` is unserialized session state. A second bump inside C3 is a plan violation to report. |
| `ABI_VERSION` | **zero C3 delta**, and read-only. 9→10 is C7's, for the FIXME-0934 IO node. |
| warm-cache acceptance evidence | taken **after** C4, never between the C1 bump and the C4 IO-layout flip ([S121 lifecycle design at checkpoint `dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md) §9), and never from a cache built before CS-6. A sidecar written in that interval is schema-25-valid with an **empty** `written_trait_impls` and restores impls-lost if trusted — `trait-impl-cache-carrier.md` §6's named residual, whose disposition is regenerate, never a compatibility shim. |

### 9.8.5 Per-filing disposition

| FIXME | Class | Disposition |
|---|---|---|
| **0924** | satisfied; filing retired | Slotless synthesis templates and concrete-use rematerialisation are live. `non-concrete-producer-obligations.md` §8 |
| **0867** | retired false obligation | Differently named constructor arms are sums; their payload labels mint no accessors. CS-2 retains product-only A-MINT and the negative sum boundary. §4; `fixme-0365-field-accessor-dotted.md` §1.6.7 |
| **0913** | satisfied; filing retired | Constructor-preserving residual defaulting and strict retry are live; exact marginal-balance evidence passes. §8 |
| **0935** | satisfied; filing retired | The collectors feed canonical storage identity into typed `MonoDemand`; carrier units cover bare accessor and renamed import. §8 |
| **0916** | producer gate only | C3 produces the concrete instances; C4 reads the census to zero and only then flips its fabricating arm. §5.1 |
| **0929** | typecheck arm satisfied | Residual parameter frames stay keyed, are excluded from the ownership universe and publish no summary. Remaining census arms retain their owning contexts. `non-concrete-producer-obligations.md` §8 |
| **0936** | evidence-only | the roster is a projection over `Life::Template{body: UniformRust}`; C3 supplies the derivation, `qa` relabels the plan row. §5.4 |
| **0553** | live implementation | `instantiate_demands`, seeding the existing worklist. `monomorphisation.md` §3.8. **The visit's one public-API addition, `arch`-approved 2026-09-01** (contract at `design/arch/bounded-contexts.md` §2); lands as CS-5. |
| **0799** | current behavior; filing retired | The supplied-free then-apply and residual-function control pass 2/2 with no production change. `auto-curry.md` §2 |
| **0779** | satisfied; filing retired | The direct seeded-carrier unit detects both drain polarities; settled recheck seams remain `Final` by construction rather than six behavioral proofs. `auto-curry.md` §3.2 |
| **0777** | current-state wash | §17.2 row 4, §17.3, §17.4 and §17.7's rider corrected against the probe result and the landed fix. `ownership-inference.md` §17 |
| **0762** | filing retirement + successor | the raw `&args[k]` is gone; the surviving obligation is the P25 grade on `unwrap_or(Origin::Fresh)`. `ownership-inference.md` §18.3 |
| **0794** | filing retirement | falsified at source — the S117 canonical mint landed. Evidence tail is `qa`'s. `qualified-trait-impl.md` §7 |
| **0912** | retired in C2 | explicit field types and parameters are enforced before typecheck; C3 retains only valid generic product/sum coverage. §4.4 |
| **0776** | not C3's | the register row stays `arch`'s; C3 discharges the two in-crate instances by enumerating each seam set with its per-seam reason. `auto-curry.md` §3.1; `monomorphisation.md` §11.8.10 |
| **0869** | satisfied; filing retired | Writer-side records, restore enrolment and the warm-cache sibling-dispatch guard are live. `traits.md` §3.0.1; `trait-impl-cache-carrier.md` §§3–4, §9 |
| **0798** | consumer arm only (filing stays C6's) | CS-1 flips the crate's one `substitute_module_alias` call to pass `state.current_module`. The lookup, the mint and the visibility rule are C1's; the writers and the evidence are C6's. Zero design freedom here — the flip is forced by C1's signature. `module-alias-scoped-lookup.md` §4, §5 |

### 9.8.6 Handoffs out

- **C4 (backend).** Concrete, canonically named codegen inputs; the instance census
  partitioned by `CallableOrigin` with its exact-zero criterion and its owed negative
  detection leg (`non-concrete-producer-obligations.md` §5.1); the release of 0916's
  producer gate; `Realization::{Body, FacadeOf}` consumption; the remaining
  `lenient_from_expr` consumers (`backend/test_support.rs:239,:755`); the three C4-owned
  fabrication arms in the §5.3 census; the codegen half of 0553's entry point, which is
  nothing new because the instances are ordinary concrete entries.
- **C6 (binary).** The delivered 0553 driver captures the live mono-variant
  demand set before the Replace commit through
  `src/worker.rs::capture_reload_instantiation_demands` and re-requests it in
  the ordinary source-or-demand transaction after reload. It has retired the
  former expression-driver replay (`monomorphisation.md` §3.8.3;
  `design/int/s122-closure.md` §2). The `result-owner.md` §1.1.1 scope correction 0913
  names; the int-layer fabrication trio in the §5.3 census. **Blocker H1 discharged by
  CS-6** — from CS-6's landing, a writer's table carries one record per `(type, trait)`
  it implemented, so N3's enrolment loop has traffic and the discriminator is reachable;
  N3 opens on CS-6, not on the whole of C3. **Blocker H2 discharged by C1 plus CS-1** —
  the scoped lookup and its mint are C1's, and typecheck's consumer is flipped, so N3's
  writer flips and the `alias_key` deletion have no typecheck dependency left.
- **C1 (`cranelisp-types`).** The `value_layout_tests.rs:323` comment correction
  (§9.8.3). Any later `lenient_from_expr` deletion requires its own public-surface
  case; C3 supplies no aggregate counter gate.
- **`arch`.** One enumeration correction: `trait-impl-cache-carrier.md` §9 names three
  phantom `check_trait_impl` rustdoc sites in `module.rs`; there are four (`:1587`).
  C3 corrects all four under the approved carve-out — the handoff is the record, not the
  edit. (`interfaces.md` §"Written-impl cache carrier" is already corrected and needs
  nothing; `design/int/s121-c6-visit.md` §15 H5 still lists it as owed.)
- **`qa`.** The three §4.3 cells; the §5.1 backend criterion; the NC-R relabel
  derivation; the §7.5 negative column. The supplied-free-variable Q10 pair is complete,
  and 0794 is retired against current source and its existing evidence. **Plus the two
  arms' evidence:** the producer rows of `trait-impl-cache-carrier.md` §8 are C3's own
  module tier and are listed in §9.8.3, but their e2e twin — the committed
  failing-not-ignored
  `tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch` — flips only
  after C6, so its plan row stays a C3→C6 span; and the 0798 matrix, scoped-isolation
  and negative-twin cells of `module-alias-scoped-lookup.md` §7 sit with C6's H3, with
  no typecheck-tier cell owed beyond the CS-1 call-site test.
- **`sprint`.** Two plan reconciliations: C3's filing row (`sprints/SPRINT.md:177`)
  does not carry 0869 or 0798, and `:185` records 0798 as moved C3→C6 without the
  call-site arm the `arch` ruling returned. C3's directive at `:229` already asks for
  the written-trait carrier to be populated, so the scope is not new — only the row is
  stale. `design` does not edit sprint plans.
- **U8.** The stdlib consequences of the accessor widening — five types gaining 13
  canonical accessors, and the cross-module `head`/`rest` bare-alias contest.

### 9.8.7 Falsifiers and `review` rejects

- A second lifecycle vocabulary anywhere in this crate.
- A `CACHE_SCHEMA_VERSION` bump inside C3, or any `cranelisp-types` edit other than the
  four rustdoc lines §9.8.3 carves out — including a `public-api.txt` regeneration for
  that crate, which the carve-out cannot produce and therefore must not accompany it.
- A `WrittenTraitImpl` field re-derived rather than taken from the values the shell is
  built from — a re-resolution of the trait or target, a parse of a mangled method
  spelling, or a second read of `state.current_module` after a per-method module switch.
- A record written outside `register_trait_impl`'s retain-prior transaction: appended
  before the shell is staged, left behind when the method-check arm rolls the shell back,
  or committed to a table other than the writer's.
- A same-`(type, trait)` re-impl that appends a second record instead of upserting.
- A third `impl$` construction site, or either of the two surviving after CS-6. The
  acceptance grep is `format!("impl$…")` outside the mint; constant `impl$…` strings in
  test files are assertions about the key's shape, not mints, and are deliberately left
  standing.
- Any typecheck-side alias-key construction or segment walk — including a fixture that
  spells `<owner>.<alias>` by hand instead of calling `module_alias_key`.
- A `storage_key` spelling swap at the collector sites without the typed demand.
- A `$Type$Arg` widening of `mangle_trait_method`, or any second mangle grammar.
- An accessor instance produced by a body re-check rather than re-synthesis.
- A defaulting that yields a bare `Int` from a constructor-rooted type, defaults a
  constrained variable, or defaults a residual occurring in a declared parameter type.
- Any typecheck change attributed to retired 0799; current supplied-free behavior is already
  covered by `auto-curry.md` §2's public pair.
- A codegen-view counter treated as safety evidence even though the same path
  already returns a located refusal and the counter has no actionable reader.
- A stale reload demand reported as `Err`, a second result carrier or warning category
  invented to report one, or a `Span` other than `Span::SYNTHETIC` on a reload demand
  (`monomorphisation.md` §3.8 M-3/M-4).
- A golden-CLIF movement outside the F0/F1/F2 frames and the attributed
  `f4_sudoku.clif::user::Grid.cells` re-baseline.
- Any typecheck-side declaration-shape reject for a spec §5.2.4 form.

---

## 10. Subordinate topic docs

| Topic | Doc | Status |
|---|---|---|
| Algorithm-W & substitution strategy | `inference.md` | Current |
| **Approved use-site candidate selection — syntactic roles, isolated HM trials, fixed-point settlement, constructor scrutinees, canonical writeback and diagnostics** | **`use-site-candidate-selection.md`** | **APPROVED (user decision 2026-09-02; S121 W3).** One private body-run carrier holds HM anchors plus surviving terminal FQ identities; trials clone narrow inference state and commit only by replay after unique selection; stalled peers are ambiguous without combination search. Reuses `Resolved`, `MethodResolutions`, `VarRef`, `ApplyRef`, and `pattern_ctors`; adds no public API, schema/ABI, or crate edge. |
| **Checked-body publication — retain checked AST/callees privately until the settled strict-view window** | **`checked-body-publication.md`** | **USER-APPROVED 2026-09-03 for the ledger and the complete §11 state-cleanup basket.** One body-occurrence-keyed module ledger replaces early `Life` settlement as transient storage, with no public/schema/ABI effect or second drain. §9 consumes the rule established by `spec/05-definitions.md` §5.13 and `spec/08-modules.md` §8.6.4. The bounded cleanup basket folds ledger-owned signature/scope/callee facts, introduces one body frame, carries `MethodResolutions` whole, removes only the per-form `expr_types` duplicate, and deletes unread `redef_slots`; dispatch grouping, a general recheck sandbox and active-map deletion are deferred. |
| Trait registry, impl recording, monomorphisation, default methods | `traits.md` | **Current.** S121: §3.0.1 carries CS-6's writer-side `WrittenTraitImpl` placement inside `register_trait_impl`'s transaction, and §10 invariant 5a the record ⟺ shell bijection; the cross-crate contract they consume is `design/arch/trait-impl-cache-carrier.md`. |
| **S116 single `method_sig` tail — transactional type/body classification, default inference, occurrence, conformance and re-impl** | **`s116-method-signature-resolution.md`** | **DESIGN (S116 Phase 3; implementation pending). One unresolved carrier and one classified sum; shares schema 23; no typecheck public-API delta.** |
| **Monomorphisation from roots — structural slot-gate first (slot ⟺ `is_concrete()`) + systematic mono + the ambiguity backstop** | **`monomorphisation.md`** | **Current** (Sprint 84, Cluster A; **re-grounded mid-Phase-5** on the structural-slot-gate-first model — user ruling 2026-06-16, resolved FIXME 0376). Pins: the corrected slot gate (`constraints.is_empty()`→`is_concrete()`; the new slot-less `UserFnState::Polymorphic` arm + the /arch FIXME 0377 + cache bump); the reachable-instance worklist EXTENDING the Tier-1/1.5 `pass4_monomorphise` spine (FIXME 0374, Wave-0-narrowed to the `(Box a)`-field-through-HOF gap); the ambiguity check **demoted to a secondary backstop** (FIXME 0373 ii); the 0344 fold canary discipline; the unit-test seams; the termination argument. **S90: §9 added — the FIXME 0432 multi-clause-`defn`-self-call panic→clean-error root fix** (R2 layer a; an early `is_concrete()` gate at the `monomorphise_call` P1 mint seam, before `build_mangled_name`, converging REPL and `--run` on the existing ambiguous-type diagnostic — the agentic-REPL Pillar-3 prerequisite). Cites Principle 20 + BC §7, `traits.md §7` (as-built pipeline it completes). **S112: §11 added — multi-sig = separate mutually-recursive functions (leg a, FIXME 0642)**: the settled §5.1.2 back-flow (collapse the two-phase ambiguity scan to ONE post-drain pass; order concrete mangling after the self-call drain; §9's "NOT a multi-clause inference change" REVERSED), the constrained-poly × multi-sig cell (user-ruled IMPLEMENT — each constrained clause a one-variant template on the standalone mono path; `ConstrainedFn` field unchanged, rustdoc via FIXME 0644 → /arch; no schema bump), the `OverloadVariant.mangled_name` determinism (`mangle_type`'s constant `Var`), and leg-(c) framing (resolved-return-dispatch `resolved_targets` producer attribution). Cites Principles 7/11/24. **S121: §3.8 added — the FIXME-0553 monomorphisation reload seed `instantiate_demands`** (one public free function beside `check_forms`; facade `arch`-approved 2026-09-01, contract at `design/arch/bounded-contexts.md` §2): a seed of the existing worklist and never a second engine (M-2); a stale post-reload demand DECLINES to a `CheckResult` warning with no new carrier, while `Gap` and invariant-gate breaks stay errors (M-3); reload demands carry `Span::SYNTHETIC`, so no span-keyed carrier can alias; complete substitutions reconstruct result context directly (M-4). **S122: §3.8.6 completes the same entry with its existing private ownership pass after the successful full drain**, preserving the strict universe, toggle/refusal absence and staging-aware publication; no public or schema delta. One typecheck `public-api.txt` line; zero `cranelisp-types`, schema, ABI and backend effect. Cites Principles 7/17. |
| **The non-concrete producer obligations — typecheck's half of the release contract (FIXMEs 0924 + 0913 + 0935; 0867 retired; gates 0916; typecheck arm of 0929/0936/0912)** | **`non-concrete-producer-obligations.md`** | **RULING** (S119 Phase 3 round 2; **re-grounded S121 Phase 3** on the adopted unified lifecycle and amended by the 2026-09-02 product-only accessor ruling). Governed by `design/arch/symbol-table-lifecycle.md` §§3–7 and `design/backend/non-concrete-release-contract.md` (R-2/R-3, §4 faces 2/3/5, §5.2/§5.4) — where they disagree, the rulings win. Pins: **P-1**, now table-enforced — `Life::Concrete` is constructed only by C1's `settle_concrete` funnel, so the crate's obligation is to route five populations through it and delete **four** hand-mints (the S119 census named two; `adt.rs:172-181` and `monomorphise.rs:680-697` were outside it); **P-2** one key encoder (`InstanceLink::instance_key`), with the FIXME's `mangle_trait_method` `$Type$Arg` widening **rejected as lossy**; **A-MINT** for polymorphic product accessors (re-synthesis over the template's `SynthSpec`, never a body re-check); the F2 scheme-truth fix; **0935 closed by the typed `MonoDemand`**, not by a spelling swap at the three collector pushes; the product/sum negative boundary that retires 0867's widening; and 0913's **defaulting step** — L-1/L-2/L-3, self-checked by re-running the strict builder, with the S119 counted-placeholder **retired** because `Realization::Body` carries its view non-optionally. The backend instance census retains its exact-zero release criterion; the separate keyed ownership-seed observation remains, while the unconsumed codegen-view counter is retired (§5). Zero `cranelisp-types` and zero typecheck public-API delta; the S119 cache-schema question is **answered** — one window, 24→25, C1's under [the S121 lifecycle plan at checkpoint `dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md) §9. Cites Principles 5/6/7/18/20/24/25/26. |
| **Type-signature match predicates (Pillar 3 importable-symbol search) — exact (alpha-equivalence) OR partial (structural-contains)** | **`signature-match.md`** | **Current** (S90 design; **S91 SHIPS** — Pillar 3 implementation, the 0432 gate cleared S90; S91-confirmation box at the doc head: algorithm HOLDS, the two predicates are the sole baseline movement, nothing stale, the §2.3 `TyConApp`-head canonicalisation note pulled forward for `/dev`). **Re-pinned S90 Phase 3 (commit `c699045`): MVP match is now exact OR partial** (superseding exact-only). Pins TWO pure free-function predicates the `int` indexer calls, **both exported from `cranelisp-typecheck`** (`/arch` Option A, §11.4/§11.8 — two additive `public-api.txt` lines at impl time): (1) `signature_matches_exact(&Type, &Type) -> bool` — alpha-equivalence up to consistent bijective var renaming (whole-tree); (2) `signature_matches_partial(query: &Type, candidate: &Type) -> bool` — **structural-CONTAINS**: query appears as a sub-tree of the candidate up to alpha-renaming (`_exact ⟹ _partial`), a containment walk reusing the `_exact` alpha-equivalence machinery, **NO unifier**. Both canonicalise-then-`==` via reused `collect_var_ids_ordered` (Principle 7); FQ-ADT discipline. Structural-contains needs NO wildcard token → `/spec` query-syntax consult NOT triggered. Hoogle subsumption (hole-instantiation + ranking) recorded as an explicit deferred `/typecheck` follow-up (NOT this sprint). Cites `repl-embedded-agent.md §11.2/§11.4/§11.8` (R3/R6/R8). |
| **Field-accessor `Type.field` (canonical) + impl-time collision rule (FIXME 0365) — INVERTED model** | **`fixme-0365-field-accessor-dotted.md`** | **Current** (Sprint 91, Thread C; **canonical/alias direction INVERTED S91 Phase-5, user ruling 2026-06-26, design-only pending user confirmation**). **`Type.field` (`Box.v`) is the CANONICAL field accessor — uniformly real + Public + listed (qualified-display convention); bare `field` is a convenience `Import` alias → canonical, ambiguous when two types share the field name.** Synthesis registers the real `Def` under the canonical key + the alias under the bare key (as-built reversed); the poison re-mint helper + per-case visibility flip are **deleted** (net code reduction). **Item 1 — typing**: reads the canonical `Def.scheme` (return arm = `FieldType`); bare alias chain-follows to it — one scheme, one compiled function (duplicate-codegen fix preserved); cross-module strictly better (canonical uniformly Public → `m/Box.v` resolves in every case, no cliff). **Item 2 — impl-time collision**: pre-flight validation in `register_trait_impl` (`impl_check.rs:18/79`) rejects a trait `impl` whose method name equals a canonical field-accessor name of the target type, before the impl registers (Principle 18); enumerates via `committed_accessor_kind` (`adt.rs:677`), union-view cross-cluster — the contested-field case simplifies (no `accessor_owning_types` consult; canonical entry is unconditional). §1.5 visibility-by-arm rule **SUPERSEDED** (banner-kept for audit). **Zero `public-api.txt` movement, no `cranelisp-types` change** (internal key relabeling). FIXMEs: 0439 (`/spec` reframe §5.2.6/§8.5.2), 0438 (`/repl`, updated for inverted listing). Cites §8.5.2/§5.2.6/§7.3.1; Principles 6/7/16/18. |
| **Ownership inference — the interprocedural lifetime/flow pass** | **`ownership-inference.md`** | **CURRENT; the pass is as-built since S102 and revised through S121.** Read **§19 first for S121** — the ownership-result correction: `ResultMode` gains a real ⊤ (`MayAliasAny`, user-approved 2026-09-07, +1 types public-API line, `CACHE_SCHEMA_VERSION` 26→27, platform ABI unchanged); the lowest-index representative retires in favour of the reaching-parameter set (§13.6(c) falsified by measurement, twice — a non-convergent permuting self-call and a caller publishing a false `Fresh`); and a cluster whose analysis does not converge **publishes nothing**, retiring the `top`/`reset_to_top` literal whose present-`Fresh` was the f4 use-after-free (§13.6(h) rewritten). Origin (S100 Phase 3 stage 2): governed by the master spine `design/arch/ownership-inference.md` (where they disagree, the spine wins). Designs the post-monomorphisation per-cluster fixpoint (a `pass5_ownership` post-pass after `pass4_monomorphise` + the callee write-back, riding `Def.callees` + `resolved_call` — one graph, two consumers with R3), the internal `OwnershipSummary` (param modes + result mode + flow/spark-ops facts; FIXME 0467 proposes the boundary-carried subset), borrow-through-projection with provenance roots (escape ⇒ materialize-at-edge; last-use root-extension seam left backend-local), the op-wise per-cell confinement join with potential-fork over-approximation (`Transferred` carried internally, collapsed to `Crossing` in increment I — promotion measurement-gated), canonical-executable-keyed instantiation-summary dedup + session memo, the increment-II write-path rulings (dynamic rc==1 default; static uniqueness scoped to the single-syntactic-use fresh-chain subset, success metric = proof chaining; mode-in-key measurement-gated), the moded-body + Decision-24-value-wrapper answer to the R2 HOF question (join-to-Owned rejected), and the declared-primitive fact-table consumption (leaves seed the fixpoint; `ring2-rc.md` §3.3 audit is the seed). **S102 Phase 3: §13 added — the increment-I change-set staging (Sprint 102 Block B2)**: CS-A dependency pin (the exact `/arch` `cranelisp-types` v11→v12 needs list, incl. conservative-read accessors, `abi_eq`, the shared-slot primitive-fact carrier, and the toggle-relocation ask), ordered change-sets CS-1–CS-4 over a new `src/ownership/` submodule cluster, the 0470/0472 graph-feed verification (template-grain feed demoted to seeding-order hint; fixpoint re-entry rides walk-harvested `DepSet` edges), the fact-table coverage verdict (one gap → FIXME 0504; `PrimitiveExtern` scope cut named), the toggle-set ⇒ **emit-no-summaries** pin, §13.6 refinements (internal summary type superseded by `ModeSummary`; post-convergence fact walk; multi-path `ResultMode` join; symbol-keyed provenance + shadow rule), and the Principle-23 scenario matrices carrying the 0497 rider. |
| **TypeExpr resolver convergence — the four-mirror single-source refactor (FIXME 0590)** | **`type-expr-resolver-convergence.md`** | **LANDED S110** (commit `5ed07d60`, in HEAD; recorded DELIVERED in `sprints/archive/sprint-110.md`). The four parallel `TypeExpr` resolvers (`resolve::resolve_type_expr` + `traits/type_resolve.rs` ×3 + `form.rs::check_type_expr`'s `collect_type_var_ids` pre-walk) converged onto the ONE `resolve::resolve_type_expr` behind a `TypeExprCtx` (`resolve.rs:33/69`, verified S115); the mirror functions are DELETED (collapse comment `traits/type_resolve.rs:154–157`); the never-error `Named` fabrication arms are GONE — `resolve_named` ERRORS on an unknown name; `form.rs::check_type_expr` uses mint-on-miss (`form.rs:413`). **FIXME 0590 was a ZOMBIE record** — resolved S110, falsely re-dispositioned S113/S114 ("convergence has not happened") over correct code, driving phantom S114/S115 work (audit `cranelisp-typecheck-s114.md` §2.2a, R-1). **DELETED at S115 Phase 1** (audit-disposal exception; residual rustdoc sub-item verified cured, `resolve.rs`/`checker.rs`). There is **no `_hkt` never-error latent-defect suspicion** — that was the phantom's framing. No S115 "0590 deployment" slot exists. `type-expr-resolver-convergence.md` is the LANDED design record. |
| **Typed resolution carrier — the `VarRef`/`ApplyRef` producer side (S114 Track A; S117 builtin-pair refinement)** | **`typed-resolution-carrier.md`** | **CURRENT; S117 §16 REFINEMENT PENDING IMPLEMENTATION.** The landed S114 carrier flip makes Var/Apply resolution total and typed. S117 W3a adds the narrow builtin identity correction: terminal builtin resolution returns one internal `{jit_name, storage_fq}` product; `ResolvedCall::BuiltinFn` keeps its bare shared ABI unchanged while every builtin settlement site writes `ApplyRef::Dispatch(storage_fq)` directly from the same resolution. The former bare-name `builtin_storage_fq` re-resolution and default-to-`primitives` path retire. No public API, cache/schema, shared-type, backend, or runtime change. Cites Principles 5/6/7/17/19/20/24/26. |
| **Return-type-poly ambiguity — the unresolved-dispatch signal (R16/R17)** | **`return-poly-dispatch-signal.md`** | **DESIGN** (S110 Phase 3; coordinated typecheck+int change-set). The row-16/17 error-quality defect (bare `(zed)` leaks `__expr`-no-GOT-slot instead of the clean §3.11 message). Signal = a return-poly dispatch UNRESOLVED after final subst, grounded in the dispatch OUTCOME (no impl selected), NOT surface-type concreteness (which false-positived on `(add2 3 4)` in the S109 revert). typecheck rejects ordinary body positions directly; the entry/eval RESULT position (`main`/`__expr`) it cannot reject (Principle 19 — no entry designation), so the signal crosses to int via a transient `CheckResult` field (carrier escalated to `/arch`, FIXME 0611). Cites Principles 24/19/7/18. |
| HKT (`Type::TyConApp`, `check_hkt_impl_method`) | `hkt.md` | **Current** (**S112 leg b, FIXMEs 0628+0639**: §5.1/§5.4 reconciled to the settled trait/impl model — kind derived ONCE at `deftrait` registration [parenthesized head + never-applied con_var ⇒ REJECTED at declaration, §7.2.1]; consumers read `TraitDeclInfo.type_params`, never scan usage [Principle 24]; the `register_trait_decl` guard fix roots the `:a 7` display defect; the settled echo-the-head impl form + the ONE §7.3.5 Case-3 kind-check seam consuming `TraitImpl.head_con_var`). |
| ADT type checking (constructors, exhaustiveness) | `adt.md` | Current |
| **Auto-currying — detection, settlement, and the drain seams** | **`auto-curry.md`** | **Current.** Records the as-built exits of `infer.rs::try_auto_curry`, the enumerated six-seam drain table and the current §4.6.3 rule that residual monotype variables stay in the same inference context. S122's supplied-free then-apply/residual-function pair passes 2/2, retiring 0799 without a production change. The direct seeded-carrier polarity unit closes 0779; the four recheck seams remain `Final` by construction rather than by six independent behavioral proofs. |
| AST annotation (Steps 1a/1b) — types and resolved calls co-located on AST | `ast-annotation.md` | Current |
| IO ADT typing | `io-types.md` | Current |
| **`check_form` per-form API** | **`check-form-api.md`** | **Stale on the `&mut SymbolTable` signature — superseded by §6.** The algorithm shape (Pass-1/Pass-2, accumulator) survives, and `program/finalize/tests.rs` traces its result-identity cases here, so the doc is retained as that anchor. |
| **`render_type` rendering contract (S87 FQ-walk consolidation)** | **`s87-fq-walk-consolidation.md`** | **Retained for §2.4** — the byte-for-byte variant × convention table three `cranelisp-types` unit tests trace to. The rendered surface itself is `arch`-owned (`design/arch/bounded-contexts.md` §"Type rendering"); rehoming the contract there is `arch`'s, and the doc stays until it lands. |

Seven S50–S76 working records were **deleted at S122**; `design/typecheck/CLAUDE.md` §"Redirections" maps a citation to its canonical destination.

---

## 11. Open questions / standing design items

The S63-era migration questions this section once tracked (FIXME 0008 free-function shape; FIXME 0098 boundary-type placement) **landed** — `check_forms` is the free function, `CheckError`/`CheckResult`/`DispatchGap` are crate-owned (§2.1). Neither FIXME exists in `design/arch/fixmes/`. The `MacroInMem`/`Gap`-post-state/`TypeCheckEnv`-generics/`Code`-default questions this section proposed were all framed against the retired facade doc and are **withdrawn** — the boundary they questioned is now the source rustdoc + `public-api.txt`, and the as-built shape (`check_forms` over `SymbolTableAccess`, crate-owned `CheckError`) answers them: `ResolutionGap` producer-attribution is a `cranelisp-types` rustdoc concern (`/arch`), not a typecheck open question; the generic-defaults and `Code` questions dissolve because typecheck works against `SymbolTable<C, L>` generically and never names a downstream `Code`.

Standing design items (not FIXMEs — this doc's own forward pointers):

- **`check-form-api.md`'s surviving Pass-1/Pass-2 account belongs in `inference.md`.** The doc is held only by the `program/finalize/tests.rs` `// spec:` anchors; once those re-point, the fold completes and the doc retires. (Its two S122 siblings — the DashMap and stateless records — are already deleted, §6.5.)
- **`finalize.rs` re-budget + `program/tests.rs` split** — FIXME 0722 (this sprint's `/dev` item), `program-decomposition.md` §3.

---

## 12. Decision register (typecheck-relevant)

Per `design/arch/CLAUDE.md`'s active-vs-legacy split: active Decisions carry forward-handoff or pre-implementation work; legacy Decisions are fully embodied in the architecture. Decisions 15 and 17 have been retracted (per `design/arch/CLAUDE.md` Decisions section); their constraints survive as embodied invariants in the resolution machinery and prelude loading, called out below.

### Active

| # | Decision | Takeaway for typecheck | Note |
|---|---|---|---|
| 30 | Form-by-form scheduler; mutual-import deadlock | REFRAMED by Decision 38 — single-worker-per-module is now scheduler ordering, not lock safety | active (forward-handoff — single-worker invariant still in flight) |
| 41 | `compile_to_module` per-symbol; `Code` moves to `cranelisp-backend` | Indirect — typecheck doesn't reference `Code`; the facade's `SymbolTable<Code, ()>` parameter pin is a documentation contract that should clarify per §11 | active (peripheral; pre-implementation amendment to 31 + 35) |

### Legacy — embodied

| # | Decision | Takeaway for typecheck |
|---|---|---|
| 1 (legacy — embodied) | 7+1 crate DAG | typecheck is one crate, no leakage |
| 2 (legacy — embodied) | `cranelisp-types` data-only | typecheck imports types from there, exports nothing of its own to the boundary |
| 6 (legacy — embodied) | `Type::from_name()` | typecheck uses it for primitive type lookups |
| 8 (legacy — embodied) | `MacroExpander` trait deleted | macros expanded before typecheck sees the AST |
| 9 (legacy — superseded) | CompiledModule decomposition | RETRACTED in part — `TypecheckProduct` / `CodegenProduct` dissolved into `ModuleEntry::Def`; framing superseded by Decisions 22, 25, 38, 41 |
| 14 (legacy — embodied) | TC emits `TraitMethod`, backend maps | typecheck emits `ResolvedCall::TraitMethod` uniformly |
| 19 (legacy — embodied) | Constraint propagation in `generalize` | Scheme.constraints populated from active type vars |
| 21 (legacy — embodied) | TC-sourced call graph on `ModuleEntry` | `CheckResult.callees` per-symbol; `int` writes onto `Def.callees` |
| 22 (legacy — embodied) | `defined_symbols()` predicate | typecheck writes entries that satisfy/fail this predicate; no parallel store |
| 33 (legacy — embodied) | Structural decls on `SymbolTable` fields | typecheck reads `imports`/`exports`/`platforms`/`submodules` from the symbol table itself; no `ModuleStructure` parallel store |
| 38 (legacy — embodied) | `SharedState` formal definition; per-symbol mutability | `check_forms` takes `&mut SymbolTableAccess` (staging) + `&SymbolTables`; mutation flows through inner DashMap per-entry locks; `write_structural_decls` is the only `&mut SymbolTable` method |
| 39 (legacy — embodied) | Per-defn source on `Introspection.source`; `defn_order: Vec<Symbol>` on `SymbolTable`; errors carry `ErrorLocation` | typecheck adds `defn_order` field, populates `ErrorLocation { fq, span, … }`, leaves `context` to formatter |

### Retracted — invariants preserved

- **Decision 15 (retracted; outcome embodied)** — Ring 0-1 BuiltinFn coexists with TraitMethod. Both resolution paths still live in `resolve.rs` + `traits.rs`; the rationale is now embodied in the resolution machinery rather than tracked as an explicit Decision.
- **Decision 17 (retracted; outcome embodied)** — Core traits in `.cl` files. `register_builtins` does NOT register `Num`/`Eq`/etc. — those load via the prelude. The constraint is enforced by the current shape of `register_builtins` (synthetic `primitives`/`macros` modules only) rather than by an explicit Decision.

Decisions not listed (3, 4, 5, 7, 10–13, 16, 18, 20, 23–29, 31, 32, 34–37, 40, 42) bind cross-crate concerns (type IDs, span shape, RC discipline, GOT model, Code-enum placement, cache schema, function symbol naming, runtime/IO trampoline relocations, platform error shape) that typecheck doesn't surface directly.

---

## 13. Cross-references

- `design/arch/CLAUDE.md` Decisions 38, 39 (legacy — embodied; NEW MODEL framing); 1, 2, 6, 8, 14, 19, 21, 22, 30 (READ THROUGH 38/39 lens), 33 (structural decls on SymbolTable), 41 (active — peripheral). Decisions 15 and 17 retracted; their constraints embodied per §12 "Retracted — invariants preserved"
- **Public surface (canonical):** `crates/cranelisp-typecheck/public-api.txt` (checked baseline) + `crates/cranelisp-typecheck/src/lib.rs` crate-root `//!` (per-item contracts) + `design/arch/bounded-contexts.md` §2 (Typecheck — the BC, cross-context invariants 1–10). **All nine `design/arch/facades/` docs are RETIRED** (S69–S81; the directory holds only S69/S70 audit records) — do NOT cite `facades/typecheck.md` / `facades/types.md` / `facades/int.md` as normative.
- `crates/cranelisp-types/src/module.rs` rustdoc — `SymbolTable` shape consumed (Decision 33 structural decls; the `Warning`/`ErrorLocation` shapes for §8)
- `design/int/` design docs + `src/` rustdoc — the `int` caller of `check_forms` + the gap-orchestration retry loop (the retired `facades/int.md` narrative → BC §6 + `design/int/`)
- `crates/cranelisp-frontend/src/lib.rs` //! preamble + `bounded-contexts.md` §1 — peer crate's public-surface contract (`SymbolTables` alias canonical home is `cranelisp-types`)
- `design/arch/principles/` — architectural principles cited above
- `audits/cranelisp-typecheck-s114.md` — the live rolling audit (`/audit`); its recommendations drive §3.2/§4.2 (R-2 is the origin of this doc's S115 rewrite; R-3 = FIXME 0722)
- `audits/typecheck-20260423.md` (+ `-{current,target}-state.{mmd,svg}`) — HISTORICAL prior audit; its six remediations are retired (their duplicate-pipeline/walker/tail findings resolved, §3.2/§4.1)
- `crates/cranelisp-typecheck/src/lib.rs` — the as-built public exports (§2)
- `design/typecheck/{inference,traits,adt,hkt,auto-curry,ast-annotation,io-types}.md` — current subordinate docs
- `design/typecheck/monomorphisation.md` — full monomorphisation-from-roots + the ambiguity check + the multi-sig back-flow / harvest-window contract (§11.8)
- `design/typecheck/ownership-inference.md` — the interprocedural ownership-inference pass (S100+; governed by `design/arch/ownership-inference.md`); §17 the S115 MS-P7 chained-face design
- `design/typecheck/typed-resolution-carrier.md` — the `VarRef`/`ApplyRef` producer carrier (S114; governed by `design/arch/typed-resolution-carrier.md`)
- `design/typecheck/qualified-trait-impl.md` — Sprint-117 conventional/HKT
  impl-head references resolve once to canonical trait identity; minting and
  enrollment consume the settled carrier
- `design/typecheck/program-decomposition.md` — the `program/` module cut + the FIXME-0722 test-split design (§3)
- `design/typecheck/check-form-api.md` — superseded on entry shape by `check_forms` and held only as the `program/finalize` test anchor, per the mutation-discipline section above. `design/typecheck/CLAUDE.md` §"Redirections" covers the records deleted at S122
