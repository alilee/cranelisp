# `cranelisp-typecheck` — master design

Owner: `/design` (per-crate triad). Audience: triad agents working the typecheck surface, plus `/arch` for cross-crate coherence.

This document is the **single source of design intent** for the typecheck crate. The contract it designs against is:

1. `design/arch/bounded-contexts.md` §2 — Typecheck (the bounded context — what the crate is responsible for)
2. The crate's **public surface itself** — `crates/cranelisp-typecheck/public-api.txt` (the checked baseline) + the `pub` item rustdoc (`lib.rs` re-exports: `CheckState`, `TypeCheckEnv`, `PreludeFallback`, `check_forms`, `CheckResult`). *(The former `design/arch/facades/typecheck.md` facade was retired at S72 Wave 5 — all nine facades retired, `design/arch/CLAUDE.md` facades row; the canonical surface is now source rustdoc + BC §2, not a separate facade doc.)*
3. `design/arch/CLAUDE.md` Decisions 30, 41 (active) and 1, 2, 6, 8, 9, 14, 19, 21, 22, 33, 38, 39 (legacy — embodied) — cross-crate decisions binding typecheck. Note: Decisions 15 and 17 have been retracted (per `design/arch/CLAUDE.md` Decisions section); their constraints are embodied in current code (Ring 0-1 builtin/trait coexistence in the resolution machinery; core traits live in `.cl` files, not in `register_builtins`)

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

The facade `design/arch/facades/typecheck.md` is normative. Pinned by reference, not restated in detail. The shape (per facade §"Public surface (as-designed)"):

- Free function `check_form(node, &SymbolTable, &SymbolTables) -> Result<CheckResult, CheckError>` — the per-form check; the only entry point `int` uses in production.
- Free function `register_builtins(&mut SymbolTable<Code, ()>)` — called once per fresh `SymbolTable`.
- `CheckState`, `TypeCheckEnv`, `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator` — finer-grained scaffolding exposed for tests and advanced callers.
- Trace hook re-exports from `trace.rs` (`install_symbol_table_ensure_hook`, …) — observability surface for `/int`'s scheduler tracing per `design/int/heisenbug-race-closure.md §3d''`.
- Re-exports from `cranelisp-types` per facade — `CheckResult, CheckError, ResolutionGap, ConstructorInfo, DisplayInfo, FieldInfo, MethodResolutions, MonoDefn, ReplSnapshot, ResolvedCall, TypeDefInfo, Scheme, Subst, Type, TypeId`.

The nine bounded-context invariants (facade §"Bounded-context invariants") are the contract that holds across sprints. The crate is designed to keep them; §6 pins how.

### 2.1 Drift between facade and current source — explicit register

The facade is **target-stating**; current source has not finished migrating to it. This register names the deltas the design intent commits to closing. None are silent debts; each is tracked.

| Facade item | Current source | Tracking |
|---|---|---|
| `check_form(node, &SymbolTable, &SymbolTables)` free function | Method `TypeCheckEnv::check_form(_module, form, pass, &mut state, &mut accumulator)` returning `FormCheckResult` | FIXME 0008 (mutability discipline + free-function shape) |
| `register_builtins(&mut SymbolTable<Code, ()>)` taking one table | `register_builtins<C, L>(&DashMap<ModuleFullPath, SymbolTable<C, L>>, &AtomicU32)` taking the whole map plus the type-var allocator | FIXME 0008 (same pivot — once `check_form` is a free function, builtins follow); see also FIXME 0098 Phase 3 for the boundary-type prerequisites |
| `CheckError`, `ResolutionGap` re-exported from `cranelisp-types` | Neither type exists in `cranelisp-types`; the crate returns `CranelispError` | **FIXME 0098 Phase 3** — typecheck migration to `check_form`/`CheckError`/`ResolutionGap` typed returns (Phase 1 lands the boundary types in `cranelisp-types` first) |
| `CheckResult` returned by `check_form` | `FormCheckResult` per call; `CheckResult` only at `check()` level after finalize | Rolls up under FIXME 0008's free-function migration |
| `TypeCheckEnv<'a>` (no generics in facade) | `TypeCheckEnv<'a, C = (), L = ()>` (defaults work in practice) | Generic-defaults convention; minor doc-clarity item, called out in §11 |
| Public surface in `lib.rs` re-exports the full type set per facade | `lib.rs` re-exports a small subset (`CheckResult, CranelispError, ReplSnapshot, TopLevel`) | Per Principle 15 (S64) — implementation-crate facades do NOT re-export `cranelisp-types` items; the existing `pub use` block is removed by FIXME 0100 Phase 1 (which also relocates `CheckResult`/`CheckError`/`ResolutionGap`/`ReplSnapshot` from `cranelisp-types` into `cranelisp-typecheck`) |

The drift items above are NOT design problems with the contract — they are implementation-not-yet-caught-up. Working through them is the next several waves of `/dev` work, sequenced behind the audit's six prioritised remediations (§5.1).

The two contract problems that DO need `/arch` arbitration are flagged in §11.

---

## 3. Internal architecture

### 3.1 Module layout (as-built)

| File | LOC | Role | Health |
|---|---:|---|---|
| `program.rs` | 6,985 | Per-form pipeline (`check`, `check_form`, `finalize_check_result`) + deprecated `check_program` / `check_repl_input` paths + multiple expression walkers | **Highest-debt file** (audit Findings 1, 2) |
| `infer.rs` | 3,054 | Algorithm-W per-`Expr`-variant inference + deferred trait-call resolver | One-method-per-variant largely clean (audit) |
| `traits.rs` | 2,919 | Trait decls, impl recording, method resolution; non-HKT and HKT impl-method paths | Duplicated impl-finalization tail (audit Finding 3) |
| `checker.rs` | 2,798 | `TypeCheckEnv` + `CheckState` + cross-module lookup helpers | Lookups scan all modules — many ad-hoc views (audit Finding 5) |
| `builtins.rs` | 2,433 | Builtin / primitive registration | 132× manual `ModuleEntry::Def { … }` literals concentrate here (audit Finding 4) |
| `adt.rs` | 923 | ADT registration, exhaustiveness | Clean |
| `resolve.rs` | 356 | Method / overload resolution helpers | Clean |
| `unify.rs` | 339 | Algorithm-W unification + occurs check | Clean |
| `scope.rs` | 191 | Scope stack | Clean |
| `scheme.rs` | 172 | `Scheme` operations (generalise / instantiate) | Clean |
| `trace.rs` | 161 | Cross-crate trace hook installer | Clean |

Total production: ~20.4 KLOC (incl. co-located tests).

### 3.2 Target shape (post FIXME 0008 + FIXME 0098 Phase 3 + the audit's six remediations)

The audit's target-state diagram (`audits/typecheck-20260423-target-state.{mmd,svg}`) pictures one `check()` / `check_form()` pipeline reading the symbol-table store via a centralised lookup facade (`Index`), shared `Expr` walker helpers, and a shared impl-method finalizer for the HKT / non-HKT trait paths. That diagram is **directionally correct** but predates Decisions 38/39 and FIXME 0008 / FIXME 0098 Phase 3. The refinements layered on top:

1. **`check_form` consumes `&SymbolTable` not `&mut SymbolTable`** (FIXME 0008 / Decision 38). The audit's diagram does not name the mutability discipline; this design pins it.
2. **Errors carry `ErrorLocation`, not bare `Span`** (Decision 39). Producer policy in §7.
3. **`check_form` returns `Result<CheckResult, CheckError>` where `CheckError::Gap(ResolutionGap)` is one variant.** The current `FormCheckResult` is an internal stage product; what crosses the facade is the rolled-up `CheckResult`. FIXME 0098 Phase 3 names the typecheck-side migration; Phase 1 lands the boundary types.
4. **`TypeCheckEnv` becomes a thin internal struct** — once `check_form` is a free function over `(&SymbolTable, &SymbolTables)`, `TypeCheckEnv`'s job is to wrap those two refs plus the per-call `CheckState`. The facade keeps it `#[non_exhaustive]` for callers that want finer-grained control, but it stops being the public API.

The audit's six prioritised remediations are the maintenance roadmap. They land in the order the audit names — pipeline consolidation first, impl-method finalization second, shared `Expr` walker third, `ModuleEntry::Def` builders fourth, lookup facade fifth, test split sixth. The triad sequences these across waves; this design doc does not bind ordering tighter than the audit does.

### 3.3 The `Index` lookup facade

The audit's Finding 5 names "many lookups scan every loaded module" as a maintainability risk and proposes a `TypecheckIndexView`. The design intent: one place owns the scan-all-modules logic; specialised lookups read through it. The motivation is **maintainability, not performance** (Principle 6 — premature performance work is forbidden; centralisation is bookkeeping). When indexing/caching becomes worth doing later, it lives behind this facade and call sites do not change.

The current `checker.rs` exposes ~30 lookup helpers (`lookup_type_def`, `lookup_constructor_type`, `all_type_defs`, `lookup_trait_decl`, `method_to_trait`, `has_impl`, `get_implementing_types`, `known_type_names`, `find_hkt_param_index_in_registry`, …). The audit-recommended consolidation gathers these onto an `Index` view; per-call complexity stays the same, but the dispatch surface localises.

---

## 4. Quality attributes

### 4.1 Simplicity (Principle 6 — complexity has a budget)

The crate's *core* is simple: per-`Expr`-variant inference, Algorithm-W unification, generalise/instantiate. The *control flow around it* is not — three issues, each named by the audit:

- **HIGH — duplicate pipelines** (audit Finding 1). `check_program*` / `check_repl_input*` shadow `check` / `check_form`. Carry real logic — registration, body checking, monomorphisation, AST annotation. Every change has to ask "one path or three?" Cleanup is the audit's #1 priority and this design doc's #1 simplification target.
- **HIGH — duplicate `Expr` walkers** (audit Finding 2). `apply_subst_to_expr`, `annotate_expr_from_maps`, `collect_constrained_calls`, `resolve_deferred_trait_calls`. New `Expr` variants risk silent coverage drift across multiple files. Target: one `walk_expr_children` shared helper; specialisation stays local, traversal centralises. Principle 12 (design for the full spec surface) says new variants must not require multi-file coordinated edits.
- **HIGH — duplicate impl-method tails** (audit Finding 3). `check_impl_method_with_sig` and `check_hkt_impl_method` share ~half their bodies (snapshot side maps → check body → resolve auto-curry → mangle → annotate → write `ModuleEntry::Def`). Factor the shared tail; keep type-resolution front halves separate.

Resolving these three reduces effective complexity meaningfully without changing what the crate does. They are direct enabling work for the FIXME 0008 free-function migration — once the duplicate paths are gone, the surviving path collapses naturally onto the facade-shaped `check_form`.

### 4.2 Maintainability

The four maintainability risks the audit names map directly onto this design doc's planned cleanups:

| Audit risk | Design response | Reference |
|---|---|---|
| Parallel/legacy code-paths in `program.rs` | Consolidate to `check` / `check_form`; deprecated paths become test shims | §4.1 + audit remediation #1 |
| Expression walking duplicated | Shared `walk_expr_children` helper | §4.1 + audit remediation #3 |
| `ModuleEntry::Def { … }` constructed 132× manually | Narrow constructors / builders (primitive def, user def placeholder, concrete checked def, overloaded placeholder, trait method def) | §4.1 + audit remediation #4 |
| Many lookups scan every loaded module | `TypecheckIndexView` — one place owns the scan-all-modules logic | §3.3 + audit remediation #5 |

The `ModuleEntry::Def` invariant drift (Finding 4) is the most insidious. 132 occurrences of fields like `got_slot`, `ast`, `code`, `trait_origin` set manually means any future field addition ages each call site independently. The 42 Decisions accumulating around `ModuleEntry::Def` (especially 25, 31, 38, 41) raise the per-field correctness stakes; the builders are a forcing function for keeping invariants in one place.

The drift register in §2.1 is also a maintainability surface — keeping it accurate as the crate evolves toward the facade is part of every triad cycle's `/design` work.

### 4.3 Observability

`trace.rs` exposes `install_symbol_table_ensure_hook` for the integration layer to wire scheduler tracing. This is the documented mechanism (`design/int/heisenbug-race-closure.md §3d''`). No further observability surface is planned for this crate — the typecheck product (`CheckResult`) is itself the diagnostic artefact, and per-symbol introspection (`Introspection.clif_ir` etc.) is `/backend` + `/int`'s.

When typecheck errors surface, `ErrorLocation` (§7) carries enough metadata for the integration-layer formatter to render rich context without typecheck duplicating the source-snippet logic.

### 4.4 Concurrency-safety

Covered in §6. The headline: typecheck holds no shared state across calls; concurrency is handled by the SymbolTable mutation discipline (Decision 38 / FIXME 0008).

### 4.5 Performance

The crate's perf posture today is "scan all loaded modules for any global question" (audit Finding 5). For Ring-2-scale workloads this is fine. The audit's proposed `TypecheckIndexView` is a **centralisation step, not an optimisation** — it makes future indexing/caching changes one-place edits instead of N-place. Premature indexing is rejected per Principle 6 / `feedback_no_premature_perf.md`.

The cross-module FQ-resolution path (`check_form` → `&SymbolTables` → `.get(&other_module)`) is shard-shared-locked once FIXME 0008 lands. Per-entry contention with concurrent insert from another worker is microsecond-scale and acceptable per FIXME 0008's analysis.

Algorithm-W's substitution-composition cost is well-understood. No spec acceptance criteria pin typecheck wall-time; if one emerges (e.g., multi-thousand-defn module), the index facade is where memoisation lands.

### 4.6 Testability (Principle 5 — testability is structural)

The crate is structurally testable today — `check_form`-equivalent driver paths take `(form, &SymbolTable-equivalent, &SymbolTables-equivalent)` plus per-call state. The test surface is large (~12 KLOC co-located) which is actively useful for invariant pinning. The audit's Finding 6 (file ergonomics) is the only testability concern: the largest production files (`program.rs` 2,815 prod / 4,170 test, `infer.rs` 849 prod / 2,205 test, `checker.rs` 812 prod / 1,986 test) are hard to navigate with tests interleaved. Split heavyweight tests into sibling `*_tests.rs` modules — but only after the pipeline cleanup, per the audit's sequencing.

The advisory scaffolding (`CheckState`, `TypeCheckEnv`, `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator`) is exposed precisely for testing — finer-grained drivers than `check_form`. `int` uses only `check_form` in production; the others are test affordances and should not become production paths.

A coverage gap that surfaced in §11: there is no narrow unit test asserting `check_form` raises `CheckError::Gap(ResolutionGap::SymbolTypechecked(fq))` for an unresolved FQ value reference (vs `TypeError`). FIXME `target: /qa` proposed in §11.

---

## 5. Pipeline structure inside the crate

The audit confirms the per-form pipeline shape is "directionally correct" (§"What is working well" #3). The pipeline:

1. **Pass 1 — Register.** `check_form_register` walks the form variant (`TypeDef | TraitDecl | TraitImpl | Defn | Expr`) and populates the symbol table with type defs, trait decls, trait impls, and signature schemes. No body checking. Default-method defns generated by `register_trait_impl` are queued for Pass-1 registration in a follow-up loop (currently in `check_inner` after the main Pass-1 loop).

2. **Pass 2 — Body check.** `check_form_body` runs Algorithm-W per body, populates `FormCheckResult.expr_types`, `method_resolutions`, `mono_defns`, `multi_sig_defns`, `default_method_defns`, and `call_graph_edges`. Defaults-defn body check follows in the same loop pattern.

3. **Finalize.** `finalize_check_result` runs the post-passes (generalisation, overload resolution, monomorphisation, AST annotation) and produces the rolled-up `CheckResult`.

The current `check()` method on `TypeCheckEnv` orchestrates all three passes for a slice of `TopLevel` forms. The facade's `check_form` is the per-form variant of the same machinery, called by `int::process_form` in the form-by-form scheduler loop (per Decision 30 / facade §"Returns").

### 5.1 The audit's six remediations — execution plan as enabling work

The audit's prioritised remediations and how they relate to the facade migration (FIXME 0008, FIXME 0098 Phase 3):

| # | Remediation | Effect on facade migration |
|---|---|---|
| 1 | Remove duplicate checking entry points from `program.rs` | **Prerequisite.** Until `check`/`check_form` are the only paths, the free-function migration cannot be done cleanly. |
| 2 | Extract shared impl-method finalization in `traits.rs` | Independent; reduces complexity in the largest area touched by FIXME 0008. |
| 3 | Introduce shared `Expr` traversal helpers | Independent; protects new variants from drift during the facade migration. |
| 4 | Add constructors/builders for `ModuleEntry::Def` | Independent; reduces blast radius of any `ModuleEntry::Def` field changes (Decision 39's `defn_order` field, Decision 41's any future additions). |
| 5 | Centralise "scan all modules" lookups behind `TypecheckIndexView` | Independent; centralises cross-module read patterns that FIXME 0008's `&SymbolTables` access will touch. |
| 6 | Split heavyweight tests out of giant implementation files | Sequenced last, per the audit. |

Sequencing #1 first is load-bearing for the FIXME 0008 / FIXME 0098 Phase 3 migration; the others are independent quality improvements that can interleave with the facade work.

---

## 6. Mutation discipline — the post-FIXME-0008 contract

This is the load-bearing simplification of S63. Earlier subordinate docs (`check-form-api.md`, `dashmap-migration.md`, `stateless-tc-impl.md`) assume `&mut SymbolTable`; the design intent commits to the post-FIXME-0008 shape per Decision 38.

### 6.1 The contract

`check_form(ast, &SymbolTable, &SymbolTables) -> Result<CheckResult, CheckError>` — `&SymbolTable`, NOT `&mut SymbolTable`.

The only `&mut SymbolTable` operations in the entire system are:

1. **Phase 0 setup** — `write_structural_decls(&mut self, decls: StructuralDecls)`, called once per module at parse time by `int::register_module`. Seeds `imports`, `exports`, `platforms`, `submodules` (per Decision 33), and seeds `defn_order: Vec<Symbol>` (per Decision 39) from the parser's declaration-order list of defn names.
2. **Per-REPL-eval `defn_order` append** — `append_defn_order(&mut self, sym: Symbol)`, called by `int` after a REPL-defined symbol commits. Brief integration-layer-only window.

Both operations live on the initiator thread. Workers never see `&mut SymbolTable`.

### 6.2 How writes happen during typecheck

`check_form` annotates `node` in place (the AST is owned by the caller, so this is local mutation, not symbol-table mutation). It does NOT call `insert_or_update` — committing the new `ModuleEntry::Def` is `int::insert_symbol`'s job (per facade invariant 2).

When typecheck logically needs to publish something to the symbol table (e.g., a synthesised mono-defn entry, or a Pass-1 signature), it does so via `SymbolTable::insert_or_update(&self, sym, entry)` — `&self`, writing through the inner `DashMap<Symbol, ModuleEntry<C>>`'s per-entry write lock per the per-symbol mutability discipline.

### 6.3 Why this matters mechanically

Two correctness payoffs (FIXME 0008 §"Operational implication"):

- **Per-symbol gap mechanism becomes mechanically sound.** A `Gap(SymbolTypechecked(m2/bar))` waker resumes and finds m2's symbol table queryable via shared shard access — no whole-module write lock to contend. This is what makes Decision 30's per-symbol gap kinds (`SymbolTypechecked(FQSymbol)`, `MacroInMem(FQSymbol)`) operationally usable.
- **Cross-module read contention disappears.** A second worker's `Sess.symbol_tables.get(&m1)` does not block behind the typecheck-in-progress worker's RefMut.

### 6.4 What the current source still does

The current `TypeCheckEnv` borrows the *whole* `DashMap<ModuleFullPath, SymbolTable<C, L>>` and acquires per-module guards (`current_symbol_table`, `current_symbol_table_mut`) ad hoc. Some of these guards are `RefMut` (write) holds across non-trivial work — exactly what FIXME 0008 targets to eliminate. The free-function `check_form(ast, &SymbolTable, &SymbolTables)` shape removes the ambiguity at the boundary; internal code paths then collapse onto shared-shard reads + per-entry inner-DashMap writes.

This is in-flight migration, not silent debt. The audit's remediation #1 (consolidate pipelines) is the prerequisite; FIXME 0008 is the contract change; the source migration is the sprint work that remains.

### 6.5 What this supersedes

- `check-form-api.md` — describes `check_form(ast, &mut SymbolTable, &SymbolTables)`. **Stale on signature.** The algorithm shape it describes (per-form Pass-1/Pass-2, accumulator) survives.
- `dashmap-migration.md` — built around `TypeChecker.modules: DashMap<…, SymbolTable>` with `&mut SymbolTable` access. **Largely stale.** The migration succeeded; the lessons are folded.
- `stateless-tc-impl.md` — Sprint-51 stateless extraction. Its goals landed (the `TypeChecker` struct dissolved, state moved to `CheckState` + the caller-supplied symbol table). The `&mut SymbolTable` patterns it documents are superseded.

§10 lists these in the pointer table.

---

## 7. Concurrency model

### 7.1 What the crate sees

`check_form` is invoked by an `int` worker. The worker holds:

- `&SymbolTable` for the worker's owning module (shard-shared lock on `shared.symbol_tables.get(&m)` — per the post-FIXME-0008 shape; under current source, a `RefMut` is held).
- `&SymbolTables` for cross-module FQ resolution (`.get(&other)` per remote module).
- `&mut CheckState` (per-call transient — owned by the worker).
- A mutable `Ast` (caller-owned; in-place annotation).

The crate does NOT read `Sess`, does NOT read `SharedState.scheduler`, does NOT call `wait_for_typecheck_*`. Per facade invariant 9 / Principle 3 (dependency flows toward stability), dependencies surface as `CheckError::Gap` values.

### 7.2 Reframing of Decision 30

Decision 30 ("form-by-form scheduler; mutual imports deadlock") historically claimed single-worker-per-module as a **lock safety requirement**. Decision 38 reframes this to **scheduler ordering only**. Per-entry inner-DashMap locks make multi-worker mutation of one SymbolTable safe in principle. The single-worker-per-module invariant still helps the scheduler avoid dispatch races and simplifies form-by-form sequencing, but it is no longer required by the lock discipline. The mutual-import deadlock remains a scheduler-level constraint with the documented `discover-tests` workaround.

### 7.3 Gap-return contract

Per the gap-return pattern (`facades/int.md` `process_form`):

| Gap | When typecheck raises it | Caller response |
|---|---|---|
| `ResolutionGap::SymbolTypechecked(fq)` | FQ value reference whose module isn't typechecked | `int` ensures `fq.module` is registered, calls `wait_for_typecheck_symbol(fq)`, retries `check_form` |
| `ResolutionGap::Type(fqt)` | FQ type reference whose module isn't typechecked | `int` ensures `fqt.module` is registered, calls `wait_for_typecheck_type(fqt)`, retries |
| `ResolutionGap::MacroInMem(fq)` | (raised by `frontend::expand`, NOT `check_form`) | by the time `check_form` runs, expansion is complete |

Typecheck asks for `SymbolTypechecked` (not `SymbolInMemory`) for value references — it needs the entry's `Scheme`, not its compiled code. This is what makes the gap-return cheap: typecheck does not block on codegen.

The `MacroInMem` variant in the unified `ResolutionGap` enum is raised by frontend, not typecheck. This is an **intentional contract**: `ResolutionGap` is the unified gap-return type spanning frontend + typecheck producers, and each producer raises only its applicable subset (Principle 7 — single source of truth: the gap enum is one shared vocabulary, even though each call site uses only part of it). §11 raises this as a doc-clarity FIXME asking `/arch` whether the rustdoc should pin which producer raises which variant.

**Source status:** `CheckError` and `ResolutionGap` do not yet exist in `cranelisp-types`. FIXME 0098 Phase 1 lands the boundary types in `cranelisp-types`; Phase 3 migrates typecheck to the typed returns. Until those land, the current source returns `CranelispError` and the Gap mechanism is implemented at the `int`-orchestration layer through ad-hoc dependency detection.

### 7.4 Snapshot / restore

`check_form` may write intermediate state (type-var allocations, deferred resolutions in `CheckState`). On `Err`, the caller restores via `ReplSnapshot` per `pipeline-v4.md §6.2`. The crate provides the snapshot/restore primitive (`TypeCheckEnv::snapshot`, `TypeCheckEnv::restore`) but does not invoke it itself. (REPL eval rollback semantics depend on this — temporary closures from `(let [f add] f)` shapes do not commit until expression eval succeeds.)

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

The `Warning` shape mirrors `ErrorLocation` (per `facades/types.md`). Typecheck warnings (e.g., shadowing, unused imports — none yet implemented) follow the same producer policy.

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

The detailed designs live in subordinate docs (cited in §10). The shape this master doc commits to:

### 9.1 Trait method dispatch — Decision 14

Typecheck always emits `ResolvedCall::TraitMethod` for trait-dispatched calls (operators included). The backend recognises known primitive impls (`Num.+$Int → iadd`, etc.) via a static lowering table. Typecheck stays clean of backend lowering choices.

### 9.2 Constraint propagation — Decision 19

`Scheme.constraints` is populated by `generalize` collecting trait constraints from active type variables. Non-empty constraints mark a constrained polymorphic function; concrete bodies are deferred to call-site monomorphisation.

### 9.3 Monomorphisation analysis

`CheckResult.mono_defns: Vec<MonoDefn>` carries the specialisation requests typecheck discovered at call sites. The integration layer commits these as `ModuleEntry::Def` entries (with mangled JIT names like `add$Int+Int` per Decision 16) for the backend to compile. Typecheck does NOT commit the mono-defn entries itself — see `auto-curry.md` for the historical machinery and `traits.md` for the trait-dispatch interaction.

**Monomorphisation from roots (structural slot-gate first) — `monomorphisation.md`.** The detailed design for the S84 Cluster A guarantee that **no `Type::Var` reaches codegen under any reachable instantiation** lives in the subordinate doc `monomorphisation.md`, **re-grounded mid-Phase-5 on the structural-slot-gate-first model** (user ruling 2026-06-16; resolved FIXME 0376). The **primary mechanism is the corrected GOT-slot-allocation gate**: a def's `fn_state` carries a slot ⟺ its finalised type is **fully concrete** (`Type::is_concrete()`, NOT `constraints.is_empty()` — the as-built leak; "concrete" ≠ "unconstrained"), per Principle 20 (S84 generalisation) + BC §7 "Callability is structural". A determined-but-non-concrete *unconstrained* generic def gets a new slot-less `UserFnState::Polymorphic` arm (sibling to `Constrained`; an additive `cranelisp-types` variant owned by /arch + a `CACHE_SCHEMA_VERSION` 5→6 bump owned by /backend — see `monomorphisation.md` §6 + FIXME 0377). The slot-less-ness makes a non-concrete def unconstructable as a codegen value (the SIGSEGV root). The doc pins: (1) the corrected gate (`constraints.is_empty()`→`is_concrete()` at `program.rs:947`/`:1143` + the demotion leg `:1312`; the scheme-writeback legs `:919`/`:1129` stay `constraints.is_empty()`, governing 0344 generalisation, not slot allocation); (2) the systematic reachable-instance worklist/fixpoint EXTENDING the landed Tier-1/1.5 `pass4_monomorphise` → `monomorphise_call` → `monomorphise_inner_parametric_hops` spine (no second entry point — /arch ruling, Principle 7), **Wave-0-narrowed to the `(Box a)`-field-carrying-`Type::Var`-through-HOF gap** (bare-`Int` HOF shapes already mono cleanly — GREEN-stay guards), cluster-level dedup keyed on the existing mangled name; (3) the §3.11.1 **ambiguity check** (0373 part ii) **demoted to a SECONDARY backstop** — fired at the post-generalisation finalisation boundary before Pass 4 (`finalize_check_result_inner`, after the first `regeneralize_defn_schemes`), raising `CranelispError::TypeError` today / `CheckError::AmbiguousType` post-FIXME-0098 (both typecheck-internal). **Wave 2 (FIXME 0379/0380) makes this check POSITION-COMPLETE and predicate-shared**: it fires the per-node verdict on the resolved type at *every* codegen-reaching value position `for_each_child_expr` visits (match scrutinee, fn-call arg, vec element, ctor field, if-branch, `ParBind` binding, nested `let`, returns — not just `let` bindings), and the verdict comes from the shared `Type::is_representation_undetermined()` predicate (the local `is_ambiguous_codegen_reaching_type` heuristic is retired) — the SAME predicate the WIDENED backend 0375 RC-site backstop uses, so the typecheck error and the backend panic agree by construction (belt-and-braces, BC §3 invariant 9). The 0344/0349 fold-accumulator over-monomorphisation is the pinned risk. Termination is bounded by monomorphic-recursion enforcement (rank-1 HM). This master doc commits to the shape `monomorphisation.md` elaborates; that doc wins on detail.

FIXME 0033 (`monodefn-redundant-side-maps`) — **Step A done; Step B is the field-drop.** `MonoDefn` (`cranelisp-types::check`) carries two Span-keyed side maps, `resolutions: MethodResolutions` and `expr_types: HashMap<Span, Type>`, that were redundant once monomorphisation annotated the AST directly. Step A landed: `traits.rs::monomorphise_call` now annotates `mono_defn.defn` in place (via `annotate_defn_from_maps` + `apply_subst_to_defn`) and **constructs `MonoDefn` with `MethodResolutions::default()` + an empty `HashMap`** — the fields are no longer populated in production. The only surviving reads are `#[cfg(test)]` scaffolding in `cranelisp-backend` (`test_compile_program_and_run`, which merges `mono.resolutions` and falls back on `mono.expr_types`). Step B is the structural removal: drop both fields, making `MonoDefn` a `Defn` newtype (or a single-field wrapper); update the one backend test to read annotations off `mono.defn` directly. **Baseline impact:** removes three `cranelisp_types::MonoDefn::{expr_types, resolutions}` lines from `crates/cranelisp-types/public-api.txt` (regenerate per the baseline-diff discipline). The field-drop and the types-crate baseline regen are `/dev`-on-`cranelisp-types` work (the struct lives in the interface crate, `/arch`-adjacent); the backend test edit is `/dev`-on-`cranelisp-backend`. Coordinate as a small two-crate change.

### 9.4 ADT typing

`TypeDefInfo` + `ConstructorInfo` + `FieldInfo` describe the registered ADTs. Pattern matching infers via standard unification + nominal constructor-to-type resolution. Exhaustiveness is checked in `adt.rs`. Polymorphic ADTs with data-constructor fields fully supported (e.g., `(Some [:a val])`).

**Field-accessor `Type.field` (canonical) + impl-time collision (FIXME 0365, S91; INVERTED S91 Phase-5) — `fixme-0365-field-accessor-dotted.md`.** **Canonical/alias direction INVERTED by user ruling (2026-06-26, design-only pending user confirmation; supersedes the §1.5 visibility-by-arm rule, kept banner-marked).** **`Type.field` (`Box.v`) is the CANONICAL field accessor — always a real Public `Def`, the listed/displayed name (qualified-display convention, Principle 16); bare `field` (`v`) is a convenience `Import` alias → `Type.field`.** Ambiguity lives in the **alias**: one type owns `v` → bare `v` resolves; two share `v` → bare `v` is ambiguous (`Ambiguous` sentinel), while canonical `Box.v`/`Cup.v` keep working (no cliff). Synthesis (`adt.rs::synthesise_one_accessor`) registers the real `Def` under the canonical key + the `Import` alias under the bare key (the as-built reversed); the poison re-mint helper (`remint_first_accessor_under_qualified_key`) and the per-case visibility flip are **deleted** (net code reduction, Principle 6). Typing reads the canonical `Def.scheme` (`FieldType` = return arm); bare alias chain-follows to it — one scheme, one compiled function (duplicate-codegen fix preserved). Cross-module is **strictly better**: canonical `Box.v` uniformly Public → `m/Box.v` resolves in every case incl. contested (the as-built poison-must-be-Public worry, `resolve.rs:578`, disappears). The impl-time collision rule (§7.3.1) fires against the canonical key — a new pre-flight validation in `register_trait_impl` (`impl_check.rs`) enumerating the type's canonical accessor names via `committed_accessor_kind` (`adt.rs:677`), intersecting with the impl method names, raising a `TypeError` naming both sites before the impl registers (Principle 18; the contested-field enumeration simplifies — no `accessor_owning_types` consult needed since the canonical entry is unconditional). `/list`/`/exports` show the qualified canonical `Box.v` (every field, every case); bare alias not separately listed. **Zero `public-api.txt` / `cranelisp-types` movement** (internal relabeling of which key is `Def` vs `Import`). FIXMEs filed: `/spec` reframe of §5.2.6/§8.5.2 (bare-as-alias, `Type.field`-as-canonical); FIXME 0438 updated for the inverted listing question. See the subordinate doc §0/§1/§1.6/§2 for the inverted design, `/dev` rework, and `/qa` guards.

### 9.5 HKT — `hkt.md`

Constructor variables (e.g., `:Functor f`, where `f` is a type-constructor variable) supported via `Type::TyConApp` and a parallel impl-method check path (`check_hkt_impl_method`). The audit Finding 3 highlights this as the duplicate-tail risk; the resolution is to share the post-resolution finalization step, keeping only the type-resolution front halves separate (audit remediation #2).

### 9.6 Multi-sig dispatch + auto-curry

`DefnMulti` defns produce one `ModuleEntry::Def` per signature variant (mangled `name$Type1+Type2`). Dispatch happens post-inference when concrete arg types match a variant. Auto-curry (calling with fewer args than declared) interacts with multi-sig — this is the most subtle interaction in the crate. Documented in `auto-curry.md`. **S112 (leg a, FIXME 0642):** the settled §5.1.2 makes a multi-sig `defn` inference-equivalent to its clauses as separate mutually-recursive functions — sibling self-calls back-flow and pin clause params (the former "clause independence / no-back-flow" barrier is removed), and the once-"not supported" **multi-sig × constrained-poly** interaction is IMPLEMENTED (each constrained clause rides the standalone constrained-template / `pass4_monomorphise` path). Designed in `monomorphisation.md` §11 (supersedes §9's drifted posture).

FIXME 0043 (`typecheck-resolved-call-autocurry-total-count`) is open — `ResolvedCall::AutoCurry` is missing `total_count` per the sketch; either extend the type or look up at codegen time. `/typecheck` and `/backend` coordinate the resolution.

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

---

## 10. Subordinate topic docs

| Topic | Doc | Status |
|---|---|---|
| Algorithm-W & substitution strategy | `inference.md` | Current |
| Trait registry, impl recording, monomorphisation, default methods | `traits.md` | Current |
| **Monomorphisation from roots — structural slot-gate first (slot ⟺ `is_concrete()`) + systematic mono + the ambiguity backstop** | **`monomorphisation.md`** | **Current** (Sprint 84, Cluster A; **re-grounded mid-Phase-5** on the structural-slot-gate-first model — user ruling 2026-06-16, resolved FIXME 0376). Pins: the corrected slot gate (`constraints.is_empty()`→`is_concrete()`; the new slot-less `UserFnState::Polymorphic` arm + the /arch FIXME 0377 + cache bump); the reachable-instance worklist EXTENDING the Tier-1/1.5 `pass4_monomorphise` spine (FIXME 0374, Wave-0-narrowed to the `(Box a)`-field-through-HOF gap); the ambiguity check **demoted to a secondary backstop** (FIXME 0373 ii); the 0344 fold canary discipline; the unit-test seams; the termination argument. **S90: §9 added — the FIXME 0432 multi-clause-`defn`-self-call panic→clean-error root fix** (R2 layer a; an early `is_concrete()` gate at the `monomorphise_call` P1 mint seam, before `build_mangled_name`, converging REPL and `--run` on the existing ambiguous-type diagnostic — the agentic-REPL Pillar-3 prerequisite). Cites Principle 20 + BC §7, `traits.md §7` (as-built pipeline it completes). **S112: §11 added — multi-sig = separate mutually-recursive functions (leg a, FIXME 0642)**: the settled §5.1.2 back-flow (collapse the two-phase ambiguity scan to ONE post-drain pass; order concrete mangling after the self-call drain; §9's "NOT a multi-clause inference change" REVERSED), the constrained-poly × multi-sig cell (user-ruled IMPLEMENT — each constrained clause a one-variant template on the standalone mono path; `ConstrainedFn` field unchanged, rustdoc via FIXME 0644 → /arch; no schema bump), the `OverloadVariant.mangled_name` determinism (`mangle_type`'s constant `Var`), and leg-(c) framing (resolved-return-dispatch `resolved_targets` producer attribution). Cites Principles 7/11/24. |
| **Type-signature match predicates (Pillar 3 importable-symbol search) — exact (alpha-equivalence) OR partial (structural-contains)** | **`signature-match.md`** | **Current** (S90 design; **S91 SHIPS** — Pillar 3 implementation, the 0432 gate cleared S90; S91-confirmation box at the doc head: algorithm HOLDS, the two predicates are the sole baseline movement, nothing stale, the §2.3 `TyConApp`-head canonicalisation note pulled forward for `/dev`). **Re-pinned S90 Phase 3 (commit `c699045`): MVP match is now exact OR partial** (superseding exact-only). Pins TWO pure free-function predicates the `int` indexer calls, **both exported from `cranelisp-typecheck`** (`/arch` Option A, §11.4/§11.8 — two additive `public-api.txt` lines at impl time): (1) `signature_matches_exact(&Type, &Type) -> bool` — alpha-equivalence up to consistent bijective var renaming (whole-tree); (2) `signature_matches_partial(query: &Type, candidate: &Type) -> bool` — **structural-CONTAINS**: query appears as a sub-tree of the candidate up to alpha-renaming (`_exact ⟹ _partial`), a containment walk reusing the `_exact` alpha-equivalence machinery, **NO unifier**. Both canonicalise-then-`==` via reused `collect_var_ids_ordered` (Principle 7); FQ-ADT discipline. Structural-contains needs NO wildcard token → `/spec` query-syntax consult NOT triggered. Hoogle subsumption (hole-instantiation + ranking) recorded as an explicit deferred `/typecheck` follow-up (NOT this sprint). Cites `repl-embedded-agent.md §11.2/§11.4/§11.8` (R3/R6/R8). |
| **Field-accessor `Type.field` (canonical) + impl-time collision rule (FIXME 0365) — INVERTED model** | **`fixme-0365-field-accessor-dotted.md`** | **Current** (Sprint 91, Thread C; **canonical/alias direction INVERTED S91 Phase-5, user ruling 2026-06-26, design-only pending user confirmation**). **`Type.field` (`Box.v`) is the CANONICAL field accessor — uniformly real + Public + listed (qualified-display convention); bare `field` is a convenience `Import` alias → canonical, ambiguous when two types share the field name.** Synthesis registers the real `Def` under the canonical key + the alias under the bare key (as-built reversed); the poison re-mint helper + per-case visibility flip are **deleted** (net code reduction). **Item 1 — typing**: reads the canonical `Def.scheme` (return arm = `FieldType`); bare alias chain-follows to it — one scheme, one compiled function (duplicate-codegen fix preserved); cross-module strictly better (canonical uniformly Public → `m/Box.v` resolves in every case, no cliff). **Item 2 — impl-time collision**: pre-flight validation in `register_trait_impl` (`impl_check.rs:18/79`) rejects a trait `impl` whose method name equals a canonical field-accessor name of the target type, before the impl registers (Principle 18); enumerates via `committed_accessor_kind` (`adt.rs:677`), union-view cross-cluster — the contested-field case simplifies (no `accessor_owning_types` consult; canonical entry is unconditional). §1.5 visibility-by-arm rule **SUPERSEDED** (banner-kept for audit). **Zero `public-api.txt` movement, no `cranelisp-types` change** (internal key relabeling). FIXMEs: 0439 (`/spec` reframe §5.2.6/§8.5.2), 0438 (`/repl`, updated for inverted listing). Cites §8.5.2/§5.2.6/§7.3.1; Principles 6/7/16/18. |
| **Ownership inference — the interprocedural lifetime/flow pass (S100 parts 6–11)** | **`ownership-inference.md`** | **DESIGN** (S100 Phase 3 stage 2; pre-implementation — no source/`cranelisp-types` edit in S100). Governed by the master spine `design/arch/ownership-inference.md` (where they disagree, the spine wins). Designs the post-monomorphisation per-cluster fixpoint (a `pass5_ownership` post-pass after `pass4_monomorphise` + the callee write-back, riding `Def.callees` + `resolved_call` — one graph, two consumers with R3), the internal `OwnershipSummary` (param modes + result mode + flow/spark-ops facts; FIXME 0467 proposes the boundary-carried subset), borrow-through-projection with provenance roots (escape ⇒ materialize-at-edge; last-use root-extension seam left backend-local), the op-wise per-cell confinement join with potential-fork over-approximation (`Transferred` carried internally, collapsed to `Crossing` in increment I — promotion measurement-gated), mangled-name-keyed instantiation-summary dedup + session memo, the increment-II write-path rulings (dynamic rc==1 default; static uniqueness scoped to the single-syntactic-use fresh-chain subset, success metric = proof chaining; mode-in-key measurement-gated), the moded-body + Decision-24-value-wrapper answer to the R2 HOF question (join-to-Owned rejected), and the declared-primitive fact-table consumption (leaves seed the fixpoint; `ring2-rc.md` §3.3 audit is the seed). **S102 Phase 3: §13 added — the increment-I change-set staging (Sprint 102 Block B2)**: CS-A dependency pin (the exact `/arch` `cranelisp-types` v11→v12 needs list, incl. conservative-read accessors, `abi_eq`, the shared-slot primitive-fact carrier, and the toggle-relocation ask), ordered change-sets CS-1–CS-4 over a new `src/ownership/` submodule cluster, the 0470/0472 graph-feed verification (template-grain feed demoted to seeding-order hint; fixpoint re-entry rides walk-harvested `DepSet` edges), the fact-table coverage verdict (one gap → FIXME 0504; `PrimitiveExtern` scope cut named), the toggle-set ⇒ **emit-no-summaries** pin, §13.6 refinements (internal summary type superseded by `ModeSummary`; post-convergence fact walk; multi-path `ResultMode` join; symbol-keyed provenance + shadow rule), and the Principle-23 scenario matrices carrying the 0497 rider. |
| **TypeExpr resolver convergence — the four-mirror single-source refactor (FIXME 0590)** | **`type-expr-resolver-convergence.md`** | **DESIGN** (S110 Phase 3; own Phase-5 `/dev` wave, independent of the 0583 backend seam). Principle-24 type-var-axis instance: the FOUR parallel `TypeExpr` resolvers (`resolve::resolve_type_expr` + `traits/type_resolve.rs` ×3 + `form.rs::check_type_expr`), each hand-rolling its own mint-on-miss + structural recursion, collapse onto the ONE `resolve::resolve_type_expr` behind a head-resolution `TypeExprCtx` (`self_type: Option<Type>` + a `ConVars` enum for HKT con-var interception). Pins: the mechanical `form.rs` collapse (drop `collect_type_var_ids`); the never-error `Named` fabrication arms DELETED (route through `resolve_terminal`, a behaviour-tightening test target); the fifth-mirror-prevention invariant (one `TypeExpr→Type` walk, `/review` grep-criterion); the rustdoc correction. **No `cranelisp-types` edit / no cache bump / typecheck-internal `public-api.txt`** (the `/arch` escalation path stays open but untriggered). Cites Principles 24/7/18/6/20. |
| **Typed resolution carrier — the `VarRef`/`ApplyRef` producer side (S114 Track A, FIXME 0653 prong 3)** | **`typed-resolution-carrier.md`** | **DESIGN** (S114 Phase 3; the producer half of the ONE coordinated multi-crate carrier flip, governed by `design/arch/typed-resolution-carrier.md` + Principle 24 §Corollary). Retires the `Option<FQSymbol>` local/unresolved conflation by TYPE: `infer_var` records a TOTAL typed verdict for every reference (`VarRef::Local{binder,binding_span}` / `VarRef::Global`), the Apply chokepoints record `ApplyRef::Dispatch`/`ViaCallee`, the `MethodResolutions` sidecar splits into total `var_refs`/`apply_refs`, and `from_expr` widens to `ViewBuildError{NotConcrete, Unresolved}` — a dropped carrier is a LOCATED typecheck error at view-build, never a codegen leak. Pins: binder-provenance via a per-frame `ScopeStack.frame_spans` (6 `push_scope` seams); the strict-first/lenient-fallback reshape (NotConcrete falls back, Unresolved propagates); the synthetic all-local lenient population → FIXME 0685 (/arch); **F-D2-10 rides the flip** as a dispatch-completeness re-attempt from settled state (the located "no impl of trait X" naming, P26); the B-2 escape-fact cache-coherence half in the ONE 21→22 window (F4/F7). Orthogonal drains (MC-X4/X4b, MC-X5, PS-SH1) + the MS-P7 evidence-brief (no fix) + 0590-last sequencing recorded. Cites Principles 24/26/18/8/6. |
| **Return-type-poly ambiguity — the unresolved-dispatch signal (R16/R17)** | **`return-poly-dispatch-signal.md`** | **DESIGN** (S110 Phase 3; coordinated typecheck+int change-set). The row-16/17 error-quality defect (bare `(zed)` leaks `__expr`-no-GOT-slot instead of the clean §3.11 message). Signal = a return-poly dispatch UNRESOLVED after final subst, grounded in the dispatch OUTCOME (no impl selected), NOT surface-type concreteness (which false-positived on `(add2 3 4)` in the S109 revert). typecheck rejects ordinary body positions directly; the entry/eval RESULT position (`main`/`__expr`) it cannot reject (Principle 19 — no entry designation), so the signal crosses to int via a transient `CheckResult` field (carrier escalated to `/arch`, FIXME 0611). Cites Principles 24/19/7/18. |
| HKT (`Type::TyConApp`, `check_hkt_impl_method`) | `hkt.md` | **Current** (**S112 leg b, FIXMEs 0628+0639**: §5.1/§5.4 reconciled to the settled trait/impl model — kind derived ONCE at `deftrait` registration [parenthesized head + never-applied con_var ⇒ REJECTED at declaration, §7.2.1]; consumers read `TraitDeclInfo.type_params`, never scan usage [Principle 24]; the `register_trait_decl` guard fix roots the `:a 7` display defect; the settled echo-the-head impl form + the ONE §7.3.5 Case-3 kind-check seam consuming `TraitImpl.head_con_var`). |
| ADT type checking (constructors, exhaustiveness) | `adt.md` | Current |
| Auto-curry (A1) detection | `auto-curry.md` | Current |
| AST annotation (Steps 1a/1b) — types and resolved calls co-located on AST | `ast-annotation.md` | Current |
| IO ADT typing | `io-types.md` | Current |
| Sprint-50 fixes (RC4 builtin leak, RC5 macro body type) | `sprint50-fixes.md` | Historical (lessons folded) |
| Step-4 macro deps assessment (Decision 21 alignment) | `step4-macro-deps.md` | Current |
| **`check_form` per-form API** | **`check-form-api.md`** | **Stale on `&mut SymbolTable` signature — superseded by §6 / FIXME 0008. Algorithm shape (Pass-1/Pass-2, accumulator) survives.** |
| **Wave 3a-β cluster-atomic two-pass entry surface** | **`wave-3a-check-form.md`** | **Current** (Sprint 66 Phase 5 Stage 2). Binds the post-Decision-44/FIXME-0167 shape: `check_form_signatures` + `check_form_body` free functions; `&mut ClusterContext` staging accessor; orchestrator-driven cluster atomicity. Supersedes `check-form-api.md` for the entry shape. |
| **DashMap migration of TypeChecker.modules** | **`dashmap-migration.md`** | **Largely stale — built around `&mut SymbolTable` access; the migration succeeded; superseded by §6.** |
| **Stateless TypeChecker (Sprint-51 extraction)** | **`stateless-tc-impl.md`** | **Stale on `&mut SymbolTable` patterns — the goal landed (`TypeChecker` struct dissolved; state in `CheckState` + caller-supplied table); §6 supersedes.** |
| **S76 — resolve_* re-pointing, macro-entanglement cleanup, ctor got-slot, platform-sig entry** | **`s76-resolution-and-enablement.md`** | **Current** (Sprint 76 Phase 3). Plans: (1) `resolve_*` family re-pointed at `cranelisp_types::resolve`/`resolve_macro_head` (chain-walk consolidates onto the types primitive — Principles 7+15; the `From<ResolveError> for CheckError` projection + view-selection stay typecheck-side); (2) `check_forms` confirmed post-expansion (no `MacroExpander` param) + the locked three-pass model's removal of the Wave-3a-β macro-clause double-typecheck entanglement; (3) 0249-a constructor GOT-slotting; (4) 0231 `check_type_expr` platform-sig entry. Resolves FIXME 0245 (recognition left typecheck's surface — no interior algorithm to author). Grounded in `design/arch/macro-availability-model.md` §0/§0.9 + BC §2 invariants 10+11. |

The three flagged docs are not edited by this design pass (per the constraint). When the next triad cycle re-touches them after audit remediation #1 lands, fold their surviving algorithmic content into `inference.md` / `traits.md` / `auto-curry.md` and archive.

---

## 11. Open questions / proposed FIXMEs

These surfaced during this design pass. Two are filed as new FIXME files (numbered, in `design/arch/fixmes/`); the rest are noted here for the user to lift if intent.

### Tracked — multi-crate migration

**FIXME 0098** — multi-crate migration covering `CheckError`/`ResolutionGap`/`ExpansionError` placement and `check_form` free-function shape. Phase 1 lands the boundary types in `cranelisp-types`; Phase 3 (typecheck) migrates `check_form` to the typed-return shape. See `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md`.

### Proposed — `target: /arch`

**Title:** `MacroInMem` gap appears in `ResolutionGap` enum but `check_form` cannot raise it.

**Issue.** `ResolutionGap::MacroInMem(FQSymbol)` per the facade is raised by `frontend::expand`, not by `check_form` (`facades/typecheck.md` §"Returns" comment confirms). Yet the gap variant is in the typecheck-re-exported `ResolutionGap` enum, which forces typecheck consumers to handle a variant typecheck never produces. Consider either (a) splitting `ResolutionGap` into `FrontendGap` + `TypecheckGap` enums, or (b) keeping the unified shape but documenting in `ResolutionGap`'s rustdoc which producer raises which variant. (a) is cleaner but adds a boundary type; (b) keeps the boundary smaller. Principle 2 (narrow interfaces) leans toward (b).

### Proposed — `target: /arch`

**Title:** `CheckError::Gap` post-Gap state contract is unspecified.

**Issue.** The facade documents the orchestrator's response per gap variant but does not pin a contract that `check_form` returns Gap **before** committing partial state. Today's implementation appears to leave `CheckState` partial-write on Gap (the caller restores via `ReplSnapshot`). Consider whether `check_form`'s Gap-return path should be specified as "no observable side effects beyond the unrestored CheckState" — i.e., does `check_form` write to `&SymbolTable` (via `insert_or_update`) before raising Gap? If yes, the Gap-then-retry pattern can leave the table with half-formed entries. If no, the contract should say so. Likely a clarification of the Gap-return contract in `facades/typecheck.md`.

### Proposed — `target: /arch`

**Title:** `TypeCheckEnv` generic parameters in facade.

**Issue.** The facade types `TypeCheckEnv<'a>` with no `<C, L>` parameters, but the as-built `TypeCheckEnv<'a, C = (), L = ()>` is generic. Recommend the facade pin `TypeCheckEnv<'a>` to mean `TypeCheckEnv<'a, (), ()>` explicitly (default-types convention) or expose the generics if integration layer code constructs a `TypeCheckEnv<'a, Code, ()>`. Today `int` does not appear to construct `TypeCheckEnv` directly (it calls `check_form`), so the default works — but spelling it in the facade prevents future surprise. Doc-clarity item; not blocking.

### Proposed — `target: /arch`

**Title:** `Code` as the default `C` for typecheck facade's `SymbolTable` parameter.

**Issue.** The facade names `&mut SymbolTable<Code, ()>` for `register_builtins` and `&SymbolTable<Code, ()>` for `check_form`. `Code` is `int`-owned per Decision 35 (`src/code.rs`) and now moving to `cranelisp-backend` per Decision 41 — neither location is in scope for `cranelisp-typecheck`'s direct deps. The facade's pin to `Code` is therefore a documentation contract, not a literal type binding — typecheck the crate works against `SymbolTable<C, L>` generic. Recommend the facade clarify whether `Code` here is "the integration layer's concrete `C`" (typecheck takes whatever the caller hands it) or "must be `Code` literally" (couples typecheck to a downstream crate, which it should not be). Doc-clarity question, not an implementation gap.

### Proposed — `target: /qa`

**Title:** Test coverage for the gap-return contract from typecheck's side.

**Issue.** The integration test surface exercises gap-then-retry through `int`'s orchestrator. There is no narrow unit test asserting that `check_form` raises `Gap(SymbolTypechecked(fq))` for an unresolved FQ value reference (vs `TypeError`) — this is the most likely place a future refactor could regress, because the gap path looks like an error path locally. Adding three or four narrow `check_form` unit tests (one per `ResolutionGap` variant typecheck can raise; one negative — confirm bare `Symbol` resolution does NOT raise Gap) would harden the contract once FIXME 0098 Phase 1+3 lands the types and the typed return.

### Proposed — `target: /design` (self — for next cycle)

**Title:** Fold `check-form-api.md`, `dashmap-migration.md`, `stateless-tc-impl.md` after pipeline cleanup.

**Issue.** Per §10 — once the audit's #1 cleanup (consolidate `check` / `check_form` as the only paths) lands, the surviving algorithmic content from these three docs (Pass-1/Pass-2 shape, accumulator, lookup style) folds into `inference.md` / `traits.md`, and the three docs archive. Sequencing: do this *after* the consolidation, not before, so the surviving content is identifiable.

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
| 38 (legacy — embodied) | `SharedState` formal definition; per-symbol mutability | `check_form` takes `&SymbolTable`; mutation flows through inner DashMap per-entry locks; `write_structural_decls` is the only `&mut` method |
| 39 (legacy — embodied) | Per-defn source on `Introspection.source`; `defn_order: Vec<Symbol>` on `SymbolTable`; errors carry `ErrorLocation` | typecheck adds `defn_order` field, populates `ErrorLocation { fq, span, … }`, leaves `context` to formatter |

### Retracted — invariants preserved

- **Decision 15 (retracted; outcome embodied)** — Ring 0-1 BuiltinFn coexists with TraitMethod. Both resolution paths still live in `resolve.rs` + `traits.rs`; the rationale is now embodied in the resolution machinery rather than tracked as an explicit Decision.
- **Decision 17 (retracted; outcome embodied)** — Core traits in `.cl` files. `register_builtins` does NOT register `Num`/`Eq`/etc. — those load via the prelude. The constraint is enforced by the current shape of `register_builtins` (synthetic `primitives`/`macros` modules only) rather than by an explicit Decision.

Decisions not listed (3, 4, 5, 7, 10–13, 16, 18, 20, 23–29, 31, 32, 34–37, 40, 42) bind cross-crate concerns (type IDs, span shape, RC discipline, GOT model, Code-enum placement, cache schema, function symbol naming, runtime/IO trampoline relocations, platform error shape) that typecheck doesn't surface directly.

---

## 13. Cross-references

- `design/arch/CLAUDE.md` Decisions 38, 39 (legacy — embodied; NEW MODEL framing); 1, 2, 6, 8, 14, 19, 21, 22, 30 (READ THROUGH 38/39 lens), 33 (structural decls on SymbolTable), 41 (active — peripheral). Decisions 15 and 17 retracted; their constraints embodied per §12 "Retracted — invariants preserved"
- `design/arch/facades/typecheck.md` — public surface (normative)
- `design/arch/facades/types.md` §"Symbol table — the single store" — `SymbolTable` shape consumed
- `design/arch/facades/int.md` §"process_form" — caller of `check_form`; defines the gap-orchestration retry loop
- `crates/cranelisp-frontend/src/lib.rs` //! preamble + `bounded-contexts.md` §1 — peer crate's public-surface contract (post-S70 B3-C facade retirement; `SymbolTables` alias canonical home is `cranelisp-types`)
- `design/arch/bounded-contexts.md` §2 — Typecheck (the BC)
- `design/arch/principles/` — architectural principles cited above
- `audits/typecheck-20260423.md` — current-state audit; HIGH/MEDIUM findings drive §4
- `audits/typecheck-20260423-{current,target}-state.{mmd,svg}` — diagrams
- `design/arch/fixmes/0008-typecheck-symboltable-per-symbol-mutability.md` — the operative target shape
- `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md` — multi-crate migration covering boundary types (Phase 1) and typecheck's typed-return shape (Phase 3)
- `design/arch/fixmes/0033-monodefn-redundant-side-maps.md` — open MonoDefn shape question
- `design/arch/fixmes/0043-typecheck-resolved-call-autocurry-total-count.md` — open AutoCurry shape question
- `crates/cranelisp-typecheck/src/lib.rs` — current public exports (subset of facade)
- `design/typecheck/{inference,traits,adt,hkt,auto-curry,ast-annotation,io-types,step4-macro-deps}.md` — current subordinate docs
- `design/typecheck/wave-3a-check-form.md` — Wave 3a-β cluster-atomic two-pass entry surface design (Sprint 66 Phase 5 Stage 2)
- `design/typecheck/monomorphisation.md` — Tier-2 full monomorphisation-from-roots + the unconstrained-var ambiguity check (Sprint 84 Cluster A; FIXMEs 0374 + 0373 ii)
- `design/typecheck/ownership-inference.md` — the interprocedural ownership-inference pass (S100 parts 6–11; governed by `design/arch/ownership-inference.md`; FIXME 0467 filed for the persisted-summary shape)
- `design/arch/fixmes/0374-typecheck-tier2-full-monomorphisation-from-roots.md` — Tier-2 spine (primary S84 deliverable)
- `design/arch/fixmes/0373-spec-rank1-hm-defaulting-and-section-12-1-representation-relaxation.md` — rank-1 HM + ambiguity rule (part ii realised as the typecheck check) + §12.1 relaxation
- `design/typecheck/{check-form-api,dashmap-migration,stateless-tc-impl,sprint50-fixes}.md` — historical / superseded subordinate docs (see §10)
