# `cranelisp-typecheck` — master design

Owner: `/design` (per-crate triad). Audience: triad agents working the typecheck surface, plus `/arch` for cross-crate coherence.

This document is the **single source of design intent** for the typecheck crate. The contract it designs against is:

1. `design/arch/bounded-contexts.md` §2 — Typecheck (the bounded context — what the crate is responsible for)
2. `design/arch/facades/typecheck.md` — the as-designed public surface
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

---

## 9. Trait + monomorphisation architecture

The detailed designs live in subordinate docs (cited in §10). The shape this master doc commits to:

### 9.1 Trait method dispatch — Decision 14

Typecheck always emits `ResolvedCall::TraitMethod` for trait-dispatched calls (operators included). The backend recognises known primitive impls (`Num.+$Int → iadd`, etc.) via a static lowering table. Typecheck stays clean of backend lowering choices.

### 9.2 Constraint propagation — Decision 19

`Scheme.constraints` is populated by `generalize` collecting trait constraints from active type variables. Non-empty constraints mark a constrained polymorphic function; concrete bodies are deferred to call-site monomorphisation.

### 9.3 Monomorphisation analysis

`CheckResult.mono_defns: Vec<MonoDefn>` carries the specialisation requests typecheck discovered at call sites. The integration layer commits these as `ModuleEntry::Def` entries (with mangled JIT names like `add$Int+Int` per Decision 16) for the backend to compile. Typecheck does NOT commit the mono-defn entries itself — see `auto-curry.md` for the historical machinery and `traits.md` for the trait-dispatch interaction.

**Monomorphisation from roots (Tier 2 + ambiguity check) — `monomorphisation.md`.** The detailed design for the *systematic completion* of monomorphisation — the S84 Cluster A guarantee that **no `Type::Var` reaches codegen under any reachable instantiation** — lives in the subordinate doc `monomorphisation.md`. It pins: (1) the reachable-instance worklist/fixpoint that EXTENDS the landed Tier-1/1.5 `pass4_monomorphise` → `monomorphise_call` → `monomorphise_inner_parametric_hops` spine (no second entry point — /arch Phase-2 ruling, Principle 7); cluster-level dedup keyed on the existing mangled name; the root set; the exact functions to extend and the current subset-coverage gaps. (2) The unconstrained-top-level-var **ambiguity check** (0373 part ii) — fired at the post-generalisation finalisation boundary, before Pass 4 (`finalize_check_result_inner`, after the first `regeneralize_defn_schemes` and before `pass4_monomorphise`), raising `CranelispError::TypeError` today and the dedicated `CheckError::AmbiguousType` post-FIXME-0098 (both typecheck-internal; no new `cranelisp-types` item). Termination is bounded by monomorphic-recursion enforcement (rank-1 HM). This master doc commits to the shape `monomorphisation.md` elaborates; that doc wins on detail.

FIXME 0033 (`monodefn-redundant-side-maps`) — **Step A done; Step B is the field-drop.** `MonoDefn` (`cranelisp-types::check`) carries two Span-keyed side maps, `resolutions: MethodResolutions` and `expr_types: HashMap<Span, Type>`, that were redundant once monomorphisation annotated the AST directly. Step A landed: `traits.rs::monomorphise_call` now annotates `mono_defn.defn` in place (via `annotate_defn_from_maps` + `apply_subst_to_defn`) and **constructs `MonoDefn` with `MethodResolutions::default()` + an empty `HashMap`** — the fields are no longer populated in production. The only surviving reads are `#[cfg(test)]` scaffolding in `cranelisp-backend` (`test_compile_program_and_run`, which merges `mono.resolutions` and falls back on `mono.expr_types`). Step B is the structural removal: drop both fields, making `MonoDefn` a `Defn` newtype (or a single-field wrapper); update the one backend test to read annotations off `mono.defn` directly. **Baseline impact:** removes three `cranelisp_types::MonoDefn::{expr_types, resolutions}` lines from `crates/cranelisp-types/public-api.txt` (regenerate per the baseline-diff discipline). The field-drop and the types-crate baseline regen are `/dev`-on-`cranelisp-types` work (the struct lives in the interface crate, `/arch`-adjacent); the backend test edit is `/dev`-on-`cranelisp-backend`. Coordinate as a small two-crate change.

### 9.4 ADT typing

`TypeDefInfo` + `ConstructorInfo` + `FieldInfo` describe the registered ADTs. Pattern matching infers via standard unification + nominal constructor-to-type resolution. Exhaustiveness is checked in `adt.rs`. Polymorphic ADTs with data-constructor fields fully supported (e.g., `(Some [:a val])`).

### 9.5 HKT — `hkt.md`

Constructor variables (e.g., `:Functor f`, where `f` is a type-constructor variable) supported via `Type::TyConApp` and a parallel impl-method check path (`check_hkt_impl_method`). The audit Finding 3 highlights this as the duplicate-tail risk; the resolution is to share the post-resolution finalization step, keeping only the type-resolution front halves separate (audit remediation #2).

### 9.6 Multi-sig dispatch + auto-curry

`DefnMulti` defns produce one `ModuleEntry::Def` per signature variant (mangled `name$Type1+Type2`). Dispatch happens post-inference when concrete arg types match a variant. Auto-curry (calling with fewer args than declared) interacts with multi-sig — this is the most subtle interaction in the crate (memory: "GOTCHA: multi-sig + constrained polymorphism interaction not yet supported"). Documented in `auto-curry.md`.

FIXME 0043 (`typecheck-resolved-call-autocurry-total-count`) is open — `ResolvedCall::AutoCurry` is missing `total_count` per the sketch; either extend the type or look up at codegen time. `/typecheck` and `/backend` coordinate the resolution.

---

## 10. Subordinate topic docs

| Topic | Doc | Status |
|---|---|---|
| Algorithm-W & substitution strategy | `inference.md` | Current |
| Trait registry, impl recording, monomorphisation, default methods | `traits.md` | Current |
| **Monomorphisation from roots — Tier 2 full mono (no `Type::Var` at codegen) + the unconstrained-var ambiguity check** | **`monomorphisation.md`** | **Current** (Sprint 84 Phase 3, Cluster A). Pins the reachable-instance worklist EXTENDING the Tier-1/1.5 `pass4_monomorphise` spine (FIXME 0374), the ambiguity check at the finalisation boundary (FIXME 0373 ii), the variant + wording, the unit-test seams, and the termination argument. Cites `traits.md §7` (as-built pipeline it completes). |
| HKT (`Type::TyConApp`, `check_hkt_impl_method`) | `hkt.md` | Current |
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
- `design/arch/fixmes/0374-typecheck-tier2-full-monomorphisation-from-roots.md` — Tier-2 spine (primary S84 deliverable)
- `design/arch/fixmes/0373-spec-rank1-hm-defaulting-and-section-12-1-representation-relaxation.md` — rank-1 HM + ambiguity rule (part ii realised as the typecheck check) + §12.1 relaxation
- `design/typecheck/{check-form-api,dashmap-migration,stateless-tc-impl,sprint50-fixes}.md` — historical / superseded subordinate docs (see §10)
