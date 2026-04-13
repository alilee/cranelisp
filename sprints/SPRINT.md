# Sprint 51: Stateless TypeChecker

**Status**: ACTIVE
**Ring**: 4 (Effects — stabilisation)
**Goal**: Make the TypeChecker fully stateless — all persistent state eliminated or moved to SharedState/scheduler, global registries replaced by per-module resolution through the module system, FQTypeName migration, `CompilerSession.tc` deleted. Fix all 11 cache test failures.

## Scope

TypeChecker currently holds 7 fields of persistent state. All of it is either derived indexes over per-module data (should be eliminated), scheduling state (belongs on the scheduler), or per-invocation state (belongs on the stack).

### The registry problem

Three global registries (`type_defs: TypeDefRegistry`, `trait_registry: TraitRegistry`, `impl_registry: ImplRegistry`) are keyed by bare `TypeName`/`TraitName` — no module qualification. But the same data already lives on per-module SymbolTables as `ModuleEntry::TypeDef`, `ModuleEntry::TraitDecl`, and `ModuleEntry::Constructor`. The registries are derived caches. `restore_cached_module()` proves this: it reconstructs the registries from SymbolTable entries.

These caches create sync bugs (like the current parallel symbol table divergence) and will collide on bare names when two modules define types with the same name. The fix is: eliminate the global registries entirely, resolve type/trait/impl lookups through the module system using fully-qualified names.

This converges with the planned FQTypeName migration (`TypeName` → `FQTypeName { module: ModuleFullPath, name: TypeName }`). Bare-name global lookup goes away; all resolution follows import chains through SymbolTables.

### TC field disposition

| Field | Current | Target | Rationale |
|-------|---------|--------|-----------|
| `modules` | `DashMap<ModuleFullPath, SymbolTable>` | SharedState | Cross-module shared data. Root cause of cache failures. |
| `type_defs` | `RwLock<TypeDefRegistry>` | **Deleted** | Derived cache. Per-module TypeDef entries on SymbolTable are the source of truth. Lookups go through module system with FQTypeName. |
| `trait_registry` | `RwLock<TraitRegistry>` | **Deleted** | Derived cache. Per-module TraitDecl entries on SymbolTable are the source of truth. |
| `impl_registry` | `RwLock<ImplRegistry>` | **Deleted** | Derived cache. Impl entries on SymbolTable are the source of truth. |
| `next_id` | `AtomicU32` | SharedState `AtomicU32` | Monotonic counter. No semantic coupling to TC. |
| `module_locks` | `Mutex<HashMap<...>>` | Scheduler (or deleted) | Compilation scheduling. Scheduler already tracks module lifecycle. |
| `state` (CheckState) | On TC struct | Stack-local per `check()` call | Per-invocation: subst, env, expr_types, etc. Created fresh each call. |
| — REPL carry-forward | `module_aliases`, `overloads`, `resolved_overloads` | SharedState REPL state | 3 fields that persist across REPL evals. |

### FQTypeName migration

`TypeName` (bare string) → `FQTypeName { module: ModuleFullPath, name: TypeName }` throughout boundary types. This is the FIXME at `types.rs:23` and `checker.rs:423`. All type resolution becomes module-qualified. The `type_modules` map in checker.rs (which maps TypeName → ModuleFullPath) becomes unnecessary — the module is embedded in FQTypeName.

**In scope:**

1. **Stateless TC**: Extract `modules` and `next_id` to SharedState. Delete `type_defs`, `trait_registry`, `impl_registry` (replace with module-system resolution). Make CheckState stack-local. Move REPL carry-forward to SharedState. Move/delete `module_locks`. Delete `CompilerSession.tc`. TC becomes free functions or worker-local.

2. **FQTypeName migration**: `TypeName` → `FQTypeName` in boundary types. Eliminate `type_modules` map. All type/trait/impl resolution through module system using qualified names.

3. **Registry elimination**: Delete `TypeDefRegistry`, `TraitRegistry`, `ImplRegistry` structs. Add `ModuleEntry::TraitImpl` variant to SymbolTable (impls are not currently first-class module entries — they only exist in the global `ImplRegistry`). Type/trait/impl lookups resolve through SymbolTable import chains to the defining module's `ModuleEntry::TypeDef`/`ModuleEntry::TraitDecl`/`ModuleEntry::TraitImpl`. `constructor_to_type` replaced by module-system lookup.

4. **Cache infrastructure fix** (11 tests): Once symbol tables live on SharedState and are the single source of truth (no parallel copies, no derived caches), nice workers can read populated symbol tables for `.meta.json` manifest writing. Also fix cache test file layout.

**Out of scope (Sprint 52):**
- Sketch-port triage (13 failures)
- IO/platform failures (3 tests)
- Checked division (2 tests)
- Ring 2 failures (2 tests)
- E2E imported fn HOF (1 test)
- Sprint 23 test triage (FIXME(/qa), 2x deferred)
- Remaining FIXMEs not resolved by this refactor
- Post-restructure architecture document
- Prior-ring spec traceability

**Success criteria:** All 11 cache tests pass. No regressions in the other 1509 passing tests. `CompilerSession.tc` field deleted. TypeChecker struct has no owned persistent state. `TypeDefRegistry`, `TraitRegistry`, `ImplRegistry` deleted. FQTypeName in use throughout boundary types. FIXMEs at `types.rs:23` and `checker.rs:423` resolved.

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `checker.rs:423` | /arch | FQTypeName migration | **in scope — resolved by FQTypeName migration** |
| `types.rs:23` | /arch | TypeName → FQTypeName | **in scope — resolved by FQTypeName migration** |
| `linker.rs:231` | /backend | BL range for runtime intrinsics | carried — Sprint 52 |
| `sprint23.rs:11` | /qa | Sprint23 tests disabled for v4 | carried — Sprint 52 (**2x deferred, must ship S52**) |
| `v4_pipeline.rs:359` | /frontend | Macro define-before-use not enforced | carried — Sprint 52 |
| `spec/08-modules.md:82` | /spec | Remove sibling fallback rule | carried — Sprint 52 |
| `session_v4.rs:3070` | /arch | Object codegen CodegenInput | carried — Sprint 52 |
| `worker.rs:1153` | /int | Dead code comment | carried — Sprint 52 |
| `worker.rs:1936` | /backend | Dep symbol compilation | carried — Sprint 52 |
| `worker.rs:2752` | /int | process_module_forms refactor | carried — Sprint 52 |

## Architecture Review

**Reviewer**: `/arch`
**Verdict**: APPROVED WITH CHANGES

**Technical coherence**: The three pieces are genuinely entangled and form a natural unit. FQTypeName is needed to make registry elimination possible; registry elimination is what makes stateless TC possible; the cache fix is a natural consequence. No hidden dependencies beyond what the plan identifies.

**No interim architecture**: PASS. The module-system resolution helper is target architecture. However, `CheckResult.type_defs` and `CheckResult.constructor_to_type` key types must be specified as FQTypeName (not left as bare TypeName — that would be semantically inconsistent).

**Critical finding — impl lookup strategy undefined (BLOCKER)**:

There is no `ModuleEntry::TraitImpl` variant on SymbolTable today. The sprint plan says "Impl entries on SymbolTable are the source of truth" but this is incorrect — impls are only recorded in the global `ImplRegistry`, not as SymbolTable entries. `restore_cached_module()` reconstructs impls by parsing mangled JIT names, not from SymbolTable data.

**Required**: Add a `ModuleEntry::TraitImpl` variant that records `(trait_name, impl_type)` pairs, making impls first-class module entries. This enables impl resolution through the module system. The design doc must specify the impl search strategy (trait's module, type's module, current module — analogous to Haskell's orphan instance rules).

**Concrete resolution path — `(+ x y)` after registry elimination:**
1. Look up `+` in scope → find scheme with constraint `Num` on var0
2. Resolve dispatch arg to concrete type `Int`
3. Look up `Num` trait's defining module (follow import chain from `+`'s source). Find `ModuleEntry::TraitDecl` for `Num` there.
4. Search for `ModuleEntry::TraitImpl { trait_name: "Num", impl_type: FQTypeName("primitives", "Int") }` in the trait's module, type's module, or current module.
5. Emit `ResolvedCall::TraitMethod { ... }`

**Interface changes required by design doc:**
- `Type::ADT(TypeName, Vec<Type>)` → `Type::ADT(FQTypeName, Vec<Type>)` — every pattern match on `Type::ADT` changes
- `CheckResult.type_defs: HashMap<TypeName, TypeDefInfo>` → `HashMap<FQTypeName, TypeDefInfo>`
- `CheckResult.constructor_to_type: HashMap<Symbol, TypeName>` → `HashMap<Symbol, FQTypeName>`
- `TypeDefInfo.name: TypeName` → `FQTypeName`
- `CodegenInput` duplicated fields must use FQTypeName too
- New `ModuleEntry::TraitImpl { trait_name: TraitName, impl_type: FQTypeName, methods: Vec<Symbol> }`

**Blast radius**: FQTypeName in cranelisp-types changes a shared boundary crate. All downstream crates break simultaneously until migrated. Must be an atomic branch — Wave 3a changes cranelisp-types, Wave 3b fixes all crates before the tree compiles.

**Risk assessment:**
- **Size (HIGH)**: ~200+ sites across every crate. Mitigated by mechanical nature + test coverage.
- **Ordering (MEDIUM)**: FQTypeName big-bang breaks all crates until migrated. Feature branch recommended.
- **Impl lookup (MEDIUM)**: Design gap — must be resolved in design doc before coding.
- **Critical path**: /typecheck is the bottleneck. Registry elimination + resolution rewrite is the novel engineering; everything else is mechanical.

**Benefits confirmed:**
- `build_type_modules()` in session_v4.rs (called ~10 times for REPL display) eliminated by FQTypeName
- Three `RwLock<Registry>` fields deleted, improving DashMap guard discipline
- Two FIXMEs resolved (`types.rs:23`, `checker.rs:423`)

## Skill Plans

### /arch
**Task**: Write stateless TC design doc `design/arch/stateless-tc.md` covering the full refactor: stateless TC + FQTypeName + registry elimination.
**Design doc**: `design/arch/stateless-tc.md` (new)
**Approach**: {to be filled by /arch}
**Design refs**: `design/arch/archive/session-restructure.md`, `design/arch/CLAUDE.md` Decisions 9+newtypes, `crates/cranelisp-typecheck/src/checker.rs`, `crates/cranelisp-typecheck/src/adt.rs` (TypeDefRegistry), `crates/cranelisp-typecheck/src/traits.rs` (TraitRegistry, ImplRegistry), `crates/cranelisp-types/src/types.rs` (TypeName), `src/session_v4.rs` (SharedState, CompilerSession), `src/worker.rs`
**Acceptance**: Design doc covers: (1) FQTypeName definition and migration path, (2) registry elimination — how type/trait/impl lookups resolve through module system, (3) `ModuleEntry::TraitImpl` variant specification, (4) impl search strategy (trait's module, type's module, current module), (5) TC public API as free functions, (6) SharedState additions (modules DashMap, next_type_id), (7) CheckState stack-local with REPL carry-forward on SharedState, (8) module_locks disposition, (9) builtins bootstrapping as free function, (10) cache manifest population path, (11) exact changes to `Type::ADT`, `TypeDefInfo`, `CheckResult`, `CodegenInput`, (12) `build_type_modules()` elimination, (13) sketch comparison.

### /typecheck
**Task**: (A) Refactor TypeChecker to stateless — extract all shared state, make CheckState stack-local. (B) Delete TypeDefRegistry, TraitRegistry, ImplRegistry — replace all lookups with module-system resolution using FQTypeName. (C) Migrate TypeName → FQTypeName throughout typecheck crate.
**Design doc**: `design/typecheck/stateless-tc-impl.md` (new)
**Approach**: {to be filled by /typecheck}
**Design refs**: `design/arch/stateless-tc.md`, `checker.rs`, `adt.rs`, `traits.rs`, `infer.rs`, `program.rs`, `scheme.rs`, `unify.rs`, `builtins.rs`
**Acceptance**: TypeChecker has no owned persistent state. Three registry structs deleted. All type/trait/impl resolution goes through module system. FQTypeName in typecheck crate. All existing passing tests pass.

### /backend
**Task**: (A) Migrate TypeName → FQTypeName in backend crate (CheckResult consumers, match codegen, ADT tag lookup). (B) Fix cache manifest writing to read from SharedState symbol tables. (C) Remove TypecheckProduct.symbols field. (D) Fix cache test file layout.
**Design doc**: `design/backend/sprint51-fqtypename-cache.md` (new)
**Approach**: {to be filled by /backend}
**Design refs**: `design/arch/stateless-tc.md`, `crates/cranelisp-backend/src/`, `crates/cranelisp-types/src/check.rs` (CheckResult), `src/session_v4.rs:3070-3133`
**Acceptance**: All 11 cache tests pass. TypecheckProduct.symbols removed. FQTypeName in backend crate.

### /frontend
**Task**: Migrate TypeName → FQTypeName in frontend crate if applicable (AST builder, expander).
**Design doc**: n/a (mechanical migration)
**Approach**: {to be filled by /frontend}
**Design refs**: `design/arch/stateless-tc.md`, `crates/cranelisp-frontend/src/`
**Acceptance**: FQTypeName in frontend crate where needed. All existing tests pass.

### /int
**Task**: (A) Add modules DashMap + next_type_id + REPL carry-forward state to SharedState. (B) Delete `CompilerSession.tc` field. (C) Update all TC call sites in session_v4.rs and worker.rs to use free functions with `&SharedState`. (D) Wire builtins registration into session startup. (E) Move/delete module_locks. (F) Migrate TypeName → FQTypeName in integration layer.
**Design doc**: n/a (wiring work driven by /arch design doc)
**Approach**:

**1. SharedState additions** (`session_v4.rs`):

Add the following fields to `SharedState`, which is already `Arc`-shared between main thread and nice workers:

- `symbol_tables: DashMap<ModuleFullPath, SymbolTable>` — migrated from `TypeChecker.modules`. This is the single source of truth for per-module symbol data. Currently the TC owns a `DashMap<ModuleFullPath, SymbolTable>` that the integration layer accesses via `tc.modules_ref()` (~12 call sites in session_v4.rs, ~8 in worker.rs). After: all sites use `shared.symbol_tables` directly.
- `next_type_id: AtomicU32` — migrated from `TypeChecker.next_id`. Monotonic counter for fresh type variables. Passed to TC free functions that need fresh IDs.
- `impl_index: Mutex<HashMap<(FQTypeName, FQTraitName), ModuleFullPath>>` — new, per `traitimpl-symbol-table.md`. Populated when modules load (fresh compilation or cache-hit). Used for O(1) impl lookup and cross-module duplicate detection. Behind `Mutex` because multiple priority workers may register impls concurrently.
- `current_module: Mutex<ModuleFullPath>` — REPL carry-forward. Currently `tc.current_module_path()`. Tracks which module the REPL prompt targets (`/mod` command). Only meaningful in REPL mode; batch compilation sets it per-worker. Behind `Mutex` for thread safety.
- `module_aliases: Mutex<HashMap<Symbol, ModuleFullPath>>` — REPL carry-forward. Currently on `CheckState` inside TC (field `state.module_aliases`). Persists across REPL evals so `(import [opt core.option])` alias survives.
- `overloads: Mutex<HashMap<Symbol, Vec<(Symbol, usize)>>>` — REPL carry-forward. Currently on `CheckState`. Multi-sig dispatch table persists across REPL evals.
- `resolved_overloads: Mutex<HashMap<Symbol, Vec<(Vec<Type>, Type, Symbol)>>>` — REPL carry-forward. Currently on `CheckState`. Resolved overload type info persists across evals.
- `repl_subst: Mutex<Subst>` — REPL carry-forward. Currently on `CheckState.subst`. Unification bindings must persist across REPL evals so that type variables from one eval are visible in the next (e.g., `(let [x 3])` → `x` has type `Int` in subsequent evals).
- `repl_env: Mutex<ScopeStack>` — REPL carry-forward. Currently on `CheckState.env`. Lexical scope must persist across evals so bindings survive.

Note: all 5 REPL carry-forward fields (`module_aliases`, `overloads`, `resolved_overloads`, `repl_subst`, `repl_env`) could be bundled into a `ReplTypeState` struct on SharedState for cleaner organization. The `/typecheck` design doc proposes this pattern.

**2. CompilerSession.tc deletion** (`session_v4.rs`):

Delete `pub tc: cranelisp_typecheck::TypeChecker` from `CompilerSession`. The TC struct no longer holds persistent state — it either becomes free functions or a transient worker-local value. The ~55 `self.tc.*` call sites in session_v4.rs and ~35 `ctx.tc.*` sites in worker.rs break down into these replacement patterns:

| Current pattern | Count (approx) | Replacement |
|---|---|---|
| `tc.current_module_path()` | 15 | `shared.current_module.lock()` (REPL) or worker-local module from scheduler (batch) |
| `tc.symbol_table()` / `tc.module_table(m)` | 14 | `shared.symbol_tables.get(&module)` |
| `tc.modules_ref()` / `tc.modules()` | 12 | `&shared.symbol_tables` (already a DashMap ref) |
| `tc.check_form()` / `tc.merge_form_result()` / `tc.finalize_check_result()` | 10 | Free functions: `typecheck::check_form(&shared.symbol_tables, &shared.next_type_id, ...)`. CheckState is stack-local, created per invocation. |
| `tc.set_current_module(m)` | 4 | `*shared.current_module.lock() = m` (REPL) or worker-local (batch) |
| `tc.register_imports()` / `tc.register_exports()` | 8 | Free functions operating on `&shared.symbol_tables` |
| `tc.has_module(m)` | 4 | `shared.symbol_tables.contains_key(m)` |
| `tc.snapshot()` / `tc.restore()` | 4 | Snapshot/restore operates on the REPL carry-forward Mutex fields. For error recovery: clone the carry-forward state before eval, restore on error. |
| `tc.check(&[input], &ctx, Additive)` | 1 | Free function with `&shared.symbol_tables`, carry-forward refs |
| `tc.resolve_module_by_name()` | 1 | Free function or helper on SharedState |
| `tc.type_def_registry()` / `tc.get_type_constructors()` / `tc.get_impls_for_type()` / `tc.get_trait_methods()` / `tc.get_implementing_types()` / `tc.defining_module_for()` | 8 | **Deleted** — these query the global registries being eliminated. Replaced by SymbolTable lookups: scan `shared.symbol_tables` for `ModuleEntry::TypeDef`, `ModuleEntry::TraitDecl`, `ModuleEntry::TraitImpl`. The `impl_index` provides O(1) impl lookup. |
| `tc.compute_display_info_public()` | 1 | Free function with SymbolTable refs |
| `tc.restore_cached_module()` / `tc.restore_cached_impls()` | 2 | Insert SymbolTable into `shared.symbol_tables`; register TraitImpl entries in `shared.impl_index`. `restore_cached_impls()` deleted entirely (TraitImpl entries are on the SymbolTable, serialized in .meta.json). |
| `tc.clear_module_for_replace_public()` | 1 | Direct SymbolTable manipulation on `shared.symbol_tables` |
| `tc.take_state()` / `tc.restore_state()` | 2 | No longer needed — CheckState is stack-local per check invocation |

The `std::mem::replace(&mut self.tc, TypeChecker::new())` pattern (lines 775, 867) for moving TC into worker threads disappears. Workers receive `&SharedState` directly (symbol_tables, next_type_id, impl_index are all on SharedState). `PriorityWorkerRefs.tc` field deleted; replaced by `shared_state` ref which already exists.

**3. build_type_modules() deletion** (`session_v4.rs`):

Called at 4 sites (lines 1285, 1850, 1876, 2616) to build `HashMap<TypeName, ModuleFullPath>` by scanning all symbol tables. With FQTypeName, `Type::ADT(fqtn, args)` carries the module directly. All 4 call sites and the function definition (line 1638) are deleted. The `type_modules` parameter is removed from `format_type_qualified()`, `format_scheme_display()`, `format_value()`, `format_result_value()` throughout the display API.

**4. TypecheckProduct changes** (`session_v4.rs`):

Delete `pub symbols: SymbolTable` from `TypecheckProduct` (line 383). Symbol tables now live on `SharedState.symbol_tables`. TypecheckProduct retains:
- `pub got: Arc<GotTable>` — per-module GOT, stable base address
- `pub file_path: Option<PathBuf>` — source file for introspection
- `pub source_text: Option<String>` — source text for /source command

The 1 site reading `tp.symbols` (nice worker .meta.json at line 3122) moves to `shared.symbol_tables.get(module)`.

**5. CodegenInput changes** (`session_v4.rs`):

Delete from `CodegenInput`:
- `pub type_defs: HashMap<TypeName, TypeDefInfo>` (line 412) — backend reads from `shared.symbol_tables` via `ModuleEntry::TypeDef`
- `pub constructor_to_type: HashMap<Symbol, TypeName>` (line 414) — backend resolves constructors via `ModuleEntry::Constructor` on SymbolTables

CodegenInput retains: `method_resolutions`, `expr_types`, `mono_defns`, `default_method_defns`, `program`, `cross_module_func_sigs`. The `compile_module_object()` function (line 3072) no longer copies `type_defs`/`constructor_to_type` into the reconstructed CheckResult.

**6. snapshot_type_defs() deletion**:

Called at 4 sites:
- `session_v4.rs:1284` — REPL eval, populating type_defs for display. Replaced by direct SymbolTable lookup using FQTypeName.
- `worker.rs:594` — priority worker stashing CodegenInput. No longer needed (type_defs/constructor_to_type deleted from CodegenInput).
- `worker.rs:1950, 1974` — similar stash sites. Same deletion.

The `snapshot_type_defs()` method on TypeChecker is deleted by /typecheck.

**7. Nice worker .meta.json write** (`session_v4.rs:3119-3133`):

Currently reads `shared.typecheck_products.get(module).map(|tp| tp.symbols.clone())`. After TypecheckProduct.symbols is deleted, reads from `shared.symbol_tables.get(module).map(|table| table.clone())`. This is actually simpler — one fewer indirection. The SymbolTable now includes `ModuleEntry::TraitImpl` entries, which get serialized into .meta.json automatically (Serde derives on ModuleEntry).

**8. impl_index wiring**:

Populated at two points in the pipeline:

- **Fresh compilation** (worker.rs, after `finalize_check_result()`): When a module's typecheck completes, scan its SymbolTable for `ModuleEntry::TraitImpl` entries. For each, insert `(impl_type, trait_name) -> module` into `shared.impl_index`. Check for duplicates (different module already registered same pair = error).

- **Cache-hit restoration** (worker.rs, in `try_cache_hit_load()` / `restore_cached_module()`): After installing the cached SymbolTable into `shared.symbol_tables`, scan for `TraitImpl` entries and populate `shared.impl_index` identically. This replaces the current `restore_cached_impls()` which reverse-engineers impls from mangled JIT names.

Both paths converge on a shared helper: `register_module_impls(shared: &SharedState, module: &ModuleFullPath) -> Result<(), CranelispError>` that scans the module's SymbolTable and populates `impl_index`.

**9. ReadOnlyMacroResolver update** (`session_v4.rs:39-86`):

Currently holds `tc: &TypeChecker`. After: holds `symbol_tables: &DashMap<ModuleFullPath, SymbolTable>`. The `resolve_macro_definition()` call (line 52-53) already takes a TC ref for SymbolTable access — update to take `&DashMap` directly.

**10. SessionCompilationEnv update** (`worker.rs:62`):

Currently holds `tc_modules: &DashMap<ModuleFullPath, SymbolTable>` sourced from `tc.modules_ref()`. After: sourced from `shared.symbol_tables`. The field type stays the same — only the construction site changes.

**11. Builtins registration** (session startup):

Currently `TypeChecker::new()` registers builtins internally (primitives module SymbolTable). After: builtins registration is a free function called during `CompilerSession::new()` that populates `shared.symbol_tables` with the `primitives` module's SymbolTable and `shared.impl_index` with any builtin impls. Called once at session startup before any user modules load.

**12. module_locks disposition**:

`module_locks` is already absent from the integration layer (confirmed by grep). The scheduler already tracks module lifecycle. If /typecheck still has `module_locks` on the TC struct, it is deleted as part of TC statelessness — no /int action needed.

**Ordering**: Items 1 (SharedState additions) and 11 (builtins) land first. Then 2-6 (TC deletion + call site migration) as one atomic change. Then 3, 7, 8 (deletions + impl_index). Item 12 is a no-op for /int.

**Design refs**: `design/arch/stateless-tc.md`, `design/arch/fqtypename.md`, `design/arch/traitimpl-symbol-table.md`, `src/session_v4.rs`, `src/worker.rs`
**Acceptance**: `CompilerSession.tc` deleted. All TC access via SharedState. FQTypeName in integration layer. All existing passing tests pass.

### /qa
**Task**: (A) Verify cache tests pass. (B) Run full suite for regressions. (C) Migrate TypeName → FQTypeName in test assertions where needed.
**Acceptance**: 11 cache tests pass. Full suite: 1520 passed, 21 failed (32 total failures minus 11 cache = 21 pre-existing non-cache failures unchanged).

### /repl
**Task**: Create sprint demo `repl/demos/ring4j.demo` showcasing cache and any visible improvements from FQTypeName (e.g., better qualified type display).
**Acceptance**: Demo plays cleanly. All prior demos play cleanly.

### /port
**Task**: Validate exemplar compiles after refactor.
**Acceptance**: Exemplar batch mode runs.

### /stdlib
**Task**: Validate stdlib compiles after refactor.
**Acceptance**: All 54 stdlib tests pass.

### /examples
**Task**: Verify all examples compile and run.
**Acceptance**: All `examples/*.cl` run successfully.

### /review
**Task**: Code review of stateless TC + FQTypeName + registry elimination + cache fixes.
**Acceptance**: 0 Blockers, all Important findings addressed.

### /docs, /platform, /spec, /sprint
**Task**: No assignment this sprint.

## Waves

### Wave 1: Design (COMPLETE)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Write `fqtypename.md` + `traitimpl-symbol-table.md` | done | 2 design sketches, 3 rounds of review |
| /typecheck | Write `stateless-tc-impl.md` | done | TypeCheckEnv, registry elimination, 5-phase migration |
| /backend | Write `sprint51-fqtypename-cache.md` | done | Direct DashMap access, no snapshot/trait |
| /int | Fill SPRINT.md approach | done | 12-point plan, ~90 call sites catalogued |

### Wave 2: Design review (COMPLETE)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review all design docs | done | APPROVED WITH CHANGES — 2 blockers fixed (REPL subst/env, TP.symbols) |

### Wave 3a: Boundary type changes in cranelisp-types (tree breaks)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Add FQTypeName, FQTraitName structs to newtype.rs | pending | |
| /typecheck | Change Type::ADT(TypeName) → Type::ADT(FQTypeName) | pending | ~182 downstream sites break |
| /typecheck | Add ModuleEntry::TraitImpl variant | pending | Per traitimpl-symbol-table.md |
| /typecheck | Add trait_origin: Option\<FQTraitName\> on ModuleEntry::Def | pending | Replaces method_to_trait |
| /typecheck | Change ModuleEntry::Constructor.type_name: Symbol → FQTypeName | pending | |
| /typecheck | Change ResolvedCall::TraitMethod fields → FQTypeName/FQTraitName | pending | |
| /typecheck | Change Scheme.constraints → Vec\<FQTraitName\> | pending | |
| /typecheck | Delete CheckResult.type_defs + constructor_to_type fields | pending | Backend reads DashMap directly |
| /typecheck | Change HeapCategory::classify signature → &DashMap | pending | cranelisp-types adds dashmap dep |

### Wave 3b: All crates fix in parallel (tree compiles again)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Stateless TC: extract all state, delete registries, TypeCheckEnv, module-system resolution | pending | Critical path — registry elimination |
| /backend | FQTypeName migration: CompileContext gets &DashMap, display simplification, ObjectCompileInput slimmed | pending | |
| /frontend | FQTypeName migration if needed (likely minimal — frontend produces TypeExpr not Type) | pending | |
| /int | SharedState additions (7 fields), CompilerSession.tc deletion, build_type_modules deletion, builtins wiring, impl_index wiring | pending | ~90 call sites |

### Wave 4: Build/test/review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Run full suite, triage failures, verify 11 cache tests pass | pending | Target: 1520 pass, 21 fail |
| /review | Code review of all new/changed code | pending | 0 Blockers required |
| all | Fix failures + review findings, iterate | pending | |

### Wave 5: Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Create sprint demo repl/demos/ring4j.demo | pending | Cache working, FQTypeName display |
| /port | Validate exemplar compiles | pending | |
| /stdlib | Validate stdlib compiles | pending | |
| /examples | Verify all examples run | pending | |

## Notes

- **This is a large refactor**. FQTypeName touches boundary types (cranelisp-types), which ripple through every crate. The registry elimination changes how typechecking resolves types/traits/impls. The stateless TC changes every TC call site. Mitigated by: (a) most changes are mechanical, (b) existing tests validate correctness, (c) the three pieces are logically entangled (doing them separately would create interim architecture).
- **FQTypeName must land in cranelisp-types first** — it's a boundary type change that all crates depend on. Wave 3 must be phased.
- **Registry elimination may need a transitional lookup helper** — a function that walks import chains to find a TypeDef/TraitDecl. This is the module-system resolution path that replaces the flat HashMap. Not interim architecture — it's the target lookup mechanism.
- **Cache test file layout**: `cache_multi_module_transitive_imports` has an independent file layout bug. /backend should fix regardless.
- **2 FIXMEs resolved**: `types.rs:23` and `checker.rs:423` are directly addressed by FQTypeName migration.
- **Sprint 23 FIXME will be 3x deferred** — requires user approval at Sprint 52 scoping.

## Outcome

{To be filled at sprint close}

### Delivered
- {TBD}

### Deferred
- {TBD}

### Findings
- {TBD}
