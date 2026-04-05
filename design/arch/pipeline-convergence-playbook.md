# Pipeline Convergence Playbook

Status as of Sprint 49, 2026-04-05.

Commits landed:
- `a642185` — phase 1 structural detach (inner removed, EvalResult redesigned, test adapter built)
- `9c6a475` — ADT display qualification fix + FQTypeName FIXME
- `5c09343` — step 1.7 old pipeline deletion (~7k lines removed)
- `43eab15` — mark Phase 1 complete in convergence playbook
- (pending) — Phase 2 display formatting fix + test validation

## What's Done

### Phase 1 Steps (structural cleanup)
- [x] 1.3 Delete `load_prelude()` — was dead code
- [x] 1.4 Delete `link()`, `run_with_workers()`, `run_with_nice_workers()`, stub spawners
- [x] 1.5 Remove `inner: Option<CompilationSession>` from `CompilerSession`
- [x] 1.6 (partial) Test adapter `ReplSession` in `tests/helpers/mod.rs` wrapping `CompilerSession`
- [x] 1.6 (complete) Port ALL test files to v4 helpers
- [x] 1.7 Delete old pipeline code (see §Deletions below)
- [x] 1.8 Clean run() in main.rs — already v4-only, no old paths remain
- [x] 1.9 Verify compilation — `cargo check` clean, `ring0` 106/108 (2 pre-existing)

### Phase 1 Steps (persistent workers) — DONE
- [x] 1.1 Persistent workers on CompilerSession — scoped threads in `register_module_with_source`
- [x] 1.2 `register_module` enqueues for workers — workers use `take_priority_work_blocking`

### Phase 2 Steps
- [x] 2.0 Scheduler unit tests — 18/18 pass
- [x] 2.1 Worker pool lifecycle — scoped threads join on scope exit, shutdown via scheduler
- [x] 2.2 Single trivial module — covered by ring0 (106/108)
- [x] 2.3 Prelude loading — stdlib 38/54 pass (16 are macro pipeline gaps)
- [x] 2.4 Import chains — partially working (modules 18/22, ring2 189/197)
- [ ] 2.5 REPL eval with prelude — not yet validated
- [x] 2.6 REPL error recovery — working for non-prelude sessions
- [x] 2.7 Integration tests (progressive) — ring0–ring3 validated, see table below
- [ ] 2.8 E2E tests — v4_pipeline needs `--v4` flag removal; subprocess tests need porting
- [ ] 2.9 Link mode E2E — not attempted
- [ ] 2.10 Full test suite — macro pipeline gaps remain (see §Remaining Work)

### Display Formatting Fix (Phase 2)
Ported rich REPL display formatting from old `src/repl/commands.rs` into `src/session_v4.rs`. The v4 pipeline's `format_eval_result` now produces the spec-compliant universal output format (spec §1.1):

- Functions: `:(Fn [primitives/Int] primitives/Int) user/square ; defn`
- Macros: `:user/name ; defmacro` + `; [params] -> Sexp` clause signatures
- Types: `:user/Point ; deftype` + `; match:` constructors + `; impl:` traits
- Traits: `:user/Num ; deftrait` + `; defn:` methods + `; impl:` types
- Special forms: `:(Fn [primitives/Bool a a] a) if ; special form - description`
- Builtin types: `:primitives/Int ; type` + `; impl:` traits
- TraitImpl: `impl user/Trait for user/Type`

`check_bare_symbol_introspection` now handles all symbol kinds: builtin types, user types, traits, macros, non-nullary constructors, special forms, and follows import/reexport chains.

### EvalResult Redesign
`EvalResult` is now an enum:
```rust
pub enum EvalResult {
    Def { symbol: FQSymbol, ty: Type, warnings: Vec<Warning> },
    Val { value: i64, ty: Type, warnings: Vec<Warning> },
}
```
Accessor methods: `.value()` (returns 0 for Def), `.ty()`, `.is_def()`, `.warnings()`.

### Test Infrastructure
Three test entry points, all through v4 `CompilerSession`:

| Helper | Purpose | Prelude |
|--------|---------|---------|
| `helpers::ReplSession` | Incremental eval (Additive) | Depends on constructor |
| `helpers::batch_run(src)` | Single-source batch (defn main + trampoline) | None (bare session) |
| `helpers::batch_run_file(path, lib_dirs)` | Multi-file batch (file discovery + trampoline) | Via lib_dirs |

**ReplSession constructors:**
- `new()` — bare, no prelude. Uses `tests/fixtures` as project_root + empty lib_dirs to avoid accidental stdlib discovery.
- `new_with_prelude(project_root, &[lib_dir])` — loads prelude from lib_dir via `register_module("user")`.
- `new_for_file(entry_path, &[lib_dirs])` — project_root from entry file's parent. For multi-file batch.

**ReplSession methods (delegating to CompilerSession):**
- `eval(src)` — returns `Result<EvalResult, CranelispError>` (None→synthetic Val)
- `register_module(name)` — resolves file from lib_dirs
- `register_module_with_source(name, source)` — explicit source
- `trampoline(module_name)` — execute main, returns `(i64, Type)`. Auto-unwraps IO.

### ADT Display
`type_modules` map populated by `sync_type_defs()` scanning TC module symbol tables. This is a temporary workaround — the real fix is `FQTypeName` (see below).

## Test File Status

**Total validated: ~853 pass / ~922 run = 93% pass rate**

| File | Tests | Status | Notes |
|------|-------|--------|-------|
| ring0.rs | 108 | **106/108 pass** | 2 checked_div pre-existing |
| repl_experience.rs | 181 | **179/181 pass** | 2 fixture prelude gaps (Functor) |
| ring1.rs | 166 | **165/166 pass** | 1 hang: `closure_and_tco` (TCO bug in v4 pipeline) |
| ring2.rs | 197 | **189/197 pass** | 8 fail: module resolution + multi-sig/trait gaps |
| ring3_repl.rs | 50 | **39/41 pass** | 2 fail: macro body type validation missing in v4 |
| repl_negative.rs | 31 | **29/31 pass** | 2 fail: bare primitives accessible without import (module scoping gap) |
| macros.rs | 28 | **22/27 pass** | 5 fail: macro-calls-macro, depth limit, defmacro-in-results, body validation |
| rc.rs | 81 | **81/81 pass** | Full pass |
| scheduler.rs | 18 | **18/18 pass** | Full pass |
| modules.rs | 22 | **18/22 pass** | 4 fail: multi-module compilation gaps |
| ring4_trace.rs | 29 | **7/29 pass** | 22 fail: trace depends on prelude/stdlib features |
| sketch_port.rs | 141 | **102/141 pass** | 39 fail: ADT display, constrained poly, platform (up from 11 pre-existing) |
| io.rs | 3 | **3/3 pass** | No longer hangs (persistent workers) |
| cache.rs | 51 | **27/51 pass** | No longer hangs; 24 fail: cache invalidation gaps |
| stdlib.rs | 54 | **38/54 pass** | No longer hangs; 16 fail: macro pipeline gaps |
| e2e.rs | 6 | **Not validated** | Subprocess tests; needs porting |
| exemplar.rs | ~5 | **Not validated** | Uses compile_module_graph |
| examples.rs | ~5 | **Not validated** | Likely needs prelude |
| lenient.rs | 16 | **4/16 fail** | Subprocess tests; binary needs `--v4` flag removed |
| sprint23.rs | 0 | **Empty** | FileWatcher tests deleted (v3 only) |
| pipeline_v2.rs | — | **Deleted** | Convergence scaffolding |
| v4_pipeline.rs | ~40 | **Not validated** | Subprocess tests; uses `--v4` flag (deleted); needs porting |
| v4_repl_eval.rs | ~10 | **Not validated** | Subprocess tests; binary needs rebuild |

## Blocking Issue: Prelude Loading Deadlock — RESOLVED

The v4 pipeline had no persistent worker threads (Phase 1 steps 1.1–1.2). `register_module` ran the worker loop inline in a single thread, deadlocking on multi-module dependency chains.

**Resolution** (Sprint 49): Three changes landed together:

1. **Scoped worker threads**: `register_module_with_source` spawns scoped priority worker threads via `std::thread::scope`. Workers park blocked modules and pick up ready ones from the scheduler, preventing deadlocks even with a single worker (`priority_workers: 1`).

2. **Export dependency loading**: `handle_export` now loads source modules on demand (same path as `handle_import`). Previously exports assumed source modules were pre-loaded.

3. **Null import / prelude suppression** (spec §8.3.6, §8.8.1): `(import [module []])` is a null import — imports nothing and skips module loading. An explicit prelude reference in any import or export form suppresses the implicit `(import [prelude [*]])`. All stdlib modules include `(import [prelude []])` to avoid circular dependencies when a project prelude re-exports from them.

4. **Pass 1 resume guard**: `pass1_done` flag on `ModuleSuspendState` prevents re-running Pass 1 when a module resumes after blocking at form index 0.

## Remaining Work

### 1. Macro pipeline gaps (16 stdlib test failures)

Three categories of failure in stdlib macro tests:

- **Macros module symbols unavailable in expansion** (str, threading macros — 10 failures): Macro bodies reference `SexpStr`, `SexpList` etc. from the `macros` synthetic module. When prelude macros expand in user context, the `macros` module symbols are not available for the expanded code. Error: `"undefined variable: SexpStr"` or `"constructor SexpList has no type scheme"`.
- **Defmacro-in-expansion-results** (const, def macros — 4 failures): The `const`/`def` prelude macros expand to `defmacro` forms. The v4 pipeline's `process_regular_form` doesn't handle defmacro produced by macro expansion. Error: `"defmacro should be handled before AST building"`.
- **Vec literal parse intercept** (vec macro — 2 failures): `(vec)` is intercepted by the parser as a vec literal before macro expansion can run. Error: `"vec literals not yet supported (Ring 1)"`.

### 2. Macro pipeline gaps (non-stdlib, from macros.rs — 5 failures)

- **Macro-calls-macro**: m2 expanding to call m1 fails with "undefined variable: m1". Macro environment not shared between sequential defmacro definitions.
- **Body type validation**: Macro body returning non-Sexp type not caught as error.
- **Expansion depth limit**: Mutual recursion between macros not detected; no depth limit enforcement.
- **Error recovery**: Bad macro body silently succeeds instead of producing a type error.

### 3. Module scoping gap (2 failures)

Bare `ReplSession::new()` sessions can still resolve bare primitive names (e.g., `add-i64`) without import. The v4 pipeline's primitives module registration or lookup fallback is too permissive. Spec §8.9.1 requires qualified-only access unless imported.

### 4. TCO hang (1 failure)

`closure_and_tco` in ring1 enters an infinite loop. The v4 pipeline's tail-call optimization has a bug when closures interact with self-recursive TCO.

### 5. Subprocess test porting

`v4_pipeline.rs`, `v4_repl_eval.rs`, and `lenient.rs` invoke the binary as subprocess with `--v4` flag which was deleted. Need to remove `--v4` from `run_v4()` and merge it with `run_old()`.

### 6. FQTypeName migration (separate task)
FIXME on `Type::ADT` in `crates/cranelisp-types/src/types.rs`.

Create `FQTypeName { module: ModuleFullPath, name: TypeName }` paralleling `FQSymbol { module, symbol }`. Change `Type::ADT(TypeName, Vec<Type>)` → `Type::ADT(FQTypeName, Vec<Type>)`. The typechecker stamps the module at type resolution time. ~182 sites across crates.

This eliminates:
- `type_modules: HashMap<TypeName, ModuleFullPath>` on CompilerSession
- `sync_type_defs` module scanning
- `TC.modules()` accessor added as workaround
- The `type_modules` parameter on `format_result_value`, `format_type_qualified`, etc.

Do interactively, not via subagent — construction sites in the typechecker need judgment about which module path to use.

## Deletions (step 1.7, completed)

- `src/main_new.rs` — deleted (168 lines, orphan pseudocode)
- `tests/pipeline_v2.rs` — deleted (656 lines, convergence scaffolding)
- `src/session.rs` — 1669→641 lines: deleted `CompilationSession`, `CacheConfig`, `CodegenWorkerMsg`, `CodegenMode`, `ModuleDependencyGraph`, `FormResult`, async codegen worker. Kept: `CacheState`, `InMemWorkerState`, `SharedCodegenState`, `WorkerJitState`, `ObjectWorkerState`, utility functions.
- `src/pipeline.rs` — 2829→853 lines: deleted `compile_unit`, `codegen_and_execute*`, `compile_and_run`, `compile_module_graph*`, `PipelineResult`, `CompiledModuleGraph`, `CompileUnitResult`, `CodegenResult`, `CodegenPacket`, old cache-hit loading, `#[cfg(test)]` module. Kept: `resolve_module_file`, `compile_and_execute_expr`, `compile_and_register_defn_shared`, `build_codegen_state_for_cache`, `discover_module_graph`, `toposort`, object compilation helpers.
- `src/repl/` — disconnected via `lib.rs` (`pub mod repl` removed). Files kept on disk as reference. ~3201 lines unreachable.
- `tests/stdlib.rs` — ported from `cranelisp::repl::ReplSession` to `helpers::ReplSession`
- `tests/cache.rs` — ported from `compile_module_graph_cached` to `helpers::batch_run_file`
- `tests/sprint23.rs` — 2 FileWatcher tests deleted (v3 only)

Total: ~3828 lines deleted + ~3201 lines disconnected = ~7029 lines removed.

## Key Decisions Made
- **IO trampoline**: `batch_run` / `batch_run_file` auto-trampoline IO via `CompilerSession::trampoline()`. Tests check post-trampoline values, not raw IO heap pointers. IO internals testing belongs in unit tests.
- **EvalResult design**: `Def | Val` enum with `ty` on both variants. `.value()` returns 0 for Def. Display formatting via `session.format_eval_result()`.
- **Bare sessions**: Use `tests/fixtures` as project_root with empty lib_dirs to prevent accidental stdlib discovery. Old code used cwd which picked up `stdlib/` from repo root.
- **ADT display**: Spec requires fully-qualified type names (`:user/Point`). Old unqualified display was a bug. Workaround via `type_modules` map until FQTypeName migration.
