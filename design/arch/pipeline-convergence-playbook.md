# Pipeline Convergence Playbook

Status as of Sprint 49, 2026-04-06.

Commits landed:
- `a642185` — phase 1 structural detach (inner removed, EvalResult redesigned, test adapter built)
- `9c6a475` — ADT display qualification fix + FQTypeName FIXME
- `5c09343` — step 1.7 old pipeline deletion (~7k lines removed)
- `43eab15` — mark Phase 1 complete in convergence playbook
- `17a9906` — macro pipeline gaps, spawn nice workers, implement link mode
- `ea5ce35` — submodule loading, no_cache flag, test isolation
- `a8e4bb7` — keep project_root for DLL resolution
- `e33aaf3` — spec + implement 3-tier search paths (§8.11) for modules and platforms
- (pending) — Pass 0 import/export resolution, handle_export registration, macro qualification, stdlib primitives imports

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
- [x] 2.3 Prelude loading — stdlib 54/54 pass
- [x] 2.4 Import chains — modules 22/22, ring2 194/197
- [x] 2.5 REPL eval with prelude — io 72/74, lenient 16/16
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
- `new()` — bare, no prelude. Uses `tests/fixtures` as project_root + empty lib_dirs.
- `new_with_prelude(project_root, &[lib_dirs])` — loads prelude from lib_dirs via `register_module("user")`. project_root and lib_dirs are separate per spec §8.11.2 (3-tier search).
- `new_for_file(entry_path, &[lib_dirs])` — project_root from entry file's parent. For multi-file batch.

**Search path model (spec §8.11):**
- `project_root` = directory of entry file (tier 2 for modules, tier 1 for platforms)
- `lib_dirs` = library search locations (tier 3 for modules, tier 2 for platforms via `/platforms/`)
- `platform_dirs` = extra DLL search dirs (tier 3 for platforms, from `CRANELISP_PLATFORM_PATH` or code)
- Tests use clean project roots (e.g., `tests/fixtures/stdlib_project/`) to avoid repo-root contamination from `user.cl`. Platform DLLs found via explicit `platform_dirs.push(target/debug)`.

**ReplSession methods (delegating to CompilerSession):**
- `eval(src)` — returns `Result<EvalResult, CranelispError>` (None→synthetic Val)
- `register_module(name)` — resolves file from lib_dirs
- `register_module_with_source(name, source)` — explicit source
- `trampoline(module_name)` — execute main, returns `(i64, Type)`. Auto-unwraps IO.

### ADT Display
`type_modules` map populated by `sync_type_defs()` scanning TC module symbol tables. This is a temporary workaround — the real fix is `FQTypeName` (see below).

## Test File Status

**Total validated: ~1,405 pass / ~1,538 run = 91% pass rate** (full --no-fail-fast 2026-04-06, post macro qualification fix)

| File | Tests | Status | Notes |
|------|-------|--------|-------|
| Unit tests (6 crates) | 915 | **915/915 pass** | All crate unit tests clean |
| ring0.rs | 108 | **106/108 pass** | 2 checked_div pre-existing |
| ring1.rs | 166 | **166/166 pass** | Full pass |
| rc.rs | 81 | **81/81 pass** | Full pass |
| ring2.rs | 197 | **194/197 pass** | 3 fail: multi-sig panic, trait-as-value (2) |
| modules.rs | 22 | **22/22 pass** | Full pass (fixed: submodule loading) |
| macros.rs | 28 | **23/28 pass** | 4 fail + 1 ignored: error recovery, depth limit |
| ring3_repl.rs | 50 | **39/50 pass** | 2 fail + 9 ignored: macro error recovery |
| stdlib.rs | 54 | **54/54 pass** | Full pass |
| lenient.rs | 16 | **16/16 pass** | Full pass (fixed: test isolation) |
| scheduler.rs | 18 | **18/18 pass** | Full pass |
| io.rs | 74 | **72/74 pass** | 2 fail: inline mod side-effect, REPL IO display |
| ring4_trace.rs | 29 | **23/29 pass** | 6 fail: run-tests + trace features |
| cache.rs | 51 | **38/51 pass** | 13 fail: multi-module/prelude caching |
| repl_experience.rs | 181 | **179/181 pass** | 2 fail: imported Option display |
| repl_negative.rs | 31 | **29/31 pass** | 2 fail: bare primitives scoping |
| e2e.rs | 133 | **87/133 pass** | 46 fail: subprocess tests, various v4 gaps |
| examples.rs | 15 | **15/15 pass** | Full pass |
| v4_repl_eval.rs | 13 | **11/13 pass** | 2 fail |
| v4_pipeline.rs | 47 | **26/47 pass** | 20 fail + 1 ignored |
| sketch_port.rs | 141 | **129/141 pass** | 12 fail (down from 39; 11 pre-existing) |
| exemplar.rs | 3 | **3/3 pass** | Full pass |
| sprint23.rs | 70 | **0/0 run** | cfg-disabled (`__sprint47_reenable` feature gate) |

## Blocking Issue: Prelude Loading Deadlock — RESOLVED

The v4 pipeline had no persistent worker threads (Phase 1 steps 1.1–1.2). `register_module` ran the worker loop inline in a single thread, deadlocking on multi-module dependency chains.

**Resolution** (Sprint 49): Three changes landed together:

1. **Scoped worker threads**: `register_module_with_source` spawns scoped priority worker threads via `std::thread::scope`. Workers park blocked modules and pick up ready ones from the scheduler, preventing deadlocks even with a single worker (`priority_workers: 1`).

2. **Export dependency loading**: `handle_export` now loads source modules on demand (same path as `handle_import`). Previously exports assumed source modules were pre-loaded.

3. **Null import / prelude suppression** (spec §8.3.6, §8.8.1): `(import [module []])` is a null import — imports nothing and skips module loading. An explicit prelude reference in any import or export form suppresses the implicit `(import [prelude [*]])`. All stdlib modules include `(import [prelude []])` to avoid circular dependencies when a project prelude re-exports from them.

4. **Pass 1 resume guard**: `pass1_done` flag on `ModuleSuspendState` prevents re-running Pass 1 when a module resumes after blocking at form index 0.

### Pass 0 Import Resolution + Export Registration Fix (Phase 2, 2026-04-06)

Two bugs prevented modules with imports from compiling correctly:

1. **Import/export forms processed too late**: `register_trait_impl` checks impl method bodies during Pass 1, but import/export forms were only processed in Pass 2. Any module that imported symbols and used them in trait impl bodies would fail with "undefined variable". Fix: added Pass 0 in `process_module_forms` that processes all import/export/mod/platform forms before Pass 1, so imported symbols are in scope when impl bodies are checked. Pass 2 retains its import/export handling (idempotent) with a FIXME to remove once Pass 0 is verified stable.

2. **`handle_export` never registered symbols**: When a dependency was already loaded, `handle_export` skipped it without calling `register_exports`. Fix: call `ctx.tc.register_exports()` for already-loaded deps, mirroring how `handle_import` calls `register_imports`.

**Impact**: 73 tests recovered (1272→1345 passing, 266→193 failing). The test fixture prelude (`tests/fixtures/prelude.cl`) now loads correctly with `(import [primitives [*]])`.

### Macro Qualification + Stdlib Primitives Import (Phase 2, 2026-04-06)

Two classes of issue prevented stdlib macros and modules from working:

1. **Stdlib modules missing `(import [primitives [*]])`**: 13 stdlib domain modules (eq, ord, num, int, float, display, string, vec, list, derive, trace, runner, lazy) used bare primitive names without importing the `primitives` module. Spec §8.9.1 requires explicit import — primitives are not auto-seeded into modules. Fix: added `(import [primitives [*]])` to all 13 files. Also added to `defs.cl` for macro body compilation.

2. **Macro expansion templates with unqualified symbols**: Macro bodies are compiled inline in the *calling* module's context (not the defining module's), so any non-prelude symbols in macro bodies must be fully qualified. Fixes:
   - `stdlib/defs.cl`: `quote-sexp` → `primitives/quote-sexp`, `str-concat` → `primitives/str-concat`
   - `stdlib/text/string.cl`: `str-concat` → `primitives/str-concat` in `str` macro expansion
   - `stdlib/io/monad.cl`: `bind` → `primitives/bind` in `do`/`bind!` macro expansions
   - `stdlib/core/syntax.cl`: `SNil` → `macros/SNil`, `SCons` → `macros/SCons` in `slist` macro

**Impact**: 60 additional tests recovered (1345→1405 passing, 193→133 failing). The real stdlib prelude now loads and all trait/type/operator tests pass. 49/57 stdlib+exemplar tests pass (was 0/57).

### Search Path Model Fix (Phase 2, 2026-04-06)

Full verification (tests/VERIFICATION.md) revealed ~215 new regressions, most caused by a single root issue: `user.cl` at the repo root (a development scratch file) was loaded as the "user" module by tests, because project_root was conflated with lib_dirs.

**Fixes (3 commits, ~140 tests recovered):**

1. **Submodule loading** (`handle_mod` in worker.rs): `(mod util)` now loads the submodule (resolve file, schedule, block for typecheck) and registers GOT aliases (`util/helper` → `helper`). Previously it did nothing.

2. **Spec §8.11 — 3-tier search paths**: Module resolution is now (submodule → project_root → lib_dirs) with project_root as a separate tier. Platform DLL resolution mirrors this with `/platforms/` subdirs. `CompilerSession` no longer adds project_root to lib_dirs.

3. **Test isolation**: Tests use clean project roots (`tests/fixtures/`, `tests/fixtures/stdlib_project/`) and explicit `platform_dirs` for `target/debug/`. The `no_cache` flag on `SessionSettings` is now respected.

## Remaining Work

### 1. Macro pipeline gaps (stdlib) — RESOLVED

Pass 0 import resolution, stdlib `(import [primitives [*]])`, and macro body qualification fixed all stdlib macro failures. 49/57 stdlib+exemplar tests pass.

Remaining 8 stdlib/exemplar failures are **test-side issues** (test code uses unqualified primitives like `vec-len`, `Pure`, `str-eq`, `add-i64` that aren't in the prelude):
- `macro_vec_empty`, `macro_vec_access`, `macro_vec_elements` — test uses bare `vec-len`/`vec-get`
- `macro_do_multi`, `macro_do_returns_last` — test uses bare `Pure`
- `macro_const_string_batch` — test source uses bare `str-eq`
- `macro_def_expression_batch` — test source uses bare `add-i64`
- `exemplar_batch_cross_module_adt` — separate exemplar issue

### 2. Macro pipeline gaps (non-stdlib, from macros.rs)

- **Body type validation**: Macro body returning non-Sexp type not caught as error.
- **Expansion depth limit**: Mutual recursion between macros not detected; no depth limit enforcement.

### 2a. Macro compilation context

Macro clause bodies are compiled inline in the *calling* module's context (`compile_macro_clause_inline` uses `ctx.tc.current_module_path()`). This means macro bodies can only reference symbols available in the caller's scope, forcing macro authors to fully qualify non-prelude symbols. The proper fix is to compile macros in the defining module's context, but the current workaround (qualification) is sufficient.

### 3. Module scoping gap (4 failures: ring2 2, repl_negative 2)

Bare `ReplSession::new()` sessions can still resolve bare primitive names (e.g., `add-i64`) without import. The v4 pipeline's primitives module registration or lookup fallback is too permissive. Spec §8.9.1 requires qualified-only access unless imported.

### 4. Multi-sig panic + trait-as-value (3 failures: ring2)

- `neg_multi_sig_bare_value_errors`: `Defn::params()` panics on `DefnMulti` — missing guard.
- `trait_method_as_value_operator`, `trait_method_as_value_comparison`: using trait method as bare value fails.

### 5. Subprocess test porting (~66 failures: e2e 46, v4_pipeline 20)

E2E and v4_pipeline tests invoke the binary as subprocess. Various issues: `--v4` flag deleted, prompt format changes, `/expand` not available in v4, `run-tests` not ported.

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
- **Search paths**: project_root and lib_dirs are separate concepts per spec §8.11.2. project_root is NOT in lib_dirs. Platform DLLs found via `{root}/platforms/` and `{lib}/platforms/` per §8.11.3, plus explicit `platform_dirs` for dev convenience (`target/debug`).
- **ADT display**: Spec requires fully-qualified type names (`:user/Point`). Old unqualified display was a bug. Workaround via `type_modules` map until FQTypeName migration.
