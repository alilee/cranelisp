# Per-Module GOT Cleanup Plan

**Status:** Sprint 49, 2026-04-07. Per-module GOTs activated; legacy path still present.

## What's Done

Per-module GOTs are active. `SessionCompilationEnv` resolves GOT entries live from TC symbol tables + `ModuleGotRegistry`. `v4_cross_module_macro_qualified_ref` passes. `def_codegen` introspection reads moved from `InMemWorkerState.got_state.def_codegen` to `CompilerSession.def_codegen`.

## What Remains

Three redundant layers still exist:

1. **`InMemWorkerState`** on `CompilerSession` — bundles GOT state, JIT lifetimes, trace state, cache linkers
2. **`SharedCodegenState`** — the `extract_from`/`sync_back_to` bridge that converts `HashMap ↔ DashMap` for worker access
3. **Legacy GOT fields** on `CompileContext` — `got_slots`, `got_base_ptr`, `cross_module_got`, `func_arities` (unused when `env` is set)

## Target State

```
CompilerSession
├── tc: TypeChecker                          # GOT slots on ModuleEntry::Def
├── shared: Arc<SharedState>
│   ├── got_registry: ModuleGotRegistry      # per-module Arc<GotTable>
│   ├── module_outputs: DashMap<...>         # typecheck results
│   ├── kept_code: Mutex<KeptCode>           # JIT + Linker lifetime
│   └── scheduler, cache_state, ...
├── def_codegen: HashMap<Symbol, DefCodegen> # introspection (/source, /clif, etc.)
├── traced_fns: Vec<TracedFnInfo>            # REPL trace state
├── trace_extra_symbols: Vec<(String, *const u8)>
└── macro_env, platform_registry, ...
```

No `InMemWorkerState`. No `SharedCodegenState`. No extract/sync dance.

## Cleanup Steps

### Phase 1: Move JIT/Linker lifetime to SharedState

`InMemWorkerState` holds `jit_modules: Vec<Jit>` and `cache_linkers: Vec<Linker>` to keep executable memory alive. `SharedCodegenState` has `kept_jits: Mutex<Vec<Jit>>` and `kept_linkers: Mutex<Vec<Linker>>` for the same purpose during the worker scope.

**Change:** Add `kept_code: Mutex<KeptCode>` to `SharedState`:
```rust
pub struct KeptCode {
    pub jits: Vec<cranelisp_backend::jit::Jit>,
    pub linkers: Vec<cranelisp_backend::cache::Linker>,
}
```

Workers drain their per-worker `WorkerJitState` directly to `shared.kept_code` instead of to `SharedCodegenState.kept_jits/kept_linkers`. The REPL expr path pushes JITs there too.

**Sites to change:**
- `WorkerJitState::drain_to_shared()` (session.rs:387) — drain to `SharedState.kept_code`
- `compile_and_execute_expr_with_trace` (pipeline.rs:170) — push JIT to `SharedState.kept_code`
- `compile_and_execute_expr` (pipeline.rs) — compiled expr JIT goes to `SharedState.kept_code`
- `compile_and_register_defn_shared` (pipeline.rs:278) — push JIT to `SharedState.kept_code` or per-worker state
- All `sync_back_to` sites — stop moving JIT/linker vecs; they're already in `SharedState`

**Verify:** Run `cargo nextest run -E "binary(ring0)" --max-fail 3` then expand.

### Phase 2: Move trace state to CompilerSession

`InMemWorkerState` holds `traced_fns` and `trace_extra_symbols` for the `(trace ...)` special form.

**Change:** Move both fields directly onto `CompilerSession`:
```rust
pub struct CompilerSession {
    pub traced_fns: Vec<TracedFnInfo>,
    pub trace_extra_symbols: Vec<(String, *const u8)>,
    ...
}
```

**Sites to change:**
- `compile_and_execute_expr` (pipeline.rs:84) — reads `inmem_worker.traced_fns`
- `compile_and_execute_expr_with_trace` (pipeline.rs:118) — reads `inmem_worker.trace_extra_symbols`
- `session_v4.rs` trace setup code — writes to `inmem_worker.traced_fns`
- All trace-related code in `session_v4.rs` that accesses `self.inmem_worker.traced_fns`

These are REPL-only and single-threaded — no concurrency concerns.

**Verify:** Run trace tests: `cargo nextest run -E "test(trace)"`.

### Phase 3: Eliminate SharedCodegenState from worker path

The worker path (`codegen_module_symbols` and helpers) still receives `&SharedCodegenState` for:

1. **`ensure_slot_for`** (worker.rs:947, 1667) — legacy slot allocation. When env is active, TC assigns slots. The remaining callers are in macro compilation and submodule GOT alias registration. These need to use TC slot assignment instead.

2. **`def_codegen` reads** for macro compilation — `has_code_ptr` (worker.rs:1696), `get_code_ptr` (worker.rs:1705), defn lookup for macro deps (worker.rs:1510). These check whether a function has been compiled. Replace with: check if the function's code pointer is in the per-module GotTable (non-null at the assigned slot).

3. **`def_codegen` writes** — storing code_ptr, param_count, defn after compilation (pipeline.rs:267-272, worker.rs:753, 1670). Route to `CompilerSession.def_codegen` (already done for reads; needs write path).

4. **`update_slot`** — writing code pointers to the flat GOT (pipeline.rs:264, worker.rs:1668). When module_got is available, this is redundant (already writes to per-module GOT). Remove the shared_codegen fallback.

5. **`register_submodule_got_aliases`** (worker.rs:1072, 1139-1162) — copies GOT entries for submodule qualified names. With `SessionCompilationEnv`, these are resolved live from the TC. Remove the alias copying.

6. **`build_all_macro_entries` / `build_persistent_macro_entries`** (worker.rs:1294-1298) — reads def_codegen for macro clause code pointers. Replace with per-module GotTable lookups.

**Per-function changes:**

| Function | File:Line | What it uses SharedCodegenState for | Replacement |
|----------|-----------|-------------------------------------|-------------|
| `process_module_forms` | worker.rs:753 | Write sexp to def_codegen | Write to session.def_codegen |
| `handle_import` | worker.rs:947 | `ensure_slot_for` for cached symbols | TC assigns slots during cache restore |
| `handle_mod` | worker.rs:1072 | `register_submodule_got_aliases` | Remove — env resolves qualified names |
| `register_submodule_got_aliases` | worker.rs:1139 | Copy GOT entries for aliases | Remove entirely |
| `build_all_macro_entries` | worker.rs:1294 | Read code_ptr from def_codegen | Read from per-module GotTable |
| `build_persistent_macro_entries` | worker.rs:1298 | Read code_ptr from def_codegen | Read from per-module GotTable |
| `expand_macros_if_needed` | worker.rs:1381,1407 | `has_code_ptr` | Check per-module GotTable slot non-null |
| `compile_macro_deps` | worker.rs:1429-1520 | Read defn, compile, `ensure_slot_for` | Use TC slots, write to per-module GOT |
| `compile_macro_defn_no_dealloc` | worker.rs:1638 | `ensure_slot_for`, `update_slot`, write def_codegen | Use TC slot, write to per-module GOT, write to session.def_codegen |
| `has_code_ptr` | worker.rs:1696 | Read def_codegen.code_ptr | Check per-module GotTable slot non-null |
| `get_code_ptr` | worker.rs:1705 | Read def_codegen.code_ptr | Read from per-module GotTable |
| `codegen_module_symbols` | worker.rs:2226 | Passed to compile fns | Remove parameter |
| `pre_register_got_slots` | worker.rs:2296 | Legacy slot allocation | Remove — `pre_register_got_slots_in_tc` already used |
| `compile_and_register_defn_shared` | pipeline.rs:196 | ensure_slot_for, update_slot, def_codegen | TC slot, per-module GOT, session def_codegen |

**Key insight:** `has_code_ptr` and `get_code_ptr` check the `def_codegen` DashMap for code pointers. With per-module GOTs, the equivalent check is `got_registry.get_table(module)?.load_slot(slot) != null`. This requires knowing the module and slot, which `SessionCompilationEnv::resolve_got` provides. Add a helper:

```rust
fn is_compiled(env: &SessionCompilationEnv, name: &Symbol) -> bool {
    env.resolve_got(name)
        .map(|(base, slot)| {
            // Load the code pointer from the GOT slot and check non-null
            let ptr = unsafe { *((base as *const u8).add(slot * 8) as *const *const u8) };
            !ptr.is_null()
        })
        .unwrap_or(false)
}
```

**Verify:** Run macro tests: `cargo nextest run -E "binary(macros)" --max-fail 5`, then ring3, stdlib, full suite.

### Phase 4: Eliminate SharedCodegenState from REPL path

Five extract/sync sites in `session_v4.rs`:

1. **`register_module_with_source`** (line ~631) — spawns scoped workers. Workers need `&SharedCodegenState` on `WorkerContext`. After Phase 3, `WorkerContext.shared_codegen` is removed, so this extract is unnecessary.

2. **`process_single_form`** (line ~922) — REPL eval. Creates `WorkerContext` for single-form typecheck + codegen. After Phase 3, `WorkerContext` no longer needs `shared_codegen`.

3. **`codegen_and_execute`** (line ~1029) — REPL codegen. Calls `codegen_module_symbols`. After Phase 3, `codegen_module_symbols` no longer takes `shared_codegen`.

4. **`compile_dep_inline`** (line ~1108) — inline dependency compilation. Same as #2.

5. **Macro compilation** (line ~1731) — REPL macro clause compilation. Uses `shared_codegen` for the same pattern as Phase 3.

**Change:** Remove `shared_codegen` from `WorkerContext`. Remove all extract/sync sites. Workers access `SharedState.got_registry` and `SharedState.kept_code` directly.

**Verify:** Run REPL tests: `cargo nextest run -E "binary(repl_experience)" --max-fail 3`.

### Phase 5: Remove InMemWorkerState

After Phases 1-4, `InMemWorkerState` fields are:
- `got_state` → dead (GOT slots on TC, GotTables in registry, code pointers in per-module GOTs)
- `jit_modules` → moved to `SharedState.kept_code`
- `traced_fns` → moved to `CompilerSession`
- `trace_extra_symbols` → moved to `CompilerSession`
- `cache_linkers` → moved to `SharedState.kept_code`

**Change:** Delete `InMemWorkerState` struct, remove from `CompilerSession`, remove from `session.rs`.

**Verify:** Full suite.

### Phase 6: Remove legacy CompileContext fields

After Phases 1-5, the legacy snapshot fields on `CompileContext` are unused:
- `got_slots: Option<&HashMap<Symbol, usize>>` — replaced by `env`
- `got_base_ptr: Option<i64>` — replaced by `env`
- `cross_module_got: Option<&CrossModuleGot>` — replaced by `env`
- `func_arities: &HashMap<Symbol, usize>` — replaced by `env.func_arity()`

**Change:** Remove these fields. Remove `CrossModuleGot` type. `CompileContext` becomes:
```rust
pub struct CompileContext<'a> {
    pub check: &'a CheckResult,
    pub env: Option<&'a dyn CompilationEnv>,
    pub func_ids: &'a HashMap<Symbol, FuncId>,
    pub current_fn: Option<&'a Symbol>,
    pub in_tail_position: bool,
    pub traced_fns: Option<&'a [TracedFnInfo]>,
    // Ring 1 intrinsic FuncIds...
}
```

Update `build_compile_context` signature. Update all callers. Update `resolve_got_entry` to remove legacy fallback.

**Verify:** Full suite, then grep for `CrossModuleGot`, `got_slots`, `got_base_ptr` — zero hits in src/.

### Phase 7: Remove `SharedCodegenState` and `ModuleCodegenState`

After Phases 1-6:
- `SharedCodegenState` has no remaining callers
- `ModuleCodegenState` (in `cranelisp-backend/src/got.rs`) has no remaining callers outside tests
- `InMemWorkerState` is deleted

**Change:** Delete `SharedCodegenState` from `session.rs`. Delete or gut `ModuleCodegenState` in `got.rs` (keep `GotTable` which is still used by `ModuleGotRegistry`). Remove `extract_from`, `sync_back_to`, `ensure_slot_for`, `allocate_slot`, `update_def`, `update_slot` from `ModuleCodegenState`.

**Verify:** `cargo check`, full suite, grep `SharedCodegenState` — zero hits.

## Old REPL Path (`src/repl/mod.rs`)

The old REPL path has 4 extract/sync sites and its own `SharedCodegenState` usage. It uses the legacy GOT path (no env). Options:

1. **Port to env path** — add `SessionCompilationEnv` support to the old REPL path. Moderate effort.
2. **Delete** — if the v4 REPL (`session_v4.rs`) handles all REPL functionality. Check if any tests still route through the old REPL.
3. **Leave as-is** — the old path works; clean up when it's deleted.

Recommendation: option 3 for now. The old REPL is disconnected (`pub mod repl` removed from `lib.rs` per playbook). Tests route through v4 `CompilerSession`. The old code is dead but kept as reference.

## Risk Assessment

**Phase 3 is highest risk** — macro compilation relies heavily on `SharedCodegenState.def_codegen` for code_ptr checks. The replacement (per-module GotTable slot null-checks) requires knowing the module that defines each macro dependency, which `SessionCompilationEnv` provides. Test macro compilation thoroughly after each function migration.

**Phase 4 is moderate risk** — the REPL uses extract/sync in 5 places, each slightly different. Test each REPL interaction pattern (eval, import, macro define+use, trace).

**Phases 1, 2, 5, 6, 7 are low risk** — field moves and dead code removal.

## Execution Order

Phases 1 and 2 can be done in parallel (independent field moves). Phase 3 is the bulk of the work. Phase 4 depends on Phase 3. Phases 5-7 are mechanical cleanup after 3-4.

Estimated: 3-4 focused sessions.
