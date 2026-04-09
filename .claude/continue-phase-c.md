# Continue: Session Restructure Phase C

## Context

Read `design/arch/session-restructure.md` for the full target data model.

Commits landed:
1. `0bc433f` — Phase A (target types, defn on ModuleEntry::Def) + Phase B foundations (unified GOT via global_value, object codegen GOT-indirect)
2. `f4abe11` — DashMaps correctly on CompilerSession (not SharedState)
3. `c8e3008` — annotate TARGET STATE and LEGACY structures
4. `fbc791a` — Phase C: activate unified GOT codegen path (Steps 1-5 + partial 6)
5. Uncommitted — migrate blocking functions + direct-write to codegen_products

## What's done

### Phase B (foundations)

- `got_data_symbol_name()` in `compiler/mod.rs` (single source of truth)
- `CompilationEnv::resolve_got_module()` returns `(ModuleFullPath, slot)` — default returns None
- `compile_direct_call` has unified GOT path using `global_value(DataId)` (checked before legacy paths)
- `emit_got_indirect_call_via_data_id()` on FnCompiler
- `ObjectCompileInput` implements `CompilationEnv` (no separate env struct)
- Object codegen uses GOT-indirect calls via env (not direct calls)
- `SessionCompilationEnv` has `resolve_module_slot` helper
- `ModuleGotRegistry::jit_got_symbols()` ready for JIT symbol registration
- `resolve_got_module` activated on `SessionCompilationEnv` — full resolution chain (current → qualified → global fallback)

### Phase C (wire codegen through new DashMaps)

**Target DashMaps on CompilerSession** — `codegen_products`, `introspection`, `typecheck_products`, `codegen_inputs`.

**compile_and_register_defn_shared rewritten:**
- No longer takes `SharedCodegenState` or `WorkerJitState`
- Signature: `(jit_symbols, defn, check, env, module_got, codegen_products, module, disable_dealloc)`
- GOT slot from `env.resolve_got()` (no legacy fallback)
- Code pointer stored in module GOT via `module_got.store_slot()`
- `Code { jit, ptr }` written directly to `codegen_products` DashMap
- `disable_dealloc` flag for macro clause compilation

**codegen_module_symbols rewritten:**
- Signature: `(platform_registry, scheduler, module, program, check, tc_modules, shared_state, codegen_products)`
- No `SharedCodegenState` or `WorkerJitState` parameters
- Builds `SessionCompilationEnv` internally
- Calls `collect_jit_symbols_for_module` for merged platform + GOT data symbols

**Macro + dep compilation migrated to env path:**
- `compile_macro_clause_inline` builds `SessionCompilationEnv`, calls `compile_and_register_defn_shared` with `disable_dealloc: true`
- `compile_dep_symbol_inline` takes `env` + `module_got` + `codegen_products`, reads defn from TC symbol table (`ModuleEntry::Def.defn`)
- `compile_macro_defn_no_dealloc` is now dead code (superseded by `compile_and_register_defn_shared` with `disable_dealloc: true`)

**Helper functions migrated:**
- `has_code_ptr(codegen_products, module, name)` — reads from `codegen_products`
- `get_code_ptr(codegen_products, module, name)` — reads from `codegen_products`
- `build_macro_entry_from_got(codegen_products, module, info)` — reads code_ptr from `codegen_products`
- `build_all_macro_entries(codegen_products, module, macro_infos)` — uses above
- `build_persistent_macro_entries(tc, codegen_products, map)` — follows import chains, reads from defining module's `codegen_products`
- `resolve_macro_entry` returns `(clauses, docstring, defining_module)` — provides module for cross-module macro lookup
- `collect_transitive_uncompiled_deps(tc, codegen_products, module, start_symbol)` — checks `codegen_products`

**WorkerContext updated:**
- Has `codegen_products: &'a DashMap<ModuleFullPath, CodegenProduct>` field
- All construction sites (3 in session_v4.rs, 1 in worker.rs, 3 in repl/mod.rs) pass `codegen_products`

**PriorityWorkerShared updated:**
- Has `codegen_products` field, borrowed from `CompilerSession` in `register_module_with_source`

**Other infrastructure:**
- `collect_jit_symbols_for_module()` on `SessionCompilationEnv` — derives platform fn ptrs + GOT data symbols from session state
- `PlatformRegistry::fn_ptr_by_jit_name()` — resolves platform fn ptrs by JIT symbol name
- `ModuleGotRegistry::all_modules()` — iterates all registered GOT tables
- `SharedCodegenState::scratch()` — lightweight scratch state for env-path compilation
- `lookup_main_code_ptr` reads from `codegen_products` (not `inmem_worker.got_state`)
- `platform_symbols` renamed to `jit_symbols` throughout
- All `shared_state: None` sites changed to `Some(&self.shared)` — workers always have GOT registry access

## What's NOT done

### Phase B remainders

1. **Linker: resolve against `__cranelisp_got` data section** — remove internal `got_mmap` from Linker. Currently Linker allocates its own GOT mmap; should resolve `__cranelisp_got_*` symbols against the session's per-module GOT tables.

2. **Remove legacy `CompileContext` fields** — `got_slots: Option<&HashMap>`, `got_base: Option<i64>`, `cross_module_got` on the backend's `CompileContext`. Dead when `env` is always `Some`.

### Phase C remainders

3. **Remove `extract_from`/`sync_back_to` from 4 session_v4.rs sites** — `register_module_with_source` (line 755), REPL eval form (line 1051), `compile_dep_inline` (line 1218), macro compilation (line 1841). These still extract SharedCodegenState from InMemWorkerState. The main codegen path (`codegen_module_symbols`) no longer uses it, but these sites pass `shared_codegen` to `WorkerContext` for functions that still reference it (e.g., `load_cached_module_via_linker`, `register_submodule_got_aliases`).

4. **Remove `extract_from`/`sync_back_to` from 4 repl/mod.rs sites** — same pattern as session_v4.rs, using `self.core.inmem_worker`.

5. **Remove `WorkerJitState`** — `WorkerContext` still has the field. `priority_worker_thread` still creates and drains one. No codegen path writes to it anymore, but `drain_to_shared` is still called. Delete the struct, remove the field, remove drain calls.

6. **Remove `SharedCodegenState`** — still exists as a struct. `extract_from`/`sync_back_to`/`scratch` methods exist. Used by the remaining extract sites and `load_cached_module_via_linker`. Once extract sites are eliminated, delete the struct.

7. **Remove `InMemWorkerState`** — fields: `got_state` (ModuleCodegenState), `jit_modules`, `traced_fns`, `trace_extra_symbols`, `cache_linkers`. `got_state` is superseded by per-module GOTs + codegen_products. `jit_modules` is superseded by codegen_products (Code owns JIT). `traced_fns` and `trace_extra_symbols` are REPL trace-specific — need a new home (on CompilerSession or ReplSession). `cache_linkers` are superseded by CodegenProduct.linker.

8. **Delete dead code:**
   - `compile_macro_defn_no_dealloc` (worker.rs) — superseded by `compile_and_register_defn_shared` with `disable_dealloc`
   - `pre_register_got_slots` (worker.rs) — legacy slot allocation, replaced by `pre_register_got_slots_in_tc`
   - `SharedCodegenState::scratch()` and `scratch_from()` — no longer needed once extract sites gone
   - `def_codegen: HashMap<Symbol, DefCodegen>` on CompilerSession — replaced by codegen_products + introspection
   - `register_module_aliases_filtered` (session.rs) — used after sync_back_to, goes away with it
   - `get_code_ptr` old signature (if any remain)

9. **`compile_and_execute_expr` still uses `InMemWorkerState`** — for the trace path (`traced_fns`, `trace_extra_symbols`). The non-trace path could take `codegen_products` directly. The trace path needs `traced_fns`/`trace_extra_symbols` relocated.

10. **`load_cached_module_via_linker`** — still takes `SharedCodegenState` + `WorkerJitState`. Needs migration to write Linker to codegen_products, read/write GOT from per-module tables.

### Approach for remaining items

Items 3-6 are coupled: once all functions that read from `shared_codegen` are migrated to read from `codegen_products` (or TC symbol tables), the extract/sync pattern and the structs can be deleted together.

The remaining readers of `shared_codegen` (beyond the extract sites themselves):
- `load_cached_module_via_linker` — writes def_codegen entries, keeps linker/JIT alive
- `register_submodule_got_aliases` — registers GOT aliases for unqualified lookups
- `handle_cached_codegen` — calls load_cached_module_via_linker

Migrate these to use `codegen_products`, then all extract sites become no-ops and can be deleted.

## Key design decisions

- Platform functions are called directly (not through GOT) — `declare_function(name, Import)` + `call`, resolved via JITBuilder::symbol()
- GOT-indirect calls use `global_value(DataId)` — same codegen for JIT and object
- JIT symbols collected per-module from symbol table scan (not global cache)
- No `platform_symbols` parameter — derived from primary sources at JIT creation
- DashMaps on CompilerSession, accessed by workers via scoped-thread field borrows
- Macro clause functions are normal functions on per-module GOTs — no "global GOT"
- Workers write directly to destination DashMaps — no intermediate state, no shuffle
- `shared_state` is always `Some` — workers always have GOT registry access

## Verification

```bash
cargo nextest run -E "binary(ring0)" --max-fail 3
cargo nextest run -E "binary(macros)" --max-fail 5
cargo nextest run -E "binary(ring0) | binary(ring1) | binary(ring2) | binary(ring3_repl) | binary(macros) | binary(modules) | binary(v4_pipeline) | binary(v4_repl_eval) | binary(rc)" --no-fail-fast
```

Pre-existing failures: 2 ring0 (checked_div), 4 macros (REPL error recovery), ~18 modules/ring2/v4_pipeline (platform/export/multi-module issues).
