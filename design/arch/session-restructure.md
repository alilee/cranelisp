# Per-Module GOT Cleanup — End-State Data Model & Plan

## Data Structure (Target)

```
CompilerSession:
  typecheck:     DashMap<ModulePath, TypecheckProduct>
  codegen_input: DashMap<ModulePath, CodegenInput>
  codegen:       DashMap<ModulePath, CodegenProduct>
  platforms:     DashMap<ModulePath, Platform>
  scheduler:     Scheduler
  introspection: DashMap<FQSymbol, Introspection>     // REPL-only
```

No other fields. Everything is in the DashMaps or derivable from them.

### TypecheckProduct

```
TypecheckProduct:
  symbols: SymbolTable    // types, schemes, got_slots, callees, defns, impl source
  file_path: PathBuf      // source file (cache invalidation, file watcher)
```

`SymbolTable` changes:
- `ModuleEntry::Def` gains `defn: Option<Defn>` — needed for monomorphisation and `--run` without cache
- `ModuleEntry::Def` gains `impl_sexp: Option<Sexp>` — trait impl source for codegen replay
- `file_path` moves here from deleted `ModuleStructure`

`ModuleStructure` deleted entirely — all its fields are derivable:
- `path` → on SymbolTable
- `file_path` → on TypecheckProduct
- `import_specs` / `export_specs` → ModuleEntry::Import/Reexport + visibility
- `mod_decls` → submodule entries in typecheck DashMap
- `platform_specs` / `dll_path` → re-discovered at load time, stored in platforms DashMap
- `impl_sexps` / `impls` → on SymbolTable entries

### CodegenInput (transient)

```
CodegenInput:
  method_resolutions:   MethodResolutions        // per-Span call resolution
  expr_types:           HashMap<Span, Type>      // per-Span type (heap classification)
  mono_defns:           Vec<MonoDefn>            // generated monomorphised definitions
  default_method_defns: Vec<Defn>                // expanded default trait methods
  program:              Vec<TopLevel>            // AST
```

Slimmed from CheckResult — fields that were duplicated from SymbolTable removed:
- `type_defs` → read from ModuleEntry::TypeDef in typecheck DashMap during codegen
- `constructor_to_type` → derived from ModuleEntry::Constructor in typecheck DashMap
- `constrained_fn_names` → derived from `scheme.constraints.is_empty()` on ModuleEntry::Def
- `warnings` → returned directly to caller, not stored
- `display` → returned directly to caller (REPL-only)

Consumed by both JIT codegen (priority workers) and .o codegen (nice workers).
Entry removed when scheduler signals both `inmem_done` and `object_done`.

### CodegenProduct

```
CodegenProduct:
  linker:   Option<Linker>          // Some if loaded from cache .o
  code:     DashMap<Symbol, Code>   // per-symbol; additive for REPL redefinition
  got:      Option<GotTable>        // Some if JIT-created; None if linker-loaded
  got_base: *const u8               // base address — either &got or linker's __cranelisp_got
```

```
Code:
  jit: Jit            // owns mmap'd executable pages
  ptr: *const u8      // code pointer (also stored in GOT slot)
```

### Introspection (REPL-only)

```
Introspection:
  source:           Option<String>
  sexp:             Option<Sexp>
  defn:             Option<Defn>
  clif_ir:          Option<String>
  disasm:           Option<String>
  code_size:        Option<usize>
  compile_duration: Option<Duration>
```

Not populated during batch compilation. Only written during REPL codegen.

### Derived state (no longer stored)

| Was on CompilerSession | Now |
|---|---|
| `macro_env: MacroEnv` | Macro clause code ptrs in CodegenProduct.code; clause info on ModuleEntry::Macro |
| `traced_fns` | Built on-demand from typecheck + codegen DashMaps when compiling `(trace ...)` |
| `trace_extra_symbols` | Passed as parameter to compile_and_execute_expr |
| `type_defs` / `type_modules` | Derived from typecheck DashMap (walk modules, collect TypeDef entries) |
| `current_module_structure` | Deleted with ModuleStructure; REPL module state is typecheck.get("user") |
| `error_modules` | Scheduler state (already tracks Failed modules) |
| `def_codegen` | Split into Code (runtime) + Introspection (REPL) |
| `inmem_worker` | Deleted |

## Unified GOT Model

### Problem

Three parallel GOTs exist per cache-loaded module:
1. `GotTable` (JIT) — `[AtomicPtr<u8>; 512]`, slot indices from SymbolTable
2. Linker `got_mmap` — separate mmap, Linker-assigned slot indices
3. `__cranelisp_got_<module>` data symbol in .o — function-address relocations, not referenced by code

### Target

One GOT per module. Slot indices always from `SymbolTable.got_slot`.

**JIT path:**
- Create `GotTable` for module
- Codegen emits `iconst(got_base) + iadd_imm(slot*8) + load + call_indirect`
- After compilation: `got.store_slot(slot, code_ptr)`
- `CodegenProduct.got = Some(got_table)`, `got_base = got_table.base_ptr()`

**Cache-load path:**
- .o compiled with GOT-indirect calls using SymbolTable slot assignments
- `__cranelisp_got_<module>` data section has function-address relocations at matching slots
- Linker loads .o, resolves data section → `__cranelisp_got` populated with code pointers
- Code's ADRP+LDR resolved against `__cranelisp_got` (no separate Linker GOT)
- `CodegenProduct.got = None`, `got_base = address of loaded __cranelisp_got`

**REPL redefinition over cache-loaded code:**
- New `Code { jit, ptr }` inserted in CodegenProduct.code
- `got_base[slot] = new_ptr` — atomic write to `__cranelisp_got` memory
- All callers (JIT or cache-loaded) load from same GOT → see new code

**Trace:**
- `cranelisp_trace_swap_got` / `cranelisp_trace_restore_got` work on `got_base` directly
- Runtime-only: saves GOT contents to heap, swaps in wrapper ptrs, restores after
- No compiler state needed — TracedFnInfo built on-demand from DashMaps

### SessionCompilationEnv

`resolve_got(name)` reads from the DashMaps:
- Slot: `typecheck.get(module).symbols.get(name).got_slot`
- Base: `codegen.get(module).got_base`
- Returns `(got_base as i64, slot)`

### Changes to object codegen (`cranelisp-backend/src/cache/object.rs`)

- Emit GOT-indirect calls (not direct) for cross-function references
- Use `SymbolTable.got_slot` for slot assignments (already available via FnSlotInfo)
- `define_got_data()` already populates `__cranelisp_got` — keep this
- Code references `__cranelisp_got` through ADRP+LDR relocations

### Changes to Linker (`cranelisp-backend/src/cache/linker.rs`)

- Remove internal `got_mmap` / `got_slots` / `got_count`
- Resolve GOT-load relocations against `__cranelisp_got` data section directly
- Return `got_base` as the address of the loaded `__cranelisp_got` data region

## What's Deleted

| Structure | Replacement |
|-----------|-------------|
| `InMemWorkerState` | Fields distributed to CodegenProduct, derived from DashMaps |
| `SharedCodegenState` | Replaced by codegen + typecheck DashMaps |
| `extract_from` / `sync_back_to` | Unnecessary — data permanently in concurrent structures |
| `WorkerJitState` | Each function stores its JIT directly in CodegenProduct.code |
| `ModuleGotRegistry` | GOT lives on CodegenProduct |
| `ModuleCodegenState` (got.rs) | GotTable used directly; slot assignment on SymbolTable |
| `DefCodegen` | Split into Code + Introspection |
| `ModuleStructure` | Deleted — fields derivable from SymbolTable or re-discovered |
| `MacroEnv` | Clause ptrs in CodegenProduct.code; clause info on ModuleEntry::Macro |
| Legacy flat GOT | Per-module GOTs only |
| `module_outputs` DashMap | Replaced by codegen_input |
| `object_codegen_inputs` Mutex | Replaced by codegen_input (both workers read same entry) |
| `CompilerSession.def_codegen` | Replaced by introspection DashMap |
| `CrossModuleGot` type | SessionCompilationEnv resolves cross-module via DashMaps |
| Linker internal `got_mmap` | `__cranelisp_got` data section serves as GOT |
| `CompileContext.got_slots/got_base_ptr/cross_module_got` | `CompileContext.env` only |
| `compile_dep_symbol_inline` with `env: None` | Always use SessionCompilationEnv |

## Thread Reference Bundles

**`PriorityWorkerRefs`** (was PriorityWorkerShared):
```
tc, platform_registry (Mutex-wrapped),
typecheck, codegen_input, codegen, platforms (DashMap refs),
scheduler, module_sexps, suspend_states,
lib_dirs, platform_dirs, project_root
```

**`ModuleCompiler`** (was WorkerContext):
```
tc, platform_registry (&mut),
typecheck, codegen_input, codegen, platforms (DashMap refs),
scheduler, lib_dirs, platform_dirs, project_root
```

No `shared_codegen`, no `worker_jit` — each function compilation writes directly to CodegenProduct.

## TC Integration

TC already stores modules in `DashMap<ModuleFullPath, SymbolTable>`. The `typecheck` DashMap wraps this with TypecheckProduct (adding file_path). For this sprint: TC produces SymbolTable, stores in typecheck DashMap. TC reads from same DashMap for cross-module type resolution.

## Cache Serialization (.meta.json)

Currently serializes `CacheMetadata { symbol_table, module_structure, codegen_state }`.

New: serialize `TypecheckProduct { symbols, file_path }` directly. `ModuleStructure` gone. `CacheCodegenState` simplified — `got_slots` already on SymbolTable entries, `def_entries` replaced by `defn` field on ModuleEntry::Def.

## Implementation Phases

### Phase A: Define new types
- `TypecheckProduct`, `CodegenInput`, `CodegenProduct`, `Code`, `Introspection`
- Add `defn: Option<Defn>` and `impl_sexp: Option<Sexp>` to `ModuleEntry::Def`
- Add `file_path` to TypecheckProduct (or SymbolTable)
- Slim `CheckResult`: remove `type_defs`, `constructor_to_type`, `constrained_fn_names`; codegen reads these from SymbolTable. `warnings` and `display` returned separately, not stored.
- Add DashMaps to CompilerSession alongside existing structures

### Phase B: Unified GOT — object codegen + linker
- Object codegen emits GOT-indirect calls with SymbolTable slot assignments
- Linker removes internal got_mmap, resolves against __cranelisp_got data section
- Return got_base from loaded data section address

### Phase C: Wire codegen through new structures
- `compile_and_register_defn_shared` → writes Code to codegen DashMap
- `codegen_module_symbols` → creates CodegenProduct, uses it throughout
- Cache load → populates CodegenProduct with Linker + got_base
- SessionCompilationEnv reads from typecheck + codegen DashMaps
- Kill legacy flat GOT — fix compile_dep_symbol_inline to use env
- MacroEnv eliminated — macro clause ptrs read from CodegenProduct.code

### Phase D: Wire typecheck + temporaries
- TypecheckProduct wraps SymbolTable + file_path
- codegen_input replaces module_outputs + object_codegen_inputs
- Entries removed when scheduler signals both phases done
- TracedFnInfo built on-demand from DashMaps
- type_defs/type_modules derived from typecheck DashMap

### Phase E: Delete legacy structures
- Delete InMemWorkerState, SharedCodegenState, extract_from/sync_back_to
- Delete WorkerJitState, ModuleGotRegistry, ModuleCodegenState
- Delete ModuleStructure, MacroEnv (as stored field), CrossModuleGot
- Delete legacy CompileContext fields (got_slots, got_base_ptr, cross_module_got)
- Delete DefCodegen
- Rename PriorityWorkerShared → PriorityWorkerRefs, WorkerContext → ModuleCompiler

### Phase F: Cache + introspection cleanup
- Update .meta.json serialization for TypecheckProduct
- Wire slash commands to introspection DashMap
- Grep for deleted types — zero hits in src/

## Verification

```bash
cargo nextest run -E "binary(ring0)" --max-fail 3
cargo nextest run -E "test(trace)" --max-fail 3
cargo nextest run -E "binary(macros)" --max-fail 5
cargo nextest run -E "binary(repl_experience)" --max-fail 3
cargo nextest run -E "binary(cache)" --max-fail 3
cargo nextest run --max-fail 10
```

## Key Files

| File | Changes |
|------|---------|
| `src/session_v4.rs` | CompilerSession with DashMaps only, delete SharedState fields |
| `src/session.rs` | Delete InMemWorkerState, SharedCodegenState, WorkerJitState |
| `src/pipeline.rs` | New signatures, kill legacy GOT paths |
| `src/worker.rs` | ModuleCompiler, PriorityWorkerRefs, DashMap access throughout |
| `crates/cranelisp-types/src/module.rs` | Delete ModuleStructure, add defn/impl_sexp to ModuleEntry::Def |
| `crates/cranelisp-backend/src/codegen_types.rs` | Code, Introspection replace DefCodegen |
| `crates/cranelisp-backend/src/got.rs` | Simplify — GotTable stays, ModuleCodegenState deleted |
| `crates/cranelisp-backend/src/cache/object.rs` | GOT-indirect calls, unified slot assignments |
| `crates/cranelisp-backend/src/cache/linker.rs` | Remove internal got_mmap, use __cranelisp_got |
| `crates/cranelisp-backend/src/cache/serialize.rs` | Serialize TypecheckProduct, not ModuleStructure |
| `crates/cranelisp-types/src/check.rs` | Slim CheckResult: remove type_defs, constructor_to_type, constrained_fn_names |
| `crates/cranelisp-backend/src/compiler/apply.rs` | Remove legacy resolve_got_entry fallbacks |
