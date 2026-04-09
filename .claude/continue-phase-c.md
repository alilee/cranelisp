# Continue: Session Restructure Phase C

## Context

Read `design/arch/session-restructure.md` for the full target data model.

Two commits landed:
1. `0bc433f` — Phase A (target types, defn on ModuleEntry::Def) + Phase B foundations (unified GOT via global_value, object codegen GOT-indirect)
2. `f4abe11` — DashMaps correctly on CompilerSession (not SharedState)

## What's done

- `TypecheckProduct`, `CodegenInput`, `CodegenProduct`, `Code`, `Introspection` types defined in `src/session_v4.rs`
- `typecheck_products`, `codegen_inputs`, `codegen_products`, `introspection` DashMaps on `CompilerSession`
- `ModuleEntry::Def` has `defn: Option<Box<Defn>>`
- `got_data_symbol_name()` in `compiler/mod.rs` (single source of truth)
- `CompilationEnv::resolve_got_module()` returns `(ModuleFullPath, slot)` — default returns None
- `compile_direct_call` has unified GOT path using `global_value(DataId)` (checked before legacy paths)
- `emit_got_indirect_call_via_data_id()` on FnCompiler
- `ObjectCompileInput` implements `CompilationEnv` (no separate env struct)
- Object codegen uses GOT-indirect calls via env (not direct calls)
- `SessionCompilationEnv` has `resolve_module_slot` helper (inactive — returns None via default until JIT GOT symbols registered)
- `ModuleGotRegistry::jit_got_symbols()` ready for JIT symbol registration

## Phase C: Wire codegen through new DashMaps

### Core pattern

Workers access DashMaps via scoped-thread borrows. `register_module_with_source` (session_v4.rs:720) already borrows fields from self for the scoped thread scope. Add `&self.codegen_products` to the borrow set.

### Steps

1. **Add `codegen_products` to `PriorityWorkerShared`** (worker.rs) — add `codegen_products: &'a DashMap<ModuleFullPath, CodegenProduct>` field. Borrow from `&self.codegen_products` in `register_module_with_source`.

2. **Write `collect_jit_symbols_for_module()`** — scans the module's symbol table imports to collect:
   - Platform function pointers (from DLL handles, for `ModuleEntry::Def { kind: Primitive { PlatformEffect } }`)
   - GOT base pointers (from `got_registry`, for each imported module)
   - Current module's own GOT base
   Only what the module actually imports, not everything in the session.

3. **Update `compile_and_register_defn_shared`** — after JIT compilation, write `Code { jit, ptr }` to `codegen_products.get(module).code.insert(name, code)`. Keep writing to SharedCodegenState too (dual-write) for backward compatibility during transition.

4. **Activate `resolve_got_module` on `SessionCompilationEnv`** — uncomment the implementation (uses `resolve_module_slot`). Register GOT data symbols on JITBuilder via `collect_jit_symbols_for_module`.

5. **Eliminate `platform_symbols` parameter** — replaced by `collect_jit_symbols_for_module`. Update `compile_and_register_defn_shared`, `compile_and_execute_expr`, `codegen_module_symbols`, `compile_macro_defn_no_dealloc`.

6. **Eliminate `SharedCodegenState` + `extract_from`/`sync_back_to`** — remove from 5 sites in session_v4.rs (lines 734, 1028, 1032, 1207, 1831). Workers use `codegen_products` DashMap directly.

7. **Eliminate `WorkerJitState`** — each compiled function writes its JIT directly to CodegenProduct.code. No per-worker accumulator, no drain.

8. **Eliminate `InMemWorkerState`** — all fields distributed. Delete struct from session.rs.

### Phase B remainders (interleave)

- Activate `resolve_got_module` on `SessionCompilationEnv` (step 4 above)
- Linker: resolve against `__cranelisp_got` data section, remove internal `got_mmap`
- Remove legacy `CompileContext` fields: `got_slots`, `got_base_ptr`, `cross_module_got`

### Key design decisions

- Platform functions are called directly (not through GOT) — they use `declare_function(name, Import)` + `call`, resolved via JITBuilder::symbol()
- GOT-indirect calls use `global_value(DataId)` — same codegen for JIT and object
- JIT symbols collected per-module from symbol table scan (not global cache)
- No `platform_symbols` parameter — derived from primary sources at JIT creation
- DashMaps on CompilerSession, accessed by workers via scoped-thread field borrows

### Verification after each step

```bash
cargo nextest run -E "binary(ring0)" --max-fail 3
cargo nextest run -E "binary(macros)" --max-fail 5
cargo nextest run --max-fail 10
```

Pre-existing failures: 2 ring0 (checked_div), 4 macros, 10 cache, 11 sketch_port.
