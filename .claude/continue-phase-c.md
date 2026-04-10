# Continue: Session Restructure — Phase C Complete

## Context

Read `design/arch/session-restructure.md` for the full target data model.
Read `design/backend/per-module-got.md` §9 for the GOT literal pool architecture.

## Commits (this session)

1. `1d17d20` — delete SharedCodegenState, WorkerJitState, InMemWorkerState; move GOT to TypecheckProduct
2. `755c003` — remove legacy CompileContext GOT fields, delete CrossModuleGot
3. `04b9264` — migrate def_codegen to introspection DashMap + codegen_products
4. `bc48f5a` — unified GOT literal pool: load GOT base from data section entry
5. Uncommitted — remove linker base_cache, add FIXME for builtin call range

## Current Architecture

### GOT dispatch (unified codegen, both JIT and object paths)

```
  entry_addr = global_value(__cranelisp_got_{module})  // literal pool entry
  got_base   = load(entry_addr)                         // GOT base from entry
  fn_ptr     = load(got_base + slot * 8)                // fn ptr from GOT
  call_indirect(fn_ptr)
```

- **GotTable**: heap-allocated during typecheck (`TypecheckProduct.got: Arc<GotTable>`), immovable
- **Literal pool**: 8-byte data entries in JIT data or .o data section, patched with GotTable address
- **JIT**: `Jit::define_got_data(name, ptr)` creates literal pool entries
- **Object**: foreign GOT symbols declared as Export data (8 bytes, zeroed), linker patches at load time
- **Self-module GOT**: full GOT table in .o data section with function address relocations (for AOT --link)

### Data flow

- `TypecheckProduct.got` — `Arc<GotTable>` allocated at module registration
- `CodegenProduct.code` — `DashMap<Symbol, Code>` with JIT + code pointer per function
- `CodegenProduct.linker` — keeps loaded .o mmap alive
- `Introspection` DashMap — `/source`, `/sexp`, `/ast`, `/clif`, `/disasm` data (FQSymbol keys)
- `codegen_products` — code pointers for macro dispatch and test discovery

## What's NOT done

1. **FIXME(/backend): external function call range** — runtime intrinsic and platform DLL function calls use BRANCH26 (BL, ±128MB range). If loaded .o code is far from these functions, BL fails. Fix: put external function addresses in literal pool entries (Export data) and use ADRP+LDR+BLR instead of BL. Same pattern as GOT bases. Filed as FIXME in linker.rs.

2. **REPL module (src/repl/)** — not compiled (commented out in lib.rs). When re-enabled, needs updating to match new APIs (no InMemWorkerState, no CompilationSession struct).

3. **`ModuleCodegenState` cleanup** — still exists in backend crate, used by cache serialization and some tests. Can be simplified or removed once cache serialization is updated.

4. **Introspection population** — `/clif`, `/disasm`, `/info` (code_size, compile_duration) fields are not populated in the v4 path. The CLIF IR is returned from `compile_defn` but discarded in `compile_and_register_defn_shared`. Thread introspection data from compilation to the DashMap.

5. **`macro_env` on CompilerSession** — legacy; macro dispatch now reads from codegen_products. Can be removed once all macro lookup paths use codegen_products.

## Verification

```bash
cargo nextest run -E "binary(ring0)" --max-fail 3
cargo nextest run -E "binary(macros)" --max-fail 5
cargo nextest run -E "binary(ring0) | binary(ring1) | binary(ring2) | binary(ring3_repl) | binary(macros) | binary(modules) | binary(v4_pipeline) | binary(v4_repl_eval) | binary(rc)" --no-fail-fast
```

Pre-existing failures (25 total): 2 ring0 (checked_div), 4 macros (REPL error recovery), ~19 modules/ring2/v4_pipeline/v4_repl.
