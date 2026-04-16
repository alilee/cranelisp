# Codegen Convergence — Sprint 54 Wave 3a

## Problem

Two codegen entry points compile a module's functions, violating Principle 11 (single pipeline) and Principle 7 (single source of truth):

1. **`compile_to_module`** (`crates/cranelisp-backend/src/lib.rs`) — backend crate's public API. Generic over `M: Module`. Used by nice worker for `.o` compilation.
2. **`codegen_module_symbols`** (`src/worker.rs`) — integration layer JIT path. Used by priority worker and REPL eval.

The two paths have diverged: `compile_to_module` handles multi-sig but skips TraitImpl. `codegen_module_symbols` handles TraitImpl but panics on multi-sig. This causes 3 test failures (multi-sig batch) and will cause more as features are added.

## Target

Pipeline-v4 §4 + §9 is the authoritative design. Key points:

- **`compile_to_module` is the sole compilation entry point** (§9.3). Both JIT and object paths call it.
- **Symbol table is the single store** (§9.1). `compile_to_module` reads AST bodies, types, resolved calls, and GOT slots from symbol table entries. No separate `program: Vec<TopLevel>` or `CheckResult`.
- **Per-function JIT isolation preserved** (§9.4). JIT callers pass one symbol name + one fresh JITModule. Object callers pass all names + one ObjectModule.
- **`compile_to_module` is self-sufficient** (§9.3). Given module path, symbol names, symbol tables, and a Module, it discovers everything internally (intrinsics, cross-module refs, platform symbols, GOT base addresses).

See `design/arch/pipeline-v4.md` §9 for the full data model.

## Current vs Target Gap

| Aspect | Current | Target (pipeline-v4 §9) |
|--------|---------|------------------------|
| Compilation entry points | 2 (`compile_to_module` + `codegen_module_symbols`) | 1 (`compile_to_module`) |
| Defn bodies | Separate `program: Vec<TopLevel>` | On `ModuleEntry::Def.ast` |
| Resolved calls / expr types | `CheckResult` side maps keyed by Span | On AST nodes directly |
| GOT table | On `TypecheckProduct` | On `SymbolTable` |
| Compiled code | Separate `codegen_products` DashMap | On `ModuleEntry::Def.code` (generic `C`) |
| Linker | Separate handling | On `SymbolTable.linker` (generic `L`) |
| Platform fn pointers | Separate `session.platform` registry | On symbol table entries |
| Introspection | On `TypecheckProduct.source_text` | Separate introspection map; source from AST |
| Module file path | On `TypecheckProduct.file_path` | Deterministic from module path + project root |
| `"user"` special-casing | In `compile_to_module` jit_prefix logic | None — backend treats all modules uniformly |

## Migration

This is a multi-phase migration. See `design/arch/pipeline-v4-roadmap.md` for the authoritative step-by-step plan with dependency ordering, verification criteria, and file-level touch lists. The roadmap supersedes any migration steps previously listed here.

Key sequence: Phase 1 (AST + types on symbol table) → Phase 2 (single codegen entry point) → Phase 3 (GOT + code on symbol table) → Phase 4 (platform + persistent workers) → Phase 5 (structural decls + cache).
