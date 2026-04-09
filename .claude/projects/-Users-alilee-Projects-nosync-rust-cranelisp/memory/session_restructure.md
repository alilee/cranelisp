---
name: Session restructure design
description: Major restructuring of CompilerSession — 5 state structs collapsed to DashMaps, unified GOT, CheckResult slimmed, ModuleStructure deleted
type: project
---

Sprint 49 design: collapse InMemWorkerState, SharedCodegenState, WorkerJitState, extract_from/sync_back_to into DashMap-based model.

**Why:** 5 redundant state structs exist from single-GOT era. extract/sync dance converts HashMap↔DashMap unnecessarily. Three parallel GOTs per cache-loaded module.

**How to apply:** Full plan at `design/arch/session-restructure.md`. Six phases (A-F). Phase A: define new types. Phase B: unified GOT. Phases C-D: wire through. Phase E: delete legacy. Phase F: cache/introspection cleanup.

Key decisions:
- CompilerSession has only DashMaps + scheduler. All other state derived.
- CodegenInput replaces CheckResult (slimmed: type_defs, constructor_to_type, constrained_fn_names removed — read from SymbolTable)
- ModuleStructure deleted entirely (all fields derivable)
- MacroEnv eliminated (clause ptrs in CodegenProduct.code)
- TracedFnInfo built on-demand, not stored
- One GOT per module: .o uses __cranelisp_got data section, Linker resolves against it, JIT creates GotTable
- One JIT per symbol (owns mmap'd pages, enables clean drop on redefinition)
- `defn: Option<Defn>` and `impl_sexp: Option<Sexp>` added to ModuleEntry::Def
