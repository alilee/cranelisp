---
number: 0023
title: Uniform codegen; mode is a Module property, not a compile_to_module parameter; two-GOT model — same data symbol, different resolvers
status: operative
---

# 0023 — Uniform codegen: mode is a Module property, not a compile_to_module parameter; two-GOT model — same data symbol, different resolvers

`compile_to_module<M: Module>(module_path, names, symbol_tables, module)` has four parameters and no mode discriminator. Object vs JIT differs only in how the passed-in `Module` implementation resolves the `__cranelisp_got_{module}` data-symbol *reference* at finalize time. The backend emits byte-identical CLIF IR in both modes — `global_value` against `__cranelisp_got_{module}` data symbols declared as `Linkage::Import` from the caller's POV. GOT bases are resolved per mode at finalize, not at codegen. Rejected designs: `CompilationEnv` trait with JIT/Object impls (re-enshrines the dual-pipeline divergence Principle 11 exists to prevent); thin `compile_to_module_jit`/`_object` wrappers over a crate-private core (two public entry points invite divergence regardless of internal structure); `CodegenTarget` enum parameter (a mode discriminator is what we're eliminating). Defined Sprint 56 Phase 2; two-GOT framing added Sprint 58 Wave 2. Canonical location: `crates/cranelisp-backend/src/lib.rs`. Rationale: Principle 11 (single pipeline; mode as Module property, not function parameter) + JIT pays one extra memory load per cross-module call vs structural simplicity — most code runs from cached object files anyway.

**The two-GOT model.** Every reference to `__cranelisp_got_{M}` resolves to a base address; the *runtime memory the base addresses* is one of two distinct artefacts depending on which Module implementation is used at finalize time. Both share the same name and the same per-slot semantics (slot index `i` is `M`'s `i`th defined function), and both are reachable from the same byte-identical CLIF — but they are otherwise unrelated:

| GOT | Backing | Owner | Lifetime | When read | Mutable |
|---|---|---|---|---|---|
| **SymbolTable GOT** | `Arc<GotTable>` field on `SymbolTable` (in-process memory) | runtime / `cranelisp-types` | session | JIT (`--run`, REPL) — `JITBuilder::symbol_lookup_fn` returns `symbol_tables[M].got.base_ptr()` at finalize | yes — REPL redefinition writes a new fn ptr into the existing slot via the Decision-31 atomic swap |
| **`.o` data section GOT** | `Linkage::Export` data symbol `__cranelisp_got_{M}` defined inside `M`'s own `.o`, with relocation initializers against the local function symbols | object-file artefact | one per `.o` file | `--link` mode — system linker (or our cache `Linker`) patches relocations against the defined data symbol; never read in `--run`/REPL | no — initialised by the linker at load time, never mutated |

The same data-symbol *reference* (`Linkage::Import` against the name `__cranelisp_got_{M}`) appears in every CLIF emission; how it is resolved is the mode parameter. This is the canonical illustration of Principle 11 (single pipeline, mode parameters): one CLIF, two resolvers. Cross-references: Decision 31 (the SymbolTable GOT slot is the redefinition atomic-swap target); Decision 36 (function symbol naming + linkage); `design/arch/interfaces.md` §"Symbol Table" (SymbolTable GOT field) + §"Backend Types" (object-file GOT artefact).
