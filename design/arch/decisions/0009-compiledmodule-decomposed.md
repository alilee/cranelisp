---
number: 0009
title: CompiledModule decomposed (superseded by 22, 25, 38, 39)
status: superseded-by-0022,0025,0038,0039
---

# 0009 — CompiledModule decomposed

The original Decision 9 framing collapsed `CompiledModule` into a `SymbolTable` + per-product side-stores model. That decomposition has fully evolved into the current shape, with each piece pinned by a successor Decision:

- **Per-symbol code** lives on `ModuleEntry::Def.code` (per Decision 25), accessed via the `defined_symbols()` predicate (per Decision 22).
- **Per-symbol AST** lives on `ModuleEntry::Def.ast` (per Decision 22's predicate filter).
- **`SharedState`** is the formal worker-shareable subset of session state with `Introspection` mode-discriminated by `Option` (per Decision 38).
- **Per-defn source** lives on `Introspection.source` (per Decision 39); no separate `module_sources` SharedState field.

`TypecheckProduct`, `CodegenProduct`, `ModuleCodegenState`, and `ModuleStructure` — the structural side-stores Decision 9 originally proposed — have all been dissolved into the per-entry shape above.

This Decision survives as a redirect: see the four superseding Decisions for the current contract.
