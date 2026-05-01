---
number: 0009
title: CompiledModule decomposed
status: operative
---

# 0009 — CompiledModule decomposed

evolved + RETRACTED in part. `ModuleCodegenState` and `ModuleStructure` deleted during session restructure (correct, retained). The framing "`SymbolTable` (in TypeChecker DashMap) + `TypecheckProduct` + `CodegenProduct` + `Introspection` on `SharedState`" is partially superseded:
   - `TypecheckProduct` + `CodegenProduct` dissolved into `ModuleEntry::Def` per Decisions 22, 25 (per-symbol code on `Def.code`, AST on `Def.ast`, etc.).
   - `Introspection on SharedState` was directionally correct but its field shape was unspecified — Decision 38 pins the formal definition (`Option<DashMap<FQSymbol, Introspection>>` with mode-conditional `Option`).
   - Per-defn source is on `Introspection.source` per Decision 39 — there is no separate `module_sources` field on SharedState.

   See Decisions 38 + 39 for the current shape.
