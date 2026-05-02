---
number: 0021
title: TC-sourced call graph with per-symbol persistence on ModuleEntry
status: operative
---

# 0021 — TC-sourced call graph with per-symbol persistence on ModuleEntry

The per-symbol call graph (callee list) is extracted during typechecking from method resolutions and stored persistently on `ModuleEntry`. `ModuleEntry::Def` and `ModuleEntry::Macro` each gain `callees: Vec<FQSymbol>`. `FormCheckResult.call_graph_edges` carries `Vec<(Symbol, FQSymbol)>` (caller is local, callee is fully qualified). `finalize_check_result()` groups edges by caller and writes to `ModuleEntry` in the `SymbolTable`. Cross-module queries use the existing `tc.symbol_table(module).get(name)` path — same as type resolution. `CheckResult` also carries a transient `call_graph: CallGraph` (rich, with tail-position/span) for within-module codegen/analysis. Codegen-sourced call graph rejected: the scheduler needs pre-codegen callee visibility for parallel macro dep compilation (§3.2 of `pipeline-v4.md`); codegen doesn't discover callees typechecking didn't resolve (Principle 7); building codegen-sourced now and replacing later violates Principle 8.
