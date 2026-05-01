---
number: 0022
title: `defined_symbols()` is the shared codegen-compilable predicate
status: operative
---

# 0022 — `defined_symbols()` is the shared codegen-compilable predicate

One filter, exposed as `SymbolTable::defined_symbols()`, returns entries where `ast.is_some() AND kind != Overloaded AND kind != UserFn { constrained_fn: Some(_) }`. Both the caller (priority worker in `/int`) and the backend internal loop consume this iterator. No alternative filter — `compile_to_module` trusts the contract: if a name in `names` resolves to an entry with `ast: None`, it returns a `CodegenError` rather than falling back to synthesis. Defined during Sprint 56 (Phase 2, Wave 0) to eliminate the split between base-defn program iteration and symbol-table lookup. Canonical location: `crates/cranelisp-types/src/module.rs` (SymbolTable impl). Rationale: Principle 7 (single source of truth — no two filters can diverge) + Principle 11 (single pipeline, mode parameters — the predicate is identical for JIT and object paths).
