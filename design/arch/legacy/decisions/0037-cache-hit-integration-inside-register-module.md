---
number: 0037
title: Cache-hit integration lives inside `register_module`'s recursive flow; codegen phase is order-independent because typecheck phase pins GOT slot LAYOUT
status: operative
---

# 0037 — Cache-hit integration lives inside `register_module`'s recursive flow; codegen phase is order-independent because typecheck phase pins GOT slot LAYOUT

Cache-hit decision and load are NOT a parallel orchestration codepath; they live INSIDE `register_module`'s normal recursive register-then-recurse-on-imports flow. The pre-Sprint-58 `try_cache_hit_load` (`src/worker.rs:1169`) — which re-implemented dependency discovery, ordering, and GOT setup for cache-hit modules in parallel with the fresh-build code path — is deleted at Sprint 58 Wave 2. The canonical recursive flow is:

```
register_module(M):
  if `<cache_dir>/M.meta.json` exists and schema_version matches:
    deserialise → install SymbolTable for M → mark typecheck-complete
  else:
    parse → typecheck → install SymbolTable for M
  for each import in SymbolTable[M].imports:
    register_module(import.module)   # recursive, blocking on transitive deps
```

After typecheck phase completes for ALL reachable modules (whether the per-module typecheck-or-deserialise step ran fresh-typecheck or cache-deserialise), codegen phase runs. Per-module codegen workers run in **any order, in parallel**:

```
codegen_worker(M):
  # Same body whether fresh or cache-hit:
  register_symbol("__cranelisp_got_M", &symbol_tables[M].got.base_ptr())   # JIT-mode GOT identity
  if fresh-build (no cached .o):
    compile_to_module<JITModule>(M, defined_symbols(M), &symbol_tables, jit)
    jit.finalize() → for each defined symbol: write got_slot[s] = jit.get_finalized_ptr(func_ids[s])
  else cache-hit (.o exists):
    linker.load_object(read(<cache_dir>/M.o))
    for each defined symbol s in symbol_tables[M]:
      ptr = linker.get_symbol(bare_name(s))   # Decision 36: bare-Local lookup
      if ptr.is_none(): error  # defensive — see "no swallowed failures" below
      symbol_tables[M].got.store_slot(symbol_tables[M].symbols[s].got_slot, ptr)
```

**Order-independence rationale.** The typecheck phase establishes GOT slot LAYOUT — slot indices are pinned in `SymbolTable.symbols[s].got_slot` for every defined symbol, before any codegen worker runs. Codegen workers fill slot CONTENTS (the function pointer at each slot). Order across modules is irrelevant because no codegen worker reads another module's GOT contents — the cross-module call mechanism (CLIF `global_value` against `__cranelisp_got_{other_M}`) reads at runtime, not at codegen time. Each module's codegen is therefore a self-contained operation on its own SymbolTable + its own JIT (or its own loaded `.o`) + its own GOT slots. No bespoke topo-sort logic is needed in the codegen phase; topo-ordering happened implicitly during typecheck-or-deserialise via the recursive `register_module` (which blocks on transitive deps for type resolution, but that's the typecheck dependency, not a codegen one).

**No swallowed failures.** The pre-Sprint-58 `worker.rs:2810-2823` pattern unconditionally pushed each cached symbol onto `loaded_symbols` regardless of whether the GOT slot population succeeded — when `linker.get_symbol(name)` returned `None` (Bug A: wrong symbol name was being looked up), the slot stayed NULL but the worker reported success. The codegen worker MUST push to `loaded_symbols` only when the address resolved, OR error out with a `CacheLoadError` when any expected symbol fails to resolve. The latter is preferred — silently producing an "inmem-done" state with empty GOT slots is a contract violation per Decision 31's safety invariant (a slot that resolves to NULL is reachable from the code path that calls it, which violates "no fn pointer reachable through the GOT is uninitialised").

Rejected alternatives: (a) keep `try_cache_hit_load` as a "specialised fast path for cache-hit" — re-implements the recursive walk of `register_module`, invites divergence (Principle 11 violation; this is precisely the dual-pipeline pattern that motivated Principle 11); (b) load all `.o` files in topo-order during cache-hit — confuses typecheck-time topology with codegen-time independence; the topo order is needed for typecheck (signatures must be visible to importers) but not for codegen (each `.o` is GOT-base-addressable independently); (c) re-codegen on cache-hit (Decision-25's earlier framing) — wastes the `.o` artefact already on disk and breaks the "cache stores both `.meta.json` and `.o`" invariant Decision 25 establishes. Defined Sprint 58 Wave 2. Canonical location: `register_module` and the codegen worker loop in `src/worker.rs` + `src/session_v4.rs`. Owner: `/int`. Rationale: Principle 11 (single pipeline — cache-hit and fresh-build branch within ONE register-then-codegen flow, parameterised by "is the cached `.o` present?") + Principle 7 (single source of truth — one register_module function, one codegen worker; no duplicated dependency-discovery logic) + Principle 8 (the recursive-flow shape IS the §9 target; the pre-Sprint-58 `try_cache_hit_load` was interim infrastructure that survived past its useful life) + Decision 31 (the safety invariant requires GOT slots to be populated atomically and observably — defensive error on resolution failure preserves the invariant) + Decision 36 (bare-Local naming makes the cache-hit linker lookup's `bare_name(s)` form correct uniformly, no per-module conditionals).
