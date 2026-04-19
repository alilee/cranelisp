# Symbol-Table Cache (Step 5b)

Implementation design for the worker-side cache write path that emits the enriched `SymbolTable` as the single cache artefact, and consumes it on cache-hit. Coordinates with `/backend`'s `module-caching.md` (the consumer-and-format-owner of the `.meta.json` envelope).

Spec anchor: `pipeline-v4.md` §9.5 ("the `.meta.json` file is a serialized `SymbolTable`"). Decisions 25 (compiled code on entry, `#[serde(skip)]`), 26 (platform fn ptr on entry, `#[serde(skip)]`), 33 (structural decls as fields), 34 (`schema_version: u32`).

## 1. Problem Statement

Today the cache write path reads from at least four distinct stores to assemble what it persists:

1. `SharedState.module_structures` — `ModuleStructure` per module (imports/exports/mod decls/platform specs).
2. `SharedState.symbol_tables` — `SymbolTable` (types, schemes, GOT slot assignments, AST bodies after Phase 1).
3. `SharedState.codegen_programs` — the `Vec<TopLevel>` "stash" populated by the priority worker so the nice (cache) worker has codegen input without re-typechecking.
4. `SharedState.kept_jits` (and `kept_linkers`) — runtime retention pools.

The cache-restore (cache-hit) path then has to rebuild the equivalent splay across these stores from a `.meta.json` shape that does not match any single one of them. The "stash" exists purely because the cache worker needed `Vec<TopLevel>` in its hands and the symbol-table form was not yet sufficient to drive `compile_to_module`. After Phase 1 (AST on symbol table) and Phase 2 (single codegen entry point) shipped in Sprints 55/56, that constraint disappeared on the producer side. Step 5b removes the compensating asymmetry: the worker writes one thing (the `SymbolTable`), the cache stores one thing, and the cache-hit path rehydrates one thing.

Two complications drove the historical splay and must be solved cleanly here:

- **`#[serde(skip)]` runtime fields**. `ModuleEntry::Def.code: Option<C>` and `.platform_fn_ptr: Option<*const u8>` are runtime state and serialise to nothing; they re-derive on cache-hit load. The cache-hit path must therefore know how to drive code re-derivation (codegen on the deserialised `ast`) and platform fn-ptr re-resolution (re-open the DLL referenced by the surviving `PlatformDecl`, read its manifest).
- **Schema version**. Caches written by older binaries (pre-Sprint-58) lack the structural-decl fields and the `schema_version` itself; cache-hit reads MUST detect and reject these to avoid restoring half-formed state.

## 2. Key Design Decisions

| Decision | Choice | Rationale |
|---|---|---|
| Cache artefact shape | `.meta.json` is a serialised `SymbolTable<(), ()>` (the typecheck-product flavour, no concrete `C`/`L`); `.o` is unchanged Cranelift `ObjectModule` output. | Decision 25 + 32 + 33 — one store, generic over runtime decorations. |
| Stash deletion | `SharedState.codegen_programs` and the `stash_codegen_program` helper deleted as part of Step 5b. The cache (nice) worker reads `symbol_tables` directly via `defined_symbols()`. | Removes the dual-pipeline residue Decision 22 was already pointing at. |
| Schema version owner | `CACHE_SCHEMA_VERSION: u32` constant lives in `crates/cranelisp-backend/src/cache/mod.rs` (owned by `/backend`). The `/int` worker reads the constant when populating `SymbolTable.schema_version` before serialising. | Decision 34. `/backend` owns the cache crate and the schema lifecycle; `/int` is a stamping consumer. |
| Cache-hit code re-derive trigger | After deserialising, the priority worker enqueues the module for codegen via the same path used for fresh builds, but with `ast` already populated and typecheck skipped. | Decision 25's "regenerated from `ast` on cache-hit load" — uses the existing single codegen entry, no parallel cache codegen path. |
| Cache-hit platform-fn-ptr re-derive trigger | Iterate `symbol_table.symbols` for `Def { kind: Primitive { primitive_kind: PlatformEffect, .. }, .. }` entries; for each, walk the import chain to the owning `PlatformDecl` (also in the symbol table) and re-resolve. | Decision 26. The walk is identical to the live-build path; the only difference is the trigger (after deserialise vs after `(platform …)` form processing). |
| Cache-hit envelope sniff | Read `schema_version` from a partial deserialise (or via a thin `CacheEnvelope { schema_version, table }` wrapper if `serde_json` ergonomics demand it). Any mismatch with `CACHE_SCHEMA_VERSION` invalidates the cache as if a dependency changed. | Decision 34. `/int` matches `/backend`'s "version mismatch is the same code path as dep-hash mismatch" framing — no special-cased restart. |

## 3. Data Flow

### 3.1 Cache-write path (priority worker → nice/cache worker)

Today (Sprint 57 transitional shape):

```
priority worker:
  ├─ pass1_register, pass2_check populate symbol_tables[module]
  ├─ form-handlers populate module_structures[module]
  ├─ on completion: stash_codegen_program(shared, module, program)
  └─ scheduler.notify_typecheck_complete(module)

cache (nice) worker:
  ├─ wakes on typecheck-complete signal
  ├─ drains codegen_programs[module] (the stash)
  ├─ reads symbol_tables[module] for type info
  ├─ reads module_structures[module] for structural decls
  ├─ assembles CacheWritePacket from all four sources
  └─ writes .meta.json + .o
```

Step 5b target shape:

```
priority worker:
  ├─ pass1_register, pass2_check populate symbol_tables[module]
  │  (same as today — Step 5a moves structural decls onto the same table,
  │   so module_structures[module] writes go away)
  ├─ on completion: scheduler.notify_typecheck_complete(module)
  │  (no stash; nothing to populate beyond symbol_tables)
  └─ (kept_jits parallel pool; reclaimed by Step 5c)

cache (nice) worker:
  ├─ wakes on typecheck-complete signal
  ├─ reads symbol_tables[module] (sole input)
  ├─ stamps schema_version = CACHE_SCHEMA_VERSION
  ├─ assembles CacheWritePacket { module, table_clone, ... }
  └─ writes .meta.json (serialise SymbolTable) + .o (compile_to_module)
```

The `.o` emit step is unchanged — it reads `defined_symbols()` from the same symbol table and runs `compile_to_module`. The `.meta.json` emit becomes a single `serde_json::to_writer(file, &symbol_table)` call (or via the `CacheEnvelope` wrapper if needed). All the splay code in `cache_writer.rs` and `compile_module_object` that exists to unify across stores deletes.

### 3.2 Cache-hit path (cache load → priority worker re-derive)

Today the cache-hit path lives in `try_cache_hit_load` (`src/worker.rs:1169`) and rebuilds the symbol table by hand from a custom packet, then has to re-register imports because the original specs aren't preserved cleanly.

Step 5b target:

```
cache-hit:
  ├─ read .meta.json bytes
  ├─ peek at schema_version (cheap partial deserialise or envelope wrapper)
  │   ├─ if mismatch: treat as cache-miss (same code path as dep-hash mismatch)
  │   └─ if match: continue
  ├─ deserialise SymbolTable<(), ()> directly via serde derive
  ├─ install symbol_tables[module] = deserialised table
  ├─ load .o through Linker (existing crate code), populate
  │  Def.code on each symbol that codegen produced (Linker resolves the
  │  symbol name → addr; the worker walks defined_symbols() and writes
  │  Code { jit: ..., ptr } back into each Def.code field)
  │  — for cached modules, the "Jit" handle slot may be a Linker handle
  │  instead; see §3.3 below for the C/L bridging
  ├─ for each Def with kind == PlatformEffect: walk to PlatformDecl,
  │  re-open the DLL, read manifest, write platform_fn_ptr
  ├─ scheduler.mark_typecheck_done(module) — same state the priority worker
  │  would emit on full typecheck; downstream importers see no difference
  └─ done
```

The cache-hit path becomes structurally identical to the priority worker's post-typecheck handoff, modulo the `.o`-via-Linker step in place of `compile_to_module`. There is no parallel "cache install" codepath that duplicates symbol-table state.

### 3.3 Bridging `C` / `L` between fresh-build and cache-hit

`SymbolTable<C, L>` is parameterised; the integration layer (Step 5c) chooses concrete types. Two natural choices coexist:

- Fresh build: `C = Arc<Jit>` (Decision 31 Scenario 2), `L = ()` (no linker for JIT'd code).
- Cache hit: `C = something that wraps the .o-mapped code address`, `L = Arc<Linker>` (the cache linker keeps `.o` pages alive).

The integration layer's session instantiation (`src/session_v4.rs`) defines a single `Code` enum that wraps both forms:

```rust
pub enum Code {
    Jit { jit: Arc<cranelisp_backend::jit::Jit>, ptr: *const u8 },
    Linker { linker: Arc<cranelisp_backend::cache::Linker>, ptr: *const u8 },
}
```

This keeps `C = Code` uniform across fresh-build and cache-hit modules in the same session (a project mixes both). The pointer-only access pattern (`code.ptr`) is the same; the variant carries the lifetime root.

The detailed shape of `Code` (and whether to split `C` vs accept the enum) is the subject of the parallel `symbol-table-generics.md` design doc (Step 5c). This doc consumes whichever shape that one lands; from the cache's perspective the only invariant is that *the deserialised table has `code: None` everywhere*, and the integration layer fills in `code: Some(...)` as the `.o` linker resolves each symbol.

## 4. Schema-Version Protocol (Decision 34)

| Aspect | Behaviour |
|---|---|
| Field placement | `pub schema_version: u32` on `SymbolTable`, `#[serde(default)]` so legacy caches deserialise as `0`. |
| Constant home | `crates/cranelisp-backend/src/cache/mod.rs` exposes `pub const CACHE_SCHEMA_VERSION: u32 = 1;` (Sprint 58 ships the first numbered shape). |
| Bump policy | `+1` on every shape-changing addition, deletion, or type change. `#[serde(default)]` field additions whose default value matches a fresh-build don't require a bump; explicit-default additions do. |
| Mismatch behaviour | Same code path as dep-hash mismatch: treat as cache-miss, fall through to fresh build. No user-visible error. The rejected cache is not deleted (next write overwrites it). |
| Sniff strategy | `/int` peeks the version via a thin envelope wrapper or partial deserialise. Both are equivalent; the wrapper is preferred if `/backend`'s `module-caching.md` selects it (the doc owns the envelope shape). |

`/int`'s worker calls into `cache::CACHE_SCHEMA_VERSION` to populate the `schema_version` field on every cache-write. The constant is read-only from `/int`'s perspective.

## 5. Affected Files

| File | Change |
|---|---|
| `src/worker.rs` form-handlers | Stop writing to `shared.module_structures` (Step 5a moves these to `symbol_tables[module].imports/exports/platforms/submodules`). |
| `src/worker.rs` `stash_codegen_program` | Delete. |
| `src/worker.rs` `try_cache_hit_load` | Rewrite to the §3.2 protocol — deserialise into `SymbolTable<(), ()>`, install, drive `.o` linker, re-derive platform fn ptrs. |
| `src/session_v4.rs` `compile_module_object` | Stop reading `codegen_programs`. Read `symbol_tables[module]` directly; `defined_symbols()` is the iteration. Stamp `schema_version` before serialise. |
| `src/session_v4.rs` `SharedState.codegen_programs` | Delete (the field on `SharedState`). |
| `src/cache_writer.rs` | The `CacheWritePacket` shape changes: now carries `SymbolTable<(), ()>` (clone) instead of the splay of typecheck/codegen/structure inputs. The TODO at line 187–188 (`empty_tables = dashmap::DashMap::new()`) goes away — the packet itself carries the table data. |
| `crates/cranelisp-backend/src/cache/` | Owned by `/backend`. The `CacheWritePacket` shape and the `process_cache_packet` logic are co-designed with the `/backend` owner during Wave 2. `/int`'s worker calls into the simplified API. |

## 6. Edge Cases & Invariants

- **Empty modules** (no `defn`, only imports). The `.meta.json` still serialises, populated with `imports` only. Cache-hit deserialises and installs without invoking `compile_to_module` (because `defined_symbols()` is empty). The scheduler's typecheck-done notification still fires, so importers don't block.
- **Modules whose only defns are constrained-fn templates**. `defined_symbols()` filters templates out (Decision 22). The `.o` emit produces nothing. The `.meta.json` still records the `Def { kind: UserFn { constrained_fn: Some(...) }, ast: Some(...), code: None, ... }` entry; importers monomorphise on demand at their own call sites.
- **Modules with `(platform …)` declarations whose DLL is missing on cache-hit load**. The cache is invalid for this run (the `platform_fn_ptr` cannot be re-resolved). Fall through to a full rebuild (which will hit the same DLL-missing error and fail cleanly with a spec-defined error message).
- **Macro entries**. `ModuleEntry::Macro` carries `clauses: Vec<MacroClauseInfo>` but the per-clause compiled fn ptrs are *not* on `Macro` directly — each clause has a corresponding `Def` entry (`__macro_{name}_clause_{i}`) which is what `defined_symbols()` returns. The `.o` covers those; cache-hit re-resolves them through the same Linker call as user fns.
- **Schema mismatch with non-empty cache directory**. Behaviour is "treat as miss" — the cache directory is left intact; the next write will overwrite. No user-visible message.
- **Concurrent cache writes**. The cache writer is single-threaded (one background mpsc consumer); the priority worker writes via the existing `queue_write` API. Step 5b does not change concurrency semantics.

## 7. Cross-Skill Coordination

| Skill | What `/int` consumes | What `/int` produces |
|---|---|---|
| `/backend` | `CACHE_SCHEMA_VERSION` constant; `CacheWritePacket` shape; `process_cache_packet` API; `Linker` API for cache-hit `.o` mapping. `/backend`'s `module-caching.md` is the authoritative envelope spec. | The worker's calling pattern: serialise the symbol table, hand the bytes + schema_version + `.o` request to the cache crate. |
| `/typecheck` | The `SymbolTable<C, L>` shape with `schema_version`, structural-decl fields, and `code: Option<C>` / `platform_fn_ptr` `#[serde(skip)]` fields. `/typecheck` owns `cranelisp-types/src/module.rs` per Decision 33. | Confirmation that round-trip serialise→deserialise reproduces the typecheck invariants the importing workers expect. |
| `/platform` | The `PlatformDecl → DLL re-resolve` mechanism. `/platform`'s `platform-registry-removal.md` already documents the live-build resolve path; cache-hit re-uses it verbatim. | A reference to the addendum confirming cache-hit resolution still works after the symbol table carries `linker: Option<L>`. |

## 8. Sketch Comparison

The sketch's cache shape is documented in `design/backend/module-caching.md` §2 ("Sketch comparison"). In short, the sketch persisted a monolithic `CompiledModule` plus a separate `manifest.json` for invalidation, with no equivalent of structural-decl preservation (it reconstructed import scope from the per-symbol entries on cache-hit, losing the original groupings). The sketch had no schema versioning — version mismatches surfaced as cryptic deserialisation errors after compiler upgrades.

This design diverges from the sketch in three load-bearing ways:

1. **Single-source serialisation**. The sketch had three `.cl`-relevant artefacts (`CompiledModule` JSON, `manifest.json`, `.o`); we have two (`.meta.json` for the symbol table, `.o` for code), with the manifest reduced to a global cache-validity index. The unified `SymbolTable` makes the symbol-table-as-cache-shape decision explicit and removes the sketch's import-scope reconstruction step.
2. **Structural-decl preservation**. Step 5a (Decision 33) puts `imports/exports/platforms/submodules` on the symbol table; the cache writes them directly. The sketch reconstructed import groupings from per-symbol Import entries, lossily — `(import [m [a b c]])` and `(import [m [a]]) (import [m [b]]) (import [m [c]])` produced the same scope but distinguishable original specs are needed for `.cl` regeneration (§6.4).
3. **Explicit schema versioning**. `CACHE_SCHEMA_VERSION` (Decision 34) gives every shape change an unambiguous invalidation path. The sketch relied on compiler-mtime to invalidate after upgrades, which fails when developers `cp -p` binaries or CI restores cached binaries. Versioned schema gives a deterministic path for both cases.

The sketch's "background mpsc cache writer" (one of the things that worked) is preserved verbatim — `cache_writer.rs` keeps its current architecture; only the packet contents change.

## 9. Open Questions

- **`CacheEnvelope { schema_version, table }` wrapper vs `schema_version` as a top-level field on `SymbolTable`**. Both work; the wrapper is cleaner for the cache-hit sniff but adds a JSON-shape difference between in-memory `SymbolTable` and serialised `SymbolTable`. Defer to `/backend`'s `module-caching.md` Wave 1 update — `/int` follows whichever shape lands.
- **Whether `SharedState.kept_linkers` survives Step 5c**. Step 5b's cache-hit code path reads from `kept_linkers` to keep `.o` pages alive. If Step 5c re-routes that retention onto `SymbolTable.linker: Option<L>`, the pool dissolves; if `LinkerStore` retention semantics genuinely differ from `CodeStore` (e.g., one Linker per module vs one Jit per batch), the pool may persist in narrowed form. The `symbol-table-generics.md` doc resolves this.

## 10. Next Skills

- `/backend` — `module-caching.md` Wave 1 update (envelope shape, `CACHE_SCHEMA_VERSION`, refresh sketch-comparison section per Condition 1).
- `/typecheck` — `ast-annotation.md` §11 (structural decls) + §12 (generics shape) confirm the round-trip invariants.
- `/qa` — Wave 5 cache round-trip tests; cache-hit equivalence to fresh build; schema-version mismatch invalidates.
