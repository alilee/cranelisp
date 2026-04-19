# Symbol-Table Cache (Step 5b)

<!-- Sprint 58 Wave 2c (/int): FIXME resolved — §3.1 row and §3.2 narrative
     rewritten in line with Decisions 36 + 37; §"Investigation findings"
     subsections reframed (Bug A dissolved by /backend's bare-Local change,
     Bug B fixed by /backend's `define_module_got_data`, /int's residual
     work is the recursive transitive cache-hit walk in `try_cache_hit_load`
     and the `_main` Export alias `.o` for `--link`). -->

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
| Cache-hit code load trigger | After deserialising, the cache-hit codegen worker for module `M` loads `.o` via `cache::Linker::load_object`, looks up function addresses by **bare** symbol-table-key name (Decision 36 — every function is `Linkage::Local` with bare name uniformly), and writes them into `symbol_tables[M].got` slots whose layout is already pinned in `symbol_tables[M].symbols[s].got_slot`. **Codegen does not re-run on cache-hit** — the cached `.o` IS the regenerated output. | Decision 25 (Sprint 58 Wave 2 rewrite — cache stores both `.meta.json` and `.o`; cache-hit LOADS the `.o`, does not re-codegen) + Decision 36 (bare-Local lookup is uniformly correct — no `user`/`main` special case). |
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

### 3.2 Cache-hit decision lives inside `register_module`'s recursive flow (Decision 37)

**Decision 37 (Sprint 58 Wave 2):** Cache-hit decision and load are NOT a parallel orchestration codepath; they live INSIDE the normal recursive register-then-recurse-on-imports flow that `handle_import` / `handle_export` / `handle_mod` / prelude injection use to discover dependencies. The pre-Sprint-58 framing — where `try_cache_hit_load` re-implemented dependency discovery, ordering, and GOT setup as a parallel path with its own bespoke orchestration — is dissolved at Wave 2c.

The canonical recursive flow is:

```
register_module(M):
  1. If <cache_dir>/M.meta.json exists and schema_version matches:
       deserialise → install SymbolTable for M → mark typecheck-complete
     Else:
       read source → parse → register with scheduler for fresh typecheck
  2. For each user-authored import in SymbolTable[M].imports:
       register_module(import.module)   # recursive; both branches above are
                                        # eligible per dep, so a project can
                                        # mix cached + fresh modules in any
                                        # combination
  3. (For platform decls on M: re-resolve via load_and_register_platform.)
```

After typecheck phase completes for ALL reachable modules — whether each module landed via fresh-typecheck or cache-deserialise — codegen phase runs. **Cache-hit codegen workers for cache-hit modules run in any order, in parallel** (no topo-sort needed at codegen time):

```
codegen_worker(M):
  Same body whether fresh or cache-hit:
    register_symbol("__cranelisp_got_M", &symbol_tables[M].got.base_ptr())
  Branch on origin:
    Fresh-build: compile_to_module<JITModule>(M, defined_symbols(M),
                                              &symbol_tables, jit)
                 → on each defined symbol: write got_slot = jit.get_finalized_ptr(...)
    Cache-hit: linker.load_object(read(<cache_dir>/M.o))
               → for each defined symbol s in symbol_tables[M]:
                   ptr = linker.get_symbol(bare_name(s))   # Decision 36
                   if ptr.is_none(): error                  # no swallowed failures
                   symbol_tables[M].got.store_slot(symbol_tables[M].symbols[s].got_slot, ptr)
```

**Order-independence rationale.** The typecheck phase establishes GOT slot LAYOUT — slot indices are pinned in `SymbolTable.symbols[s].got_slot` for every defined symbol, before any codegen worker runs. Codegen workers fill slot CONTENTS (the function pointer at each slot). Order across modules is irrelevant because no codegen worker reads another module's GOT contents — the cross-module call mechanism (CLIF `global_value` against `__cranelisp_got_{other_M}`) reads at runtime, not at codegen time. Each module's codegen is therefore a self-contained operation on its own SymbolTable + its own JIT (or its own loaded `.o`) + its own GOT slots.

**Implementation in `src/worker.rs`** (Sprint 58 Wave 2c): `try_cache_hit_load` retains its name and call sites (one in `handle_import`, one in `handle_export`, one in `handle_mod`, one in prelude injection — symmetric with the fresh-build path within each handler), but is extended with a transitive recursion step (`register_transitive_cached_imports`) that walks `cached.symbol_table.imports` and recursively cache-loads or scheduler-registers each transitive dep. This is the recursive `register_module(M)` shape Decision 37 mandates, expressed via the existing handler structure. The codegen worker (`load_cached_module_via_linker`) remains the cache-hit codegen body and now errors out (rather than silently producing `inmem_done` with empty GOT slots) when any expected bare-name symbol fails to resolve — see §"No swallowed failures" in Decision 37 + the Wave 2c implementation in `src/worker.rs::load_cached_module_via_linker`.

**No swallowed failures.** The pre-Sprint-58 `worker.rs:2810-2823` pattern unconditionally pushed each cached symbol onto `loaded_symbols` regardless of whether the GOT slot population succeeded — when `linker.get_symbol(name)` returned `None` (Bug A: wrong symbol name was being looked up), the slot stayed NULL but the worker reported success. The Wave 2c fix surfaces a `CacheLoadError` when any expected symbol fails to resolve. Per Decision 31's safety invariant ("a slot that resolves to NULL is reachable from the code path that calls it"), silently producing an `inmem_done` state with empty GOT slots is a contract violation.

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

- **`CacheEnvelope { schema_version, table }` wrapper vs `schema_version` as a top-level field on `SymbolTable`**. Resolved (Sprint 58 Wave 2b): top-level field on `SymbolTable`. `/backend` shipped `serialise_meta(&table, schema_version)` / `load_meta(&path)` with `schema_version` as a stamped field on the cloned table, no envelope wrapper. `/int` calls `cache::write_meta(&meta_path, &symbol_table, cache::CACHE_SCHEMA_VERSION)` from `compile_module_object` (`src/session_v4.rs`). One JSON shape, both write and read.
- **Implicit-prelude `ImportSpec` placement on `SymbolTable.imports` (CP3 from Phase 3a)**. Resolved (Sprint 58 Wave 2b): **option (b) — keep `imports` user-authored**. The implicit `(import [prelude [*]])` synthesised by `inject_prelude_if_needed` (`src/worker.rs:~1973`) is NOT recorded on `SymbolTable.imports`; only `(import …)` forms that appeared lexically in the user's `.cl` source are recorded there. Rationale: (a) `.cl` regeneration (`src/save.rs::generate_imports`) emits user-authored forms only — the implicit prelude is suppressed by both the user-authored discipline AND a belt-and-braces filter at line 142, matching the round-trip invariant; (b) the per-symbol `ModuleEntry::Import` chain still carries the resolved effects of the implicit prelude, so type-resolution and cross-module references work identically; (c) symmetry with `submodules` is not load-bearing here — `submodules` records the parent's own `(mod-)` decl which IS source-of-truth for the privacy check, but `imports` is consumed by the regenerator and the duplicate-warning code, both of which reason about user intent. Documented in `src/worker.rs::record_imports_on_symbol_table` and the unit test `writer_does_not_record_implicit_prelude_in_imports` enforces it as an invariant.
- **Whether `SharedState.kept_linkers` survives Step 5c**. Step 5b's cache-hit code path reads from `kept_linkers` to keep `.o` pages alive. If Step 5c re-routes that retention onto `SymbolTable.linker: Option<L>`, the pool dissolves; if `LinkerStore` retention semantics genuinely differ from `CodeStore` (e.g., one Linker per module vs one Jit per batch), the pool may persist in narrowed form. The `symbol-table-generics.md` doc resolves this.

## 10. Next Skills

- `/backend` — `module-caching.md` Wave 1 update (envelope shape, `CACHE_SCHEMA_VERSION`, refresh sketch-comparison section per Condition 1).
- `/typecheck` — `ast-annotation.md` §11 (structural decls) + §12 (generics shape) confirm the round-trip invariants.
- `/qa` — Wave 5 cache round-trip tests; cache-hit equivalence to fresh build; schema-version mismatch invalidates.

## Investigation findings (Sprint 58 Wave 2c — `/int`)

`/qa` filed five FIXMEs for cache-hit / cross-module GOT failures. Three were traced deeply (`v4_cache_hit_dependency`, `link_multi_module_project`, the multi-module SIGSEGV cluster). Two distinct bugs explain all twelve failing tests; both are implementation-level (Wave 2 fixable) and predate Sprint 58.

### Bug A — DISSOLVED (Sprint 58 Wave 2 — Decision 36)

The original framing of Bug A pointed at `cache::load_cached_object` looking up bare symbol-table keys against a linker that indexed `module/name`-qualified symbols (the pre-Sprint-58 `compile_to_module` behaviour for non-`user`/non-`main` modules).

Per **Decision 36** (`design/arch/CLAUDE.md`, Sprint 58 Wave 2), `compile_to_module` now declares every user-defined function with its bare symbol-table name and `Linkage::Local`, **uniformly across all modules**. The pre-Sprint-58 user/main vs FQ-Export discriminator was a defect, not a feature, and is deleted. With bare-Local naming uniformly, `linker.get_symbol(bare_name)` succeeds for every module's defined functions — Bug A's mismatch is structurally impossible. The originally proposed fix shape ("(a) compose `format!('{module}/{name}')` for non-`user`/non-`main` modules") is obsolete: bare lookup is the correct form uniformly, made consistent by the backend's Decision-36 change.

The secondary "swallowed failure" issue (loaded_symbols pushed even when ptr is None, worker.rs:2822) survived this dissolution as a separate hygiene fix. Sprint 58 Wave 2c (`/int`) errors out when any expected symbol fails to resolve, in `load_cached_module_via_linker`. Decision 31's safety invariant ("a slot that resolves to NULL is reachable from the code path that calls it") makes this a hard error rather than a swallowed warning — see §3.2 above.

### Bug B — FIXED (Sprint 58 Wave 2 — Decision 23 + new `define_module_got_data` trait method)

`/backend` Wave 2 added a new trait method `CodeFinalizer::define_module_got_data(name, slot_count, slot_funcs)` and made `compile_to_module` call it after function declarations. For `JITModule` it is a no-op (the JIT-mode definition lives outside `compile_to_module` via `Jit::define_got_data` pointing at the runtime `SymbolTable.got.base_ptr()`); for `ObjectModule` it declares the per-module `__cranelisp_got_{M}` as `Linkage::Export` with `slot_count * 8` bytes and writes a function-address relocation initializer at byte offset `slot * 8` for each defined function. The system linker (`--link` mode) and the cache `Linker` (`--run` mode after cache-hit) materialise the relocations into actual function addresses at load time. See `crates/cranelisp-backend/src/lib.rs::CodeFinalizer` impls and `/arch` Decision 23 (two-GOT model + Bug B fix) + `compile-to-module.md` §5.4.

The transitive-loading concern (`load_cached_module_via_linker(main.mid)` happens before `main.mid.leaf`'s symbol table is installed) is Wave 2c residual `/int` work and is solved by the recursive transitive walk in `try_cache_hit_load` — see §3.2 above and `register_transitive_cached_imports` in `src/worker.rs`. With the recursion, every cache-hit module ensures its transitive deps' symbol tables (and hence their `__cranelisp_got_M` GOT base addresses) are installed before its own codegen worker runs.

<!-- FIXME(/backend) Sprint 58 Wave 2c (filed by /int).
     `define_module_got_data` for `ObjectModule` (in
     `crates/cranelisp-backend/src/lib.rs:200-260`) uses
     `desc.define_zeroinit(slot_count * 8)` followed by
     `desc.write_function_addr(offset, func_ref)`. Cranelift composes these
     as a `__DATA,__bss` section (Mach-O `S_ZEROFILL`) carrying relocations.
     macOS `ld` segfaults on `.o` files containing relocations in a
     `S_ZEROFILL` section because BSS has no file content for the linker
     to patch (verified via `nm` / `otool -lv` / direct `ld` invocation
     reproducing exit 139 with empty stderr).

     Symptom: every `link_*` test in `tests/sprint23.rs`
     (link_main_returns_int_exit_code, link_hello_world_produces_executable,
     link_default_output_is_entry_stem, link_reuses_cached_object_files,
     link_multi_module_project) reports "linker failed:" with no further
     output — that is `ld` segfaulting silently.

     Fix shape: replace
       `desc.define_zeroinit(slot_count * 8)`
     with
       `desc.define(vec![0u8; slot_count * 8].into_boxed_slice())`
     so the data lands in `__DATA,__data` (where `ld` can patch the
     relocations) instead of `__DATA,__bss`. The data content is identical
     (zeros pre-relocation); only the section affinity changes.

     Independent: `cache_multi_module_transitive_imports` fails with
     "unexpected GOT-load relocation for '__cranelisp_got_main_mid_leaf'".
     The cache `Linker` (`crates/cranelisp-backend/src/cache/linker.rs:228-243`)
     rejects `ARM64_RELOC_GOT_LOAD_*` relocations. Cranelift emits these for
     `Linkage::Import` data references (cross-module GOT-base lookup).
     Either the cache linker needs to handle GOT_LOAD (resolve to absolute
     address, patch the load instruction) or `compile_to_module` needs a
     different mechanism for cross-module GOT-base references that doesn't
     use Import data linkage. Both options are `/backend`-side decisions. -->

### `--link` `_main` entry-point alias mechanism (Decision 36 exception, Sprint 58 Wave 2c — `/int`)

Per **Decision 36** (`design/arch/CLAUDE.md` §"`--link` entry point exception"), every user-defined function — including the entry module's `main` — is declared `Linkage::Local` by `compile_to_module`. The system linker (`ld`) requires `_main` (or whatever the startup stub references) as a globally-visible symbol. The exception is satisfied by an explicit `Linkage::Export` alias of `main` → main module's `main` function address, **emitted by the `--link` layer (`/int`-owned)**.

Wave 2c implementation (`src/exe.rs::generate_main_alias_object`, called from `src/session_v4.rs::link_by_name`):

1. `link_by_name` reads the entry module's symbol table to find `main`'s GOT slot index (`crate::exe::entry_main_got_slot`).
2. `generate_main_alias_object(entry_module, main_got_slot)` emits a small `.o` via Cranelift `ObjectModule` containing one Export function `main` whose body is:
   ```
   load __cranelisp_got_{entry_module}[main_got_slot * 8]
   call_indirect (loaded_ptr) -> i64
   ```
3. The alias `.o` is appended to the system linker's `.o` list. The startup stub still imports `main` (now bare per Decision 36); the system linker resolves the import against the alias `.o`'s Export `main`. The alias's GOT-load reaches the runtime function pointer through `__cranelisp_got_{entry_module}` (which is `Linkage::Export` in the entry module's `.o` per Bug B fix above).

This isolates the `--link` mode's `_main` requirement to one helper in `/int`'s domain. `compile_to_module` keeps its bare-Local discipline; backend signatures remain `<C, L>`-blind; the alias mechanism is a `--link`-only concern that does not pollute the `--run` / REPL paths.

### Are the bugs related?

The original framing — both bugs stemmed from the JIT-vs-Object split in how GOT identity (data symbol) and GOT contents (function pointers) are bridged across the cache boundary — is correct historically. The Sprint 58 Wave 2 architectural reframing closes the seam:
- Bug A: dissolved by Decision 36 (bare-Local naming uniformly — no Object-path mismatch to compensate for in the cache loader).
- Bug B: fixed by the `CodeFinalizer::define_module_got_data` trait method (Decision 23 implementation), which gives both `Module` impls (`JITModule` and `ObjectModule`) a place to define the `__cranelisp_got_{M}` data symbol with the appropriate semantics.

### Implementation-level vs architectural

Both bugs were implementation-level. Both ship as part of Wave 2:

- Bug A is dissolved by Decision 36's bare-Local change in `compile_to_module`. The defensive error in `load_cached_module_via_linker` (Wave 2c — `/int`) is the hygiene addition that prevents future similar bugs (Decision 31 safety invariant).
- Bug B is fixed by the new `CodeFinalizer::define_module_got_data` trait method called from `compile_to_module` (Wave 2 — `/backend`).
- Wave 2c residual `/int` work: (a) recursive transitive walk in `try_cache_hit_load` so cache-hit deps of cache-hit modules are installed in time for codegen; (b) the `_main` Export alias `.o` for `--link` (Decision 36 exception); (c) the swallowed-failure guard in `load_cached_module_via_linker`.

Step 5c (Code enum + generics) tightens the abstraction so the bug class can't recur, but is NOT the prerequisite — Wave 2 lands the targeted fixes inside the existing data model.

### Test cluster mapping

| FIXME | Tests | Root cause | Wave 2 status |
|---|---|---|---|
| #1 (cache.rs block — 9-10 SIGSEGV tests) | `cache_multi_module_*`, `cache_repl_*`, `cache_quick_build_links_cached_objects`, `cache_round_trip_multi_module_observable_equivalence` | Bug A (dissolved by Decision 36) + transitive-load ordering for one case | Bug A: `/backend` Wave 2 (Decision 36). Transitive walk: `/int` Wave 2c (`register_transitive_cached_imports`). |
| #2 (`cache_repl_loads_on_startup`) | prelude rebinding | Bug A (`prelude/+` vs bare `+`) | Bug A: `/backend` Wave 2. |
| #3 (`link_multi_module_project`) | `--link` system-linker error | Bug B + `_main` alias (Decision 36 exception) | Bug B: `/backend` Wave 2 (`define_module_got_data`). Alias: `/int` Wave 2c (`generate_main_alias_object`). |
| #4 (`persist_import_survives_restart`) | session-2 helper missing | Bug A (helper.cl regenerated, then cached-load fails) | Bug A: `/backend` Wave 2. |
| #5 (`v4_cache_hit_dependency`) | second `--run` SIGSEGV | Bug A | Bug A: `/backend` Wave 2. |

