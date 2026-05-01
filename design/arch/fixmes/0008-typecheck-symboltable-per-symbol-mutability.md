---
number: 0008
target: /typecheck
filed_by: /arch
filed_at: 2026-04-26
sprint_filed: 63
refers_to: design/arch/facades/types.md §"Symbol table — the single store", design/arch/facades/typecheck.md, design/arch/sequences/concurrency-symbol-table-entry.mmd, design/arch/CLAUDE.md Decisions 38 + 39
status: open
---

# SymbolTable mutation discipline shifts to per-entry; check_form drops `&mut SymbolTable`

## Issue

The current `SymbolTable<C, L>` facade has three `&mut self` methods:

- `write_structural_decls(&mut self, decls: StructuralDecls)` — appends to `imports: Vec<ImportSpec>` etc. (Decision 33 fields)
- `install_import_bindings(&mut self, from: &ModuleFullPath, names: ImportNames)` — installs Import-variant entries for bare-name resolution
- `check_form(ast, &mut SymbolTable, &SymbolTables) -> Result` — typecheck consumes `&mut SymbolTable` (per `facades/int.md` `process_form` line 412–413)

This forces the integration layer to hold `Sess.symbol_tables.entry(m1).or_default()` (a DashMap entry write lock — RefMut) **across the entire `check_form` call**. The hold has two unwanted effects:

1. **Cross-module read contention.** A second worker reading m1 via `Sess.symbol_tables.get(&m1)` blocks behind the RefMut shard write lock, even though it only wants shared access to ALREADY-typechecked entries. Cross-shard collisions (m3 hashing to m1's shard) inherit the same block.

2. **Per-symbol gap mechanism unsound.** A waker on `wait_for_typecheck_symbol(m2/bar)` would resume immediately to find PWb still holding m2's RefMut for the next form, gap again, livelock. The session restructure audit (`design/arch/sequences/concurrency-symbol-table-entry.mmd`) showed this — the only mechanically-sound wait under whole-module RefMut would be module-grained (`wait_for_typecheck_module`), losing the per-symbol granularity Decision 30 + the per-symbol gap kinds (`SymbolTypechecked(FQSymbol)`, `MacroInMem(FQSymbol)`) currently provide.

## Proposed resolution

Shift `SymbolTable` mutation to **per-entry locks via the inner `symbols: DashMap<Symbol, ModuleEntry<C>>`**:

1. **`write_structural_decls(&mut self, decls: StructuralDecls)` — keep `&mut self`.**
   - Called ONCE per module at parse-time (Phase 0 in the diagram), with the full StructuralDecls assembled from the parser's structural-decl extraction pass.
   - The integration layer acquires `Sess.symbol_tables.entry(m).or_default()` only across this call, then drops the RefMut. No further `&mut SymbolTable` access happens.

2. **`install_import_bindings(&self, from: &ModuleFullPath, names: ImportNames)` — change to `&self`.**
   - Writes `ModuleEntry::Import { … }` entries into `self.symbols` via the inner DashMap's interior mutability (per-entry write locks). No outer `&mut` needed.

3. **`check_form(ast, &SymbolTable, &SymbolTables) -> Result<…>` — change to `&SymbolTable`.**
   - Reads from own module via shared access; writes via `self.insert_or_update(sym, entry)` (already `&self`).
   - Cross-module reads via `&SymbolTables` (`.get(&other)` shared shard ref); per-entry contention with concurrent insert is microsecond-scale and acceptable.

4. **Add `defn_order: Vec<Symbol>` field on `SymbolTable` (per Decision 39).**
   - Phase-0-mutable: seeded by `write_structural_decls` from the parser's declaration-order list of defn names.
   - Per-eval REPL append via `append_defn_order(&mut self, sym: Symbol)` — brief `&mut SymbolTable` window on the initiator thread. Used by `regenerate_backing_file` to walk defns in canonical source order.
   - See `facades/types.md` §"Symbol table — the single store" for the field declaration.

After (1)–(4), all access to `SymbolTable` is `&SymbolTable` + per-entry inner DashMap locks for typecheck/codegen-time mutation. The integration layer's per-form RefMut hold goes away, replaced by `Sess.shared.symbol_tables.get(&m1)` shared shard ref. The only `&mut SymbolTable` operations remain the initiator-thread Phase 0 setup and per-REPL-eval `defn_order` append.

## Operational implication

- **Per-symbol gap mechanism becomes mechanically sound.** `Gap(SymbolTypechecked(m2/bar))` → `wait_for_typecheck_symbol(&m2/bar)` → wake on `notify_symbol_typechecked` → retry succeeds without contending on a whole-module write lock. Decision 30's per-symbol gap kinds keep their current shape; no new `ModuleTypechecked` gap kind needed.

- **Decision 30 single-worker-per-module becomes ORDERING-only, not lock-safety.** Per-entry locks make multi-worker mutation of one SymbolTable safe in principle. The single-worker invariant remains as scheduler ordering (avoid dispatch races, simplify form-by-form sequencing) but is no longer a correctness requirement of the lock discipline.

- **REPL redefinition carry-forward (Decision 31) unaffected.** `insert_or_update` reads the existing `code: Option<C>` field under the per-entry write lock and clones it forward into the new entry; the GOT swap and old-`Arc<Jit>` drop sequencing happens identically inside `write_code`.

- **Cache schema (Decision 34) requires a bump.** Adding `defn_order: Vec<Symbol>` changes the serialised shape of `SymbolTable`. The current `CACHE_SCHEMA_VERSION = 1` (per Decision 34) must increment to `2` when this lands. Old caches will be rejected as version-mismatch on load (the same path that fires on source mtime / dependency hash change).

## Context

Surfaced during S63 W2 sequence-diagram authoring of `design/arch/sequences/concurrency-symbol-table-entry.mmd`. Earlier drafts of that diagram tried to retain the `&mut SymbolTable` shape under various wait/contention strategies — including a non-blocking-`try_get`-with-`ModuleTypechecked`-gap design. User direction (S63 W2 review) selected per-symbol mutability instead, motivating this FIXME.

**Now formally specified by Decisions 38 + 39** (filed in `design/arch/CLAUDE.md` Sprint 63 alongside this FIXME revision). The decisions pin: (a) `SharedState` formal definition with field-level inventory of where workers reach what; (b) per-symbol mutability discipline as the architectural commitment; (c) `Introspection` placement (Option-discriminated mode store on `SharedState`); (d) per-defn source on `Introspection.source` with `defn_order: Vec<Symbol>` on `SymbolTable` for canonical regeneration order; (e) errors carry `ErrorLocation` with permissive coordinate data + downstream formatting policy. This FIXME is the `/typecheck` slice of those decisions.

Pairs with FIXME 0009 (the integration-layer counterpart — `register_module` Phase 0 split + `process_form` shifting from `entry().or_default()` to `get()` + `regenerate_backing_file` via `defn_order` + introspection).
