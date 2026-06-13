---
number: 0220
target: /arch
filed_by: /arch
filed_at: 2026-05-25
sprint_filed: 70
refers_to: src/session_v4.rs §Introspection, src/save.rs, design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md, design/arch/bounded-contexts.md §int, repl/spec.md §15.4
status: open    # RULED by /arch S81 — design settled; left open for the /dev int wave (the lazy re-read + non-macro .cl regen fix)
ruled_at: 2026-06-13
resolves_to: /dev int    # design arbitrated by /arch; residual implementation is int's
recorded_in: design/arch/bounded-contexts.md §6 In-scope (cache-hit introspection rehydration bullet)
---

# Cache-hit source rehydration on demand (REPL-edit + `.cl` regen for cache-loaded modules)

## /arch ruling (S81, 2026-06-13) — design SETTLED; open for the /dev int wave

RULED: **lazy on-demand re-read** — option (a) of the "WHEN to trigger" question below.
NOT eager-at-restore (b), NOT the rejected serialize-into-cache non-fix. Grounded in
D1/D1b (`design/arch/d1-introspection-repl-only.md`; `memory/introspection-repl-only-principle.md`):
introspection is REPL-only and does not exist outside REPL; **any data the compile pipeline
reads must live on the symbol table, not introspection.** Canonical home for this disposition:
**BC §6 In-scope** ("Cache-hit introspection rehydration" bullet). Summary:

1. **No rehydration owed for compile-necessary data — it is already on the symbol table.**
   The load-bearing concern this FIXME raised (on-demand macro-clause recompile + `.cl` regen
   silently dropping cache-loaded macros) is **already resolved by D1**: macro source rides
   `DefKind::Macro.macro_sexp` (serialized, cache-survives) — `worker::resolve_macro_sexp_from`
   reads it; `save::generate_fns_and_macros` uses it as the macro fallback. Every other Def
   kind carries its compile input as `ast: Option<DefnVariant>`. So the "empty regeneration"
   failure no longer applies to macros, and no compiler read depends on introspection on
   cache-hit.

2. **REPL-display data rehydrates LAZILY on first `/source`/`/sexp`/`/expand`/`/clif`/`/disasm`
   (or `.cl` regen) request** for a cache-loaded symbol with an absent record — by re-reading +
   re-parsing the backing `.cl` (the cache key, always present), and regenerating CLIF/disasm
   from the resident GOT-slot code via the existing `produce_disasm` path. Lazy + content-fresh;
   the read-only REPL session pays nothing.

3. **Residual concrete gap (the real implementation work): non-macro `.cl` regeneration.**
   `save::generate_fns_and_macros` sources a `UserFn`'s text from `introspection_sexp` only
   (its `.or(macro_table_sexp)` covers macros, never UserFns) — so a cache-restored regular
   function with no introspection record is dropped from the regenerated `.cl`. Fix: the same
   lazy re-read (re-parse the backing file for the symbol's region) OR reconstruction from the
   entry's `ast`. REPL-only; touches neither the cache nor D1.

4. **Int-side shape:** one int-crate private path (`SharedState::rehydrate_introspection(fq)`):
   FQSymbol → backing-file path (the watcher/loader already maps this) → re-parse → populate
   the REPL `Introspection` entry → return it. No new cross-crate type or trait. `frontend`
   owns the parse; file-IO + populate is int's.

**Disposition: NOT a no-op** (item 3 is a live gap). Left **OPEN** for the /dev int wave; the
design questions below are answered (lazy per-symbol, re-read the backing file; the
`source_range`-in-cache micro-optimisation is OPTIONAL, defer unless profiling motivates it).

---

## Original filing (preserved below)

## Issue

When a module is loaded from the on-disk compile cache, its symbols populate
the in-memory `SymbolTable` (per `cranelisp-types::SymbolTable`'s
Serde-derive) but the integration layer's `Introspection` DashMap on
`SharedState` (defined at `src/session_v4.rs:566`) is NOT rehydrated:

- `Introspection` is `#[derive(Debug, Clone, Default)]` — non-Serde.
- BC §int classifies it under "development tooling: tracing, observability,
  introspection" — REPL-only by design.
- Cache-hit path skips the populate step that the JIT-compile path performs
  via `compile_to_module`'s `introspection: Option<&DashMap<FQSymbol,
  Introspection>>` parameter (Decision 41).

Consequence: for a cache-loaded module's symbols, the integration layer has
no `source`, no `sexp`, no `expanded`, no `clif_ir`, no `disasm`, no
`code_size`. REPL `/source <name>` / `/sexp <name>` / `/expand <name>` /
`/clif <name>` / `/disasm <name>` return absent. More load-bearing: REPL
editing (defn-of-existing-name at the prompt) cannot regenerate the backing
`.cl` file via `save::regenerate_backing_file` (`src/save.rs`) because the
walk reads each symbol's `sexp` from Introspection — empty entries produce
an empty regeneration.

## The non-fix

**Serializing `Introspection` into the cache is NOT the answer.** It:

1. **Mixes concerns.** The compile cache exists to skip recompilation
   (binary code + symbol-table state). Introspection is a separate
   integration-layer development-tooling surface (BC §int) with different
   lifecycle, different audience, and different invalidation rules. Folding
   them confuses both.
2. **Bloats the cache.** `Introspection` carries `source: Option<String>`
   (the full source-text slice for every symbol — possibly multi-KB),
   `clif_ir: Option<String>` (CLIF text, easily 10–100KB per non-trivial
   defn), `disasm: Option<String>` (similar). For a moderate-size module
   the introspection record dwarfs the compiled code.
3. **Raises invalidation questions.** What invalidates a cached
   Introspection entry? Source text becomes stale the moment a user
   touches the `.cl` file via an editor — but the cache hit predicate
   doesn't notice unless content-hashed; `clif_ir` is snapshotted from a
   specific codegen build that may not match the current backend version.

## Proposed resolution direction

**Lazy re-read of the backing source file on demand.** When the integration
layer needs source / sexp for a cache-loaded symbol whose Introspection
record is absent:

1. Find the backing file (`module_path -> filesystem path`; the watcher /
   module loader already knows this mapping).
2. Re-parse the file region that defined the symbol (or the whole file if
   region-mapping is unimplemented at first cut).
3. Populate `Introspection { source: ..., sexp: ..., .. }` on the
   `SharedState` DashMap for the queried symbol.
4. Return the now-present record to the caller.

This is **content fresh at the moment of need**, defers cost until
something actually consults the introspection surface, and avoids cache
bloat. Re-parse is cheap (frontend is the fast crate); compared to
recompiling, it's noise.

## Open design questions

- **WHEN to trigger the re-read.** Options:
  - **On first `/source <name>` / `/sexp <name>` / `.cl` regen request**
    for that symbol. Lazy per-symbol.
  - **On entry to REPL** for the cache-loaded modules. Eager per-module
    (preloads everything; one-time cost at session start).
  - **On first REPL modification of any symbol in a cache-loaded module.**
    Eager per-module, but deferred until the user actually edits — the
    common steady-state read-only REPL session pays nothing.

  The lazy per-symbol option is the cleanest narrative, but per-symbol
  re-parse is wasteful if the file is large and many symbols are queried —
  cache the parsed file in some intermediate. Alternatively, the
  per-modification eager populate avoids the wasteful per-symbol re-reads
  but front-loads cost on the first edit.

- **HOW to map FQSymbol back to file region.** The frontend produces
  `Sexp` with spans, but the span -> file-byte-offset round-trip after a
  cache reload requires either the original source file to be present
  (already true — `.cl` is the cache key) or per-symbol byte-range
  metadata serialized into the cache (a minimal alternative to
  full-Introspection serialization — just `Option<Range<usize>>` per
  symbol pointing into the `.cl`). The latter is small (16 bytes/symbol)
  and gives O(1) symbol-region lookup with no full-file re-parse.

  **Tentative direction**: serialize per-symbol `source_range:
  Option<Range<usize>>` into the cache (cheap; tiny); populate Introspection
  lazily by `&source[range]` slicing + targeted re-parse on the region.
  Defer until the design is decided.

- **WHO owns the re-read trigger.** `SharedState` (the int crate) holds
  the Introspection DashMap; the file-IO call belongs in int.
  `cranelisp-frontend` owns the parse. The new code is one int-crate
  function (e.g. `SharedState::rehydrate_introspection(fq: &FQSymbol)`).
  No new cross-crate type or trait is required — this is pure int-side
  work behind a private path.

## Operational implication

Until this lands, REPL editing of cache-loaded modules is **degraded**:
`/source <name>` returns absent; defn-of-existing-name at the prompt
regenerates an incomplete `.cl` (silently dropping the cache-loaded
symbols whose Introspection is missing). Workaround: drop the cache for a
module before editing it via REPL — the next compile populates
Introspection fresh.

This is architectural debt, not a S70 closure item. It does not justify
restoring D41-violating shadow fields on any `DefKind` variant (the
S70 Phase 3 settlement explicitly excluded that path).

## Skill scope

The design lives in `/arch` (cross-cutting BC §int contract decision: where
the rehydration trigger sits, what shape it takes); the implementation
lives in `/dev (int)`. Filed `target: /arch` so the design question is
arbitrated first; the implementing FIXME on `/dev (int)` follows once
direction is settled.
