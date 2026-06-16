---
number: 0387
target: /dev
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 84
refers_to: crates/cranelisp-backend/src/cache/ (the .meta.json writer), src/worker.rs §derive_codegen_batch, tests/*::cache_prelude_modules_cached, design/arch/concrete-boundary-type.md §2.5 (Cache-schemes-without-codegen), §4-B
status: open
---

# Cache `.meta.json` must persist independent of codegen `.o` (generic-only-prelude case, Phase 4B)

## Issue

Phase 4 part B (generic-body-codegen elimination) excludes a slot-less
`Polymorphic` def's body from the `defined_symbols()` codegen batch at both filter
sites. A prelude/stdlib module whose ONLY def is an uninstantiated generic (e.g. a
module exporting only `(defn id [x] x)`) therefore produces **no codegen artifact**
(empty `.o` batch) — yet its SCHEME must still be cached so a downstream module can
monomorphise it on a later cold-load. If the cache writer gates `.meta.json`
(schemes / symbol-table shape — the *typecheck output*) on the presence of a
codegen object (`.o`), the generic-only module's meta is not persisted and
`cache_prelude_modules_cached` regresses.

## Proposed resolution

This is a **cache-layer change**, not "the prelude always has something to emit"
(the empty-`.o` case is real). Decouple `.meta.json` emission from `.o` emission:

- `.meta.json` persistence is driven by the **typecheck result** (the module's
  schemes + `ModuleEntry` shape), independent of whether `compile_to_module`
  produced any object. A module that type-checks but codegens nothing still writes
  its `.meta.json`.
- The `.o` is written iff the module's `defined_symbols()` batch is non-empty (a
  generic-only module's batch is empty → no `.o`, which is correct).
- On cold-load, a `.meta.json`-only module (no `.o`) rehydrates its schemes (its
  generics available as mono *sources*) and emits no code — its post-part-B
  session-init behaviour. The downstream module that reaches a concrete
  instantiation mints + codegens the concrete instance into ITS own `.o`, as it
  already does for every on-demand mono instance.
- `cache_prelude_modules_cached` stays green: the assertion is about schemes/meta
  round-tripping, which still happens; the `.o` absence for a generic-only module
  is the correct new state, not a miss.

Split work: /dev(backend) confirms the cache writer
(`crates/cranelisp-backend/src/cache/`) decouples `.meta.json` from `.o`;
/dev(int) confirms the loader tolerates a `.meta.json`-only module (no `.o` to
mmap). If the current writer *requires* an `.o` to write the meta, that coupling
IS the part-B cache change — remove it.

## Operational implication / Context

- Part of the Phase-4-part-B change-set (`design/arch/concrete-boundary-type.md`
  §4-B); lands with the `Polymorphic`-exclusion filter changes.
- No `cranelisp-types` shape change, no `CACHE_SCHEMA_VERSION` bump — this changes
  *which artifacts are written* for a module, not any serialized shape (the
  `MonoExpr`/`MonoDefnVariant` 6→7 bump already landed in Phase 2a).
- Mandatory unit/integration test: a module exporting only a generic def caches its
  `.meta.json` (schemes round-trip) with no `.o`, and a downstream concrete use
  cold-loads + monomorphises it.
