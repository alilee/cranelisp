# Module Caching

The backend's module-cache contract: what makes a cached module valid, what the
persisted pair holds, how the object is emitted and loaded, and which points
remain open. Owned by `design` (backend).

**Status (verified against source 2026-09-24).** Sections 3–14 describe the
cache as built. The dependency record (§3) is realised by int; its known gaps
are in [dependency record and validity](../int/int.md#76-dependency-record-and-validity).

Current realisation lives in source. This document states the design and its
reasons, and it links to other owners rather than copying their facts.

## 1. Purpose and goals

Compiling a project runs every module through the whole pipeline on every
invocation. The cache persists each module's compiled products so an unchanged
module skips parsing, expansion, typechecking and code generation. **The module
is the caching unit**: each module caches independently of when other modules
are written.

Goals, in priority order:

1. **Correctness.** A cache hit is observationally identical to a fresh compile
   of the same sources (§8).
2. **Invalidation safety.** A stale entry is never served. When in doubt, the
   module recompiles, and there is no partial hit (§6).
3. **One pipeline.** Cache hit and cache miss share the ordinary registration
   and codegen path, with no parallel cache orchestration (Principle 11).
4. **Every mode.** `--run` and the REPL restore objects in process; `--link`
   links the same objects with the system linker (§11).
5. **Responsiveness.** Cache writes stay off the interactive path (§7).

Non-goals:

- sharing a cache across machines or build environments;
- incremental compilation within a module;
- release-mode objects, since the future optimising backend recompiles from
  source;
- trusting hand-edited or corrupted cache content beyond the persisted-index
  validation of §14.7. The user declined broader hardening
  ([dependency record and validity](../int/int.md#76-dependency-record-and-validity)).

## 2. Where the cache contract lives

| Question | Canonical home |
|---|---|
| Cache-hit flow, restoration parity, writer scheduling, dependency-record construction and the current-hash lookup | [integration cache design](../int/int.md#7-cache--linker-orchestration-decisions-34-37) |
| Symbol-table shape, slot authority and lifecycle legality of a decoded table | [slot and cache authority](../arch/interfaces.md#slot-and-cache-authority), [symbol-table lifecycle](../arch/symbol-table-lifecycle.md) |
| Cache interior invariants and the persisted-index census | module rustdoc in `crates/cranelisp-backend/src/cache/mod.rs` and `crates/cranelisp-backend/src/cache/serialize.rs` |
| The emitted GOT shape and its two resolvers | [per-module GOT](per-module-got.md), [compile to module](compile-to-module.md) |
| Standalone executables from cached objects | [executable generation](executable-generation.md) |
| Cache placement in the backend context | [BC 3](../arch/bounded-contexts.md#3-backend-cratescranelisp-backend) |
| This document | Validity keys, invalidation, the persisted pair, object emission and loading rules, and open points |

## 3. Cache Key Design

A module's cache entry is valid when every input that affects its compiled
output is unchanged.

### Primary key: content hash

- The primary key is the SHA-256 of the module's source text (`hash_source`).
- Content hashing makes the check independent of modification times, and an
  empty presented hash never matches a recorded one.

### Secondary key: transitive dependency hashes

- **The record is the closure.** Each manifest entry maps every module in its
  transitive dependency closure to the source hash it was compiled against. The
  owner of the closure's edge set, the hash provenance and the builder every
  writer uses is [dependency record and validity](../int/int.md#76-dependency-record-and-validity).
- **Why not direct imports.** An importer's sidecar and object embed slot
  indices, layouts, expanded macros, instances compiled from generic bodies and
  inferred types. A change can reach the importer through an unchanged
  intermediate module, so direct-import hashes would miss it.
- **What the backend check compares.** `check_manifest` compares exactly the
  current-hash map its caller supplies. A supplied member that is missing from
  the record, or whose hash differs, is a miss. The check does not walk the
  record itself, so the caller must build the map from the record's keys.
  Int's validity query builds that map from a current-hash source, so no
  int caller can run the comparison over nothing.
- **Conservative.** Members are keyed by whole source, so a private edit in a
  dependency still invalidates its importers. Interface hashing is §12.

Gaps in what the record covers, including a dependency reached only through a
qualified reference, are recorded in int's
[dependency record and validity](../int/int.md#76-dependency-record-and-validity).

### Global invalidation keys

`check_manifest` compares these before any per-module lookup. A mismatch is a
`CacheInvalidReason`, and the whole manifest is discarded.

| Key | What it detects |
|---|---|
| `cache_format_version` | Manifest or sidecar format change. Its value is currently `CACHE_SCHEMA_VERSION`, so a schema bump also discards the manifest. |
| `compiler_mtime` | A rebuilt compiler: the running binary's modification-time fingerprint, memoised per process. The comparison is skipped when either side is empty (§12). |
| `target_triple` | Architecture or operating system, matched exactly. |
| `cranelift_version` | A Cranelift upgrade that may change object output. |
| `ownership_disabled` | The ownership-analysis toggle polarity. Mixing polarities would mix calling conventions ([toggle as invalidation key](ownership-codegen.md) §2.3). `read_manifest` also refuses a manifest written under the other polarity. |

## 4. Serialization Format

Each module persists one pair beside the project manifest:

- **`.meta.json`** is the module's serialised `SymbolTable<(), ()>`, stamped with
  the schema version and the build identity. Runtime-only state is not
  serialised (§14.1).
- **`.o`** is the relocatable object produced by the ordinary emission path
  against a Cranelift object module (§13).

Sidecars are JSON because they are small, inspectable and diffable. The object
file is the performance-critical artefact. If sidecar decoding ever measures as
a bottleneck, a binary encoding is a change local to `serialise_meta` and
`deserialise_meta`, and it takes a schema bump.

## 5. ObjectModule vs JITModule

- **Dual compilation is deliberate.** A fresh build JIT-compiles for immediate
  execution. The same targets compile again against an object module for the
  `.o`, off the interactive path.
- **Why not serialise JIT memory.** JIT code embeds process-specific absolute
  addresses. Relocatable objects are required to load at a different address in
  a later session.
- **Why not object-only.** Routing every REPL evaluation through object
  emission and the in-process linker would add linking latency to interactive
  input.
- **One emission path.** Both compilations call `compile_to_module`. The mode is
  the Cranelift module the caller supplies, and the only emitted difference is
  the resolver behind the module's GOT data symbol ([per-module GOT](per-module-got.md) §2).
- **One ISA constructor.** `build_isa(is_pic)` is the single construction
  point: position-independent for objects, absolute for the JIT.

## 6. Cache Invalidation Strategy

### When to invalidate

| Trigger | Scope | Detection |
|---|---|---|
| Source file changed | That module | Source-hash mismatch in its manifest entry |
| Dependency changed | Every module whose closure includes it | Dependency record (§3) |
| Compiler rebuilt | All modules | Compiler fingerprint in the manifest; build identity in each sidecar |
| Schema or format version bumped | All modules | `cache_format_version` in the manifest; `schema_version` in each sidecar |
| Target architecture changed | All modules | `target_triple` |
| Cranelift version changed | All modules | `cranelift_version` |
| Ownership toggle flipped | All modules | `ownership_disabled` |
| Sidecar unreadable, malformed or failing validation | That module | `CacheStale` (§14.7) |

### When NOT to invalidate

- A `.cl` file touched without a content change.
- An unrelated module changed, where the module is outside the changed module's
  closure.
- A cache directory copied within the same build environment. Entries are keyed
  by content and build identity, not by location.

### Invalidation is conservative

Any failed check recompiles the module. There is no partial hit: either the
sidecar and, where the module has codegen targets, its object are both
accepted, or the module compiles from scratch.

## 7. Background Writing

- **Int owns scheduling.** The nice worker writes a module's sidecar, then its
  object, then records its manifest entry, all off the interactive path. The
  index worker writes sidecars without objects ([index-worker isolation](../int/index-worker-isolation.md) §3). Every writer records its manifest entry through int's one
  dependency-record builder, which defers an entry until its record settles
  ([dependency record and validity](../int/int.md#76-dependency-record-and-validity)).
- **Backend supplies the pieces.**
  - `write_meta` serialises the table with the schema version and build
    identity, then writes it atomically.
  - `compile_to_module` runs against an object module, and the caller
    finalises it into bytes.
  - `build_isa(true)` builds the position-independent ISA.
  - `write_manifest` writes the index atomically.
  - The backend's writers go through a temporary file and a rename, so a
    concurrent reader never sees a partial sidecar or manifest.
- **Int writes the object.** The nice worker writes the emitted `.o` bytes with
  a plain file write, not the backend's atomic helper. It records the manifest
  entry only after that write succeeds.
- **Open: the packet API has no live consumer.** `build_cache_packet`,
  `process_cache_packet`, `CacheWritePacket`, `ObjectCompileInput` and
  `ProcessedPacket` are public, but no live production path calls them. Their
  only int caller, `src/cache_writer.rs`, is marked dormant and passes an empty
  symbol-table map. Keeping, wiring or removing them is an inter-crate
  public-API decision for `arch` and the user.

## 8. Pipeline Integration Points

**Cache hit equivalence.** A restored module must yield the runtime state a
fresh compile yields: the same symbol table, the same populated GOT slots, and
the same installed scope and relationships. Int realises this by making each
restore step the same call the fresh path makes
([restoration parity](../int/int.md#75-restoration-parity)). The backend's share is that
the sidecar round-trips every serialised field (§14.6), and that the object
comes from the same emission the JIT runs (§5).

- **The hit decision is inside registration.** The cache-hit branch lives in
  int's recursive dependency registration, and restored and fresh modules mix
  in any combination ([cache-hit flow](../int/int.md#71-cache-hit-flow-inside-register_module)).
- **`try_load_cached_module`** reads and validates the sidecar.
  - Any `CacheStale`, or a table whose recorded path differs from the requested
    module, is an ordinary miss: `Ok(None)`.
  - It reports `has_object` only when a non-empty `.o` exists beside the sidecar.
  - It never returns a table that failed a check.
- **`CachedModule::imported_modules`** lists the modules a restored table
  imports from, excluding the compiler-owned `primitives` and `macros` modules.
- **`load_cached_object`** maps the `.o` into a `Linker` and returns one address
  per semantic `CallableTarget`.
  - The emitted label spelling stays private to the backend.
  - The caller must first register every external symbol the object
    references.
  - A target the object does not define is absent from the returned map. Int
    turns that absence into a hard load error, because a published NULL slot
    would be reachable from its callers.

## 9. Crate Ownership

| Component | Owner | Reason |
|---|---|---|
| Manifest, source hashing, global keys, `check_manifest` | backend (`cache::manifest`) | Validity is a property of the compiled artefact |
| Sidecar encode and decode, `CacheStale`, persisted-index validation | backend (`cache::serialize`) | The decoder is the trust boundary for disk content |
| Object emission, ISA construction | backend (`compile_to_module`, `cache::object`) | Cranelift-dependent |
| `Linker` | backend (`cache::linker`) | Relocation formats and executable mappings |
| Cache paths, `CACHE_SCHEMA_VERSION`, `BUILD_ID` | backend (`cache`) | One home for the persisted format |
| Symbol-table shape and lifecycle validation; GOT data-symbol naming | types | Shared by every producer and consumer |
| When to write, the dependency record, cache directory, restore flow, `Code::Linker` publication | int | Orchestration, session state and project-root discovery |

### Why the Linker lives in backend

The linker resolves relocations against in-memory addresses and owns the
executable mappings. That is Cranelift-adjacent knowledge, which the types
crate may not name (Principle 3). Its callers register symbols and read
addresses; they never see relocation types.

### Why scheduling lives in int

Deciding when to write, and coordinating writes with sessions and shutdown, is
pipeline orchestration ([BC 6](../arch/bounded-contexts.md#6-binary--int--src--cratescranelisp-exe-bundle)).
The backend exposes functions and holds no cadence.

## 10. Edge Cases

### Cross-module dependencies

- If a dependency of `A` changed, the closure record invalidates `A` too (§3).
- The record does not yet cover a dependency reached only through a
  qualified reference, or the other known gaps int records
  ([dependency record and validity](../int/int.md#76-dependency-record-and-validity)).
- A private implementation change in a dependency still invalidates importers
  (§3, §12).

### Prelude caching

- The prelude caches like any other module.
- A module whose prelude fallback is set records the prelude in its closure, so
  a prelude change invalidates those modules (§3). A module cached while no
  prelude resolved records none; adding a prelude later is an int known gap.
- The compiler-owned `primitives` and `macros` modules are never cached. They
  are process-static and covered by the build identity and compiler
  fingerprint.

### Cache directory layout

- Every module cache, including the standard library's, lives in
  `{project_root}/.cranelisp-cache/` beside `manifest.json`. Only modules a
  project actually loads are cached, and nothing is written to a possibly
  read-only library location. The project-root rule is int's
  ([REPL lifecycle](../int/repl-lifecycle.md)).
- `module_cache_path` mirrors the module hierarchy. `core.numerics` maps to
  `core/numerics.meta.json` and `core/numerics.o`, `user` maps to `user.*`, and
  the entry module maps to `_entry.*`.

### Modules without an object

- A module with no codegen targets writes a sidecar and no `.o`. Examples
  include generic-only, types-only and imports-only modules.
- On restore, a missing `.o` is correct for such a module and is a miss for any
  other module (§13.6).

### Incremental monomorphisation

- An instance minted after a module was cached is a concrete entry in the table
  of the module that demanded it. It is cached with that module's pair
  ([restoration parity](../int/int.md#75-restoration-parity)).
- The generic module's own pair does not change when a later importer
  instantiates it.

## 11. Three-Mode Compilation Support

- **`--run` and REPL.** Valid modules restore in process: the sidecar installs,
  then the `Linker` maps the `.o` (§8, §13.3). Invalid modules compile fresh,
  and the nice worker writes their pair for the next session.
- **`--link`.** Modules compile through the same pipeline, reusing valid cache
  entries, and the system linker links their `.o` files with a startup stub.
  The CLI rejects `--no-cache` with `--link` (`src/main.rs`); CD-1
  uses a fresh project for its uncached link control.
- **Release.** The future optimising backend recompiles all reachable source
  and ignores the Cranelift cache.

## 12. Future Considerations

Each item is an open point with the trigger that would take it up.

- **Interface hashing.** Key importers on a dependency's public interface
  rather than its whole source, so private edits stop invalidating importers.
  The hash would have to cover every generic and macro body an importer
  compiles from, not only signatures
  ([dependency record and validity](../int/int.md#76-dependency-record-and-validity)).
  Trigger: measured rebuild cost from private-only dependency edits.
- **Cache garbage collection.** A removed or renamed module leaves an orphaned
  pair. Orphans cost disk space, not correctness. Trigger: reported cache
  growth.
- **Empty compiler fingerprint.** When the running binary's modification time
  is unreadable, the manifest's compiler gate is skipped, and each sidecar's
  build identity is the remaining gate. That identity is the package version
  plus the commit, so two uncommitted builds of one commit share it. This
  residual is asserted, not measured. Falsifier: with the fingerprint forced
  empty, rebuild an uncommitted change that alters emitted code without a
  schema bump, then check whether a cached module restores.

## 13. ObjectModule Compilation and Loading

### 13.1 What goes in the `.o` file

The `.o` is a standard relocatable object: Mach-O on macOS and ELF on Linux,
both aarch64. It contains:

- machine code for each of the module's codegen targets;
- the module's GOT as an exported data symbol, sized to its slots, with a
  function-address relocation at each occupied slot
  ([per-module GOT](per-module-got.md) §2);
- data sections for constants such as string literals, including
  object-local `.L` labels (§13.3.1);
- relocations for calls, GOT loads, imported GOT data symbols of other modules,
  and runtime, primitive and platform imports.

It contains no type information, which is in the sidecar, no source, and no
absolute addresses.

### 13.2 Generation path

- The writer builds a position-independent ISA, calls `compile_to_module` with
  an object module and the module's codegen targets, then finalises and emits
  the bytes. `FnCompiler` is generic over the Cranelift `Module` for this
  reason.
- Cross-module references are emitted GOT-indirect and resolved at load.
  Object-mode compilation renders no IR text, because introspection never
  reads it.

### 13.3 Loading path

`Linker::load_object`:

1. parses the object;
2. copies its text and data sections into mapped memory;
3. resolves each relocation against the object's local symbols, then symbols
   defined by objects it has already loaded, then registered external symbols;
4. allocates an in-process slot for each GOT-load relocation target;
5. marks the code executable;
6. records the object's defined symbols.

The caller registers runtime, primitive, platform and other modules' GOT
addresses before loading, then stores the returned addresses into the module's
live GOT (§8). Every entry restored from one object shares that `Linker`
through `Arc`, and the mapping lives until the last clone drops
([linker retention](../int/int.md#74-linker-retention)).

#### 13.3.1 Object-local `.L` data symbols are GOT-resolvable targets

Cranelift emits `.L`-prefixed **object-local** data labels for string-literal
constants, for example the runtime-panic messages raised from prelude
trait-method dispatchers. It references them through a GOT-load relocation
pair, the same ADRP+LDR mechanism used for cross-module imports. A `.L` local is
therefore a **relocation target that needs an in-process GOT slot**, not a
private datum the linker may ignore.

Two rules follow, and both are load-bearing:

- **Every symbol-resolution path in `Linker` sees the same three maps in the same
  priority order**: per-object local symbols, then defined symbols, then
  registered symbols. A slot allocator that consulted only the last two
  rejected a target the relocation loop had already resolved; that shipped as
  a cache-load failure. Keep slot allocation a pure allocator: **pass the
  already-resolved address down** rather than re-resolving it.
- **A GOT-relocation regression test must use a `.L`-prefixed object-local
  target, not only an imported global.** An import resolves on every path, so it
  cannot witness this class. A guard that used only an import passed while the
  defect shipped.

Only the cache-load path is exposed. A fresh JIT session resolves literal
references through Cranelift's own symbol table and performs no object
relocation fixup, so the asymmetry appears only when a later session reads the
persisted object. Pinned by
`crates/cranelisp-backend/src/cache/linker/tests.rs::ensure_got_slot_accepts_preresolved_local_symbol_address`
(unit) and `tests/cache.rs::cache_repl_second_session_loads_prelude_from_cache`
(e2e).

### 13.4 GOT data-symbol naming

- The types crate's `got_data_symbol_name` is the single mint for
  `__cranelisp_got_{module}`. It is an injective escape of the full module
  path, with carve-outs for the entry module and platform modules. The
  backend's `compiler::got_data_symbol_name` delegates to it.
- The symbol is exported from the owning module's object and imported by every
  object that calls into that module.
- **Changing the mint renames every cached object's relocations**, so it lands
  with a `CACHE_SCHEMA_VERSION` bump in the same change-set.

### 13.5 GOT data is file-backed

Define the GOT data with explicit zero bytes, never as zero-initialised data.
Zero-init places it in BSS on Mach-O, which has no file-backed content, and the
system linker faults when applying relocations there. The emitter states the
same rule at its definition site.

### 13.6 Modules without codegen targets

- A module with no codegen targets writes no `.o` (§10).
- Macro clauses are ordinary codegen targets. They restore from the object like
  any callable, and int validates the clause ABI of a restored table before
  accepting it.

### 13.11 Single emission path

The JIT and the object path are one function, `compile_to_module`, parameterised
by the Cranelift module. Do not rebuild a parallel object-input assembler that
re-derives definitions or slot numbers outside the symbol table. The retired
separate object path crashed on multi-signature definitions and invented slot
numbers that disagreed with the live GOT. The emission entry and its caller
contract are in [compile to module](compile-to-module.md).
`ObjectCompileInput` now carries only a module path and its targets.

## 14. Persisted module record

### 14.1 Persisted shape

- **`.meta.json` is the module's serialised `SymbolTable<(), ()>`.** It persists
  every serde-visible field the types crate defines, including the
  declarations, callable lifecycle records with their slots, ownership
  summaries and bodies, and structural declarations. It adds no parallel store.
- **Runtime state is not persisted.** Code owners, the per-module GOT and linker
  handles are skipped and re-derived on restore. The GOT starts empty and is
  repopulated from the loaded object and the platform reload.
- The shape of the table and its restore-time legality belong to the types
  crate ([slot and cache authority](../arch/interfaces.md#slot-and-cache-authority)).
  Summary persistence belongs to [ownership inference](../arch/ownership-inference.md).
- The compiler-owned `primitives` module is never cached. Its table and GOT are
  process-static.

### 14.2 `CACHE_SCHEMA_VERSION` ownership

**Schema versioning.** The backend owns `CACHE_SCHEMA_VERSION` in
`crates/cranelisp-backend/src/cache/mod.rs`, and int stamps it on every write
([schema versioning](../int/int.md#73-cache-schema-versioning-decision-34)).

- **Bump rule.** Bump for any change to persisted bytes that an older sidecar
  cannot be read as. Also bump for a value-only change when an older sidecar can
  carry a value the current compiler would misuse. Soundness corrections to
  persisted ownership summaries are examples of the second kind. The constant's
  rustdoc carries the per-version record. Read the current value there rather
  than from prose.
- **Build identity.** `BUILD_ID` is stamped next to the schema version and
  compared on load. It catches a rebuilt compiler, but it is not a substitute
  for a bump. It misses cross-branch cache reuse, and it misses two uncommitted
  builds of one commit.
- A mismatch of either is a `CacheStale`, which is an ordinary miss, never a
  decoding error.

### 14.3 Cache-restore (load path)

The restore steps, with the owner of each:

- **Step [1], read** the sidecar bytes (backend).
- **Step [2], decode** them as `SymbolTable<(), ()>` (backend).
- **Step [3], version gate.** A schema-version or build-identity mismatch is
  `CacheStale::SchemaMismatch` or `CacheStale::BuildIdMismatch`. The module
  falls through to a fresh build (backend).
- **Step [4], validate** in one pass: the recorded path, every persisted index in the
  census of §14.7, and the instance-key identity reported by the types crate's
  `validate_lifecycle`. Any failure is a `CacheStale` (backend).
- **Step [5], install and recurse.** Int installs the table, re-resolves platform
  declarations, registers the module as typechecked-from-cache, and recurses
  into its dependencies ([cache-hit flow](../int/int.md#71-cache-hit-flow-inside-register_module)).
  - **Step [5a], platform reload.** A failed platform re-resolution is a miss (int).
  - **Step [5b], object load.** The codegen worker calls `load_cached_object`,
    stores each returned address in its target's GOT slot and attaches
    `Code::Linker`. **Codegen does not run on a hit**: the persisted `.o` is the
    compiled output. A target the object does not define is a hard error (int
    and backend).
- **Step [6], relationships.** Children, written trait impls and aliases are rebuilt
  by the same writers the fresh path uses
  ([restoration parity](../int/int.md#75-restoration-parity)) (int).

Typecheck, fresh or restored, fixes each module's slot layout, and codegen only
fills slot contents. Modules therefore load in any order.

### 14.4 One source for write and restore

The symbol table is the only input to both directions. The writer serialises
the table and compiles the table's codegen targets. The restorer decodes the
table and loads the object. No stashed compile inputs, packets of scattered
session state or cache-only copies of table facts exist beside it. A second
store would let a cache hit diverge from a fresh compile without any check
noticing (Principle 7).

### 14.5 Cache-write path

1. Clone the module's table from the session store.
2. Serialise it with the schema version and build identity (`write_meta`), and
   write it atomically.
3. If the module has codegen targets, compile them against an object module
   (§13.2) and write the `.o` atomically.
4. Record the manifest entry: the module's source hash and its dependency record
   (§3). Int defers the entry until that record settles.

The sidecar write depends on typecheck alone, so a module whose object fails to
compile still persists its table. Int owns ordering, error tolerance and
scheduling (§7).

### 14.6 Symmetry invariant (mirrors §8 design principle)

- **Equal in memory.** Fresh build and restore agree in what ends up in memory:
  the same table content, the same populated GOT slots and the same installed
  scope.
- **Different lifetime root.** A fresh build's entries hold `Code::Jit` and are
  reclaimed per batch; a restore's entries hold `Code::Linker` and are
  reclaimed per object ([Code lifecycle](../int/int.md#5-code-enum--lifecycle-decisions-31-35-41)).
  In both cases the callable address lives in the GOT, not in `Code`.
- **Mixed sessions are normal.** Restored and fresh entries coexist in one
  session.
- **Evidence.**
  - A serialise-then-decode round trip must equal the original on every
    serialised field. The backend unit tests in
    `crates/cranelisp-backend/src/cache/serialize/tests.rs` carry this.
  - Fresh and cache-hit runs of one project must behave identically in values,
    effects and IO order. The e2e cells in `tests/cache.rs` carry this.

### 14.7 Failure modes (CacheStale discriminator)

- **Per-module staleness.** `CacheStale` in
  `crates/cranelisp-backend/src/cache/serialize.rs` names every reason a
  sidecar is refused. The families are:
  - missing file, I/O failure or undecodable bytes;
  - schema or build-identity mismatch;
  - path mismatch;
  - persisted-index census failures;
  - instance-key mismatch.
- **One caller-visible behaviour.** Every variant means the same thing to the
  caller: treat the module as a miss, recompile it and write a fresh pair. The
  discriminator exists for diagnostics and tests, not for control flow.
- **Other staleness.** Dependency staleness is `check_manifest` returning
  `Ok(false)`, not a `CacheStale`. Global staleness is `CacheInvalidReason`
  (§3).
- **Census rule.** Cache bytes are external data. Every persisted index is
  validated once at load and diagnosed as stale, never asserted or trusted into
  emission. The census table and its maintenance rule live in the `serialize`
  module rustdoc: a new persisted index adds its row and its check in the same
  change-set.
- **Lifecycle scope.** Validation of other decoded lifecycle states is an
  accepted residual, not a cache guarantee
  ([integration obligations](../int/int.md) §16.0).
