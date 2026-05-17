# Facade spec — `crates/cranelisp-backend/src/cache/` (sub-facade)

**Parent facade.** `facades/backend.md` — backend's top-level surface. This document is the sub-facade for the cache submodule (`cranelisp_backend::cache`), which was the largest single facade gap identified by the Sprint 67 Phase 2 audit (~60 pub items doubled across submodules + a root-level re-export layer). Parent facade is silent on cache shape; this document fills that silence.

**Bounded context citation.** Cache is the persistence half of backend's bounded context: it serialises the typecheck product (sidecar) + the codegen product (`.o`) to disk, validates cache hits against current source hashes and toolchain fingerprints, and reads them back into memory at session start. Lives in `cranelisp-backend` because the cache `Linker` newtype mediates ELF/Mach-O object loading — a Cranelift-adjacent capability that `cranelisp-types` may not name (Principle 3).

This spec is **target-stating**. Drift is detected by `cargo-public-api` (the doubled root-level re-export layer is itself the largest single drift — see §"Disposition decisions" below).

---

## Architectural shape

Four sibling submodules under `cranelisp_backend::cache`:

| Submodule | Role | Largest external consumer |
|---|---|---|
| `linker` | Mach-O / ELF object loading + per-symbol resolution. Wraps `memmap2` + `object` crates. | `cranelisp-backend::compile_to_module` (cache-hit path) + `int::session_v4` (Linker retention) |
| `manifest` | Cache index (`manifest.json`): per-module source + dependency hash records; cache-validity check against compiler fingerprint, target triple, cranelift version, format version. | `int::cache` (manifest read/write orchestration) |
| `object` | `.o` build packet construction + processing; Cranelift `ObjectModule` + `TargetIsa` plumbing; GOT data symbol naming. | `cranelisp-backend::compile_to_object` (codegen entry) + nice worker hot path |
| `serialize` | Sidecar (`.meta.json`) read/write; `SymbolTable<(), ()>` serde via `bincode`; `CacheStale` discrimination at deserialise time. | `int::cache` (cache-hit typecheck-skip path) + nice worker (sidecar write) |

The doubled root-level surface (`cranelisp_backend::cache::CacheManifest`, `cranelisp_backend::cache::Linker`, etc.) is a convenience re-export layer authored before per-submodule organisation stabilised. Per the disposition table below, the re-export layer narrows to `pub(crate)` — callers route through submodule paths.

---

## Public surface (as-designed)

### `cache::linker` — object loading + per-symbol resolution

```rust
pub struct Linker { /* opaque — mmap'd .o + Mach-O/ELF relocation state */ }

impl Linker {
    pub fn new() -> Result<Self, CranelispError>;
    pub fn load_object(&mut self, module_name: &str, bytes: &[u8]) -> Result<(), CranelispError>;
    pub fn get_symbol(&self, name: &str) -> Result<*const u8, LinkerError>;       // Decision 36 bare-name lookup — RETURN TYPE CHANGE pending Wave 3 (currently Option<*const u8>)
    pub fn register_symbol(&mut self, name: &str, addr: *const u8);               // intrinsic resolution pre-link
}
```

`Linker` is named in `facades/backend.md` §"Linker" — this sub-facade adds the per-method enumeration. `get_symbol`'s post-S67 return type lifts from `Option<*const u8>` to `Result<*const u8, LinkerError>` per Decision 37 — implementation lands at Wave 3 (`/dev (backend)`); the typed error itself lives in `crates/cranelisp-backend/src/error.rs` (authored Wave 0 — REV-4).

### `cache::manifest` — cache index + validity

```rust
#[non_exhaustive]
pub struct CacheManifest {                                                        // serialised as `manifest.json`
    pub cache_format_version: u32,                                                // monotonic; bump on shape change
    pub compiler_mtime: String,                                                   // binary fingerprint (build id + mtime)
    pub cranelift_version: String,                                                // exact crate version
    pub target_triple: String,                                                    // host triple at write time
    pub modules: HashMap<String, CachedModuleRef>,                                // keyed by module path string
}

#[non_exhaustive]
pub struct CachedModuleRef {
    pub source_hash: String,                                                      // SHA-256 of module source
    pub dependency_hashes: HashMap<String, String>,                               // transitive deps for cache invalidation
}

#[non_exhaustive]
pub enum CacheInvalidReason {
    CompilerChanged,                                                              // binary fingerprint mismatch
    CraneliftVersion { cached: String, current: String },
    FormatVersion { cached: u32, current: u32 },
    TargetTriple { cached: String, current: String },
}

impl CacheManifest {
    pub fn new(target_triple: &str) -> Self;
    pub fn new_for_host() -> Self;
    pub fn get_module(&self, module_path: &ModuleFullPath) -> Option<&CachedModuleRef>;
    pub fn upsert_module(&mut self, module_path: &ModuleFullPath, source_hash: String, dependency_hashes: HashMap<String, String>);
    pub fn remove_module(&mut self, module_path: &ModuleFullPath);
}

// Free functions
pub fn binary_fingerprint() -> String;                                            // current binary's identity for cache invalidation
pub fn hash_source(source: &str) -> String;                                       // canonical source hashing function
pub fn check_manifest(manifest: &CacheManifest, module_path: &ModuleFullPath, current_source_hash: &str, dependency_source_hashes: &HashMap<ModuleFullPath, String>) -> Result<bool, CacheInvalidReason>;
pub fn read_manifest(cache_dir: &Path) -> Option<CacheManifest>;
pub fn write_manifest(cache_dir: &Path, manifest: &CacheManifest) -> Result<(), CranelispError>;
```

### `cache::object` — `.o` packet construction + processing

```rust
#[non_exhaustive]
pub struct CacheWritePacket {                                                     // sidecar metadata + .o bytes pair, write-ready
    pub cache_dir: PathBuf,
    pub module_path: ModuleFullPath,
    pub source_hash: String,
    pub is_stdlib: bool,
    pub dependency_hashes: HashMap<String, String>,
    pub meta_path: PathBuf,                                                       // `{cache_dir}/{module}.meta.json` — sidecar destination
    pub meta_json_bytes: Vec<u8>,                                                 // pre-serialised sidecar bytes — write_meta output ready for atomic-rename write
    pub object_path: PathBuf,                                                     // `{cache_dir}/{module}.o` — object destination
    pub object_compile_input: ObjectCompileInput,                                 // frozen codegen input handed to compile_to_object
}

#[non_exhaustive]
pub struct ObjectCompileInput {                                                   // serialised codegen input — frozen typecheck state ready for ObjectModule compile
    pub module_path: ModuleFullPath,
    pub defns: Vec<(Defn, Scheme)>,                                               // typechecked AST bodies + their schemes — codegen iterates these
    pub expr_types: HashMap<Span, Type>,                                          // per-expression resolved Type for codegen-time lookup (RC heap-category, monomorphisation)
    pub fn_slot_assignments: HashMap<Symbol, FnSlotInfo>,                         // per-fn GOT slot pre-assignment (cluster-atomic — see Decision 23)
    pub fn_to_module: HashMap<Symbol, ModuleFullPath>,                            // resolved owning module per call-target Symbol — backend's cross-module call routing
    pub cross_module_fns: Vec<(Symbol, usize)>,                                   // out-of-module call targets + their GOT slots on the foreign module's table
    pub intrinsics: IntrinsicTable,                                               // fully resolved intrinsic names this `.o` calls — declared with `Linkage::Import`
    pub method_resolutions: MethodResolutions,                                    // trait dispatch table from typecheck — resolves `ResolvedCall::TraitMethod` at codegen time
    pub next_got_slot: usize,                                                     // monotonic slot counter — codegen may grow the GOT for cluster-internal closures
}

#[non_exhaustive]
pub struct ProcessedPacket {                                                      // CacheWritePacket consumed; success record returned to caller
    pub module_path: ModuleFullPath,
    pub source_hash: String,
    pub is_stdlib: bool,
    pub dependency_hashes: HashMap<String, String>,
}

#[non_exhaustive]
pub struct FnSlotInfo {                                                           // per-fn GOT slot index + linkage metadata for sidecar
    pub slot: usize,                                                              // GOT slot index in `SymbolTable[module].got`
    pub param_count: usize,                                                       // arity — sidecar shape stability check at cache-hit reload
}

#[non_exhaustive]
pub struct IntrinsicTable {                                                       // fully resolved intrinsic name → FuncId map, per-`.o`
    pub global_names: HashSet<Symbol>,                                            // every intrinsic symbol referenced anywhere in this `.o` — duplicate filter
    pub primitive_fns: Vec<IntrinsicEntry>,                                       // calls into `cranelisp-primitives` (Decision 43)
    pub runtime_fns: Vec<IntrinsicEntry>,                                         // calls into `cranelisp-intrinsics` (Decision 43; alloc, rc_*, drop glue, …)
    pub platform_fns: Vec<IntrinsicEntry>,                                        // calls into `cranelisp-platform` (DLL boundary fns)
}

#[non_exhaustive]
pub struct IntrinsicEntry {                                                       // one row in IntrinsicTable
    pub user_name: Symbol,                                                        // surface name as written by codegen (`+`, `add-i64`, `runtime/panic`, `str-concat`)
    pub jit_name: String,                                                         // linker-visible symbol name (`cranelisp_alloc`, `vec_push_copy`, …) — what `JITBuilder::symbol` / system `ld` binds
    pub param_count: usize,                                                       // arity for declare_function signature
}

// Free functions
pub fn build_cache_packet(cache_dir: &Path, module_path: &ModuleFullPath, source_hash: &str, is_stdlib: bool, dependency_hashes: HashMap<String, String>, metadata: &CacheMetadata, object_compile_input: ObjectCompileInput) -> Result<CacheWritePacket, CranelispError>;
pub fn build_isa(is_pic: bool) -> Result<Arc<dyn TargetIsa>, CranelispError>;     // RE-EXPORTED AT BACKEND ROOT — single ISA construction point (architecture decision 7)
pub fn got_data_symbol_name(module_path: &ModuleFullPath) -> String;              // `__cranelisp_got_{module}` — Decision 23 GOT data symbol naming
pub fn process_cache_packet(packet: &CacheWritePacket, symbol_tables: &DashMap<ModuleFullPath, SymbolTable>) -> Result<ProcessedPacket, CranelispError>;
```

### `cache::serialize` — sidecar serialisation

```rust
#[non_exhaustive]
pub struct CacheMetadata {                                                        // sidecar header + payload — serialised as `{module}.meta.json` per Decision 25
    pub symbol_table: SymbolTable,                                                // serialised `SymbolTable<(), ()>` — types, schemes, AST bodies, GOT layout (Decision 25)
    pub dependencies: Vec<String>,                                                // dotted module paths this module imports — used by `CachedModule::imported_modules`
}

#[non_exhaustive]
pub enum CacheStale {                                                             // all variants surface as cache misses to the caller (`int` recompiles); they are distinct only for telemetry / diagnostic reporting
    Missing { path: PathBuf },                                                    // sidecar file absent on disk — first compile, eviction, or paired-with-`.o`-deletion race
    Io { path: PathBuf, message: String },                                        // file read failed (permissions, partial read, fs error) — treat as cache miss; the recompile will recreate the file
    Deserialise { path: PathBuf, message: String },                               // bincode failed — corruption, partial-write recovery, ABI mismatch from a manually-edited cache
    SchemaMismatch { path: PathBuf, expected: u32, found: u32 },                  // `CACHE_SCHEMA_VERSION` bumped since this sidecar was written — Decision 34 fail-loud
    BuildIdMismatch { path: PathBuf, expected: String, found: String },           // compiler binary fingerprint changed — every cached module is invalidated atomically
    PathMismatch { path: PathBuf, expected: ModuleFullPath, found: ModuleFullPath },  // sidecar's recorded `module_path` does not match the lookup key — moved file or corruption
}

impl CacheStale {
    pub fn reason(&self) -> &'static str;                                         // for telemetry
}

// Free functions
pub fn serialise_meta<C, L>(table: &SymbolTable<C, L>, schema_version: u32) -> Result<Vec<u8>, CranelispError>
    where C: CodeStore + Clone, L: LinkerStore + Clone;
pub fn deserialise_meta(bytes: &[u8], expected_schema_version: u32, path: &Path) -> Result<SymbolTable, CacheStale>;
pub fn write_meta<C, L>(meta_path: &Path, table: &SymbolTable<C, L>, schema_version: u32) -> Result<(), CranelispError>
    where C: CodeStore, L: LinkerStore;
pub fn load_meta(meta_path: &Path) -> Result<SymbolTable, CacheStale>;
pub fn read_cached_metadata(meta_path: &Path) -> Result<CacheMetadata, CranelispError>;
pub fn write_cached_metadata(meta_path: &Path, metadata: &CacheMetadata) -> Result<(), CranelispError>;
```

### `cache::*` (root) — orchestration helpers + cross-cutting types

```rust
#[non_exhaustive]
pub struct CachedModule {                                                         // composite: loaded sidecar + path-pairing flag — handed to int's process_cluster
    pub metadata: CacheMetadata,                                                  // the deserialised sidecar header + SymbolTable
    pub meta_path: PathBuf,                                                       // origin path on disk — kept for diagnostic messages + manifest cross-check
    pub object_path: PathBuf,                                                     // sibling `.o` path — Linker::load_object consumes if `has_object`
    pub has_object: bool,                                                         // pair-invariant flag: false implies the sidecar exists but the `.o` was deleted (corrupted cache) — caller treats as cache miss
}

impl CachedModule {
    pub fn symbol_table(&self) -> &SymbolTable;                                   // `&self.metadata.symbol_table` — convenience accessor
    pub fn imported_modules(&self) -> HashSet<ModuleFullPath>;                    // transitive deps from `metadata.dependencies` — `int` uses this to pre-warm the cluster
}

// Public consts
pub const BUILD_ID: &str;                                                         // baked-in build identifier
pub const CACHE_FORMAT_VERSION: u32;                                              // bump when CacheManifest layout shifts
pub const CACHE_SCHEMA_VERSION: u32;                                              // bump when SymbolTable serialised shape shifts (Decision 34)

// Free orchestration functions — keep at cache:: root because they tie multiple submodules together
pub fn module_cache_path(cache_dir: &Path, module_path: &ModuleFullPath) -> (PathBuf, PathBuf);  // returns (sidecar_path, object_path)
pub fn try_load_cached_module(cache_dir: &Path, module_path: &ModuleFullPath) -> Result<CachedModule, CacheStale>;
pub fn load_cached_object(linker: &mut Linker, cached: &CachedModule) -> Result<(), CranelispError>;
```

---

## Disposition decisions — per item

The audit identified each pub item as either PFR (pull facade to reality — name it in the sub-facade) or PIF (push implementation to facade — narrow to `pub(crate)` or relocate). Per-row dispositions:

### `cache::linker` (5 items)

| Item | Direction | Rationale |
|---|---|---|
| `pub struct Linker` | PFR | Named in parent facade; sub-facade enumerates methods |
| `Linker::new` | PFR | Constructor — keep public |
| `Linker::load_object` | PFR | Used by parent facade's free function `load_object` (Wave 3 carve-out) |
| `Linker::get_symbol` | PFR — return-type lift Wave 3 | `Option<*const u8>` → `Result<*const u8, LinkerError>` per Decision 37 |
| `Linker::register_symbol` | PFR | Used at JIT setup for intrinsic resolution |

### `cache::manifest` (10 items)

| Item | Direction | Rationale |
|---|---|---|
| `pub struct CacheManifest` + fields | PFR | Named here; serde shape locks via Decision 34 schema version |
| `pub struct CachedModuleRef` | PFR | Component of CacheManifest |
| `pub enum CacheInvalidReason` | PFR | Public — `int::cache` matches on variants to decide cache miss vs partial-invalidation telemetry |
| `CacheManifest::new`/`new_for_host`/`get_module`/`upsert_module`/`remove_module` | PFR | Standard CRUD on the manifest |
| `binary_fingerprint`, `hash_source` | PFR | Used by `int` to compute current state pre-check |
| `check_manifest` | PFR | Used at every cache-hit attempt |
| `read_manifest`, `write_manifest` | PFR | File IO bookends |

### `cache::object` (15 items)

| Item | Direction | Rationale |
|---|---|---|
| `CacheWritePacket` + fields (`cache_dir`, `module_path`, `source_hash`, `is_stdlib`, `dependency_hashes`, `meta_path`, `meta_json_bytes`, `object_path`, `object_compile_input`) | PFR | Crosses backend↔int boundary (nice worker produces, int writes). All fields are `pub` so `int`'s `ObjectCache::write` can do atomic-rename file IO without going through accessor methods |
| `ObjectCompileInput` + fields (`module_path`, `defns`, `expr_types`, `fn_slot_assignments`, `fn_to_module`, `cross_module_fns`, `intrinsics`, `method_resolutions`, `next_got_slot`) | PFR | Crosses orchestrator↔backend boundary at `compile_to_object`. Fields are the frozen typecheck product the nice worker hands to backend codegen — every field is read once during a single `compile_to_object` call |
| `ProcessedPacket` + fields | PFR | Return type for `process_cache_packet`; carries the bookkeeping `int` needs to update the manifest after a successful write |
| `FnSlotInfo` + fields (`slot`, `param_count`), `IntrinsicTable` + fields (`global_names`, `primitive_fns`, `runtime_fns`, `platform_fns`), `IntrinsicEntry` + fields (`user_name`, `jit_name`, `param_count`) | PFR | Sidecar shape components; serde-stable. The three-bucket `IntrinsicTable` split (primitive / runtime / platform) tracks Decision 43's three-crate split of the post-runtime relocation targets — backend declares each bucket with `Linkage::Import` and the bucket determines which archive the system linker (`--link` mode) or `JITBuilder::symbol` (JIT mode) resolves against |
| `build_cache_packet` | PFR | Nice worker → packet construction |
| `build_isa` | PFR | Already re-exported at backend crate root; **the re-export at root is the canonical name** (Decision 7); the submodule-qualified form `cache::object::build_isa` is the source of truth but parent facade names it without the path |
| `got_data_symbol_name` | PFR | Decision 23 GOT data symbol naming — referenced from compile-to-module |
| `process_cache_packet` | PFR | Orchestrator hot path |

### `cache::serialize` (10 items)

| Item | Direction | Rationale |
|---|---|---|
| `CacheMetadata` | PFR | Sidecar header |
| `CacheStale` enum + `reason()` | PFR | Discrimination at cache load — `int` matches on this for telemetry. Variants: `Missing`, `Io`, `Deserialise`, `SchemaMismatch`, `BuildIdMismatch`, `PathMismatch` — each names `path` for diagnostic context; version-mismatch variants additionally carry `expected` / `found` |
| `serialise_meta`, `deserialise_meta` | PFR | Symmetric read/write pair; both `pub` for nice worker + cache-hit path |
| `write_meta`, `load_meta` | PFR | File IO wrappers around the byte-level pair |
| `read_cached_metadata`, `write_cached_metadata` | PFR | Header-only read/write (cheaper than full sidecar) — used for cache-hit pre-validation |

### `cache::*` root re-export layer (~30 items — the doubled surface)

All items in `cranelisp_backend::cache::{CacheManifest, CachedModuleRef, CacheInvalidReason, CacheMetadata, CacheStale, CacheWritePacket, CachedModule, FnSlotInfo, IntrinsicEntry, IntrinsicTable, Linker, ObjectCompileInput}` are re-exports of items already named in their submodules.

| Item set | Direction | Rationale |
|---|---|---|
| All `cache::{...}` re-exports of submodule items | **PIF — narrow to `pub(crate)`** | Doubled public-API surface. Callers route through submodule paths (`cache::linker::Linker`, `cache::manifest::CacheManifest`, etc.). The convenience re-exports double the cargo-public-api line count (502 lines vs ~250 lines), produce confusing dual-name search results, and offer zero value over the qualified path. **Wave 4 `/dev (backend)` removes the re-exports.** |
| `cache::CachedModule` + fields (`metadata`, `meta_path`, `object_path`, `has_object`) + methods (`symbol_table`, `imported_modules`) | PFR (retain at root) | Composite type that ties multiple submodules together — has no natural single-submodule home. Keep at `cache::` root with the orchestration helpers below. `has_object` is the pair-invariant flag the cache-hit path consults before calling `Linker::load_object` |
| `cache::BUILD_ID`, `CACHE_FORMAT_VERSION`, `CACHE_SCHEMA_VERSION` | PFR | Top-level consts — keep at root |
| `cache::binary_fingerprint`, `hash_source`, `check_manifest`, `read_manifest`, `write_manifest` | **PIF — narrow to `pub(crate)` then prefer `cache::manifest::*` paths** | Already exist in `cache::manifest::*` as the canonical home. Root-level duplicates are convenience shims. Wave 4 removes. |
| `cache::build_cache_packet`, `got_data_symbol_name`, `process_cache_packet` | **PIF — narrow to `pub(crate)` then prefer `cache::object::*`** | Same — submodule home is canonical. |
| `cache::serialise_meta`, `deserialise_meta`, `write_meta`, `load_meta`, `read_cached_metadata`, `write_cached_metadata` | **PIF — narrow to `pub(crate)` then prefer `cache::serialize::*`** | Same — submodule home is canonical. |
| `cache::module_cache_path`, `try_load_cached_module`, `load_cached_object` | PFR (retain at root) | Multi-submodule orchestration helpers — natural home is `cache::` root |

**Volume note.** The PIF narrowing of the doubled re-export layer is `/dev (backend)`'s Wave 4 work — call-site routing through submodule paths is mechanical. Caller-side updates in `int` are bounded (`grep cranelisp_backend::cache:: src/*.rs`).

---

## Items that should move OUT of `cranelisp-backend::cache`

None identified. Every item under `cache::` is single-consumer (per Principle 15): `int` is the sole external consumer, and `cranelisp-backend` itself is the sole internal consumer. No item naturally crosses into `cranelisp-types` (each references either Cranelift state, mmap'd memory, or file IO — none of which `cranelisp-types` may name per Principle 3).

`CacheStale` was briefly considered for hoisting to `cranelisp-types` (it crosses the backend↔int boundary as a `Result` error variant). Rejected: hoisting it would also require hoisting `CacheMetadata` (which it can carry context from) and `Linker` (referenced indirectly via `load_cached_object`). The dependency tree is backend-rooted; keeping `CacheStale` in `cranelisp-backend::cache::serialize` keeps the cycle out.

---

## Forbidden patterns

These are patterns that future cache changes MUST NOT introduce. Listed here so `/review` can flag any regression.

### No `pub` items shared across submodules without naming the canonical home

Every cache type has exactly one canonical home (submodule). Root-level re-exports were the historical pattern; per the disposition above, they are removed in Wave 4. New types added to cache must:

1. Land in exactly one submodule by responsibility.
2. NOT be re-exported at `cache::` root unless they are genuine orchestration helpers (multi-submodule consumers).
3. Be named in this sub-facade in the appropriate per-submodule section before landing.

### No bare `Option<*const u8>` at the cache boundary

Per Decision 37 — `Linker::get_symbol`'s current `Option<*const u8>` is the pre-S58 silent-NULL regression net. Future cache APIs that return optional pointers must use typed errors (`LinkerError` or successor) so that consumers can discriminate "cache miss" from "symbol not in this object".

### No serde-shape changes without `CACHE_SCHEMA_VERSION` bump

`CACHE_SCHEMA_VERSION: u32` is Decision 34's load-bearing version field. Any change to a `#[derive(Serialize, Deserialize)]` shape that affects on-disk bytes MUST bump the version. `deserialise_meta` will reject mismatched versions with `CacheStale::SchemaMismatch`; the consumer treats this as cache miss and recompiles. Skipping the bump corrupts user cache directories silently — fail-loud over fail-silent.

---

## Bounded-context invariants

These hold across sprints — the contract `cache::` makes with the rest of the workspace:

1. **`Linker` is the only mmap-holder.** No other type in the workspace holds mmap'd object memory. Per-symbol retention via `Arc<Linker>` (cloned per `Code::Linker` clone) keeps pages alive until the last reference drops.

2. **`CacheManifest` is the single index.** No other on-disk structure indexes the cache. Per-module sidecars (`{module}.meta.json`) and objects (`{module}.o`) are referenced via `CacheManifest::modules` and pair-invariantly (sidecar present implies object present, and vice versa — see parent facade §"Pairing invariant").

3. **Cache-validity is checked at every cache-hit attempt.** `check_manifest` runs before any `try_load_cached_module` invocation. Stale cache surfaces as `CacheStale` and the caller recompiles — no implicit "use stale cache anyway" fallback.

4. **`CACHE_FORMAT_VERSION` and `CACHE_SCHEMA_VERSION` are independent.** Format version bumps with `CacheManifest` shape (the index); schema version bumps with `SymbolTable` serialised shape (the sidecars). A version-mismatched manifest invalidates all cached modules atomically; a version-mismatched sidecar invalidates only that one module.

5. **No re-codegen on cache-hit.** Cache-hit modules skip `compile_to_module` entirely; backend reads the pre-built `.o` via `Linker::load_object` and writes `Code::Linker` lifecycle owners + per-symbol GOT slots. The `.o` byte content is authoritative for cache-hit modules; no per-symbol re-emission ever happens.

---

## Wave 4 checklist — `/dev (backend)`

Concrete items the Wave 4 narrowing change-set must touch. Every item below is a `pub(crate)`-narrowing (no behaviour change, no caller-visible signature change) UNLESS marked otherwise. Caller-side updates land in the same change-set: `grep -rn 'cranelisp_backend::cache::' src/ crates/cranelisp-int/` reveals the call sites to route through submodule paths.

| Item | Disposition | Action |
|---|---|---|
| `cranelisp_backend::cache::CacheManifest` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cranelisp_backend::cache::manifest::CacheManifest` |
| `cranelisp_backend::cache::CachedModuleRef` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::manifest::CachedModuleRef` |
| `cranelisp_backend::cache::CacheInvalidReason` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::manifest::CacheInvalidReason` |
| `cranelisp_backend::cache::CacheMetadata` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::CacheMetadata` |
| `cranelisp_backend::cache::CacheStale` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::CacheStale` |
| `cranelisp_backend::cache::CacheWritePacket` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::CacheWritePacket` |
| `cranelisp_backend::cache::FnSlotInfo` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::FnSlotInfo` |
| `cranelisp_backend::cache::IntrinsicEntry` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::IntrinsicEntry` |
| `cranelisp_backend::cache::IntrinsicTable` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::IntrinsicTable` |
| `cranelisp_backend::cache::Linker` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::linker::Linker` |
| `cranelisp_backend::cache::ObjectCompileInput` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::ObjectCompileInput` |
| `cranelisp_backend::cache::binary_fingerprint` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::manifest::binary_fingerprint` |
| `cranelisp_backend::cache::hash_source` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::manifest::hash_source` |
| `cranelisp_backend::cache::check_manifest` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::manifest::check_manifest` |
| `cranelisp_backend::cache::read_manifest` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::manifest::read_manifest` |
| `cranelisp_backend::cache::write_manifest` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::manifest::write_manifest` |
| `cranelisp_backend::cache::build_cache_packet` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::build_cache_packet` |
| `cranelisp_backend::cache::got_data_symbol_name` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::got_data_symbol_name` |
| `cranelisp_backend::cache::process_cache_packet` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::object::process_cache_packet` |
| `cranelisp_backend::cache::serialise_meta` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::serialise_meta` |
| `cranelisp_backend::cache::deserialise_meta` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::deserialise_meta` |
| `cranelisp_backend::cache::write_meta` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::write_meta` |
| `cranelisp_backend::cache::load_meta` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::load_meta` |
| `cranelisp_backend::cache::read_cached_metadata` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::read_cached_metadata` |
| `cranelisp_backend::cache::write_cached_metadata` (root re-export) | PIF-narrow | Mark `pub(crate)`; callers use `cache::serialize::write_cached_metadata` |
| `Linker::get_symbol` return type | PFR — **signature change** (Decision 37) | Return type lifts from `Option<*const u8>` to `Result<*const u8, LinkerError>`. Regenerate `crates/cranelisp-backend/public-api.txt`; callers in `int` adopt `?` propagation |

**Nothing in the Wave 4 cache list deletes.** Every cache item has a single canonical home in a submodule (`linker` / `manifest` / `object` / `serialize`) or at the `cache::` root for genuine orchestration helpers (`CachedModule`, `module_cache_path`, `try_load_cached_module`, `load_cached_object`, `BUILD_ID`, `CACHE_FORMAT_VERSION`, `CACHE_SCHEMA_VERSION`). The Wave 4 work is narrowing only — public surface shrinks by ~25 lines (the root re-export layer), no functional behaviour changes, no caller-visible bytes-on-disk changes.

**Acceptance signal.** Post-Wave-4 `cargo public-api -p cranelisp-backend` produces a 25-line shorter `public-api.txt`; `cargo nextest run --test facade_compliance` stays green; `int` builds clean against the narrowed surface.

---

## Cross-references

- Parent facade: `facades/backend.md`
- Decision 23 — two-GOT model, single CLIF
- Decision 25 — sidecar shape (serialised `SymbolTable<(), ()>`)
- Decision 34 — schema versioning
- Decision 36 — bare-name + `Linkage::Local` symbol naming
- Decision 37 — no swallowed failures (typed errors at the cache boundary)
- Decision 38 — `write_code` / `Introspection` direct writes
- Decision 41 — per-symbol JIT cardinality; cache-hit cardinality unchanged (per-module)
- `crates/cranelisp-backend/src/error.rs` — `LinkerError` (Wave 0 — REV-4)
- `crates/cranelisp-backend/src/artefact.rs` — `LinkerArtefact`, `ObjectArtefact` (Wave 0 — REV-4)
