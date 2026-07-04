//! Module caching — backend's persistence half (an internal implementation
//! detail, NOT a separate bounded-context surface).
//!
//! Serialises the typecheck product (sidecar) + the codegen product (`.o`) to
//! disk, validates cache hits against current source hashes and toolchain
//! fingerprints, and reads them back into memory at session start. It lives in
//! `cranelisp-backend` because the cache `Linker` newtype mediates ELF/Mach-O
//! object loading — a Cranelift-adjacent capability `cranelisp-types` may not
//! name (Principle 3).
//!
//! On-disk layout:
//! ```text
//!   .cranelisp-cache/
//!     manifest.json           # version, target triple, module hashes
//!     <module>.meta.json      # serialized SymbolTable (includes GOT slot assignments)
//!     <module>.o              # relocatable object file
//! ```
//! See `design/backend/module-caching.md` for the full design.
//!
//! # Four sibling submodules
//!
//! | Submodule | Role |
//! |---|---|
//! | [`linker`] | Mach-O / ELF object loading + per-symbol resolution (wraps `memmap2` + `object`). |
//! | [`manifest`] | Cache index (`manifest.json`): per-module source + dependency hashes; cache-validity check against compiler fingerprint, target triple, cranelift version, format version. |
//! | [`object`] | `.o` build-packet construction + processing; `ObjectModule` + `TargetIsa` plumbing; GOT data-symbol naming. Drives the object path `compile_to_module::<ObjectModule>` + caller `finish().emit()`. |
//! | [`serialize`] | Sidecar (`.meta.json`) read/write; `SymbolTable<(), ()>` serde; `CacheStale` discrimination at deserialise time. |
//!
//! This crate-internal root holds the genuine multi-submodule orchestration
//! helpers ([`CachedModule`], [`module_cache_path`], [`try_load_cached_module`],
//! [`load_cached_object`]) and the version consts ([`CACHE_SCHEMA_VERSION`],
//! [`CACHE_FORMAT_VERSION`], [`BUILD_ID`]). The pre-S67 doubled root-level
//! re-export layer was retired in S67 Wave 4 (see the routing note below); the
//! canonical home of every cache type is exactly one submodule.
//!
//! # Cache invariants (internal implementation invariants)
//!
//! These describe how the cache submodule behaves internally — they are not
//! contracts the rest of the workspace reasons about at the bounded-context
//! boundary:
//!
//! 1. **`Linker` is the only mmap-holder.** No other type in the workspace
//!    holds mmap'd object memory. Per-symbol retention via `Arc<Linker>`
//!    (cloned per `Code::Linker` clone) keeps pages alive until the last
//!    reference drops. (See [`linker`].)
//! 2. **`CacheManifest` is the single index.** Per-module sidecars
//!    (`{module}.meta.json`) and objects (`{module}.o`) are referenced via
//!    `CacheManifest::modules`, pair-invariantly (sidecar present implies
//!    object present, and vice versa). (See [`manifest`].)
//! 3. **Cache-validity is checked at every cache-hit attempt.**
//!    `manifest::check_manifest` runs before any [`try_load_cached_module`];
//!    a stale cache surfaces as `serialize::CacheStale` and the caller
//!    recompiles — no implicit "use stale cache anyway" fallback.
//! 4. **[`CACHE_FORMAT_VERSION`] and [`CACHE_SCHEMA_VERSION`] are independent.**
//!    Format version tracks the `CacheManifest` (index) shape; schema version
//!    tracks the `SymbolTable` serialised (sidecar) shape. A version-mismatched
//!    manifest invalidates all cached modules atomically; a mismatched sidecar
//!    invalidates only that one module.
//! 5. **No re-codegen on cache-hit.** Cache-hit modules skip
//!    `compile_to_module` entirely; backend reads the pre-built `.o` via
//!    `linker::Linker::load_object` and writes `Code::Linker` lifecycle owners
//!    plus per-symbol GOT slots. The `.o` byte content is authoritative; no
//!    per-symbol re-emission ever happens.
//!
//! # Forbidden patterns
//!
//! - **No `pub` items shared across submodules without a single canonical
//!   home.** Each cache type lives in exactly one submodule by responsibility;
//!   new types are NOT re-exported at `cache::` root unless they are genuine
//!   multi-submodule orchestration helpers.
//! - **No serde-shape change without a [`CACHE_SCHEMA_VERSION`] bump** (see
//!   [`serialize`]).

use cranelisp_types::ErrorLocation;

pub mod manifest;
pub mod serialize;
pub mod object;
pub mod linker;

// Doubled root re-export layer retired (Sprint 67 Wave 4 narrowing per
// `design/arch/facades/backend-cache.md` §"Wave 4 checklist"). Every item
// formerly re-exported here has a canonical home in a submodule
// (`manifest`, `serialize`, `object`, `linker`); the root-level
// re-exports were a pre-S67 convenience layer that doubled the published
// surface. External callers route through the canonical submodule paths:
//
//   - `cranelisp_backend::cache::manifest::{CacheManifest, CachedModuleRef,
//      CacheInvalidReason, check_manifest, hash_source, read_manifest,
//      write_manifest, binary_fingerprint}`
//   - `cranelisp_backend::cache::serialize::{CacheMetadata, CacheStale,
//      serialise_meta, deserialise_meta, write_meta, load_meta,
//      read_cached_metadata, write_cached_metadata}`
//   - `cranelisp_backend::cache::object::{CacheWritePacket,
//      ObjectCompileInput, IntrinsicTable, IntrinsicEntry, FnSlotInfo,
//      build_cache_packet, process_cache_packet, got_data_symbol_name,
//      build_isa}`
//   - `cranelisp_backend::cache::linker::Linker`
//
// In-crate use sites within `cranelisp-backend` itself use the submodule
// paths directly (`crate::cache::linker::Linker`, …).

/// Cache schema version (Decision 34, Sprint 58 §14.2).
///
/// Stamped onto `SymbolTable.schema_version` at cache-write time. Cache-load
/// peeks the field first; mismatch returns `CacheStale::SchemaMismatch` and
/// the caller falls through to a fresh build (same code path as dep-hash
/// mismatch).
///
/// Bump on:
/// * field deletions on `SymbolTable` / any `ModuleEntry` variant,
/// * field type changes (`deserialise<New>` would fail on persisted Old),
/// * enum variant additions to a serde-tagged enum used inside `SymbolTable`,
/// * variant renames.
///
/// Field additions with `#[serde(default)]` whose default matches a fresh-build
/// value do NOT require a bump.
///
/// **v2 (S76 W1b):** added `SymbolTable.schema_literal: Option<String>` (the
/// platform-as-module schema text). RETIRED in v3 — see below.
///
/// **v3 (S76 Wave 5):** `SymbolTable.schema_literal` REMOVED. The
/// platform-interface design (`platform-interface.md` §6.5, user-ratified
/// 2026-06-07) supersedes it: platforms declare ADTs as ordinary `.cl` modules
/// (which cache normally), and the DLL-embedded schema + layout-hash gate
/// replaces the cache round-trip — no schema text crosses the boundary, so
/// there is nothing to stash on `SymbolTable`. The field deletion changes the
/// serialised shape, so the version bumps (Decision 34) to invalidate stale v2
/// caches gracefully via `CacheStale::SchemaMismatch` fall-through.
///
/// **v4 (S79 R2.2 — ctor dual-facet, FIXME 0320):** the serialised shape of two
/// `ModuleEntry`-reachable types changed (Option 3a, FIXME 0319):
/// `ModuleEntry::TypeDef` LOST `constructor_scheme: Option<Scheme>` (retired),
/// and `DefKind::Constructor` GAINED `type_def: Option<Box<TypeDefInfo>>` (the
/// product-type facet — `Some` iff the ctor IS its own type). Both are
/// `#[serde(default)]` so old caches deserialise without a hard error, but the
/// *meaning* changed: a stale v3 product-type entry is a `TypeDef`-only record
/// with no surviving got-slotted ctor `Def`, which the new model cannot
/// reconstruct — it would silently mis-load (lost field names; a §4.2.1
/// violation masked behind a cache hit). Decision 34 mandates the bump so stale
/// v3 caches are rejected as version-mismatch rather than mis-loaded.
/// **S83 bump 4 → 5 (Option-A callability reshape, FIXME 0356/0358).** The
/// serialized `DefKind` / `ModuleEntry::Def` shape changed: the flat
/// `ModuleEntry::Def.got_slot` field was retired and the GOT slot moved onto the
/// callable `DefKind` variants (`UserFn { fn_state: Concrete { got_slot } }`,
/// `Primitive { got_slot }`, `Constructor { got_slot, .. }`,
/// `PlatformEffect { got_slot, .. }`); `UserFn` gained a `fn_state:
/// UserFnState` payload. A stale v4 `.meta.json` would deserialize a callable
/// with NO slot (the absent field defaulting to slot-less), so the call would
/// lower through a NULL GOT slot — the exact NULL-call regression Principle 20
/// forecloses. The bump invalidates every v4 cache as
/// `CacheStale::SchemaMismatch` (treated as a cache-miss → recompile) so the
/// slot-less mis-load can never happen.
/// **S84 bump 5 → 6 (structural slot gate, FIXME 0374/0377).** `UserFnState`
/// gained a new slot-less `Polymorphic(Box<ParametricFn>)` variant (the
/// generic-unconstrained-def arm — slot ⟺ concrete). The serialized
/// `DefKind::UserFn { fn_state }` shape therefore changed: a stale v5
/// `.meta.json` predates the variant and cannot round-trip a `Polymorphic`
/// entry, and a v5-shaped generic def that the old gate mis-slotted as
/// `Concrete`-with-a-`Type::Var` would re-introduce the NULL-slot / unsound-RC
/// regression. The bump rejects every v5 cache as `CacheStale::SchemaMismatch`
/// (cache-miss → recompile) so the corrected gate always runs.
/// **S84 bump 6 → 7 (concrete-boundary arc Phase 2a, `MonoExpr` lands).**
/// `cranelisp-types` gained the `MonoExpr` / `MonoDefnVariant` post-mono codegen
/// AST (`design/arch/concrete-boundary-type.md` §2.4) — a serde-deriving shape
/// that participates in the cached `.meta.json` symbol-table/AST surface as the
/// mono output representation. Phase 2a lands the representation (produces-but-
/// unused); the bump invalidates every v6 cache as `CacheStale::SchemaMismatch`
/// (cache-miss → recompile) so no v6 `.meta.json` is round-tripped against the
/// extended serde surface.
/// **S84 bump 7 → 8 (concrete-boundary arc Phase 3 threading, `codegen_view`
/// lands).** `ModuleEntry::Def` gained the additive `codegen_view:
/// Option<MonoDefnVariant>` field — the concrete-boundary codegen view the
/// backend consumes (`design/arch/concrete-boundary-type.md` §2.4 / §4 Phase 3,
/// threading option (a)). It is a `#[serde(default)]` participant in the cached
/// `.meta.json` symbol-table shape (it carries no pointer/`C` state), so its
/// addition changes the serialized `ModuleEntry::Def` surface. The bump rejects
/// every v7 cache as `CacheStale::SchemaMismatch` (cache-miss → recompile) so no
/// v7 `.meta.json` is round-tripped against the extended serde surface. The
/// field defaults `None` on a v8 cold-load — the typecheck seam (Phase 2b/3,
/// /dev) repopulates it, and the backend's relocated backstop (a `None` at a
/// codegen-reached entry) is the single structural guard.
///
/// **S88 bump 8 → 9 (module-preamble storage, FIXME 0428).** The per-module
/// `SymbolTable` gained the additive `module_preamble: Option<String>` field
/// (spec §8.16, BC §7) — module-level documentation text, off the symbol axis.
/// It is a `#[serde(default)]` participant in the cached `.meta.json`
/// symbol-table shape, so its addition changes the serialized `SymbolTable`
/// surface. The bump rejects every v8 cache as `CacheStale::SchemaMismatch`
/// (cache-miss → recompile) so no v8 `.meta.json` is round-tripped against the
/// extended serde surface. The field defaults `None` on a v9 cold-load; the
/// frontend reader (a future `/dev` change) populates it from the leading
/// comment block (§8.16.2).
/// **S97 v9 (ABI v8→v9 ctx-vtable cutover, `io-trampoline.md §17.4`).** The poll-node
/// arg handling changed: `compile_poll_effect` no longer peels a leading `(token,
/// capacity)` pair, so the state-closure env now packs a poll leaf's natural args at
/// `capture(1..)` with no leading-pair displacement, AND `ConcurrencyDescriptor` gained
/// a `role` byte. A stale `.o`/`.meta.json` cached under the v8 convention would marshal
/// args at the wrong capture slots, so the bump rejects every pre-v9 cache as
/// `CacheStale::SchemaMismatch` (cache-miss → recompile). This is the v8→v9 marker.
/// **S101 bump 10 → 11 (`Def.callees` enrichment, FIXME 0470 + 0472).** No
/// serde-shape change — the carrier stays `callees: Vec<FQSymbol>` — but the
/// field's *meaning* changed: typecheck now records EVERY statically-resolved
/// user-fn reference (plain direct calls + value-position fn references), at
/// EVERY body-check seam including trait-impl / default / HKT method bodies
/// (the 0472 seam cure landed inside this same S101 bump window — no
/// re-bump), where the old extraction recorded only `ResolvedCall`-derived
/// edges (trait methods, sig-dispatch, auto-curry). Deliberate residue:
/// mono-instance bodies carry no own edges — their constrained template's
/// entry carries the complete set. A cache-restored module carrying
/// pre-enrichment sparse `callees` would silently starve the S101
/// dependent-recompilation transaction's affected-set closure
/// (`design/int/session-transaction.md` §3.2 — the reverse index is derived
/// from these edges). The bump rejects every v10 cache as
/// `CacheStale::SchemaMismatch` (cache-miss → recompile) so every loaded
/// table's edges are extraction-current by construction. **One bump serves
/// all S101 waves** — Wave 3's manifest-key work does NOT re-bump.
///
/// **S102 bump 11 → 12 (ownership-inference carriers, CS-A — the single
/// increment-I types change).** The cached `.meta.json` serde surface gained,
/// in one change-set (`design/typecheck/ownership-inference.md` §13.1;
/// `design/arch/ownership-inference.md` §3.3): `mode_summary:
/// Option<ModeSummary>` on the callable `DefKind` variants
/// (`UserFnState::Concrete`, `Primitive`, `Constructor`, `PlatformEffect`)
/// and on `MonoDefnVariant`; advisory site-fact fields
/// (`escapes`/`confined`/`unique_static`/`provenance`) on `MonoExpr`
/// alloc/capture/projection nodes; the per-entry `value_use` mark on
/// `ModuleEntry::Def`; and the FIXME-0476 `DefKind::Primitive` reshape
/// (`got_slot: usize` → `body: PrimitiveBody::{Extern{got_slot,
/// borrowed_sibling_slot}, Inline}` — a non-additive variant-payload change,
/// the part that makes this bump mandatory rather than serde-default-safe).
/// All additive fields are `#[serde(default)]` = the Decision-24 conservative
/// point. The bump rejects every v11 cache as `CacheStale::SchemaMismatch`
/// (cache-miss → recompile). **One bump serves all of increment I** — the
/// consuming change-sets (CS-B/CS-1..4, backend B1-be..B3.x) do NOT re-bump.
///
/// **S102 bump 12 → 13 (FIXME 0519 — unified lossless mono-mangler).** The
/// monomorphised-instance mangled name changed grammar from the lossy
/// `{bare}${head-types}` to the canonical home-qualified lossless
/// `{home}/{bare}${recursive-concrete-sig}` (`design/typecheck/monomorphisation.md`
/// §3.5). The mangled name IS the persisted symbol-table entry key / `.meta.json`
/// identity and the `LinkerSymbol` the GOT-slot dispatch resolves against, so a
/// v12 cache carrying old-grammar mono keys would mis-resolve. The bump rejects
/// every v12 cache as `CacheStale::SchemaMismatch` (cache-miss → recompile). No
/// other cascade — the name is an opaque `String`/`LinkerSymbol` at every crate
/// boundary (no `public-api.txt`, no `cranelisp-types`, no interfaces change).
///
/// **S102 bump 13 → 14 (FIXME 0520 — result-mode partial-param-return cure).**
/// The pass5 ownership analysis no longer collapses a param returned through a
/// PARTIAL control-flow path to `ResultMode::Fresh`; such a callable's persisted
/// `ModeSummary.result` changes value (`Fresh` → `AliasOf(i)`/`ProjectionOf(i)`).
/// A stale v13 `.meta.json` written between 0519 and 0520 carries the pre-cure
/// `Fresh`. The backend's B3.2 `Apply`-body restriction guards the DIRECT case
/// (a partial-return body is an `if`/`match`, never a direct `Apply`, so its own
/// codegen never trusts `result`), but NOT the CROSS-MODULE composition: a
/// post-0520 caller whose body IS a direct `Apply` `(f v)` reading an imported,
/// stale `f.result = Fresh` would elide its return protect and free a returned
/// param → UAF. The bump rejects every v13 cache as `CacheStale::SchemaMismatch`
/// (cache-miss → recompute the correct summary). Serde shape is UNCHANGED (a
/// value-only change); the bump is a soundness invalidation, not a format change.
pub const CACHE_SCHEMA_VERSION: u32 = 14;

/// Compile-time build identifier (Sprint 60 Workstream C).
///
/// Emitted by `build.rs` as `<pkg_version>+<git_sha>` (e.g. `0.1.0+3b2df720fe63`),
/// stamped onto `.meta.json` next to `schema_version`, and compared on cache-load.
/// Mismatch routes through the same `CacheStale` fall-through as a schema-version
/// bump or a source-mtime change.
///
/// **This is an ADDITIONAL cache-invalidation trigger, not a substitute for the
/// manual `CACHE_SCHEMA_VERSION` bump that Decision 34 requires on explicit
/// serialised-shape changes.** The build-id catches the "I rebuilt the compiler
/// and forgot the cache was keyed on the old shape" class of mystery; it does
/// NOT replace the discipline of bumping `CACHE_SCHEMA_VERSION` whenever a
/// `SymbolTable` / `ModuleEntry` field is deleted, retyped, or renamed. Both
/// triggers coexist: shape changes that also rebuild the compiler hit the
/// build-id gate first; shape changes that land without a compiler-side rebuild
/// (cross-branch cache reuse) are caught only by the schema-version gate.
///
/// Pre-Sprint-60 `.meta.json` files lack the `build_id` field; they deserialise
/// with the `#[serde(default)]` empty string, which never matches a non-empty
/// `BUILD_ID` and routes through the same fall-through path.
pub const BUILD_ID: &str = env!("CRANELISP_BUILD_ID");

/// **SUPERSEDED (Sprint 58 §14.2)**: renamed to `CACHE_SCHEMA_VERSION` so
/// `/int`'s `symbol-table-cache.md` and Decision 34 use one term. The semantic
/// is unchanged. Kept as an alias so `tests/cache.rs` (owned by `/qa`)
/// continues to compile during the Wave 2b parallel migration. Doc-only
/// deprecation: a `#[deprecated]` attribute would surface warnings inside
/// files this crate is forbidden to edit.
pub const CACHE_FORMAT_VERSION: u32 = CACHE_SCHEMA_VERSION;

/// Compute the cache directory path for module files.
///
/// Module hierarchy maps to filesystem directories:
///   `core.numerics` -> `core/numerics.{meta.json,o}`
///   `user` -> `user.{meta.json,o}`
///   entry module -> `_entry.{meta.json,o}`
pub fn module_cache_path(
    cache_dir: &std::path::Path,
    module_path: &cranelisp_types::ModuleFullPath,
) -> (std::path::PathBuf, std::path::PathBuf) {
    let (dir, stem) = module_dir_and_stem(module_path);
    let base = if dir.is_empty() {
        cache_dir.to_path_buf()
    } else {
        cache_dir.join(dir)
    };
    (
        base.join(format!("{stem}.meta.json")),
        base.join(format!("{stem}.o")),
    )
}

/// Split a module path into (directory, stem) components.
/// `core.numerics` -> ("core", "numerics")
/// `user` -> ("", "user")
/// Root/entry -> ("", "_entry")
fn module_dir_and_stem(module_path: &cranelisp_types::ModuleFullPath) -> (String, String) {
    let path_str: &str = module_path.as_ref();
    if path_str.is_empty() || path_str == "_root" || path_str == "_entry" {
        return (String::new(), "_entry".to_string());
    }
    if let Some(dot_pos) = path_str.rfind('.') {
        let dir = path_str[..dot_pos].replace('.', "/");
        let stem = path_str[dot_pos + 1..].to_string();
        (dir, stem)
    } else {
        (String::new(), path_str.to_string())
    }
}

/// Result of loading a cached module from disk.
///
/// Contains all the metadata needed to restore a module into the compilation
/// session without re-parsing, expanding macros, or type-checking. The `/int`
/// pipeline installs these into the TypeChecker and codegen state.
///
/// **Sprint 22 scope**: Metadata-only cache. On cache hit, the symbol table
/// and module structure are restored from `.meta.json`, allowing downstream
/// modules to typecheck against this module's exports. Codegen is still
/// re-done from source (fast compared to full pipeline). Full `.o` loading
/// via the Linker is deferred to a future sprint.
#[derive(Debug, Clone)]
#[allow(deprecated)]
pub struct CachedModule {
    /// The deserialized module metadata (symbol table, structure, codegen state).
    ///
    /// **Note (Sprint 58 §14.4)**: this field still typed as `CacheMetadata`
    /// for back-compat during Wave 2b. New callers should consume
    /// `cached.symbol_table()` directly and ignore the envelope. The envelope
    /// dissolves when the `/int` worker migrates to the `load_meta` API.
    pub metadata: serialize::CacheMetadata,
    /// Path to the `.meta.json` file (for diagnostics).
    pub meta_path: std::path::PathBuf,
    /// Path to the `.o` file (may not exist yet in metadata-only mode).
    pub object_path: std::path::PathBuf,
    /// Whether a valid `.o` file exists on disk.
    pub has_object: bool,
}

#[allow(deprecated)]
impl CachedModule {
    /// Get the restored symbol table.
    pub fn symbol_table(&self) -> &cranelisp_types::SymbolTable {
        &self.metadata.symbol_table
    }

    /// Extract the set of module paths this cached module imports from.
    ///
    /// Scans Import entries in the symbol table and collects the unique
    /// source module paths. The orchestration layer uses this to
    /// recursively load transitive dependencies from cache.
    ///
    /// Excludes `primitives` and `macros` (synthetic compiler modules)
    /// since they are always available without cache loading.
    pub fn imported_modules(&self) -> std::collections::HashSet<cranelisp_types::ModuleFullPath> {
        let mut modules = std::collections::HashSet::new();
        for (_name, entry) in self.metadata.symbol_table.all_symbols() {
            if let cranelisp_types::ModuleEntry::Import { source, .. } = entry {
                let mod_path = &source.module;
                // Skip synthetic compiler modules.
                if mod_path.as_ref() != "primitives" && mod_path.as_ref() != "macros" {
                    modules.insert(mod_path.clone());
                }
            }
        }
        modules
    }
}

/// Attempt to load a cached module from disk.
///
/// Returns `Ok(Some(CachedModule))` if the `.meta.json` exists and is valid.
/// Returns `Ok(None)` if the cache files are missing or corrupt (cache miss).
/// Returns `Err` only on unexpected I/O errors.
///
/// The caller (pipeline) is responsible for:
/// 1. Checking the manifest first via `check_manifest()` to confirm the
///    module's source hash is current.
/// 2. Installing the returned `CachedModule` into the TypeChecker.
/// 3. Deciding whether to skip codegen (if `.o` exists) or recompile
///    (metadata-only mode).
///
/// **Cache-load/fresh-compile equivalence invariant**: The deserialized
/// `SymbolTable` must have the same entries as a freshly typechecked module.
/// This is enforced structurally: both paths feed the same
/// `install_module_scope()` function in the pipeline.
#[allow(deprecated)]
pub fn try_load_cached_module(
    cache_dir: &std::path::Path,
    module_path: &cranelisp_types::ModuleFullPath,
) -> Result<Option<CachedModule>, cranelisp_types::CranelispError> {
    let (meta_path, object_path) = module_cache_path(cache_dir, module_path);

    // Use the authoritative `load_meta` API; treat any `CacheStale` variant
    // as a cache miss (§14.7 — every variant maps to "fall through to fresh
    // build" caller-side).
    let symbol_table = match serialize::load_meta(&meta_path) {
        Ok(t) => t,
        Err(_stale) => return Ok(None),
    };

    // Validate the module path matches (defense against file mix-ups)
    if symbol_table.path != *module_path {
        return Ok(None);
    }

    // Check for .o file existence (for future full-cache-hit path)
    let has_object = object_path.exists()
        && std::fs::metadata(&object_path)
            .map(|m| m.len() > 0)
            .unwrap_or(false);

    // Wrap the symbol table back into the deprecated `CacheMetadata` envelope
    // for back-compat with the `CachedModule { metadata }` field shape. Once
    // `/int` migrates `try_cache_hit_load` to consume `SymbolTable` directly,
    // this wrapper goes away with `CacheMetadata` itself.
    let metadata = serialize::CacheMetadata {
        symbol_table,
        dependencies: Vec::new(),
    };

    Ok(Some(CachedModule {
        metadata,
        meta_path,
        object_path,
        has_object,
    }))
}

/// Load a cached module's `.o` file into the linker and return function addresses.
///
/// This is the entry point for `/int` to use on cache hit with `has_object: true`.
/// It reads the `.o` file, loads it into the linker (resolving relocations against
/// registered symbols), and returns a map of function name → code pointer for
/// wiring into the live GOT.
///
/// **Prerequisites** (the caller must ensure before calling):
/// 1. All external symbols the `.o` references are registered with the linker:
///    - Runtime intrinsics (`linker.register_symbol("runtime/alloc", ptr)`)
///    - Functions from already-loaded modules (topo order guarantees this)
///    - GOT base pointers for already-compiled modules
/// 2. The `CachedModule` was loaded via `try_load_cached_module()` and
///    `has_object` is `true`.
///
/// **After calling**, the caller should wire the returned function pointers
/// into the live GOT using the slot assignments from `cached.codegen_state().got_slots`.
///
/// Returns a map of function name → code pointer (`*const u8`).
#[allow(deprecated)]
pub fn load_cached_object(
    linker: &mut linker::Linker,
    cached: &CachedModule,
) -> Result<std::collections::HashMap<String, *const u8>, cranelisp_types::CranelispError> {
    let obj_bytes = std::fs::read(&cached.object_path).map_err(|e| {
        cranelisp_types::CranelispError::CodegenError {
            message: format!(
                "failed to read cached object file '{}': {e}",
                cached.object_path.display()
            ),
            location: ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
        }
    })?;

    let module_name = cached.metadata.symbol_table.path.as_ref().to_string();
    linker.load_object(&module_name, &obj_bytes)?;

    // Collect function addresses from the linker's defined_symbols.
    // Function names with GOT slots are on ModuleEntry::Def in the symbol table.
    let mut fn_addrs = std::collections::HashMap::new();
    for (name, entry) in cached.symbol_table().all_symbols() {
        if entry.callable_got_slot().is_some()
            && let Ok(addr) = linker.get_symbol(name.as_ref())
        {
            fn_addrs.insert(name.as_ref().to_string(), addr);
        }
    }

    Ok(fn_addrs)
}

/// Atomic file write: write to temp file then rename.
/// Prevents concurrent readers from seeing partial writes.
pub(crate) fn atomic_write(
    path: &std::path::Path,
    data: &[u8],
) -> std::io::Result<()> {
    use std::io::Write;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let tmp_path = path.with_extension("tmp");
    let mut f = std::fs::File::create(&tmp_path)?;
    f.write_all(data)?;
    f.sync_all()?;
    std::fs::rename(&tmp_path, path)?;
    Ok(())
}

#[cfg(test)]
#[allow(deprecated)]
mod tests;
