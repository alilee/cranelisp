//! Sidecar (`.meta.json`) serialisation + `CacheStale` discrimination.
//!
//! Per `design/backend/module-caching.md` §14: the `.meta.json` file IS a
//! serialised `SymbolTable<(), ()>` (Decision 25 — types, schemes, AST bodies,
//! GOT slot layout, structural decls). Runtime fields (`code`, `got`, `linker`)
//! are `#[serde(skip)]` and re-derived on cache-hit. The `schema_version` field
//! (Decision 34) is the cache-invalidation handshake.
//!
//! **Forbidden pattern — no serde-shape change without a `CACHE_SCHEMA_VERSION`
//! bump.** Any change to a `#[derive(Serialize, Deserialize)]` shape that
//! affects on-disk bytes MUST bump `super::CACHE_SCHEMA_VERSION`;
//! [`deserialise_meta`] rejects mismatched versions with
//! [`CacheStale::SchemaMismatch`] and the caller treats it as a cache miss.
//! Skipping the bump silently corrupts user cache directories — fail-loud over
//! fail-silent.
//!
//! Authoritative API (use these in new code):
//!   - `serialise_meta(table, schema_version) -> Vec<u8>`
//!   - `deserialise_meta(bytes, expected_schema_version, path) -> Result<SymbolTable, CacheStale>`
//!   - `write_meta(path, table, schema_version) -> Result<(), CranelispError>`
//!   - `load_meta(path) -> Result<SymbolTable, CacheStale>`
//!
//! The legacy `CacheMetadata` envelope and its companion functions
//! (`read_cached_metadata`, `write_cached_metadata`) are retained as
//! `#[deprecated]` shims that delegate to the new API so remaining call sites
//! can migrate at their own pace; they are removed when those files migrate.

use std::path::Path;

use serde::{Deserialize, Serialize};

use cranelisp_types::{
    ErrorLocation, CranelispError, GOT_TABLE_SIZE, ModuleFullPath, Span, SymbolTable,
};

// ---------------------------------------------------------------------------
// CacheStale — failure-mode discriminator (Sprint 58 §14.7)
// ---------------------------------------------------------------------------

/// Reason a cache load did not produce a usable `SymbolTable`.
///
/// Every variant maps to the same caller-visible behaviour: invalidate, fall
/// through to a fresh build, write a new cache entry. The discriminator exists
/// for diagnostics and tests, not for branching control flow. See
/// `design/backend/module-caching.md` §14.7.
#[derive(Debug, Clone)]
pub enum CacheStale {
    /// `.meta.json` file was not present on disk.
    Missing { path: std::path::PathBuf },
    /// `schema_version` on disk did not match `CACHE_SCHEMA_VERSION`
    /// (Decision 34). This is the primary cache-versioning gate.
    SchemaMismatch {
        path: std::path::PathBuf,
        found: u32,
        expected: u32,
    },
    /// `build_id` on disk did not match the compile-time `BUILD_ID`
    /// (Sprint 60 Workstream C). Additional invalidation trigger on top of
    /// `SchemaMismatch`; catches silent cache staleness when the compiler
    /// binary is rebuilt without a manual `CACHE_SCHEMA_VERSION` bump.
    BuildIdMismatch {
        path: std::path::PathBuf,
        found: String,
        expected: String,
    },
    /// I/O failure reading the file (permissions, disk error, etc.).
    Io {
        path: std::path::PathBuf,
        message: String,
    },
    /// Bytes did not deserialise as a `SymbolTable` (corrupt or
    /// schema-incompatible in a way the version sniff didn't catch).
    Deserialise {
        path: std::path::PathBuf,
        message: String,
    },
    /// The deserialised table's `path` field did not match the expected
    /// module path (defence against file mix-ups).
    PathMismatch {
        path: std::path::PathBuf,
        expected: ModuleFullPath,
        found: ModuleFullPath,
    },
    /// A restored entry carried a `got_slot >= GOT_TABLE_SIZE` — the one
    /// untrusted GOT-index source (S111 R7). With allocation checked at the
    /// seam, an out-of-range slot can only enter from a corrupt or hand-edited
    /// `.meta.json`; treating it as cache-stale (→ recompile) is the diagnosed
    /// recovery, never a panic on disk content nor a later OOB GOT access.
    GotSlotOutOfRange {
        path: std::path::PathBuf,
        slot: usize,
    },
}

impl CacheStale {
    /// Short reason name for diagnostics / logging.
    pub fn reason(&self) -> &'static str {
        match self {
            CacheStale::Missing { .. } => "missing",
            CacheStale::SchemaMismatch { .. } => "schema_mismatch",
            CacheStale::BuildIdMismatch { .. } => "build_id_mismatch",
            CacheStale::Io { .. } => "io",
            CacheStale::Deserialise { .. } => "deserialise",
            CacheStale::PathMismatch { .. } => "path_mismatch",
            CacheStale::GotSlotOutOfRange { .. } => "got_slot_out_of_range",
        }
    }
}

impl std::fmt::Display for CacheStale {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CacheStale::Missing { path } => {
                write!(f, "cache file missing: {}", path.display())
            }
            CacheStale::SchemaMismatch {
                path,
                found,
                expected,
            } => write!(
                f,
                "cache schema mismatch at {}: found {found}, expected {expected}",
                path.display()
            ),
            CacheStale::BuildIdMismatch {
                path,
                found,
                expected,
            } => write!(
                f,
                "cache build-id mismatch at {}: found {found:?}, expected {expected:?}",
                path.display()
            ),
            CacheStale::Io { path, message } => {
                write!(f, "cache I/O error at {}: {message}", path.display())
            }
            CacheStale::Deserialise { path, message } => write!(
                f,
                "cache deserialise error at {}: {message}",
                path.display()
            ),
            CacheStale::PathMismatch {
                path,
                expected,
                found,
            } => write!(
                f,
                "cache path mismatch at {}: expected {expected}, found {found}",
                path.display()
            ),
            CacheStale::GotSlotOutOfRange { path, slot } => write!(
                f,
                "cache GOT slot out of range at {}: slot {slot} >= {GOT_TABLE_SIZE}",
                path.display()
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Authoritative API — operates directly on SymbolTable
// ---------------------------------------------------------------------------

/// Serialise a `SymbolTable` into the `.meta.json` byte representation.
///
/// Stamps `schema_version` on a clone of the table before serialising, so the
/// caller's table is untouched. Per Decision 34, `schema_version` is the
/// cache-invalidation handshake; the value here is what `load_meta` will
/// compare against `CACHE_SCHEMA_VERSION` on the read side.
///
/// `code`, `got`, and `linker` are `#[serde(skip)]` on
/// `SymbolTable` / `ModuleEntry::Def`, so the produced bytes never contain
/// pointer state — they are re-derived on cache-hit per §14.3. The runtime
/// address for an addressable callable lives in the GOT (per its `got_slot`)
/// and is re-populated on cache-hit by codegen / platform reload.
pub fn serialise_meta<C, L>(
    table: &SymbolTable<C, L>,
    schema_version: u32,
) -> Result<Vec<u8>, CranelispError>
where
    C: cranelisp_types::CodeStore + Clone,
    L: cranelisp_types::LinkerStore + Clone,
{
    serialise_meta_with_build_id(table, schema_version, super::BUILD_ID)
}

/// Serialise a `SymbolTable` with an explicit `build_id` (Sprint 60 W/S C).
///
/// Separated from `serialise_meta` so tests can stamp synthetic build-ids
/// without shelling out to the compile-time `BUILD_ID` constant.
pub(crate) fn serialise_meta_with_build_id<C, L>(
    table: &SymbolTable<C, L>,
    schema_version: u32,
    build_id: &str,
) -> Result<Vec<u8>, CranelispError>
where
    C: cranelisp_types::CodeStore + Clone,
    L: cranelisp_types::LinkerStore + Clone,
{
    let mut stamped = table.clone();
    stamped.schema_version = schema_version;
    let mut value = serde_json::to_value(&stamped).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to serialise SymbolTable for cache: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;
    // Insert `build_id` as a sibling of `schema_version` at the JSON root.
    // This keeps `.meta.json` shape-identical to pre-Sprint-60 except for
    // the added field (which pre-Sprint-60 loaders would have ignored;
    // post-Sprint-60 loaders check it and invalidate on mismatch).
    if let Some(obj) = value.as_object_mut() {
        obj.insert(
            "build_id".to_string(),
            serde_json::Value::String(build_id.to_string()),
        );
    }
    serde_json::to_vec_pretty(&value).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to serialise SymbolTable for cache: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
}

/// Deserialise `.meta.json` bytes into a `SymbolTable`, gated on
/// `schema_version`.
///
/// Per §14.3:
/// * Deserialise errors → `CacheStale::Deserialise` (treat as miss).
/// * `schema_version` mismatch → `CacheStale::SchemaMismatch` (treat as miss).
/// * Success → return the table; `code` / `got` / `linker` are at their
///   default values and the caller is responsible for re-deriving them per
///   §14.3 step 5. (The runtime address for each addressable callable is
///   re-populated into the GOT slot on cache-hit by codegen / platform
///   reload — there is no separate `fn_ptr` field on the entry.)
pub fn deserialise_meta(
    bytes: &[u8],
    expected_schema_version: u32,
    path: &Path,
) -> Result<SymbolTable, CacheStale> {
    deserialise_meta_with_build_id(bytes, expected_schema_version, super::BUILD_ID, path)
}

/// Deserialise with an explicit expected `build_id` (Sprint 60 W/S C).
///
/// Check order: parse → schema_version → build_id. Schema mismatch shadows
/// build-id mismatch (a shape change strictly subsumes a build-id change),
/// but both flow through `CacheStale` so the caller routes identically.
///
/// Pre-Sprint-60 caches lack the `build_id` field; `#[serde(default)]` on
/// the capture struct yields `""` which never matches a non-empty compile-time
/// `BUILD_ID`, producing `CacheStale::BuildIdMismatch` → fresh build.
pub(crate) fn deserialise_meta_with_build_id(
    bytes: &[u8],
    expected_schema_version: u32,
    expected_build_id: &str,
    path: &Path,
) -> Result<SymbolTable, CacheStale> {
    // First: pull the `build_id` sibling off the JSON root before letting
    // serde derive the SymbolTable (SymbolTable has no `build_id` field,
    // but serde is lenient with unknown keys by default, so deserialise
    // succeeds and we only inspect the sidecar field for the version check).
    let value: serde_json::Value =
        serde_json::from_slice(bytes).map_err(|e| CacheStale::Deserialise {
            path: path.to_path_buf(),
            message: e.to_string(),
        })?;
    let found_build_id = value
        .get("build_id")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();
    let table: SymbolTable =
        serde_json::from_value(value).map_err(|e| CacheStale::Deserialise {
            path: path.to_path_buf(),
            message: e.to_string(),
        })?;
    if table.schema_version != expected_schema_version {
        return Err(CacheStale::SchemaMismatch {
            path: path.to_path_buf(),
            found: table.schema_version,
            expected: expected_schema_version,
        });
    }
    if found_build_id != expected_build_id {
        return Err(CacheStale::BuildIdMismatch {
            path: path.to_path_buf(),
            found: found_build_id,
            expected: expected_build_id.to_string(),
        });
    }
    // S111 R7 — validate every restored callable's GOT slot at the ONE
    // untrusted GOT-index boundary. Allocation is now checked at the seam, so
    // an in-process out-of-range slot is a hard-fail invariant breach; the only
    // remaining way an out-of-range index enters is a corrupt / hand-edited
    // `.meta.json`. Treat it as cache-stale (→ recompile) rather than letting it
    // reach the always-on `store_slot`/`load_slot` `assert!` as a panic on disk
    // content.
    for (_sym, entry) in table.all_symbols() {
        if let Some(slot) = entry.callable_got_slot()
            && slot >= GOT_TABLE_SIZE
        {
            return Err(CacheStale::GotSlotOutOfRange {
                path: path.to_path_buf(),
                slot,
            });
        }
    }
    Ok(table)
}

/// Write a serialised `SymbolTable` to `meta_path` atomically.
///
/// Stamps `schema_version` and writes via temp-file-then-rename to avoid
/// partial-read hazards. `meta_path`'s parent directory is created if absent.
pub fn write_meta<C, L>(
    meta_path: &Path,
    table: &SymbolTable<C, L>,
    schema_version: u32,
) -> Result<(), CranelispError>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let bytes = serialise_meta(table, schema_version)?;
    super::atomic_write(meta_path, &bytes).map_err(|e| CranelispError::CodegenError {
        message: format!(
            "failed to write cache metadata {}: {e}",
            meta_path.display()
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
}

/// Read and deserialise a `SymbolTable` from `meta_path`, gated on
/// `CACHE_SCHEMA_VERSION` (the constant owned by this crate per Decision 34).
///
/// All failure modes — missing file, I/O error, deserialise failure, schema
/// mismatch — flow through `CacheStale` so the caller (`/int`'s worker) can
/// log the discriminator and route through the same "treat as cache-miss"
/// fall-through code path used for source-mtime change.
pub fn load_meta(meta_path: &Path) -> Result<SymbolTable, CacheStale> {
    if !meta_path.exists() {
        return Err(CacheStale::Missing {
            path: meta_path.to_path_buf(),
        });
    }
    let bytes = std::fs::read(meta_path).map_err(|e| CacheStale::Io {
        path: meta_path.to_path_buf(),
        message: e.to_string(),
    })?;
    deserialise_meta(&bytes, super::CACHE_SCHEMA_VERSION, meta_path)
}

// ---------------------------------------------------------------------------
// Deprecated shims — present so that pre-Phase-5 callers in `/int`-owned
// (`src/session_v4.rs`) and `/qa`-owned (`tests/cache.rs`) files continue to
// compile during the Wave 2b parallel migration. Remove when those callers
// have all migrated to the authoritative API above.
// ---------------------------------------------------------------------------

/// Combined metadata for a cached module.
///
/// **SUPERSEDED (Sprint 58 §14.4)**: this envelope is replaced by direct
/// serialisation of `SymbolTable` (the schema_version lives on the table
/// itself per Decision 34). The `dependencies` field is no longer used by
/// the cache loader — it walked `ModuleEntry::Import` source paths anyway.
/// Use `serialise_meta` / `deserialise_meta` / `write_meta` / `load_meta`
/// instead. This shim exists so `/int`'s session_v4.rs cache-write call site
/// and `/qa`'s tests/cache.rs continue to compile during the Sprint 58
/// Wave 2b parallel migration.
///
/// No `#[deprecated]` attribute is applied because doing so would surface
/// warnings inside `/int`-owned files that this crate is forbidden to edit
/// during the Wave 2b parallel handoff. The doc-only marker here is the
/// migration signal; the type is removed when `/int` deletes its last
/// reference and `/qa` rewrites `tests/cache.rs`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheMetadata {
    pub symbol_table: SymbolTable,
    /// Module paths this module directly imports from (excluding primitives/macros).
    /// **No longer consulted** by the cache loader — kept for source compatibility.
    #[serde(default)]
    pub dependencies: Vec<String>,
}

/// Read cached module metadata from disk.
///
/// **SUPERSEDED (Sprint 58 §14.4)**: use `load_meta` which returns a
/// `SymbolTable` directly with structured `CacheStale` failure modes.
/// Doc-only deprecation per the same rationale on `CacheMetadata`.
pub fn read_cached_metadata(meta_path: &Path) -> Result<CacheMetadata, CranelispError> {
    let content = std::fs::read_to_string(meta_path).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to read cache metadata {}: {e}", meta_path.display()),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })?;
    serde_json::from_str(&content).map_err(|e| CranelispError::CodegenError {
        message: format!(
            "failed to deserialize cache metadata {}: {e}",
            meta_path.display()
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
}

/// Write cached module metadata to disk atomically.
///
/// **SUPERSEDED (Sprint 58 §14.4)**: use `write_meta` which serialises the
/// `SymbolTable` directly and stamps `schema_version`. Doc-only deprecation
/// per the same rationale on `CacheMetadata`.
pub fn write_cached_metadata(
    meta_path: &Path,
    metadata: &CacheMetadata,
) -> Result<(), CranelispError> {
    let json = serde_json::to_string_pretty(metadata).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to serialize cache metadata: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })?;
    super::atomic_write(meta_path, json.as_bytes()).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to write cache metadata {}: {e}", meta_path.display()),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
