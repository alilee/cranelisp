// Module metadata serialization for the cache.
//
// Sprint 58 Step 5b — Per `design/backend/module-caching.md` §14 (PRESCRIPTIVE):
// the `.meta.json` file IS a serialised `SymbolTable<(), ()>`. The pre-Phase-5
// `CacheMetadata` envelope dissolves; runtime fields (`code`, `got`,
// `linker`) are `#[serde(skip)]` on the symbol table itself and are
// re-derived on cache-hit by re-running codegen against `ast` and re-resolving
// platform DLLs. The schema_version field on `SymbolTable` (Decision 34) is
// the cache invalidation handshake.
//
// Authoritative API (use these in new code):
//   - `serialise_meta(table, schema_version) -> Vec<u8>`
//   - `deserialise_meta(bytes) -> Result<SymbolTable, CacheStale>`
//   - `write_meta(path, table, schema_version) -> Result<(), CacheError>`
//   - `load_meta(path) -> Result<SymbolTable, CacheStale>`
//
// The legacy `CacheMetadata` envelope and its companion functions
// (`read_cached_metadata`, `write_cached_metadata`) are retained as
// `#[deprecated]` shims that delegate to the new API, so that `/int`-owned
// (`src/session_v4.rs`) and `/qa`-owned (`tests/cache.rs`) call sites can
// migrate at their own pace within Sprint 58 Wave 2b–3. They must be removed
// when those files migrate.

use std::path::Path;

use serde::{Deserialize, Serialize};

use cranelisp_types::{ErrorLocation, CranelispError, ModuleFullPath, Span, SymbolTable};

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
///   §14.3 step [5]. (The runtime address for each addressable callable is
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
mod tests {
    use super::*;
    use cranelisp_types::{DefKind, Defn, DefnVariant, Expr, FQSymbol, ImportSpec, ModuleEntry, ModuleFullPath,
        Scheme, Span as TSpan, Symbol, Type, Visibility,
    };
    use std::collections::HashMap;

    fn make_def(name: &str) -> ModuleEntry {
        let defn = Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 42,
                    span: TSpan::new(10, 12),
                    inferred_type: None,
                },
                span: TSpan::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: TSpan::new(0, 20),
        };
        ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: vec![],
            got_slot: Some(7),
            trait_origin: None,
            ast: Some(defn),
            code: None,
        }
    }

    /// G.11 Test 1 (test plan §G.11) — cache_meta_json_is_serialised_symbol_table
    ///
    /// Per design/backend/module-caching.md §14.1: `.meta.json` IS a
    /// serialised `SymbolTable`. Write a populated table with schema_version
    /// stamped, deserialise, assert structural identity (modulo `#[serde(skip)]`
    /// fields).
    // spec: design/backend/module-caching.md §14.1
    #[test]
    fn cache_meta_json_is_serialised_symbol_table() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("user.meta.json");

        let mut table = SymbolTable::new(ModuleFullPath::from("user"));
        table.insert(Symbol::from("answer"), make_def("answer"));

        write_meta(&meta_path, &table, super::super::CACHE_SCHEMA_VERSION).unwrap();
        let loaded = load_meta(&meta_path).expect("cache load should succeed");

        assert_eq!(loaded.path, table.path);
        assert_eq!(loaded.symbols.len(), 1);
        assert!(loaded.symbols.contains_key(&Symbol::from("answer")));
        assert_eq!(
            loaded.schema_version,
            super::super::CACHE_SCHEMA_VERSION,
            "schema_version must match after round-trip"
        );

        // Confirm the persisted bytes never contain pointer fields (§14.1):
        let json_str = std::fs::read_to_string(&meta_path).unwrap();
        assert!(
            !json_str.contains("\"code\""),
            "ModuleEntry::Def.code is #[serde(skip)] — must not appear: {json_str}"
        );
        assert!(
            !json_str.contains("\"fn_ptr\""),
            "ModuleEntry::Def has no `fn_ptr` field (Sprint 66 Wave 0 amendment); must not appear"
        );
    }

    /// G.11 Test 2 (test plan §G.11) — cache_schema_version_mismatch_falls_through
    ///
    /// Per design/backend/module-caching.md §14.3 step [3]: schema mismatch
    /// returns `CacheStale::SchemaMismatch` so the caller can route through
    /// the same fall-through code path as dep-hash mismatch (§14.7).
    // spec: design/arch/CLAUDE.md Decision 34
    #[test]
    fn cache_schema_version_mismatch_falls_through() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("user.meta.json");

        // Write at version 0, load at version 1.
        let table = SymbolTable::new(ModuleFullPath::from("user"));
        write_meta(&meta_path, &table, 0).unwrap();

        // Direct deserialise with explicit version mismatch:
        let bytes = std::fs::read(&meta_path).unwrap();
        let result = deserialise_meta(&bytes, 1, &meta_path);
        match result {
            Err(CacheStale::SchemaMismatch { found, expected, .. }) => {
                assert_eq!(found, 0);
                assert_eq!(expected, 1);
            }
            other => panic!("expected SchemaMismatch, got {other:?}"),
        }

        // Synthesise a u32::MAX mismatch as in test plan §G.11:
        let mut tampered = SymbolTable::new(ModuleFullPath::from("user"));
        tampered.schema_version = u32::MAX;
        let tampered_bytes = serde_json::to_vec(&tampered).unwrap();
        let result = deserialise_meta(
            &tampered_bytes,
            super::super::CACHE_SCHEMA_VERSION,
            &meta_path,
        );
        assert!(
            matches!(result, Err(CacheStale::SchemaMismatch { found: u32::MAX, .. })),
            "u32::MAX schema_version must produce SchemaMismatch (not Err / not panic)"
        );
    }

    /// Per task: write-then-read round-trip. Full multi-field SymbolTable
    /// round-trips byte-identical (modulo skipped fields). Covers the §14.6
    /// symmetry invariant.
    // spec: design/backend/module-caching.md §14.6
    #[test]
    fn cache_round_trip_multi_field_symbol_table() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("multi.meta.json");

        let mut table = SymbolTable::new(ModuleFullPath::from("multi"));
        table.insert(Symbol::from("answer"), make_def("answer"));
        table.insert(Symbol::from("relay"), make_def("relay"));
        table.insert(
            Symbol::from("dep-val"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("other"),
                    symbol: Symbol::from("dep-val"),
                },
            },
        );
        table.next_got_slot = 13;

        // Populate structural-decl fields (Wave 2a additions per Decision 33).
        table.imports.push(ImportSpec {
            module_path: ModuleFullPath::from("other"),
            alias: None,
            names: cranelisp_types::ImportNames::Specific(vec![Symbol::from("dep-val")]),
            span: TSpan::new(0, 30),
        });

        // Round-trip via the authoritative API.
        write_meta(&meta_path, &table, super::super::CACHE_SCHEMA_VERSION).unwrap();
        let loaded = load_meta(&meta_path).expect("cache load should succeed");

        // Identity on every persisted field (modulo #[serde(skip)] runtime state).
        assert_eq!(loaded.path, table.path);
        assert_eq!(loaded.symbols.len(), table.symbols.len());
        assert_eq!(loaded.next_got_slot, table.next_got_slot);
        assert_eq!(loaded.imports.len(), table.imports.len());
        assert_eq!(loaded.exports.len(), table.exports.len());
        assert_eq!(loaded.platforms.len(), table.platforms.len());
        assert_eq!(loaded.submodules.len(), table.submodules.len());
        assert_eq!(loaded.schema_version, super::super::CACHE_SCHEMA_VERSION);

        // The first ImportSpec round-trips on its module + names shape.
        assert_eq!(loaded.imports[0].module_path, table.imports[0].module_path);

        // Round-trip is idempotent: re-writing produces the same bytes.
        let bytes_a = serialise_meta(&loaded, super::super::CACHE_SCHEMA_VERSION).unwrap();
        let bytes_b = serialise_meta(&loaded, super::super::CACHE_SCHEMA_VERSION).unwrap();
        assert_eq!(bytes_a, bytes_b, "serialisation must be deterministic");
    }

    /// load_meta on a missing file returns `CacheStale::Missing`, not an
    /// uncategorised error.
    // spec: design/backend/module-caching.md §14.7
    #[test]
    fn load_meta_missing_file_returns_cache_stale_missing() {
        let dir = tempfile::tempdir().unwrap();
        let absent = dir.path().join("nope.meta.json");
        let err = load_meta(&absent).expect_err("missing file should be CacheStale");
        assert!(matches!(err, CacheStale::Missing { .. }), "got {err:?}");
        assert_eq!(err.reason(), "missing");
    }

    /// load_meta on corrupt bytes returns `CacheStale::Deserialise`, not a
    /// panic. Mirrors the §14.7 invariant that all failure modes flow through
    /// the discriminator.
    // spec: design/backend/module-caching.md §14.7
    #[test]
    fn load_meta_corrupt_bytes_returns_cache_stale_deserialise() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("corrupt.meta.json");
        super::super::atomic_write(&path, b"not valid json").unwrap();
        let err = load_meta(&path).expect_err("corrupt bytes should be CacheStale");
        assert!(matches!(err, CacheStale::Deserialise { .. }), "got {err:?}");
        assert_eq!(err.reason(), "deserialise");
    }

    // -- Deprecated shim coverage (kept compiling for /int + /qa migration window) --

    #[allow(deprecated)]
    #[test]
    fn deprecated_metadata_round_trip_still_works() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("legacy.meta.json");
        let original = CacheMetadata {
            symbol_table: SymbolTable::new(ModuleFullPath::from("legacy")),
            dependencies: Vec::new(),
        };
        write_cached_metadata(&meta_path, &original).unwrap();
        let loaded = read_cached_metadata(&meta_path).unwrap();
        assert_eq!(loaded.symbol_table.path, ModuleFullPath::from("legacy"));
    }

    #[allow(deprecated)]
    #[test]
    fn deprecated_read_nonexistent_returns_error() {
        let result = read_cached_metadata(Path::new("/nonexistent/path/test.meta.json"));
        assert!(result.is_err());
    }

    // -- Sprint 60 Workstream C: compile-time build-id gate --

    /// The compile-time `BUILD_ID` const is emitted by `build.rs` as
    /// `<pkg_version>+<git_sha>`. It MUST be non-empty so that pre-Sprint-60
    /// caches (which carry `""` via `#[serde(default)]`) always invalidate.
    // spec: sprints/SPRINT.md §Workstream C
    #[test]
    fn build_id_const_is_nonempty_and_well_formed() {
        let id = super::super::BUILD_ID;
        assert!(!id.is_empty(), "BUILD_ID must not be empty");
        assert!(id.contains('+'), "BUILD_ID must be <pkg_version>+<sha>: {id}");
    }

    /// Fresh-build round-trip: the current `BUILD_ID` stamps in, load succeeds.
    // spec: sprints/SPRINT.md §Workstream C
    #[test]
    fn build_id_round_trip_succeeds() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("user.meta.json");
        let table = SymbolTable::new(ModuleFullPath::from("user"));
        write_meta(&meta_path, &table, super::super::CACHE_SCHEMA_VERSION).unwrap();
        let loaded = load_meta(&meta_path).expect("fresh-build cache must load");
        assert_eq!(loaded.path, table.path);
    }

    /// Pre-Sprint-60 caches lack the `build_id` field — they deserialise
    /// with `""` and MUST be rejected as `BuildIdMismatch`.
    // spec: sprints/SPRINT.md §Workstream C
    #[test]
    fn missing_build_id_field_routes_cache_stale() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("legacy.meta.json");

        // Emit a .meta.json shaped like a pre-Sprint-60 cache: serialise
        // the SymbolTable directly (no `build_id` sibling field).
        let mut table = SymbolTable::new(ModuleFullPath::from("legacy"));
        table.schema_version = super::super::CACHE_SCHEMA_VERSION;
        let bytes = serde_json::to_vec_pretty(&table).unwrap();
        super::super::atomic_write(&meta_path, &bytes).unwrap();

        let err = load_meta(&meta_path).expect_err("pre-S60 cache must be stale");
        match err {
            CacheStale::BuildIdMismatch { found, .. } => {
                assert_eq!(found, "", "legacy cache produces empty build_id");
            }
            other => panic!("expected BuildIdMismatch, got {other:?}"),
        }
    }

    /// Build-id mismatch (cache written by a different compiler build) is
    /// reported as `BuildIdMismatch`, not `SchemaMismatch` or `Deserialise`.
    // spec: sprints/SPRINT.md §Workstream C
    #[test]
    fn stale_build_id_produces_build_id_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("old.meta.json");
        let table = SymbolTable::new(ModuleFullPath::from("old"));

        // Write with a synthetic build-id that will never match live `BUILD_ID`.
        let bytes = serialise_meta_with_build_id(
            &table,
            super::super::CACHE_SCHEMA_VERSION,
            "0.0.0+deadbeef0000",
        )
        .unwrap();
        super::super::atomic_write(&meta_path, &bytes).unwrap();

        let err = load_meta(&meta_path).expect_err("stale-build-id cache must be stale");
        match err {
            CacheStale::BuildIdMismatch { found, expected, .. } => {
                assert_eq!(found, "0.0.0+deadbeef0000");
                assert_eq!(expected, super::super::BUILD_ID);
            }
            other => panic!("expected BuildIdMismatch, got {other:?}"),
        }
    }

    /// Schema mismatch takes precedence over build-id mismatch — a shape
    /// change strictly subsumes a compiler-binary change, and the schema
    /// check runs first.
    // spec: sprints/SPRINT.md §Workstream C (check-order discipline)
    #[test]
    fn schema_mismatch_shadows_build_id_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("both-stale.meta.json");
        let table = SymbolTable::new(ModuleFullPath::from("both"));

        // Both wrong schema AND wrong build-id. Caller should see
        // `SchemaMismatch` (the shape-safety check is primary).
        let bytes = serialise_meta_with_build_id(&table, 99_999, "0.0.0+deadbeef0000").unwrap();
        super::super::atomic_write(&meta_path, &bytes).unwrap();

        let err = load_meta(&meta_path).expect_err("schema mismatch must invalidate");
        assert!(
            matches!(err, CacheStale::SchemaMismatch { .. }),
            "schema check must fire before build-id check; got {err:?}"
        );
    }

    /// `BuildIdMismatch` exposes a stable diagnostic reason string so
    /// callers can log / branch on it without matching the variant.
    // spec: sprints/SPRINT.md §Workstream C
    #[test]
    fn build_id_mismatch_has_diagnostic_reason() {
        let err = CacheStale::BuildIdMismatch {
            path: std::path::PathBuf::from("/tmp/x.meta.json"),
            found: "a".to_string(),
            expected: "b".to_string(),
        };
        assert_eq!(err.reason(), "build_id_mismatch");
        // Display trail exposes both ids for operator diagnosis.
        let msg = format!("{err}");
        assert!(msg.contains("\"a\""), "display includes found: {msg}");
        assert!(msg.contains("\"b\""), "display includes expected: {msg}");
    }
}
