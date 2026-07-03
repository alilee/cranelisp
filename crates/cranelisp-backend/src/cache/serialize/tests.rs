use super::*;
use cranelisp_types::{DefKind, DefnVariant, Expr, FQSymbol, ImportSpec, ModuleEntry, ModuleFullPath,
    Scheme, Span as TSpan, Symbol, Type, UserFnState, Visibility,
};
use std::collections::HashMap;

fn make_def(_name: &str) -> ModuleEntry {
    let variant = DefnVariant {
        params: vec![],
        body: Expr::IntLit {
            value: 42,
            span: TSpan::new(10, 12),
            inferred_type: None,
        },
        span: TSpan::new(0, 20),
    };
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![], Box::new(Type::Int)),
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::UserFn {
            fn_state: UserFnState::Concrete { got_slot: 7, mode_summary: None },
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: Some(variant),
        codegen_view: None,
        code: None,
        value_use: false,
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

/// S83 Option-A reshape guard (FIXME 0356/0358): a `.meta.json` stamped at
/// the prior schema version 4 — written before the `DefKind`/`ModuleEntry::Def`
/// callability reshape — MUST be rejected as `CacheStale::SchemaMismatch`
/// against the bumped `CACHE_SCHEMA_VERSION` (now 5), so the caller treats it
/// as a cache-miss and recompiles. It must NOT deserialise a callable with a
/// missing/defaulted slot (the NULL-GOT-slot regression Principle 20
/// forecloses). The bump 4→5 is the no-serde-change-without-bump discipline
/// applied to the slot-onto-DefKind move.
// spec: design/backend/module-caching.md §"Schema versioning" (Decision 34)
#[test]
fn cache_v4_meta_rejected_after_callability_reshape() {
    // The bump must actually have happened — a v4 cache must be stale now.
    const {
        assert!(
            super::super::CACHE_SCHEMA_VERSION >= 5,
            "S83 reshape requires CACHE_SCHEMA_VERSION bumped past 4"
        );
    }

    let dir = tempfile::tempdir().unwrap();
    let meta_path = dir.path().join("user.meta.json");

    // Emit a sidecar stamped at the legacy v4 (current build_id, so only the
    // schema version differs — isolating the schema-mismatch route).
    let mut table = SymbolTable::new(ModuleFullPath::from("user"));
    table.insert(Symbol::from("callable"), make_def("callable"));
    write_meta(&meta_path, &table, 4).unwrap();

    let bytes = std::fs::read(&meta_path).unwrap();
    let result =
        deserialise_meta(&bytes, super::super::CACHE_SCHEMA_VERSION, &meta_path);
    match result {
        Err(CacheStale::SchemaMismatch { found, expected, .. }) => {
            assert_eq!(found, 4, "the stale cache was stamped at v4");
            assert_eq!(
                expected,
                super::super::CACHE_SCHEMA_VERSION,
                "rejected against the current (bumped) schema version"
            );
        }
        // Crucially NOT Ok(table): a v4 cache must never load a callable.
        other => panic!(
            "v4 cache must be rejected as SchemaMismatch (cache-miss), got {other:?}"
        ),
    }
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
            visibility: cranelisp_types::Visibility::Private,
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
