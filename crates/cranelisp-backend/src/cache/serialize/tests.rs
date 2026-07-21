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

/// S110 W0 bump guard (0583, KC-W0-3): a `.meta.json` stamped at schema
/// version 18 — written before the `resolved_targets` sidecar +
/// `MonoExpr::{Var,Apply}.resolved_target` carriers landed — MUST be rejected
/// as `CacheStale::SchemaMismatch` against the bumped `CACHE_SCHEMA_VERSION`
/// (19), so the caller recompiles rather than deserialising `None` carriers
/// that (post-W1) would hard-fail the backend's keyed read. The three carrier
/// additions are `#[serde(default)]` but their fresh-build value on a
/// table-reference node is `Some`, NOT the default — the exempt-default class
/// does not apply, so the wholesale invalidation is required.
// spec: design/arch/backend-keyed-consumer.md §8 (the pinned W0 diff — cache 18→19)
#[test]
fn cache_v18_meta_rejected_after_resolved_target_carriers() {
    // The bump must actually have happened — a v18 cache must be stale now.
    const {
        assert!(
            super::super::CACHE_SCHEMA_VERSION >= 19,
            "S110 0583 carriers require CACHE_SCHEMA_VERSION bumped past 18"
        );
    }

    let dir = tempfile::tempdir().unwrap();
    let meta_path = dir.path().join("user.meta.json");

    // Emit a sidecar stamped at the legacy v18 (current build_id, so only the
    // schema version differs — isolating the schema-mismatch route).
    let mut table = SymbolTable::new(ModuleFullPath::from("user"));
    table.insert(Symbol::from("callable"), make_def("callable"));
    write_meta(&meta_path, &table, 18).unwrap();

    let bytes = std::fs::read(&meta_path).unwrap();
    let result =
        deserialise_meta(&bytes, super::super::CACHE_SCHEMA_VERSION, &meta_path);
    match result {
        Err(CacheStale::SchemaMismatch { found, expected, .. }) => {
            assert_eq!(found, 18, "the stale cache was stamped at v18");
            assert_eq!(
                expected,
                super::super::CACHE_SCHEMA_VERSION,
                "rejected against the current (bumped) schema version"
            );
        }
        // Crucially NOT Ok(table): a v18 cache must never load post-carrier.
        other => panic!(
            "v18 cache must be rejected as SchemaMismatch (cache-miss), got {other:?}"
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

// (The deprecated `CacheMetadata` round-trip / read-nonexistent tests were
// removed with the envelope + its shims at S111 CS-5, FIXME 0634 — the
// authoritative `write_meta`/`load_meta` round-trip is covered above.)

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

/// Build a Def carrying an arbitrary GOT slot (used to forge an out-of-range
/// slot the on-disk cache would otherwise never legally hold).
fn make_def_with_slot(slot: usize) -> ModuleEntry {
    let mut entry = make_def("x");
    if let ModuleEntry::Def { kind, .. } = &mut entry {
        **kind = DefKind::UserFn {
            fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
        };
    }
    entry
}

// spec: 12-runtime §12.2 — GOT exhaustion / out-of-range slot at the ONE
// untrusted GOT-index boundary (GE-3, backend cache-load validation). A
// corrupt / hand-edited `.meta.json` carrying `got_slot >= GOT_TABLE_SIZE` is
// the only path to an out-of-range index once allocation is checked at the seam.
// The cache-load seam validates each restored callable's slot and treats a
// violation as cache-stale (→ recompile) — a diagnosed recovery, NEVER a panic
// on disk content (which the always-on `store_slot`/`load_slot` assert would be).
#[test]
fn cache_load_rejects_out_of_range_got_slot_as_stale() {
    let dir = tempfile::tempdir().unwrap();
    let meta_path = dir.path().join("corrupt.meta.json");

    // A well-formed within-bounds slot loads cleanly.
    let mut ok_table = SymbolTable::new(ModuleFullPath::from("corrupt"));
    ok_table.insert(Symbol::from("f"), make_def_with_slot(cranelisp_types::GOT_TABLE_SIZE - 1));
    write_meta(&meta_path, &ok_table, super::super::CACHE_SCHEMA_VERSION).unwrap();
    load_meta(&meta_path).expect("in-bounds slot must load");

    // Forge a cache with an out-of-range slot (== GOT_TABLE_SIZE, the first
    // illegal index) and confirm the load refuses it as cache-stale.
    let mut bad_table = SymbolTable::new(ModuleFullPath::from("corrupt"));
    bad_table.insert(Symbol::from("f"), make_def_with_slot(cranelisp_types::GOT_TABLE_SIZE));
    write_meta(&meta_path, &bad_table, super::super::CACHE_SCHEMA_VERSION).unwrap();

    match load_meta(&meta_path) {
        Err(CacheStale::GotSlotOutOfRange { slot, .. }) => {
            assert_eq!(slot, cranelisp_types::GOT_TABLE_SIZE, "reports the offending slot");
        }
        other => panic!("expected GotSlotOutOfRange cache-stale, got {other:?}"),
    }
}

// =============================================================================
// R6 — the persisted-index trust boundary (S115 W3 change-set 4)
//
// `design/arch/safety-invariants.md` §4 R6 + the census table in this module's
// rustdoc + `tests/plan/s115-test-plan.md` §6.1. Each cell corrupts ONE
// persisted index and asserts its OWN `CacheStale` class (the classes must be
// distinct — a diagnosis has to name the family that failed), plus the
// false-fire fence: a valid meta with every index populated round-trips clean.
//
// Each cell fails on revert of its validation arm: without the arm the corrupt
// meta LOADS, and the assertion that it was refused fails.
// =============================================================================

/// A primitive Def carrying an `Extern` body with the R5 borrowed-sibling slot
/// forged to `slot` — the second GOT-index family.
fn make_primitive_with_sibling_slot(slot: usize) -> ModuleEntry {
    let mut entry = make_def("p");
    if let ModuleEntry::Def { kind, .. } = &mut entry {
        **kind = DefKind::Primitive {
            body: cranelisp_types::PrimitiveBody::Extern {
                got_slot: 3,
                borrowed_sibling_slot: Some(slot),
            },
            mode_summary: None,
        };
    }
    entry
}

/// A Def whose ownership summary declares `MayAliasOf(index)` over a signature
/// of `arity` parameters.
fn make_def_with_may_alias(index: usize, arity: usize) -> ModuleEntry {
    make_def_with_result_mode(cranelisp_types::ResultMode::MayAliasOf(index), arity)
}

/// A `Def` carrying an arbitrary `ResultMode` at a given arity — the per-variant
/// matrix driver (FIXME 0750: the census must cover EVERY index-carrying
/// variant, not just the one that happens to be read through a checked
/// accessor).
fn make_def_with_result_mode(result: cranelisp_types::ResultMode, arity: usize) -> ModuleEntry {
    let mut entry = make_def("m");
    if let ModuleEntry::Def { kind, scheme, param_names, .. } = &mut entry {
        scheme.ty = Type::Fn(vec![Type::Int; arity], Box::new(Type::Int));
        *param_names = (0..arity).map(|i| Symbol::from(format!("p{i}"))).collect();
        **kind = DefKind::UserFn {
            fn_state: UserFnState::Concrete {
                got_slot: 1,
                mode_summary: Some(cranelisp_types::ModeSummary {
                    result,
                    ..Default::default()
                }),
            },
        };
    }
    entry
}

fn make_def_with_callee(module: &str, symbol: &str) -> ModuleEntry {
    let mut entry = make_def("c");
    if let ModuleEntry::Def { callees, .. } = &mut entry {
        *callees = vec![FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(symbol),
        }];
    }
    entry
}

fn make_def_with_view_span(start: u32, end: u32) -> ModuleEntry {
    let mut entry = make_def("v");
    if let ModuleEntry::Def { codegen_view, .. } = &mut entry {
        *codegen_view = Some(cranelisp_types::MonoDefnVariant {
            name: Symbol::from("v"),
            params: vec![],
            body: cranelisp_types::MonoExpr::IntLit {
                value: 1,
                span: TSpan::SYNTHETIC,
                ty: cranelisp_types::ConcreteType::Int,
            },
            span: TSpan { start, end },
            mode_summary: None,
        });
    }
    entry
}

/// Write a one-entry table and attempt to load it back.
fn roundtrip(dir: &std::path::Path, name: &str, entry: ModuleEntry) -> Result<SymbolTable, CacheStale> {
    let meta_path = dir.join(format!("{name}.meta.json"));
    let mut table = SymbolTable::new(ModuleFullPath::from("r6"));
    table.insert(Symbol::from(name), entry);
    write_meta(&meta_path, &table, super::super::CACHE_SCHEMA_VERSION).unwrap();
    load_meta(&meta_path)
}

// spec: design/arch/safety-invariants.md §4 R6 — the R5 borrowed-sibling slot is
// a GOT index like any other; an out-of-range value on disk must be diagnosed at
// load, not left to panic in `store_slot`/`load_slot` when its first consumer
// reads it (the co-landing rule — validation lands now, the CONSUMER stays
// parked per FIXME 0637).
#[test]
fn cache_load_rejects_out_of_range_sibling_slot_as_stale() {
    let dir = tempfile::tempdir().unwrap();
    roundtrip(dir.path(), "ok", make_primitive_with_sibling_slot(cranelisp_types::GOT_TABLE_SIZE - 1))
        .expect("an in-bounds sibling slot must load");
    match roundtrip(dir.path(), "bad", make_primitive_with_sibling_slot(cranelisp_types::GOT_TABLE_SIZE)) {
        Err(CacheStale::SiblingSlotOutOfRange { slot, .. }) => {
            assert_eq!(slot, cranelisp_types::GOT_TABLE_SIZE);
        }
        other => panic!("expected SiblingSlotOutOfRange, got {other:?}"),
    }
}

// spec: design/arch/safety-invariants.md §4 R6 — a persisted
// `ResultMode::MayAliasOf(k)` with `k >= arity` is the `arg_origins[k]` OOB read
// the register row names. Boundary-exact: `k == arity - 1` loads, `k == arity`
// is refused.
#[test]
fn cache_load_rejects_out_of_range_summary_param_index_as_stale() {
    let dir = tempfile::tempdir().unwrap();
    roundtrip(dir.path(), "ok", make_def_with_may_alias(1, 2))
        .expect("MayAliasOf(arity-1) is in range and must load");
    match roundtrip(dir.path(), "bad", make_def_with_may_alias(2, 2)) {
        Err(CacheStale::SummaryParamIndexOutOfRange { index, arity, .. }) => {
            assert_eq!((index, arity), (2, 2), "reports the offending index + arity");
        }
        other => panic!("expected SummaryParamIndexOutOfRange, got {other:?}"),
    }
    // A nullary callable with ANY MayAliasOf is out of range by construction.
    assert!(matches!(
        roundtrip(dir.path(), "nullary", make_def_with_may_alias(0, 0)),
        Err(CacheStale::SummaryParamIndexOutOfRange { .. })
    ));
}

// spec: design/arch/safety-invariants.md §4 R6 / FIXME 0750 — the census must
// cover EVERY index-carrying `ResultMode` variant, not one of the three.
// `ProjectionOf` is the sharp one: the consume seam reads `arg_origins` through
// a CHECKED `.get(k)` for all three, but then does a RAW `args[k]` index for the
// projection arm (`cranelisp-typecheck/src/ownership/transfer.rs`) — so the one
// genuine panic-on-disk-content path in the family was the unvalidated variant.
// Per-variant matrix, boundary-exact, so a future fourth variant cannot escape.
#[test]
fn cache_load_rejects_out_of_range_index_for_every_result_mode_variant() {
    use cranelisp_types::ResultMode;
    let dir = tempfile::tempdir().unwrap();
    for make in [
        ResultMode::ProjectionOf as fn(usize) -> ResultMode,
        ResultMode::AliasOf,
        ResultMode::MayAliasOf,
    ] {
        roundtrip(dir.path(), "ok", make_def_with_result_mode(make(1), 2))
            .unwrap_or_else(|e| panic!("{:?} at arity-1 must load, got {e:?}", make(1)));
        match roundtrip(dir.path(), "bad", make_def_with_result_mode(make(2), 2)) {
            Err(CacheStale::SummaryParamIndexOutOfRange { index, arity, .. }) => {
                assert_eq!((index, arity), (2, 2));
            }
            other => panic!("expected SummaryParamIndexOutOfRange for {:?}, got {other:?}", make(2)),
        }
        assert!(
            matches!(
                roundtrip(dir.path(), "nullary", make_def_with_result_mode(make(0), 0)),
                Err(CacheStale::SummaryParamIndexOutOfRange { .. })
            ),
            "a nullary callable carrying {:?} is out of range by construction",
            make(0)
        );
    }
}

// spec: §4 R6 (NEGATIVE / false-fire fence) — `ResultMode::Fresh` carries NO
// index, so it must load at every arity including nullary.
#[test]
fn index_free_result_mode_is_never_rejected_neg() {
    let dir = tempfile::tempdir().unwrap();
    for arity in [0usize, 1, 3] {
        roundtrip(dir.path(), "fresh", make_def_with_result_mode(cranelisp_types::ResultMode::Fresh, arity))
            .expect("Fresh carries no index and must always load");
    }
}

// spec: design/arch/safety-invariants.md §4 R6 — a `callees` FQ with an empty
// module or symbol component is not a nameable key; it would corrupt resolution
// and the reverse who-calls-whom index the dependent-recompilation transaction
// derives from these edges.
#[test]
fn cache_load_rejects_malformed_callee_fq_as_stale() {
    let dir = tempfile::tempdir().unwrap();
    roundtrip(dir.path(), "ok", make_def_with_callee("user", "f"))
        .expect("a well-formed callee FQ must load");
    for (module, symbol) in [("", "f"), ("user", ""), ("", "")] {
        match roundtrip(dir.path(), "bad", make_def_with_callee(module, symbol)) {
            Err(CacheStale::MalformedCalleeFq { .. }) => {}
            other => panic!("expected MalformedCalleeFq for ({module:?}, {symbol:?}), got {other:?}"),
        }
    }
}

// spec: design/arch/safety-invariants.md §4 R6 — an inverted persisted span
// (`start > end`) yields an out-of-source slice / keyed-read miss at the
// diagnostic seam.
#[test]
fn cache_load_rejects_malformed_span_as_stale() {
    let dir = tempfile::tempdir().unwrap();
    roundtrip(dir.path(), "ok", make_def_with_view_span(3, 9))
        .expect("a well-formed span must load");
    roundtrip(dir.path(), "empty", make_def_with_view_span(4, 4))
        .expect("an EMPTY (start == end) span is well-formed and must load");
    match roundtrip(dir.path(), "bad", make_def_with_view_span(9, 3)) {
        Err(CacheStale::MalformedSpanKey { start, end, .. }) => {
            assert_eq!((start, end), (9, 3));
        }
        other => panic!("expected MalformedSpanKey, got {other:?}"),
    }
}

// spec: design/arch/safety-invariants.md §4 R6 (FALSE-FIRE FENCE) — a valid meta
// with EVERY persisted index populated at a legal value round-trips untouched.
// Without this, an over-eager arm could reject healthy caches and the only
// symptom would be a silent permanent recompile.
#[test]
fn cache_load_accepts_a_valid_meta_with_every_persisted_index_populated() {
    let dir = tempfile::tempdir().unwrap();
    let meta_path = dir.path().join("all.meta.json");
    let mut table = SymbolTable::new(ModuleFullPath::from("r6"));
    table.insert(Symbol::from("slot"), make_def_with_slot(cranelisp_types::GOT_TABLE_SIZE - 1));
    table.insert(
        Symbol::from("sib"),
        make_primitive_with_sibling_slot(cranelisp_types::GOT_TABLE_SIZE - 2),
    );
    table.insert(Symbol::from("alias"), make_def_with_may_alias(0, 1));
    table.insert(Symbol::from("callee"), make_def_with_callee("user", "f"));
    table.insert(Symbol::from("view"), make_def_with_view_span(0, 12));
    write_meta(&meta_path, &table, super::super::CACHE_SCHEMA_VERSION).unwrap();
    let loaded = load_meta(&meta_path).expect("a fully-populated valid meta must load clean");
    assert_eq!(loaded.symbols.len(), 5);
}

// spec: design/arch/safety-invariants.md §4 R6 — the classes are DISTINCT, so a
// diagnosis names the family that failed rather than collapsing every corrupt
// index onto one reason string.
#[test]
fn r6_stale_classes_are_distinct_per_family() {
    let dir = tempfile::tempdir().unwrap();
    let reasons: Vec<&'static str> = vec![
        roundtrip(dir.path(), "a", make_def_with_slot(cranelisp_types::GOT_TABLE_SIZE)),
        roundtrip(dir.path(), "b", make_primitive_with_sibling_slot(cranelisp_types::GOT_TABLE_SIZE)),
        roundtrip(dir.path(), "c", make_def_with_may_alias(5, 1)),
        roundtrip(dir.path(), "d", make_def_with_callee("", "f")),
        roundtrip(dir.path(), "e", make_def_with_view_span(9, 1)),
    ]
    .into_iter()
    .map(|r| r.expect_err("each forged index must be refused").reason())
    .collect();
    let unique: std::collections::HashSet<_> = reasons.iter().collect();
    assert_eq!(
        unique.len(),
        reasons.len(),
        "each persisted-index family needs its OWN CacheStale class; got {reasons:?}"
    );
}
