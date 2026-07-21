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
//! (`read_cached_metadata`, `write_cached_metadata`) were REMOVED at S111 CS-5
//! (FIXME 0634) — the on-disk format has been SymbolTable-direct since Sprint 58
//! Wave 2b; the envelope lingered only as an in-memory `CachedModule` wrapper.
//!
//! # R6 — the persisted-index trust boundary (the census)
//!
//! `design/arch/safety-invariants.md` §4 R6: *every index / key / slot
//! deserialised from `.meta.json` is validated at load; a violation is a
//! diagnosed [`CacheStale`], never trusted into emission.* Cache bytes are
//! **external data** (§2 tier-3 trust-boundary sub-form) — so every arm below
//! DIAGNOSES and recompiles; none of them `assert!` (contrast the in-process
//! `store_slot`/`load_slot` asserts, where an out-of-range index is a compiler
//! invariant breach).
//!
//! There is exactly ONE validation site — the per-entry loop in
//! `deserialise_meta_with_build_id` — and ONE pass over
//! `SymbolTable::all_symbols()`. Each family is a cheap field check with its own
//! `CacheStale` class, so a diagnosis names the family that failed.
//!
//! | Persisted index | Corrupt-bytes hazard | Validation arm | `CacheStale` class |
//! |---|---|---|---|
//! | `callable_got_slot()` | OOB slot → `store_slot`/`load_slot` `assert!` panics on disk content | `< GOT_TABLE_SIZE` | [`CacheStale::GotSlotOutOfRange`] |
//! | `PrimitiveBody::Extern.borrowed_sibling_slot` (R5 carrier) | OOB → the same GOT panic when its first consumer reads it | `< GOT_TABLE_SIZE` when present | [`CacheStale::SiblingSlotOutOfRange`] |
//! | summary param index — `ResultMode::{ProjectionOf,AliasOf,MayAliasOf}(k)` | `k ≥ arity` → a raw `args[k]` index PANIC at the consume seam (see below) | `k < arity` (signature arity, `param_names` fallback), all three variants | [`CacheStale::SummaryParamIndexOutOfRange`] |
//! | `Def.callees` FQs (feeds the reverse who-calls-whom index) | empty module/symbol component → resolve / reverse-index corruption | non-empty module AND symbol | [`CacheStale::MalformedCalleeFq`] |
//! | `codegen_view` span | `start > end` → out-of-source slice / keyed-read miss at the diagnostic seam | `start ≤ end` | [`CacheStale::MalformedSpanKey`] |
//!
//! **Where the summary index actually panics (FIXME 0750 — the row above used
//! to name the wrong site and cover only one of the three variants).** At the
//! consume seam (`cranelisp-typecheck/src/ownership/transfer.rs`) the
//! `arg_origins` reads are CHECKED for all three variants
//! (`.get(k)…unwrap_or(Origin::Fresh)`), so no OOB is possible there. The
//! `ProjectionOf` arm then additionally does a **raw `args[k]` index** to
//! recover the container span — that is the one genuine panic-on-disk-content
//! path in the family, and it belonged to the variant the census originally
//! omitted. Validating here closes it at the trust boundary; the raw index
//! itself is a typecheck-side concern (validation at one boundary is not a
//! licence for an unchecked read at the consumer, Principle 25) and is routed
//! there separately — the backend cannot fix a cross-crate site.
//!
//! **Scope note (kept honest).** The typecheck-side span-keyed sidecars
//! (`MethodResolutions::{resolved_calls, var_refs, apply_refs, pattern_ctors}`)
//! are NOT persisted — they are consumed when the mono view is built, and the
//! S114 typed-carrier flip moved their content ONTO the `MonoExpr` nodes. The
//! spans that survive into `.meta.json` therefore ride inside `codegen_view` as
//! diagnostic locations, not as lookup keys; the row above validates the view's
//! own span, and per-node spans are deliberately NOT walked (the one-pass,
//! no-allocation constraint — a deep walk over every mono body at every cache
//! load is not a cheap field check).
//!
//! **Maintenance rule (R6).** Any NEW persisted index adds its row here AND its
//! arm in the loop, in the same change-set that introduces the index. `/review`
//! verifies census completeness against this table — no persisted index may
//! escape a row.

use std::path::Path;

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
    /// A restored entry carried a `borrowed_sibling_slot >= GOT_TABLE_SIZE`
    /// (S115 W3 change-set 4; R6 census row 2). The R5 sibling-slot carrier is
    /// a GOT index like any other: an out-of-range value on disk would reach the
    /// always-on `store_slot`/`load_slot` `assert!` as a panic on disk content
    /// when its first consumer reads it. Validated at load defensively (the
    /// co-landing rule); the CONSUMER itself stays parked to its first reader
    /// (FIXME 0637 / the re-affirmed R5 ruling).
    SiblingSlotOutOfRange {
        path: std::path::PathBuf,
        slot: usize,
    },
    /// A restored ownership summary carried an index-carrying `ResultMode`
    /// (`ProjectionOf`/`AliasOf`/`MayAliasOf`) with `k >= arity` (S115 W3
    /// change-set 4; R6 census row 3, widened to all three variants by FIXME
    /// 0750). The consume seam reads `arg_origins` through a checked `.get(k)`
    /// but the `ProjectionOf` arm then indexes `args[k]` raw — an out-of-range
    /// `k` from disk panics there, which is the hazard this row exists for.
    SummaryParamIndexOutOfRange {
        path: std::path::PathBuf,
        index: usize,
        arity: usize,
    },
    /// A restored entry carried a malformed `callees` FQ — an empty module or
    /// symbol component (S115 W3 change-set 4; R6 census row 4). The `callees`
    /// edge set feeds resolution and the reverse who-calls-whom index; an empty
    /// component is not a nameable key and would corrupt both.
    MalformedCalleeFq {
        path: std::path::PathBuf,
        symbol: String,
    },
    /// A restored mono codegen view carried a malformed span (`start > end`)
    /// (S115 W3 change-set 4; R6 census row 5). Spans locate diagnostics and key
    /// the producer-side sidecars; an inverted span yields a keyed-read miss or
    /// an out-of-source slice at the diagnostic seam.
    MalformedSpanKey {
        path: std::path::PathBuf,
        symbol: String,
        start: u32,
        end: u32,
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
            CacheStale::SiblingSlotOutOfRange { .. } => "sibling_slot_out_of_range",
            CacheStale::SummaryParamIndexOutOfRange { .. } => {
                "summary_param_index_out_of_range"
            }
            CacheStale::MalformedCalleeFq { .. } => "malformed_callee_fq",
            CacheStale::MalformedSpanKey { .. } => "malformed_span_key",
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
            CacheStale::SiblingSlotOutOfRange { path, slot } => write!(
                f,
                "cache borrowed-sibling GOT slot out of range at {}: slot {slot} >= \
                 {GOT_TABLE_SIZE}",
                path.display()
            ),
            CacheStale::SummaryParamIndexOutOfRange { path, index, arity } => write!(
                f,
                "cache ownership summary param index out of range at {}: \
                 result mode index {index} with arity {arity}",
                path.display()
            ),
            CacheStale::MalformedCalleeFq { path, symbol } => write!(
                f,
                "cache malformed callee FQ at {}: entry {symbol} carries a callee with \
                 an empty module or symbol component",
                path.display()
            ),
            CacheStale::MalformedSpanKey { path, symbol, start, end } => write!(
                f,
                "cache malformed span at {}: entry {symbol} codegen view span \
                 {start}..{end} is inverted",
                path.display()
            ),
        }
    }
}

/// The persisted param index a [`ResultMode`](cranelisp_types::ResultMode)
/// carries, or `None` for the index-free point — the R6 census's
/// compile-enforced completeness instrument (FIXME 0750).
///
/// Exhaustive on purpose: adding a variant to `ResultMode` breaks THIS build
/// until its index-carrying-ness is decided, which is what a census must be
/// (the prose table above documents; this match enforces).
pub(crate) fn result_mode_param_index(result: cranelisp_types::ResultMode) -> Option<usize> {
    use cranelisp_types::ResultMode;
    match result {
        ResultMode::Fresh => None,
        ResultMode::ProjectionOf(k) | ResultMode::AliasOf(k) | ResultMode::MayAliasOf(k) => Some(k),
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
    //
    // S115 W3 change-set 4 (R6, `design/arch/safety-invariants.md` §4) — this is
    // the ONE per-entry validation loop for EVERY persisted index; each family
    // below is one cheap field check with its own `CacheStale` class. The census
    // it implements is the module rustdoc table above; a NEW persisted index adds
    // its row + its arm HERE, in the same change-set that introduces it (the R6
    // maintenance rule). Never a parallel walk, and never an `assert!`: cache
    // bytes are EXTERNAL data (the tier-3 trust-boundary sub-form) — diagnose and
    // recompile.
    for (sym, entry) in table.all_symbols() {
        if let Some(slot) = entry.callable_got_slot()
            && slot >= GOT_TABLE_SIZE
        {
            return Err(CacheStale::GotSlotOutOfRange {
                path: path.to_path_buf(),
                slot,
            });
        }
        if let cranelisp_types::ModuleEntry::Def { kind, .. } = entry
            && let cranelisp_types::DefKind::Primitive {
                body:
                    cranelisp_types::PrimitiveBody::Extern {
                        borrowed_sibling_slot: Some(slot),
                        ..
                    },
                ..
            } = kind.as_ref()
            && *slot >= GOT_TABLE_SIZE
        {
            return Err(CacheStale::SiblingSlotOutOfRange {
                path: path.to_path_buf(),
                slot: *slot,
            });
        }
        // EVERY index-carrying `ResultMode` variant (FIXME 0750). All three are
        // persisted through the same `ModeSummary.result` field and read
        // positionally against the same arg vector — a per-variant arm was the
        // coverage-by-definition-variants miss, and it happened to validate the
        // one variant whose consumer reads are all checked.
        //
        // `result_mode_param_index` is an EXHAUSTIVE match (no `_ =>`) — the
        // standing instrument: a NEW `ResultMode` variant is a compile error
        // here until someone decides whether it carries a param index, rather
        // than silently escaping the census the prose table describes.
        if let Some(summary) = entry.mode_summary()
            && let Some(k) = result_mode_param_index(summary.result)
        {
            // Arity from the persisted signature — the same positional vector
            // the consume seam's `arg_origins` is built over. The `param_names`
            // list is the fallback for entries whose scheme is not a `Fn` shape.
            let arity = match entry {
                cranelisp_types::ModuleEntry::Def { scheme, param_names, .. } => {
                    match &scheme.ty {
                        cranelisp_types::Type::Fn(params, _) => params.len(),
                        _ => param_names.len(),
                    }
                }
                _ => 0,
            };
            if k >= arity {
                return Err(CacheStale::SummaryParamIndexOutOfRange {
                    path: path.to_path_buf(),
                    index: k,
                    arity,
                });
            }
        }
        for callee in entry.callees() {
            if callee.module.as_ref().is_empty() || callee.symbol.as_ref().is_empty() {
                return Err(CacheStale::MalformedCalleeFq {
                    path: path.to_path_buf(),
                    symbol: sym.to_string(),
                });
            }
        }
        if let Some(view) = entry.codegen_view()
            && view.span.start > view.span.end
        {
            return Err(CacheStale::MalformedSpanKey {
                path: path.to_path_buf(),
                symbol: sym.to_string(),
                start: view.span.start,
                end: view.span.end,
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
// The deprecated `CacheMetadata` envelope + its `read_cached_metadata` /
// `write_cached_metadata` shims were REMOVED at S111 CS-5 (FIXME 0634). The
// on-disk `.meta.json` has been a SymbolTable-direct serialisation since
// Sprint 58 Wave 2b (`serialise_meta` / `deserialise_meta` / `write_meta` /
// `load_meta`); the envelope was only an in-memory back-compat wrapper on
// `CachedModule`, now dissolved.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
