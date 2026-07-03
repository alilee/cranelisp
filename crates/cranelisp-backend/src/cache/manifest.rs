//! Cache index + validity — `module -> hash` mapping and global invalidation
//! keys.
//!
//! The manifest is a single JSON file at the root of the cache directory; it
//! provides O(1) cache-hit checks without reading every module's metadata.
//! `CacheManifest` is the **single index** (cache invariant 2): per-module
//! sidecars and objects are referenced via `CacheManifest::modules`,
//! pair-invariantly.
//!
//! `check_manifest` is the validity gate run at **every** cache-hit attempt
//! (cache invariant 3) before any `super::try_load_cached_module`; it compares
//! the compiler fingerprint, target triple, cranelift version, and format
//! version, surfacing a typed `CacheInvalidReason` on mismatch so the caller
//! recompiles.
//!
//! See `design/backend/module-caching.md` §3 for the cache key design.

use std::collections::HashMap;
use std::path::Path;
use std::sync::OnceLock;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use cranelisp_types::{ErrorLocation, CranelispError, ModuleFullPath, Span};

// `cache_format_version` is the field name on `CacheManifest` (kept stable
// for on-disk JSON compatibility). The constant value comes from
// `CACHE_SCHEMA_VERSION` post-Sprint-58 §14.2 rename.
use super::CACHE_SCHEMA_VERSION as CACHE_FORMAT_VERSION;

/// Global cache manifest. Maps module paths to source hashes and
/// stores global invalidation keys.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheManifest {
    /// Cache format version. Mismatch invalidates all caches.
    pub cache_format_version: u32,
    /// mtime-based fingerprint of the compiler binary.
    /// Invalidates all caches when the compiler is rebuilt.
    pub compiler_mtime: String,
    /// Target architecture triple (exact match via target_lexicon).
    pub target_triple: String,
    /// Cranelift version string.
    pub cranelift_version: String,
    /// The `CRANELISP_NO_OWNERSHIP` master-toggle polarity this cache was
    /// written under (`design/backend/ownership-codegen.md` §2.1/§2.3 — the
    /// S101 stage-M manifest key, pulled forward by the `/arch` S101 Phase-2
    /// ruling). A cache written analysis-ON persists moded summaries +
    /// machine code compiled against moded conventions; loading it under the
    /// other polarity would mix ABIs (the §3.1-spine leak/double-free through
    /// the cache). Flipping the toggle therefore invalidates the whole cache
    /// — a full recompile, exactly as a compiler upgrade does — making
    /// mixed-ABI caches unrepresentable (Principle 18/20). Pre-analysis
    /// (stage M) the key is inert: both polarities produce byte-identical
    /// code, but the invalidation discipline is already load-bearing as
    /// increment I's differential-oracle substrate.
    ///
    /// `#[serde(default)]`: a pre-key manifest was written pre-analysis
    /// (both polarities byte-identical), so treating it as
    /// `ownership_disabled: false` is sound — it invalidates iff the current
    /// session sets the toggle.
    #[serde(default)]
    pub ownership_disabled: bool,
    /// Per-module entries: module path -> source hash.
    pub modules: HashMap<String, CachedModuleRef>,
}

/// A single module's cache reference in the manifest.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedModuleRef {
    /// Hex-encoded SHA-256 of the module's source text.
    pub source_hash: String,
    /// Source hashes of direct dependencies at the time this module was cached.
    /// Used for transitive dependency invalidation (design doc §3).
    #[serde(default)]
    pub dependency_hashes: HashMap<String, String>,
}

impl CacheManifest {
    /// Create a new manifest for the current environment.
    pub fn new(target_triple: &str) -> Self {
        CacheManifest {
            cache_format_version: CACHE_FORMAT_VERSION,
            compiler_mtime: binary_fingerprint(),
            target_triple: target_triple.to_string(),
            cranelift_version: cranelift_version(),
            ownership_disabled: no_ownership_enabled(),
            modules: HashMap::new(),
        }
    }

    /// Create a new manifest auto-detecting the host target triple.
    pub fn new_for_host() -> Self {
        Self::new(&host_target_triple())
    }

    /// Add or update a module entry.
    pub fn upsert_module(
        &mut self,
        module_path: &ModuleFullPath,
        source_hash: String,
        dependency_hashes: HashMap<String, String>,
    ) {
        self.modules.insert(
            module_path.to_string(),
            CachedModuleRef {
                source_hash,
                dependency_hashes,
            },
        );
    }

    /// Remove a module entry.
    pub fn remove_module(&mut self, module_path: &ModuleFullPath) {
        self.modules.remove(module_path.as_ref());
    }

    /// Look up a module's cached reference.
    pub fn get_module(&self, module_path: &ModuleFullPath) -> Option<&CachedModuleRef> {
        self.modules.get(module_path.as_ref())
    }
}

/// Check whether a manifest is compatible with the current environment,
/// and whether a specific module's cache is valid.
///
/// Returns Ok(true) if the module can be loaded from cache,
/// Ok(false) if the module needs recompilation,
/// Err if the entire manifest is invalid (global key mismatch).
pub fn check_manifest(
    manifest: &CacheManifest,
    module_path: &ModuleFullPath,
    current_source_hash: &str,
    dependency_source_hashes: &HashMap<ModuleFullPath, String>,
) -> Result<bool, CacheInvalidReason> {
    // Global invalidation checks
    if manifest.cache_format_version != CACHE_FORMAT_VERSION {
        return Err(CacheInvalidReason::FormatVersion {
            cached: manifest.cache_format_version,
            current: CACHE_FORMAT_VERSION,
        });
    }

    let current_mtime = binary_fingerprint();
    if !current_mtime.is_empty()
        && !manifest.compiler_mtime.is_empty()
        && manifest.compiler_mtime != current_mtime
    {
        return Err(CacheInvalidReason::CompilerChanged);
    }

    let current_triple = host_target_triple();
    if manifest.target_triple != current_triple {
        return Err(CacheInvalidReason::TargetTriple {
            cached: manifest.target_triple.clone(),
            current: current_triple,
        });
    }

    let current_cl_version = cranelift_version();
    if manifest.cranelift_version != current_cl_version {
        return Err(CacheInvalidReason::CraneliftVersion {
            cached: manifest.cranelift_version.clone(),
            current: current_cl_version,
        });
    }

    // Ownership-toggle polarity (§2.3): a polarity flip invalidates the
    // whole cache — mixed-ownership-ABI caches are unrepresentable.
    let current_ownership_disabled = no_ownership_enabled();
    if manifest.ownership_disabled != current_ownership_disabled {
        return Err(CacheInvalidReason::OwnershipToggle {
            cached: manifest.ownership_disabled,
            current: current_ownership_disabled,
        });
    }

    // Per-module check
    let entry = match manifest.get_module(module_path) {
        Some(e) => e,
        None => return Ok(false), // Not in manifest
    };

    // Check own source hash
    if entry.source_hash != current_source_hash {
        return Ok(false);
    }

    // Check transitive dependency hashes
    for (dep_path, current_dep_hash) in dependency_source_hashes {
        match entry.dependency_hashes.get(dep_path.as_ref()) {
            Some(cached_dep_hash) if cached_dep_hash == current_dep_hash => {}
            _ => return Ok(false), // Dependency changed or new dependency
        }
    }

    Ok(true)
}

/// Reason why the cache manifest is globally invalid.
#[derive(Debug)]
pub enum CacheInvalidReason {
    FormatVersion { cached: u32, current: u32 },
    CompilerChanged,
    TargetTriple { cached: String, current: String },
    CraneliftVersion { cached: String, current: String },
    /// The `CRANELISP_NO_OWNERSHIP` master-toggle polarity flipped since the
    /// cache was written (§2.3 — wholesale invalidation; mixed-ownership-ABI
    /// caches unrepresentable).
    OwnershipToggle { cached: bool, current: bool },
}

impl std::fmt::Display for CacheInvalidReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CacheInvalidReason::FormatVersion { cached, current } => {
                write!(f, "cache format version mismatch: cached={cached}, current={current}")
            }
            CacheInvalidReason::CompilerChanged => {
                write!(f, "compiler binary changed since cache was written")
            }
            CacheInvalidReason::TargetTriple { cached, current } => {
                write!(f, "target triple mismatch: cached={cached}, current={current}")
            }
            CacheInvalidReason::CraneliftVersion { cached, current } => {
                write!(f, "Cranelift version mismatch: cached={cached}, current={current}")
            }
            CacheInvalidReason::OwnershipToggle { cached, current } => {
                write!(
                    f,
                    "CRANELISP_NO_OWNERSHIP polarity flipped since the cache was \
                     written: cached ownership_disabled={cached}, current={current} \
                     (wholesale invalidation — mixed-ownership-ABI caches are \
                     unrepresentable)"
                )
            }
        }
    }
}

// --- The CRANELISP_NO_OWNERSHIP master toggle ---

/// Read-once gate for the **`CRANELISP_NO_OWNERSHIP`** master analysis-off
/// toggle (`design/backend/ownership-codegen.md` §2.1 — sibling of
/// `CRANELISP_NO_LENIENT`; the same read-once `OnceLock` pattern as
/// `CRANELISP_NONATOMIC_RC` in `heap.rs`, so one process observes one
/// consistent polarity).
///
/// Semantics: when set, force the conservative point everywhere. Enforcement
/// is **producer-primary** — with the toggle set, typecheck's
/// `pass5_ownership` does not run (no summaries ⇒ every consumer is at the
/// Decision-24 conservative point with zero consumer-side branching; that
/// crate reads the same env when the pass lands at increment I). At stage M
/// (pre-analysis) the backend's only consumer is the cache-manifest global
/// key ([`CacheManifest::ownership_disabled`], §2.3): a polarity flip
/// invalidates the cache wholesale so mixed-ownership-ABI caches are
/// unrepresentable. Increment I's emission gates read this same fn.
pub(crate) fn no_ownership_enabled() -> bool {
    static E: OnceLock<bool> = OnceLock::new();
    *E.get_or_init(|| std::env::var_os("CRANELISP_NO_OWNERSHIP").is_some())
}

// --- Source hashing ---

/// Compute a hex-encoded SHA-256 hash of source text.
pub fn hash_source(source: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(source.as_bytes());
    let result = hasher.finalize();
    hex_encode(&result)
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// --- Binary fingerprint ---

/// Fingerprint of the running cranelisp binary based on its modification time.
/// Changes on any rebuild, ensuring cached .o files match the current codegen.
/// Memoized via OnceLock -- computed at most once per process.
pub fn binary_fingerprint() -> String {
    static FINGERPRINT: OnceLock<String> = OnceLock::new();
    FINGERPRINT
        .get_or_init(|| {
            let exe = match std::env::current_exe() {
                Ok(p) => p,
                Err(_) => return String::new(),
            };
            let meta = match std::fs::metadata(&exe) {
                Ok(m) => m,
                Err(_) => return String::new(),
            };
            let mtime = match meta.modified() {
                Ok(t) => t,
                Err(_) => return String::new(),
            };
            let duration = mtime
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default();
            format!("mtime-{}.{}", duration.as_secs(), duration.subsec_nanos())
        })
        .clone()
}

/// Get the host target triple as a string.
/// Uses target_lexicon for exact matching (addresses sketch MED-6).
fn host_target_triple() -> String {
    target_lexicon::Triple::host().to_string()
}

/// Get the Cranelift version string.
fn cranelift_version() -> String {
    // cranelift-codegen exposes VERSION
    cranelift_codegen::VERSION.to_string()
}

// --- Manifest I/O ---

/// Read the cache manifest from disk. Returns None if file doesn't exist,
/// cannot be parsed, or was written under the OTHER `CRANELISP_NO_OWNERSHIP`
/// polarity.
///
/// The polarity gate here (not only in [`check_manifest`]) is what makes the
/// §2.3 invalidation CONVERGE: the session loads the on-disk manifest into
/// memory at startup and re-writes that same object (global keys preserved)
/// after recompiles — so an other-polarity manifest surviving the load would
/// be flushed back with the stale polarity and the next same-polarity run
/// would still miss. Treating it as absent starts the session from a fresh
/// manifest stamped with the current polarity ([`CacheManifest::new`]):
/// wholesale invalidation on the flip run, ordinary cache hits on the next
/// same-polarity run. Mixed-ownership-ABI caches are unrepresentable
/// (Principle 18/20).
pub fn read_manifest(cache_dir: &Path) -> Option<CacheManifest> {
    let path = cache_dir.join("manifest.json");
    let content = std::fs::read_to_string(path).ok()?;
    let manifest: CacheManifest = serde_json::from_str(&content).ok()?;
    if manifest.ownership_disabled != no_ownership_enabled() {
        return None;
    }
    Some(manifest)
}

/// Write the cache manifest to disk atomically.
pub fn write_manifest(
    cache_dir: &Path,
    manifest: &CacheManifest,
) -> Result<(), CranelispError> {
    std::fs::create_dir_all(cache_dir).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to create cache dir: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;
    let path = cache_dir.join("manifest.json");
    let json = serde_json::to_string_pretty(manifest).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to serialize manifest: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })?;
    super::atomic_write(&path, json.as_bytes()).map_err(|e| CranelispError::CodegenError {
        message: format!("failed to write manifest: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;
    Ok(())
}

#[cfg(test)]
mod tests;
