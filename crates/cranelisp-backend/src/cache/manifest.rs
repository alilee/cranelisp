// Cache manifest: module->hash mapping and global invalidation keys.
//
// The manifest is a single JSON file at the root of the cache directory.
// It provides O(1) cache-hit checks without reading every module's metadata.
//
// See design/backend/module-caching.md §3 for the cache key design.

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
            module_path.0.clone(),
            CachedModuleRef {
                source_hash,
                dependency_hashes,
            },
        );
    }

    /// Remove a module entry.
    pub fn remove_module(&mut self, module_path: &ModuleFullPath) {
        self.modules.remove(&module_path.0);
    }

    /// Look up a module's cached reference.
    pub fn get_module(&self, module_path: &ModuleFullPath) -> Option<&CachedModuleRef> {
        self.modules.get(&module_path.0)
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
        match entry.dependency_hashes.get(&dep_path.0) {
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
        }
    }
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

/// Read the cache manifest from disk. Returns None if file doesn't exist
/// or cannot be parsed.
pub fn read_manifest(cache_dir: &Path) -> Option<CacheManifest> {
    let path = cache_dir.join("manifest.json");
    let content = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&content).ok()
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
mod tests {
    use super::*;

    // spec: design/backend/module-caching.md §3 — SHA-256 source hashing
    #[test]
    fn test_hash_source_deterministic() {
        let h1 = hash_source("(defn foo [x] x)");
        let h2 = hash_source("(defn foo [x] x)");
        assert_eq!(h1, h2);
    }

    // spec: design/backend/module-caching.md §3 — different source produces different hash
    #[test]
    fn test_hash_source_different_input() {
        let h1 = hash_source("(defn foo [x] x)");
        let h2 = hash_source("(defn bar [x] x)");
        assert_ne!(h1, h2);
    }

    // spec: design/backend/module-caching.md §3 — hash is 64 hex chars (SHA-256)
    #[test]
    fn test_hash_source_length() {
        let h = hash_source("hello");
        assert_eq!(h.len(), 64);
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
    }

    // spec: design/backend/module-caching.md §3 — empty source produces valid hash
    #[test]
    fn test_hash_source_empty() {
        let h = hash_source("");
        assert_eq!(h.len(), 64);
    }

    // spec: design/backend/module-caching.md §3 — binary fingerprint is memoized
    #[test]
    fn test_binary_fingerprint_stable() {
        let fp1 = binary_fingerprint();
        let fp2 = binary_fingerprint();
        assert_eq!(fp1, fp2);
    }

    // spec: design/backend/module-caching.md §3 — manifest round-trip
    #[test]
    fn test_manifest_round_trip() {
        let dir = tempfile::tempdir().unwrap();
        let mut manifest = CacheManifest::new("aarch64-apple-darwin");
        let mp = ModuleFullPath::from("core.numerics");
        let mut deps = HashMap::new();
        deps.insert("prelude".to_string(), hash_source("prelude source"));
        manifest.upsert_module(&mp, hash_source("source"), deps);

        write_manifest(dir.path(), &manifest).unwrap();
        let loaded = read_manifest(dir.path()).unwrap();

        assert_eq!(loaded.cache_format_version, CACHE_FORMAT_VERSION);
        assert_eq!(loaded.target_triple, "aarch64-apple-darwin");
        let entry = loaded.get_module(&mp).unwrap();
        assert_eq!(entry.source_hash, hash_source("source"));
        assert_eq!(
            entry.dependency_hashes.get("prelude").unwrap(),
            &hash_source("prelude source")
        );
    }

    // spec: design/backend/module-caching.md §3 — check_manifest with valid cache
    #[test]
    fn test_check_manifest_valid() {
        let triple = target_lexicon::Triple::host().to_string();
        let mut manifest = CacheManifest::new(&triple);
        let mp = ModuleFullPath::from("user");
        let source_hash = hash_source("(defn main [] 42)");
        manifest.upsert_module(&mp, source_hash.clone(), HashMap::new());

        let result = check_manifest(&manifest, &mp, &source_hash, &HashMap::new());
        assert!(result.unwrap());
    }

    // spec: design/backend/module-caching.md §3 — check_manifest with changed source
    #[test]
    fn test_check_manifest_source_changed() {
        let triple = target_lexicon::Triple::host().to_string();
        let mut manifest = CacheManifest::new(&triple);
        let mp = ModuleFullPath::from("user");
        manifest.upsert_module(&mp, hash_source("old source"), HashMap::new());

        let result = check_manifest(&manifest, &mp, &hash_source("new source"), &HashMap::new());
        assert!(!result.unwrap());
    }

    // spec: design/backend/module-caching.md §3 — check_manifest with changed dependency
    #[test]
    fn test_check_manifest_dependency_changed() {
        let triple = target_lexicon::Triple::host().to_string();
        let mut manifest = CacheManifest::new(&triple);
        let mp = ModuleFullPath::from("user");
        let source_hash = hash_source("user source");
        let mut dep_hashes = HashMap::new();
        dep_hashes.insert("prelude".to_string(), hash_source("old prelude"));
        manifest.upsert_module(&mp, source_hash.clone(), dep_hashes);

        let mut current_deps = HashMap::new();
        current_deps.insert(
            ModuleFullPath::from("prelude"),
            hash_source("new prelude"),
        );
        let result = check_manifest(&manifest, &mp, &source_hash, &current_deps);
        assert!(!result.unwrap());
    }

    // spec: design/backend/module-caching.md §3 — check_manifest with format version mismatch
    #[test]
    fn test_check_manifest_format_version_mismatch() {
        let triple = target_lexicon::Triple::host().to_string();
        let mut manifest = CacheManifest::new(&triple);
        manifest.cache_format_version = 999;
        let mp = ModuleFullPath::from("user");

        let result = check_manifest(&manifest, &mp, "hash", &HashMap::new());
        assert!(result.is_err());
    }

    // spec: design/backend/module-caching.md §3 — check_manifest with uncached module
    #[test]
    fn test_check_manifest_uncached_module() {
        let triple = target_lexicon::Triple::host().to_string();
        let manifest = CacheManifest::new(&triple);
        let mp = ModuleFullPath::from("unknown");

        let result = check_manifest(&manifest, &mp, "hash", &HashMap::new());
        assert!(!result.unwrap());
    }

    // spec: design/backend/module-caching.md §3 — manifest upsert replaces existing
    #[test]
    fn test_manifest_upsert_replaces() {
        let mut manifest = CacheManifest::new("test");
        let mp = ModuleFullPath::from("mod");
        manifest.upsert_module(&mp, "hash1".to_string(), HashMap::new());
        manifest.upsert_module(&mp, "hash2".to_string(), HashMap::new());
        assert_eq!(manifest.get_module(&mp).unwrap().source_hash, "hash2");
    }
}
