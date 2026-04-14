// Module metadata serialization for the cache.
//
// Serializes SymbolTable as a `.meta.json` file. Deserialization
// reconstructs the symbol table for cache-load. GOT slot assignments
// are stored on ModuleEntry::Def in the SymbolTable itself.

use std::path::Path;

use serde::{Deserialize, Serialize};

use cranelisp_types::{CranelispError, Span, SymbolTable};

/// Combined metadata for a cached module.
/// This is what gets serialized to the `.meta.json` file.
///
/// GOT slot assignments and function definitions are on SymbolTable entries
/// (ModuleEntry::Def.got_slot, ModuleEntry::Def.defn). No separate codegen
/// state is needed.
///
/// `dependencies` records which modules this module imports, enabling
/// recursive cache loading of transitive dependencies.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheMetadata {
    pub symbol_table: SymbolTable,
    /// Module paths this module directly imports from (excluding primitives/macros).
    /// Populated at cache-write time so the orchestration layer can recursively
    /// load transitive dependencies on cache hit without scanning the symbol table.
    #[serde(default)]
    pub dependencies: Vec<String>,
}

/// Read cached module metadata from disk.
pub fn read_cached_metadata(
    meta_path: &Path,
) -> Result<CacheMetadata, CranelispError> {
    let content = std::fs::read_to_string(meta_path).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to read cache metadata {}: {e}", meta_path.display()),
            span: Span::SYNTHETIC,
        }
    })?;
    serde_json::from_str(&content).map_err(|e| CranelispError::CodegenError {
        message: format!(
            "failed to deserialize cache metadata {}: {e}",
            meta_path.display()
        ),
        span: Span::SYNTHETIC,
    })
}

/// Write cached module metadata to disk atomically.
pub fn write_cached_metadata(
    meta_path: &Path,
    metadata: &CacheMetadata,
) -> Result<(), CranelispError> {
    let json = serde_json::to_string_pretty(metadata).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to serialize cache metadata: {e}"),
            span: Span::SYNTHETIC,
        }
    })?;
    super::atomic_write(meta_path, json.as_bytes()).map_err(|e| {
        CranelispError::CodegenError {
            message: format!("failed to write cache metadata {}: {e}", meta_path.display()),
            span: Span::SYNTHETIC,
        }
    })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::ModuleFullPath;

    fn make_test_metadata() -> CacheMetadata {
        CacheMetadata {
            symbol_table: SymbolTable::new(ModuleFullPath::from("test")),
            dependencies: Vec::new(),
        }
    }

    // spec: design/backend/module-caching.md §4 — metadata round-trip
    #[test]
    fn test_metadata_round_trip() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("test.meta.json");

        let original = make_test_metadata();
        write_cached_metadata(&meta_path, &original).unwrap();
        let loaded = read_cached_metadata(&meta_path).unwrap();

        assert_eq!(loaded.symbol_table.path, ModuleFullPath::from("test"));
    }

    // spec: design/backend/module-caching.md §4 — read nonexistent file returns error
    #[test]
    fn test_read_nonexistent_returns_error() {
        let result = read_cached_metadata(Path::new("/nonexistent/path/test.meta.json"));
        assert!(result.is_err());
    }
}
