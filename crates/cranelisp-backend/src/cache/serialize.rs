// Module metadata serialization for the cache.
//
// Serializes SymbolTable + ModuleStructure + CacheCodegenState as a
// combined `.meta.json` file. Deserialization reconstructs these types
// for cache-load.
//
// See design/backend/module-caching.md §4 for format details.

use std::collections::HashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use cranelisp_types::{
    CranelispError, ModuleStructure, Span, Symbol, SymbolTable,
};

use crate::codegen_types::DefCodegen;

/// Codegen state that is serialized alongside the symbol table.
///
/// Contains GOT slot assignments, function parameter counts, and
/// REPL introspection data. This is the serializable subset of
/// `ModuleCodegenState` -- runtime pointers are reconstructed from
/// the `.o` file on load.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheCodegenState {
    /// GOT slot assignments: function name -> slot index.
    pub got_slots: HashMap<Symbol, usize>,
    /// Next available GOT slot (for continuing slot allocation on reload).
    pub next_got_slot: usize,
    /// Per-definition introspection data (source, sexp, defn, param_count).
    /// code_ptr, clif_ir, disasm, compile_duration are not serialized --
    /// they are runtime artifacts reconstructed from the .o file.
    pub def_entries: HashMap<Symbol, SerializedDefEntry>,
}

/// Serializable subset of DefCodegen for REPL introspection.
/// Runtime-only fields (code_ptr, clif_ir, disasm, compile_duration) are omitted.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializedDefEntry {
    pub got_slot: Option<usize>,
    pub source: Option<String>,
    pub sexp: Option<cranelisp_types::Sexp>,
    pub defn: Option<cranelisp_types::Defn>,
    pub param_count: Option<usize>,
}

impl From<&DefCodegen> for SerializedDefEntry {
    fn from(dc: &DefCodegen) -> Self {
        SerializedDefEntry {
            got_slot: dc.got_slot,
            source: dc.source.clone(),
            sexp: dc.sexp.clone(),
            defn: dc.defn.clone(),
            param_count: dc.param_count,
        }
    }
}

impl From<&SerializedDefEntry> for DefCodegen {
    fn from(se: &SerializedDefEntry) -> Self {
        DefCodegen {
            got_slot: se.got_slot,
            source: se.source.clone(),
            sexp: se.sexp.clone(),
            defn: se.defn.clone(),
            param_count: se.param_count,
            // Runtime state reconstructed from .o file
            code_ptr: None,
            clif_ir: None,
            disasm: None,
            code_size: None,
            compile_duration: None,
        }
    }
}

/// Combined metadata for a cached module.
/// This is what gets serialized to the `.meta.json` file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheMetadata {
    pub symbol_table: SymbolTable,
    pub module_structure: ModuleStructure,
    pub codegen_state: CacheCodegenState,
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
    use cranelisp_types::{ModuleFullPath, ModuleStructure, SymbolTable};

    fn make_test_metadata() -> CacheMetadata {
        CacheMetadata {
            symbol_table: SymbolTable::new(ModuleFullPath::from("test")),
            module_structure: ModuleStructure {
                path: ModuleFullPath::from("test"),
                file_path: Some(std::path::PathBuf::from("test.cl")),
                mod_decls: vec![],
                import_specs: vec![],
                export_specs: vec![],
                platform_specs: vec![],
                impl_sexps: vec![],
                impls: vec![],
                dll_path: None,
            },
            codegen_state: CacheCodegenState {
                got_slots: HashMap::new(),
                next_got_slot: 0,
                def_entries: HashMap::new(),
            },
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
        assert_eq!(loaded.module_structure.path, ModuleFullPath::from("test"));
        assert_eq!(loaded.codegen_state.next_got_slot, 0);
    }

    // spec: design/backend/module-caching.md §4 — metadata with GOT slots
    #[test]
    fn test_metadata_with_got_slots() {
        let dir = tempfile::tempdir().unwrap();
        let meta_path = dir.path().join("test.meta.json");

        let mut metadata = make_test_metadata();
        metadata.codegen_state.got_slots.insert(Symbol::from("foo"), 0);
        metadata.codegen_state.got_slots.insert(Symbol::from("bar"), 1);
        metadata.codegen_state.next_got_slot = 2;
        metadata.codegen_state.def_entries.insert(
            Symbol::from("foo"),
            SerializedDefEntry {
                got_slot: Some(0),
                source: Some("(defn foo [x] x)".to_string()),
                sexp: None,
                defn: None,
                param_count: Some(1),
            },
        );

        write_cached_metadata(&meta_path, &metadata).unwrap();
        let loaded = read_cached_metadata(&meta_path).unwrap();

        assert_eq!(loaded.codegen_state.next_got_slot, 2);
        assert_eq!(
            loaded.codegen_state.got_slots.get(&Symbol::from("foo")),
            Some(&0)
        );
        let entry = loaded
            .codegen_state
            .def_entries
            .get(&Symbol::from("foo"))
            .unwrap();
        assert_eq!(entry.param_count, Some(1));
        assert_eq!(entry.source.as_deref(), Some("(defn foo [x] x)"));
    }

    // spec: design/backend/module-caching.md §4 — SerializedDefEntry to DefCodegen conversion
    #[test]
    fn test_def_entry_conversion() {
        let serialized = SerializedDefEntry {
            got_slot: Some(5),
            source: Some("src".to_string()),
            sexp: None,
            defn: None,
            param_count: Some(3),
        };
        let dc: DefCodegen = (&serialized).into();
        assert_eq!(dc.got_slot, Some(5));
        assert_eq!(dc.param_count, Some(3));
        // Runtime fields should be None
        assert!(dc.code_ptr.is_none());
        assert!(dc.clif_ir.is_none());
        assert!(dc.compile_duration.is_none());
    }

    // spec: design/backend/module-caching.md §4 — read nonexistent file returns error
    #[test]
    fn test_read_nonexistent_metadata() {
        let result = read_cached_metadata(Path::new("/nonexistent/path.meta.json"));
        assert!(result.is_err());
    }
}
