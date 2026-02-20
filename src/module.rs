use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::{CranelispError, Span};
use crate::sexp::Sexp;
use crate::typechecker::TypeChecker;

// Re-export ModuleFullPath from names.rs — canonical definition lives there.
pub use crate::names::ModuleFullPath;

use cranelift_module::FuncId;

use crate::ast::{Defn, TraitDecl, TraitImpl, Visibility};
use crate::names::{FQSymbol, JitSymbol, ModuleName, Symbol, TraitName, TypeName};
use crate::typechecker::{
    ConstrainedFn, ConstructorInfo, MethodResolutions, PrimitiveKind, SymbolMeta, TypeDefInfo,
};
use crate::types::{Scheme, Type};

/// Maximum number of GOT slots per module.
pub const GOT_TABLE_SIZE: usize = 1024;

/// Check whether a module name is a synthetic module provided by the runtime,
/// not backed by files. These are skipped during module graph file discovery.
pub fn is_synthetic_module(name: &str) -> bool {
    matches!(name, "primitives" | "macros") || name.starts_with("platform.")
}

// ── Definition kind + codegen artifacts ──────────────────────────────────

/// Classification of a definition entry, determining how it's compiled and displayed.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    /// A special form (if, let, defn, ...). Has a description string for /sig display.
    SpecialForm { description: String },
    /// A built-in primitive (inline IR, extern FFI, or platform effect).
    Primitive {
        primitive_kind: PrimitiveKind,
        jit_name: Option<JitSymbol>,
        #[serde(skip)]
        func_id: Option<FuncId>,
    },
    /// A user-defined function.
    UserFn {
        constrained_fn: Option<ConstrainedFn>,
        codegen: DefCodegen,
    },
}

/// Codegen artifacts for a user-defined function.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DefCodegen {
    pub got_slot: Option<usize>,
    #[serde(skip)]
    pub code_ptr: Option<*const u8>,
    pub source: Option<String>,
    pub sexp: Option<Sexp>,
    pub defn: Option<Defn>,
    pub clif_ir: Option<String>,
    pub disasm: Option<String>,
    pub code_size: Option<usize>,
    #[serde(skip)]
    pub compile_duration: Option<std::time::Duration>,
    pub param_count: Option<usize>,
}


// ── Per-module symbol tables ──────────────────────────────────────────────

/// Stored trait impl block for file regeneration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImplSexp {
    pub trait_name: TraitName,
    pub target: TypeName,
    pub sexp: Sexp,
}

/// A compiled module's symbol table.
/// Each module owns its definitions, imports, and re-exports.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompiledModule {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry>,
    // Module-level source info for file generation
    pub file_path: Option<PathBuf>,
    pub mod_decls: Vec<ModuleName>,
    pub import_specs: Vec<ImportSpec>,
    pub export_specs: Vec<ExportSpec>,
    pub impl_sexps: Vec<ImplSexp>,
    /// Trait implementations registered in this module.
    pub impls: Vec<TraitImpl>,
    /// Path to the DLL for platform modules (only set for `platform.*` modules).
    pub dll_path: Option<PathBuf>,
    /// SHA-256 hash of the last saved/loaded source content.
    /// Used to skip redundant reloads when file content hasn't changed.
    pub content_hash: Option<String>,
    /// Transient: method resolutions accumulated during compilation, used for cache .o emission.
    #[serde(skip)]
    pub cache_method_resolutions: MethodResolutions,
    /// Transient: expression types accumulated during compilation, used for cache .o emission.
    #[serde(skip)]
    pub cache_expr_types: HashMap<Span, Type>,
    /// Per-module function pointer table (GOT). Lazily allocated on first use.
    #[serde(skip)]
    pub got_table: Option<Box<[*const u8; GOT_TABLE_SIZE]>>,
    /// Next available slot in the GOT.
    #[serde(skip)]
    pub next_got_slot: usize,
}

/// An entry in a module's symbol table.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModuleEntry {
    /// A definition (defn, constructor scheme, trait method scheme, primitive, special form).
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<String>,
        kind: DefKind,
        /// Denormalized copy of the original SymbolMeta. Kept for backward compatibility
        /// with callers that use get_symbol_meta(). Will be removed once callers migrate to DefKind.
        meta: Option<SymbolMeta>,
    },
    /// An imported name from another module.
    Import { source: FQSymbol },
    /// A re-exported name from another module.
    Reexport { source: FQSymbol },
    /// A type definition (deftype).
    /// For single-constructor product types where the constructor has the same name
    /// as the type (e.g., `Point`), `constructor_scheme` holds the constructor's scheme
    /// so this entry serves double duty as both TypeDef and Constructor.
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        constructor_scheme: Option<Scheme>,
        sexp: Option<crate::sexp::Sexp>,
    },
    /// A trait declaration (deftrait).
    TraitDecl {
        decl: TraitDecl,
        visibility: Visibility,
        sexp: Option<crate::sexp::Sexp>,
    },
    /// A constructor (from a deftype).
    Constructor {
        type_name: Symbol,
        info: ConstructorInfo,
        scheme: Scheme,
        visibility: Visibility,
    },
    /// A macro definition (defmacro).
    /// Expansion stays in `MacroEnv`; this stores enough for introspection and import/export.
    Macro {
        name: String,
        fixed_params: Vec<String>,
        rest_param: Option<String>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<crate::sexp::Sexp>,
        /// Original source text of the defmacro form.
        source: Option<String>,
    },
    /// A platform DLL declaration (platform name).
    /// Stored in the declaring module's symbol table as the source of truth.
    PlatformDecl {
        dll_path: PathBuf,
        platform_module: ModuleFullPath,
    },
    /// A bare name that became ambiguous (two different sources registered it).
    /// Qualified alternatives are derived at error time by scanning TraitDecl/TypeDef entries.
    Ambiguous,
}

impl CompiledModule {
    pub fn new(path: ModuleFullPath) -> Self {
        CompiledModule {
            path,
            symbols: HashMap::new(),
            file_path: None,
            mod_decls: Vec::new(),
            import_specs: Vec::new(),
            export_specs: Vec::new(),
            impl_sexps: Vec::new(),
            impls: Vec::new(),
            dll_path: None,
            content_hash: None,
            cache_method_resolutions: HashMap::new(),
            cache_expr_types: HashMap::new(),
            got_table: None,
            next_got_slot: 0,
        }
    }

    /// Insert or update a definition entry.
    /// Accepts `Option<SymbolMeta>` for compatibility; converts to `DefKind` internally.
    pub fn insert_def(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        visibility: Visibility,
        meta: Option<SymbolMeta>,
    ) {
        let (docstring, param_names, kind) = match &meta {
            Some(SymbolMeta::SpecialForm {
                description,
                docstring,
            }) => (
                Some(docstring.clone()),
                vec![],
                DefKind::SpecialForm {
                    description: description.clone(),
                },
            ),
            Some(SymbolMeta::Primitive {
                kind,
                docstring,
                param_names,
            }) => (
                Some(docstring.clone()),
                param_names.clone(),
                DefKind::Primitive {
                    primitive_kind: *kind,
                    jit_name: None,
                    func_id: None,
                },
            ),
            Some(SymbolMeta::UserFn {
                docstring,
                param_names,
            }) => (
                docstring.clone(),
                param_names.clone(),
                DefKind::UserFn {
                    constrained_fn: None,
                    codegen: DefCodegen::default(),
                },
            ),
            None => (
                None,
                vec![],
                DefKind::UserFn {
                    constrained_fn: None,
                    codegen: DefCodegen::default(),
                },
            ),
        };
        self.symbols.insert(
            name,
            ModuleEntry::Def {
                scheme,
                visibility,
                docstring,
                param_names,
                kind,
                meta,
            },
        );
    }

    /// Insert a Def if the name is not already taken by a different definition.
    /// If a Def or Constructor entry already exists (from a different type/trait),
    /// replace with Ambiguous. Import/Reexport entries are silently overwritten
    /// (local definitions shadow imports). Returns true if the name was poisoned.
    pub fn insert_def_checked(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        visibility: Visibility,
        meta: Option<SymbolMeta>,
    ) -> bool {
        if let Some(existing) = self.symbols.get(&name) {
            match existing {
                ModuleEntry::Ambiguous => return true,
                ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. } => {}
                ModuleEntry::TraitDecl { .. } | ModuleEntry::TypeDef { .. } => {}
                ModuleEntry::PlatformDecl { .. } => {}
                ModuleEntry::Def { .. }
                | ModuleEntry::Constructor { .. }
                | ModuleEntry::Macro { .. } => {
                    self.symbols.insert(name, ModuleEntry::Ambiguous);
                    return true;
                }
            }
        }
        self.insert_def(name, scheme, visibility, meta);
        false
    }

    /// Insert an Import if the name is not already taken.
    /// If an entry already exists, replace with Ambiguous and return true.
    /// Exception: if the existing entry is an Import with the same FQSymbol source
    /// (duplicate via re-export paths), skip without poisoning.
    pub fn insert_import_checked(&mut self, name: Symbol, source: FQSymbol) -> bool {
        if let Some(existing) = self.symbols.get(&name) {
            match existing {
                ModuleEntry::Ambiguous => return true,
                ModuleEntry::Import {
                    source: existing_src,
                } => {
                    if *existing_src == source {
                        return false; // same source, not a conflict
                    }
                }
                _ => {}
            }
            // Different source — poison
            self.symbols.insert(name, ModuleEntry::Ambiguous);
            return true;
        }
        self.insert_import(name, source);
        false
    }

    /// Insert an import entry.
    pub fn insert_import(&mut self, name: Symbol, source: FQSymbol) {
        self.symbols.insert(name, ModuleEntry::Import { source });
    }

    /// Insert a re-export entry.
    pub fn insert_reexport(&mut self, name: Symbol, source: FQSymbol) {
        self.symbols.insert(name, ModuleEntry::Reexport { source });
    }

    /// Look up an entry by bare name.
    pub fn get(&self, name: &str) -> Option<&ModuleEntry> {
        self.symbols.get(name)
    }

    /// Update a Def entry's codegen fields after compilation.
    /// If the name is not found or is not a UserFn Def, this is a no-op (best-effort).
    pub fn update_codegen(
        &mut self,
        name: &str,
        metadata: &crate::jit::CompileMetadata,
        source_text: Option<&str>,
        sexp_val: Option<&crate::sexp::Sexp>,
        defn_val: Option<&Defn>,
    ) {
        if let Some(ModuleEntry::Def {
            kind: DefKind::UserFn { codegen, .. },
            ..
        }) = self.symbols.get_mut(name)
        {
            codegen.got_slot = Some(metadata.got_slot);
            codegen.code_ptr = Some(metadata.code_ptr);
            codegen.clif_ir = Some(metadata.clif_ir.clone());
            codegen.disasm = metadata.disasm.clone();
            codegen.code_size = metadata.code_size;
            codegen.compile_duration = Some(metadata.compile_duration);
            codegen.param_count = Some(metadata.param_count);
            codegen.source = source_text.map(|s| s.to_string());
            codegen.sexp = sexp_val.cloned();
            codegen.defn = defn_val.cloned();
        }
    }

    /// Get the got_slot for a UserFn Def entry, if it exists and has been assigned.
    pub fn get_got_slot(&self, name: &str) -> Option<usize> {
        match self.symbols.get(name)? {
            ModuleEntry::Def {
                kind: DefKind::UserFn { codegen, .. },
                ..
            } => codegen.got_slot,
            _ => None,
        }
    }

    /// Extract GOT (slot, code_ptr) entries for all compiled UserFn Def symbols.
    /// Used for save/restore during module reload.
    pub fn got_entries(&self) -> Vec<(usize, *const u8)> {
        self.symbols
            .values()
            .filter_map(|entry| {
                if let ModuleEntry::Def {
                    kind: DefKind::UserFn { codegen, .. },
                    ..
                } = entry
                {
                    if let (Some(slot), Some(ptr)) = (codegen.got_slot, codegen.code_ptr) {
                        if !ptr.is_null() {
                            return Some((slot, ptr));
                        }
                    }
                }
                None
            })
            .collect()
    }

    /// Lazily allocate the GOT table if not yet created.
    pub fn ensure_got(&mut self) {
        if self.got_table.is_none() {
            self.got_table = Some(Box::new([std::ptr::null(); GOT_TABLE_SIZE]));
        }
    }

    /// Get the stable address of this module's GOT table (for embedding as iconst in JIT code).
    /// Returns None if the GOT has not been allocated.
    pub fn got_table_addr(&self) -> Option<i64> {
        self.got_table.as_ref().map(|t| t.as_ptr() as i64)
    }

    /// Allocate a slot in this module's GOT.
    pub fn allocate_got_slot(&mut self, span: Span) -> Result<usize, CranelispError> {
        self.ensure_got();
        let slot = self.next_got_slot;
        if slot >= GOT_TABLE_SIZE {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "module '{}' function table full",
                    self.path.short_name()
                ),
                span,
            });
        }
        self.next_got_slot += 1;
        Ok(slot)
    }

    /// Write a code pointer to a GOT slot.
    pub fn write_got_slot(&mut self, slot: usize, code_ptr: *const u8) {
        self.ensure_got();
        self.got_table.as_mut().unwrap()[slot] = code_ptr;
    }

    /// Restore GOT slot entries from saved state (used during module reload rollback).
    pub fn restore_got_entries(&mut self, saved: &[(usize, *const u8)]) {
        self.ensure_got();
        let table = self.got_table.as_mut().unwrap();
        for &(slot, code_ptr) in saved {
            table[slot] = code_ptr;
        }
    }

    /// Pre-register a Def entry's got_slot and param_count before compilation,
    /// so that `build_fn_slots_from_modules` includes this function (needed for recursion).
    /// No-op if the entry is not a UserFn Def.
    pub fn pre_register_for_codegen(&mut self, name: &str, slot: usize, param_count_val: usize) {
        if let Some(ModuleEntry::Def {
            kind: DefKind::UserFn { codegen, .. },
            ..
        }) = self.symbols.get_mut(name)
        {
            codegen.got_slot = Some(slot);
            codegen.param_count = Some(param_count_val);
        }
    }

    /// Get the scheme for a Def, Constructor, or product-type TypeDef entry, if it exists.
    pub fn get_scheme(&self, name: &str) -> Option<&Scheme> {
        match self.symbols.get(name)? {
            ModuleEntry::Def { scheme, .. } => Some(scheme),
            ModuleEntry::Constructor { scheme, .. } => Some(scheme),
            ModuleEntry::TypeDef {
                constructor_scheme: Some(scheme),
                ..
            } => Some(scheme),
            _ => None,
        }
    }

    /// Update the meta (docstring + param_names) of a Def entry (best-effort, no-op if not a Def).
    pub fn update_meta(&mut self, name: &str, new_meta: SymbolMeta) {
        if let Some(ModuleEntry::Def {
            docstring,
            param_names,
            meta,
            ..
        }) = self.symbols.get_mut(name)
        {
            match &new_meta {
                SymbolMeta::UserFn {
                    docstring: ds,
                    param_names: pn,
                } => {
                    *docstring = ds.clone();
                    *param_names = pn.clone();
                }
                SymbolMeta::Primitive {
                    docstring: ds,
                    param_names: pn,
                    ..
                } => {
                    *docstring = Some(ds.clone());
                    *param_names = pn.clone();
                }
                SymbolMeta::SpecialForm { docstring: ds, .. } => {
                    *docstring = Some(ds.clone());
                }
            }
            *meta = Some(new_meta);
        }
    }

    /// Set the JIT symbol name on an existing Primitive entry.
    pub fn set_jit_name(&mut self, name: &str, jit_name: JitSymbol) {
        if let Some(ModuleEntry::Def {
            kind: DefKind::Primitive { jit_name: slot, .. },
            ..
        }) = self.symbols.get_mut(name)
        {
            *slot = Some(jit_name);
        }
    }

    /// Get visibility of a locally-defined symbol (not imports/reexports).
    pub fn get_visibility(&self, name: &str) -> Option<Visibility> {
        match self.symbols.get(name)? {
            ModuleEntry::Def { visibility, .. }
            | ModuleEntry::Constructor { visibility, .. }
            | ModuleEntry::TraitDecl { visibility, .. }
            | ModuleEntry::Macro { visibility, .. } => Some(*visibility),
            ModuleEntry::TypeDef { visibility, .. } => Some(*visibility),
            ModuleEntry::Import { .. }
            | ModuleEntry::Reexport { .. }
            | ModuleEntry::PlatformDecl { .. }
            | ModuleEntry::Ambiguous => None,
        }
    }

    /// Get all public names defined in this module (Def/Constructor/TraitDecl/TypeDef).
    /// Skips Import/Reexport/Ambiguous entries.
    pub fn public_names(&self) -> Vec<String> {
        let mut names = Vec::new();
        for (sym, entry) in &self.symbols {
            match entry {
                ModuleEntry::Def { visibility, .. }
                | ModuleEntry::Constructor { visibility, .. }
                | ModuleEntry::TraitDecl { visibility, .. }
                | ModuleEntry::TypeDef { visibility, .. }
                | ModuleEntry::Macro { visibility, .. } => {
                    if *visibility == Visibility::Public {
                        names.push(sym.to_string());
                    }
                }
                // Re-exports are inherently public
                ModuleEntry::Reexport { .. } => {
                    names.push(sym.to_string());
                }
                _ => continue,
            }
        }
        names
    }

    /// Get all names with visibility defined or re-exported by this module.
    /// Skips Import/Ambiguous entries.
    pub fn all_names_with_visibility(&self) -> Vec<(String, Visibility)> {
        let mut names = Vec::new();
        for (sym, entry) in &self.symbols {
            match entry {
                ModuleEntry::Def { visibility, .. }
                | ModuleEntry::Constructor { visibility, .. }
                | ModuleEntry::TraitDecl { visibility, .. }
                | ModuleEntry::TypeDef { visibility, .. }
                | ModuleEntry::Macro { visibility, .. } => {
                    names.push((sym.to_string(), *visibility));
                }
                // Re-exports are inherently public
                ModuleEntry::Reexport { .. } => {
                    names.push((sym.to_string(), Visibility::Public));
                }
                _ => continue,
            }
        }
        names
    }

    /// Check if a name is an Import, returning the source module path.
    pub fn import_source(&self, name: &str) -> Option<&ModuleFullPath> {
        match self.symbols.get(name)? {
            ModuleEntry::Import { source } => Some(&source.module),
            _ => None,
        }
    }

    /// Insert a macro entry.
    pub fn insert_macro(
        &mut self,
        name: Symbol,
        fixed_params: Vec<String>,
        rest_param: Option<String>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<crate::sexp::Sexp>,
        source: Option<String>,
    ) {
        self.symbols.insert(
            name.clone(),
            ModuleEntry::Macro {
                name: name.to_string(),
                fixed_params,
                rest_param,
                docstring,
                visibility,
                sexp,
                source,
            },
        );
    }

    /// Update the code_ptr for a function at a given GOT slot (used by cache loading).
    pub fn update_code_ptr_for_slot(&mut self, slot: usize, code_ptr: *const u8) {
        for entry in self.symbols.values_mut() {
            if let ModuleEntry::Def {
                kind:
                    DefKind::UserFn {
                        codegen:
                            DefCodegen {
                                got_slot: Some(s),
                                code_ptr: cp,
                                ..
                            },
                        ..
                    },
                ..
            } = entry
            {
                if *s == slot {
                    *cp = Some(code_ptr);
                    return;
                }
            }
        }
    }

    /// Accumulate method resolutions into transient cache fields (for cache .o emission).
    pub fn accumulate_method_resolutions(&mut self, mr: MethodResolutions) {
        self.cache_method_resolutions.extend(mr);
    }

    /// Accumulate expression types into transient cache fields (for cache .o emission).
    pub fn accumulate_expr_types(&mut self, et: HashMap<Span, Type>) {
        self.cache_expr_types.extend(et);
    }

    /// Clear transient cache fields after cache write.
    pub fn clear_cache_transients(&mut self) {
        self.cache_method_resolutions.clear();
        self.cache_expr_types.clear();
    }

    /// Extract (Defn, Scheme) pairs from all UserFn entries that have a stored Defn.
    /// Used by cache .o compilation.
    pub fn compiled_defns(&self) -> Vec<(&Defn, &Scheme)> {
        self.symbols
            .values()
            .filter_map(|entry| {
                if let ModuleEntry::Def {
                    kind: DefKind::UserFn { codegen, .. },
                    scheme,
                    ..
                } = entry
                {
                    codegen.defn.as_ref().map(|d| (d, scheme))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Update the constrained_fn field of a UserFn Def entry (best-effort, no-op if not UserFn Def).
    pub fn update_constrained_fn(&mut self, name: &str, cf: ConstrainedFn) {
        if let Some(ModuleEntry::Def {
            kind: DefKind::UserFn { constrained_fn, .. },
            ..
        }) = self.symbols.get_mut(name)
        {
            *constrained_fn = Some(cf);
        }
    }
}

// ── Import / Export data structures ─────────────────────────────────────

/// What names to import from a module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportNames {
    /// Import specific names: `[Some None]`
    Specific(Vec<String>),
    /// Import all public names: `[*]`
    Glob,
    /// Import all members of a type or trait: `[Display.*]`
    MemberGlob(String),
    /// No names — alias-only: `[]`
    None,
}

/// A single import specification from an `(import ...)` form.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportSpec {
    /// Module path, e.g. "core.option"
    pub module_path: String,
    /// Optional alias, e.g. Some("opt") from `(core.option opt)`
    pub alias: Option<String>,
    /// What names to import
    pub names: ImportNames,
    pub span: Span,
}

/// A single export specification from an `(export ...)` form.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportSpec {
    /// Module path to re-export from
    pub module_path: String,
    /// What names to re-export
    pub names: ImportNames,
    pub span: Span,
}

/// Result of extracting module declarations from raw sexps.
#[derive(Debug)]
pub struct ModuleDecls {
    pub mod_names: Vec<(String, Span)>,
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<(String, Option<String>, Span)>,
    pub remaining: Vec<Sexp>,
}

/// Information about a discovered module.
#[derive(Debug)]
pub struct ModuleInfo {
    pub id: ModuleFullPath,
    pub file_path: PathBuf,
    pub source: String,
    pub sexps: Vec<Sexp>,
    /// (mod name) declarations found in this module, with spans for error reporting.
    pub child_mod_names: Vec<(String, Span)>,
    /// Resolved child ModuleFullPaths.
    pub dependencies: Vec<ModuleFullPath>,
    /// Import declarations from this module.
    pub imports: Vec<ImportSpec>,
    /// Export declarations from this module.
    pub exports: Vec<ExportSpec>,
    /// Platform declarations from this module: `(platform name)` or `(platform name "path")`.
    pub platforms: Vec<(String, Option<String>, Span)>,
    /// Whether this module's source lives under the lib directory (vs project-local).
    pub is_lib: bool,
}

/// Dependency graph of all modules in a project.
#[derive(Debug)]
pub struct ModuleGraph {
    pub modules: HashMap<ModuleFullPath, ModuleInfo>,
    /// Topological order: leaves (no deps) first, root last.
    pub compile_order: Vec<ModuleFullPath>,
}

/// Extract `(mod name)` declarations from a list of top-level sexps.
/// Returns (mod_names_with_spans, remaining_sexps).
pub fn extract_mod_decls(sexps: Vec<Sexp>) -> (Vec<(String, Span)>, Vec<Sexp>) {
    let mut mod_decls = Vec::new();
    let mut remaining = Vec::new();

    for sexp in sexps {
        if let Sexp::List(ref children, span) = sexp {
            if children.len() == 2 {
                if let Sexp::Symbol(ref head, _) = children[0] {
                    if head == "mod" {
                        if let Sexp::Symbol(ref name, _) = children[1] {
                            mod_decls.push((name.clone(), span));
                            continue;
                        }
                    }
                }
            }
        }
        remaining.push(sexp);
    }

    (mod_decls, remaining)
}

/// Extract all module declarations from raw sexps: `(mod ...)`, `(import ...)`, `(export ...)`.
/// Returns a `ModuleDecls` with parsed declarations and the remaining sexps.
pub fn extract_module_decls(sexps: Vec<Sexp>) -> Result<ModuleDecls, CranelispError> {
    let mut mod_names = Vec::new();
    let mut imports = Vec::new();
    let mut exports = Vec::new();
    let mut platforms = Vec::new();
    let mut remaining = Vec::new();

    for sexp in sexps {
        if let Sexp::List(ref children, span) = sexp {
            if !children.is_empty() {
                if let Sexp::Symbol(ref head, _) = children[0] {
                    match head.as_str() {
                        "mod" => {
                            if children.len() == 2 {
                                if let Sexp::Symbol(ref name, _) = children[1] {
                                    mod_names.push((name.clone(), span));
                                    continue;
                                }
                            }
                            return Err(CranelispError::ParseError {
                                message: "(mod ...) requires exactly one module name".to_string(),
                                offset: span.0,
                            });
                        }
                        "import" => {
                            if children.len() != 2 {
                                return Err(CranelispError::ParseError {
                                    message: "(import ...) requires a bracket body".to_string(),
                                    offset: span.0,
                                });
                            }
                            let parsed = parse_import_body(&children[1], span)?;
                            imports.extend(parsed);
                            continue;
                        }
                        "export" => {
                            if children.len() != 2 {
                                return Err(CranelispError::ParseError {
                                    message: "(export ...) requires a bracket body".to_string(),
                                    offset: span.0,
                                });
                            }
                            let parsed = parse_export_body(&children[1], span)?;
                            exports.extend(parsed);
                            continue;
                        }
                        "platform" => {
                            // (platform name) or (platform name "path")
                            match children.len() {
                                2 => {
                                    if let Sexp::Symbol(ref name, _) = children[1] {
                                        platforms.push((name.clone(), None, span));
                                        continue;
                                    }
                                }
                                3 => {
                                    if let Sexp::Symbol(ref name, _) = children[1] {
                                        if let Sexp::Str(ref path, _) = children[2] {
                                            platforms.push((name.clone(), Some(path.clone()), span));
                                            continue;
                                        }
                                    }
                                }
                                _ => {}
                            }
                            return Err(CranelispError::ParseError {
                                message: "(platform name) or (platform name \"path\") expected".to_string(),
                                offset: span.0,
                            });
                        }
                        _ => {}
                    }
                }
            }
        }
        remaining.push(sexp);
    }

    Ok(ModuleDecls {
        mod_names,
        imports,
        exports,
        platforms,
        remaining,
    })
}

/// Parse the bracket body of an `(import [...])` form.
/// The body is alternating module-spec / names-list pairs:
///   `[core.option [Some None] (core.string str) [concat join]]`
fn parse_import_body(sexp: &Sexp, outer_span: Span) -> Result<Vec<ImportSpec>, CranelispError> {
    let items = match sexp {
        Sexp::Bracket(children, _) => children,
        _ => {
            return Err(CranelispError::ParseError {
                message: "import body must be a bracket [...]".to_string(),
                offset: sexp.span().0,
            });
        }
    };

    let mut specs = Vec::new();
    let mut i = 0;
    while i < items.len() {
        // Parse module spec: bare symbol or (module alias) list
        let (module_path, alias, _) = parse_module_spec(&items[i])?;
        i += 1;

        // Parse names list: must be a bracket
        if i >= items.len() {
            return Err(CranelispError::ParseError {
                message: format!("import: module '{}' missing names list [...]", module_path),
                offset: items[i - 1].span().0,
            });
        }
        let names = parse_names_list(&items[i])?;
        i += 1;

        specs.push(ImportSpec {
            module_path,
            alias,
            names,
            span: outer_span,
        });
    }

    Ok(specs)
}

/// Parse the bracket body of an `(export [...])` form.
/// Same format as import but without aliases.
fn parse_export_body(sexp: &Sexp, outer_span: Span) -> Result<Vec<ExportSpec>, CranelispError> {
    let items = match sexp {
        Sexp::Bracket(children, _) => children,
        _ => {
            return Err(CranelispError::ParseError {
                message: "export body must be a bracket [...]".to_string(),
                offset: sexp.span().0,
            });
        }
    };

    let mut specs = Vec::new();
    let mut i = 0;
    while i < items.len() {
        // Parse module spec: bare symbol (no alias for exports)
        let (module_path, _alias, _) = parse_module_spec(&items[i])?;
        i += 1;

        if i >= items.len() {
            return Err(CranelispError::ParseError {
                message: format!("export: module '{}' missing names list [...]", module_path),
                offset: items[i - 1].span().0,
            });
        }
        let names = parse_names_list(&items[i])?;
        i += 1;

        specs.push(ExportSpec {
            module_path,
            names,
            span: outer_span,
        });
    }

    Ok(specs)
}

/// Parse a module spec: bare symbol `core.option` or aliased `(core.option opt)`.
/// Returns (module_path, optional_alias, span).
fn parse_module_spec(sexp: &Sexp) -> Result<(String, Option<String>, Span), CranelispError> {
    match sexp {
        Sexp::Symbol(name, span) => Ok((name.clone(), None, *span)),
        Sexp::List(children, span) => {
            if children.len() != 2 {
                return Err(CranelispError::ParseError {
                    message: "module spec alias must be (module alias)".to_string(),
                    offset: span.0,
                });
            }
            let module_path = match &children[0] {
                Sexp::Symbol(name, _) => name.clone(),
                _ => {
                    return Err(CranelispError::ParseError {
                        message: "expected module name in module spec".to_string(),
                        offset: children[0].span().0,
                    });
                }
            };
            let alias = match &children[1] {
                Sexp::Symbol(name, _) => name.clone(),
                _ => {
                    return Err(CranelispError::ParseError {
                        message: "expected alias name in module spec".to_string(),
                        offset: children[1].span().0,
                    });
                }
            };
            Ok((module_path, Some(alias), *span))
        }
        _ => Err(CranelispError::ParseError {
            message: "expected module name or (module alias)".to_string(),
            offset: sexp.span().0,
        }),
    }
}

/// Parse a names list: `[Some None]`, `[*]`, `[Display.*]`, or `[]`.
fn parse_names_list(sexp: &Sexp) -> Result<ImportNames, CranelispError> {
    let items = match sexp {
        Sexp::Bracket(children, _) => children,
        _ => {
            return Err(CranelispError::ParseError {
                message: "expected names list [...]".to_string(),
                offset: sexp.span().0,
            });
        }
    };

    if items.is_empty() {
        return Ok(ImportNames::None);
    }

    if items.len() == 1 {
        if let Sexp::Symbol(name, _) = &items[0] {
            if name == "*" {
                return Ok(ImportNames::Glob);
            }
            if name.ends_with(".*") && name.len() > 2 {
                let parent = name[..name.len() - 2].to_string();
                return Ok(ImportNames::MemberGlob(parent));
            }
        }
    }

    let mut names = Vec::new();
    for item in items {
        match item {
            Sexp::Symbol(name, span) => {
                if name == "*" {
                    return Err(CranelispError::ParseError {
                        message: "[*] must be the only element in a names list".to_string(),
                        offset: span.0,
                    });
                }
                if name.ends_with(".*") {
                    return Err(CranelispError::ParseError {
                        message: "[Type.*] must be the only element in a names list".to_string(),
                        offset: span.0,
                    });
                }
                names.push(name.clone());
            }
            _ => {
                return Err(CranelispError::ParseError {
                    message: "expected name in import list".to_string(),
                    offset: item.span().0,
                });
            }
        }
    }

    Ok(ImportNames::Specific(names))
}

/// Resolve a module name using the unified search order.
/// Used by `(mod ...)` and `(export ...)` declarations.
/// Search order:
/// 1) parent_dir/stem/name.cl (child directory)
/// 2) parent_dir/name.cl (sibling file)
/// 3) project_root/name.cl
/// 4) lib_dir/name.cl
pub fn resolve_module(
    name: &str,
    parent_file: &Path,
    project_root: &Path,
    lib_dir: Option<&Path>,
) -> Result<PathBuf, CranelispError> {
    let parent_dir = parent_file.parent().unwrap_or_else(|| Path::new("."));
    let parent_stem = parent_file
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("");

    let mut searched = Vec::new();

    // 1) Child directory: parent_dir/stem/name.cl
    let child_dir_path = parent_dir
        .join(parent_stem)
        .join(format!("{}.cl", name));
    if child_dir_path.exists() {
        return Ok(child_dir_path);
    }
    searched.push(child_dir_path);

    // 2) Sibling: parent_dir/name.cl
    let sibling_path = parent_dir.join(format!("{}.cl", name));
    if sibling_path.exists() {
        return Ok(sibling_path);
    }
    searched.push(sibling_path);

    // 3) Project root: project_root/name.cl
    let root_path = project_root.join(format!("{}.cl", name));
    if root_path.exists() && !searched.contains(&root_path) {
        return Ok(root_path);
    }
    if !searched.contains(&root_path) {
        searched.push(root_path);
    }

    // 4) Library root: lib_dir/name.cl
    if let Some(lib) = lib_dir {
        let lib_path = lib.join(format!("{}.cl", name));
        if lib_path.exists() {
            return Ok(lib_path);
        }
        if !searched.contains(&lib_path) {
            searched.push(lib_path);
        }
    }

    let searched_str = searched
        .iter()
        .map(|p| format!("  {}", p.display()))
        .collect::<Vec<_>>()
        .join("\n");

    Err(CranelispError::ModuleError {
        message: format!(
            "module '{}' not found — searched:\n{}",
            name, searched_str
        ),
        file: Some(parent_file.to_path_buf()),
        span: (0, 0),
    })
}

/// Resolve a root module name (project root or lib directory only).
/// Used for import-triggered auto-discovery of root modules.
/// Returns None if no matching file is found (not an error — the import
/// may reference a module loaded through other means).
pub fn resolve_root_module(
    name: &str,
    project_root: &Path,
    lib_dir: Option<&Path>,
) -> Option<PathBuf> {
    // 1) Project root: project_root/name.cl
    let root_path = project_root.join(format!("{}.cl", name));
    if root_path.exists() {
        return Some(root_path);
    }

    // 2) Library root: lib_dir/name.cl
    if let Some(lib) = lib_dir {
        let lib_path = lib.join(format!("{}.cl", name));
        if lib_path.exists() {
            return Some(lib_path);
        }
    }

    None
}

/// Find the site library directory for module resolution.
/// Search order:
/// 1) CRANELISP_LIB env var
/// 2) {project_root}/lib (standard project library)
/// 3) {CARGO_MANIFEST_DIR}/lib (development fallback)
pub fn find_lib_dir(project_root: &Path) -> Option<PathBuf> {
    // 1) CRANELISP_LIB env var
    if let Ok(lib) = std::env::var("CRANELISP_LIB") {
        let path = PathBuf::from(lib);
        if path.is_dir() {
            return Some(path);
        }
    }

    // 2) {project_root}/lib
    let project_lib = project_root.join("lib");
    if project_lib.is_dir() {
        return Some(project_lib);
    }

    // 3) Development fallback via CARGO_MANIFEST_DIR
    if let Some(manifest_dir) = option_env!("CARGO_MANIFEST_DIR") {
        let dev_lib = PathBuf::from(manifest_dir).join("lib");
        if dev_lib.is_dir() {
            return Some(dev_lib);
        }
    }

    None
}

/// Compute module ID from file path relative to project root.
/// e.g., "app/handler.cl" relative to project root → "app.handler"
/// The root entry file itself gets ModuleFullPath("").
pub fn path_to_module_full_path(file_path: &Path, project_root: &Path) -> ModuleFullPath {
    let relative = file_path.strip_prefix(project_root).unwrap_or(file_path);
    let stem = relative.with_extension("");
    let id = stem
        .components()
        .map(|c| c.as_os_str().to_string_lossy().to_string())
        .collect::<Vec<_>>()
        .join(".");
    ModuleFullPath(id)
}

impl ModuleGraph {
    pub fn build(entry_path: &Path) -> Result<Self, CranelispError> {
        let entry_path = entry_path
            .canonicalize()
            .map_err(|e| CranelispError::ModuleError {
                message: format!("cannot resolve path '{}': {}", entry_path.display(), e),
                file: None,
                span: (0, 0),
            })?;

        let project_root = entry_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf();

        let lib_dir = find_lib_dir(&project_root);

        let mut modules = HashMap::new();
        let mut visit_stack = Vec::new();
        let mut visited = HashSet::new();

        // Discover the entry module and all dependencies.
        // Prelude is discovered automatically via implicit imports.
        Self::discover(
            &entry_path,
            &project_root,
            lib_dir.as_deref(),
            &mut modules,
            &mut visit_stack,
            &mut visited,
        )?;

        // Topological sort: Kahn's algorithm
        let compile_order = Self::topo_sort(&modules)?;

        Ok(ModuleGraph {
            modules,
            compile_order,
        })
    }

    fn discover(
        file_path: &Path,
        project_root: &Path,
        lib_dir: Option<&Path>,
        modules: &mut HashMap<ModuleFullPath, ModuleInfo>,
        visit_stack: &mut Vec<ModuleFullPath>,
        visited: &mut HashSet<ModuleFullPath>,
    ) -> Result<ModuleFullPath, CranelispError> {
        // Determine if this is a lib module and compute effective roots
        let is_lib = lib_dir.is_some_and(|ld| file_path.starts_with(ld));
        let effective_root = if is_lib { lib_dir.unwrap() } else { project_root };
        let effective_lib: Option<&Path> = if is_lib { None } else { lib_dir };

        // Compute module ID relative to effective root
        let module_id = if visit_stack.is_empty() {
            // Entry file → stem only
            let stem = file_path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("");
            ModuleFullPath(stem.to_string())
        } else {
            path_to_module_full_path(file_path, effective_root)
        };

        // Cycle detection
        if visit_stack.contains(&module_id) {
            let cycle: Vec<String> = visit_stack
                .iter()
                .skip_while(|id| *id != &module_id)
                .map(|id| id.0.clone())
                .collect();
            return Err(CranelispError::ModuleError {
                message: format!(
                    "circular module dependency: {} → {}",
                    cycle.join(" → "),
                    module_id.0,
                ),
                file: Some(file_path.to_path_buf()),
                span: (0, 0),
            });
        }

        // Already processed
        if visited.contains(&module_id) {
            return Ok(module_id);
        }

        visit_stack.push(module_id.clone());

        // Read and parse source
        let source =
            fs::read_to_string(file_path).map_err(|e| CranelispError::ModuleError {
                message: format!("cannot read '{}': {}", file_path.display(), e),
                file: Some(file_path.to_path_buf()),
                span: (0, 0),
            })?;

        let all_sexps =
            crate::sexp::parse_sexps(&source).map_err(|e| CranelispError::ModuleError {
                message: format!("in module '{}': {}", file_path.display(), e),
                file: Some(file_path.to_path_buf()),
                span: (0, 0),
            })?;

        let mut decls =
            extract_module_decls(all_sexps).map_err(|e| CranelispError::ModuleError {
                message: format!("in module '{}': {}", file_path.display(), e),
                file: Some(file_path.to_path_buf()),
                span: (0, 0),
            })?;

        // Inject implicit (import [macros [*]]) for all modules.
        // The macros module (SList, Sexp) is needed by expanded macro code.
        if !decls.imports.iter().any(|i| i.module_path == "macros") {
            decls.imports.push(ImportSpec {
                module_path: "macros".to_string(),
                alias: None,
                names: ImportNames::Glob,
                span: (0, 0),
            });
        }

        // Inject implicit (import [prelude [*]]) for non-prelude modules,
        // but only if a prelude is actually discoverable at a root location.
        if module_id.short_name() != "prelude"
            && !decls.imports.iter().any(|i| i.module_path == "prelude")
            && resolve_root_module("prelude", effective_root, effective_lib).is_some()
        {
            decls.imports.push(ImportSpec {
                module_path: "prelude".to_string(),
                alias: None,
                names: ImportNames::Glob,
                span: (0, 0),
            });
        }

        // Resolve child modules from (mod ...) declarations
        let mut dependencies = Vec::new();
        for (child_name, span) in &decls.mod_names {
            let child_path =
                resolve_module(child_name, file_path, effective_root, effective_lib)
                    .map_err(|e| match e {
                        CranelispError::ModuleError { message, file, .. } => {
                            CranelispError::ModuleError {
                                message,
                                file,
                                span: *span,
                            }
                        }
                        other => other,
                    })?;
            let child_id = Self::discover(
                &child_path,
                project_root,
                lib_dir,
                modules,
                visit_stack,
                visited,
            )?;
            dependencies.push(child_id);
        }

        // Resolve export dependencies
        for export in &decls.exports {
            if is_synthetic_module(&export.module_path) {
                continue;
            }
            let export_path =
                resolve_module(&export.module_path, file_path, effective_root, effective_lib)
                    .map_err(|e| match e {
                        CranelispError::ModuleError { message, file, .. } => {
                            CranelispError::ModuleError {
                                message,
                                file,
                                span: export.span,
                            }
                        }
                        other => other,
                    })?;
            let child_id = Self::discover(
                &export_path,
                project_root,
                lib_dir,
                modules,
                visit_stack,
                visited,
            )?;
            dependencies.push(child_id);
        }

        // Discover root modules referenced by imports (auto-discovery).
        // Only searches project root + lib root, NOT submodules.
        for import in &decls.imports {
            let import_name = &import.module_path;
            if is_synthetic_module(import_name) {
                continue;
            }
            if let Some(import_path) =
                resolve_root_module(import_name, effective_root, effective_lib)
            {
                // Compute tentative module ID to check visit state
                let tentative_is_lib =
                    lib_dir.is_some_and(|ld| import_path.starts_with(ld));
                let tentative_root =
                    if tentative_is_lib { lib_dir.unwrap() } else { project_root };
                let tentative_id = path_to_module_full_path(&import_path, tentative_root);

                if visit_stack.contains(&tentative_id) {
                    // In-progress module: import is recorded but no dependency
                    // edge to avoid cycles (e.g., core's implicit prelude import
                    // when prelude is still being discovered)
                    continue;
                }

                if visited.contains(&tentative_id) {
                    // Already processed: add dependency edge
                    if !dependencies.contains(&tentative_id) {
                        dependencies.push(tentative_id);
                    }
                    continue;
                }

                // Not yet discovered: discover it and add dependency edge
                let child_id = Self::discover(
                    &import_path,
                    project_root,
                    lib_dir,
                    modules,
                    visit_stack,
                    visited,
                )?;
                if !dependencies.contains(&child_id) {
                    dependencies.push(child_id);
                }
            }
            // If not found at root level, silently skip — will error at
            // compile time if the import can't be resolved
        }

        visit_stack.pop();
        visited.insert(module_id.clone());

        modules.insert(
            module_id.clone(),
            ModuleInfo {
                id: module_id.clone(),
                file_path: file_path.to_path_buf(),
                source,
                sexps: decls.remaining,
                child_mod_names: decls.mod_names.clone(),
                dependencies,
                imports: decls.imports,
                exports: decls.exports,
                platforms: decls.platforms.clone(),
                is_lib,
            },
        );

        Ok(module_id)
    }

    fn topo_sort(
        modules: &HashMap<ModuleFullPath, ModuleInfo>,
    ) -> Result<Vec<ModuleFullPath>, CranelispError> {
        let mut in_degree: HashMap<&ModuleFullPath, usize> = HashMap::new();
        let mut dependents: HashMap<&ModuleFullPath, Vec<&ModuleFullPath>> = HashMap::new();

        for (id, info) in modules {
            in_degree.entry(id).or_insert(0);
            for dep in &info.dependencies {
                *in_degree.entry(dep).or_insert(0) += 0; // ensure dep is in map
                dependents.entry(dep).or_default().push(id);
            }
            *in_degree.entry(id).or_insert(0) = info.dependencies.len();
        }

        let mut queue: Vec<&ModuleFullPath> = in_degree
            .iter()
            .filter(|&(_, &deg)| deg == 0)
            .map(|(id, _)| *id)
            .collect();
        // Sort for deterministic order
        queue.sort_by(|a, b| a.0.cmp(&b.0));

        let mut result = Vec::new();
        while let Some(id) = queue.pop() {
            result.push(id.clone());
            if let Some(deps) = dependents.get(id) {
                for dep_id in deps {
                    if let Some(deg) = in_degree.get_mut(dep_id) {
                        *deg -= 1;
                        if *deg == 0 {
                            queue.push(dep_id);
                            queue.sort_by(|a, b| a.0.cmp(&b.0));
                        }
                    }
                }
            }
        }

        if result.len() != modules.len() {
            // This shouldn't happen if cycle detection works, but just in case
            return Err(CranelispError::ModuleError {
                message: "internal error: topological sort did not include all modules".to_string(),
                file: None,
                span: (0, 0),
            });
        }

        Ok(result)
    }
}

/// Resolve import declarations for a module into (bare_name, source_module) pairs.
/// Used by both batch compilation and REPL module loading.
pub fn resolve_module_imports(
    imports: &[ImportSpec],
    tc: &TypeChecker,
    mod_name_to_short: &std::collections::HashMap<String, String>,
) -> Result<Vec<(String, String)>, CranelispError> {
    let mut resolved = Vec::new();

    for import in imports {
        let source_short = mod_name_to_short
            .get(&import.module_path)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "import: module '{}' not found (did you forget a (mod {}) declaration?)",
                    import.module_path, import.module_path
                ),
                file: None,
                span: import.span,
            })?
            .clone();

        match &import.names {
            ImportNames::Specific(names) => {
                let public = tc.get_module_public_names(&source_short);
                for name in names {
                    if !public.contains(name) {
                        return Err(CranelispError::ModuleError {
                            message: format!(
                                "import: '{}' is not a public name in module '{}'",
                                name, import.module_path
                            ),
                            file: None,
                            span: import.span,
                        });
                    }
                    resolved.push((name.clone(), source_short.clone()));
                }
            }
            ImportNames::Glob => {
                let public = tc.get_module_public_names(&source_short);
                for name in public {
                    resolved.push((name, source_short.clone()));
                }
            }
            ImportNames::MemberGlob(type_or_trait) => {
                let public = tc.get_module_public_names(&source_short);
                let qualified_type = format!("{}/{}", source_short, type_or_trait);
                if let Some(tdi) = tc.resolve_type_def_via_modules(&qualified_type) {
                    for ctor in &tdi.constructors {
                        if public.contains(&ctor.name) {
                            resolved.push((ctor.name.clone(), source_short.clone()));
                        }
                    }
                } else if let Some(trait_decl) = tc.get_trait(type_or_trait) {
                    for method in &trait_decl.methods {
                        resolved.push((method.name.clone(), source_short.clone()));
                    }
                } else {
                    return Err(CranelispError::ModuleError {
                        message: format!(
                            "import: '{}' is not a type or trait in module '{}'",
                            type_or_trait, import.module_path
                        ),
                        file: None,
                        span: import.span,
                    });
                }
            }
            ImportNames::None => {
                // Alias-only import — no bare names to install
            }
        }
    }

    Ok(resolved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::parse_sexps;

    #[test]
    fn extract_mod_decls_basic() {
        let sexps = parse_sexps("(mod util) (defn main [] (pure 0))").unwrap();
        let (mods, remaining) = extract_mod_decls(sexps);
        assert_eq!(mods.len(), 1);
        assert_eq!(mods[0].0, "util");
        assert_eq!(remaining.len(), 1);
    }

    #[test]
    fn extract_mod_decls_multiple() {
        let sexps = parse_sexps("(mod util) (mod db) (defn main [] (pure 0))").unwrap();
        let (mods, remaining) = extract_mod_decls(sexps);
        assert_eq!(mods.len(), 2);
        assert_eq!(mods[0].0, "util");
        assert_eq!(mods[1].0, "db");
        assert_eq!(remaining.len(), 1);
    }

    #[test]
    fn extract_mod_decls_none() {
        let sexps = parse_sexps("(defn main [] (pure 0))").unwrap();
        let (mods, remaining) = extract_mod_decls(sexps);
        assert!(mods.is_empty());
        assert_eq!(remaining.len(), 1);
    }

    #[test]
    fn path_to_module_full_path_simple() {
        let root = Path::new("/project");
        let file = Path::new("/project/util.cl");
        assert_eq!(
            path_to_module_full_path(file, root),
            ModuleFullPath("util".to_string())
        );
    }

    #[test]
    fn path_to_module_full_path_nested() {
        let root = Path::new("/project");
        let file = Path::new("/project/app/handler.cl");
        assert_eq!(
            path_to_module_full_path(file, root),
            ModuleFullPath("app.handler".to_string())
        );
    }

    #[test]
    fn resolve_module_sibling() {
        let dir = std::env::temp_dir().join("cranelisp_test_resolve_sibling");
        let _ = fs::create_dir_all(&dir);
        let parent = dir.join("main.cl");
        let child = dir.join("util.cl");
        fs::write(&parent, "").unwrap();
        fs::write(&child, "").unwrap();

        let result = resolve_module("util", &parent, &dir, None).unwrap();
        assert_eq!(result, child);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn resolve_module_child_dir() {
        let dir = std::env::temp_dir().join("cranelisp_test_resolve_child_dir");
        let _ = fs::create_dir_all(dir.join("main"));
        let parent = dir.join("main.cl");
        let child = dir.join("main").join("util.cl");
        fs::write(&parent, "").unwrap();
        fs::write(&child, "").unwrap();

        let result = resolve_module("util", &parent, &dir, None).unwrap();
        assert_eq!(result, child);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn resolve_module_child_dir_priority() {
        // Child dir takes priority over sibling
        let dir = std::env::temp_dir().join("cranelisp_test_resolve_priority");
        let _ = fs::create_dir_all(dir.join("main"));
        let parent = dir.join("main.cl");
        let child_dir = dir.join("main").join("util.cl");
        let sibling = dir.join("util.cl");
        fs::write(&parent, "").unwrap();
        fs::write(&child_dir, "").unwrap();
        fs::write(&sibling, "").unwrap();

        let result = resolve_module("util", &parent, &dir, None).unwrap();
        assert_eq!(result, child_dir);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn resolve_module_not_found() {
        let dir = std::env::temp_dir().join("cranelisp_test_resolve_missing");
        let _ = fs::create_dir_all(&dir);
        let parent = dir.join("main.cl");
        fs::write(&parent, "").unwrap();

        let result = resolve_module("nonexistent", &parent, &dir, None);
        assert!(result.is_err());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn resolve_module_lib_fallback() {
        let dir = std::env::temp_dir().join("cranelisp_test_resolve_lib");
        let lib = dir.join("lib");
        let _ = fs::create_dir_all(&lib);
        let parent = dir.join("main.cl");
        let lib_mod = lib.join("utils.cl");
        fs::write(&parent, "").unwrap();
        fs::write(&lib_mod, "").unwrap();

        let result = resolve_module("utils", &parent, &dir, Some(&lib)).unwrap();
        assert_eq!(result, lib_mod);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn resolve_root_module_finds_project_root() {
        let dir = std::env::temp_dir().join("cranelisp_test_root_module");
        let _ = fs::create_dir_all(&dir);
        let target = dir.join("math.cl");
        fs::write(&target, "").unwrap();

        let result = resolve_root_module("math", &dir, None);
        assert_eq!(result, Some(target));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn resolve_root_module_finds_lib() {
        let dir = std::env::temp_dir().join("cranelisp_test_root_module_lib");
        let lib = dir.join("lib");
        let _ = fs::create_dir_all(&lib);
        let target = lib.join("core.cl");
        fs::write(&target, "").unwrap();

        let result = resolve_root_module("core", &dir, Some(&lib));
        assert_eq!(result, Some(target));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn module_graph_single_file() {
        let dir = std::env::temp_dir().join("cranelisp_test_graph_single");
        let _ = fs::create_dir_all(&dir);
        let main_path = dir.join("main.cl");
        fs::write(&main_path, "(defn main [] (pure 0))").unwrap();

        let graph = ModuleGraph::build(&main_path).unwrap();
        // +2 for auto-discovered prelude + core, +7 for core submodules (dev fallback)
        assert_eq!(graph.modules.len(), 10);
        assert_eq!(graph.compile_order.len(), 10);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn module_graph_two_files() {
        let dir = std::env::temp_dir().join("cranelisp_test_graph_two");
        let _ = fs::create_dir_all(&dir);
        let main_path = dir.join("main.cl");
        let util_path = dir.join("util.cl");
        fs::write(&main_path, "(mod util) (defn main [] (pure 0))").unwrap();
        fs::write(&util_path, "(defn helper [:Int x] :Int (+ x 1))").unwrap();

        let graph = ModuleGraph::build(&main_path).unwrap();
        // +2 for auto-discovered prelude + core, +7 for core submodules
        assert_eq!(graph.modules.len(), 11);
        assert_eq!(graph.compile_order.len(), 11);
        // util should come before main in compile order (leaf first)
        let util_idx = graph
            .compile_order
            .iter()
            .position(|id| id.short_name() == "util")
            .unwrap();
        let main_idx = graph
            .compile_order
            .iter()
            .position(|id| id.short_name() == "main")
            .unwrap();
        assert!(util_idx < main_idx);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn module_graph_cycle_detection() {
        let dir = std::env::temp_dir().join("cranelisp_test_graph_cycle");
        let _ = fs::create_dir_all(&dir);
        let a_path = dir.join("a.cl");
        let b_path = dir.join("b.cl");
        // a depends on b, b depends on a
        fs::write(&a_path, "(mod b)").unwrap();
        fs::write(&b_path, "(mod a)").unwrap();

        let result = ModuleGraph::build(&a_path);
        assert!(result.is_err());
        let err = result.unwrap_err();
        let msg = format!("{}", err);
        assert!(
            msg.contains("circular"),
            "error should mention circular: {}",
            msg
        );

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn module_graph_diamond() {
        let dir = std::env::temp_dir().join("cranelisp_test_graph_diamond");
        let _ = fs::create_dir_all(&dir);
        // main depends on a and b, both depend on shared
        fs::write(
            dir.join("main.cl"),
            "(mod a) (mod b) (defn main [] (pure 0))",
        )
        .unwrap();
        fs::write(dir.join("a.cl"), "(mod shared) (defn a-fn [] (pure 0))").unwrap();
        fs::write(dir.join("b.cl"), "(mod shared) (defn b-fn [] (pure 0))").unwrap();
        fs::write(dir.join("shared.cl"), "(defn shared-fn [:Int x] :Int x)").unwrap();

        let graph = ModuleGraph::build(&dir.join("main.cl")).unwrap();
        // +2 for auto-discovered prelude + core, +7 for core submodules
        assert_eq!(graph.modules.len(), 13);
        // shared should come before a and b
        let shared_idx = graph
            .compile_order
            .iter()
            .position(|id| id.short_name() == "shared")
            .unwrap();
        let a_idx = graph
            .compile_order
            .iter()
            .position(|id| id.short_name() == "a")
            .unwrap();
        let b_idx = graph
            .compile_order
            .iter()
            .position(|id| id.short_name() == "b")
            .unwrap();
        let main_idx = graph
            .compile_order
            .iter()
            .position(|id| id.short_name() == "main")
            .unwrap();
        assert!(shared_idx < a_idx);
        assert!(shared_idx < b_idx);
        assert!(a_idx < main_idx);
        assert!(b_idx < main_idx);

        let _ = fs::remove_dir_all(&dir);
    }

    // ── extract_module_decls tests ──────────────────────────────────────

    #[test]
    fn extract_module_decls_mod_only() {
        let sexps = parse_sexps("(mod util) (defn main [] (pure 0))").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.mod_names.len(), 1);
        assert_eq!(decls.mod_names[0].0, "util");
        assert!(decls.imports.is_empty());
        assert!(decls.exports.is_empty());
        assert_eq!(decls.remaining.len(), 1);
    }

    #[test]
    fn extract_module_decls_import_specific() {
        let sexps = parse_sexps("(import [core.option [Some None]])").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.imports.len(), 1);
        assert_eq!(decls.imports[0].module_path, "core.option");
        assert_eq!(decls.imports[0].alias, None);
        assert_eq!(
            decls.imports[0].names,
            ImportNames::Specific(vec!["Some".to_string(), "None".to_string()])
        );
    }

    #[test]
    fn extract_module_decls_import_glob() {
        let sexps = parse_sexps("(import [core.math [*]])").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.imports.len(), 1);
        assert_eq!(decls.imports[0].module_path, "core.math");
        assert_eq!(decls.imports[0].names, ImportNames::Glob);
    }

    #[test]
    fn extract_module_decls_import_member_glob() {
        let sexps = parse_sexps("(import [core.fmt [Display.*]])").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.imports.len(), 1);
        assert_eq!(decls.imports[0].module_path, "core.fmt");
        assert_eq!(
            decls.imports[0].names,
            ImportNames::MemberGlob("Display".to_string())
        );
    }

    #[test]
    fn extract_module_decls_import_alias() {
        let sexps = parse_sexps("(import [(core.string str) [concat join]])").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.imports.len(), 1);
        assert_eq!(decls.imports[0].module_path, "core.string");
        assert_eq!(decls.imports[0].alias, Some("str".to_string()));
        assert_eq!(
            decls.imports[0].names,
            ImportNames::Specific(vec!["concat".to_string(), "join".to_string()])
        );
    }

    #[test]
    fn extract_module_decls_import_alias_only() {
        let sexps = parse_sexps("(import [(core.option opt) []])").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.imports.len(), 1);
        assert_eq!(decls.imports[0].module_path, "core.option");
        assert_eq!(decls.imports[0].alias, Some("opt".to_string()));
        assert_eq!(decls.imports[0].names, ImportNames::None);
    }

    #[test]
    fn extract_module_decls_import_multiple_modules() {
        let sexps = parse_sexps("(import [core.option [Some None] core.math [*]])").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.imports.len(), 2);
        assert_eq!(decls.imports[0].module_path, "core.option");
        assert_eq!(decls.imports[1].module_path, "core.math");
        assert_eq!(decls.imports[1].names, ImportNames::Glob);
    }

    #[test]
    fn extract_module_decls_export() {
        let sexps = parse_sexps("(export [core.option [Option Some None]])").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert!(decls.imports.is_empty());
        assert_eq!(decls.exports.len(), 1);
        assert_eq!(decls.exports[0].module_path, "core.option");
        assert_eq!(
            decls.exports[0].names,
            ImportNames::Specific(vec![
                "Option".to_string(),
                "Some".to_string(),
                "None".to_string()
            ])
        );
    }

    #[test]
    fn extract_module_decls_mixed() {
        let sexps = parse_sexps(
            "(mod util) (import [util [helper]]) (export [util [helper]]) (defn main [] (pure 0))",
        )
        .unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.mod_names.len(), 1);
        assert_eq!(decls.imports.len(), 1);
        assert_eq!(decls.exports.len(), 1);
        assert_eq!(decls.remaining.len(), 1);
    }

    #[test]
    fn extract_module_decls_missing_names_list() {
        let sexps = parse_sexps("(import [core.option])").unwrap();
        let result = extract_module_decls(sexps);
        assert!(result.is_err());
        let msg = format!("{}", result.unwrap_err());
        assert!(msg.contains("missing names list"), "got: {}", msg);
    }

    #[test]
    fn extract_module_decls_glob_not_alone() {
        let sexps = parse_sexps("(import [core.math [* foo]])").unwrap();
        let result = extract_module_decls(sexps);
        assert!(result.is_err());
        let msg = format!("{}", result.unwrap_err());
        assert!(msg.contains("must be the only element"), "got: {}", msg);
    }

    #[test]
    fn extract_module_decls_backward_compat() {
        // Existing programs with just (mod ...) should still work
        let sexps = parse_sexps("(mod a) (mod b) (defn main [] (pure 0))").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.mod_names.len(), 2);
        assert!(decls.imports.is_empty());
        assert!(decls.exports.is_empty());
        assert!(decls.platforms.is_empty());
        assert_eq!(decls.remaining.len(), 1);
    }

    // ── platform declaration tests ────────────────────────────────────

    #[test]
    fn extract_module_decls_platform_stdio() {
        let sexps = parse_sexps("(platform stdio) (defn main [] (pure 0))").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.platforms.len(), 1);
        assert_eq!(decls.platforms[0].0, "stdio");
        assert!(decls.platforms[0].1.is_none());
        assert_eq!(decls.remaining.len(), 1);
    }

    #[test]
    fn extract_module_decls_platform_with_explicit_path() {
        let sexps = parse_sexps(r#"(platform stdio "/path/to/lib.dylib") (defn main [] (pure 0))"#).unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.platforms.len(), 1);
        assert_eq!(decls.platforms[0].0, "stdio");
        assert_eq!(decls.platforms[0].1, Some("/path/to/lib.dylib".to_string()));
        assert_eq!(decls.remaining.len(), 1);
    }

    #[test]
    fn extract_module_decls_platform_multiple() {
        let sexps = parse_sexps("(platform stdio) (platform audio) (defn main [] (pure 0))").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.platforms.len(), 2);
        assert_eq!(decls.platforms[0].0, "stdio");
        assert_eq!(decls.platforms[1].0, "audio");
        assert_eq!(decls.remaining.len(), 1);
    }

    #[test]
    fn extract_module_decls_platform_missing_arg() {
        let sexps = parse_sexps("(platform)").unwrap();
        let result = extract_module_decls(sexps);
        assert!(result.is_err());
        let msg = format!("{}", result.unwrap_err());
        assert!(msg.contains("(platform name)"), "got: {}", msg);
    }

    #[test]
    fn extract_module_decls_platform_too_many_args() {
        let sexps = parse_sexps(r#"(platform stdio "path" "extra")"#).unwrap();
        let result = extract_module_decls(sexps);
        assert!(result.is_err());
        let msg = format!("{}", result.unwrap_err());
        assert!(msg.contains("(platform name)"), "got: {}", msg);
    }

    #[test]
    fn extract_module_decls_platform_mixed_with_other_decls() {
        let sexps = parse_sexps("(platform stdio) (mod util) (import [util [*]]) (defn main [] (pure 0))").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert_eq!(decls.platforms.len(), 1);
        assert_eq!(decls.platforms[0].0, "stdio");
        assert_eq!(decls.mod_names.len(), 1);
        assert_eq!(decls.imports.len(), 1);
        assert_eq!(decls.remaining.len(), 1);
    }

    #[test]
    fn extract_module_decls_no_platform_is_empty() {
        let sexps = parse_sexps("(defn main [] (pure 0))").unwrap();
        let decls = extract_module_decls(sexps).unwrap();
        assert!(decls.platforms.is_empty());
    }
}
