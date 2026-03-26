// Session persistence: regenerate module source from symbol table and save to disk.
//
// The REPL accumulates definitions interactively. After each definition-like
// input (defn, deftype, deftrait, impl, defmacro, import, platform), we
// regenerate the module's `.cl` file from the symbol table and write it
// atomically (temp file + rename).
//
// On next REPL startup, the saved file is loaded through the normal module
// graph pipeline, restoring all definitions. Cache hits make this near-instant.
//
// Port of sketch/src/repl/save.rs adapted for the reimplementation's
// decomposed data model (SymbolTable + ModuleStructure + DefCodegen).

use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::Path;

use cranelisp_backend::codegen_types::DefCodegen;
use cranelisp_types::{
    DefKind, ExportSpec, ImportNames, ImportSpec, ModDecl, ModuleEntry,
    ModuleFullPath, ModuleStructure, Sexp, Symbol, SymbolTable,
};

/// Generate the source text for a module from its decomposed data.
///
/// Produces a complete `.cl` file in canonical order:
///   1. `(mod ...)` declarations
///   2. `(platform ...)` declarations
///   3. `(import ...)` — merged, excluding implicit prelude
///   4. `(export ...)`
///   5. `(deftrait ...)` declarations
///   6. `(deftype ...)` definitions
///   7. `(impl ...)` implementations
///   8. `(defn ...)` and `(defmacro ...)` — dependency-sorted
pub fn generate_module_source(
    sym_table: &SymbolTable,
    structure: &ModuleStructure,
    def_codegen: &HashMap<Symbol, DefCodegen>,
) -> String {
    let mut sections = Vec::new();

    // 1. Module declarations
    let mod_section = generate_mod_decls(&structure.mod_decls);
    if !mod_section.is_empty() {
        sections.push(mod_section);
    }

    // 2. Platform declarations
    let platform_section = generate_platforms(sym_table);
    if !platform_section.is_empty() {
        sections.push(platform_section);
    }

    // 3. Imports (merged, excluding implicit prelude)
    let import_section = generate_imports(&structure.import_specs);
    if !import_section.is_empty() {
        sections.push(import_section);
    }

    // 4. Exports (merged)
    let export_section = generate_exports(&structure.export_specs);
    if !export_section.is_empty() {
        sections.push(export_section);
    }

    // 5. Trait declarations
    let trait_section = generate_traits(sym_table);
    if !trait_section.is_empty() {
        sections.push(trait_section);
    }

    // 6. Type definitions
    let type_section = generate_types(sym_table);
    if !type_section.is_empty() {
        sections.push(type_section);
    }

    // 7. Trait implementations
    let impl_section = generate_impls(structure);
    if !impl_section.is_empty() {
        sections.push(impl_section);
    }

    // 8. Functions and macros (dependency-sorted)
    let fn_section = generate_fns_and_macros(sym_table, def_codegen);
    if !fn_section.is_empty() {
        sections.push(fn_section);
    }

    let mut result = sections.join("\n\n");
    if !result.is_empty() {
        result.push('\n');
    }
    result
}

/// Generate `(mod name)` declarations.
fn generate_mod_decls(mod_decls: &[ModDecl]) -> String {
    mod_decls
        .iter()
        .map(|decl| {
            if decl.is_private {
                format!("(mod- {})", decl.name)
            } else {
                format!("(mod {})", decl.name)
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Generate `(platform name)` declarations from PlatformDecl entries.
fn generate_platforms(sym_table: &SymbolTable) -> String {
    let mut platforms: Vec<String> = Vec::new();
    for (_sym, entry) in sym_table.symbols.iter() {
        if let ModuleEntry::PlatformDecl {
            platform_module, ..
        } = entry
        {
            // Extract the platform name from "platform.<name>"
            let name = platform_module.0
                .strip_prefix("platform.")
                .unwrap_or(&platform_module.0);
            platforms.push(format!("(platform {name})"));
        }
    }
    platforms.sort();
    platforms.join("\n")
}

/// Merge and generate a single `(import [...])` form.
fn generate_imports(specs: &[ImportSpec]) -> String {
    // Filter out implicit prelude import
    let filtered: Vec<&ImportSpec> = specs
        .iter()
        .filter(|s| {
            !(s.module_path.as_ref() == "prelude"
                && s.names == ImportNames::Glob
                && s.alias.is_none())
        })
        .collect();

    if filtered.is_empty() {
        return String::new();
    }

    // Group by module_path, merging names
    let mut groups: Vec<(ModuleFullPath, Option<cranelisp_types::ModuleName>, ImportNames)> =
        Vec::new();
    for spec in &filtered {
        if let Some(existing) = groups
            .iter_mut()
            .find(|(path, _, _)| *path == spec.module_path)
        {
            // Merge: Glob wins over Specific
            match (&existing.2, &spec.names) {
                (ImportNames::Glob, _) => {} // Glob already covers everything
                (_, ImportNames::Glob) => existing.2 = ImportNames::Glob,
                (ImportNames::Specific(existing_names), ImportNames::Specific(new_names)) => {
                    let mut merged = existing_names.clone();
                    for name in new_names {
                        if !merged.contains(name) {
                            merged.push(name.clone());
                        }
                    }
                    existing.2 = ImportNames::Specific(merged);
                }
                _ => {} // MemberGlob, None — keep existing
            }
        } else {
            groups.push((
                spec.module_path.clone(),
                spec.alias.clone(),
                spec.names.clone(),
            ));
        }
    }

    let mut parts = Vec::new();
    for (module_path, alias, names) in &groups {
        let mod_part = match alias {
            Some(a) => format!("({module_path} {a})"),
            None => module_path.as_ref().to_string(),
        };
        let names_part = match names {
            ImportNames::Glob => "[*]".to_string(),
            ImportNames::Specific(names) => {
                let name_strs: Vec<&str> = names.iter().map(|n| n.as_ref()).collect();
                format!("[{}]", name_strs.join(" "))
            }
            ImportNames::MemberGlob(parent) => format!("[{parent}.*]"),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{mod_part} {names_part}"));
    }

    format!("(import [{}])", parts.join(" "))
}

/// Merge and generate a single `(export [...])` form.
fn generate_exports(specs: &[ExportSpec]) -> String {
    if specs.is_empty() {
        return String::new();
    }

    let mut parts = Vec::new();
    for spec in specs {
        let names_part = match &spec.names {
            ImportNames::Glob => "[*]".to_string(),
            ImportNames::Specific(names) => {
                let name_strs: Vec<&str> = names.iter().map(|n| n.as_ref()).collect();
                format!("[{}]", name_strs.join(" "))
            }
            ImportNames::MemberGlob(parent) => format!("[{parent}.*]"),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{} {names_part}", spec.module_path));
    }

    format!("(export [{}])", parts.join(" "))
}

/// Generate trait declarations section.
fn generate_traits(sym_table: &SymbolTable) -> String {
    let mut items = Vec::new();
    for (name, entry) in sym_table.symbols.iter() {
        if let ModuleEntry::TraitDecl {
            sexp: Some(sexp), ..
        } = entry
        {
            items.push((name.as_ref().to_string(), sexp.format_indented(0)));
        }
    }
    items.sort_by(|a, b| a.0.cmp(&b.0));
    items
        .into_iter()
        .map(|(_, text)| text)
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Generate type definitions section.
fn generate_types(sym_table: &SymbolTable) -> String {
    let mut items = Vec::new();
    for (name, entry) in sym_table.symbols.iter() {
        if let ModuleEntry::TypeDef {
            sexp: Some(sexp), ..
        } = entry
        {
            items.push((name.as_ref().to_string(), sexp.format_indented(0)));
        }
    }
    items.sort_by(|a, b| a.0.cmp(&b.0));
    items
        .into_iter()
        .map(|(_, text)| text)
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Generate trait implementations section.
fn generate_impls(structure: &ModuleStructure) -> String {
    structure
        .impl_sexps
        .iter()
        .map(|impl_sexp| impl_sexp.sexp.format_indented(0))
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Generate functions and macros section, dependency-sorted.
fn generate_fns_and_macros(
    sym_table: &SymbolTable,
    def_codegen: &HashMap<Symbol, DefCodegen>,
) -> String {
    let mut items: Vec<(String, Sexp)> = Vec::new();

    for (name, entry) in sym_table.symbols.iter() {
        // Skip mangled names (impl methods like `show$Int`)
        if name.as_ref().contains('$') {
            continue;
        }
        match entry {
            ModuleEntry::Def { kind, .. } => {
                if matches!(kind.as_ref(), DefKind::UserFn { .. }) {
                    // Look up the sexp in def_codegen (separate from symbol table
                    // in the reimplementation's decomposed architecture).
                    if let Some(dc) = def_codegen.get(name)
                        && let Some(sexp) = &dc.sexp
                    {
                        items.push((name.as_ref().to_string(), sexp.clone()));
                    }
                }
            }
            ModuleEntry::Macro {
                sexp: Some(sexp), ..
            } => {
                items.push((name.as_ref().to_string(), sexp.clone()));
            }
            _ => {}
        }
    }

    let sorted = dependency_sort(items);
    sorted
        .into_iter()
        .map(|(_, sexp)| sexp.format_indented(0))
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Topological sort of named items based on symbol references in their bodies.
///
/// Uses Kahn's algorithm. Items with no dependencies come first; items
/// that depend on others come after their dependencies. Ties broken
/// alphabetically. Cycles (mutual recursion) are appended alphabetically.
fn dependency_sort(items: Vec<(String, Sexp)>) -> Vec<(String, Sexp)> {
    if items.len() <= 1 {
        return items;
    }

    let names: HashSet<String> = items.iter().map(|(n, _)| n.clone()).collect();

    // Build adjacency: item depends on other items whose names appear in its body
    let mut deps: HashMap<String, HashSet<String>> = HashMap::new();
    for (name, sexp) in &items {
        let mut refs = HashSet::new();
        collect_symbol_refs(sexp, &mut refs);
        let item_deps: HashSet<String> = refs
            .into_iter()
            .filter(|r| names.contains(r) && r != name)
            .collect();
        deps.insert(name.clone(), item_deps);
    }

    // Kahn's algorithm
    let mut in_degree: HashMap<String, usize> = HashMap::new();
    let mut dependents: HashMap<String, Vec<String>> = HashMap::new();
    for (name, _) in &items {
        in_degree.entry(name.clone()).or_insert(0);
    }
    for (name, item_deps) in &deps {
        for dep in item_deps {
            dependents
                .entry(dep.clone())
                .or_default()
                .push(name.clone());
            *in_degree.entry(name.clone()).or_insert(0) += 1;
        }
    }

    let mut queue: Vec<String> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(name, _)| name.clone())
        .collect();
    queue.sort_by(|a, b| b.cmp(a)); // reverse sort so pop() gives smallest

    let mut order = Vec::new();
    while let Some(name) = queue.pop() {
        order.push(name.clone());
        if let Some(dep_list) = dependents.get(&name) {
            for dep_name in dep_list {
                if let Some(deg) = in_degree.get_mut(dep_name) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push(dep_name.clone());
                        queue.sort_by(|a, b| b.cmp(a));
                    }
                }
            }
        }
    }

    // Any remaining items (cycles) get added alphabetically
    let ordered_set: HashSet<&str> = order.iter().map(|s| s.as_str()).collect();
    let mut remaining: Vec<String> = items
        .iter()
        .filter(|(n, _)| !ordered_set.contains(n.as_str()))
        .map(|(n, _)| n.clone())
        .collect();
    remaining.sort();
    order.extend(remaining);

    // Reorder items according to order
    let item_map: HashMap<String, Sexp> = items.into_iter().collect();
    order
        .into_iter()
        .filter_map(|name| {
            item_map
                .get(&name)
                .map(|sexp| (name.clone(), sexp.clone()))
        })
        .collect()
}

/// Collect all symbol names referenced in a sexp tree.
fn collect_symbol_refs(sexp: &Sexp, refs: &mut HashSet<String>) {
    match sexp {
        Sexp::Symbol(name, _)
            // Skip type annotations (colon-prefixed), keywords, etc.
            if !name.starts_with(':') && name != "&" => {
                refs.insert(name.clone());
        }
        Sexp::List(children, _) | Sexp::Bracket(children, _) => {
            for child in children {
                collect_symbol_refs(child, refs);
            }
        }
        _ => {}
    }
}

/// Write the generated source to the module's backing file.
///
/// Uses atomic write (temp file + rename) for safety.
/// Returns the content hash of the written source on success.
pub fn save_module_file(
    file_path: &Path,
    sym_table: &SymbolTable,
    structure: &ModuleStructure,
    def_codegen: &HashMap<Symbol, DefCodegen>,
) -> Option<String> {
    let source = generate_module_source(sym_table, structure, def_codegen);

    // Don't write empty files (no user definitions yet).
    if source.trim().is_empty() {
        return None;
    }

    let hash = cranelisp_backend::cache::hash_source(&source);
    if let Err(e) = atomic_write(file_path, &source) {
        eprintln!("Warning: failed to save {}: {e}", file_path.display());
        return None;
    }
    Some(hash)
}

/// Write content to a file atomically (write to temp, then rename).
fn atomic_write(path: &Path, content: &str) -> std::io::Result<()> {
    let dir = path.parent().unwrap_or_else(|| Path::new("."));
    if !dir.exists() {
        std::fs::create_dir_all(dir)?;
    }
    let tmp_path = path.with_extension("cl.tmp");
    let mut file = std::fs::File::create(&tmp_path)?;
    file.write_all(content.as_bytes())?;
    file.flush()?;
    drop(file);
    std::fs::rename(&tmp_path, path)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{Span, Sexp};

    fn sym(name: &str) -> Sexp {
        Sexp::Symbol(name.to_string(), Span::SYNTHETIC)
    }

    fn int(n: i64) -> Sexp {
        Sexp::Int(n, Span::SYNTHETIC)
    }

    fn list(children: Vec<Sexp>) -> Sexp {
        Sexp::List(children, Span::SYNTHETIC)
    }

    fn bracket(children: Vec<Sexp>) -> Sexp {
        Sexp::Bracket(children, Span::SYNTHETIC)
    }

    fn make_defn_sexp(name: &str, params: Vec<&str>, body: Sexp) -> Sexp {
        let param_sexps: Vec<Sexp> = params.into_iter().map(sym).collect();
        list(vec![sym("defn"), sym(name), bracket(param_sexps), body])
    }

    // spec: design/int/session-persistence.md §1 — imports filter prelude
    #[test]
    fn merge_imports_filters_prelude() {
        let specs = vec![ImportSpec {
            module_path: ModuleFullPath::from("prelude"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_imports(&specs), "");
    }

    // spec: design/int/session-persistence.md §1 — specific imports
    #[test]
    fn merge_imports_specific() {
        let specs = vec![ImportSpec {
            module_path: ModuleFullPath::from("core"),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from("foo"), Symbol::from("bar")]),
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_imports(&specs), "(import [core [foo bar]])");
    }

    // spec: design/int/session-persistence.md §1 — glob wins over specific
    #[test]
    fn merge_imports_glob_wins() {
        let specs = vec![
            ImportSpec {
                module_path: ModuleFullPath::from("core"),
                alias: None,
                names: ImportNames::Specific(vec![Symbol::from("foo")]),
                span: Span::SYNTHETIC,
            },
            ImportSpec {
                module_path: ModuleFullPath::from("core"),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
        ];
        assert_eq!(generate_imports(&specs), "(import [core [*]])");
    }

    // spec: design/int/session-persistence.md §1 — multiple modules
    #[test]
    fn merge_imports_multiple_modules() {
        let specs = vec![
            ImportSpec {
                module_path: ModuleFullPath::from("core"),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
            ImportSpec {
                module_path: ModuleFullPath::from("util"),
                alias: None,
                names: ImportNames::Specific(vec![Symbol::from("helper")]),
                span: Span::SYNTHETIC,
            },
        ];
        assert_eq!(
            generate_imports(&specs),
            "(import [core [*] util [helper]])"
        );
    }

    // spec: design/int/session-persistence.md §1 — dependency sort linear
    #[test]
    fn dependency_sort_linear() {
        let items = vec![
            (
                "b".to_string(),
                make_defn_sexp("b", vec![], list(vec![sym("a")])),
            ),
            ("a".to_string(), make_defn_sexp("a", vec![], int(1))),
        ];
        let sorted = dependency_sort(items);
        assert_eq!(sorted[0].0, "a");
        assert_eq!(sorted[1].0, "b");
    }

    // spec: design/int/session-persistence.md §1 — no deps = alphabetical
    #[test]
    fn dependency_sort_no_deps() {
        let items = vec![
            ("c".to_string(), make_defn_sexp("c", vec![], int(3))),
            ("a".to_string(), make_defn_sexp("a", vec![], int(1))),
            ("b".to_string(), make_defn_sexp("b", vec![], int(2))),
        ];
        let sorted = dependency_sort(items);
        assert_eq!(sorted[0].0, "a");
        assert_eq!(sorted[1].0, "b");
        assert_eq!(sorted[2].0, "c");
    }

    // spec: design/int/session-persistence.md §1 — cycles handled
    #[test]
    fn dependency_sort_cycle() {
        let items = vec![
            (
                "a".to_string(),
                make_defn_sexp("a", vec![], list(vec![sym("b")])),
            ),
            (
                "b".to_string(),
                make_defn_sexp("b", vec![], list(vec![sym("a")])),
            ),
        ];
        let sorted = dependency_sort(items);
        assert_eq!(sorted.len(), 2);
    }

    // spec: design/int/session-persistence.md §1 — empty exports
    #[test]
    fn generate_exports_empty() {
        assert_eq!(generate_exports(&[]), "");
    }

    // spec: design/int/session-persistence.md §1 — basic export
    #[test]
    fn generate_exports_basic() {
        let specs = vec![ExportSpec {
            module_path: ModuleFullPath::from("util"),
            names: ImportNames::Specific(vec![Symbol::from("helper")]),
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_exports(&specs), "(export [util [helper]])");
    }

    // spec: design/int/session-persistence.md §1 — empty source for empty module
    #[test]
    fn empty_module_produces_empty_source() {
        let sym_table = SymbolTable::new(ModuleFullPath::from("user"));
        let structure = ModuleStructure {
            path: ModuleFullPath::from("user"),
            file_path: None,
            mod_decls: vec![],
            import_specs: vec![],
            export_specs: vec![],
            platform_specs: vec![],
            impl_sexps: vec![],
            impls: vec![],
            dll_path: None,
        };
        let def_codegen = HashMap::new();
        let source = generate_module_source(&sym_table, &structure, &def_codegen);
        assert_eq!(source, "");
    }

    // spec: design/int/session-persistence.md §1 — mod decls
    #[test]
    fn generate_mod_decls_basic() {
        let decls = vec![ModDecl {
            name: cranelisp_types::ModuleName::from("sub"),
            is_private: false,
            inline_body: None,
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_mod_decls(&decls), "(mod sub)");
    }

    // spec: design/int/session-persistence.md §1 — private mod decls
    #[test]
    fn generate_mod_decls_private() {
        let decls = vec![ModDecl {
            name: cranelisp_types::ModuleName::from("internal"),
            is_private: true,
            inline_body: None,
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_mod_decls(&decls), "(mod- internal)");
    }
}
