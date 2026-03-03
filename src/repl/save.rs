use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::Path;

use crate::module::{CompiledModule, ExportSpec, ImportNames, ImportSpec, ModuleEntry};
use crate::sexp::Sexp;
use crate::typechecker::TypeChecker;

/// Generate the source text for a module from its CompiledModule data.
pub fn generate_module_source(cm: &CompiledModule, tc: &TypeChecker) -> String {
    let mut sections = Vec::new();

    // 1. Module declarations
    let mod_section = generate_mod_decls(&cm.mod_decls);
    if !mod_section.is_empty() {
        sections.push(mod_section);
    }

    // 1b. Platform declarations
    let platform_section = generate_platforms(cm);
    if !platform_section.is_empty() {
        sections.push(platform_section);
    }

    // 2. Imports (merged, excluding implicit prelude)
    let import_section = generate_imports(&cm.import_specs);
    if !import_section.is_empty() {
        sections.push(import_section);
    }

    // 3. Exports (merged)
    let export_section = generate_exports(&cm.export_specs);
    if !export_section.is_empty() {
        sections.push(export_section);
    }

    // 4. Trait declarations
    let trait_section = generate_traits(cm);
    if !trait_section.is_empty() {
        sections.push(trait_section);
    }

    // 5. Type definitions
    let type_section = generate_types(cm);
    if !type_section.is_empty() {
        sections.push(type_section);
    }

    // 6. Trait implementations
    let impl_section = generate_impls(cm, tc);
    if !impl_section.is_empty() {
        sections.push(impl_section);
    }

    // 7. Functions + macros (dependency-sorted)
    let fn_section = generate_fns_and_macros(cm, tc);
    if !fn_section.is_empty() {
        sections.push(fn_section);
    }

    let mut result = sections.join("\n\n");
    if !result.is_empty() {
        result.push('\n');
    }
    result
}

/// Generate `(platform name)` declarations from PlatformDecl entries.
fn generate_platforms(cm: &CompiledModule) -> String {
    let mut platforms: Vec<String> = Vec::new();
    for (sym, entry) in &cm.symbols {
        if let ModuleEntry::PlatformDecl {
            platform_module, ..
        } = entry
        {
            // Extract the platform name from "platform.<name>"
            let name = platform_module
                .0
                .strip_prefix("platform.")
                .unwrap_or(&platform_module.0);
            let _ = sym; // keyed by "platform.<name>" in symbols
            platforms.push(format!("(platform {})", name));
        }
    }
    platforms.sort();
    platforms.join("\n")
}

/// Generate `(mod name)` declarations.
fn generate_mod_decls(mod_decls: &[crate::names::ModuleName]) -> String {
    mod_decls
        .iter()
        .map(|name| format!("(mod {})", name))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Merge and generate a single `(import [...])` form.
fn generate_imports(specs: &[ImportSpec]) -> String {
    // Filter out implicit prelude import
    let filtered: Vec<&ImportSpec> = specs
        .iter()
        .filter(|s| {
            !(s.module_path == "prelude" && s.names == ImportNames::Glob && s.alias.is_none())
        })
        .collect();

    if filtered.is_empty() {
        return String::new();
    }

    // Group by module_path, merging names
    let mut groups: Vec<(String, Option<String>, ImportNames)> = Vec::new();
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
            Some(a) => format!("({} {})", module_path, a),
            None => module_path.clone(),
        };
        let names_part = match names {
            ImportNames::Glob => "[*]".to_string(),
            ImportNames::Specific(names) => format!("[{}]", names.join(" ")),
            ImportNames::MemberGlob(parent) => format!("[{}.*]", parent),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{} {}", mod_part, names_part));
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
            ImportNames::Specific(names) => format!("[{}]", names.join(" ")),
            ImportNames::MemberGlob(parent) => format!("[{}.*]", parent),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{} {}", spec.module_path, names_part));
    }

    format!("(export [{}])", parts.join(" "))
}

/// Generate trait declarations section.
fn generate_traits(cm: &CompiledModule) -> String {
    let mut items = Vec::new();
    for (name, entry) in &cm.symbols {
        if let ModuleEntry::TraitDecl {
            sexp: Some(sexp), ..
        } = entry
        {
            items.push((name.to_string(), sexp.format_indented(0)));
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
fn generate_types(cm: &CompiledModule) -> String {
    let mut items = Vec::new();
    for (name, entry) in &cm.symbols {
        if let ModuleEntry::TypeDef {
            sexp: Some(sexp), ..
        } = entry
        {
            items.push((name.to_string(), sexp.format_indented(0)));
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
fn generate_impls(cm: &CompiledModule, tc: &TypeChecker) -> String {
    cm.impl_sexps
        .iter()
        .map(|impl_sexp| qualify_sexp(&impl_sexp.sexp, tc).format_indented(0))
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Generate functions and macros section, dependency-sorted.
fn generate_fns_and_macros(cm: &CompiledModule, tc: &TypeChecker) -> String {
    let mut items: Vec<(String, Sexp)> = Vec::new();

    for (name, entry) in &cm.symbols {
        // Skip mangled names (impl methods like `show$Int`)
        if name.contains('$') {
            continue;
        }
        match entry {
            ModuleEntry::Def {
                kind:
                    crate::module::DefKind::UserFn {
                        codegen: crate::module::DefCodegen { sexp: Some(sexp), .. },
                        ..
                    },
                ..
            } => {
                items.push((name.to_string(), sexp.clone()));
            }
            ModuleEntry::Macro {
                sexp: Some(sexp), ..
            } => {
                items.push((name.to_string(), sexp.clone()));
            }
            _ => {}
        }
    }

    let sorted = dependency_sort(items);
    sorted
        .into_iter()
        .map(|(_, sexp)| qualify_sexp(&sexp, tc).format_indented(0))
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Qualify constructor and trait method references in a sexp tree.
/// Local variables, keywords, and operators are left unchanged.
pub fn qualify_sexp(sexp: &Sexp, tc: &TypeChecker) -> Sexp {
    match sexp {
        Sexp::Symbol(name, span) => {
            if let Some(qualified) = tc.qualify_name(name) {
                Sexp::Symbol(qualified, *span)
            } else {
                sexp.clone()
            }
        }
        Sexp::List(children, span) => {
            let qualified_children: Vec<Sexp> =
                children.iter().map(|c| qualify_sexp(c, tc)).collect();
            Sexp::List(qualified_children, *span)
        }
        Sexp::Bracket(children, span) => {
            let qualified_children: Vec<Sexp> =
                children.iter().map(|c| qualify_sexp(c, tc)).collect();
            Sexp::Bracket(qualified_children, *span)
        }
        // Int, Float, Bool, Str pass through unchanged
        _ => sexp.clone(),
    }
}

/// Topological sort of named items based on symbol references in their bodies.
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
        Sexp::Symbol(name, _) => {
            // Skip type annotations (colon-prefixed), keywords, etc.
            if !name.starts_with(':') && name != "&" {
                refs.insert(name.clone());
            }
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
/// Uses atomic write (temp file + rename) for safety.
/// Returns the SHA-256 hash of the written content on success.
pub fn save_module_file(cm: &CompiledModule, tc: &TypeChecker) -> Option<String> {
    let file_path = cm.file_path.as_ref()?;
    let source = generate_module_source(cm, tc);
    let hash = crate::cache::hash_source(&source);
    if let Err(e) = atomic_write(file_path, &source) {
        eprintln!("Warning: failed to save {}: {}", file_path.display(), e);
        return None;
    }
    Some(hash)
}

/// Write content to a file atomically (write to temp, then rename).
fn atomic_write(path: &Path, content: &str) -> std::io::Result<()> {
    let dir = path.parent().unwrap_or_else(|| Path::new("."));
    // Create parent directory if it doesn't exist
    if !dir.exists() {
        std::fs::create_dir_all(dir)?;
    }
    // Write to a temp file in the same directory, then rename
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
    use crate::sexp::parse_sexp;

    #[test]
    fn merge_imports_filters_prelude() {
        let specs = vec![ImportSpec {
            module_path: "prelude".to_string(),
            alias: None,
            names: ImportNames::Glob,
            span: (0, 0),
        }];
        assert_eq!(generate_imports(&specs), "");
    }

    #[test]
    fn merge_imports_specific() {
        let specs = vec![ImportSpec {
            module_path: "core".to_string(),
            alias: None,
            names: ImportNames::Specific(vec!["foo".to_string(), "bar".to_string()]),
            span: (0, 0),
        }];
        assert_eq!(generate_imports(&specs), "(import [core [foo bar]])");
    }

    #[test]
    fn merge_imports_glob() {
        let specs = vec![ImportSpec {
            module_path: "core".to_string(),
            alias: None,
            names: ImportNames::Glob,
            span: (0, 0),
        }];
        assert_eq!(generate_imports(&specs), "(import [core [*]])");
    }

    #[test]
    fn merge_imports_glob_wins() {
        let specs = vec![
            ImportSpec {
                module_path: "core".to_string(),
                alias: None,
                names: ImportNames::Specific(vec!["foo".to_string()]),
                span: (0, 0),
            },
            ImportSpec {
                module_path: "core".to_string(),
                alias: None,
                names: ImportNames::Glob,
                span: (0, 0),
            },
        ];
        assert_eq!(generate_imports(&specs), "(import [core [*]])");
    }

    #[test]
    fn merge_imports_multiple_modules() {
        let specs = vec![
            ImportSpec {
                module_path: "core".to_string(),
                alias: None,
                names: ImportNames::Glob,
                span: (0, 0),
            },
            ImportSpec {
                module_path: "util".to_string(),
                alias: None,
                names: ImportNames::Specific(vec!["helper".to_string()]),
                span: (0, 0),
            },
        ];
        assert_eq!(
            generate_imports(&specs),
            "(import [core [*] util [helper]])"
        );
    }

    #[test]
    fn dependency_sort_linear() {
        let items = vec![
            (
                "b".to_string(),
                parse_sexp("(defn b [] (a))").unwrap(),
            ),
            ("a".to_string(), parse_sexp("(defn a [] 1)").unwrap()),
        ];
        let sorted = dependency_sort(items);
        assert_eq!(sorted[0].0, "a");
        assert_eq!(sorted[1].0, "b");
    }

    #[test]
    fn dependency_sort_no_deps() {
        let items = vec![
            ("c".to_string(), parse_sexp("(defn c [] 3)").unwrap()),
            ("a".to_string(), parse_sexp("(defn a [] 1)").unwrap()),
            ("b".to_string(), parse_sexp("(defn b [] 2)").unwrap()),
        ];
        let sorted = dependency_sort(items);
        // No dependencies, should be alphabetical
        assert_eq!(sorted[0].0, "a");
        assert_eq!(sorted[1].0, "b");
        assert_eq!(sorted[2].0, "c");
    }

    #[test]
    fn dependency_sort_cycle() {
        let items = vec![
            (
                "a".to_string(),
                parse_sexp("(defn a [] (b))").unwrap(),
            ),
            (
                "b".to_string(),
                parse_sexp("(defn b [] (a))").unwrap(),
            ),
        ];
        let sorted = dependency_sort(items);
        // Cycle members should still appear (alphabetical tiebreak)
        assert_eq!(sorted.len(), 2);
    }

    #[test]
    fn generate_exports_empty() {
        assert_eq!(generate_exports(&[]), "");
    }

    #[test]
    fn generate_exports_basic() {
        let specs = vec![ExportSpec {
            module_path: "util".to_string(),
            names: ImportNames::Specific(vec!["helper".to_string()]),
            span: (0, 0),
        }];
        assert_eq!(generate_exports(&specs), "(export [util [helper]])");
    }
}
