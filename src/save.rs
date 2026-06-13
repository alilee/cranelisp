// Session persistence: source regeneration and atomic write.
//
// Implements repl/spec.md §15 and design/int/session-persistence.md.
// Regenerates the backing .cl file for the current module from the
// symbol table after each definition.
//
// Sprint 58 Step 5a (Decision 33): the structural decls
// (imports/exports/platforms/submodules) live as fields on `SymbolTable`
// itself. The transitional `ModuleStructure` parallel store on
// `SharedState.module_structures` dissolves; this module reads everything
// from `SymbolTable`.

use std::collections::HashSet;
use std::io::Write;
use std::path::Path;

use cranelisp_types::{
    ExportSpec, FQSymbol, ImportNames, ImportSpec, ModDecl, ModuleEntry,
    ModuleFullPath, PlatformSpec, Sexp,
};

use dashmap::DashMap;

use crate::session_v4::Introspection;

// ---------------------------------------------------------------------------
// Source regeneration — pure function
// ---------------------------------------------------------------------------

/// Generate complete module source from the module's `SymbolTable`.
///
/// Pure function: reads data, returns source text. Sections appear in
/// the order specified by design/int/session-persistence.md §1.3:
///   1. mod decls
///   2. platform decls
///   3. imports (merged, prelude filtered)
///   4. exports (merged)
///   5. traits (alphabetical)
///   6. types (alphabetical)
///   7. impls (from TraitImpl entries)
///   8. fns and macros (dependency-sorted)
///
/// Sprint 58 Step 5a: structural decls read directly from
/// `symbol_table.{submodules, platforms, imports, exports}`. The implicit
/// prelude `(import [prelude [*]])` is suppressed by `generate_imports`
/// itself — `imports` records only user-authored forms (CP3 / option (b),
/// see `design/int/symbol-table-cache.md` §3) but the filter remains as a
/// belt-and-braces guard.
pub fn generate_module_source(
    symbol_table: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    let mut sections = Vec::new();

    // 1. Module declarations
    let mod_section = generate_mod_decls(&symbol_table.submodules);
    if !mod_section.is_empty() {
        sections.push(mod_section);
    }

    // 2. Platform declarations
    let platform_section = generate_platforms(&symbol_table.platforms);
    if !platform_section.is_empty() {
        sections.push(platform_section);
    }

    // 3. Imports (merged, prelude filtered)
    let import_section = generate_imports(&symbol_table.imports);
    if !import_section.is_empty() {
        sections.push(import_section);
    }

    // 4. Exports (merged)
    let export_section = generate_exports(&symbol_table.exports);
    if !export_section.is_empty() {
        sections.push(export_section);
    }

    // 5. Trait declarations (alphabetical)
    let trait_section = generate_traits(symbol_table, introspection, module_path);
    if !trait_section.is_empty() {
        sections.push(trait_section);
    }

    // 6. Type definitions (alphabetical)
    let type_section = generate_types(symbol_table, introspection, module_path);
    if !type_section.is_empty() {
        sections.push(type_section);
    }

    // 7. Trait implementations
    let impl_section = generate_impls(symbol_table);
    if !impl_section.is_empty() {
        sections.push(impl_section);
    }

    // 8. Functions and macros (dependency-sorted)
    let fn_section = generate_fns_and_macros(symbol_table, introspection, module_path);
    if !fn_section.is_empty() {
        sections.push(fn_section);
    }

    let mut result = sections.join("\n\n");
    if !result.is_empty() {
        result.push('\n');
    }
    result
}

// ---------------------------------------------------------------------------
// Section generators
// ---------------------------------------------------------------------------

fn generate_mod_decls(decls: &[ModDecl]) -> String {
    decls
        .iter()
        .map(|decl| {
            let keyword = if decl.visibility == cranelisp_types::Visibility::Private {
                "mod-"
            } else {
                "mod"
            };
            format!("({} {})", keyword, decl.name)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn generate_platforms(specs: &[PlatformSpec]) -> String {
    let mut platforms: Vec<String> = specs
        .iter()
        .map(|spec| format!("(platform {})", spec.name))
        .collect();
    platforms.sort();
    platforms.dedup();
    platforms.join("\n")
}

/// Merge and generate a single `(import [...])` form.
/// Filters out the implicit prelude import.
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
        let mod_path = spec.module_path.to_string();
        let alias = spec.alias.as_ref().map(|a| a.to_string());
        if let Some(existing) = groups.iter_mut().find(|(path, _, _)| *path == mod_path) {
            // Merge: Glob wins over Specific
            match (&existing.2, &spec.names) {
                (ImportNames::Glob, _) => {}
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
                _ => {}
            }
        } else {
            groups.push((mod_path, alias, spec.names.clone()));
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
            ImportNames::Specific(names) => {
                let name_strs: Vec<&str> = names.iter().map(|n| n.as_ref()).collect();
                format!("[{}]", name_strs.join(" "))
            }
            ImportNames::MemberGlob(parent) => format!("[{}.*]", parent),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{} {}", mod_part, names_part));
    }

    format!("(import [{}])", parts.join(" "))
}

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
            ImportNames::MemberGlob(parent) => format!("[{}.*]", parent),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{} {}", spec.module_path, names_part));
    }

    format!("(export [{}])", parts.join(" "))
}

/// Look up the canonical `sexp` for a symbol from the Introspection DashMap
/// (per Decision 41: `Introspection` is the single store for source/sexp/
/// expanded/clif_ir/disasm/code_size across all `DefKind` variants and
/// `ModuleEntry::{TypeDef, TraitDecl}`). Returns `None` for cache-loaded
/// modules whose Introspection has not been rehydrated — tracked at
/// FIXME 0220 (lazy re-read on demand); the symmetric None-skip is the
/// correct behaviour at this site.
fn introspection_sexp(
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
    name: &cranelisp_types::Symbol,
) -> Option<Sexp> {
    let fq = FQSymbol {
        module: module_path.clone(),
        symbol: name.clone(),
    };
    introspection
        .and_then(|m| m.get(&fq))
        .and_then(|intro| intro.sexp.clone())
}

fn generate_traits(
    st: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    let mut items: Vec<(String, String)> = Vec::new();
    for (name, entry) in st.all_symbols() {
        if let ModuleEntry::TraitDecl { .. } = entry
            && let Some(sexp) = introspection_sexp(introspection, module_path, name)
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

fn generate_types(
    st: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    let mut items: Vec<(String, String)> = Vec::new();
    for (name, entry) in st.all_symbols() {
        if let ModuleEntry::TypeDef { .. } = entry
            && let Some(sexp) = introspection_sexp(introspection, module_path, name)
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

/// Generate trait implementations. Uses sexp from TraitImpl entries
/// on the symbol table (if they have sexp fields). Falls back to
/// introspection for impl method sources.
fn generate_impls(st: &crate::code::SessionSymbolTable) -> String {
    // TraitImpl entries currently don't have an sexp field (see §2.1 gap).
    // For now, skip impl regeneration — impls will need the sexp field
    // added to ModuleEntry::TraitImpl as a prerequisite (design §9.1).
    // This allows basic persistence (defn, deftype, import) to work.
    let _ = st;
    String::new()
}

fn generate_fns_and_macros(
    st: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    // Partition into macros and non-macro fns. Macros MUST be emitted BEFORE
    // the functions that use them (S77 W-MacroTrait, FIXME 0299): defmacro-
    // before-use is normative (`macro-availability-model.md` §0.2), and the
    // regenerated file must be round-trip-safe (§0.3 — a cached REPL restart
    // recompiles the regenerated `user.cl` under the SAME availability rules
    // the live session used). The callee-list `dependency_sort` does NOT model
    // the macro-use edge (a macro call is not a `callees()` entry), so without
    // this partition `(defn main [] (twice 21))` could be emitted before
    // `(defmacro twice …)`, and the restart would reject `twice` as a forward
    // reference. Per the locked model a macro depends only on PRIOR modules +
    // other macros (never a same-module non-macro def), so emitting all macros
    // first is always valid; functions then see every macro defined above them.
    let mut macro_items: Vec<(String, Sexp)> = Vec::new();
    let mut fn_items: Vec<(String, Sexp)> = Vec::new();

    for (name, entry) in st.all_symbols() {
        // Skip mangled names (impl methods like `show$Int`, macro clause
        // variants like `m$clause-0`)
        if name.contains('$') {
            continue;
        }
        // Predicate: include both UserFn and Macro Def entries for
        // regeneration; skip primitives, constructors, platform effects,
        // overloaded base entries, etc. Per FIXME 0219 — macros surface
        // through the same `ModuleEntry::Def` arm symmetric with UserFn.
        // For macros, capture the symbol-table `macro_sexp` (D1 ruling §6) as a
        // fallback source: a cache-restored-then-REPL-edited `defmacro` has no
        // introspection record (introspection is REPL-only and absent on cache
        // restore), but `macro_sexp` round-trips the cache — without this
        // fallback `regenerate_backing_file` would silently DROP the macro from
        // the regenerated `.cl`, breaking a cached REPL restart that uses it.
        let (is_macro, macro_table_sexp) = match entry {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                cranelisp_types::DefKind::Macro { macro_sexp, .. } => {
                    (true, Some(macro_sexp.clone()))
                }
                cranelisp_types::DefKind::UserFn { .. } => (false, None),
                _ => continue,
            },
            _ => continue,
        };
        // Prefer the introspection record (carries the verbatim REPL input text
        // when present); fall back to the symbol-table `macro_sexp` for macros.
        let sexp = introspection_sexp(introspection, module_path, name)
            .or(macro_table_sexp);
        if let Some(sexp) = sexp {
            if is_macro {
                macro_items.push((name.to_string(), sexp));
            } else {
                fn_items.push((name.to_string(), sexp));
            }
        }
    }

    // Dependency-sort each section independently (macro→macro and fn→fn
    // intra-section edges still matter), then concatenate macros-first.
    let macros_sorted = dependency_sort(macro_items, st);
    let fns_sorted = dependency_sort(fn_items, st);
    macros_sorted
        .into_iter()
        .chain(fns_sorted)
        .map(|(_, sexp)| sexp.format_indented(0))
        .collect::<Vec<_>>()
        .join("\n\n")
}

// ---------------------------------------------------------------------------
// Dependency sorting (Kahn's topological sort)
// ---------------------------------------------------------------------------

/// Sort functions/macros by dependency order using callee lists from the
/// symbol table (Decision 21). Items with no intra-module deps appear first.
/// Cycles are broken alphabetically.
fn dependency_sort(items: Vec<(String, Sexp)>, st: &crate::code::SessionSymbolTable) -> Vec<(String, Sexp)> {
    if items.len() <= 1 {
        return items;
    }

    let names: HashSet<&str> = items.iter().map(|(n, _)| n.as_str()).collect();

    // Build adjacency from callee lists (intra-module only)
    let mut deps: std::collections::HashMap<&str, HashSet<&str>> = std::collections::HashMap::new();
    for (name, _) in &items {
        let mut item_deps = HashSet::new();
        if let Some(entry) = st.get(name) {
            for callee in entry.callees() {
                let callee_name = callee.symbol.as_ref();
                if names.contains(callee_name)
                    && callee_name != name.as_str()
                    && callee.module == st.path
                {
                    item_deps.insert(callee_name);
                }
            }
        }
        deps.insert(name.as_str(), item_deps);
    }

    // Kahn's algorithm
    let mut in_degree: std::collections::HashMap<&str, usize> =
        std::collections::HashMap::new();
    let mut dependents: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();
    for (name, _) in &items {
        in_degree.entry(name.as_str()).or_insert(0);
    }
    for (name, item_deps) in &deps {
        for dep in item_deps {
            dependents.entry(*dep).or_default().push(*name);
            *in_degree.entry(*name).or_insert(0) += 1;
        }
    }

    let mut queue: Vec<&str> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(name, _)| *name)
        .collect();
    queue.sort_by(|a, b| b.cmp(a)); // reverse so pop() gives smallest

    let mut order: Vec<String> = Vec::new();
    while let Some(name) = queue.pop() {
        order.push(name.to_string());
        if let Some(dep_list) = dependents.get(name) {
            for dep_name in dep_list {
                if let Some(deg) = in_degree.get_mut(dep_name) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push(*dep_name);
                        queue.sort_by(|a, b| b.cmp(a));
                    }
                }
            }
        }
    }

    // Remaining items (cycles) added alphabetically
    let ordered_set: HashSet<&str> = order.iter().map(|s| s.as_str()).collect();
    let mut remaining: Vec<String> = items
        .iter()
        .filter(|(n, _)| !ordered_set.contains(n.as_str()))
        .map(|(n, _)| n.clone())
        .collect();
    remaining.sort();
    order.extend(remaining);

    // Reorder items according to order
    let item_map: std::collections::HashMap<String, Sexp> = items.into_iter().collect();
    order
        .into_iter()
        .filter_map(|name| item_map.get(&name).map(|sexp| (name, sexp.clone())))
        .collect()
}

// ---------------------------------------------------------------------------
// Atomic write
// ---------------------------------------------------------------------------

/// Write content to a file atomically (temp file + rename).
/// The temp file is placed in the same directory to ensure atomic rename.
pub fn atomic_write(path: &Path, content: &str) -> std::io::Result<()> {
    let dir = path.parent().unwrap_or_else(|| Path::new("."));
    if !dir.exists() {
        std::fs::create_dir_all(dir)?;
    }
    let tmp_path = path.with_extension("cl.tmp");
    let mut file = std::fs::File::create(&tmp_path)?;
    file.write_all(content.as_bytes())?;
    file.flush()?;
    // fsync for durability
    file.sync_all()?;
    drop(file);
    std::fs::rename(&tmp_path, path)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Span;

    #[test]
    fn merge_imports_filters_prelude() {
        let specs = vec![ImportSpec {
            module_path: "prelude".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_imports(&specs), "");
    }

    #[test]
    fn merge_imports_specific() {
        let specs = vec![ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Specific(vec!["foo".into(), "bar".into()]),
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_imports(&specs), "(import [core [foo bar]])");
    }

    #[test]
    fn merge_imports_glob_wins() {
        let specs = vec![
            ImportSpec {
                module_path: "core".into(),
                alias: None,
                names: ImportNames::Specific(vec!["foo".into()]),
                span: Span::SYNTHETIC,
            },
            ImportSpec {
                module_path: "core".into(),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
        ];
        assert_eq!(generate_imports(&specs), "(import [core [*]])");
    }

    #[test]
    fn generate_exports_empty() {
        assert_eq!(generate_exports(&[]), "");
    }

    #[test]
    fn generate_mod_decls_basic() {
        let decls = vec![ModDecl {
            name: "helper".into(),
            visibility: cranelisp_types::Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_mod_decls(&decls), "(mod helper)");
    }

    #[test]
    fn atomic_write_creates_file() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("test.cl");
        atomic_write(&path, "(defn foo [] 42)\n").expect("write");
        let content = std::fs::read_to_string(&path).expect("read");
        assert_eq!(content, "(defn foo [] 42)\n");
    }
}
