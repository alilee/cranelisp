//! Int-side import/export installer (int plan §1.4; FIXME 0242 §S76-addendum
//! (2); BC §2 invariants 2 + 8).
//!
//! Import/export registration is an int-side alias-installer concern, NOT
//! typecheck's: typecheck's `register_imports` / `register_exports` were
//! struck from its public surface (BC §2). This module reconstructs the
//! per-symbol binding installation directly against the session symbol
//! tables:
//!
//! - resolved per-symbol bindings → `ModuleEntry::Import { source, visibility }`
//!   in the current module's symbol table (visibility `Private` for `(import …)`,
//!   `Public` for `(export …)` re-export edges);
//! - module-path aliases (`(import [(target alias) …])`) →
//!   `ModuleAliases` keyed by `<owner>.<alias>`.
//!
//! typecheck reads `module_aliases` read-only and surfaces unresolved
//! dependencies as `CheckError::Gap`; the installer is the *producer*.
//!
//! The resolution semantics (glob / specific / member-glob; visibility checks;
//! ambiguity detection) mirror the deleted typecheck bodies (recovered from
//! git `cee8152^`), now operating directly on `SessionSymbolTable` values.

use cranelisp_types::{
    CranelispError, DefKind, ErrorLocation, ExportSpec, FQSymbol, ImportNames, ImportSpec,
    ModuleAliasEntry, ModuleAliases, ModuleEntry, ModuleFullPath, Span, Symbol, TraitName,
    Visibility,
};

use crate::code::{Code, SessionSymbolTable};

type SessionTables = dashmap::DashMap<ModuleFullPath, SessionSymbolTable>;

/// Install resolved import bindings for `specs` into `current_module`'s symbol
/// table, plus any module-path aliases into `module_aliases`. Replaces the
/// struck `cranelisp_typecheck::register_imports`.
pub(crate) fn install_imports(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    specs: &[ImportSpec],
) -> Result<(), CranelispError> {
    for spec in specs {
        // Module-path alias (§8.3.4) → ModuleAliases keyed by <owner>.<alias>.
        if let Some(alias) = &spec.alias {
            let key = alias_key(current_module, alias.as_ref());
            module_aliases.insert(
                key,
                ModuleAliasEntry::new(
                    spec.module_path.clone(),
                    Visibility::Private,
                    spec.span,
                ),
            );
        }

        let to_add = {
            let source_guard = symbol_tables.get(&spec.module_path).ok_or_else(|| {
                CranelispError::TypeError {
                    message: format!("unknown module '{}' in import", spec.module_path),
                    location: ErrorLocation::from_span(spec.span),
                }
            })?;
            collect_bindings(
                &source_guard,
                current_module,
                &spec.module_path,
                &spec.names,
                spec.span,
                Visibility::Private,
            )?
        };

        let mut guard = symbol_tables
            .get_mut(current_module)
            .ok_or_else(|| missing_current_module(current_module, spec.span))?;
        insert_detecting_ambiguity(&mut guard, to_add);
    }
    Ok(())
}

/// Install re-export bindings for `specs` into `current_module`'s symbol
/// table. Replaces the struck `cranelisp_typecheck::register_exports`.
/// Re-export edges resolve their source module via try-as-is then
/// child-of-current (spec §8.6.x relative form) and install `Public`-visible
/// `ModuleEntry::Import` bindings (the retired `Reexport` variant's effect).
pub(crate) fn install_exports(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    specs: &[ExportSpec],
) -> Result<(), CranelispError> {
    for spec in specs {
        // Resolve module path: try as-is, then as child-of-current.
        let resolved_path = if symbol_tables.contains_key(&spec.module_path) {
            spec.module_path.clone()
        } else {
            let child = ModuleFullPath::from(format!("{current_module}.{}", spec.module_path));
            if symbol_tables.contains_key(&child) {
                child
            } else {
                return Err(CranelispError::TypeError {
                    message: format!("unknown module '{}' in export", spec.module_path),
                    location: ErrorLocation::from_span(spec.span),
                });
            }
        };

        let to_add = {
            let source_guard = symbol_tables
                .get(&resolved_path)
                .unwrap_or_else(|| unreachable!("module existence verified above"));
            collect_bindings(
                &source_guard,
                current_module,
                &resolved_path,
                &spec.names,
                spec.span,
                Visibility::Public,
            )?
        };

        let mut guard = symbol_tables
            .get_mut(current_module)
            .ok_or_else(|| missing_current_module(current_module, spec.span))?;
        insert_detecting_ambiguity(&mut guard, to_add);
    }
    Ok(())
}

/// `<owner>.<alias>` key for the session-level alias table; owner is the
/// declaring module.
fn alias_key(current_module: &ModuleFullPath, alias: &str) -> ModuleFullPath {
    let cur: &str = current_module.as_ref();
    if cur.is_empty() {
        ModuleFullPath::from(alias)
    } else {
        ModuleFullPath::from(format!("{cur}.{alias}"))
    }
}

fn missing_current_module(current_module: &ModuleFullPath, span: Span) -> CranelispError {
    CranelispError::TypeError {
        message: format!("current module '{current_module}' has no symbol table"),
        location: ErrorLocation::from_span(span),
    }
}

/// Collect the per-symbol bindings a single import/export spec produces.
/// `visibility` is `Private` for imports, `Public` for re-exports.
fn collect_bindings(
    source_table: &SessionSymbolTable,
    current_module: &ModuleFullPath,
    module_path: &ModuleFullPath,
    names: &ImportNames,
    span: Span,
    visibility: Visibility,
) -> Result<Vec<(Symbol, ModuleEntry<Code>)>, CranelispError> {
    match names {
        ImportNames::Glob => Ok(collect_glob(source_table, module_path, visibility)),
        ImportNames::Specific(names) => {
            collect_specific(source_table, current_module, names, module_path, span, visibility)
        }
        ImportNames::MemberGlob(parent) => {
            Ok(collect_member_glob(source_table, parent, module_path, visibility))
        }
        ImportNames::None => Ok(Vec::new()),
    }
}

/// All public symbols from the source module → Import bindings.
fn collect_glob(
    source_table: &SessionSymbolTable,
    module_path: &ModuleFullPath,
    visibility: Visibility,
) -> Vec<(Symbol, ModuleEntry<Code>)> {
    source_table
        .public_symbols()
        .map(|(name, _)| {
            (
                name.clone(),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: module_path.clone(),
                        symbol: name.clone(),
                    },
                    visibility,
                },
            )
        })
        .collect()
}

/// Specific named symbols — visibility + existence checks (spec §8.3).
fn collect_specific(
    source_table: &SessionSymbolTable,
    current_module: &ModuleFullPath,
    names: &[Symbol],
    module_path: &ModuleFullPath,
    span: Span,
    visibility: Visibility,
) -> Result<Vec<(Symbol, ModuleEntry<Code>)>, CranelispError> {
    let mut result = Vec::new();
    for name in names {
        match source_table.get(name.as_ref()) {
            Some(entry) => {
                if !entry.is_public() && !is_in_subtree(current_module, module_path) {
                    return Err(CranelispError::TypeError {
                        message: format!("'{name}' is not public in '{module_path}'"),
                        location: ErrorLocation::from_span(span),
                    });
                }
                result.push((
                    name.clone(),
                    ModuleEntry::Import {
                        source: FQSymbol {
                            module: module_path.clone(),
                            symbol: name.clone(),
                        },
                        visibility,
                    },
                ));
            }
            None => {
                return Err(CranelispError::TypeError {
                    message: format!("'{name}' not found in module '{module_path}'"),
                    location: ErrorLocation::from_span(span),
                });
            }
        }
    }
    Ok(result)
}

/// All constructors of a type or all methods of a trait (member glob).
fn collect_member_glob(
    source_table: &SessionSymbolTable,
    parent: &Symbol,
    module_path: &ModuleFullPath,
    visibility: Visibility,
) -> Vec<(Symbol, ModuleEntry<Code>)> {
    let trait_name = TraitName::from(parent.as_ref());
    let mut result = Vec::new();
    for (name, entry) in source_table.public_symbols() {
        let is_member = match entry {
            ModuleEntry::Def {
                trait_origin, kind, ..
            } => match kind.as_ref() {
                DefKind::Constructor { type_name, .. } => {
                    type_name.name.as_ref() == parent.as_ref()
                }
                DefKind::Primitive | DefKind::UserFn { .. } => trait_origin
                    .as_ref()
                    .is_some_and(|fqtn| fqtn.name == trait_name),
                _ => false,
            },
            _ => false,
        };
        if is_member {
            result.push((
                name.clone(),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: module_path.clone(),
                        symbol: name.clone(),
                    },
                    visibility,
                },
            ));
        }
    }
    result
}

/// Insert import entries, marking same-name entries from different sources as
/// ambiguous (spec §8.6.4); same-source duplicates silently dedup; seeded
/// builtins (`user`/`primitives`) take priority; directly-defined entries
/// take priority over incoming imports.
fn insert_detecting_ambiguity(
    table: &mut SessionSymbolTable,
    imports: Vec<(Symbol, ModuleEntry<Code>)>,
) {
    for (name, new_entry) in imports {
        if let Some(existing) = table.get(name.as_ref()) {
            let is_same_source = match (existing, &new_entry) {
                (
                    ModuleEntry::Import { source: s1, .. },
                    ModuleEntry::Import { source: s2, .. },
                ) => s1 == s2,
                _ => false,
            };
            if is_same_source {
                continue;
            }

            let both_indirect = matches!(
                (existing, &new_entry),
                (ModuleEntry::Import { .. }, ModuleEntry::Import { .. })
            );
            if both_indirect {
                let is_seeded = |entry: &ModuleEntry<Code>| -> bool {
                    matches!(entry, ModuleEntry::Import { source, .. }
                        if { let m: &str = source.module.as_ref(); m == "user" || m == "primitives" })
                };
                if is_seeded(existing) || is_seeded(&new_entry) {
                    continue;
                }
                table.insert(
                    name,
                    ModuleEntry::Ambiguous {
                        visibility: Visibility::Public,
                    },
                );
                continue;
            }
            // Existing directly-defined entry takes priority — skip new.
            continue;
        }
        table.insert(name, new_entry);
    }
}

/// Whether `module` is in the subtree rooted at `ancestor` (dotted-path
/// prefix relationship; equal counts). Used for the private-visibility
/// exception: a module may import non-public names from its ancestors.
fn is_in_subtree(module: &ModuleFullPath, ancestor: &ModuleFullPath) -> bool {
    let m: &str = module.as_ref();
    let a: &str = ancestor.as_ref();
    if a.is_empty() {
        return true;
    }
    m == a || m.starts_with(&format!("{a}."))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{Scheme, Type};
    use std::collections::HashMap as StdHashMap;

    fn tables() -> SessionTables {
        SessionTables::new()
    }

    fn ensure(tables: &SessionTables, path: &str) {
        let p = ModuleFullPath::from(path);
        tables
            .entry(p.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(p));
    }

    /// A public primitive Def, as `primitives` carries `add-i64`.
    fn primitive_def() -> ModuleEntry<Code> {
        ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: StdHashMap::new(),
                ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            },
            DefKind::Primitive,
        )
        .visibility(Visibility::Public)
        .build()
    }

    fn glob_spec(module: &str) -> ImportSpec {
        ImportSpec {
            module_path: ModuleFullPath::from(module),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }
    }

    fn glob_export(module: &str) -> ExportSpec {
        ExportSpec {
            module_path: ModuleFullPath::from(module),
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }
    }

    // spec: 08-modules.md §8.7.3 — a glob import brings in only PUBLIC names.
    // A primitive that arrives in `prelude` as `(import [primitives [*]])`
    // (Private binding) MUST NOT flow on to `user` through the implicit
    // prelude glob. This is the int-side guard for FIXME 0263: the dominant
    // "undefined variable: add-i64" failure class is a fixture defect, not an
    // int wiring defect — the import installer is spec-correct.
    #[test]
    fn glob_import_does_not_re_expose_private_imports() {
        let tables = tables();
        ensure(&tables, "primitives");
        ensure(&tables, "prelude");
        ensure(&tables, "user");
        let aliases = ModuleAliases::default();

        // primitives carries a public Def for add-i64.
        tables
            .get_mut(&ModuleFullPath::from("primitives"))
            .unwrap()
            .insert(Symbol::from("add-i64"), primitive_def());

        // prelude does `(import [primitives [*]])` → Private bindings in prelude.
        install_imports(
            &tables,
            &ModuleFullPath::from("prelude"),
            &aliases,
            &[glob_spec("primitives")],
        )
        .unwrap();

        // The prelude binding is present but Private.
        {
            let prelude = tables.get(&ModuleFullPath::from("prelude")).unwrap();
            let entry = prelude.get("add-i64").expect("prelude has the import");
            assert!(
                !entry.is_public(),
                "an `(import …)` binding MUST be Private (spec §8.7.3)",
            );
        }

        // user does the implicit `(import [prelude [*]])`.
        install_imports(
            &tables,
            &ModuleFullPath::from("user"),
            &aliases,
            &[glob_spec("prelude")],
        )
        .unwrap();

        // user MUST NOT have received add-i64 — prelude's binding was Private.
        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        assert!(
            user.get("add-i64").is_none(),
            "Private prelude import MUST NOT flow through the user glob \
             (spec §8.7.3) — this is what produces `undefined variable: add-i64` \
             when a fixture uses `import` instead of `export` (FIXME 0263)",
        );
    }

    // spec: 08-modules.md §8.4 + §8.8 — a re-export (`export`) makes a name
    // PUBLIC in the re-exporting module, so it DOES flow through a downstream
    // glob. This is the spec-conformant prelude shape; the int installer
    // implements it correctly.
    #[test]
    fn glob_picks_up_re_exported_public_names() {
        let tables = tables();
        ensure(&tables, "primitives");
        ensure(&tables, "prelude");
        ensure(&tables, "user");
        let aliases = ModuleAliases::default();

        tables
            .get_mut(&ModuleFullPath::from("primitives"))
            .unwrap()
            .insert(Symbol::from("add-i64"), primitive_def());

        // prelude does `(export [primitives [*]])` → Public re-export bindings.
        install_exports(
            &tables,
            &ModuleFullPath::from("prelude"),
            &[glob_export("primitives")],
        )
        .unwrap();

        {
            let prelude = tables.get(&ModuleFullPath::from("prelude")).unwrap();
            let entry = prelude.get("add-i64").expect("prelude re-exports it");
            assert!(
                entry.is_public(),
                "an `(export …)` re-export binding MUST be Public (spec §8.4)",
            );
        }

        // user's implicit prelude glob now picks it up.
        install_imports(
            &tables,
            &ModuleFullPath::from("user"),
            &aliases,
            &[glob_spec("prelude")],
        )
        .unwrap();

        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        let entry = user
            .get("add-i64")
            .expect("re-exported primitive MUST flow through the user glob");
        match entry {
            ModuleEntry::Import { source, .. } => {
                // Provenance chain-follows to prelude (one hop); the terminal
                // resolve to primitives is the resolver's job, not the installer's.
                assert_eq!(source.module, ModuleFullPath::from("prelude"));
            }
            other => panic!("expected an Import binding, got {other:?}"),
        }
    }
}
