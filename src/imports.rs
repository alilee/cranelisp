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

        // Verify the current module's table exists before installing (the
        // per-name insertion re-acquires it; terminal-source dedup reads OTHER
        // modules, so the mutable guard is not held across those reads).
        if !symbol_tables.contains_key(current_module) {
            return Err(missing_current_module(current_module, spec.span));
        }
        insert_detecting_ambiguity(symbol_tables, current_module, to_add, spec.span)?;
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

        if !symbol_tables.contains_key(current_module) {
            return Err(missing_current_module(current_module, spec.span));
        }
        insert_detecting_ambiguity(symbol_tables, current_module, to_add, spec.span)?;
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

/// Insert import entries, marking same-name entries from different **terminal**
/// sources as ambiguous (spec §8.6.4); same-terminal-source duplicates silently
/// dedup; directly-defined entries take priority over incoming imports.
///
/// **Terminal-source dedup (FIXME 0316).** §8.6.4 says *"the same name arriving
/// through two re-export paths from the same original definition is NOT
/// ambiguous"*. The decisive comparison is the **terminal** `(home_module,
/// canonical_symbol)` reached by chain-following each `Import` edge — NOT the
/// immediate `source.module`. A glob `(import [primitives [*]])` and a specific
/// `(import [fn.option [Option]])` where `fn.option` *re-exports*
/// `primitives/Option` have DIFFERENT immediate sources (`primitives` vs
/// `fn.option`) but the SAME terminal (`primitives/Option`), so they dedup
/// rather than collide. Two imports whose chains terminate at distinct original
/// definitions still collide. The immediate-source `s1 == s2` fast-path is gone;
/// the visibility-UPGRADE handling moves onto the same-terminal arm.
///
/// `symbol_tables` is the full table set so terminals can be chain-followed;
/// `current_module`'s mutable guard is acquired only for the brief read+insert
/// of each name, never held across the cross-module terminal reads.
///
/// S78 §2: the former `is_seeded` name-keyed skip (`user`/`primitives`-sourced
/// imports bypass §8.6.4 ambiguity) stays DELETED.
///
/// **Ambiguity diagnostic (FIXME 0316).** When two `Import` edges chain-follow
/// to DISTINCT terminals the name is poisoned. The `ModuleEntry::Ambiguous`
/// sentinel is still installed (the spec §8.6.5 poison-on-reference model), but
/// because the sentinel variant carries no payload a later bare reference to it
/// surfaces only `undefined variable: <name>` — useless for disambiguation. So
/// the collision is ALSO reported eagerly here as a `CranelispError` that NAMES
/// BOTH qualified alternatives (`a/Bar`, `b/Bar`), satisfying the §8.6.5
/// requirement that the diagnostic identify the conflict and tell the user how
/// to disambiguate. (Carrying the alternatives ON the sentinel + reporting
/// lazily at reference time would be the leaner model but requires reshaping
/// `ModuleEntry::Ambiguous` — a `cranelisp-types`/typecheck change outside the
/// int boundary; tracked separately.)
fn insert_detecting_ambiguity(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    imports: Vec<(Symbol, ModuleEntry<Code>)>,
    span: Span,
) -> Result<(), CranelispError> {
    for (name, new_entry) in imports {
        // Snapshot the existing entry (clone + release the read guard) before
        // any cross-module terminal reads — never hold a guard on
        // `current_module` while chain-following other modules' tables.
        let existing = {
            let Some(guard) = symbol_tables.get(current_module) else {
                return Ok(());
            };
            guard.get(name.as_ref()).cloned()
        };

        let Some(existing) = existing else {
            // No prior entry — install directly.
            if let Some(mut guard) = symbol_tables.get_mut(current_module) {
                guard.insert(name, new_entry);
            }
            continue;
        };

        let both_indirect = matches!(
            (&existing, &new_entry),
            (ModuleEntry::Import { .. }, ModuleEntry::Import { .. })
        );
        if !both_indirect {
            // Existing directly-defined entry takes priority — skip new.
            continue;
        }

        // Both are `Import` edges. Chain-follow BOTH to their terminal
        // `(home_module, canonical_symbol)` and compare. Equal terminals are
        // the same original definition → dedup (with visibility upgrade);
        // distinct terminals → §8.6.4 ambiguity.
        let existing_terminal = terminal_identity(symbol_tables, &existing);
        let new_terminal = terminal_identity(symbol_tables, &new_entry);

        let same_terminal = match (&existing_terminal, &new_terminal) {
            (Some(a), Some(b)) => a == b,
            // If either chain cannot resolve a terminal (a dangling/forward
            // edge), fall back to the immediate-source comparison so a genuine
            // same-source re-export still dedups rather than spuriously
            // colliding.
            _ => immediate_source_eq(&existing, &new_entry),
        };

        if same_terminal {
            // Same original definition. The ONE write case is a visibility
            // UPGRADE — a `(export [mod [name]])` re-export of an already
            // `(import …)`'d name: the import installed Private, the export
            // installs Public with the same terminal. Re-point to the
            // more-visible entry so the re-export takes effect (spec §8.4).
            // Equal/downgrade → silent dedup.
            if !existing.is_public()
                && new_entry.is_public()
                && let Some(mut guard) = symbol_tables.get_mut(current_module)
            {
                guard.insert(name, new_entry);
            }
            continue;
        }

        // Distinct terminals → §8.6.5 ambiguity. Uniform — no name-keyed
        // exemption (S78 §2: `is_seeded` deleted). Install the poison sentinel
        // (spec poison-on-reference model) AND report eagerly with both
        // qualified alternatives so the user can disambiguate.
        if let Some(mut guard) = symbol_tables.get_mut(current_module) {
            guard.insert(
                name.clone(),
                ModuleEntry::Ambiguous {
                    visibility: Visibility::Public,
                },
            );
        }
        let (alt_a, alt_b) =
            qualified_alternatives(&name, &existing_terminal, &new_terminal, &existing, &new_entry);
        return Err(CranelispError::TypeError {
            message: format!(
                "ambiguous bare name '{name}' — imported from distinct sources \
                 '{alt_a}' and '{alt_b}'; use a qualified reference to disambiguate"
            ),
            location: ErrorLocation::from_span(span),
        });
    }
    Ok(())
}

/// Produce the two qualified alternative names (`a/Bar`, `b/Bar`) for an
/// ambiguity diagnostic. Prefers the chain-followed terminal `(home, symbol)`;
/// falls back to the immediate `Import` source when a terminal did not resolve.
fn qualified_alternatives(
    name: &Symbol,
    existing_terminal: &Option<(ModuleFullPath, Symbol)>,
    new_terminal: &Option<(ModuleFullPath, Symbol)>,
    existing: &ModuleEntry<Code>,
    new_entry: &ModuleEntry<Code>,
) -> (String, String) {
    let qualify = |terminal: &Option<(ModuleFullPath, Symbol)>, entry: &ModuleEntry<Code>| {
        if let Some((home, sym)) = terminal {
            format!("{home}/{sym}")
        } else if let ModuleEntry::Import { source, .. } = entry {
            format!("{}/{}", source.module, source.symbol)
        } else {
            name.to_string()
        }
    };
    (
        qualify(existing_terminal, existing),
        qualify(new_terminal, new_entry),
    )
}

/// Chain-follow an `Import` entry to its terminal `(home_module,
/// canonical_symbol)` via the shared `cranelisp_types` primitive. A
/// non-`Import` (already-canonical) entry has no terminal identity here — the
/// caller only reaches this for two-`Import` collisions.
fn terminal_identity(
    symbol_tables: &SessionTables,
    entry: &ModuleEntry<Code>,
) -> Option<(ModuleFullPath, Symbol)> {
    let ModuleEntry::Import { source, .. } = entry else {
        return None;
    };
    cranelisp_types::resolve_terminal_entry_and_home(
        symbol_tables,
        &source.module,
        source.symbol.as_ref(),
    )
    .map(|(_, home)| (home, source.symbol.clone()))
}

/// Fallback when a terminal chain cannot resolve: compare the immediate
/// `source` FQSymbols of two `Import` edges (the pre-FIXME-0316 behaviour).
fn immediate_source_eq(a: &ModuleEntry<Code>, b: &ModuleEntry<Code>) -> bool {
    matches!(
        (a, b),
        (
            ModuleEntry::Import { source: s1, .. },
            ModuleEntry::Import { source: s2, .. },
        ) if s1 == s2
    )
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

    fn specific_spec(module: &str, name: &str) -> ImportSpec {
        ImportSpec {
            module_path: ModuleFullPath::from(module),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from(name)]),
            span: Span::SYNTHETIC,
        }
    }

    fn specific_export(module: &str, name: &str) -> ExportSpec {
        ExportSpec {
            module_path: ModuleFullPath::from(module),
            names: ImportNames::Specific(vec![Symbol::from(name)]),
            span: Span::SYNTHETIC,
        }
    }

    // spec: 08-modules.md §8.4 — a module that first `(import [base [x]])`s a
    // name (Private binding) and then `(export [base [x]])`s the SAME name MUST
    // end up with a PUBLIC binding for `x`. Both edges share the same source
    // (`base/x`); the installer's same-source dedup must NOT swallow the
    // Public re-export and leave the name Private. Defect A repro
    // (spec_09::cross_module_macro_transitive_via_reexport_chain): without the
    // visibility-upgrade branch a downstream importer of the re-exporting
    // module saw "'x' is not public in '<relay>'".
    #[test]
    fn import_then_export_same_source_upgrades_to_public() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "relay");
        ensure(&tables, "downstream");
        let aliases = ModuleAliases::default();

        // base defines a public `base-val`.
        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("base-val"), primitive_def());

        // relay: (import [base [base-val]]) → Private binding (source base/base-val).
        install_imports(
            &tables,
            &ModuleFullPath::from("relay"),
            &aliases,
            &[specific_spec("base", "base-val")],
        )
        .unwrap();
        {
            let relay = tables.get(&ModuleFullPath::from("relay")).unwrap();
            assert!(
                !relay.get("base-val").unwrap().is_public(),
                "the bare import binding must start Private",
            );
        }

        // relay: (export [base [base-val]]) → same source, Public. MUST upgrade.
        install_exports(
            &tables,
            &ModuleFullPath::from("relay"),
            &[specific_export("base", "base-val")],
        )
        .unwrap();
        {
            let relay = tables.get(&ModuleFullPath::from("relay")).unwrap();
            assert!(
                relay.get("base-val").unwrap().is_public(),
                "import-then-export of the same source MUST yield a Public \
                 binding (spec §8.4) — the same-source dedup must not swallow \
                 the re-export's visibility upgrade",
            );
        }

        // Downstream module can now import the re-exported name from relay.
        install_imports(
            &tables,
            &ModuleFullPath::from("downstream"),
            &aliases,
            &[specific_spec("relay", "base-val")],
        )
        .expect(
            "a specific import of the re-exported name from relay MUST succeed \
             — it is now public there",
        );
    }

    // spec: 08-modules.md §8.4 — the reverse order (export before import, or a
    // second identical import after an export) MUST NOT DOWNGRADE an
    // already-public re-export back to Private. Guards the upgrade branch
    // against a visibility regression on a later same-source private import.
    #[test]
    fn export_then_import_same_source_stays_public() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "relay");
        let aliases = ModuleAliases::default();

        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("base-val"), primitive_def());

        // Public re-export first.
        install_exports(
            &tables,
            &ModuleFullPath::from("relay"),
            &[specific_export("base", "base-val")],
        )
        .unwrap();
        // Then a (redundant) private import of the same source.
        install_imports(
            &tables,
            &ModuleFullPath::from("relay"),
            &aliases,
            &[specific_spec("base", "base-val")],
        )
        .unwrap();

        let relay = tables.get(&ModuleFullPath::from("relay")).unwrap();
        assert!(
            relay.get("base-val").unwrap().is_public(),
            "a later same-source Private import MUST NOT downgrade an existing \
             Public re-export",
        );
    }

    // spec: 08-modules.md §8.6.4 — TERMINAL-source dedup at the installer seam.
    // `prim` defines `Foo`; `reexp` re-exports `prim/Foo`. A module that imports
    // `Foo` BOTH via a glob of `prim` (immediate source `prim`) AND specifically
    // from `reexp` (immediate source `reexp`) brings two bindings whose chains
    // terminate at the SAME `(prim, Foo)`. They MUST dedup silently — no error,
    // no `Ambiguous` sentinel. This pins the terminal-resolve logic at the seam
    // (the e2e proves the user path; this pins the chain-follow comparison).
    #[test]
    fn same_terminal_two_paths_dedup_no_ambiguity() {
        let tables = tables();
        ensure(&tables, "prim");
        ensure(&tables, "reexp");
        ensure(&tables, "main");
        let aliases = ModuleAliases::default();

        // prim defines a public `Foo`.
        tables
            .get_mut(&ModuleFullPath::from("prim"))
            .unwrap()
            .insert(Symbol::from("Foo"), primitive_def());

        // reexp re-exports prim/Foo (Public Import edge → prim).
        install_exports(
            &tables,
            &ModuleFullPath::from("reexp"),
            &[specific_export("prim", "Foo")],
        )
        .unwrap();

        // main globs prim (brings Foo, source prim) ...
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &[glob_spec("prim")],
        )
        .expect("glob of prim installs Foo");

        // ... and specifically imports Foo from reexp (source reexp, terminal prim/Foo).
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &[specific_spec("reexp", "Foo")],
        )
        .expect(
            "a glob + a re-export of the same terminal definition MUST dedup \
             silently (spec §8.6.4 terminal-source comparison) — NOT error",
        );

        let main = tables.get(&ModuleFullPath::from("main")).unwrap();
        let entry = main.get("Foo").expect("Foo is installed");
        assert!(
            !matches!(entry, ModuleEntry::Ambiguous { .. }),
            "same-terminal dedup MUST NOT poison the name as Ambiguous; got {entry:?}",
        );
    }

    // spec: 08-modules.md §8.6.5 — distinct-terminal collision at the seam. `a`
    // and `b` each define their OWN, DIFFERENT `Bar`. Importing both bare MUST
    // error, and the diagnostic MUST name BOTH qualified alternatives (`a/Bar`,
    // `b/Bar`) so the user can disambiguate. The poison sentinel is also
    // installed (poison-on-reference model), but the eager error is what carries
    // the alternatives (the sentinel variant has no payload).
    #[test]
    fn distinct_terminals_error_naming_both_alternatives() {
        let tables = tables();
        ensure(&tables, "a");
        ensure(&tables, "b");
        ensure(&tables, "main");
        let aliases = ModuleAliases::default();

        tables
            .get_mut(&ModuleFullPath::from("a"))
            .unwrap()
            .insert(Symbol::from("Bar"), primitive_def());
        tables
            .get_mut(&ModuleFullPath::from("b"))
            .unwrap()
            .insert(Symbol::from("Bar"), primitive_def());

        // main imports a/Bar bare (no collision yet).
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &[specific_spec("a", "Bar")],
        )
        .expect("first bare import of Bar installs cleanly");

        // main imports b/Bar bare → distinct terminal → MUST error.
        let err = install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &[specific_spec("b", "Bar")],
        )
        .expect_err(
            "two DISTINCT terminal `Bar` definitions imported under the same \
             bare name MUST collide (spec §8.6.5 footgun protection)",
        );

        let msg = match &err {
            CranelispError::TypeError { message, .. } => message.clone(),
            other => panic!("expected a TypeError, got {other:?}"),
        };
        assert!(
            msg.to_lowercase().contains("ambiguous"),
            "the diagnostic MUST identify the conflict as ambiguous; got: {msg}",
        );
        assert!(
            msg.contains("a/Bar") && msg.contains("b/Bar"),
            "the diagnostic MUST name BOTH qualified alternatives \
             (`a/Bar` and `b/Bar`); got: {msg}",
        );

        // The poison sentinel is installed too (poison-on-reference model).
        let main = tables.get(&ModuleFullPath::from("main")).unwrap();
        assert!(
            matches!(main.get("Bar"), Some(ModuleEntry::Ambiguous { .. })),
            "the colliding name MUST be poisoned with the Ambiguous sentinel",
        );
    }
}
