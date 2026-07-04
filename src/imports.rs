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
    // Default (non-incremental) install: a whole-module (Replace) load, a
    // background index worker, cache restore, or a unit-test harness. These do
    // NOT reject an import bringing a name a local definition already owns —
    // the module re-establishes itself as one unit (same-cluster; the local
    // def wins). Only the incremental REPL (Additive) Pass-0 path opts into the
    // symmetric §8.6.4 import-over-def rejection via `install_imports_gated`.
    install_imports_gated(symbol_tables, current_module, module_aliases, specs, false)
}

/// As [`install_imports`], but `reject_over_local_def` opts into the §8.6.4
/// symmetric rejection: an import whose bare name is already bound by a
/// module-local definition (`Def`/`TypeDef`) is a compile-time error. The REPL
/// Additive Pass-0 sets it `true` (an import entered over an existing local
/// definition is the later-arriving conflicting form); every whole-module load
/// leaves it `false` (Replace re-establishes its own defs and its own imports
/// co-arrive — same-cluster, the local def wins).
pub(crate) fn install_imports_gated(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    specs: &[ImportSpec],
    reject_over_local_def: bool,
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

        // §8.11.2 step 1 — resolve a bare submodule name current-module-relative
        // (try as-is, then `<current>.<name>`), SYMMETRIC with `install_exports`
        // (which already does this). Without it a bare `(import [child …])` in a
        // `(mod child)`-declaring shell fails "unknown module 'child'": the source
        // table is registered as `<current>.child`, not root `child`. Bare names
        // with no child candidate + dotted paths fall through to `spec.module_path`
        // unchanged (the `.get(&resolved_path).ok_or_else(…)` below still errors for
        // a genuinely-missing module).
        let resolved_path = if symbol_tables.contains_key(&spec.module_path) {
            spec.module_path.clone()
        } else {
            let child =
                ModuleFullPath::from(format!("{current_module}.{}", spec.module_path));
            if symbol_tables.contains_key(&child) {
                child
            } else {
                spec.module_path.clone()
            }
        };

        let to_add = {
            let source_guard = symbol_tables.get(&resolved_path).ok_or_else(|| {
                CranelispError::TypeError {
                    message: format!("unknown module '{}' in import", spec.module_path),
                    location: ErrorLocation::from_span(spec.span),
                }
            })?;
            collect_bindings(
                &source_guard,
                current_module,
                &resolved_path,
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
        insert_detecting_ambiguity(
            symbol_tables,
            current_module,
            to_add,
            spec.span,
            reject_over_local_def,
        )?;
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
    // Default (non-incremental) install — see `install_imports` for the
    // gating rationale. `export` populates the inner scope identically to
    // `import` (§8.4.0, differing only in visibility), so it carries the same
    // symmetric-rejection opt-in.
    install_exports_gated(symbol_tables, current_module, specs, false)
}

/// As [`install_exports`], but `reject_over_local_def` opts into the §8.6.4
/// symmetric rejection (export-over-local-def). See [`install_imports_gated`].
pub(crate) fn install_exports_gated(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    specs: &[ExportSpec],
    reject_over_local_def: bool,
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
        insert_detecting_ambiguity(
            symbol_tables,
            current_module,
            to_add,
            spec.span,
            reject_over_local_def,
        )?;
    }
    Ok(())
}

/// Establish a module's session-env companions (prelude-fallback bit, import
/// `as`-aliases, submodule short-name aliases) from its **already-installed**
/// symbol table's structural fields (S102 CS-D3a; `design/int/s102-defect-wave.md`
/// §6.2). These companions are session-side and UNSERIALIZED, so a module that
/// enters the session by any route OTHER than the fresh-typecheck path (cache
/// restore, blank `/mod` creation) would otherwise have none of them — its next
/// `/mod`-namespace turn typechecks with no prelude fallback (bare `+`/`:Int`
/// unresolved) and no aliases.
///
/// **Invariant (Principle 18/20):** the companions are computed at INSTALL time,
/// uniformly across every route, from the table's OWN structural representation
/// — never as a side effect of one route's Pass 0. This is the structural mirror
/// of the fresh path's `inject_prelude_if_needed` (`!sexps_reference_prelude`),
/// `install_imports` (alias registration), and `register_submodule_alias`.
///
/// Idempotent: re-running for an already-established module recomputes the same
/// bit + aliases (DashMap insert overwrites with the same values).
pub(crate) fn install_module_session_env(
    symbol_tables: &SessionTables,
    module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
) {
    let prelude_path = ModuleFullPath::from("prelude");
    let Some(table) = symbol_tables.get(module) else {
        return;
    };

    // (a) Prelude-fallback bit. ON for every non-prelude module that does not
    //     explicitly reference `prelude` in its imports/exports — the structural
    //     equivalent of the fresh path's `!sexps_reference_prelude` gate
    //     (§8.8.1). A module that imports prelude explicitly keeps the bit OFF
    //     (absence-is-OFF), exactly as `inject_prelude_if_needed`'s early return
    //     leaves it.
    if *module != prelude_path && !table_references_prelude(&table) {
        prelude_fallback.insert(module.clone(), true);
    }

    // (b) Import `as`-aliases (`(import [(target alias) …])`) → `<module>.<alias>`
    //     — the alias half of `install_imports` (the per-symbol Import bindings
    //     themselves were serialized in the restored table; only the session-side
    //     alias map needs re-populating).
    for spec in &table.imports {
        if let Some(alias) = &spec.alias {
            module_aliases.insert(
                alias_key(module, alias.as_ref()),
                ModuleAliasEntry::new(
                    spec.module_path.clone(),
                    Visibility::Private,
                    spec.span,
                ),
            );
        }
    }

    // (c) Submodule short-name aliases (`(mod util)` → bare `util/…` resolves to
    //     `<module>.util`) — mirror of `register_submodule_alias`, keyed by the
    //     bare short name so §8.6.6 longest-prefix substitution matches.
    for decl in &table.submodules {
        let sub_path = ModuleFullPath::from(format!("{module}.{}", decl.name));
        module_aliases.insert(
            ModuleFullPath::from(decl.name.as_ref()),
            ModuleAliasEntry::new(sub_path, Visibility::Private, decl.span),
        );
    }
}

/// Structural equivalent of `dependency::sexps_reference_prelude` (§8.8.1) over a
/// restored table's `imports`/`exports` fields: does the module explicitly name
/// `prelude` in an import or export? Used by `install_module_session_env` to
/// decide the prelude-fallback bit without the source sexps in hand.
fn table_references_prelude(table: &SessionSymbolTable) -> bool {
    table.imports.iter().any(|s| s.module_path.as_ref() == "prelude")
        || table.exports.iter().any(|s| s.module_path.as_ref() == "prelude")
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

/// §8.6.4 definition-over-(import|export) collision diagnostic — the single
/// message source for BOTH the commit-gate def-over-import direction
/// (`worker::commit_staging_to_live`) and the symmetric Pass-0 import-over-def
/// direction ([`insert_detecting_ambiguity`]).
///
/// `import_entry` is the in-scope `ModuleEntry::Import` binding the definition
/// contests — a private `(import …)` or a public `(export …)` edge (§8.4.0
/// makes them the same bring-into-scope operation, differing only in
/// visibility); it carries the terminal source that becomes the fully-qualified
/// remedy. `def_is_later` selects the phrasing: `true` when a definition arrives
/// over an existing import/export (commit gate), `false` when an import/export
/// arrives over an existing local definition (Pass-0). The message names the
/// source module and the `module/name` FQ remedy per §8.6.4's diagnostics
/// requirement.
pub(crate) fn def_over_binding_error(
    name: &Symbol,
    import_entry: &ModuleEntry<Code>,
    span: Span,
    def_is_later: bool,
) -> CranelispError {
    let (src_module, src_symbol) = match import_entry {
        ModuleEntry::Import { source, .. } => {
            (source.module.to_string(), source.symbol.to_string())
        }
        _ => (String::new(), name.to_string()),
    };
    let kind = if import_entry.is_public() { "export" } else { "import" };
    let message = if def_is_later {
        format!(
            "error: definition of '{name}' conflicts with the explicit {kind} of \
             '{name}' from '{src_module}' (spec/08-modules.md §8.6.4): a definition \
             may not shadow a name brought into scope via import or export. Rename \
             the definition, use a renamed {kind} (§8.3.5), or drop '{name}' from \
             the {kind} list and reference the other symbol fully-qualified as \
             '{src_module}/{src_symbol}'"
        )
    } else {
        format!(
            "error: {kind} of '{name}' from '{src_module}' conflicts with the local \
             definition of '{name}' (spec/08-modules.md §8.6.4): an import or export \
             may not shadow a module-local definition. Rename the definition, use a \
             renamed {kind} (§8.3.5), or drop '{name}' from the {kind} list and \
             reference the other symbol fully-qualified as '{src_module}/{src_symbol}'"
        )
    };
    CranelispError::TypeError {
        message,
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
                DefKind::Primitive { .. } | DefKind::UserFn { .. } => trait_origin
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
    reject_over_local_def: bool,
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
            // The existing entry is a module-LOCAL definition (`Def`/`TypeDef`),
            // and `new_entry` is an incoming import/export binding. Under the
            // §8.6.4 unified rule this is the symmetric collision: an import (or
            // export) that would bind a bare name already bound by a local
            // definition is the later-arriving conflicting form. Reject it when
            // the caller is the incremental REPL (Additive) path — a whole-module
            // (Replace) load's own imports co-arrive with its own defs
            // (same-cluster; the local def legitimately wins, and this is also
            // how a module re-establishes itself on reload). NB: the glob/specific
            // shape is NOT consulted — the decision is prior-local-def vs
            // co-arriving, per constraint #3.
            if reject_over_local_def
                && matches!(new_entry, ModuleEntry::Import { .. })
                && matches!(
                    existing,
                    ModuleEntry::Def { .. } | ModuleEntry::TypeDef { .. }
                )
            {
                return Err(def_over_binding_error(&name, &new_entry, span, false));
            }
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
mod tests;
