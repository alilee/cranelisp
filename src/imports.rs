//! Int-side import/export installer (int plan §1.4; FIXME 0242 §S76-addendum
//! (2); BC §2 invariants 2 + 8).
//!
//! Import/export registration is an int-side alias-installer concern, NOT
//! typecheck's: typecheck's `register_imports` / `register_exports` were
//! struck from its public surface (BC §2). This module reconstructs the
//! per-symbol binding installation directly against the session symbol
//! tables:
//!
//! - resolved per-symbol exposures → terminal `NameCandidate` references in the
//!   current module's symbol table (`Private` for imports, `Public` for exports);
//! - module-path aliases (`(import [(target alias) …])`) →
//!   `ModuleAliases` keyed by `<owner>.<alias>`.
//!
//! typecheck reads `module_aliases` read-only and surfaces unresolved
//! dependencies as `CheckError::Gap`; the installer is the *producer*.
//!
//! The resolution semantics (glob / specific / member-glob; visibility checks;
//! ambiguity detection) mirror the deleted typecheck bodies (recovered from
//! git `cee8152^`), now operating directly on `SessionSymbolTable` values.

use std::collections::HashSet;

use cranelisp_typecheck::PreludeFallback;
use cranelisp_types::{
    CranelispError, ErrorLocation, ExportSpec, FQSymbol, ImportNames, ImportSpec, ModuleAliasEntry,
    ModuleAliases, ModuleFullPath, Span, Symbol, Visibility,
};

/// The session-side declared-export closure map (FIXME 0604 §2.2): `M → D(M)`,
/// where `D(M)` is the union of the names `M`'s own `(export …)` specs bring in.
/// A **separate** `DashMap` from `symbol_tables` (so a read never re-enters a
/// `get_mut` shard the caller holds — the deadlock hazard) and **unserialized**,
/// recomputed per session (modelled on `prelude_fallback`). Candidate exposure
/// checks key on `D(M)`, not on the source-provider heuristic the S114 predicate used.
pub(crate) type DeclaredExports = dashmap::DashMap<ModuleFullPath, HashSet<Symbol>>;

use crate::code::SessionSymbolTable;

type SessionTables = dashmap::DashMap<ModuleFullPath, SessionSymbolTable>;

#[derive(Debug, Clone)]
struct CandidateExposure {
    local_name: Symbol,
    source: FQSymbol,
    visibility: Visibility,
}

/// Install resolved import bindings for `specs` into `current_module`'s symbol
/// table, plus any module-path aliases into `module_aliases`. Replaces the
/// struck `cranelisp_typecheck::register_imports`.
///
/// `prelude_fallback` remains part of the orchestration call shape; the shared
/// resolver owns union with implicit-prelude candidates. This installer records
/// terminal candidates only and does not decide ambiguity eagerly.
pub(crate) fn install_imports(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    _prelude_fallback: &PreludeFallback,
    specs: &[ImportSpec],
) -> Result<(), CranelispError> {
    for spec in specs {
        // Module-path alias (§8.3.4) → ModuleAliases keyed by <owner>.<alias>.
        if let Some(alias) = &spec.alias {
            let key = alias_key(current_module, alias.as_ref());
            module_aliases.insert(
                key,
                ModuleAliasEntry::new(spec.module_path.clone(), Visibility::Private, spec.span),
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
            let child = ModuleFullPath::from(format!("{current_module}.{}", spec.module_path));
            if symbol_tables.contains_key(&child) {
                child
            } else {
                spec.module_path.clone()
            }
        };

        let to_add = {
            let source_guard =
                symbol_tables
                    .get(&resolved_path)
                    .ok_or_else(|| CranelispError::TypeError {
                        message: format!("unknown module '{}' in import", spec.module_path),
                        location: ErrorLocation::from_span(spec.span),
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
        // FIXME 0604 chokepoint: route through the terminal-closure gate BEFORE
        // delegating to the poison consumer, so a mis-targeted/materialized
        // phantom public write is rejected at the seam and never reaches a live
        // table. `import` edges are Private → the gate is a no-op here (census
        // legal-skip: !is_public short-circuits, so `D(M)` is never consulted —
        // pass `None`), but routing uniformly keeps the structural guard greppable.
        for exposure in &to_add {
            check_candidate_closure(current_module, exposure, spec.span, None)?;
        }
        install_candidates(symbol_tables, current_module, to_add, spec.span)?;
    }
    Ok(())
}

/// Install re-export bindings for `specs` into `current_module`'s symbol
/// table. Replaces the struck `cranelisp_typecheck::register_exports`.
/// Re-export edges resolve their source module via try-as-is then
/// child-of-current (spec §8.6.x relative form) and install `Public`-visible
/// public candidate exposures.
///
/// `export` populates the inner scope identically to `import` (§8.4.0), so it
/// runs through the same candidate-install path as `import`.
///
/// `declared_exports` (FIXME 0604 §2.2) is the session-side `M → D(M)` map. When
/// `Some`, the names this seam installs are RECORDED into `D(current_module)` —
/// the authoritative declared-export set `commit_staging_to_live` later gates
/// against (recorded from the specs at INSTALL time, before any phantom write
/// could be injected, so the check is not circular against the entries it
/// validates). The BACKGROUND index path (isolated private tables, R13) passes
/// `None` — it must never write live session state.
pub(crate) fn install_exports(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    _prelude_fallback: &PreludeFallback,
    declared_exports: Option<&DeclaredExports>,
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
        // FIXME 0604 §2.2: RECORD this module's declared exports `D(M)` from the
        // names its own `(export …)` specs bring in — the settled surface
        // `commit_staging_to_live` gates against. Recorded at install time (before
        // any phantom write), keyed by the destination module.
        let spec_names: HashSet<Symbol> = to_add
            .iter()
            .map(|exposure| exposure.local_name.clone())
            .collect();
        if let Some(de) = declared_exports {
            de.entry(current_module.clone())
                .or_default()
                .extend(spec_names.iter().cloned());
        }
        // FIXME 0604 chokepoint: `export` edges are Public — the gate routes here
        // too. `D(M)` for these entries is exactly the names being installed (this
        // seam DEFINES the declared exports), so every entry passes by
        // construction; the routing keeps the structural census closed (Principle
        // 18) — a phantom out-of-closure public write is caught at the LIVE commit
        // seam (`commit_staging_to_live`), where `D(M)` is already recorded.
        for exposure in &to_add {
            check_candidate_closure(current_module, exposure, spec.span, Some(&spec_names))?;
        }
        install_candidates(symbol_tables, current_module, to_add, spec.span)?;
    }
    Ok(())
}

// ===========================================================================
// FIXME 0604 — the foreground public-write CHOKEPOINT (prelude-table-write-
// isolation.md §2). Isolation by construction: every foreground writer that can
// insert a PUBLIC name candidate into a module's live symbol table routes through
// the ONE `check_exposed_candidate_closure` gate (below) or carries a named
// legal-skip.
//
// ─────────────────────────── FOREGROUND WRITER CENSUS (§2.1) ───────────────
//
// | Writer seam                              | Public? | Disposition            |
// |------------------------------------------|---------|------------------------|
// | imports.rs::install_exports (Public)     | yes     | ROUTE through gate     |
// | imports.rs::install_imports (Private)    | no      | route (no-op: !public) |
// | imports.rs::install_candidates           | yes     | candidate exposures are|
// |                                          |         | vetted by the install  |
// |                                          |         | seam above              |
// | cluster.rs::insert_cluster (commit gate) | yes     | ROUTE (normally empty) |
// | worker::commit_staging_to_live (the REAL | yes     | ROUTE through gate     |
// |   staging→live commit; S115 missed-row)  |         | (D(M) precomputed      |
// |                                          |         | before the get_mut)    |
// | process_form/form_dispatch (defmacro reg)| yes     | ROUTE (own-def → Ok,   |
// |                                          |         | no map read, D=None)   |
// | Code-install sites (mutate existing)     | no new  | legal-skip (no new     |
// |                                          | entry   | public table entry)    |
// | process_form/cache_restore.rs            | yes     | off the recipe path    |
// |                                          |         | (--no-cache); its own  |
// |                                          |         | restore guard          |
// | worker::inject_prelude_if_needed /       | n/a     | legal-skip (session-   |
// |   install_module_session_env             |         | side maps: fallback    |
// |                                          |         | bit + aliases, NOT a   |
// |                                          |         | symbol-table entry)    |
// | bootstrap.rs::mount_synthetic_modules    | yes     | LEGAL-SKIP, ASSERTED   |
// |   (session-init synthetic seeds; S115    |         | (see note below)       |
// |    W6, FIXME 0740 disposition)           |         |                        |
// | lifecycle.rs PRIMITIVES_TABLE whole-table| yes     | named legal-skip: own  |
// |   session-init mount                     |         | definitions before pool|
// | platform.rs::register_platform_in_tc     | yes     | named legal-skip:      |
// |   (DLL-load orchestration)               |         | canonical own-def only |
//
// **bootstrap legal-skip, with a detection proof (not an argument).**
// `mount_synthetic_modules` runs ONCE at session init, single-threaded, BEFORE
// any worker is spawned — it is outside the foreground concurrent-compile path
// entirely — and it seeds only (a) own definitions (special forms at root,
// intrinsic types / TypeDefs / synthetic ADT ctors + Defs in `primitives`, the
// `macros` ADTs) and (b) ONE intra-module public self-alias
// (`primitives/Bind → primitives/IO.Bind`, `bootstrap.rs` step 5). The four
// `macros`-module edges to `primitives` (`Int`/`Bool`/`Float`/`String`) are
// `Visibility::Private`, so they are not public writes at all. Making the whole
// init path fallible to route an unreachable rejection would buy no soundness
// (Principle 6/8); instead the skip is ASSERTED by
// `bootstrap::tests::bootstrap_public_candidate_exposures_are_self_aliases_or_private`,
// which sweeps every seeded name candidate through
// `check_exposed_candidate_closure` under the strictest closure `D(M) = {}` —
// so a future cross-module PUBLIC exposure (the phantom shape) turns that test
// RED.
//
// The census's job is to prove the set is CLOSED: no OTHER foreground seam can
// insert a public table entry without routing through the gate. The greppable
// structural guard (Principle 18): a public-insert seam that bypasses
// `check_exposed_candidate_closure` is a `/review` finding.
// ===========================================================================

/// The ONE terminal-table export-closure chokepoint (FIXME 0604, §2.2).
///
/// **Invariant:** a module never accepts a new PUBLIC entry outside its declared
/// export closure `D(M)`. Supersedes the retired S113 prelude-only PS-R7
/// `debug_assert!` with an **unconditional, generalized, DIAGNOSED
/// error** — it fires in EVERY build, for ANY module (not just `prelude`), and a
/// firing NAMES its caller in production (module, name, source edge), turning the
/// next phantom occurrence anywhere (`bit-and → primitives/bit-and`, FIXME 0604)
/// into a located defect instead of another quiet-environment hunt. The message
/// self-identifies as an internal R7 invariant breach (never mistakable for a
/// user diagnostic — /arch Phase-2 §4 sub-form ruling).
///
/// Keys on the DESTINATION module's DECLARED EXPORTS `D(M)` (Principle 26 — read
/// the settled `(export …)` surface, NOT the source-provider heuristic the S114
/// predicate mistook for it). The S114 predicate was **provider-existence** shaped
/// and BLIND to the live phantom by construction: `bit-and` IS a bundled public
/// primitive (`cranelisp-primitives/src/lib.rs:412`), so a phantom
/// `bit-and → primitives/bit-and` names a genuine provider and provider-existence
/// returned `true` (/qa S114 re-attribution; /arch Phase-2 §4). The distinguishing
/// fact is that `bit-and` is **outside prelude's declared export closure**
/// (`stdlib/prelude.cl` re-exports a curated primitive set, not a glob).
///
/// - a module's own public definition is exported by §8.4 → **Ok with NO map
///   read** (keeps definition staging safe under its module guard);
/// - a public re-export `Import` edge whose `name ∈ D(M)` → Ok; `name ∉ D(M)`
///   (the phantom shape) → rejected + diagnosed;
/// - `declared_exports == None` (D(M) unknown/not-yet-recorded) → PERMIT — a
///   foreign write racing ahead of `M`'s own export processing is permitted; the
///   guard catches it once `D(M)` is recorded (the diagnostic must NEVER
///   false-fire).
///
/// Non-public writes are always Ok (isolation is a PUBLIC-write invariant).
fn check_candidate_closure(
    module: &ModuleFullPath,
    exposure: &CandidateExposure,
    span: Span,
    declared_exports: Option<&HashSet<Symbol>>,
) -> Result<(), CranelispError> {
    check_exposed_candidate_closure(
        module,
        &exposure.local_name,
        &exposure.source,
        exposure.visibility,
        span,
        declared_exports,
    )
}

/// Check one candidate exposure against the destination module's declared
/// export closure. This value-parameter form is shared by import installation
/// and staged publication without exposing the import installer's carrier.
pub(crate) fn check_exposed_candidate_closure(
    module: &ModuleFullPath,
    local_name: &Symbol,
    source: &FQSymbol,
    visibility: Visibility,
    span: Span,
    declared_exports: Option<&HashSet<Symbol>>,
) -> Result<(), CranelispError> {
    if visibility != Visibility::Public
        || source.module == *module
        || declared_exports.is_none_or(|names| names.contains(local_name))
    {
        return Ok(());
    }
    Err(CranelispError::TypeError {
        message: format!(
            "internal: rejected out-of-closure public binding `{}` into module `{module}` \
             (source `{}`) — not in the module's declared export closure \
             (FIXME 0604 terminal-table write isolation / R7 invariant breach)",
            local_name, source
        ),
        location: ErrorLocation::from_span(span),
    })
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
                ModuleAliasEntry::new(spec.module_path.clone(), Visibility::Private, spec.span),
            );
        }
    }

    // (c) Submodule short-name aliases (`(mod util)` → bare `util/…` resolves to
    //     `<module>.util`) — mirror of `register_submodule_alias`, keyed by the
    //     declaring module plus short name so aliases cannot leak across
    //     module sessions. The resolver supplies that scope for §8.6.6
    //     longest-prefix substitution.
    for decl in &table.submodules {
        let sub_path = ModuleFullPath::from(format!("{module}.{}", decl.name));
        module_aliases.insert(
            cranelisp_types::module_alias_key(module, decl.name.as_ref()),
            ModuleAliasEntry::new(sub_path, Visibility::Private, decl.span),
        );
    }
}

/// Structural equivalent of `dependency::sexps_reference_prelude` (§8.8.1) over a
/// restored table's `imports`/`exports` fields: does the module explicitly name
/// `prelude` in an import or export? Used by `install_module_session_env` to
/// decide the prelude-fallback bit without the source sexps in hand.
fn table_references_prelude(table: &SessionSymbolTable) -> bool {
    table
        .imports
        .iter()
        .any(|s| s.module_path.as_ref() == "prelude")
        || table
            .exports
            .iter()
            .any(|s| s.module_path.as_ref() == "prelude")
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
) -> Result<Vec<CandidateExposure>, CranelispError> {
    match names {
        ImportNames::Glob => Ok(collect_glob(source_table, module_path, visibility)),
        ImportNames::Specific(names) => collect_specific(
            source_table,
            current_module,
            names,
            module_path,
            span,
            visibility,
        ),
        ImportNames::MemberGlob(parent) => Ok(collect_member_glob(
            source_table,
            parent,
            module_path,
            visibility,
        )),
        ImportNames::None => Ok(Vec::new()),
    }
}

/// All public symbols from the source module → Import bindings.
fn collect_glob(
    source_table: &SessionSymbolTable,
    _module_path: &ModuleFullPath,
    visibility: Visibility,
) -> Vec<CandidateExposure> {
    source_table
        .public_name_candidates()
        .map(|(name, candidate)| CandidateExposure {
            local_name: name.clone(),
            source: candidate.source,
            visibility,
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
) -> Result<Vec<CandidateExposure>, CranelispError> {
    let mut result = Vec::new();
    for name in names {
        let candidates = source_table.name_candidates(name);
        if candidates.is_empty() {
            return Err(CranelispError::TypeError {
                message: format!("'{name}' not found in module '{module_path}'"),
                location: ErrorLocation::from_span(span),
            });
        }
        let accessible: Vec<_> = candidates
            .into_iter()
            .filter(|candidate| {
                candidate.visibility == Visibility::Public
                    || is_in_subtree(current_module, module_path)
            })
            .collect();
        if accessible.is_empty() {
            return Err(CranelispError::TypeError {
                message: format!("'{name}' is not public in '{module_path}'"),
                location: ErrorLocation::from_span(span),
            });
        }
        for candidate in accessible {
            result.push(CandidateExposure {
                local_name: name.clone(),
                source: candidate.source,
                visibility,
            });
        }
    }
    Ok(result)
}

/// All constructors of a type or all methods of a trait (member glob).
fn collect_member_glob(
    source_table: &SessionSymbolTable,
    parent: &Symbol,
    _module_path: &ModuleFullPath,
    visibility: Visibility,
) -> Vec<CandidateExposure> {
    let prefix = format!("{}.", parent.as_ref());
    source_table
        .public_name_candidates()
        .filter(|(_, candidate)| candidate.source.symbol.as_ref().starts_with(&prefix))
        .map(|(_, candidate)| CandidateExposure {
            local_name: Symbol::from(cranelisp_types::bare_member_name(
                candidate.source.symbol.as_ref(),
            )),
            source: candidate.source,
            visibility,
        })
        .collect()
}

/// Install every terminal exposure produced by an import or export.
///
/// Candidate coexistence is deliberate: duplicate sources deduplicate inside
/// `SymbolTable::expose_candidate`, while distinct sources remain available to
/// type-directed resolution. Ambiguity is diagnosed only if several candidates
/// remain viable at the use site.
fn install_candidates(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    exposures: Vec<CandidateExposure>,
    span: Span,
) -> Result<(), CranelispError> {
    let mut table = symbol_tables
        .get_mut(current_module)
        .ok_or_else(|| missing_current_module(current_module, span))?;
    for exposure in exposures {
        table
            .expose_candidate(exposure.local_name, exposure.source, exposure.visibility)
            .map_err(|error| CranelispError::TypeError {
                message: error.to_string(),
                location: ErrorLocation::from_span(span),
            })?;
    }
    Ok(())
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
