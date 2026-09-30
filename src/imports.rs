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
    CranelispError, ErrorLocation, ExportSpec, FQSymbol, ImportNames, ImportSpec, ModDecl,
    ModuleAliasEntry, ModuleAliases, ModuleFullPath, ModuleName, Span, Symbol, Visibility,
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

/// The children one module declares with `(mod name)` or `(mod- name)` — the
/// only fact that makes a bare module name in its `import` and `export` specs
/// name a child (spec §8.11.2 item 1, §8.11.2.1; `design/int/int.md` §6.9).
///
/// Built from declarations alone. The resolver has no symbol-table, filesystem
/// or load-state input, so a registered or file-backed child that the module
/// does not declare cannot capture a name.
#[derive(Debug, Clone)]
pub(crate) struct DeclaredChildren {
    parent: ModuleFullPath,
    names: HashSet<ModuleName>,
}

/// An `import` or `export` spec paired with the module it names. Only
/// [`DeclaredChildren`] constructs one, so an installer receives the resolved
/// module and cannot re-resolve the spelling.
#[derive(Debug)]
pub(crate) struct ResolvedSpec<'s, S> {
    spec: &'s S,
    module: ModuleFullPath,
}

impl<S> ResolvedSpec<'_, S> {
    pub(crate) fn spec(&self) -> &S {
        self.spec
    }

    pub(crate) fn module(&self) -> &ModuleFullPath {
        &self.module
    }
}

impl DeclaredChildren {
    pub(crate) fn of<'d>(
        parent: &ModuleFullPath,
        declarations: impl IntoIterator<Item = &'d ModDecl>,
    ) -> Self {
        DeclaredChildren {
            parent: parent.clone(),
            names: declarations
                .into_iter()
                .map(|decl| decl.name.clone())
                .collect(),
        }
    }

    /// The module `spelling` names inside the parent: its declared child
    /// `<parent>.<spelling>` for a bare declared name in a non-root module,
    /// otherwise the absolute module `spelling`.
    pub(crate) fn resolve(&self, spelling: &ModuleFullPath) -> ModuleFullPath {
        let name: &str = spelling.as_ref();
        let names_child =
            !self.parent.as_ref().is_empty() && !name.contains('.') && self.names.contains(name);
        if names_child {
            declared_child_path(&self.parent, name)
        } else {
            spelling.clone()
        }
    }

    pub(crate) fn resolve_import<'s>(&self, spec: &'s ImportSpec) -> ResolvedSpec<'s, ImportSpec> {
        ResolvedSpec {
            spec,
            module: self.resolve(&spec.module_path),
        }
    }

    pub(crate) fn resolve_export<'s>(&self, spec: &'s ExportSpec) -> ResolvedSpec<'s, ExportSpec> {
        ResolvedSpec {
            spec,
            module: self.resolve(&spec.module_path),
        }
    }
}

/// The module path of `parent`'s declared child `name`.
pub(crate) fn declared_child_path(parent: &ModuleFullPath, name: &str) -> ModuleFullPath {
    ModuleFullPath::from(format!("{parent}.{name}"))
}

/// Install resolved import bindings for `specs` into `current_module`'s symbol
/// table, plus any module-path aliases into `module_aliases`. Replaces the
/// struck `cranelisp_typecheck::register_imports`.
///
/// Each spec's source is the module it was resolved to; a missing table for
/// that module is an error naming it.
///
/// `prelude_fallback` remains part of the orchestration call shape; the shared
/// resolver owns union with implicit-prelude candidates. This installer records
/// terminal candidates only and does not decide ambiguity eagerly.
pub(crate) fn install_imports(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    _prelude_fallback: &PreludeFallback,
    specs: &[ResolvedSpec<'_, ImportSpec>],
) -> Result<(), CranelispError> {
    for resolved in specs {
        let spec = resolved.spec;
        install_import_alias(current_module, module_aliases, resolved);

        let to_add = {
            let source_guard =
                symbol_tables
                    .get(&resolved.module)
                    .ok_or_else(|| CranelispError::TypeError {
                        message: format!("unknown module '{}' in import", resolved.module),
                        location: ErrorLocation::from_span(spec.span),
                    })?;
            collect_bindings(
                &source_guard,
                current_module,
                &resolved.module,
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
/// Each re-export installs `Public`-visible candidate exposures from the module
/// its spec was resolved to; a missing table for that module is an error
/// naming it.
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
    specs: &[ResolvedSpec<'_, ExportSpec>],
) -> Result<(), CranelispError> {
    for resolved in specs {
        let spec = resolved.spec;
        let to_add = {
            let source_guard =
                symbol_tables
                    .get(&resolved.module)
                    .ok_or_else(|| CranelispError::TypeError {
                        message: format!("unknown module '{}' in export", resolved.module),
                        location: ErrorLocation::from_span(spec.span),
                    })?;
            collect_bindings(
                &source_guard,
                current_module,
                &resolved.module,
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
// FIXME 0604 — the foreground public-write CHOKEPOINT (design/int/int.md §6.7).
// Isolation by construction: every foreground writer that can
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
/// primitive (`crates/cranelisp-primitives/src/declarations.rs`), so a phantom
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
    let Some(table) = symbol_tables.get(module) else {
        return;
    };

    // (a) Prelude-fallback bit. ON for every non-prelude module that does not
    //     explicitly reference `prelude` in its imports/exports — the structural
    //     equivalent of the fresh path's `!sexps_reference_prelude` gate
    //     (§8.8.1). A module that imports prelude explicitly keeps the bit OFF
    //     (absence-is-OFF), exactly as `inject_prelude_if_needed`'s early return
    //     leaves it.
    if gets_prelude_fallback(module, &table.imports, &table.exports) {
        prelude_fallback.insert(module.clone(), true);
    }

    // (b)+(c) The module-path aliases its declarations make (the per-symbol
    //     Import bindings themselves were serialized in the restored table;
    //     only the session-side alias map needs re-populating).
    install_declared_aliases(module, module_aliases, &table.imports, &table.submodules);
}

/// Install the module-path aliases `module`'s declarations make: each import
/// `as`-alias (`(import [(target alias) …])`), targeting the module the spec
/// resolves to among `submodules`, and each `(mod util)` short name, targeting
/// `<module>.util`. Every entry is private and keyed by `module`, so an alias
/// serves only `module`'s own qualified references. The same aliases Pass 0
/// writes through `install_imports` and `register_submodule_alias`.
pub(crate) fn install_declared_aliases(
    module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    imports: &[ImportSpec],
    submodules: &[ModDecl],
) {
    let declared = DeclaredChildren::of(module, submodules);
    for spec in imports {
        install_import_alias(module, module_aliases, &declared.resolve_import(spec));
    }
    for decl in submodules {
        let sub_path = declared_child_path(module, decl.name.as_ref());
        module_aliases.insert(
            cranelisp_types::module_alias_key(module, decl.name.as_ref()),
            ModuleAliasEntry::new(sub_path, Visibility::Private, decl.span),
        );
    }
}

/// Whether a module with these structural declarations gets the prelude
/// fallback: every module except the prelude itself that does not import or
/// export `prelude` explicitly (§8.8.1). The structural equivalent of
/// `dependency::sexps_reference_prelude`, for callers without the source sexps.
pub(crate) fn gets_prelude_fallback(
    module: &ModuleFullPath,
    imports: &[ImportSpec],
    exports: &[ExportSpec],
) -> bool {
    let is_prelude = |path: &ModuleFullPath| path.as_ref() == "prelude";
    !is_prelude(module)
        && !imports.iter().any(|s| is_prelude(&s.module_path))
        && !exports.iter().any(|s| is_prelude(&s.module_path))
}

/// Register a resolved spec's module-path alias (§8.3.4, §8.3.6), if it has
/// one, targeting the module the spec names. This is the one import-alias
/// writer, and it needs no loaded target: a name-less alias-only import
/// registers its alias without loading anything.
pub(crate) fn install_import_alias(
    current_module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    resolved: &ResolvedSpec<'_, ImportSpec>,
) {
    let spec = resolved.spec;
    if let Some(alias) = &spec.alias {
        module_aliases.insert(
            alias_key(current_module, alias.as_ref()),
            ModuleAliasEntry::new(resolved.module.clone(), Visibility::Private, spec.span),
        );
    }
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
