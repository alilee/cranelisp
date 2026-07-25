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

use std::collections::HashSet;

use cranelisp_typecheck::PreludeFallback;
use cranelisp_types::{
    CranelispError, DefKind, ErrorLocation, ExportSpec, FQSymbol, ImportNames, ImportSpec,
    ModuleAliasEntry, ModuleAliases, ModuleEntry, ModuleFullPath, Span, Symbol, TraitName,
    Visibility,
};

/// The session-side declared-export closure map (FIXME 0604 §2.2): `M → D(M)`,
/// where `D(M)` is the union of the names `M`'s own `(export …)` specs bring in.
/// A **separate** `DashMap` from `symbol_tables` (so a read never re-enters a
/// `get_mut` shard the caller holds — the deadlock hazard) and **unserialized**,
/// recomputed per session (modelled on `prelude_fallback`). `check_terminal_closure`
/// keys on `D(M)`, not on the source-provider heuristic the S114 predicate used.
pub(crate) type DeclaredExports = dashmap::DashMap<ModuleFullPath, HashSet<Symbol>>;

use crate::code::{Code, SessionSymbolTable};

type SessionTables = dashmap::DashMap<ModuleFullPath, SessionSymbolTable>;

/// Install resolved import bindings for `specs` into `current_module`'s symbol
/// table, plus any module-path aliases into `module_aliases`. Replaces the
/// struck `cranelisp_typecheck::register_imports`.
///
/// `prelude_fallback` carries the per-module implicit-prelude bit so
/// [`insert_detecting_ambiguity`] can poison a **distinct-terminal** overlap
/// between an incoming import and a prelude-provided name of the same bare name
/// (§8.6.5 — the prelude is just an implicit import; FIXME 0514/0515). The
/// former Additive-gated import-over-local-def rejection is retired: the
/// symmetric §8.6.4 def/import collision now fires uniformly at the shared
/// typecheck `check_forms` seam (a def registered over an already-installed
/// import), so the installer keeps only ambiguity detection.
pub(crate) fn install_imports(
    symbol_tables: &SessionTables,
    current_module: &ModuleFullPath,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,
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
        for (name, entry) in &to_add {
            check_terminal_closure(current_module, name.as_ref(), entry, spec.span, None)?;
        }
        insert_detecting_ambiguity(
            symbol_tables,
            current_module,
            prelude_fallback,
            to_add,
            spec.span,
        )?;
    }
    Ok(())
}

/// Install re-export bindings for `specs` into `current_module`'s symbol
/// table. Replaces the struck `cranelisp_typecheck::register_exports`.
/// Re-export edges resolve their source module via try-as-is then
/// child-of-current (spec §8.6.x relative form) and install `Public`-visible
/// `ModuleEntry::Import` bindings (the retired `Reexport` variant's effect).
///
/// `export` populates the inner scope identically to `import` (§8.4.0), so it
/// runs through the SAME [`insert_detecting_ambiguity`] path (including the
/// distinct-terminal prelude-overlap poison, §8.6.5).
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
    prelude_fallback: &PreludeFallback,
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
        let spec_names: HashSet<Symbol> = to_add.iter().map(|(n, _)| n.clone()).collect();
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
        for (name, entry) in &to_add {
            check_terminal_closure(
                current_module,
                name.as_ref(),
                entry,
                spec.span,
                Some(&spec_names),
            )?;
        }
        insert_detecting_ambiguity(
            symbol_tables,
            current_module,
            prelude_fallback,
            to_add,
            spec.span,
        )?;
    }
    Ok(())
}

/// R7/0604 observability rider (`index-worker-isolation.md` §8; `/arch`
/// `safety-invariants.md` R7). ONE shared seam assert (Principle 7/18) called
/// BESIDE every live-table insertion. The invariant:
///
/// > a **public** binding written into the `prelude` module's live table MUST
/// > trace to prelude's own declared exports / re-export edges — never a
/// > foreground compile's import-direction write mis-targeting `prelude` (the
/// > phantom `bit-and → primitives/bit-and`, FIXME 0604).
///
/// **Observability ONLY — no behaviour change.** It does NOT locate or fix the
/// phantom writer (the S110 disposition re-scoped it to the foreground
/// concurrent-compile path; no stable RED exists). The deliverable is that the
/// NEXT firing anywhere NAMES its seam (`debug_assert!` in debug, `MODULE_TRACE`
/// emit in release) instead of needing another quiet-environment hunt. Because it
/// is single-sourced, its call sites are the greppable structural guard (§8.3): a
/// live-table insertion without the assert is a `/review` finding.
///
/// The closure check keys on the write's SOURCE (Principle 26 — read the settled
/// edge, not a name heuristic): a re-export/import edge into prelude is closure-
/// valid iff its source module GENUINELY provides the name publicly; prelude's own
/// definition (a non-`Import` entry) is exported by §8.4. An unknown source module
/// is permitted (cannot judge — observability must NEVER false-fire the build).
pub(crate) fn assert_prelude_closure(
    symbol_tables: &SessionTables,
    module: &ModuleFullPath,
    name: &str,
    entry: &ModuleEntry<Code>,
) {
    if module.as_ref() != "prelude" || !entry.is_public() {
        return;
    }
    if prelude_write_is_closure_valid(symbol_tables, entry) {
        return;
    }
    if std::env::var("CRANELISP_MODULE_TRACE").is_ok() {
        eprintln!(
            "[MODULE_TRACE] R7 prelude-export-closure breach: public `{name}` \
             written into the `prelude` live table but not traceable to prelude's \
             declared export closure (entry: {entry:?})"
        );
    }
    debug_assert!(
        false,
        "R7 prelude-export-closure breach: public `{name}` written into the \
         `prelude` live table but not in its export closure (entry: {entry:?}) — \
         a foreground import-direction write mis-targeting `prelude` (FIXME 0604)"
    );
}

/// Closure-validity of a public write into prelude's table (R7 rider helper).
fn prelude_write_is_closure_valid(
    symbol_tables: &SessionTables,
    entry: &ModuleEntry<Code>,
) -> bool {
    match entry {
        // A re-export / import edge: the SOURCE module must publicly provide the
        // name. NOTE (FIXME 0604 falsified-premise rider, /arch Phase-2 §4): this
        // legacy PRELUDE-ONLY observability rider is provider-existence shaped and
        // is BLIND to the live phantom by construction — `bit-and` IS a bundled
        // public primitive (`cranelisp-primitives/src/lib.rs:412`; homed in
        // num.bits only as a wrapper), so a phantom `bit-and → primitives/bit-and`
        // names a genuine provider and PASSES here. The authoritative gate is the
        // DECLARED-EXPORT-CLOSURE `check_terminal_closure` above (keyed on the
        // destination's `D(M)`, where `bit-and ∉ D(prelude)`); this rider stays as
        // a debug-only defense-in-depth tripwire, NOT the load-bearing check.
        ModuleEntry::Import { source, .. } => match symbol_tables.get(&source.module) {
            Some(src) => src
                .get(source.symbol.as_ref())
                .map(|e| e.is_public())
                .unwrap_or(false),
            None => true, // unknown source module — cannot judge; permit
        },
        // Prelude's own definition (§8.4: a public def is exported).
        _ => true,
    }
}

// ===========================================================================
// FIXME 0604 — the foreground public-write CHOKEPOINT (prelude-table-write-
// isolation.md §2). Isolation by construction: every foreground writer that can
// insert a PUBLIC entry into a module's live symbol table routes through the ONE
// `check_terminal_closure` gate (below) or carries a named legal-skip.
//
// ─────────────────────────── FOREGROUND WRITER CENSUS (§2.1) ───────────────
//
// | Writer seam                              | Public? | Disposition            |
// |------------------------------------------|---------|------------------------|
// | imports.rs::install_exports (Public)     | yes     | ROUTE through gate     |
// | imports.rs::install_imports (Private)    | no      | route (no-op: !public) |
// | imports.rs::insert_detecting_ambiguity   | reads/  | poison consumer —      |
// |   (§8.6.5 poison consumer)               | marks   | CORRECT, NOT TOUCHED;  |
// |                                          |         | its writes are already |
// |                                          |         | vetted by the install- |
// |                                          |         | seam gate above        |
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
// | platform.rs::register_platform_in_tc     | yes     | ROUTE through gate     |
// |   (DLL-load orchestration)               |         | (own-def arm, D=None)  |
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
// `bootstrap::tests::bootstrap_seeds_pass_the_terminal_closure_gate`, which
// sweeps EVERY seeded entry through `check_terminal_closure` under the strictest
// closure `D(M) = {}` — so a future cross-module PUBLIC `Import` seed (the
// phantom shape) turns that test RED.
//
// The census's job is to prove the set is CLOSED: no OTHER foreground seam can
// insert a public table entry without routing through the gate. The greppable
// structural guard (Principle 18): a public-insert seam that bypasses
// `check_terminal_closure` is a `/review` finding.
// ===========================================================================

/// The ONE terminal-table export-closure chokepoint (FIXME 0604, §2.2).
///
/// **Invariant:** a module never accepts a new PUBLIC entry outside its declared
/// export closure `D(M)`. Promotes the S113 prelude-only PS-R7 `debug_assert!`
/// ([`assert_prelude_closure`]) to an **unconditional, generalized, DIAGNOSED
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
/// - a module's own public definition (a non-`Import` entry) is exported by §8.4
///   → **Ok with NO map read** (keeps `register_macro_in_module`'s under-guard
///   gate call safe by construction — a macro/def `Def` never reaches the
///   `Import` arm);
/// - a public re-export `Import` edge whose `name ∈ D(M)` → Ok; `name ∉ D(M)`
///   (the phantom shape) → rejected + diagnosed;
/// - `declared_exports == None` (D(M) unknown/not-yet-recorded) → PERMIT — a
///   foreign write racing ahead of `M`'s own export processing is permitted; the
///   guard catches it once `D(M)` is recorded (the diagnostic must NEVER
///   false-fire).
///
/// Non-public writes are always Ok (isolation is a PUBLIC-write invariant).
pub(crate) fn check_terminal_closure(
    module: &ModuleFullPath,
    name: &str,
    entry: &ModuleEntry<Code>,
    span: Span,
    declared_exports: Option<&HashSet<Symbol>>,
) -> Result<(), CranelispError> {
    if !entry.is_public() || write_is_closure_valid(module, name, entry, declared_exports) {
        return Ok(());
    }
    let source_desc = match entry {
        ModuleEntry::Import { source, .. } => format!("{}/{}", source.module, source.symbol),
        _ => "own definition".to_string(),
    };
    if std::env::var("CRANELISP_MODULE_TRACE").is_ok() {
        eprintln!(
            "[MODULE_TRACE] 0604 terminal-closure breach: public `{name}` written into \
             module `{module}` from source `{source_desc}` — outside its declared export closure"
        );
    }
    Err(CranelispError::TypeError {
        message: format!(
            "internal: rejected out-of-closure public binding `{name}` into module \
             `{module}` (source `{source_desc}`) — not in the module's declared export \
             closure (FIXME 0604 terminal-table write isolation / R7 invariant breach)"
        ),
        location: ErrorLocation::from_span(span),
    })
}

/// Declared-export-closure validity predicate for [`check_terminal_closure`]
/// (Principle 26 — keyed on the DESTINATION's settled export surface). The
/// closure invariant is a CROSS-module invariant:
///
/// - a module's own definition (non-`Import`) is exported by §8.4 → Ok, NO map
///   read (own-def arm stays deadlock-safe under a held `get_mut`);
/// - an **intra-module self-alias** — an `Import` edge whose `source.module` is
///   the DESTINATION module itself (a bare ctor alias `ZedC → prelude/Zed.ZedC`
///   to the module's own canonical `Type.Ctor`, a same-module visibility upgrade,
///   …) — is the module aliasing its OWN entry, exported by §8.4 → Ok, NO D read;
/// - a **cross-module** public re-export (`source.module ≠ M`) is valid iff its
///   NAME is in `D(M)`; `name ∉ D(M)` (the phantom `bit-and → primitives/bit-and`
///   shape — source `primitives` ≠ dest `prelude`) → rejected;
/// - an unknown `D(M)` (`None`) is permitted (never false-fire).
fn write_is_closure_valid(
    module: &ModuleFullPath,
    name: &str,
    entry: &ModuleEntry<Code>,
    declared_exports: Option<&HashSet<Symbol>>,
) -> bool {
    match entry {
        // Intra-module self-alias — the module's OWN entry (§8.4); no D read.
        ModuleEntry::Import { source, .. } if source.module == *module => true,
        // Cross-module public re-export — checked against the destination's D(M).
        ModuleEntry::Import { .. } => match declared_exports {
            None => true, // D(M) unknown — cannot judge; permit (never false-fire)
            Some(d) => d.contains(&Symbol::from(name)),
        },
        _ => true, // the module's own definition (§8.4) — no map read
    }
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

/// The implicit-prelude module (§8.8.1). A module whose `prelude_fallback` bit
/// is ON resolves bare-name misses against this module's OWN public table.
const PRELUDE_MODULE: &str = "prelude";

/// The prelude module `current_module` falls back to as its OUTER scope, or
/// `None` when there is no fallback (bit OFF, or `current_module` IS the
/// prelude — a module never falls back onto itself). Mirrors typecheck's
/// `prelude_fallback_target` (S78 §2.7) on the int side.
fn prelude_fallback_target(
    prelude_fallback: &PreludeFallback,
    current_module: &ModuleFullPath,
) -> Option<ModuleFullPath> {
    if current_module.as_ref() != PRELUDE_MODULE
        && prelude_fallback
            .get(current_module)
            .map(|b| *b)
            .unwrap_or(false)
    {
        Some(ModuleFullPath::from(PRELUDE_MODULE))
    } else {
        None
    }
}

/// The prelude OUTER-scope terminal `(home, symbol)` for bare `name`, or `None`
/// when the prelude does not provide `name` as a reachable bare binding.
///
/// Public-only head filter (I-1 discipline, S78 §2): only a PUBLIC prelude head
/// entry is reachable as a bare name from a user module (never in prelude's
/// subtree), so a private prelude entry is treated as not-found and cannot
/// poison. The public head is chain-followed to its terminal via the shared
/// `cranelisp_types` primitive (so a prelude re-export of `primitives/x` shares
/// the same terminal as a direct `(import [primitives [x]])` — same terminal,
/// no poison).
fn prelude_terminal(
    symbol_tables: &SessionTables,
    prelude_path: &ModuleFullPath,
    name: &str,
) -> Option<(ModuleFullPath, Symbol)> {
    let head_public = {
        let guard = symbol_tables.get(prelude_path)?;
        guard.get(name)?.is_public()
    };
    if !head_public {
        return None;
    }
    cranelisp_types::resolve_terminal_entry_and_home(symbol_tables, prelude_path, name)
        .map(|(_, home)| (home, Symbol::from(name)))
}

/// §8.6.5 ambiguity diagnostic naming both qualified alternatives.
fn ambiguity_error(name: &Symbol, alt_a: &str, alt_b: &str, span: Span) -> CranelispError {
    CranelispError::TypeError {
        message: format!(
            "ambiguous bare name '{name}' — provided by distinct sources \
             '{alt_a}' and '{alt_b}'; use a qualified reference to disambiguate"
        ),
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
            // S109 W1 (dotted-ctor-canonical-keys.md §3.3): under the canonical
            // keying a matched constructor `Def` is keyed `Type.Ctor` (`Lst.Cons`);
            // a member-glob importer wants the BARE ctor reference too, so also
            // install a bare-alias edge (`Cons → source/Lst.Cons`) alongside the
            // canonical import. On pre-flip bare keying the name has no `.`, so
            // this is inert (commit 1 behaviour-invariant). A cross-type bare
            // collision at the importer is handled by `insert_detecting_ambiguity`
            // (§8.6.5), unchanged.
            if let Some((_, bare)) = name.as_ref().rsplit_once('.') {
                result.push((
                    Symbol::from(bare),
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
    prelude_fallback: &PreludeFallback,
    imports: Vec<(Symbol, ModuleEntry<Code>)>,
    span: Span,
) -> Result<(), CranelispError> {
    // The prelude OUTER scope this module falls back to (S78 §2.7), if any.
    // An incoming import/export whose bare name ALSO resolves in the prelude
    // outer scope with a DISTINCT terminal is a §8.6.5 ambiguity — the prelude
    // is just an implicit import, so a distinct-terminal overlap poisons the
    // bare name (FIXME 0514/0515). A SAME-terminal overlap (e.g. importing
    // `primitives/x` while the prelude re-exports it) is not a conflict.
    let prelude_target = prelude_fallback_target(prelude_fallback, current_module);

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
            // No prior INNER entry. Before installing, check the prelude OUTER
            // scope: a distinct-terminal overlap poisons the bare name.
            if let Some(prelude_path) = &prelude_target
                && let Some(prelude_term) =
                    prelude_terminal(symbol_tables, prelude_path, name.as_ref())
                && let Some(new_term) = terminal_identity(symbol_tables, &new_entry)
                && prelude_term != new_term
            {
                // R7 grep-guard (§8.3): observe the poison-sentinel insertion too
                // (an `Ambiguous` entry is non-`Import` → the assert short-circuits
                // to valid without a map read, so it is safe beside the insert).
                let poison = ModuleEntry::Ambiguous {
                    visibility: Visibility::Public,
                };
                assert_prelude_closure(symbol_tables, current_module, name.as_ref(), &poison);
                if let Some(mut guard) = symbol_tables.get_mut(current_module) {
                    guard.insert(name.clone(), poison);
                }
                let alt_import = format!("{}/{}", new_term.0, new_term.1);
                let alt_prelude = format!("{}/{}", prelude_term.0, prelude_term.1);
                return Err(ambiguity_error(&name, &alt_import, &alt_prelude, span));
            }
            // No prelude overlap (or same terminal) — install directly.
            // R7 rider (§8.3): observe the write BESIDE the insertion (never
            // inside the §8.6.5 poison decision above — that logic is CORRECT).
            assert_prelude_closure(symbol_tables, current_module, name.as_ref(), &new_entry);
            if let Some(mut guard) = symbol_tables.get_mut(current_module) {
                guard.insert(name, new_entry);
            }
            continue;
        };

        // Import-over-def (§8.6.4 symmetric companion; FIXME 0516 #8). The
        // existing entry is a module-LOCAL definition (`Def` — incl. a
        // `DefKind::Macro` binding — / `TypeDef` / `TraitDecl`) and `new_entry`
        // is an incoming import/export edge. This is the ONLY place this
        // direction can be caught: no def registers in THIS import's cluster, so
        // the typecheck def-event seam never fires (the REPL separate-turn hole).
        // Reject via the SAME shared predicate the def-event uses
        // (`check_binding_addition`) — one rule, both events, all modes. It fires
        // ONLY across clusters: within a single cluster Pass-0 install precedes
        // Pass-1 def-register, so no local def exists at install time (that case
        // is caught by the def-event) — no double-fire. `TraitDecl` is in the set
        // (S108 Wave-G CS2): a local `deftrait` bound as `TraitDecl` was
        // previously invisible to this predicate, so a later import over it
        // escaped the symmetric §8.6.4 rejection.
        if matches!(
            existing,
            ModuleEntry::Def { .. } | ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. }
        ) {
            let incoming = if new_entry.is_public() {
                cranelisp_types::BindingProvenance::Export
            } else {
                cranelisp_types::BindingProvenance::Import
            };
            // The FQ remedy is the incoming import's terminal identity — the
            // symbol the user should reference qualified rather than bind bare
            // over the local definition.
            let remedy = terminal_identity(symbol_tables, &new_entry)
                .map(|(module, symbol)| FQSymbol { module, symbol })
                .unwrap_or_else(|| match &new_entry {
                    ModuleEntry::Import { source, .. } => source.clone(),
                    _ => FQSymbol {
                        module: current_module.clone(),
                        symbol: name.clone(),
                    },
                });
            return cranelisp_types::check_binding_addition(
                &name,
                incoming,
                cranelisp_types::BindingProvenance::Definition,
                &remedy,
                span,
            );
        }

        let both_indirect = matches!(
            (&existing, &new_entry),
            (ModuleEntry::Import { .. }, ModuleEntry::Import { .. })
        );
        if !both_indirect {
            // The existing entry is some other directly-bound kind (`Ambiguous`,
            // `SpecialForm`, `IntrinsicType`) — it takes priority; skip the new
            // import/export edge.
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
            if !existing.is_public() && new_entry.is_public() {
                // R7 rider: observe the public visibility-upgrade write BEFORE
                // acquiring the mutable guard (the assert reads other tables — it
                // must not run while a `get_mut` guard is held, DashMap shard
                // re-entrancy).
                assert_prelude_closure(symbol_tables, current_module, name.as_ref(), &new_entry);
                if let Some(mut guard) = symbol_tables.get_mut(current_module) {
                    guard.insert(name, new_entry);
                }
            }
            continue;
        }

        // Distinct terminals → §8.6.5 ambiguity. Uniform — no name-keyed
        // exemption (S78 §2: `is_seeded` deleted). Install the poison sentinel
        // (spec poison-on-reference model) AND report eagerly with both
        // qualified alternatives so the user can disambiguate.
        // R7 grep-guard (§8.3): observe the poison-sentinel insertion.
        let poison = ModuleEntry::Ambiguous {
            visibility: Visibility::Public,
        };
        assert_prelude_closure(symbol_tables, current_module, name.as_ref(), &poison);
        if let Some(mut guard) = symbol_tables.get_mut(current_module) {
            guard.insert(name.clone(), poison);
        }
        let (alt_a, alt_b) = qualified_alternatives(
            &name,
            &existing_terminal,
            &new_terminal,
            &existing,
            &new_entry,
        );
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
