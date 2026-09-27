//! Disk-cache restoration (S87 §1.1 extraction from `process_form.rs`).
//!
//! Restore a module from the disk cache, skipping typecheck: validity check →
//! meta decode → table install → platform re-resolve → scheduler register →
//! transitive recurse. `try_cache_hit_load` is the single entry point (called
//! from `dependency.rs`'s structural handlers before they fall through to a
//! fresh build); the phase helpers (`cache_validity_check`/`extract_cached_specs`/
//! `install_cached_table`/`reresolve_cached_platforms`/`register_cached_with_scheduler`)
//! were lifted along the existing `1.`…`9.` phase comments (S87 §3.1).
//!
//! Cross-submodule: calls `super::register_dep` (the per-dep prologue lives in
//! `dependency.rs`).

use std::collections::BTreeSet;
use std::path::Path;

use cranelisp_types::{
    CranelispError, Decl, ErrorLocation, ImportNames, ImportSpec, Life, ModDecl, ModuleFullPath,
    PlatformSpec, Realization, Span, Symbol, WrittenTraitImpl,
};

use crate::cache::dependency_record::{
    DependencyRecord, ModuleSources, callee_modules, is_compiler_owned,
};
use crate::scheduler::{CachedLoadHold, CompileScheduler};
use crate::session_setup::CacheValidity;
use crate::worker::{ModuleCompiler, ensure_typecheck_product};

use super::register_dep;

/// Attempt to load a module from the disk cache, skipping typecheck.
///
/// Returns `true` if the module was successfully loaded from cache:
/// type info restored into TC, module registered with scheduler at
/// TypecheckDone, GOT slots pre-allocated, **and transitive imports
/// recursively cache-loaded or registered for fresh build**. Returns
/// `false` on any cache miss (caller falls through to full typecheck
/// path).
///
/// **Decision 37 / Sprint 58 Wave 2c**: cache-hit decision lives inside
/// the recursive `register_module(M)` flow. After installing M's symbol
/// table, we walk `M.imports`, re-export targets and callee modules and
/// recursively attempt cache-load for each transitive dep — failing over
/// to fresh-build registration when
/// any dep is not cached. This ensures cache-hit modules' transitive
/// `__cranelisp_got_{transitive_dep}` symbols are registerable when the
/// codegen-phase worker walks `symbol_tables` (per Decision 37 §3.2).
pub(super) fn try_cache_hit_load<'a>(
    ctx: &mut ModuleCompiler<'a>,
    dep: &ModuleFullPath,
    dep_file: &Path,
) -> Result<bool, CranelispError> {
    // Already-installed guard: another path may have installed this dep
    // already (concurrent load, prelude pre-load). Skip without re-reading.
    // Returning `true` signals "this dep is satisfied — caller proceeds";
    // the caller will register imports against the existing table.
    if ctx.symbol_tables.contains_key(dep) {
        return Ok(true);
    }

    // Phases 1–3: validity check + meta decode + `.o`-exists gate. `None` on any
    // miss → caller returns `false`.
    let Some(ValidCacheEntry {
        cached,
        source,
        needs_inmem_load,
    }) = cache_validity_check(ctx, dep, dep_file)
    else {
        return Ok(false);
    };

    // Phase 4: extract all data BEFORE moving the symbol table (avoids clone /
    // honours the extract-before-move ordering invariant).
    let mut specs = extract_cached_specs(dep, &cached);

    // A writer-side impl record publishes its discovery shell into the trait's
    // HOME table. Make those homes available before consuming/installing the
    // writer cache; if a home is not itself cache-restorable, treat the writer
    // as an ordinary miss so fresh typecheck can drive the dependency. This
    // also keeps malformed metadata distinct from a benign cache miss.
    if !prepare_cached_trait_homes(ctx, dep, &specs.written_trait_impls)? {
        return Ok(false);
    }

    // Restore type info into TC (consumes `symbol_table` by value).
    install_cached_table(ctx, dep, cached);

    // Re-resolve platform fn ptrs. A failure aborts the cache-hit (miss).
    if !reresolve_cached_platforms(ctx, dep, &specs.platforms) {
        return Ok(false);
    }

    // Phases 5–8: scheduler register + typecheck-product + record-hit +
    // cached-module insert + file_to_module. The object load stays held until
    // the walk, which installs the tables `dep`'s object links against, has
    // returned by any path (`design/int/int.md` §7.1).
    let symbols = std::mem::take(&mut specs.symbols);
    let load_hold =
        register_cached_with_scheduler(ctx, dep, dep_file, symbols, source, needs_inmem_load);
    walk_restored_module(ctx, dep, &specs, load_hold.as_ref())?;

    Ok(true)
}

/// Phase 9 of `try_cache_hit_load`: restore or register everything `dep`'s
/// object and declarations reach. Borrowing the hold keeps `dep`'s object
/// load held until this walk returns.
fn walk_restored_module(
    ctx: &mut ModuleCompiler,
    dep: &ModuleFullPath,
    specs: &CachedSpecs,
    _load_hold: Option<&CachedLoadHold<'_>>,
) -> Result<(), CranelispError> {
    register_transitive_cached_imports(ctx, &specs.imports)?;
    // Re-export targets are transitive deps too (FIXME 0387 — prelude's
    // `(export [text.string [str]])` etc.). Walk them through the same path.
    register_transitive_cached_imports(ctx, &specs.reexport_deps)?;
    // Callee modules: the restored object binds their GOTs even when no
    // import names them (§7.6.1). The walk installs no names in `dep`.
    for callee_module in &specs.callee_modules {
        register_cached_dependency(ctx, callee_module)?;
    }
    enrol_cached_written_impls(ctx, dep, &specs.written_trait_impls)?;
    // Declared submodules are part of the parent's load graph even when they
    // are private and never imported. A fresh parent enrolls them after its
    // own cluster commits; cache restore must mirror that structural walk or
    // commands such as `/run-tests parent.test` cannot see the child at all.
    register_cached_submodules(ctx, dep, &specs.submodules)
}

/// A cache entry that passed every restore gate.
struct ValidCacheEntry {
    cached: cranelisp_backend::cache::CachedModule,
    source: RestoredSource,
    /// Whether the module has an `.o` to load (a generic-only module has none).
    needs_inmem_load: bool,
}

/// The source version a restore installs, recorded for the importers'
/// dependency records (`design/int/int.md` §7.6).
struct RestoredSource {
    source_hash: String,
    record: DependencyRecord,
}

/// Phases 1–3 of `try_cache_hit_load`: cache-dir check, source read + hash,
/// manifest validity (own source and every recorded dependency), meta decode,
/// and the `.o`-exists / generic-only gate. Returns `None` on any cache miss.
fn cache_validity_check(
    ctx: &ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
) -> Option<ValidCacheEntry> {
    use cranelisp_backend::cache;
    use cranelisp_backend::cache::manifest as cache_manifest;

    let shared = ctx.shared_state?;

    // 1. Check cache validity: read source, compute hash, check manifest.
    let cache_dir = shared.cache.cache_dir()?;

    let dep_source = std::fs::read_to_string(dep_file).ok()?;
    let source_hash = cache_manifest::hash_source(&dep_source);

    let sources = ModuleSources::new(ctx.project_root, ctx.lib_dirs);
    let CacheValidity::Valid { record } = shared.cache.validate(dep, &source_hash, &sources) else {
        return None;
    };

    // `CRANELISP_MODULE_TRACE` — the module-discovery / compile-order / cache-hit
    // observability channel (tests/CLAUDE.md §"Diagnostic Logging"). The `.meta`
    // is valid here: the module's typecheck result is cached (a cache HIT on the
    // typecheck artifact), so the import path reuses it rather than re-deriving
    // it from scratch. This is the S91 index→import cache-hit signal (§25.5): a
    // module the indexer wrote a `.meta` for (no `.o`) validates here and its
    // typecheck is reused on a later real `/import`.
    if std::env::var("CRANELISP_MODULE_TRACE").is_ok() {
        eprintln!("module-trace: cache hit (.meta valid) for {dep}");
    }

    // 2. Load metadata from disk.
    let cached = match cache::try_load_cached_module(&cache_dir, dep) {
        Ok(Some(c)) => c,
        _ => return None,
    };
    if !cache_macro_clauses_valid(&cached.symbol_table) {
        return None;
    }

    // 3. Check .o exists — UNLESS this is a generic-only module that codegens
    //    nothing (S84 Phase 4B, FIXME 0387). The `.meta.json` persists
    //    independently of the `.o` now: a module whose only defs are slot-less
    //    `Polymorphic` templates produces no codegen object (its
    //    `codegen_targets()` batch is empty), yet its schemes still cache so a
    //    downstream module can monomorphise it on cold-load. For such a module a
    //    missing `.o` is the CORRECT cached state, not a miss; we install its
    //    schemes and register it WITHOUT scheduling an `.o` load. A non-empty
    //    codegen batch with a missing `.o` is still a genuine cache miss
    //    (recompile).
    let has_codegen_targets = cached.symbol_table.codegen_targets().next().is_some();
    if !cached.has_object && has_codegen_targets {
        return None;
    }
    let needs_inmem_load = cached.has_object;

    Some(ValidCacheEntry {
        cached,
        source: RestoredSource {
            source_hash,
            record,
        },
        needs_inmem_load,
    })
}

/// Cache metadata is accepted only when every owned macro clause has the
/// canonical expansion argument ABI, a concrete result, and a concrete body.
/// Macro bodies retain their inferred concrete result type: definition alone
/// does not require it to be `Sexp`; invocation validates the produced value.
/// Family roster identity and lifecycle shape are validated by the types-owned
/// deserialization gate.
fn cache_macro_clauses_valid(table: &cranelisp_types::SymbolTable) -> bool {
    let abi = super::macro_clause::macro_clause_scheme();
    for (_, binding) in table.all_symbols() {
        let Decl::Macro(declaration) = &binding.declaration else {
            continue;
        };
        for clause in &declaration.clauses {
            if !super::macro_clause::same_macro_abi(&clause.callable.scheme, &abi)
                || !matches!(
                    clause.callable.life,
                    Life::Concrete {
                        realization: Realization::Body { .. },
                        ..
                    }
                )
            {
                return false;
            }
        }
    }
    true
}

/// Structural specs pulled out of a `CachedModule`'s symbol table BEFORE it is
/// moved into the live tables (phase 4 of `try_cache_hit_load`). Named struct
/// (no bare tuple) per `src/CLAUDE.md §Code Structure`.
struct CachedSpecs {
    /// All `Def`-named symbols (for scheduler register).
    symbols: std::collections::HashSet<Symbol>,
    /// Platform decls — re-resolved after install.
    platforms: Vec<PlatformSpec>,
    /// User-authored imports — recursed as transitive deps.
    imports: Vec<ImportSpec>,
    /// Re-export edges (as `ImportSpec`-shaped specs) — also transitive deps.
    reexport_deps: Vec<ImportSpec>,
    /// `(mod ...)` / `(mod- ...)` declarations — enrolled recursively just as
    /// they are after a fresh parent compile.
    submodules: Vec<ModDecl>,
    /// Canonical writer-side trait implementation records. Cache restore
    /// re-enrols each one into its trait-home table.
    written_trait_impls: Vec<WrittenTraitImpl>,
    /// Modules the table's callables call — also transitive deps.
    callee_modules: BTreeSet<ModuleFullPath>,
}

/// Phase 4: extract every spec the install + register + recurse phases need out
/// of the about-to-be-moved cached symbol table (extract-before-move invariant).
fn extract_cached_specs(
    dep: &ModuleFullPath,
    cached: &cranelisp_backend::cache::CachedModule,
) -> CachedSpecs {
    use std::collections::HashSet as StdHashSet;

    let symbols: StdHashSet<Symbol> = cached
        .symbol_table
        .all_symbols()
        .filter_map(|(name, entry)| {
            matches!(
                entry.declaration,
                Decl::Callable(_) | Decl::Overloaded(_) | Decl::Macro(_)
            )
            .then(|| name.clone())
        })
        .collect();
    // Collect names of functions with GOT slots for trait impl restoration.
    // The callable slot rides on the `DefKind` variant (S83 reshape, FIXME
    // 0356/0357) — a Def with a callable slot is a got-slotted function.
    let mangled_names: Vec<String> = cached
        .symbol_table
        .codegen_targets()
        .map(|(target, _)| format!("{target:?}"))
        .collect();
    // `mangled_names` is preserved here as a marker for the cached-fn set in
    // case future audits need it (it was a no-op pass-through in the original).
    let _ = &mangled_names;
    // Sprint 58 Step 5b §3.2 — pull structural decls (platforms) out of the
    // about-to-be-moved symbol table BEFORE `restore_cached_module` consumes
    // it. We re-resolve platform DLLs after install so each
    // `PlatformEffect`-kind entry's `fn_ptr` is repopulated
    // (Decision 26 — re-derive on cache-hit load via the same
    // `load_and_register_platform` path used by fresh build).
    let platforms: Vec<PlatformSpec> = cached.symbol_table.platforms.clone();

    // Sprint 58 Wave 2c / Decision 37 — capture user-authored imports BEFORE
    // moving the symbol table, so we can recurse and ensure every
    // transitive dep's symbol table (and `__cranelisp_got_{M}` data symbol)
    // is installed before this dep's codegen worker tries to load its `.o`.
    let imports: Vec<ImportSpec> = cached.symbol_table.imports.clone();

    // S84 Phase 4B / FIXME 0387 — a re-export edge (`(export [mod [names]])`) is
    // ALSO a transitive dependency: the re-exported target module must be
    // installed on cache-restore so a downstream consumer can chain-follow the
    // re-export to the canonical entry. The prelude is the motivating case — it
    // re-exports `text.string`'s `str` macro etc. via `exports` (NOT `imports`),
    // and once the prelude's own `.meta.json` caches (0387) its cache-restore
    // must load those targets or a bare `str` resolves to nothing
    // (`undefined variable: str`). Capture the exports as `ImportSpec`-shaped
    // specs (drop the missing `alias`) so the same transitive walk handles them.
    let reexport_deps: Vec<ImportSpec> = cached
        .symbol_table
        .exports
        .iter()
        .map(|e| ImportSpec {
            module_path: e.module_path.clone(),
            alias: None,
            names: e.names.clone(),
            span: e.span,
        })
        .collect();
    let submodules = cached.symbol_table.submodules.clone();
    let written_trait_impls = cached.symbol_table.written_trait_impls.clone();
    let callee_modules = callee_modules(dep, &cached.symbol_table);

    CachedSpecs {
        symbols,
        platforms,
        imports,
        reexport_deps,
        submodules,
        written_trait_impls,
        callee_modules,
    }
}

/// Ensure every foreign trait-home table required by a cached writer is
/// synchronously restored before the writer table is consumed. A valid cache
/// miss returns `Ok(false)`; malformed provenance is a hard cache diagnostic.
fn prepare_cached_trait_homes(
    ctx: &mut ModuleCompiler,
    writer: &ModuleFullPath,
    records: &[WrittenTraitImpl],
) -> Result<bool, CranelispError> {
    for record in records {
        let canonical_names_present = !record.trait_name.module.as_ref().is_empty()
            && !record.trait_name.name.as_ref().is_empty()
            && !record.impl_type.module.as_ref().is_empty()
            && !record.impl_type.name.as_ref().is_empty();
        if &record.impl_module != writer || record.methods.is_empty() || !canonical_names_present {
            // Malformed persisted provenance is cache-stale: refuse this
            // sidecar before installing the writer so the caller can rebuild
            // it from source. A divergent live shell is different and remains
            // a hard error at `enrol_written_trait_impl` below.
            return Ok(false);
        }
        let home = &record.trait_name.module;
        if home == writer || ctx.symbol_tables.contains_key(home) {
            continue;
        }
        let Some(home_file) =
            crate::pipeline::resolve_module_file(home, ctx.project_root, ctx.lib_dirs)
        else {
            return Ok(false);
        };
        if !try_cache_hit_load(ctx, home, &home_file)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Publish cached writer records through the single strict trait-home
/// enrollment primitive. Divergent occupants remain hard errors.
fn enrol_cached_written_impls(
    ctx: &ModuleCompiler,
    writer: &ModuleFullPath,
    records: &[WrittenTraitImpl],
) -> Result<(), CranelispError> {
    for record in records {
        let mut home = ctx
            .symbol_tables
            .get_mut(&record.trait_name.module)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "cannot restore impl written by '{}': trait home '{}' is not loaded",
                    writer, record.trait_name.module
                ),
                location: ErrorLocation::unknown(),
            })?;
        cranelisp_types::enrol_written_trait_impl(&mut home, record)?;
    }
    Ok(())
}

/// Install the cached (decoded) symbol table into the live tables — the
/// `advance_next_id_past_table` + `install_module` pair (consumes `cached`).
///
/// Restore type info into TC (consumes symbol_table by value).
/// Sprint 58 Wave 3b: cached `<()>` table is converted to `<Code, ()>`
/// via `into_concrete` (every entry's `code` becomes `None::<Code>`;
/// codegen will populate fresh `Code::Jit` / `Code::Linker` entries).
///
/// Sprint 67 hack-back (FIXME 0192 method 11 split): the prior
/// `restore_cached_module` method is deleted. Compose the two primitives
/// directly: advance `next_type_id` past any TypeId vars in the cached
/// schemes (preserves the consistency invariant — fresh vars must not
/// collide with cached vars during `apply_subst`), then atomically
/// install the decoded table via the `cranelisp-types` primitive.
fn install_cached_table(
    ctx: &ModuleCompiler,
    dep: &ModuleFullPath,
    cached: cranelisp_backend::cache::CachedModule,
) {
    let concrete_table = cached.symbol_table.into_concrete::<crate::code::Code, ()>();
    cranelisp_typecheck::advance_next_id_past_table(ctx.next_type_id, &concrete_table);
    cranelisp_types::install_module(ctx.symbol_tables, dep.clone(), concrete_table);
}

/// Re-resolve platform fn ptrs for each `(platform …)` decl recorded on the
/// cached SymbolTable. Returns `false` (a cache miss) if any platform fails to
/// load. Phase between install and scheduler register.
///
/// Sprint 58 Step 5b §3.2 — the GOT is `#[serde(skip)]` so cache-hit arrives
/// with all slots null; re-running `load_and_register_platform` opens the DLL,
/// validates the manifest, and populates the live entries on the synthetic
/// `platform.{name}` module. Unlike the fresh-build `handle_platform` path,
/// this cache-restore composition INTENTIONALLY skips the §7.2
/// associated-`.cl`-type-module pre-resolve (FIXME 0323): the cached sigs were
/// already FQ-resolved at build time and decoded into the restored SymbolTable
/// above, so there is no unresolved type-ref to drive a dependency for — only
/// the fn-ptr GOT slots (`#[serde(skip)]`) need re-populating. Failures here
/// are non-fatal at the cache-hit level (we treat them as "platform missing —
/// fall back to full rebuild" per `design/int/int.md` §7.1); we abandon the
/// cache-hit attempt and let the normal load path retry.
fn reresolve_cached_platforms(
    ctx: &ModuleCompiler,
    dep: &ModuleFullPath,
    cached_platforms: &[PlatformSpec],
) -> bool {
    let shared = match ctx.shared_state {
        Some(s) => s,
        None => return true,
    };
    for spec in cached_platforms {
        // Submodules cannot load platforms (spec §10.9.1) — skip.
        if dep.as_ref().contains('.') {
            continue;
        }
        match crate::platform::load_and_register_platform(
            ctx.symbol_tables,
            ctx.module_aliases,
            &spec.name,
            ctx.project_root,
            ctx.lib_dirs,
            ctx.platform_dirs,
            spec.span,
        ) {
            Ok(platform) => {
                // `register_platform_in_tc` already wrapped the DLL's exported
                // GOT in place and set `got_slot = manifest index` per entry
                // (platform-interface.md §6.4); no per-slot allocation / fn-ptr
                // store is needed on cache-hit either. Retain the DLL handle for
                // session lifetime so the wrapped slab + pointers stay valid.
                shared
                    .kept_dlls
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(platform);
            }
            Err(_) => {
                // Cache invalid for this run — treat as cache miss.
                return false;
            }
        }
    }
    true
}

/// Phases 5–8 of `try_cache_hit_load`: scheduler register (object / no-object),
/// typecheck-product create, record-cache-hit, cached-module insert, and the
/// file_to_module mapping. Returns the object-load hold, if one was placed.
fn register_cached_with_scheduler<'a>(
    ctx: &ModuleCompiler<'a>,
    dep: &ModuleFullPath,
    dep_file: &Path,
    symbols: std::collections::HashSet<Symbol>,
    source: RestoredSource,
    needs_inmem_load: bool,
) -> Option<CachedLoadHold<'a>> {
    let shared = ctx.shared_state?;
    let scheduler: &'a CompileScheduler = ctx.scheduler;

    // 5. Register with scheduler at TypecheckDone. A generic-only module with no
    //    `.o` (FIXME 0387) registers as already-inmem-done (no codegen load to
    //    schedule); any other cached module registers with its `.o` load held
    //    for the caller to release.
    let load_hold = if needs_inmem_load {
        scheduler.register_module_cached(dep.clone(), symbols)
    } else {
        scheduler.register_module_cached_no_object(dep.clone(), symbols);
        None
    };

    // 6. Create typecheck product with GOT table for cached module, and make
    //    `file_path` authoritative (S102 CS-D3a, §6.2.1): the restore is keyed
    //    by the source file it hashed, so `dep_file` is the module's real
    //    backing file. The rehydration chokepoint (`resolve_recheck_sexps`),
    //    `module_grain_reload`, and `regenerate_backing_file` all read this —
    //    a cache-restored module carries no introspection, so dependent
    //    recompilation reaches its stored bodies ONLY via this file authority.
    ensure_typecheck_product(ctx.typecheck_products, dep);
    if let Some(mut tp) = ctx.typecheck_products.get_mut(dep) {
        tp.file_path = Some(dep_file.to_path_buf());
    }

    // Establish the session-env companions (prelude-fallback bit + aliases) from
    // the just-installed table's structural fields (S102 CS-D3a, §6.2.2). The
    // cache-restore path populated none of them, so a `/mod {dep}` turn would
    // otherwise typecheck with no prelude fallback (`undefined variable: +`) and
    // no aliases — the /port D3 / FIXME 0487 env wall.
    crate::imports::install_module_session_env(
        ctx.symbol_tables,
        dep,
        ctx.module_aliases,
        ctx.prelude_fallback,
    );

    // 7. Record cache hit with the record it validated under.
    shared
        .cache
        .record_cache_hit(dep, source.source_hash, source.record);

    // 8. Record in cached_modules set (via scheduler — Sprint 67 Cluster B
    //    sub-fire 2e) and file_to_module mapping.
    shared.scheduler.cached_module_insert(dep.clone());
    if let Ok(canonical) = dep_file.canonicalize() {
        shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(canonical, dep.clone());
    }
    load_hold
}

/// Walk a cached module's `imports` and ensure each transitive dep is
/// installed. A null import (§8.3.6) loads nothing and is skipped here only;
/// the same module reached as a callee still loads.
pub(super) fn register_transitive_cached_imports(
    ctx: &mut ModuleCompiler,
    imports: &[ImportSpec],
) -> Result<(), CranelispError> {
    for spec in imports {
        if matches!(&spec.names, ImportNames::None) {
            continue;
        }
        register_cached_dependency(ctx, &spec.module_path)?;
    }
    Ok(())
}

/// Ensure one dependency of a cache-restored module is installed, by cache
/// hit or fresh-build registration (Decision 37 §3.2). Imports, re-export
/// targets and callee modules share this step.
///
/// - Session-installed modules (`primitives`, `macros`, `platform.*`,
///   `prelude`) and already-installed modules are satisfied.
/// - An unresolvable file is left for the regular handler to report.
/// - A cache miss registers the module with the scheduler without blocking:
///   restore runs inside the outer module's form processing, which cannot
///   also drive a fresh build.
#[allow(clippy::result_large_err)] // CranelispError is the crate-wide error carrier
fn register_cached_dependency(
    ctx: &mut ModuleCompiler,
    dependency: &ModuleFullPath,
) -> Result<(), CranelispError> {
    if is_compiler_owned(dependency)
        || dependency.as_ref() == "prelude"
        || ctx.symbol_tables.contains_key(dependency)
    {
        return Ok(());
    }
    let Some(dep_file) =
        crate::pipeline::resolve_module_file(dependency, ctx.project_root, ctx.lib_dirs)
    else {
        return Ok(());
    };
    if try_cache_hit_load(ctx, dependency, &dep_file)? {
        return Ok(());
    }
    // `register_dep` publishes the sexps before returning, stashes the source
    // text and hash, and maps the file. A read or parse failure here is left
    // for the regular handler to surface when it reaches the dependency.
    let dep_file_ref = dep_file.clone();
    let dep_for_err = dependency.clone();
    let Ok(dep_sexps) = register_dep(ctx, dependency, &dep_file, |e| {
        CranelispError::ModuleError {
            message: format!(
                "failed to read transitive dep '{}' from '{}': {}",
                dep_for_err,
                dep_file_ref.display(),
                e
            ),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(dep_file_ref.clone())),
        }
    }) else {
        return Ok(());
    };
    // Every dependency site passes `delays_other = true`
    // (`design/int/int.md` §6.1, queue-priority rule).
    ctx.scheduler
        .register_module(dependency.clone(), dep_sexps, true);
    Ok(())
}

/// Enrol every child declared by a cache-restored parent. Metadata restoration
/// is synchronous when the child also hits cache; a cache miss is registered
/// for the ordinary priority-worker path. Unlike imports, visibility is
/// irrelevant: `(mod- child)` still belongs to the parent's module graph.
fn register_cached_submodules(
    ctx: &mut ModuleCompiler,
    parent: &ModuleFullPath,
    declarations: &[ModDecl],
) -> Result<(), CranelispError> {
    for decl in declarations {
        // The cached parent is already terminal, so it does not enter the
        // fresh parent's TypecheckBlocked/retry protocol. Enrollment itself is
        // nevertheless identical and errors remain mandatory.
        let _ = super::dependency::enrol_declared_submodule(ctx, parent, decl)?;
    }
    Ok(())
}
