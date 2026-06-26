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

use std::path::Path;

use cranelisp_types::{
    CranelispError, ErrorLocation, ImportNames, ImportSpec, ModuleEntry,
    ModuleFullPath, PlatformSpec, Span, Symbol,
};

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
/// table, we walk `M.imports` and recursively attempt cache-load for
/// each transitive dep — failing over to fresh-build registration when
/// any dep is not cached. This ensures cache-hit modules' transitive
/// `__cranelisp_got_{transitive_dep}` symbols are registerable when the
/// codegen-phase worker walks `symbol_tables` (per Decision 37 §3.2).
pub(super) fn try_cache_hit_load(
    ctx: &mut ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
) -> bool {
    // Already-installed guard: another path may have installed this dep
    // already (concurrent load, prelude pre-load). Skip without re-reading.
    // Returning `true` signals "this dep is satisfied — caller proceeds";
    // the caller will register imports against the existing table.
    if ctx.symbol_tables.contains_key(dep) {
        return true;
    }

    // Phases 1–3: validity check + meta decode + `.o`-exists gate. `None` on any
    // miss → caller returns `false`.
    let (cached, source_hash, needs_inmem_load) = match cache_validity_check(ctx, dep, dep_file) {
        Some(t) => t,
        None => return false,
    };

    // Phase 4: extract all data BEFORE moving the symbol table (avoids clone /
    // honours the extract-before-move ordering invariant).
    let specs = extract_cached_specs(&cached);

    // Restore type info into TC (consumes `symbol_table` by value).
    install_cached_table(ctx, dep, cached);

    // Re-resolve platform fn ptrs. A failure aborts the cache-hit (miss).
    if !reresolve_cached_platforms(ctx, dep, &specs.platforms) {
        return false;
    }

    // Phases 5–8: scheduler register + typecheck-product + record-hit +
    // cached-module insert + file_to_module.
    register_cached_with_scheduler(ctx, dep, dep_file, specs.symbols, source_hash, needs_inmem_load);

    // Phase 9: recurse on transitive imports + re-export targets.
    register_transitive_cached_imports(ctx, &specs.imports);
    // Re-export targets are transitive deps too (FIXME 0387 — prelude's
    // `(export [text.string [str]])` etc.). Walk them through the same path.
    register_transitive_cached_imports(ctx, &specs.reexport_deps);

    true
}

/// Phases 1–3 of `try_cache_hit_load`: cache-dir check, source read + hash,
/// manifest validity, meta decode, and the `.o`-exists / generic-only gate.
///
/// Returns `None` on any cache miss (the caller returns `false`); on a hit
/// returns `(cached_module, source_hash, needs_inmem_load)`.
fn cache_validity_check(
    ctx: &ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
) -> Option<(cranelisp_backend::cache::CachedModule, String, bool)> {
    use cranelisp_backend::cache;
    use cranelisp_backend::cache::manifest as cache_manifest;
    use std::collections::HashMap as StdHashMap;

    let shared = ctx.shared_state?;

    // 1. Check cache validity: read source, compute hash, check manifest.
    //    Sprint 67 Cluster B sub-fire 3: ObjectCache facade.
    let cache_dir = shared.cache.cache_dir()?;

    let dep_source = std::fs::read_to_string(dep_file).ok()?;
    let source_hash = cache_manifest::hash_source(&dep_source);

    // Check manifest (source hash only, no dep hashes yet).
    let dep_hashes: StdHashMap<ModuleFullPath, String> = StdHashMap::new();
    if !shared.cache.is_cache_valid(dep, &source_hash, &dep_hashes) {
        return None;
    }

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

    // 3. Check .o exists — UNLESS this is a generic-only module that codegens
    //    nothing (S84 Phase 4B, FIXME 0387). The `.meta.json` persists
    //    independently of the `.o` now: a module whose only defs are slot-less
    //    `Polymorphic` templates produces no codegen object (its
    //    `defined_symbols()` batch is empty), yet its schemes still cache so a
    //    downstream module can monomorphise it on cold-load. For such a module a
    //    missing `.o` is the CORRECT cached state, not a miss; we install its
    //    schemes and register it WITHOUT scheduling an `.o` load. A non-empty
    //    codegen batch with a missing `.o` is still a genuine cache miss
    //    (recompile).
    let has_codegen_targets = cached.metadata.symbol_table.defined_symbols().next().is_some();
    if !cached.has_object && has_codegen_targets {
        return None;
    }
    let needs_inmem_load = cached.has_object;

    Some((cached, source_hash, needs_inmem_load))
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
}

/// Phase 4: extract every spec the install + register + recurse phases need out
/// of the about-to-be-moved cached symbol table (extract-before-move invariant).
fn extract_cached_specs(cached: &cranelisp_backend::cache::CachedModule) -> CachedSpecs {
    use std::collections::HashSet as StdHashSet;

    let symbols: StdHashSet<Symbol> = cached.metadata.symbol_table
        .all_symbols()
        .filter_map(|(name, entry)| match entry {
            ModuleEntry::Def { .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    // Collect names of functions with GOT slots for trait impl restoration.
    // The callable slot rides on the `DefKind` variant (S83 reshape, FIXME
    // 0356/0357) — a Def with a callable slot is a got-slotted function.
    let mangled_names: Vec<String> = cached.metadata.symbol_table
        .all_symbols()
        .filter_map(|(name, entry)| match entry {
            ModuleEntry::Def { .. } if entry.callable_got_slot().is_some() => {
                Some(name.as_ref().to_string())
            }
            _ => None,
        })
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
    let platforms: Vec<PlatformSpec> =
        cached.metadata.symbol_table.platforms.clone();

    // Sprint 58 Wave 2c / Decision 37 — capture user-authored imports BEFORE
    // moving the symbol table, so we can recurse and ensure every
    // transitive dep's symbol table (and `__cranelisp_got_{M}` data symbol)
    // is installed before this dep's codegen worker tries to load its `.o`.
    let imports: Vec<ImportSpec> =
        cached.metadata.symbol_table.imports.clone();

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
        .metadata
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

    CachedSpecs { symbols, platforms, imports, reexport_deps }
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
    let concrete_table =
        cached.metadata.symbol_table.into_concrete::<crate::code::Code, ()>();
    cranelisp_typecheck::advance_next_id_past_table(ctx.next_type_id, &concrete_table);
    cranelisp_types::install_module(
        ctx.symbol_tables,
        dep.clone(),
        concrete_table,
    );
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
/// fall back to full rebuild" per `symbol-table-cache.md` §6); we abandon the
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
/// file_to_module mapping.
fn register_cached_with_scheduler(
    ctx: &ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
    symbols: std::collections::HashSet<Symbol>,
    source_hash: String,
    needs_inmem_load: bool,
) {
    let shared = match ctx.shared_state {
        Some(s) => s,
        None => return,
    };

    // 5. Register with scheduler at TypecheckDone. A generic-only module with no
    //    `.o` (FIXME 0387) registers as already-inmem-done (no codegen load to
    //    schedule); any other cached module registers normally and its `.o` is
    //    loaded by the Level-4 `JitCodegen` worker.
    if needs_inmem_load {
        ctx.scheduler.register_module_cached(dep.clone(), symbols);
    } else {
        ctx.scheduler.register_module_cached_no_object(dep.clone(), symbols);
    }

    // 6. Create typecheck product with GOT table for cached module.
    ensure_typecheck_product(ctx.typecheck_products, dep);

    // 7. Record cache hit. Sprint 67 Cluster B sub-fire 3: ObjectCache facade.
    shared.cache.record_cache_hit(dep, source_hash);

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
}

/// Walk a cached module's `imports` and ensure each transitive dep is
/// installed (cache-hit or fresh-build registration). Decision 37 §3.2:
/// the recursive register-then-recurse-on-imports flow that the cache-hit
/// branch must mirror.
///
/// For each `ImportSpec`:
/// - If the dep is already in `ctx.symbol_tables`, skip (already installed
///   via another path).
/// - If the dep file is found and cache-loadable, recurse into
///   `try_cache_hit_load` (which will recurse further on its own imports).
/// - Otherwise, register with the scheduler for fresh build — the
///   priority worker will pick it up. Source parsing is deferred to the
///   worker via `ensure_module_sexps_for_fresh_build`; we cannot block here
///   because cache-hit load is called from inside form processing of the
///   *outer* module, which is mid-typecheck and cannot also drive a
///   fresh build of a transitive dep.
pub(super) fn register_transitive_cached_imports(
    ctx: &mut ModuleCompiler,
    imports: &[ImportSpec],
) {
    for spec in imports {
        let transitive_dep = &spec.module_path;
        // §8.3.6 Null import — skip.
        if matches!(&spec.names, ImportNames::None) {
            continue;
        }
        // Synthetic compiler modules (primitives, macros, platform.*) are
        // installed by the session, not file-backed.
        let dep_str = transitive_dep.as_ref();
        if dep_str == "primitives"
            || dep_str == "macros"
            || dep_str.starts_with("platform.")
            || dep_str == "prelude"
        {
            continue;
        }
        // Already installed via another path — done.
        if ctx.symbol_tables.contains_key(transitive_dep) {
            continue;
        }
        // Resolve the dep file. If we can't find it, leave for the regular
        // import handler — it will surface the error properly.
        let Some(dep_file) =
            crate::pipeline::resolve_module_file(transitive_dep, ctx.project_root, ctx.lib_dirs)
        else {
            continue;
        };
        // Try cache-hit load first (recurses transitively itself).
        if try_cache_hit_load(ctx, transitive_dep, &dep_file) {
            continue;
        }
        // Sprint 60 Workstream E-1 — route the cache-miss branch through the
        // `register_dep` shim (worker.rs:1327), closing the 6th per-dep
        // prologue site. See `design/int/dual-path-persistence-collapse.md §8.1`.
        // The shim publishes dep_sexps BEFORE returning (Sprint 58 W6 Defect 1
        // ordering), stashes source_text for /source introspection, records the
        // source hash, and updates file_to_module. Silent-continue-on-error is
        // preserved: cache-hit transitive recursion is best-effort; if we can't
        // read/parse the dep file here, the regular import handler will surface
        // a proper error when it reaches the dep.
        let dep_file_ref = dep_file.clone();
        let dep_for_err = transitive_dep.clone();
        let dep_sexps = match register_dep(ctx, transitive_dep, &dep_file, |e| {
            CranelispError::ModuleError {
                message: format!(
                    "failed to read transitive dep '{}' from '{}': {}",
                    dep_for_err, dep_file_ref.display(), e
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(dep_file_ref.clone())),
            }
        }) {
            Ok(s) => s,
            Err(_) => continue,
        };
        // Register with scheduler — the sexps ride the dep's work packet (S78).
        // The worker loop processes this dep's typecheck and eventually marks
        // it `inmem_done`. We do NOT block here (we are inside the outer
        // module's typecheck); the outer module either already typechecked or
        // its own normal import-block chain handles its dependency on this dep.
        // `delays_other=true` matches worker-side consensus (see §8.2 rationale).
        ctx.scheduler.register_module(transitive_dep.clone(), dep_sexps, true);
    }
}
