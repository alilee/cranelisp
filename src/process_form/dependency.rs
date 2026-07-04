//! Dependency-driving + structural-handler family (S87 §1.1 extraction from
//! `process_form.rs`).
//!
//! The gap-orchestration crossing point: every function here either (a) resolves
//! a structural decl (`import`/`export`/`mod`/prelude) into a scheduler
//! `register_module`/`block_for_typecheck` edge, or (b) is its file-IO support
//! (inline-mod write/splice). `register_dep` is the shared per-dep prologue;
//! `drive_module_dep` is the single FQ-autoload drive seam; `gap_target_module`
//! maps a `ResolutionGap` to the module to load. This is the SOLE crate-crossing
//! where a `ResolutionGap` becomes a scheduler call — kept as one cohesive module
//! (do not split block/notify/drive across files; S87 §5, `src/CLAUDE.md
//! §Cluster-Atomic Orchestration`). `compile_macro_clause_*` stays a documented
//! single-impl-with-adapters elsewhere; this module owns the dep protocol.

use std::path::{Path, PathBuf};

use cranelisp_types::{
    CranelispError, ErrorLocation, ExportSpec, ImportNames, ImportSpec,
    ModuleFullPath, Sexp, Span, Symbol, Visibility,
};

use crate::worker::{ModuleCompiler, ensure_typecheck_product};

use super::cache_restore::try_cache_hit_load;

// ---------------------------------------------------------------------------
// BlockAction — import/mod handler result
// ---------------------------------------------------------------------------

/// Signals the structural-peel (Pass 0) whether to continue or that a
/// dependency was registered + blocked on.
///
/// S78: the `Block` arm no longer carries `dep_sexps` — the structural
/// handler has already parsed the dep and handed its sexps to
/// `scheduler.register_module(dep, sexps, true)` (the sexps ride the dep's
/// work packet, not a shared `module_sexps` map). The handler has also called
/// `block_for_typecheck`, recording the register-edge. The caller
/// (`process_cluster_once`) returns `ClusterOnce::Gap { dep }`.
pub(super) enum BlockAction {
    /// Continue processing the next form.
    Continue,
    /// A dependency was discovered, registered, and blocked on.
    Block {
        dep_module: ModuleFullPath,
    },
}

// ---------------------------------------------------------------------------
// Import handling (Step 5)
// ---------------------------------------------------------------------------

/// Test whether an import of `dep` from `importer` is allowed by spec
/// §8.2.3 private-submodule visibility rules.
///
/// Spec: a `(mod- name)` declaration in module P makes `P.name` private —
/// accessible only within P itself or any descendant of P. Peer modules
/// (siblings of P, the root, anything outside P's subtree) MUST NOT
/// import names from `P.name`.
///
/// Algorithm:
/// 1. Compute `parent_path` = `dep` minus its trailing component.
/// 2. If `parent_path` is not loaded, the check is deferred (returns Ok).
///    Spec §8.2.3 enforcement requires the parent's structural decls; if
///    we don't have them yet, fall through to the existing
///    register-and-block flow (which loads the parent transitively).
/// 3. Look up the trailing component in `parent_path.submodules`. If found
///    with `is_private == true`, check whether `importer` is within
///    `parent_path`'s subtree (`importer == parent_path` or
///    `importer` starts with `parent_path + "."`). If not, reject.
///
/// Returns `Ok(())` when the import is allowed, `Err(ModuleError ...)` when
/// it must be rejected. Spec citation in the error message.
pub(crate) fn check_private_submodule_import(
    ctx: &ModuleCompiler,
    importer: &ModuleFullPath,
    dep: &ModuleFullPath,
    spec_span: Span,
) -> Result<(), CranelispError> {
    // Compute parent_path: drop trailing `.component` from `dep`.
    let dep_str: &str = dep.as_ref();
    let (parent_str, trailing) = match dep_str.rsplit_once('.') {
        Some((p, t)) => (p, t),
        // No `.` in path → top-level module, no parent → no privacy
        // check at this layer (top-level modules are never private
        // submodules of anything).
        None => return Ok(()),
    };
    let parent_path = ModuleFullPath::from(parent_str);

    // If parent isn't loaded yet, we cannot consult its `submodules`.
    // Defer to the regular load flow — which will block on the parent
    // transitively. The privacy check fires on the next visit (after
    // parent has been typechecked).
    let parent_table = match ctx.symbol_tables.get(&parent_path) {
        Some(t) => t,
        None => return Ok(()),
    };

    // Look for a matching ModDecl in the parent's structural decls.
    let private_decl = parent_table
        .submodules
        .iter()
        .find(|d| d.name.as_ref() == trailing && d.visibility == Visibility::Private);
    let Some(_decl) = private_decl else {
        return Ok(());
    };

    // Subtree containment check: importer must be the parent itself
    // or a descendant.
    let importer_str: &str = importer.as_ref();
    let prefix_with_dot = format!("{parent_str}.");
    if importer_str == parent_str || importer_str.starts_with(&prefix_with_dot) {
        return Ok(());
    }

    Err(CranelispError::ModuleError {
        message: format!(
            "cannot import from private submodule '{dep}': declared private \
             by '{parent_path}' via (mod- {trailing}); importer '{importer}' \
             is not within the '{parent_path}' subtree (spec §8.2.3)"
        ),
        location: ErrorLocation::from_span_file(spec_span, None),
    })
}

/// Handle import forms: discover deps, register with scheduler, block if needed.
///
/// For each import spec:
/// - If the dependency module is already loaded in TC, register the import.
/// - Otherwise, resolve the file, parse it, register with scheduler, and block.
///
/// `block_for_typecheck` is called INSIDE this function (F1 fix).
/// The function is idempotent on resume: already-loaded specs are re-registered
/// (register_imports is idempotent), and new deps trigger blocking (F2 fix).
pub(super) fn handle_import(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: Vec<ImportSpec>,
    // §8.6.4 (FIXME 0484): reject an import over a module-local definition only
    // on the incremental REPL (Additive) path — a whole-module (Replace) load's
    // own defs and imports co-arrive (same-cluster; the local def wins).
    additive: bool,
) -> Result<BlockAction, CranelispError> {
    for spec in &specs {
        // §8.11.2 step 1 — resolve a bare submodule name current-module-relative
        // (`<module>.<name>`) BEFORE the root/lib file search, SYMMETRIC with
        // `handle_export` (the shared helper's own doc names BOTH `handle_export`
        // and `handle_import` as afflicted; only the export side was wired). Without
        // it a bare `(import [child …])` in a `(mod child)`-declaring shell resolves
        // `child` only as a ROOT module and errors "module 'child' not found". Bare
        // non-submodule names and dotted deps pass through unchanged, so no genuine
        // root/lib import regresses. NOTE: the late (registration) stage
        // `install_imports` applies the SAME relative resolution (it is called with
        // the raw spec here), mirroring `install_exports` — the two together close
        // the bare-submodule-import mirror.
        let dep_owned = resolve_current_module_relative(
            ctx.symbol_tables,
            ctx.project_root,
            ctx.lib_dirs,
            module,
            &spec.module_path,
        );
        let dep = &dep_owned;

        // §8.3.6 Null import: empty names means suppress loading entirely.
        if matches!(&spec.names, ImportNames::None) {
            continue;
        }

        // §8.2.3 — reject imports of private submodules from outside the
        // declaring parent's subtree. Done before file resolution so a
        // peer cannot trigger a load of a private module's source. The
        // check is a no-op when the parent isn't loaded yet (deferred to
        // the next visit on resume).
        check_private_submodule_import(ctx, module, dep, spec.span)?;

        // Already loaded — register the import and continue.
        //
        // Sprint 60 Wave 2 Round 4 fix (publish-vs-flag race). Before the
        // fix this fast path tested only `contains_key(dep)`. But
        // `ensure_module_exists` (called from `register_dep_for_eval` and
        // from the worker's `handle_typecheck_work_shared` at entry) inserts
        // an empty seeded `SymbolTable` into `ctx.symbol_tables` BEFORE the
        // module's Defs are populated. A REPL retry that observes
        // `contains_key=true` but pool=`TypecheckWorking`/`TypecheckBlocked`
        // would jump to `register_imports`, whose `source_table.get(name)`
        // finds no entry and raises "'name' not found in module 'dep'"
        // — the signature of the Round 4 heisenbug. Require a terminal
        // typecheck state via `scheduler.is_typechecked(dep)` so the fast
        // path only fires when `dep`'s SymbolTable is fully populated.
        if ctx.symbol_tables.contains_key(dep)
            && ctx.scheduler.is_typechecked(dep)
        {
            // Sprint 61 Wave 3 step 3e — H4 race closure (Change B).
            // Emit the reader-side trace tag immediately before
            // `register_imports` consumes `symbol_tables[dep]`. This is
            // the data-plane lookup the failing-run dump's ordering
            // analysis (§7.4) implicates as the race site — emitting
            // here (after the `is_typechecked` gate, before the lookup)
            // makes the post-fix dump show the invariant directly:
            // `RepublishFromSymbolTable user` must precede
            // `RegisterImportsLookup helper` on any successful eval.
            // See `design/int/heisenbug-race-closure.md §8.2`.
            crate::observability::record_module_event(
                crate::observability::SchedulerTraceTag::RegisterImportsLookup,
                dep.as_ref(),
            );
            crate::imports::install_imports_gated(ctx.symbol_tables, &ctx.current_module, ctx.module_aliases, std::slice::from_ref(spec), additive)?;
            continue;
        }

        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.project_root, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "module '{}' not found (imported by '{}')",
                    dep, module
                ),
                location: ErrorLocation::from_span_file(spec.span, None),
            })?;

        // Populate file_to_module mapping for file watcher (Step 14).
        if let Some(shared) = ctx.shared_state
            && let Ok(canonical) = dep_file.canonicalize() {
                shared
                    .file_to_module
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(canonical, dep.clone());
            }

        // Cache check: try to load from disk cache before parsing.
        if try_cache_hit_load(ctx, dep, &dep_file) {
            crate::imports::install_imports_gated(ctx.symbol_tables, &ctx.current_module, ctx.module_aliases, std::slice::from_ref(spec), additive)?;
            continue;
        }

        // Run the shared per-dep prologue (read source, parse, record
        // source hash, stash source text, update file_to_module, publish
        // dep_sexps). Sprint 59 Workstream A §7 Step 1/2.
        let dep_file_for_err = dep_file.clone();
        let dep_clone_for_err = dep.clone();
        let spec_span = spec.span;
        let dep_sexps = register_dep(ctx, dep, &dep_file, |e| {
            CranelispError::ModuleError {
                message: format!(
                    "cannot read module '{}' from '{}': {}",
                    dep_clone_for_err,
                    dep_file_for_err.display(),
                    e
                ),
                location: ErrorLocation::from_span_file(spec_span, Some(dep_file_for_err.clone())),
            }
        })?;

        // Register dep with scheduler (idempotent — skips if already
        // registered). The sexps ride the dep's work packet (S78).
        ctx.scheduler.register_module(dep.clone(), dep_sexps, true);

        // Record the dependency edge (F1: called inside handle_import).
        // Pool path blocks + requeues; eval path records a cycle-check edge only
        // (S93 Invariant SW — the entry module is never moved to
        // TypecheckBlocked).
        block_dep(ctx, module, dep)?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
        });
    }

    Ok(BlockAction::Continue)
}

/// Whether `dep` is fully loaded (typechecked) and therefore ready to satisfy
/// an FQ reference without a load.
///
/// Mirrors the `handle_import` fast-path gate (Sprint 60 Wave 2 Round 4): a
/// seeded-but-empty `SymbolTable` may exist in `symbol_tables` before a
/// module's Defs are populated, so a `contains_key` check alone is not
/// sufficient. Require a terminal typecheck state via `is_typechecked`.
pub(super) fn fq_module_is_loaded(ctx: &ModuleCompiler, dep: &ModuleFullPath) -> bool {
    ctx.symbol_tables.contains_key(dep) && ctx.scheduler.is_typechecked(dep)
}

/// Drive a dependency module to readiness — the register-edge half of the
/// in-call-stack gap protocol (S78; FIXME 0268 for the FQ-auto-load case).
///
/// Resolves the module file with the **same rules as `import`** (no new search
/// semantics), parses it, registers it with the scheduler (sexps ride the dep's
/// work packet), and records the M→dep edge via `block_for_typecheck` (which
/// runs the acyclicity check FIRST, so a transitive cycle back to `module` is
/// rejected with the standard error before any wait — OQ-2). It does NOT wait:
/// the caller (`process_cluster_once`'s caller — the worker wrapper or the eval
/// wrapper) drives the wait + retry-from-top after this returns and the cluster
/// surfaces `ClusterOnce::Gap`.
///
/// For an already-loaded dep (peer import, prior retry, or cache hit) there is
/// no future `notify_typecheck_done(dep)` sweep, so we block-then-immediately-
/// unblock to re-queue the referencing module.
///
/// Macro-vs-fn discrimination is orchestrator-owned and implicit in the retry:
/// once `dep` is typechecked-and-compiled, the cluster re-runs — an FQ function
/// reference resolves against `dep`'s now-live signatures; an FQ macro
/// reference re-expands and the recogniser's on-demand clause compile finds the
/// clause code already JIT'd by `dep`'s own Pass-2 codegen. No speculative
/// function JIT push.
/// Record the `module → dep` typecheck dependency edge (S93, Invariant SW —
/// the single seam that decides pool-block vs eval-cycle-edge).
///
/// **Pool path** (`ctx.eval_driven == false`): the full `block_for_typecheck` —
/// moves `module` to `TypecheckBlocked`, registers a whole-module waiter, runs
/// the acyclicity check; the scheduler requeues `module` when `dep` completes
/// (`notify_typecheck_done` → `try_unblock_locked`).
///
/// **Eval path** (`ctx.eval_driven == true`): the REPL eval thread is the sole
/// orchestrator of `module` (its entry) and waits on `dep` itself, re-running
/// the cluster from the top — so `module` MUST NOT enter `TypecheckBlocked`
/// (that would make it pool-reclaimable: the retired-`eval_owned` B1 race).
/// Records only the cycle-check edge; the eval wrapper (`register_dep_for_eval`)
/// clears it after the wait.
pub(super) fn block_dep(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    dep: &ModuleFullPath,
) -> Result<(), CranelispError> {
    if ctx.eval_driven {
        ctx.scheduler.register_dep_edge_for_cycle_check(module, dep)
    } else {
        ctx.scheduler
            .block_for_typecheck(module, dep, &Symbol::from("*"))
    }
}

pub(super) fn drive_module_dep(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    dep: &ModuleFullPath,
    span: Span,
) -> Result<(), CranelispError> {
    // Already loaded — block-then-unblock to re-queue the referencing module
    // without a file load (no future notify sweep would fire). On the eval path
    // the eval thread retries itself, so no requeue is needed and the entry is
    // never blocked (S93 Invariant SW); the dep is loaded so there is no cycle.
    if fq_module_is_loaded(ctx, dep) {
        if !ctx.eval_driven {
            ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;
            ctx.scheduler.unblock_module(module);
        }
        return Ok(());
    }

    // Resolve the file — same rules as import (no new search semantics).
    let dep_file = crate::pipeline::resolve_module_file(dep, ctx.project_root, ctx.lib_dirs)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!(
                "module '{}' referenced by '{}/...' not found (referenced by '{}')",
                dep, dep, module
            ),
            location: ErrorLocation::from_span_file(span, None),
        })?;

    // Populate file_to_module mapping for the file watcher (parity with import).
    if let Some(shared) = ctx.shared_state
        && let Ok(canonical) = dep_file.canonicalize()
    {
        shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(canonical, dep.clone());
    }

    // Cache check: try to load from disk cache before parsing (parity with
    // import). On a cache hit `dep` is registered `TypecheckDone` synchronously
    // — block-then-immediately-unblock to re-queue the referencing module.
    if try_cache_hit_load(ctx, dep, &dep_file) {
        if !ctx.eval_driven {
            ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;
            ctx.scheduler.unblock_module(module);
        }
        return Ok(());
    }

    // Read + parse dep sexps (shared per-dep prologue).
    let dep_file_for_err = dep_file.clone();
    let dep_clone_for_err = dep.clone();
    let dep_sexps = register_dep(ctx, dep, &dep_file, |e| CranelispError::ModuleError {
        message: format!(
            "cannot read module '{}' from '{}': {}",
            dep_clone_for_err,
            dep_file_for_err.display(),
            e
        ),
        location: ErrorLocation::from_span_file(span, Some(dep_file_for_err.clone())),
    })?;

    // Register dep with scheduler (sexps ride the packet) and record the edge.
    // `block_dep` runs the acyclicity check, so a transitive cycle back to
    // `module` is rejected with the standard error (pool path blocks+requeues;
    // eval path records a cycle-check edge only — S93 Invariant SW).
    ctx.scheduler.register_module(dep.clone(), dep_sexps, true);
    block_dep(ctx, module, dep)?;

    Ok(())
}

/// The module a `ResolutionGap` names as needing to be loaded, if any.
///
/// All three gap variants reduce to "load `fq.module`": `SymbolTypechecked` is
/// what typecheck produces for an FQ value/function reference to an unknown
/// module (`QualifiedModuleUnknown` → `SymbolTypechecked`); `MacroInMem` is the
/// expand-phase macro gap; `Type` is the FQ-type-reference twin. A future
/// non-exhaustive variant returns `None` (not actionable here).
pub(crate) fn gap_target_module(gap: &cranelisp_types::ResolutionGap) -> Option<ModuleFullPath> {
    use cranelisp_types::ResolutionGap;
    match gap {
        ResolutionGap::SymbolTypechecked(fq) | ResolutionGap::MacroInMem(fq) => {
            Some(fq.module.clone())
        }
        ResolutionGap::Type(fqt) => Some(fqt.module.clone()),
        _ => None,
    }
}

/// Run the per-dep prologue that every structural form handler
/// (handle_import, handle_export, handle_mod, inject_prelude_if_needed) and the
/// FQ-auto-load drive run before `scheduler.register_module`:
///
///   1. read source from dep_file
///   2. parse to sexps
///   3. record source hash in CacheState
///   4. stash source text on the typecheck product for /source
///   5. update file_to_module for the file watcher
///
/// S78 in-call-stack restructure: the prologue NO LONGER publishes to a shared
/// `module_sexps` map (that map is deleted). It returns the parsed sexps as an
/// `Arc<[Sexp]>` so the caller hands them straight to
/// `scheduler.register_module(dep, sexps, true)` — the sexps ride the dep's
/// own work packet. The publish-before-register race window (the S60–S62
/// heisenbug substrate) is gone: there is no map for a racing worker to read
/// empty.
///
/// Does NOT call `scheduler.register_module` or `block_for_typecheck` — the
/// caller does that. The caller-specific error framing (span / message
/// wording) is produced by `prologue_err`.
pub(super) fn register_dep(
    ctx: &mut ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
    prologue_err: impl FnOnce(std::io::Error) -> CranelispError,
) -> Result<std::sync::Arc<[Sexp]>, CranelispError> {
    // file_to_module mapping for the file watcher (Step 14).
    if let Some(shared) = ctx.shared_state
        && let Ok(canonical) = dep_file.canonicalize()
    {
        shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(canonical, dep.clone());
    }

    // 1. read source.
    let source = std::fs::read_to_string(dep_file).map_err(prologue_err)?;
    // 2. parse.
    let dep_sexps: std::sync::Arc<[Sexp]> =
        std::sync::Arc::from(cranelisp_frontend::parse(&source)?);

    // 2b. Module-preamble wiring (§8.16.5; design/frontend/module-preamble.md §5):
    //     capture the leading `;;` comment block from the SAME source string and
    //     write it onto this dependency module's live `SymbolTable.module_preamble`.
    //     Orthogonal to the structural-decl peel; one call + one field write.
    //     (Cache-hit deps skip this path entirely — they restore the preamble via
    //     serde, so no re-capture occurs on a cache hit.)
    crate::save::apply_module_preamble(ctx.symbol_tables, dep, &source);

    // 3. record source hash for manifest generation. Sprint 67 Cluster B
    //    sub-fire 3: ObjectCache facade.
    if let Some(shared) = ctx.shared_state {
        let hash = cranelisp_backend::cache::manifest::hash_source(&source);
        shared.cache.record_source_hash(dep, hash);
    }

    // 4. store source text for /source introspection (--repl) + make `file_path`
    //    authoritative (S102 CS-D3a, §6.2.1): the fresh dep-load path knows the
    //    module's real backing file, so record it uniformly with the
    //    cache-restore path — `regenerate_backing_file`'s private
    //    `{root}/{module}.cl` fallback stops being load-bearing when a `/mod`
    //    turn edits a fresh file-backed dep.
    if ctx.introspection.is_some() {
        ensure_typecheck_product(ctx.typecheck_products, dep);
        if let Some(mut tp) = ctx.typecheck_products.get_mut(dep) {
            tp.file_path = Some(dep_file.to_path_buf());
            tp.source_text = Some(source);
        }
    }

    crate::observability::record_module_event(
        crate::observability::SchedulerTraceTag::RegisterDepPublish,
        dep.as_ref(),
    );

    Ok(dep_sexps)
}

// ---------------------------------------------------------------------------
// Static import-closure cycle gate (S93 — signature/body pre-pass Phase-A)
//
// `design/int/signature-body-prepass.md` §3.1 / §4 / §7 step 1+4. Before any
// body typechecks, compute the cluster's STATIC import closure from the Pass-0
// `(import …)` declarations (resolvable without inference — the decls name the
// modules directly) and reject a cycle with a clean diagnostic at the import
// site. This is the D0030 mutual-import disposition: mutual imports are a
// compile-time cycle-error, NOT compiled (ratified user ruling, §4). It runs at
// the uniform `process_cluster_once` entry seam (worker + REPL), upstream of the
// form-by-form dep drive — so a 2-cycle surfaces as `circular dependency
// detected: a -> b -> a` instead of the H6/H7-era `'aa' not found in module 'a'`
// (the is_typechecked fast-path reading a half-published sibling).
// ---------------------------------------------------------------------------

/// Extract the directly-imported module paths from a module's parsed forms (its
/// Pass-0 `(import …)` declarations). Null imports (`ImportNames::None`,
/// §8.3.6 — suppress loading) contribute no edge. Returns the dep paths plus the
/// span of the first import form (for the cycle diagnostic).
fn direct_import_deps(
    sexps: &[Sexp],
    module: &ModuleFullPath,
) -> (Vec<ModuleFullPath>, Option<Span>) {
    let mut deps = Vec::new();
    let mut first_span: Option<Span> = None;
    for sexp in sexps {
        if let Ok(super::form_dispatch::FormKind::Import(specs)) =
            super::form_dispatch::classify_form(sexp, module)
        {
            for spec in specs {
                if matches!(spec.names, cranelisp_types::ImportNames::None) {
                    continue;
                }
                first_span.get_or_insert(spec.span);
                deps.push(spec.module_path.clone());
            }
        }
    }
    (deps, first_span)
}

/// Compute the static import closure rooted at `module` (topologically ordered,
/// imports-first), returning a clean `ModuleError` cycle diagnostic if the
/// declared import graph has a cycle (the D0030 disposition — mutual imports are
/// a compile-time cycle-error, NOT compiled; `signature-body-prepass.md` §4).
///
/// Returns `None` when the cluster declares no imports (no closure → fast exit).
/// The returned [`ClosureOrder`] is reused by the body-boundary signature
/// barrier (S93 Invariant PP) — so the closure walk runs ONCE per cluster, both
/// the cycle check and the barrier gate consuming it.
///
/// Side-effect free: it reads + parses each transitively-imported module's
/// source ONLY to peel its Pass-0 import decls — it does NOT register, block,
/// typecheck, or mutate any shared state. A dependency whose file cannot be
/// resolved or parsed is treated as an edge-free leaf (conservative — the gate
/// reports a cycle only when one is definitively present in the declared import
/// graph, never a false positive that would block a legitimate build).
pub(super) fn static_import_closure(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
) -> Result<Option<crate::scheduler::ClosureOrder>, CranelispError> {
    let (root_deps, first_span) = direct_import_deps(sexps, module);
    if root_deps.is_empty() {
        return Ok(None); // no imports → no closure → no cycle (fast exit).
    }

    // S93 Task-3 — per-cluster memo. The transitive walk below does an
    // `fs::read_to_string` + `parse` for every transitively-imported module, and
    // `process_cluster_once` re-enters this function at the top of EVERY pass
    // (including every retry-from-top a dependency gap triggers). Memo the
    // computed `ClosureOrder` keyed by a cheap fingerprint of the cluster's
    // DIRECT imports (the closure's root set, computed above without any IO): a
    // hit reuses the walk; a different cluster on the same module scope (a new
    // REPL form with different imports) misses on the fingerprint and recomputes.
    // The filesystem is stable across a single cluster's retry sequence, so the
    // root-set fingerprint is a sound key; `re_register_module` resets the memo
    // when a module's source changes. A cycle (Err below) is NOT memoised — it
    // aborts the cluster, so there is no retry to serve.
    let fingerprint = closure_fingerprint(&root_deps);
    if let Some(cached) = ctx.scheduler.cached_static_closure(module, fingerprint) {
        return Ok(Some(cached));
    }

    let mut edges: Vec<(ModuleFullPath, Vec<ModuleFullPath>)> = Vec::new();
    let mut visited: std::collections::HashSet<ModuleFullPath> =
        std::collections::HashSet::new();
    edges.push((module.clone(), root_deps.clone()));
    visited.insert(module.clone());

    let mut queue: std::collections::VecDeque<ModuleFullPath> =
        root_deps.into_iter().collect();
    while let Some(dep) = queue.pop_front() {
        if !visited.insert(dep.clone()) {
            continue; // already walked
        }
        // Resolve + parse the dep's source to peel ITS imports. Any failure
        // (unresolvable file, parse error) → treat as a leaf.
        let Some(dep_file) =
            crate::pipeline::resolve_module_file(&dep, ctx.project_root, ctx.lib_dirs)
        else {
            continue;
        };
        let Ok(source) = std::fs::read_to_string(&dep_file) else {
            continue;
        };
        let Ok(parsed) = cranelisp_frontend::parse(&source) else {
            continue;
        };
        let (dep_deps, _) = direct_import_deps(&parsed, &dep);
        for d in &dep_deps {
            if !visited.contains(d) {
                queue.push_back(d.clone());
            }
        }
        edges.push((dep, dep_deps));
    }

    match crate::scheduler::dependency_closure(module, &edges) {
        Ok(closure) => {
            // Memoise for this cluster's subsequent retry-from-top passes.
            ctx.scheduler
                .cache_static_closure(module, fingerprint, &closure);
            Ok(Some(closure))
        }
        Err(cycle) => Err(CranelispError::ModuleError {
            message: format!("circular dependency detected: {}", cycle.render()),
            location: ErrorLocation::from_span_file(
                first_span.unwrap_or(Span::SYNTHETIC),
                None,
            ),
        }),
    }
}

/// Cheap order-sensitive fingerprint of a cluster's DIRECT import dep paths —
/// the key for the per-cluster static-closure memo (S93 Task-3). Hashing the
/// direct-import root set (a handful of module paths) is orders of magnitude
/// cheaper than the transitive `fs::read_to_string` + `parse` walk it gates, so
/// the memo turns O(retries × closure-size) redundant IO into a single walk per
/// cluster. The order is significant (it reflects the declared import order),
/// which is fine — the same cluster re-peels its imports in the same order every
/// retry, so the fingerprint is stable across a cluster's retry sequence.
fn closure_fingerprint(root_deps: &[ModuleFullPath]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    root_deps.hash(&mut hasher);
    hasher.finish()
}

/// Gate the cluster's body (Pass-1/Pass-2) on the signature barrier (S93,
/// Invariant PP; BC §6 ruling B). Returns `Ok(Some(member))` when a static
/// closure module's signatures are not yet published (the member has not reached
/// a terminal typecheck pool) — the caller frees back to the pool (worker) or
/// waits (eval) and retries from the top; `Ok(None)` when the barrier is open and
/// the body may proceed.
///
/// **Worker path** (`ctx.eval_driven == false`): a pool worker MUST NOT park its
/// thread on the barrier. It calls the ATOMIC
/// `block_on_first_unready_closure_member` — which, under a SINGLE scheduler lock,
/// scans for the first unready member AND registers `module` as its waiter (the
/// requeue kernel), with no gap for `notify_typecheck_done(member)` to slip the
/// waiter-sweep through (the lost-wakeup Blocker fix) — and surfaces a `Gap`; the
/// scheduler requeues the body work when the member completes
/// (`notify_typecheck_done` → `try_unblock_locked`).
///
/// **Eval path** (`ctx.eval_driven == true`): the eval thread is the one genuine
/// waiter (it consumes no pool slot), so it blocks inside the scheduler on
/// `await_signature_barrier` until the whole closure is published, then proceeds
/// — no `Gap`, no requeue.
///
/// Because Pass-0 already drove every direct import to its terminal (done) state
/// — and a done import implies ITS imports were done — the barrier is, in the
/// common case, already open when the body boundary is reached; the gate is the
/// *structural* enforcement of "no body reads a sibling until the whole closure
/// is published" (§3.3), now locally verifiable in `process_cluster_once`
/// rather than only emergent from the per-dep Pass-0 convention.
pub(super) fn gate_body_on_signature_barrier(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    closure: &crate::scheduler::ClosureOrder,
) -> Result<Option<ModuleFullPath>, CranelispError> {
    // Gate on the root's FORWARD dependencies only — never on the root itself
    // nor on any ANCESTOR of the root. The root (`module`) is the cluster being
    // typechecked NOW; its own signatures are not yet registered (that is Pass-1
    // below). An ancestor is a `(mod …)` parent reached by a `super` import: the
    // submodule drive order commits the parent's signatures BEFORE driving the
    // child (`drive_submodules` runs after the parent's `finalize_cluster`), and
    // the parent is then intentionally mid-flight (blocked waiting on the child)
    // — it is NOT a forward dependency to barrier-wait on, and gating on it
    // would both false-deadlock and trip a false runtime cycle (parent ⇄ child).
    // So exclude the root and every ancestor (`module` == ancestor or starts
    // with `ancestor + "."`).
    let is_self_or_ancestor = |m: &ModuleFullPath| -> bool {
        m == module
            || module
                .as_ref()
                .strip_prefix(m.as_ref())
                .is_some_and(|rest| rest.starts_with('.'))
    };
    let deps = crate::scheduler::ClosureOrder {
        order: closure
            .order
            .iter()
            .filter(|m| !is_self_or_ancestor(m))
            .cloned()
            .collect(),
    };
    if deps.order.is_empty() {
        return Ok(None);
    }
    if ctx.eval_driven {
        // The eval thread genuinely waits — returns immediately when open.
        ctx.scheduler
            .await_signature_barrier(&deps)
            .map_err(CranelispError::from)?;
        return Ok(None);
    }
    // Pool worker: ATOMIC check-and-block (Blocker fix — single lock acquisition,
    // no lost-wakeup window). Under one scheduler lock the method scans for the
    // first unready member AND registers `module` as its waiter; there is no gap
    // for `notify_typecheck_done(member)` to slip the waiter-sweep through. On a
    // `Some(member)` the worker surfaces a `Gap` and frees back to the pool (the
    // requeue kernel re-queues it when the member completes); never parks a pool
    // thread. The former two-call `first_unready_closure_member` + `block_dep`
    // shape — a check-then-act across two lock acquisitions — is retired.
    ctx.scheduler
        .block_on_first_unready_closure_member(module, &deps)
}

/// Handle export forms: register export metadata in the typechecker.
/// Handle export forms: ensure source modules are loaded, then register re-exports.
///
/// Export forms like `(export [compare.eq [Eq = !=]])` re-export symbols from
/// the named module. The source module must be loaded in the typechecker before
/// `register_exports` can read its symbol table. If the source module isn't
/// loaded, we trigger dependency loading via the same path as `handle_import`
/// and return `BlockAction::Block`.
/// §8.11.2 step 1 — current-module-relative module resolution. A **bare**
/// (single-component) module reference inside `module` first resolves as a
/// submodule of `module` (`<module>.<dep>`, declared via `(mod dep)`) BEFORE the
/// project-root / lib-dir search-order fallthrough. Returns the effective module
/// path: the `<module>.<dep>` submodule when it is already registered OR has a
/// backing file (`<module-dir>/<dep>.cl`); the original `dep` otherwise (a genuine
/// root/lib module, or a name with no current-module-relative candidate).
///
/// This mirrors the current-module-relative resolution `imports::install_exports`
/// already applies at the LATE (re-export-registration) stage — without it the
/// EARLY (dep-load) stage in `handle_export`/`handle_import` resolves a bare
/// submodule name only as a ROOT module and errors "module 'name' not found"
/// (bare-submodule-reexport defect). Dotted `dep`s (FQ / ancestor-qualified) and a
/// root-level `module` (empty path) have no current-module-relative candidate and
/// pass through unchanged.
fn resolve_current_module_relative<V>(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, V>,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    module: &ModuleFullPath,
    dep: &ModuleFullPath,
) -> ModuleFullPath {
    // Only a bare name inside a non-root module is a current-module-relative
    // candidate; a dotted `dep` is already an explicit path.
    if dep.as_ref().contains('.') || module.as_ref().is_empty() {
        return dep.clone();
    }
    let candidate = ModuleFullPath::from(format!("{}.{}", module.as_ref(), dep.as_ref()));
    if symbol_tables.contains_key(&candidate)
        || crate::pipeline::resolve_module_file(&candidate, project_root, lib_dirs).is_some()
    {
        candidate
    } else {
        dep.clone()
    }
}

pub(super) fn handle_export(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: &[ExportSpec],
    // §8.6.4 (FIXME 0484): reject an export over a module-local definition only
    // on the incremental REPL (Additive) path — see `handle_import`.
    additive: bool,
) -> Result<BlockAction, CranelispError> {
    for spec in specs {
        // §8.11.2 step 1 — resolve a bare submodule name current-module-relative
        // (`<module>.<name>`) BEFORE the root/lib file search, symmetric with the
        // FQ path and with `install_exports`'s late-stage resolution. Without this
        // a bare `(export [child …])` in a `(mod child)`-declaring shell resolves
        // `child` only as a ROOT module and errors "module 'child' not found".
        let dep_owned = resolve_current_module_relative(
            ctx.symbol_tables,
            ctx.project_root,
            ctx.lib_dirs,
            module,
            &spec.module_path,
        );
        let dep = &dep_owned;

        // Already loaded — register the re-export and continue.
        if ctx.symbol_tables.contains_key(dep) {
            crate::imports::install_exports_gated(ctx.symbol_tables, &ctx.current_module, std::slice::from_ref(spec), additive)?;
            continue;
        }

        // Source module not loaded — need to load it first.
        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.project_root, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "module '{}' not found (re-exported by '{}')",
                    dep, module
                ),
                location: ErrorLocation::from_span_file(spec.span, None),
            })?;

        // Populate file_to_module mapping for file watcher.
        if let Some(shared) = ctx.shared_state
            && let Ok(canonical) = dep_file.canonicalize() {
                shared
                    .file_to_module
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(canonical, dep.clone());
            }

        // Cache check.
        if try_cache_hit_load(ctx, dep, &dep_file) {
            continue;
        }

        // Run the shared per-dep prologue (read source, parse, record
        // source hash, stash source text, update file_to_module, publish
        // dep_sexps). Sprint 59 Workstream A §7 Step 1/2.
        let dep_file_for_err = dep_file.clone();
        let dep_clone_for_err = dep.clone();
        let spec_span = spec.span;
        let dep_sexps = register_dep(ctx, dep, &dep_file, |e| {
            CranelispError::ModuleError {
                message: format!(
                    "cannot read module '{}' from '{}': {}",
                    dep_clone_for_err, dep_file_for_err.display(), e
                ),
                location: ErrorLocation::from_span_file(spec_span, Some(dep_file_for_err.clone())),
            }
        })?;

        // Register dep with scheduler (sexps ride the packet) and record edge.
        ctx.scheduler.register_module(dep.clone(), dep_sexps, true);
        block_dep(ctx, module, dep)?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
        });
    }

    // All source modules loaded — register the re-exports.
    crate::imports::install_exports_gated(ctx.symbol_tables, &ctx.current_module, specs, additive)?;
    Ok(BlockAction::Continue)
}

/// Register the bare-short-name → full-submodule-path module alias for a
/// `(mod name)` declaration, so qualified references using the short name
/// (spec §8.2.6 / §8.5.1, e.g. `util/helper`) resolve to the loaded submodule
/// `<parent>.name`. Keyed by the bare short name so §8.6.6 longest-prefix
/// substitution (`substitute_module_alias`) matches the `module_part` of a
/// bare qualified reference. `Visibility::Private` — the alias serves the
/// declaring module's own qualified lookups (peers reference a submodule by
/// its full path or import it). Idempotent: re-declaration overwrites with the
/// same target (DashMap insert).
fn register_submodule_alias(
    ctx: &ModuleCompiler,
    name: &cranelisp_types::ModuleName,
    sub_path: &ModuleFullPath,
    span: Span,
) {
    ctx.module_aliases.insert(
        ModuleFullPath::from(name.as_ref()),
        cranelisp_types::ModuleAliasEntry::new(
            sub_path.clone(),
            Visibility::Private,
            span,
        ),
    );
}

/// Handle mod forms: write inline body to disk, then load the submodule.
///
/// `(mod util)` declares a submodule whose symbols are accessible via qualified
/// references like `util/helper`. The submodule must be loaded (typechecked)
/// before the parent can resolve these references, so we block for it — same
/// as `handle_import` does for explicit imports.
pub(super) fn handle_mod(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<BlockAction, CranelispError> {
    if let Some(body_sexps) = &decl.inline_body {
        // Step 1 (§8.2.2): write the inline body to the submodule backing file.
        // Always required — the submodule loads from this child `.cl` regardless
        // of whether the parent keeps the inline body (REPL) or is rewritten to
        // a bare reference (batch). The backing file is resolved LIB-DIR-relative
        // (next to the PARENT module's own on-disk file), NEVER CWD-relative —
        // FIXME 0423.
        write_inline_mod_to_disk(
            module,
            &decl.name,
            body_sexps,
            ctx.project_root,
            ctx.lib_dirs,
        )?;
        // Step 2 (§8.2.2, FIXME 0217): rewrite the PARENT source file, replacing
        // the inline `(mod name form…)` form with a bare `(mod name)` reference,
        // then drop `inline_body` from the in-memory ModDecl so the persistent
        // symbol-table shape matches a manually-created submodule (the §8.2.2
        // "indistinguishable" + "one-time creation syntax" invariants).
        //
        // REPL-mode preservation (FIXME 0343): in REPL mode the parent file is
        // the user's editable, regenerated-from-state backing file. Extracting
        // its inline `(mod …)` body to a bare reference (then having
        // `regenerate_backing_file` rewrite the parent from the table, which
        // cannot reproduce the CHILD's defns) silently DROPS the submodule body
        // from the parent on disk — a data-corruption defect. So the extraction
        // rewrite fires ONLY in batch mode (`--run`/`--link`, introspection
        // None); in REPL mode the parent keeps the inline body verbatim (the
        // child `.cl` from step 1 makes the submodule loadable; regeneration is
        // role-gated off for submodule-bearing parents, see `save::should_*`).
        // Failures to locate/rewrite the parent file are non-fatal — step 1
        // already created the backing file, so loading proceeds; the rewrite is
        // durable-shape cleanup, not a correctness gate for this run.
        if ctx.introspection.is_none() {
            rewrite_parent_inline_mod(ctx, module, decl);
        }
    }

    // Compute submodule path: "main" + "util" → "main.util"
    let sub_path = ModuleFullPath::from(format!("{}.{}", module, decl.name));

    // Register a module-path alias so the short submodule name is usable as a
    // qualified reference (spec §8.2.6 / §8.5.1 — `(mod util)` makes
    // `util/helper` resolve to the loaded submodule `<parent>.util`). The
    // loaded module's identity is its full path (§8.1); without this alias a
    // bare `util/...` qualified ref hits `QualifiedModuleUnknown` because no
    // module literally named `util` exists. Keyed by the bare short name so
    // `substitute_module_alias` (§8.6.6 longest-prefix) matches the
    // `module_part` of a bare qualified reference. Idempotent across re-entry
    // (e.g. cache-hit / already-loaded paths below).
    register_submodule_alias(ctx, &decl.name, &sub_path, decl.span);

    // FIXME 0342 — DEFER the submodule register+typecheck-block. During Pass 0
    // the PARENT's own definitions are not yet registered/committed to live, so
    // a submodule that imports a parent symbol via `(import [super [helper]])`
    // would typecheck BEFORE `helper` exists and fail "'helper' not found in
    // module '<parent>'" (a non-cyclic child→parent `super` import, conforming
    // per spec §8.3.8). Pass 0 therefore does ONLY the lightweight,
    // ordering-independent work (inline-body write above + alias) and returns
    // `Continue`; the submodule is driven (resolved + registered + blocked on)
    // AFTER `finalize_cluster` commits the parent's symbols — see
    // `drive_submodules`. Idempotent on the cluster's retry-from-top: already
    // loaded submodules are skipped by `drive_submodule`'s contains-key gate.
    Ok(BlockAction::Continue)
}

/// Drive a single declared submodule to typecheck readiness (register + block),
/// AFTER the parent cluster has committed its own symbols (FIXME 0342). Returns
/// `Continue` when the submodule is already loaded / cache-hit (no block) or
/// `Block { dep_module }` when the caller must surface a `Gap` and retry the
/// cluster from the top once the submodule is live.
///
/// This is the deferred second half of the former `handle_mod` body — the
/// file-resolution + `register_dep` + `register_module` + `block_for_typecheck`
/// sequence, moved out of Pass 0 so the parent's definitions are live (and thus
/// visible to a `super` import) before the submodule typechecks.
fn drive_submodule(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<BlockAction, CranelispError> {
    let sub_path = ModuleFullPath::from(format!("{}.{}", module, decl.name));

    // Already loaded — resolution chain handles qualified references.
    if ctx.symbol_tables.contains_key(&sub_path) {
        return Ok(BlockAction::Continue);
    }

    // Resolve file path.
    let dep_file = crate::pipeline::resolve_module_file(&sub_path, ctx.project_root, ctx.lib_dirs)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!(
                "submodule '{}' not found (declared by '{}')",
                sub_path, module
            ),
            location: ErrorLocation::from_span_file(decl.span, None),
        })?;

    // Populate file_to_module mapping for file watcher.
    if let Some(shared) = ctx.shared_state
        && let Ok(canonical) = dep_file.canonicalize() {
            shared
                .file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, sub_path.clone());
        }

    // Cache check: try to load from disk cache before parsing.
    if try_cache_hit_load(ctx, &sub_path, &dep_file) {
        return Ok(BlockAction::Continue);
    }

    // Run the shared per-dep prologue (read source, parse, record source
    // hash, stash source text, update file_to_module, publish dep_sexps).
    // Sprint 59 Workstream A §7 Step 1/2.
    let dep_file_for_err = dep_file.clone();
    let sub_path_for_err = sub_path.clone();
    let decl_span = decl.span;
    let dep_sexps = register_dep(ctx, &sub_path, &dep_file, |e| {
        CranelispError::ModuleError {
            message: format!(
                "cannot read submodule '{}' from '{}': {}",
                sub_path_for_err,
                dep_file_for_err.display(),
                e
            ),
            location: ErrorLocation::from_span_file(decl_span, Some(dep_file_for_err.clone())),
        }
    })?;

    // Register dep with scheduler (sexps ride the packet) and record edge.
    ctx.scheduler.register_module(sub_path.clone(), dep_sexps, true);
    block_dep(ctx, module, &sub_path)?;

    Ok(BlockAction::Block {
        dep_module: sub_path,
    })
}

/// Drive all of `module`'s declared submodules to typecheck readiness AFTER the
/// parent cluster has committed its symbols (FIXME 0342). Returns the first
/// submodule that needed loading (so the caller surfaces a `Gap` and retries the
/// cluster from the top); `None` when every submodule is already live. The
/// cluster's retry-from-top makes this drain one submodule per pass — idempotent
/// (`drive_submodule` skips already-loaded ones).
pub(super) fn drive_submodules(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
) -> Result<Option<ModuleFullPath>, CranelispError> {
    // Snapshot the decls — `drive_submodule` borrows `ctx` mutably (registers
    // modules), so we cannot hold a `submodules` borrow across the call.
    let decls: Vec<cranelisp_types::ModDecl> = match ctx.symbol_tables.get(module) {
        Some(st) => st.submodules.clone(),
        None => return Ok(None),
    };
    for decl in &decls {
        if let BlockAction::Block { dep_module } = drive_submodule(ctx, module, decl)? {
            return Ok(Some(dep_module));
        }
    }
    Ok(None)
}

/// Write an inline mod body to disk as `{parent_dir}/{stem}/{name}.cl`
/// (§8.2.2 extraction step / §8.2.5 nested-child path).
///
/// FIXME 0423 — the backing file MUST be resolved against the **parent
/// module's own on-disk directory** (the lib-dir for a lib-dir module), NEVER
/// the process CWD. The old code joined `project_root` (the CWD for a
/// run-from-elsewhere invocation) to the dotted module path, producing stray
/// `<cwd>/<module>/<name>.cl` trees outside the lib-dir. We instead locate the
/// parent module's real file via the same `resolve_module_file` rules the
/// loader uses (project-root, then lib-dirs) and write the backing file next to
/// it — `<parent_file_dir>/<stem>/<name>.cl`. If the parent file cannot be
/// located (it should always exist — it is what declared this `(mod …)`), we
/// fall back to the `project_root`-relative path so the run is not blocked.
///
/// If an extraction-stable backing file already exists at the target path, we
/// PREFER recognizing it (no re-emit) — the hand-authored / previously-extracted
/// copy is canonical (FIXME 0423 resolution point 2).
pub(crate) fn write_inline_mod_to_disk(
    parent_module: &ModuleFullPath,
    name: &cranelisp_types::ModuleName,
    body_sexps: &[Sexp],
    project_root: &Path,
    lib_dirs: &[PathBuf],
) -> Result<(), CranelispError> {
    // Resolve the backing-file directory against the PARENT module's own
    // on-disk location (lib-dir-relative, FIXME 0423), not the process CWD.
    let mod_dir = match crate::pipeline::resolve_module_file(
        parent_module,
        project_root,
        lib_dirs,
    ) {
        // Parent file found (e.g. `lib/accum.cl`): backing dir is the parent's
        // own directory joined with the parent's stem — `lib/accum/`.
        Some(parent_file) => {
            let parent_dir = parent_file
                .parent()
                .map(Path::to_path_buf)
                .unwrap_or_else(|| project_root.to_path_buf());
            let stem = parent_module
                .as_ref()
                .rsplit('.')
                .next()
                .unwrap_or(parent_module.as_ref());
            parent_dir.join(stem)
        }
        // Fallback (parent file not yet on disk — should not happen for a
        // module that declared this inline `(mod …)`): project-root-relative.
        None => project_root.join(parent_module.as_ref().replace('.', "/")),
    };
    let file_path = mod_dir.join(format!("{}.cl", name));

    // Prefer recognizing an existing extraction-stable backing file over
    // re-emitting it (FIXME 0423 point 2): the canonical copy already on disk
    // is read, not rewritten.
    if file_path.is_file() {
        return Ok(());
    }

    // Create directory if needed.
    std::fs::create_dir_all(&mod_dir).map_err(|e| CranelispError::ModuleError {
        message: format!(
            "cannot create directory for inline mod '{}': {}",
            file_path.display(),
            e
        ),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(file_path.clone())),
    })?;

    // Write body sexps as source text.
    let source: String = body_sexps
        .iter()
        .map(|s| format!("{}", s))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(&file_path, &source).map_err(|e| CranelispError::ModuleError {
        message: format!(
            "cannot write inline mod '{}': {}",
            file_path.display(),
            e
        ),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(file_path)),
    })?;

    Ok(())
}

/// Spec §8.2.2 step 2 (FIXME 0217): rewrite the parent source file, replacing
/// the inline `(mod name form…)` form with a bare `(mod name)` reference, and
/// drop `inline_body` from the in-memory `ModDecl` so the persistent
/// symbol-table shape is indistinguishable from a manually-created submodule
/// (the "one-time creation syntax" semantic).
///
/// Best-effort: the parent backing file is located with the same rules as
/// module loading; if it cannot be resolved/read/parsed-back, the rewrite is
/// skipped (step 1 already produced the backing file, so loading is unaffected).
/// `decl.span` is the full `(mod …)` `Sexp::List` span (byte offsets into the
/// parent source), so the replacement is a single byte-range splice that
/// preserves all surrounding whitespace and comments.
fn rewrite_parent_inline_mod(
    ctx: &ModuleCompiler,
    parent_module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) {
    // Drop `inline_body` from the in-memory ModDecl regardless of whether the
    // file rewrite succeeds — the data-shape symptom (a persistent inline_body)
    // is the load-bearing half; a manually-created submodule's ModDecl carries
    // no body.
    if let Some(mut st) = ctx.symbol_tables.get_mut(parent_module) {
        for sm in st.submodules.iter_mut() {
            if sm.name == decl.name {
                sm.inline_body = None;
            }
        }
    }

    let Some(parent_file) =
        crate::pipeline::resolve_module_file(parent_module, ctx.project_root, ctx.lib_dirs)
    else {
        return;
    };
    let Ok(source) = std::fs::read_to_string(&parent_file) else {
        return;
    };

    // The pure splice decides whether (and how) to rewrite; `None` means
    // "leave the file untouched" (no inline `(mod name …)` form present —
    // the idempotence / already-extracted case). Only write when the content
    // actually changes. The splice is SELF-LOCATING: it re-parses the CURRENT
    // on-disk content and finds the live inline form by name, so it cannot be
    // mis-targeted by a stale `decl.span` carried over from the original parse
    // (FIXME 0336 — the cluster retry-from-top re-runs Pass-0 against the
    // original `sexps`, whose span no longer addresses the already-rewritten
    // file).
    if let Some(rewritten) = splice_inline_mod_to_bare(&source, decl.name.as_ref()) {
        // Atomic-ish write (best-effort; a failure leaves step 1's backing file
        // in place and the in-memory body already dropped, so the run is
        // unaffected).
        let _ = std::fs::write(&parent_file, rewritten);
    }
}

/// Pure parent-file rewrite (spec §8.2.2 step 2): splice the inline
/// `(mod name form…)` form down to a bare `(mod name)` reference, preserving
/// all surrounding whitespace and comments.
///
/// **Self-locating (FIXME 0336):** the form to splice is located by re-parsing
/// the CURRENT `source` and finding the live top-level inline `(mod <name> …)`
/// form (head symbol `mod`/`mod-`, the named submodule, and at least one body
/// form). The byte range comes from THAT parse — never from a caller-supplied
/// span. This is correct-by-construction against the double-invocation defect:
/// the S78 cluster retry-from-top re-runs Pass-0 against the *original* `sexps`
/// (whose `decl.span` addresses the pre-rewrite 96-byte file), but by the second
/// call the on-disk file is already the rewritten 77-byte bare form — a splice
/// keyed on the stale span would slice the wrong range and truncate `main`.
/// Re-locating in the current content makes the second call a natural no-op: an
/// already-extracted `(mod name)` (no inline body) is not matched, so `None` is
/// returned and the file is left untouched.
///
/// Returns `Some(new_source)` when a live inline form is found and rewritten,
/// `None` when the file MUST be left untouched:
/// - no top-level inline `(mod <name> …)` form is present (already extracted /
///   bare reference — the idempotence case, including the stale-span retry);
/// - the source does not parse (best-effort — the rewrite is durable-shape
///   cleanup, not a correctness gate).
///
/// Extracted as the pure owner of the transformation so the parent-rewrite
/// logic is unit-testable without an FS harness or a `ModuleCompiler` (mirrors
/// the `layout_hash_gate` extraction; `src/CLAUDE.md` testability discipline).
pub(crate) fn splice_inline_mod_to_bare(source: &str, name: &str) -> Option<String> {
    // Re-parse the CURRENT content and locate the live inline `(mod <name> …)`
    // form. A parse failure (corrupt / mid-edit file) is a no-op — best-effort.
    let sexps = cranelisp_frontend::parse(source).ok()?;
    let span = find_inline_mod_span(&sexps, name)?;

    let start = span.start as usize;
    let end = span.end as usize;
    // The span comes from the current parse, so it is in-range and on char
    // boundaries by construction; guard defensively regardless.
    if start >= end
        || end > source.len()
        || !source.is_char_boundary(start)
        || !source.is_char_boundary(end)
    {
        return None;
    }
    let replacement = format!("(mod {name})");
    // An inline form (matched by `find_inline_mod_span`, body present) is never
    // already-bare, but keep the guard so a no-op stays a no-op.
    if &source[start..end] == replacement {
        return None;
    }
    let mut rewritten = String::with_capacity(source.len());
    rewritten.push_str(&source[..start]);
    rewritten.push_str(&replacement);
    rewritten.push_str(&source[end..]);
    Some(rewritten)
}

/// Locate a top-level inline `(mod <name> body…)` / `(mod- <name> body…)` form
/// in a parsed sexp stream, returning its full byte span.
///
/// A form qualifies only when it has the `mod`/`mod-` head, the named submodule
/// as the first argument, AND at least one body form (≥ 3 children) — a bare
/// `(mod name)` (exactly 2 children) is NOT an inline form and is skipped, which
/// is what makes the rewrite idempotent on an already-extracted file. Returns
/// the span of the FIRST matching form (multiple inline mods of the same name in
/// one file would be a duplicate-submodule error caught elsewhere; the first is
/// the one whose body was just written to disk).
fn find_inline_mod_span(sexps: &[Sexp], name: &str) -> Option<Span> {
    for sexp in sexps {
        let Sexp::List(children, span) = sexp else {
            continue;
        };
        if children.len() < 3 {
            continue;
        }
        let Sexp::Symbol(head, _) = &children[0] else {
            continue;
        };
        if head != "mod" && head != "mod-" {
            continue;
        }
        let Sexp::Symbol(sub_name, _) = &children[1] else {
            continue;
        };
        if sub_name == name {
            return Some(*span);
        }
    }
    None
}

/// Inject prelude import for non-prelude modules, blocking if prelude needs loading.
///
/// Per spec §8.8.1: the implicit `(import [prelude [*]])` is suppressed when the
/// module's source contains an explicit `(import [prelude ...])` or
/// `(export [prelude ...])`. This allows modules to control their prelude
/// relationship — specific imports, null import (§8.3.6), or re-export.
///
/// Returns `Some(dep_module)` (the prelude path) if the prelude was registered
/// + blocked on and the cluster must retry once it is live; `None` if prelude
/// is already loaded, not found, or suppressed (S78 in-call-stack shape).
pub(super) fn inject_prelude_if_needed(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
) -> Result<Option<ModuleFullPath>, CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");
    if *module == prelude_path {
        return Ok(None);
    }

    // §8.8.1: explicit import/export of prelude suppresses the implicit glob.
    if sexps_reference_prelude(sexps) {
        return Ok(None);
    }

    // S78 §2.7 — prelude is an OUTER SCOPE, not flattened into this module's
    // table. We are on the ON path (the module neither IS `prelude` nor
    // references it), so record the per-module fallback bit ON: bare-name
    // inner-table misses in this module fall back to prelude's own table
    // (chain-following its `(export [primitives [*]])` re-exports). The bit
    // is set unconditionally here — every code path below merely ensures
    // prelude is LOADED (so the fallback has a table to consult); none of
    // them flatten prelude's symbols into this module anymore.
    ctx.prelude_fallback.insert(module.clone(), true);

    if !ctx.symbol_tables.contains_key(&prelude_path) {
        // Discover prelude through the same lazy path as any user import.
        let prelude_file = crate::session_setup::resolve_prelude(
            ctx.project_root,
            ctx.lib_dirs,
        );
        if let Some(prelude_file) = prelude_file {
            // Cache check: load prelude from disk cache (so the fallback has a
            // table to consult). No flatten — the bit was set above.
            if try_cache_hit_load(ctx, &prelude_path, &prelude_file) {
                return Ok(None);
            }

            // Run the shared per-dep prologue (read source, parse, record
            // source hash, stash source text, update file_to_module). The
            // sexps ride the prelude's work packet (S78).
            let prelude_file_for_err = prelude_file.clone();
            let prelude_sexps = register_dep(ctx, &prelude_path, &prelude_file, |e| {
                CranelispError::ModuleError {
                    message: format!(
                        "cannot read prelude '{}': {}",
                        prelude_file_for_err.display(),
                        e
                    ),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(prelude_file_for_err.clone())),
                }
            })?;

            ctx.scheduler.register_module(prelude_path.clone(), prelude_sexps, true);
            block_dep(ctx, module, &prelude_path)?;

            return Ok(Some(prelude_path));
        }
        // No prelude file found. Per spec §8.9.1: primitives are NOT
        // available as bare names without explicit import or prelude. The
        // fallback bit set above is harmless — with no `prelude` table to
        // consult, a bare-name fallback probe simply misses (modules that
        // need primitives must have a prelude that re-exports them or import
        // explicitly).
    } else {
        // Prelude already loaded — nothing to flatten; the bit set above
        // makes the fallback consult prelude's own table on a bare-name miss.
    }

    Ok(None)
}

/// Check whether a module's source sexps contain an explicit reference to
/// `prelude` in an import or export form (spec §8.8.1).
pub(super) fn sexps_reference_prelude(sexps: &[Sexp]) -> bool {
    for sexp in sexps {
        let Sexp::List(items, _) = sexp else { continue };
        if items.len() < 2 { continue; }
        let Sexp::Symbol(head, _) = &items[0] else { continue };
        if head.as_str() != "import" && head.as_str() != "export" {
            continue;
        }
        // Check each import/export spec for a module path of "prelude".
        // Import/export specs use brackets: (import [module [names...]])
        // The inner spec is Sexp::Bracket, not Sexp::List.
        for spec_sexp in &items[1..] {
            let spec_items = match spec_sexp {
                Sexp::Bracket(items, _) => items,
                Sexp::List(items, _) => items,
                _ => continue,
            };
            if spec_items.is_empty() { continue; }
            let module_name = match &spec_items[0] {
                Sexp::Symbol(name, _) => Some(name.as_str()),
                // Aliased form: [(module alias) [...]] or ((module alias) [...])
                Sexp::Bracket(alias_items, _) | Sexp::List(alias_items, _)
                    if !alias_items.is_empty() =>
                {
                    match &alias_items[0] {
                        Sexp::Symbol(name, _) => Some(name.as_str()),
                        _ => None,
                    }
                }
                _ => None,
            };
            if module_name == Some("prelude") {
                return true;
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// FIXME 0423 — `(mod …)` extraction write path is lib-dir-relative, not CWD.
// The source fix landed S88 (commit 5833bd1); this is the owed `/dev`
// acceptance unit test (design/int/session-persistence.md §10.3).
// spec: 08-modules.md §8.2.2
// ---------------------------------------------------------------------------
#[cfg(test)]
mod current_module_relative_tests {
    use super::*;

    // spec: spec/08-modules.md §8.11.2 (step 1 — submodule of current module) —
    // a bare name matching a REGISTERED `<module>.<name>` submodule resolves
    // current-module-relative (the `(mod child)` load ran before the export/import).
    #[test]
    fn bare_name_resolves_to_registered_submodule() {
        let tables: dashmap::DashMap<ModuleFullPath, ()> = dashmap::DashMap::new();
        tables.insert(ModuleFullPath::from("shell.child"), ());
        let td = tempfile::tempdir().unwrap();
        let got = resolve_current_module_relative(
            &tables,
            td.path(),
            &[],
            &ModuleFullPath::from("shell"),
            &ModuleFullPath::from("child"),
        );
        assert_eq!(
            got,
            ModuleFullPath::from("shell.child"),
            "a bare `child` inside `shell` with a registered `shell.child` submodule \
             must resolve current-module-relative (§8.11.2 step 1)"
        );
    }

    // spec: spec/08-modules.md §8.11.2 (step 1) — a bare name with a backing file
    // `<module-dir>/<name>.cl` resolves current-module-relative even before the
    // submodule is registered (the `(mod child)` load has not run yet).
    #[test]
    fn bare_name_resolves_to_file_backed_submodule() {
        let tables: dashmap::DashMap<ModuleFullPath, ()> = dashmap::DashMap::new();
        let td = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(td.path().join("shell")).unwrap();
        std::fs::write(td.path().join("shell/child.cl"), "(defn foo [x] x)\n").unwrap();
        let got = resolve_current_module_relative(
            &tables,
            td.path(),
            &[],
            &ModuleFullPath::from("shell"),
            &ModuleFullPath::from("child"),
        );
        assert_eq!(got, ModuleFullPath::from("shell.child"));
    }

    // spec: spec/08-modules.md §8.11.2 — NEGATIVE: a bare name with NO
    // current-module-relative candidate (neither registered nor file-backed) passes
    // through unchanged, so the root/lib search-order fallthrough still resolves a
    // genuine root module.
    #[test]
    fn bare_name_without_candidate_passes_through() {
        let tables: dashmap::DashMap<ModuleFullPath, ()> = dashmap::DashMap::new();
        let td = tempfile::tempdir().unwrap();
        let got = resolve_current_module_relative(
            &tables,
            td.path(),
            &[],
            &ModuleFullPath::from("shell"),
            &ModuleFullPath::from("other"),
        );
        assert_eq!(
            got,
            ModuleFullPath::from("other"),
            "a bare name with no submodule candidate must pass through to the \
             root/lib search-order fallthrough"
        );
    }

    // spec: spec/08-modules.md §8.11.2 — NEGATIVE: a DOTTED (FQ / ancestor-qualified)
    // dep is already an explicit path and is never re-rooted current-module-relative
    // (no double-prefixing `shell.a.b`).
    #[test]
    fn dotted_dep_passes_through_unchanged() {
        let tables: dashmap::DashMap<ModuleFullPath, ()> = dashmap::DashMap::new();
        tables.insert(ModuleFullPath::from("shell.a.b"), ());
        let td = tempfile::tempdir().unwrap();
        let got = resolve_current_module_relative(
            &tables,
            td.path(),
            &[],
            &ModuleFullPath::from("shell"),
            &ModuleFullPath::from("a.b"),
        );
        assert_eq!(got, ModuleFullPath::from("a.b"), "a dotted dep is explicit — unchanged");
    }
}

#[cfg(test)]
mod inline_mod_write_tests {
    use super::*;
    use cranelisp_types::ModuleName;

    fn body() -> Vec<Sexp> {
        // A trivial body sexp: `(defn helper [] 1)` is not needed — any sexp
        // round-trips through Display; use a single symbol for simplicity.
        vec![Sexp::Symbol("placeholder".to_string(), Span::SYNTHETIC)]
    }

    // The backing file lands beside the PARENT module's on-disk file (under the
    // lib dir), and NO stray file is created under project_root (the CWD-relative
    // regression guard).
    #[test]
    fn writes_relative_to_lib_dir_parent_not_cwd() {
        // lib dir holds the parent module `accum` → lib/accum.cl.
        let lib_td = tempfile::tempdir().unwrap();
        let lib_dir = lib_td.path().to_path_buf();
        std::fs::write(lib_dir.join("accum.cl"), "(defn seed [] 0)\n").unwrap();

        // project_root is a DIFFERENT tmpdir (the CWD analogue).
        let proj_td = tempfile::tempdir().unwrap();
        let project_root = proj_td.path();

        let parent = ModuleFullPath::from("accum");
        let name = ModuleName::from("test");
        write_inline_mod_to_disk(&parent, &name, &body(), project_root, std::slice::from_ref(&lib_dir))
            .expect("write_inline_mod_to_disk");

        // (a) backing file beside the parent, under the lib dir.
        let expected = lib_dir.join("accum").join("test.cl");
        assert!(
            expected.is_file(),
            "backing file must land at {{lib_dir}}/accum/test.cl; not found at {}",
            expected.display()
        );

        // (b) NO stray file under project_root (the CWD-relative bug guard).
        let stray = project_root.join("accum").join("test.cl");
        assert!(
            !stray.exists(),
            "no stray file may be created under project_root; found {}",
            stray.display()
        );
        assert!(
            !project_root.join("accum").exists(),
            "no stray accum/ tree may be created under project_root"
        );
    }

    // Recognize-existing: an extraction-stable backing file already on disk is a
    // no-op (Ok(())) and is left byte-identical (not rewritten). FIXME 0423 pt 2.
    #[test]
    fn recognizes_existing_backing_file_no_op() {
        let lib_td = tempfile::tempdir().unwrap();
        let lib_dir = lib_td.path().to_path_buf();
        std::fs::write(lib_dir.join("accum.cl"), "(defn seed [] 0)\n").unwrap();

        // Pre-create an extraction-stable backing file with canonical content.
        let mod_dir = lib_dir.join("accum");
        std::fs::create_dir_all(&mod_dir).unwrap();
        let backing = mod_dir.join("test.cl");
        let canonical = "(defn canonical [] 42)\n";
        std::fs::write(&backing, canonical).unwrap();

        let proj_td = tempfile::tempdir().unwrap();
        let parent = ModuleFullPath::from("accum");
        let name = ModuleName::from("test");
        write_inline_mod_to_disk(&parent, &name, &body(), proj_td.path(), std::slice::from_ref(&lib_dir))
            .expect("no-op write");

        let after = std::fs::read_to_string(&backing).unwrap();
        assert_eq!(
            after, canonical,
            "an existing extraction-stable backing file must be left byte-identical"
        );
    }
}
