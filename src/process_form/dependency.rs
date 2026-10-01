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

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CranelispError, ErrorLocation, ExportSpec, ImportNames, ImportSpec, ModuleFullPath, Sexp, Span,
    Symbol, Visibility,
};

use crate::imports::DeclaredChildren;
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
    Block { dep_module: ModuleFullPath },
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
///
/// Each spec is resolved once against the cluster's `declared` children
/// (`design/int/int.md` §6.9); that module feeds the privacy check, the fast
/// path, the load and installation.
pub(super) fn handle_import(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: Vec<ImportSpec>,
    declared: &DeclaredChildren,
) -> Result<BlockAction, CranelispError> {
    for spec in &specs {
        let resolved = declared.resolve_import(spec);
        let dep = resolved.module();

        // A name-less import loads nothing (§8.3.7); an alias-only one still
        // registers its alias (§8.3.6), and a qualified reference through it
        // auto-loads the target (§8.5.4).
        if matches!(&spec.names, ImportNames::None) {
            crate::imports::install_import_alias(
                &ctx.current_module,
                ctx.module_aliases,
                &resolved,
            );
            continue;
        }

        // §8.2.3 — reject imports of private submodules from outside the
        // declaring parent's subtree. Done before file resolution so a
        // peer cannot trigger a load of a private module's source. The
        // check is a no-op when the parent isn't loaded yet (deferred to
        // the next visit on resume).
        check_private_submodule_import(ctx, module, dep, spec.span)?;
        refuse_failed_table(ctx, module, dep, spec.span)?;

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
        if ctx.symbol_tables.contains_key(dep) && ctx.scheduler.is_typechecked(dep) {
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
            crate::imports::install_imports(
                ctx.symbol_tables,
                &ctx.current_module,
                ctx.module_aliases,
                ctx.prelude_fallback,
                std::slice::from_ref(&resolved),
            )?;
            continue;
        }

        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.project_root, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!("module '{}' not found (imported by '{}')", dep, module),
                location: ErrorLocation::from_span_file(spec.span, None),
            })?;

        // Populate file_to_module mapping for file watcher (Step 14).
        if let Some(shared) = ctx.shared_state
            && let Ok(canonical) = dep_file.canonicalize()
        {
            shared
                .file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, dep.clone());
        }

        // Cache check: try to load from disk cache before parsing.
        if try_cache_hit_load(ctx, dep, &dep_file)? {
            crate::imports::install_imports(
                ctx.symbol_tables,
                &ctx.current_module,
                ctx.module_aliases,
                ctx.prelude_fallback,
                std::slice::from_ref(&resolved),
            )?;
            continue;
        }

        // Run the shared per-dep prologue (read source, parse, record
        // source hash, stash source text, update file_to_module, publish
        // dep_sexps). Sprint 59 Workstream A §7 Step 1/2.
        let dep_file_for_err = dep_file.clone();
        let dep_clone_for_err = dep.clone();
        let spec_span = spec.span;
        let dep_sexps = register_dep(ctx, Some(module), dep, &dep_file, |e| {
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
        block_dep(ctx, module, dep, spec_span)?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
        });
    }

    Ok(BlockAction::Continue)
}

/// Pass 0's fail-fast on a declared module that has a table and stands
/// `Failed` (`design/int/int.md` §6.11): the attempt fails with that module's
/// error, and no name resolves against its failed table. A failed module with
/// no table takes the load path instead: its wait fails fast with the same
/// error or, on the eval path, retries after the purge.
fn refuse_failed_table(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    dep: &ModuleFullPath,
    span: Span,
) -> Result<(), CranelispError> {
    if ctx.symbol_tables.contains_key(dep) {
        ctx.scheduler.refuse_failed_dependency(module, dep, span)?;
    }
    Ok(())
}

/// Whether `dep` is fully loaded (typechecked) and therefore ready to satisfy
/// an FQ reference without a load.
///
/// Mirrors the `handle_import` fast-path gate (Sprint 60 Wave 2 Round 4): a
/// seeded-but-empty `SymbolTable` may exist in `symbol_tables` before a
/// module's Defs are populated, so a `contains_key` check alone is not
/// sufficient. Require a terminal typecheck state via `is_typechecked`.
///
/// **"Loaded/terminal" requires EVER-terminal, not merely present-with-symbols
/// (I1, 0571.2 + 0571.3).** `is_typechecked` answers `true` for EVERY module the
/// scheduler does not track (its doc: "not in the scheduler — synthetic OR
/// removed via Failed reset"), so it cannot tell a genuinely-loaded module from
/// one that FAILED to load. A failed dep is left with an import-seeded table —
/// `(import [primitives [Int]])` writes the `Int` alias into the LIVE table
/// *before* the body-check failure — so a "present-with-symbols" test also reads
/// it "loaded" and reports the §8.5.4 edge-4/5 false "module X has no member Y"
/// on an autoload RETRY (0571.2 fixed the empty-table case, 0571.3 the
/// import-seeded case). We therefore split on scheduler registration: a tracked
/// module trusts its terminal-pool verdict (covers a genuinely-loaded EMPTY
/// `.cl` file); an UNTRACKED module is loaded only if it EVER reached terminal
/// (`was_ever_terminal` — a was-good module the scheduler later forgot, monotone
/// across reset) OR is a compiler-seeded synthetic module (`primitives`/`macros`
/// — mounted at bootstrap, fully populated, never scheduler-tracked). A
/// never-terminal failed/import-seeded dep is neither → not loaded → re-drives.
pub(super) fn fq_module_is_loaded(ctx: &ModuleCompiler, dep: &ModuleFullPath) -> bool {
    if !ctx.symbol_tables.contains_key(dep) {
        return false;
    }
    if ctx.scheduler.is_registered(dep) {
        return ctx.scheduler.is_typechecked(dep);
    }
    ctx.scheduler.was_ever_terminal(dep)
        || crate::bootstrap::seeded_importable_modules().contains(dep)
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
    ref_span: Span,
) -> Result<(), CranelispError> {
    if ctx.eval_driven {
        ctx.scheduler
            .register_dep_edge_for_cycle_check(module, dep, ref_span)
    } else {
        ctx.scheduler
            .block_for_typecheck(module, dep, &Symbol::from("*"), ref_span)
    }
}

pub(crate) fn drive_module_dep(
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
            ctx.scheduler
                .block_for_typecheck(module, dep, &Symbol::from("*"), span)?;
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
    if try_cache_hit_load(ctx, dep, &dep_file)? {
        if !ctx.eval_driven {
            ctx.scheduler
                .block_for_typecheck(module, dep, &Symbol::from("*"), span)?;
            ctx.scheduler.unblock_module(module);
        }
        return Ok(());
    }

    // Read + parse dep sexps (shared per-dep prologue).
    let dep_file_for_err = dep_file.clone();
    let dep_clone_for_err = dep.clone();
    let dep_sexps = register_dep(ctx, Some(module), dep, &dep_file, |e| {
        CranelispError::ModuleError {
            message: format!(
                "cannot read module '{}' from '{}': {}",
                dep_clone_for_err,
                dep_file_for_err.display(),
                e
            ),
            location: ErrorLocation::from_span_file(span, Some(dep_file_for_err.clone())),
        }
    })?;

    // Register dep with scheduler (sexps ride the packet) and record the edge.
    // `block_dep` runs the acyclicity check, so a transitive cycle back to
    // `module` is rejected with the standard error (pool path blocks+requeues;
    // eval path records a cycle-check edge only — S93 Invariant SW).
    ctx.scheduler.register_module(dep.clone(), dep_sexps, true);
    block_dep(ctx, module, dep, span)?;

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

/// The referenced member NAME a gap names (the symbol / type after the `/`) —
/// for the reference-site span lookup and the honest "module X has no member Y"
/// diagnostic (0571 AL-3). Empty for a non-member gap shape.
pub(crate) fn gap_member(gap: &cranelisp_types::ResolutionGap) -> String {
    use cranelisp_types::ResolutionGap;
    match gap {
        ResolutionGap::SymbolTypechecked(fq) | ResolutionGap::MacroInMem(fq) => {
            fq.symbol.to_string()
        }
        ResolutionGap::Type(fqt) => fqt.name.to_string(),
        _ => String::new(),
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
    loader: Option<&ModuleFullPath>,
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

    // 1. read source, 2. parse. A failure is the dependency's own, located in
    //    its file: it is recorded `Failed`, and the loader is refused by it
    //    (`design/int/repl-lifecycle.md` §1.3.1, A dependency that fails
    //    before it registers).
    let text = std::fs::read_to_string(dep_file);
    if let Some(shared) = ctx.shared_state
        && let Some(state) = crate::watch::FileState::of_read(&text)
    {
        shared.record_source(dep_file, state);
    }
    let read = text.map_err(prologue_err).and_then(|source| {
        let parsed = cranelisp_frontend::parse(&source)?;
        Ok((source, parsed))
    });
    let (source, dep_sexps): (String, std::sync::Arc<[Sexp]>) = match read {
        Ok((source, parsed)) => (source, std::sync::Arc::from(parsed)),
        Err(error) => return Err(fail_before_registration(ctx, loader, dep, dep_file, error)),
    };

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

    // 4. record the module's backing file in every mode, as cache restore does
    //    (S102 CS-D3a, §6.2.1): regeneration and the test runner's
    //    project/library classifier read it (`design/int/test-runner.md`
    //    §4.1). The source text is REPL-only, for /source introspection.
    ensure_typecheck_product(ctx.typecheck_products, dep);
    if let Some(mut tp) = ctx.typecheck_products.get_mut(dep) {
        tp.file_path = Some(dep_file.to_path_buf());
        if ctx.introspection.is_some() {
            tp.source_text = Some(source);
        }
    }

    crate::observability::record_module_event(
        crate::observability::SchedulerTraceTag::RegisterDepPublish,
        dep.as_ref(),
    );

    Ok(dep_sexps)
}

/// Record `dep`'s read or parse failure as its failed generation, located in
/// `dep_file`, and refuse `loader` by it (`design/int/repl-lifecycle.md`
/// §1.3.1, A dependency that fails before it registers). A parse error keeps
/// its own span, an offset in `dep_file`; a read error has no position there,
/// so it sits at the file's start and never carries the loader's import span.
/// Returns the loader's refusal, which wraps the error once, else the error.
fn fail_before_registration(
    ctx: &ModuleCompiler,
    loader: Option<&ModuleFullPath>,
    dep: &ModuleFullPath,
    dep_file: &Path,
    error: CranelispError,
) -> CranelispError {
    let located = |span: Span| ErrorLocation::from_span_file(span, Some(dep_file.to_path_buf()));
    let recorded = match error {
        CranelispError::ParseError { message, location } => CranelispError::ParseError {
            message,
            location: located(location.span),
        },
        read => CranelispError::ModuleError {
            message: read.message().to_string(),
            location: located(Span::new(0, 0)),
        },
    };
    let unrefused = match &recorded {
        CranelispError::ParseError { message, location } => CranelispError::ParseError {
            message: message.clone(),
            location: location.clone(),
        },
        other => CranelispError::ModuleError {
            message: other.message().to_string(),
            location: other.location().clone(),
        },
    };
    ctx.scheduler.fail_generation(dep, recorded);
    match loader {
        Some(loader) => ctx
            .scheduler
            .refuse_failed_dependency(loader, dep, Span::SYNTHETIC)
            .err()
            .unwrap_or(unrefused),
        None => unrefused,
    }
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

/// The `(mod …)` and `(mod- …)` declarations among `module`'s forms. A form
/// that fails to classify declares nothing here; Pass 0 reports it.
fn mod_declarations(sexps: &[Sexp], module: &ModuleFullPath) -> Vec<cranelisp_types::ModDecl> {
    sexps
        .iter()
        .filter_map(
            |sexp| match super::form_dispatch::classify_form(sexp, module) {
                Ok(super::form_dispatch::FormKind::Mod(decl)) => Some(decl),
                _ => None,
            },
        )
        .collect()
}

/// The `import` specs among `module`'s forms, including null imports. A form
/// that fails to classify declares nothing here; Pass 0 reports it.
fn import_declarations(sexps: &[Sexp], module: &ModuleFullPath) -> Vec<ImportSpec> {
    sexps
        .iter()
        .filter_map(
            |sexp| match super::form_dispatch::classify_form(sexp, module) {
                Ok(super::form_dispatch::FormKind::Import(specs)) => Some(specs),
                _ => None,
            },
        )
        .flatten()
        .collect()
}

/// The children a cluster of `module` may name in its `import` and `export`
/// specs: the cluster's own `mod` forms together with the declarations earlier
/// turns recorded on the module's table (`design/int/int.md` §6.9). Computed
/// once per pass, before the static closure and Pass 0, so an `import` written
/// before its `(mod …)` resolves as it does after it.
pub(super) fn cluster_declared_children(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
) -> DeclaredChildren {
    let mut declarations = mod_declarations(sexps, module);
    if let Some(table) = ctx.symbol_tables.get(module) {
        declarations.extend(table.submodules.iter().cloned());
    }
    DeclaredChildren::of(module, &declarations)
}

/// Which declarations of a module's forms a walk reads as dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeclaredEdges {
    /// `import` declarations that load: the static gate's walk, whose closure
    /// is also the signature barrier's members.
    Imports,
    /// `import` declarations that load and every `export` target: a failed
    /// attempt's dependencies and the prelude-reach walk
    /// (`design/int/repl-lifecycle.md` §1.2.1, `design/int/int.md` §6.12).
    ImportsAndExports,
}

/// The modules `module`'s `sexps` depend on through their declarations, each
/// resolved against `declared`, with the span of the first such declaration
/// (for a cycle diagnostic). A null import (`ImportNames::None`, spec §8.3.7)
/// loads nothing and is no edge.
fn declared_dependencies(
    sexps: &[Sexp],
    module: &ModuleFullPath,
    declared: &DeclaredChildren,
    edges: DeclaredEdges,
) -> (Vec<ModuleFullPath>, Option<Span>) {
    let mut deps = Vec::new();
    let mut first_span: Option<Span> = None;
    for sexp in sexps {
        match super::form_dispatch::classify_form(sexp, module) {
            Ok(super::form_dispatch::FormKind::Import(specs)) => {
                for spec in specs {
                    if matches!(spec.names, ImportNames::None) {
                        continue;
                    }
                    first_span.get_or_insert(spec.span);
                    deps.push(declared.resolve(&spec.module_path));
                }
            }
            Ok(super::form_dispatch::FormKind::Export(specs))
                if edges == DeclaredEdges::ImportsAndExports =>
            {
                for spec in specs {
                    first_span.get_or_insert(spec.span);
                    deps.push(declared.resolve(&spec.module_path));
                }
            }
            _ => {}
        }
    }
    (deps, first_span)
}

fn prelude_module() -> ModuleFullPath {
    ModuleFullPath::from(crate::expander::PRELUDE_MODULE)
}

/// The implicit prelude dependency of `module`'s source `sexps` (spec §8.8.1;
/// `design/int/int.md` §6.12): the prelude, unless `module` is the prelude,
/// its source names the prelude in an `import` or `export`, or there is no
/// prelude file to depend on.
fn source_prelude_edge(
    module: &ModuleFullPath,
    sexps: &[Sexp],
    prelude_file_exists: bool,
) -> Option<ModuleFullPath> {
    let prelude = prelude_module();
    (prelude_file_exists && *module != prelude && !sexps_reference_prelude(sexps))
        .then_some(prelude)
}

/// The parsed source of `module`'s file. `None` when the file cannot be
/// resolved, read or parsed; every file walk treats such a module as a leaf.
fn parse_module_file(ctx: &ModuleCompiler, module: &ModuleFullPath) -> Option<Vec<Sexp>> {
    let file = crate::pipeline::resolve_module_file(module, ctx.project_root, ctx.lib_dirs)?;
    let source = std::fs::read_to_string(file).ok()?;
    cranelisp_frontend::parse(&source).ok()
}

/// Compute the static import closure rooted at `module` (topologically ordered,
/// imports-first), returning a clean `ModuleError` cycle diagnostic if the
/// declared dependency graph has a cycle (the D0030 disposition — mutual imports
/// are a compile-time cycle-error, NOT compiled; `signature-body-prepass.md` §4).
///
/// The graph is each walked module's `import` declarations that load plus its
/// implicit prelude dependency (`design/int/int.md` §6.12): the root's follows
/// the fallback bit this attempt set, and each walked file's follows the spec
/// §8.8.1 predicate over that file. The returned [`ClosureOrder`], which the
/// body-boundary signature barrier (S93 Invariant PP) waits on, is the closure
/// over written imports alone: a declared child of a module the prelude
/// depends on keeps the implicit import, so a barrier wait on the prelude could
/// deadlock the parent that waits for that child.
///
/// Returns `None` when the cluster has no dependency to walk (fast exit).
///
/// Side-effect free apart from the failure-dependency record of a cycle: it
/// reads + parses each walked module's source ONLY to peel its declarations —
/// it does NOT register, block, typecheck, or mutate any other shared state. A
/// dependency whose file cannot be resolved or parsed is an edge-free leaf, so
/// the gate reports a cycle only when one is definitively present.
///
/// The root's imports resolve against the cluster's `declared` children; each
/// walked module's imports resolve against the `mod` forms of its own file.
pub(super) fn static_import_closure(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    declared: &DeclaredChildren,
) -> Result<Option<crate::scheduler::ClosureOrder>, CranelispError> {
    let (root_imports, first_span) =
        declared_dependencies(sexps, module, declared, DeclaredEdges::Imports);
    let prelude_file_exists =
        crate::session_setup::resolve_prelude(ctx.project_root, ctx.lib_dirs).is_some();
    let root_prelude = (prelude_file_exists
        && ctx.prelude_fallback.get(module).is_some_and(|bit| *bit))
    .then(prelude_module);
    if root_imports.is_empty() && root_prelude.is_none() {
        return Ok(None); // nothing to walk → no closure → no cycle (fast exit).
    }

    // S93 Task-3 — per-cluster memo. The transitive walk below reads and
    // parses every walked module's file, and `process_cluster_once` re-enters
    // this function at the top of EVERY pass (including every retry-from-top a
    // dependency gap triggers). The memo is keyed by a cheap fingerprint of the
    // root's direct dependencies; the filesystem is stable across a single
    // cluster's retry sequence, and `re_register_module` resets the memo when
    // a module's source changes. A cycle (Err below) is NOT memoised — it
    // aborts the cluster, so there is no retry to serve.
    let fingerprint = closure_fingerprint(&root_imports, root_prelude.is_some());
    if let Some(cached) = ctx.scheduler.cached_static_closure(module, fingerprint) {
        return Ok(Some(cached));
    }

    let mut imports: Vec<(ModuleFullPath, Vec<ModuleFullPath>)> =
        vec![(module.clone(), root_imports.clone())];
    let mut dependencies: Vec<(ModuleFullPath, Vec<ModuleFullPath>)> = vec![(
        module.clone(),
        root_imports.iter().cloned().chain(root_prelude).collect(),
    )];
    let mut visited: std::collections::HashSet<ModuleFullPath> =
        std::collections::HashSet::from([module.clone()]);
    let mut queue: std::collections::VecDeque<ModuleFullPath> =
        dependencies[0].1.iter().cloned().collect();
    while let Some(dep) = queue.pop_front() {
        if !visited.insert(dep.clone()) {
            continue; // already walked
        }
        let Some(parsed) = parse_module_file(ctx, &dep) else {
            continue;
        };
        let dep_declared = DeclaredChildren::of(&dep, &mod_declarations(&parsed, &dep));
        let (dep_imports, _) =
            declared_dependencies(&parsed, &dep, &dep_declared, DeclaredEdges::Imports);
        let dep_dependencies: Vec<ModuleFullPath> = dep_imports
            .iter()
            .cloned()
            .chain(source_prelude_edge(&dep, &parsed, prelude_file_exists))
            .collect();
        queue.extend(
            dep_dependencies
                .iter()
                .filter(|d| !visited.contains(*d))
                .cloned(),
        );
        imports.push((dep.clone(), dep_imports));
        dependencies.push((dep, dep_dependencies));
    }

    let closure = crate::scheduler::dependency_closure(module, &dependencies)
        .and_then(|_| crate::scheduler::dependency_closure(module, &imports));
    match closure {
        Ok(closure) => {
            // Memoise for this cluster's subsequent retry-from-top passes.
            ctx.scheduler
                .cache_static_closure(module, fingerprint, &closure);
            Ok(Some(closure))
        }
        Err(cycle) => {
            // The next module on the cycle, or the cycle's first module when
            // `module` only reaches it (`design/int/repl-lifecycle.md` §1.2.1).
            let reached = cycle
                .cycle
                .iter()
                .position(|member| member == module)
                .and_then(|at| cycle.cycle.get(at + 1))
                .or_else(|| cycle.cycle.first());
            if let Some(reached) = reached {
                ctx.scheduler
                    .record_failure_dependencies(module, [reached.clone()]);
            }
            ctx.scheduler.record_cycle_failure(module);
            Err(CranelispError::ModuleError {
                message: format!("circular dependency detected: {}", cycle.render()),
                location: ErrorLocation::from_span_file(
                    first_span.unwrap_or(Span::SYNTHETIC),
                    None,
                ),
            })
        }
    }
}

/// Cheap fingerprint of a cluster's direct dependencies — the key for the
/// per-cluster static-closure memo (S93 Task-3). Hashing the direct imports
/// and the prelude edge is orders of magnitude cheaper than the transitive
/// file walk it gates. The import order is significant, which is fine — the
/// same cluster re-peels its imports in the same order every retry.
fn closure_fingerprint(root_imports: &[ModuleFullPath], prelude_edge: bool) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    root_imports.hash(&mut hasher);
    prelude_edge.hash(&mut hasher);
    hasher.finish()
}

// ---------------------------------------------------------------------------
// A failed whole-source attempt (design/int/repl-lifecycle.md §1.2.1;
// design/int/int.md §6.12)
// ---------------------------------------------------------------------------

/// The module qualifier of every qualified symbol written in `forms` outside
/// reader-quoted data, before alias substitution. A type annotation's
/// qualifier counts. Quoted data is shielded as the expander shields it,
/// through the one quote classifier `cranelisp_types::quote_head`: a `quote`
/// subject is data, and inside a `quasiquote` only an `unquote` at the
/// template's own depth is live.
fn written_qualifiers<'a>(forms: impl IntoIterator<Item = &'a Sexp>) -> BTreeSet<ModuleFullPath> {
    fn walk(node: &Sexp, quasiquote_depth: usize, out: &mut BTreeSet<ModuleFullPath>) {
        match node {
            Sexp::Symbol(name, _) if quasiquote_depth == 0 => {
                let written = name.strip_prefix(':').unwrap_or(name);
                if let Some((qualifier, member)) = written.split_once('/')
                    && !qualifier.is_empty()
                    && !member.is_empty()
                {
                    out.insert(ModuleFullPath::from(qualifier));
                }
            }
            Sexp::List(children, _) => match cranelisp_types::quote_head(children) {
                Some(cranelisp_types::QuoteHead::Quote) => {}
                Some(cranelisp_types::QuoteHead::Quasiquote) => {
                    walk(&children[1], quasiquote_depth + 1, out)
                }
                Some(
                    cranelisp_types::QuoteHead::Unquote
                    | cranelisp_types::QuoteHead::UnquoteSplicing,
                ) => walk(&children[1], quasiquote_depth.saturating_sub(1), out),
                None => children
                    .iter()
                    .for_each(|child| walk(child, quasiquote_depth, out)),
            },
            Sexp::Bracket(children, _) => children
                .iter()
                .for_each(|child| walk(child, quasiquote_depth, out)),
            Sexp::Annotated {
                annotation,
                subject,
                ..
            } => {
                walk(annotation, quasiquote_depth, out);
                walk(subject, quasiquote_depth, out);
            }
            _ => {}
        }
    }
    let mut out = BTreeSet::new();
    for form in forms {
        walk(form, 0, &mut out);
    }
    out
}

/// The modules `module`'s written qualified symbols in `forms` name, each
/// substituted through `aliases` as qualified auto-loading substitutes it.
fn qualified_modules<'a>(
    aliases: &cranelisp_types::ModuleAliases,
    module: &ModuleFullPath,
    forms: impl IntoIterator<Item = &'a Sexp>,
) -> BTreeSet<ModuleFullPath> {
    written_qualifiers(forms)
        .iter()
        .map(|qualifier| cranelisp_types::substitute_module_alias(aliases, module, qualifier))
        .collect()
}

/// The dependencies of one failed whole-source attempt of `module`
/// (`design/int/repl-lifecycle.md` §1.2.1): the declarations in its forms, the
/// prelude when its bit is on, its live table's reload edges, the modules its
/// qualified symbols name in its forms and in what it expanded, and its
/// accumulated macro heads. The union over-approximates, which selection
/// tolerates.
pub(super) fn attempt_dependencies(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    forms: &[Sexp],
    expanded: &[Sexp],
    macro_heads: &BTreeSet<ModuleFullPath>,
) -> BTreeSet<ModuleFullPath> {
    let fallback = ctx.prelude_fallback.get(module).is_some_and(|bit| *bit);
    let declared = cluster_declared_children(ctx, module, forms);
    let (declarations, _) =
        declared_dependencies(forms, module, &declared, DeclaredEdges::ImportsAndExports);
    let mut dependencies: BTreeSet<ModuleFullPath> = declarations.into_iter().collect();
    if fallback {
        dependencies.insert(prelude_module());
    }
    if let Some(table) = ctx.symbol_tables.get(module) {
        dependencies.extend(crate::cache::dependency_record::reload_edges(
            module, &table, fallback,
        ));
    }
    dependencies.extend(qualified_modules(
        ctx.module_aliases,
        module,
        forms.iter().chain(expanded),
    ));
    dependencies.extend(macro_heads.iter().cloned());
    dependencies.retain(|dependency| {
        dependency != module && !crate::cache::dependency_record::is_compiler_owned(dependency)
    });
    dependencies
}

/// The cycle `module -> prelude -> … -> module` when the prelude's source
/// reaches `module` (`design/int/int.md` §6.12, cycle precedence). The walk
/// starts at the prelude's file and follows each walked file's `import`
/// declarations that load, its `export` targets and its written qualified
/// symbols; it follows no prelude edge and no declared child. `None` when the
/// prelude does not reach `module`.
///
/// A walked file's qualifiers are substituted through the aliases that file
/// declares, not the session carrier, which the walked module's Pass 0 may not
/// yet have written. Every alias the session writes is private to its
/// declaring module, so those are all the aliases the file's qualifiers can
/// read; a writable public module alias would falsify this.
pub(super) fn prelude_reach_cycle(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
) -> Option<crate::scheduler::CycleError> {
    let prelude = prelude_module();
    let aliases = cranelisp_types::ModuleAliases::default();
    let mut reached_from: std::collections::HashMap<ModuleFullPath, ModuleFullPath> =
        std::collections::HashMap::new();
    let mut queue = std::collections::VecDeque::from([prelude.clone()]);
    while let Some(visiting) = queue.pop_front() {
        let Some(parsed) = parse_module_file(ctx, &visiting) else {
            continue;
        };
        let submodules = mod_declarations(&parsed, &visiting);
        crate::imports::install_declared_aliases(
            &visiting,
            &aliases,
            &import_declarations(&parsed, &visiting),
            &submodules,
        );
        let declared = DeclaredChildren::of(&visiting, &submodules);
        let (declarations, _) = declared_dependencies(
            &parsed,
            &visiting,
            &declared,
            DeclaredEdges::ImportsAndExports,
        );
        let qualified = qualified_modules(&aliases, &visiting, &parsed);
        for next in declarations.into_iter().chain(qualified) {
            if next == prelude
                || next == visiting
                || reached_from.contains_key(&next)
                || crate::cache::dependency_record::is_compiler_owned(&next)
            {
                continue;
            }
            reached_from.insert(next.clone(), visiting.clone());
            if next == *module {
                let mut path = vec![module.clone()];
                while let Some(previous) = reached_from.get(path.last()?) {
                    path.push(previous.clone());
                }
                path.push(module.clone());
                path.reverse();
                return Some(crate::scheduler::CycleError { cycle: path });
            }
            queue.push_back(next);
        }
    }
    None
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

/// Handle export forms: ensure source modules are loaded, then register re-exports.
///
/// Export forms like `(export [compare.eq [Eq = !=]])` re-export symbols from
/// the named module. The source module must be loaded in the typechecker before
/// `register_exports` can read its symbol table. If the source module isn't
/// loaded, we trigger dependency loading via the same path as `handle_import`
/// and return `BlockAction::Block`.
///
/// Each spec is resolved once against the cluster's `declared` children
/// (`design/int/int.md` §6.9); that module feeds the load and installation.
pub(super) fn handle_export(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: &[ExportSpec],
    declared: &DeclaredChildren,
) -> Result<BlockAction, CranelispError> {
    let resolved_specs: Vec<_> = specs
        .iter()
        .map(|spec| declared.resolve_export(spec))
        .collect();
    for resolved in &resolved_specs {
        let spec = resolved.spec();
        let dep = resolved.module();
        refuse_failed_table(ctx, module, dep, spec.span)?;

        // Already loaded — register the re-export and continue.
        if ctx.symbol_tables.contains_key(dep) {
            crate::imports::install_exports(
                ctx.symbol_tables,
                &ctx.current_module,
                ctx.prelude_fallback,
                ctx.shared_state.map(|s| &s.declared_exports),
                std::slice::from_ref(resolved),
            )?;
            continue;
        }

        // Source module not loaded — need to load it first.
        // Resolve file path.
        let dep_file = crate::pipeline::resolve_module_file(dep, ctx.project_root, ctx.lib_dirs)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!("module '{}' not found (re-exported by '{}')", dep, module),
                location: ErrorLocation::from_span_file(spec.span, None),
            })?;

        // Populate file_to_module mapping for file watcher.
        if let Some(shared) = ctx.shared_state
            && let Ok(canonical) = dep_file.canonicalize()
        {
            shared
                .file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, dep.clone());
        }

        // Cache check.
        if try_cache_hit_load(ctx, dep, &dep_file)? {
            continue;
        }

        // Run the shared per-dep prologue (read source, parse, record
        // source hash, stash source text, update file_to_module, publish
        // dep_sexps). Sprint 59 Workstream A §7 Step 1/2.
        let dep_file_for_err = dep_file.clone();
        let dep_clone_for_err = dep.clone();
        let spec_span = spec.span;
        let dep_sexps = register_dep(ctx, Some(module), dep, &dep_file, |e| {
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

        // Register dep with scheduler (sexps ride the packet) and record edge.
        ctx.scheduler.register_module(dep.clone(), dep_sexps, true);
        block_dep(ctx, module, dep, spec_span)?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
        });
    }

    // All source modules loaded — register the re-exports. Record `D(M)` from
    // these specs into the session-side map (FIXME 0604 §2.2) for the live commit
    // gate; the background index path uses its own isolated call with `None`.
    crate::imports::install_exports(
        ctx.symbol_tables,
        &ctx.current_module,
        ctx.prelude_fallback,
        ctx.shared_state.map(|s| &s.declared_exports),
        &resolved_specs,
    )?;
    Ok(BlockAction::Continue)
}

/// Register the module-scoped short-name → full-submodule-path alias for a
/// `(mod name)` declaration, so qualified references using the short name
/// (spec §8.2.6 / §8.5.1, e.g. `util/helper`) resolve to the loaded submodule
/// `<parent>.name`. The key includes the declaring module, preventing another
/// module's same-spelled submodule alias from replacing it; alias substitution
/// supplies that scope while matching the qualified reference's module part.
/// `Visibility::Private` — the alias serves the
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
        cranelisp_types::module_alias_key(&ctx.current_module, name.as_ref()),
        cranelisp_types::ModuleAliasEntry::new(sub_path.clone(), Visibility::Private, span),
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
    let sub_path = crate::imports::declared_child_path(module, decl.name.as_ref());

    // Register a module-path alias so the short submodule name is usable as a
    // qualified reference (spec §8.2.6 / §8.5.1 — `(mod util)` makes
    // `util/helper` resolve to the loaded submodule `<parent>.util`). The
    // loaded module's identity is its full path (§8.1); without this alias a
    // bare `util/...` qualified ref hits `QualifiedModuleUnknown` because no
    // module literally named `util` exists. The alias is scoped to this parent
    // module; `substitute_module_alias` supplies that scope before applying its
    // §8.6.6 longest-prefix match. Idempotent across re-entry (e.g. cache-hit /
    // already-loaded paths below).
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
pub(super) enum DeclaredSubmoduleEnrollment {
    Ready,
    Registered(ModuleFullPath),
}

/// The single declared-submodule enrollment mechanism shared by fresh-parent
/// and cache-restored-parent orchestration. It owns path resolution, watcher
/// mapping, child cache restoration and fresh registration; callers decide
/// whether their parent must block on a newly registered child.
pub(super) fn enrol_declared_submodule(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<DeclaredSubmoduleEnrollment, CranelispError> {
    let sub_path = crate::imports::declared_child_path(module, decl.name.as_ref());

    // Already loaded — resolution chain handles qualified references.
    if ctx.symbol_tables.contains_key(&sub_path) {
        return Ok(DeclaredSubmoduleEnrollment::Ready);
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
        && let Ok(canonical) = dep_file.canonicalize()
    {
        shared
            .file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(canonical, sub_path.clone());
    }

    // Cache check: try to load from disk cache before parsing.
    if try_cache_hit_load(ctx, &sub_path, &dep_file)? {
        return Ok(DeclaredSubmoduleEnrollment::Ready);
    }

    // Run the shared per-dep prologue (read source, parse, record source
    // hash, stash source text, update file_to_module, publish dep_sexps).
    // Sprint 59 Workstream A §7 Step 1/2.
    let dep_file_for_err = dep_file.clone();
    let sub_path_for_err = sub_path.clone();
    let decl_span = decl.span;
    let dep_sexps = register_dep(ctx, Some(module), &sub_path, &dep_file, |e| {
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
    ctx.scheduler
        .register_module(sub_path.clone(), dep_sexps, true);
    Ok(DeclaredSubmoduleEnrollment::Registered(sub_path))
}

fn drive_submodule(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<BlockAction, CranelispError> {
    match enrol_declared_submodule(ctx, module, decl)? {
        DeclaredSubmoduleEnrollment::Ready => Ok(BlockAction::Continue),
        DeclaredSubmoduleEnrollment::Registered(sub_path) => {
            block_dep(ctx, module, &sub_path, decl.span)?;
            Ok(BlockAction::Block {
                dep_module: sub_path,
            })
        }
    }
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
    let mod_dir = match crate::pipeline::resolve_module_file(parent_module, project_root, lib_dirs)
    {
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
        message: format!("cannot write inline mod '{}': {}", file_path.display(), e),
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

/// Single-source the per-module implicit-prelude fallback bit (S78 §2.7;
/// FIXME 0516 fold-in). The bit is ON iff the module is neither `prelude`
/// itself nor explicitly references prelude in an `import`/`export` form
/// (§8.8.1 — an explicit reference suppresses the implicit fallback). Both
/// arms of [`super::process_cluster_once`] call this — the ONE spot the two
/// arms write the same invariant (Principle 7); `fresh` selects the write
/// discipline:
///
/// - `fresh == true` (Replace / batch recompile): the module's table is being
///   rebuilt, so recompute from scratch. Writes the ON bit when the module
///   neither is nor references prelude; leaves the entry absent otherwise
///   (absence-is-OFF) — behaviour-identical to the former
///   `inject_prelude_if_needed` ON-path set.
/// - `fresh == false` (Additive / REPL eval): the bit was set ON at the
///   module's startup compile and module state persists across turns, so apply
///   only the incremental OFF delta — a later form that newly references
///   prelude turns the implicit fallback OFF for this module.
pub(super) fn ensure_prelude_bit(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    fresh: bool,
) {
    let prelude_path = prelude_module();
    if fresh {
        if *module != prelude_path && !sexps_reference_prelude(sexps) {
            ctx.prelude_fallback.insert(module.clone(), true);
        }
    } else if sexps_reference_prelude(sexps) {
        ctx.prelude_fallback.insert(module.clone(), false);
    }
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
    let prelude_path = prelude_module();
    if *module == prelude_path {
        return Ok(None);
    }

    // §8.8.1: explicit import/export of prelude suppresses the implicit glob.
    if sexps_reference_prelude(sexps) {
        return Ok(None);
    }

    // S78 §2.7 — prelude is an OUTER SCOPE, not flattened into this module's
    // table. The per-module fallback bit is now written by the single-source
    // `ensure_prelude_bit` (called by BOTH the Replace and Additive arms of
    // `process_cluster_once` — FIXME 0516 fold-in), NOT here. This function
    // keeps only the prelude-LOADING responsibility on the ON path: every code
    // path below ensures prelude is LOADED (so the fallback has a table to
    // consult); none flatten prelude's symbols into this module.
    if !ctx.symbol_tables.contains_key(&prelude_path) {
        // Discover prelude through the same lazy path as any user import.
        let prelude_file = crate::session_setup::resolve_prelude(ctx.project_root, ctx.lib_dirs);
        if let Some(prelude_file) = prelude_file {
            // Cache check: load prelude from disk cache (so the fallback has a
            // table to consult). No flatten — the bit was set above.
            if try_cache_hit_load(ctx, &prelude_path, &prelude_file)? {
                return Ok(None);
            }

            // Run the shared per-dep prologue (read source, parse, record
            // source hash, stash source text, update file_to_module). The
            // sexps ride the prelude's work packet (S78).
            let prelude_file_for_err = prelude_file.clone();
            let prelude_sexps =
                register_dep(ctx, Some(module), &prelude_path, &prelude_file, |e| {
                    CranelispError::ModuleError {
                        message: format!(
                            "cannot read prelude '{}': {}",
                            prelude_file_for_err.display(),
                            e
                        ),
                        location: ErrorLocation::from_span_file(
                            Span::SYNTHETIC,
                            Some(prelude_file_for_err.clone()),
                        ),
                    }
                })?;

            ctx.scheduler
                .register_module(prelude_path.clone(), prelude_sexps, true);
            block_dep(ctx, module, &prelude_path, Span::SYNTHETIC)?;

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
        // A table does not mean the prelude compiled: a failed rebuild leaves
        // a fresh one. The implicit import then refuses as an explicit one
        // does, unless the prelude reaches `module`, which puts `module` on a
        // cycle with it rather than below it (`design/int/int.md` §6.12,
        // Refusal by a failed prelude).
        if ctx.scheduler.is_failed(&prelude_path) && prelude_reach_cycle(ctx, module).is_none() {
            ctx.scheduler
                .refuse_failed_dependency(module, &prelude_path, Span::SYNTHETIC)?;
        }
    }

    Ok(None)
}

/// Check whether a module's source sexps contain an explicit reference to
/// `prelude` in an import or export form (spec §8.8.1).
pub(super) fn sexps_reference_prelude(sexps: &[Sexp]) -> bool {
    for sexp in sexps {
        let Sexp::List(items, _) = sexp else { continue };
        if items.len() < 2 {
            continue;
        }
        let Sexp::Symbol(head, _) = &items[0] else {
            continue;
        };
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
            if spec_items.is_empty() {
                continue;
            }
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

// spec: spec/08-modules.md §8.11.2 item 1, §8.11.2.1 — a bare module name in
// `import` names the current module's child only when that module declares
// `(mod name)`, wherever the declaration sits in the cluster or in an earlier
// turn; a file-backed `a/q.cl` alone does not make `q` a child.
#[cfg(test)]
mod bare_module_name_tests {
    use super::*;
    use crate::code::SessionSymbolTable;
    use crate::scheduler::CompileScheduler;
    use cranelisp_types::{ModDecl, ModuleName, ModuleStrategy};

    /// A project directory holding `files`, and the session state one cluster
    /// prologue for module `a` runs against.
    struct Project {
        dir: tempfile::TempDir,
        tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
        next_type_id: std::sync::atomic::AtomicU32,
        scheduler: CompileScheduler,
        products: dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
        aliases: cranelisp_types::ModuleAliases,
        fallback: cranelisp_typecheck::PreludeFallback,
    }

    impl Project {
        fn new(files: &[(&str, &str)]) -> Self {
            let dir = tempfile::tempdir().unwrap();
            for (path, source) in files {
                let path = dir.path().join(path);
                std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                std::fs::write(path, source).unwrap();
            }
            Project {
                dir,
                tables: dashmap::DashMap::new(),
                next_type_id: std::sync::atomic::AtomicU32::new(0),
                scheduler: CompileScheduler::new(),
                products: dashmap::DashMap::new(),
                aliases: Default::default(),
                fallback: Default::default(),
            }
        }

        /// Record `(mod name)` on `a`'s table, as an earlier turn would.
        fn record_earlier_declaration(&self, name: &str) {
            let a = ModuleFullPath::from("a");
            cranelisp_types::ensure_module_exists(&self.tables, &a);
            self.tables.get_mut(&a).unwrap().submodules.push(ModDecl {
                name: ModuleName::from(name),
                visibility: Visibility::Public,
                inline_body: None,
                span: Span::SYNTHETIC,
            });
        }

        /// The session state one cluster of `module` runs against.
        fn ctx(&self, module: &ModuleFullPath) -> ModuleCompiler<'_> {
            ModuleCompiler {
                symbol_tables: &self.tables,
                next_type_id: &self.next_type_id,
                module_aliases: &self.aliases,
                prelude_fallback: &self.fallback,
                check_state: cranelisp_typecheck::CheckState::new(module.clone()),
                current_module: module.clone(),
                scheduler: &self.scheduler,
                typecheck_products: &self.products,
                introspection: None,
                lib_dirs: &[],
                platform_dirs: &[],
                project_root: self.dir.path(),
                shared_state: None,
                eval_driven: true,
            }
        }

        /// Run `a`'s cluster prologue over `source`: `Ok(Some(dep))` names the
        /// dependency its import blocked on.
        #[allow(clippy::result_large_err)] // CranelispError is the crate-wide error carrier
        fn prologue(&self, source: &str) -> Result<Option<ModuleFullPath>, CranelispError> {
            let a = ModuleFullPath::from("a");
            let mut ctx = self.ctx(&a);
            let sexps = cranelisp_frontend::parse(source).unwrap();
            super::super::run_cluster_prologue(&mut ctx, &a, &sexps, ModuleStrategy::Additive)
        }

        /// The static import closure of `root`'s own file, with `root`'s
        /// fallback bit set as its source implies (spec §8.8.1).
        #[allow(clippy::result_large_err)] // CranelispError is the crate-wide error carrier
        fn static_closure_of(
            &self,
            root: &str,
        ) -> Result<Option<crate::scheduler::ClosureOrder>, CranelispError> {
            let root = module(root);
            let sexps = parse_module_file(&self.ctx(&root), &root).unwrap_or_default();
            if source_prelude_edge(&root, &sexps, true).is_some() {
                self.fallback.insert(root.clone(), true);
            }
            let ctx = self.ctx(&root);
            let declared = cluster_declared_children(&ctx, &root, &sexps);
            static_import_closure(&ctx, &root, &sexps, &declared)
        }

        /// The error a failed whole-source attempt of `root`'s own file
        /// reports in place of `error`, with `root`'s fallback bit set as its
        /// source implies.
        fn failed_attempt_error(&self, root: &str, error: &str) -> String {
            let root = module(root);
            let sexps = parse_module_file(&self.ctx(&root), &root).unwrap_or_default();
            if source_prelude_edge(&root, &sexps, true).is_some() {
                self.fallback.insert(root.clone(), true);
            }
            let prefix = super::super::ExpandedPrefix::resuming(
                &crate::scheduler::SourceContinuation::source(sexps.clone()),
            );
            super::super::fail_whole_source_attempt(
                &self.ctx(&root),
                &root,
                &sexps,
                &prefix,
                CranelispError::TypeError {
                    message: error.to_string(),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                },
            )
            .to_string()
        }
    }

    fn module(path: &str) -> ModuleFullPath {
        ModuleFullPath::from(path)
    }

    fn expect_missing_child(outcome: Result<Option<ModuleFullPath>, CranelispError>) {
        match outcome {
            Err(CranelispError::ModuleError { message, .. }) => assert!(
                message.contains("'a.q' not found"),
                "the error names the declared child: {message}"
            ),
            other => panic!("expected the declared child `a.q` to be missing, got {other:?}"),
        }
    }

    #[test]
    fn import_before_mod_in_one_cluster_names_the_child() {
        let source = "(import [q [g]])\n(mod q)\n";
        let with_file =
            Project::new(&[("a/q.cl", "(defn g [] 11)\n"), ("q.cl", "(defn g [] 99)\n")]);
        assert_eq!(with_file.prologue(source).unwrap(), Some(module("a.q")));
        let without_file = Project::new(&[("q.cl", "(defn g [] 99)\n")]);
        expect_missing_child(without_file.prologue(source));
    }

    #[test]
    fn declaration_recorded_by_an_earlier_turn_names_the_child() {
        let project = Project::new(&[("q.cl", "(defn g [] 99)\n")]);
        project.record_earlier_declaration("q");
        expect_missing_child(project.prologue("(import [q [g]])\n"));
    }

    #[test]
    fn undeclared_name_is_the_root_module_even_with_a_child_file() {
        let project = Project::new(&[("a/q.cl", "(defn g [] 11)\n"), ("q.cl", "(defn g [] 99)\n")]);
        assert_eq!(
            project.prologue("(import [q [g]])\n").unwrap(),
            Some(module("q"))
        );
    }

    /// Root `q.cl` imports `a`; `a/q.cl` imports nothing.
    fn root_q_importing_a() -> Project {
        Project::new(&[
            ("a/q.cl", "(defn g [] 11)\n"),
            ("q.cl", "(import [a [h]])\n(defn g [] 99)\n"),
        ])
    }

    #[test]
    fn static_closure_follows_the_declared_child_and_finds_no_cycle() {
        let outcome = root_q_importing_a().prologue("(mod q)\n(import [q [g]])\n(defn h [] (g))\n");
        assert_eq!(outcome.unwrap(), Some(module("a.q")));
    }

    #[test]
    fn static_closure_of_an_undeclared_name_reaches_the_root_cycle() {
        match root_q_importing_a().prologue("(import [q [g]])\n(defn h [] (g))\n") {
            Err(CranelispError::ModuleError { message, .. }) => assert!(
                message.contains("circular dependency detected: a -> q -> a"),
                "{message}"
            ),
            other => panic!("expected the root `q` cycle, got {other:?}"),
        }
    }

    // spec: design/int/repl-lifecycle.md §1.2.1 — the static import-closure
    // gate records the next module on the cycle the module closed.
    #[test]
    fn static_closure_cycle_records_the_next_module_as_failure_dependency() {
        let project = root_q_importing_a();
        project
            .scheduler
            .register_module(module("a"), std::sync::Arc::from(Vec::new()), false);
        assert!(
            project
                .prologue("(import [q [g]])\n(defn h [] (g))\n")
                .is_err()
        );
        assert_eq!(
            project.scheduler.failure_dependencies(&module("a")),
            BTreeSet::from([module("q")])
        );
    }

    fn cycle_message(
        outcome: Result<Option<crate::scheduler::ClosureOrder>, CranelispError>,
    ) -> String {
        match outcome {
            Err(CranelispError::ModuleError { message, .. }) => message,
            other => panic!("expected a cycle, got {other:?}"),
        }
    }

    /// A project whose prelude imports `x`, and a third module `c`; `x`
    /// carries the fallback bit unless it null-imports the prelude.
    fn prelude_importing_x(x_opted_out: bool) -> Project {
        let x = if x_opted_out {
            "(import [prelude []])\n(defn one [] 1)\n"
        } else {
            "(defn one [] 1)\n"
        };
        Project::new(&[
            ("prelude.cl", "(import [x [one]])\n"),
            ("x.cl", x),
            ("c.cl", "(defn c [] 1)\n"),
        ])
    }

    // spec: spec/08-modules.md §8.8.1, §8.10.2; design/int/int.md §6.12 — the
    // static gate walks the implicit prelude edge: from the prelude, from `x`
    // and from a third module with the bit on, the prelude importing `x`,
    // whose bit is on, is a cycle; with `x` null-importing the prelude, none.
    #[test]
    fn static_closure_walks_the_implicit_prelude_edge() {
        for (root, cycle) in [
            ("prelude", "prelude -> x -> prelude"),
            ("x", "x -> prelude -> x"),
            ("c", "prelude -> x -> prelude"),
        ] {
            let message = cycle_message(prelude_importing_x(false).static_closure_of(root));
            assert!(
                message.contains(&format!("circular dependency detected: {cycle}")),
                "{root}: {message}"
            );
            assert!(
                prelude_importing_x(true).static_closure_of(root).is_ok(),
                "{root}"
            );
        }
    }

    // spec: design/int/int.md §6.12 (The barrier does not wait on the edge) —
    // the signature barrier's members for a root with the bit on and no
    // imports exclude the prelude.
    #[test]
    fn static_closure_barrier_members_exclude_the_prelude() {
        let closure = prelude_importing_x(true).static_closure_of("c").unwrap();
        let members = closure.map(|closure| closure.order).unwrap_or_default();
        assert!(!members.contains(&module("prelude")), "{members:?}");
    }

    const X_FAILS_ON_P: &str = "(defn get [:P p] (P.n p))\n(defn one [] 3)\n";
    const P_UNKNOWN: &str = "unknown type `P`";

    // spec: spec/08-modules.md §8.5.4 item 6, §8.10.1; design/int/int.md §6.12
    // (cycle precedence) — `x`, with the bit on, failing on a prelude type
    // while the prelude reaches it through `export`, a qualified reference, or
    // another module's import, reports the cycle instead of its own error.
    #[test]
    fn failed_attempt_reached_by_the_prelude_reports_the_cycle() {
        for (prelude, extra, cycle) in [
            (
                "(export [x [one]])\n(deftype P [:Int n])\n",
                None,
                "x -> prelude -> x",
            ),
            (
                "(deftype P [:Int n])\n(defn pone [] (x/one))\n",
                None,
                "x -> prelude -> x",
            ),
            (
                "(export [a [f]])\n(deftype P [:Int n])\n",
                Some(("a.cl", "(import [x [one]])\n(defn f [] (one))\n")),
                "x -> prelude -> a -> x",
            ),
        ] {
            let mut files = vec![("prelude.cl", prelude), ("x.cl", X_FAILS_ON_P)];
            files.extend(extra);
            let message = Project::new(&files).failed_attempt_error("x", P_UNKNOWN);
            assert!(
                message.contains(&format!("circular dependency detected: {cycle}")),
                "{prelude}: {message}"
            );
        }
    }

    // spec: spec/08-modules.md §8.5.4 item 6; design/int/int.md §6.12 (Aliases
    // come from the walked file) — `a` reaches `x` only as `y/one` through its
    // own `(import [(x y) []])`; with no alias in the session carrier, as before
    // `a`'s Pass 0 runs, the walk still reports the cycle through `a`.
    #[test]
    fn failed_attempt_reached_through_a_walked_file_s_own_alias_reports_the_cycle() {
        let project = Project::new(&[
            ("prelude.cl", "(export [a [f]])\n(deftype P [:Int n])\n"),
            (
                "a.cl",
                "(import [prelude []])\n(import [(x y) []])\n(defn f [] (y/one))\n",
            ),
            ("x.cl", X_FAILS_ON_P),
        ]);
        assert!(project.aliases.is_empty(), "precondition: no session alias");
        let message = project.failed_attempt_error("x", P_UNKNOWN);
        assert!(
            message.contains("circular dependency detected: x -> prelude -> a -> x"),
            "{message}"
        );
    }

    // spec: design/int/int.md §6.12 (cycle precedence) — the precedence walk
    // over-reaches nowhere: `x` keeps its own error when it null-imports the
    // prelude, when the prelude names `x/one` only inside quoted data, and
    // when `x` is a declared child of a module the prelude exports.
    #[test]
    fn failed_attempt_not_reached_by_the_prelude_keeps_its_own_error() {
        let cases: [(&[(&str, &str)], &str); 3] = [
            (
                &[
                    ("prelude.cl", "(export [x [one]])\n(deftype P [:Int n])\n"),
                    ("x.cl", "(import [prelude []])\n(defn one [] (nope))\n"),
                ],
                "x",
            ),
            (
                &[
                    (
                        "prelude.cl",
                        "(deftype P [:Int n])\n(defmacro m [] `(x/one))\n(defn q [] (quote x/one))\n",
                    ),
                    ("x.cl", X_FAILS_ON_P),
                ],
                "x",
            ),
            (
                &[
                    ("prelude.cl", "(export [p [f]])\n(deftype P [:Int n])\n"),
                    ("p.cl", "(mod x)\n(defn f [] 1)\n"),
                    ("p/x.cl", X_FAILS_ON_P),
                ],
                "p.x",
            ),
        ];
        for (files, failing) in cases {
            let message = Project::new(files).failed_attempt_error(failing, P_UNKNOWN);
            assert!(
                message.contains(P_UNKNOWN) && !message.contains("circular"),
                "{files:?}: {message}"
            );
        }
    }

    // spec: design/int/repl-lifecycle.md §1.2.1 — the qualifier enumeration
    // shields reader-quoted data as the expander does: a `quote` subject and a
    // `quasiquote` template are data, an `unquote` inside the template is live.
    #[test]
    fn written_qualifiers_skip_quoted_data_and_read_live_unquotes() {
        let forms =
            cranelisp_frontend::parse("(f a/x (quote b/y) `(c/z ~(d/w)) :e/T (/ 1 2))").unwrap();
        let qualifiers: Vec<String> = written_qualifiers(&forms)
            .iter()
            .map(ToString::to_string)
            .collect();
        assert_eq!(qualifiers, ["a", "d", "e"]);
    }

    const W_REFUSAL: &str = "circular dependency detected: w -> prelude -> w";

    /// A project whose `w` has a table defining `one`, standing `Failed` with
    /// [`W_REFUSAL`] or compiled; `a` is registered so it can record failure
    /// dependencies.
    fn project_with_w(failed: bool) -> Project {
        let project = Project::new(&[("w.cl", "(defn one [] 1)\n")]);
        let (a, w) = (module("a"), module("w"));
        cranelisp_types::ensure_module_exists(&project.tables, &a);
        let mut table = SessionSymbolTable::new_with_params(w.clone());
        let _ =
            crate::repl::test_support::install_userfn(&mut table, "one", None, Visibility::Public);
        project.tables.insert(w.clone(), table);
        let empty = || std::sync::Arc::from(Vec::new());
        project.scheduler.register_module(a, empty(), false);
        project.scheduler.register_module(w.clone(), empty(), false);
        if failed {
            project.scheduler.notify_module_failed(
                &w,
                CranelispError::ModuleError {
                    message: W_REFUSAL.to_string(),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                },
            );
        } else {
            project.scheduler.notify_typecheck_done(&w);
        }
        project
    }

    impl Project {
        /// Run Pass 0 alone over `source` in module `a`.
        #[allow(clippy::result_large_err)] // CranelispError is the crate-wide error carrier
        fn pass0(&self, source: &str) -> Result<Option<ModuleFullPath>, CranelispError> {
            let a = module("a");
            let mut ctx = self.ctx(&a);
            let sexps = cranelisp_frontend::parse(source).unwrap();
            let declared = cluster_declared_children(&ctx, &a, &sexps);
            super::super::pass0_peel_structural(&mut ctx, &a, &sexps, &declared)
        }

        fn a_names(&self, name: &str) -> bool {
            self.tables.get(&module("a")).is_some_and(|table| {
                !table
                    .name_candidates(&cranelisp_types::Symbol::from(name))
                    .is_empty()
            })
        }
    }

    // spec: spec/08-modules.md §8.5.4 item 5, §8.10.3; design/int/int.md §6.11
    // (Pass-0 fail-fast) — an `import` or `export` of a module standing
    // `Failed` with a present table fails with that module's error, records
    // it as a failure dependency and resolves no name against its table,
    // whether or not the table holds the declared name.
    #[test]
    fn pass0_declaration_of_a_failed_module_fails_with_its_error() {
        let mut failures = Vec::new();
        for source in [
            "(export [w [one]])\n",
            "(export [w [two]])\n",
            "(import [w [one]])\n",
            "(import [w [two]])\n",
        ] {
            let project = project_with_w(true);
            let outcome = project.pass0(source);
            let carries_w_error = matches!(
                &outcome,
                Err(CranelispError::ModuleError { message, .. }) if message.contains(W_REFUSAL)
            );
            let recorded = project.scheduler.failure_dependencies(&module("a"));
            if !carries_w_error
                || recorded != BTreeSet::from([module("w")])
                || project.a_names("one")
            {
                failures.push(format!("{source}{outcome:?}; recorded {recorded:?}"));
            }
        }
        assert!(failures.is_empty(), "{failures:#?}");
    }

    // spec: design/int/int.md §6.11 (Pass-0 fail-fast) negative — with `w`
    // compiled, the same declarations install as before and record nothing.
    #[test]
    fn pass0_declaration_of_a_compiled_module_installs_its_names() {
        for source in ["(export [w [one]])\n", "(import [w [one]])\n"] {
            let project = project_with_w(false);
            assert_eq!(project.pass0(source).unwrap(), None, "{source}");
            assert!(project.a_names("one"), "{source}");
            assert!(
                project
                    .scheduler
                    .failure_dependencies(&module("a"))
                    .is_empty(),
                "{source}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// FIXME 0423 — `(mod …)` extraction write path is lib-dir-relative, not CWD.
// The source fix landed S88 (commit 5833bd1); this is the owed `/dev`
// acceptance unit test (design/int/session-persistence.md §10.3).
// spec: 08-modules.md §8.2.2
// ---------------------------------------------------------------------------
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
        write_inline_mod_to_disk(
            &parent,
            &name,
            &body(),
            project_root,
            std::slice::from_ref(&lib_dir),
        )
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
        write_inline_mod_to_disk(
            &parent,
            &name,
            &body(),
            proj_td.path(),
            std::slice::from_ref(&lib_dir),
        )
        .expect("no-op write");

        let after = std::fs::read_to_string(&backing).unwrap();
        assert_eq!(
            after, canonical,
            "an existing extraction-stable backing file must be left byte-identical"
        );
    }
}
