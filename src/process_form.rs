//! Cluster / per-form processing — the gap-orchestration crossing point.
//!
//! Extracted from `worker.rs` (FIXME 0109 Wave C). This module hosts the
//! shared form-processing family: `process_cluster_once` (the whole-cluster
//! Pass-0/1/2 core that `cluster::process_cluster` and the eval path drive)
//! and `process_regular_form` (per-form expand→build→check), plus their
//! family-private helpers — structural-form classification + handlers
//! (`classify_form`, `handle_import`/`handle_export`/`handle_mod`/
//! `handle_platform`), macro recognition + on-demand clause compilation
//! (`SymbolTableMacroResolver`, `compile_macro_*`), Pass-1 registration,
//! Pass-2 expand-then-check, dependency driving (`drive_module_dep`,
//! `register_dep`, cache-hit load), and module prep/cleanup
//! (`inject_prelude_if_needed`, `clear_module_codegen`, `wrap_exprs_as_defns`).
//!
//! This is the sole crate-crossing where a `ResolutionGap` value becomes a
//! scheduler call (Principle 1, Principle 7). The codegen/cache subsystem and
//! the worker loops stay in `worker.rs` and call into this module across the
//! module boundary via `process_cluster_once` / `process_regular_form`.
//!
//! Shared infrastructure types (`ModuleCompiler`, `ModuleCheckAccumulator`,
//! `ClusterOnce`) and the typecheck-dispatch shims (`build_program_compat`,
//! `check_program_compat*`, `ensure_typecheck_product`) remain in `worker.rs`
//! (they are referenced by both this family and the codegen path / external
//! callers) and are reached here via `crate::worker::*`.

use cranelisp_types::{ErrorLocation,
    CranelispError,
    Expr, MatchArm, ModuleFullPath, ModuleStrategy,
    ResolutionGap, Sexp, Span, TopLevel,
};

use crate::worker::{
    ModuleCheckAccumulator, ModuleCompiler, ClusterOnce,
    build_program_compat, check_program_compat,
    leading_annotation_len,
};

// ---------------------------------------------------------------------------
// Submodules (S87 §1 decomposition). The parent file holds the cluster spine
// (`process_cluster_once` / `finalize_cluster` / `pass2_*` / `process_regular_form`)
// + re-exports of the externally-cited public items so `crate::process_form::X`
// paths stay stable (the compatibility membrane, S87 §5).
// ---------------------------------------------------------------------------

mod cache_restore;
mod macro_clause;
mod macro_resolution;
pub(crate) mod form_dispatch;
mod platform;
mod dependency;

use self::platform::handle_platform;
use self::dependency::{
    BlockAction, handle_import, handle_export, handle_mod, drive_submodules,
    drive_module_dep, ensure_prelude_bit, fq_module_is_loaded, inject_prelude_if_needed,
};
// `register_dep` (the per-dep prologue) lives in `dependency`; `cache_restore`
// reaches it via `super::register_dep`, so it must be in the parent's scope.
use self::dependency::register_dep;
use self::macro_resolution::{try_expand_sexp, ExpandOutcome, compile_macro_if_needed};
use self::form_dispatch::{
    FormKind, classify_form, record_exports_on_symbol_table,
    record_platform_on_symbol_table, separate_macros, register_macro_in_module,
    pass1_register, register_default_methods, wrap_exprs_as_defns,
};

// Re-export externally-cited items so `crate::process_form::X` paths stay stable
// (the compatibility membrane, S87 §1.2 / §5).
pub use self::macro_resolution::compile_macro_for_repl;
pub(crate) use self::form_dispatch::{
    record_imports_on_symbol_table, record_submodule_on_symbol_table,
};
pub(crate) use self::dependency::gap_target_module;
use self::dependency::gap_member;
// `check_private_submodule_import`/`splice_inline_mod_to_bare` are `pub(crate)` in
// `dependency`; their only callers are the sibling/worker test modules — re-export
// on the parent path (test-only, gated to avoid a lib-build unused-import warning).
#[cfg(test)]
pub(crate) use self::dependency::{
    check_private_submodule_import, splice_inline_mod_to_bare, write_inline_mod_to_disk,
};
// `LayoutHashGate`/`layout_hash_gate` are `pub(crate)` in `platform`; their only
// caller is the sibling `tests` module via `use super::*` — re-export on the
// parent path (test-only, gated to avoid a lib-build unused-import warning).
#[cfg(test)]
pub(crate) use self::platform::{LayoutHashGate, layout_hash_gate};
// `has_code_ptr` is `pub(crate)` in `macro_resolution`; the only external caller
// is `crate::process_form::has_code_ptr` in `worker/tests.rs` — re-export it on
// the parent path so that reference resolves (test-only, gated to avoid a
// lib-build unused-import warning).
#[cfg(test)]
pub(crate) use self::macro_resolution::has_code_ptr;

// Private re-export of the resolver struct the sibling `tests` module constructs
// via `use super::*` (visible to descendants of the parent, not beyond — S87 §1.3).
#[cfg(test)]
use self::macro_resolution::SymbolTableMacroResolver;
// `CompileScheduler`/`FQSymbol`/`CheckState` are no longer used by the parent
// spine (their only callers moved into submodules), but the sibling `tests`
// module reaches them via `use super::*`; keep them in the parent's test-scope
// so those tests resolve.
#[cfg(test)]
use crate::scheduler::CompileScheduler;
#[cfg(test)]
use cranelisp_types::{FQSymbol, Symbol, Visibility};
#[cfg(test)]
use cranelisp_typecheck::CheckState;
#[cfg(test)]
use std::path::Path;


// ---------------------------------------------------------------------------
// process_module_forms — two-pass per-form typecheck (C1)
// ---------------------------------------------------------------------------

/// Process a whole cluster of forms once, from the top (S78 in-call-stack
/// restructure — replaces the legacy `process_module_forms` per-form outer
/// loop + saved-suspend-state resume).
///
/// Runs the full Pass-0 / Pass-1 / Pass-2 sequence over `sexps` against the
/// live `SymbolTable`, building all in-progress state (parsed forms, staging
/// table, expand position, accumulator) on THIS call's stack frame:
///
/// - **Pass 0** — peel structural forms (`import`/`export`/`mod`/`platform`)
///   and the implicit prelude. A structural dep that is not yet loaded is
///   registered with the scheduler (its sexps ride the dep's work packet) and
///   blocked on (`block_for_typecheck`), then this function returns
///   `ClusterOnce::Gap { dep }` — the in-progress frame is dropped (atomic
///   discard; live unchanged).
/// - **Pass 1** — separate macros, build AST, register signatures / macros /
///   default methods.
/// - **Pass 2** — per-form expand-then-check. An FQ reference to an unloaded
///   module surfaces a gap that is driven to readiness (register + block) and
///   returns `ClusterOnce::Gap { dep }`.
/// - **Finalize** — single `check_program_compat` (cluster-mode staging,
///   commit-on-Ok / discard-on-Err). A surviving FQ-auto-load gap is driven;
///   any other gap is a hard error.
///
/// On a `Gap` the caller drives the wait + retry-from-top: the worker wrapper
/// frees back to the pool (the scheduler requeues this module when `dep`
/// completes), the eval wrapper blocks on `wait_module_inmem_complete_blocking`
/// then loops. There is no saved resume index — each pass re-derives from
/// `sexps` against now-larger live state. The forms-before-import are always
/// re-processed (Defect-B / OQ-4 preserved by construction).
///
/// On `Done` the cluster's expanded program is returned for codegen; the
/// cluster-level REPL/scheduler metadata rides on `ProcessedCluster` (committed
/// via `cluster::insert_cluster`). The per-symbol staging entries already
/// committed to live inside `check_program_compat`.
pub fn process_cluster_once(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    strategy: ModuleStrategy,
) -> Result<ClusterOnce, CranelispError> {
    // In-call-stack working state — rebuilt from `sexps` every pass, dropped on
    // a gap. Never lands in a shared map (the S60–S62 heisenbug substrate is
    // gone). `expanded_program` accumulates within THIS pass only.
    let mut accumulator = ModuleCheckAccumulator::new();
    let mut expanded_program: Vec<TopLevel> = Vec::new();

    // §8.6.4 (FIXME 0514) — the definition-over-(import|export|prelude)
    // rejection is no longer mode-gated here: it moved to the shared typecheck
    // `check_forms` Pass-1 seam, where it fires identically in every mode (the
    // mode-parity MUST) and is the only place that also sees the prelude OUTER
    // scope. The former `additive` flag threaded into the two int-side reject
    // seams is retired; Pass-0 import/export install keeps only §8.6.5 ambiguity
    // detection (including the distinct-terminal prelude-overlap poison).

    // S93 signature/body pre-pass — the cluster's STATIC import closure
    // (`signature-body-prepass.md` §3.1/§4). Computed ONCE from this cluster's
    // Pass-0 `(import …)` decls; a cycle is a clean compile-time error (D0030
    // mutual-import disposition: NOT compiled), surfaced at the import site
    // instead of the H6/H7-era half-published `'sym' not found in module 'x'`.
    // The same `ClosureOrder` is reused by the body-boundary signature barrier
    // (Invariant PP) below. `None` when the cluster declares no imports.
    let closure;

    if strategy == ModuleStrategy::Replace {
        // Set active module. Symbol table is preserved for slot reuse
        // and type-change detection.
        ctx.set_current_module(module.clone());

        // Static cycle gate — fast-exits when the cluster has no imports.
        closure = dependency::static_import_closure(ctx, module, sexps)?;

        // Zero GOT slots and clear codegen artifacts for this module's
        // symbols. Slot assignments are preserved so re-compiled code
        // lands in the same slots.
        clear_module_codegen(ctx, module);

        // Prelude fallback bit (§8.8.1) — single-sourced via `ensure_prelude_bit`
        // (FIXME 0516 fold-in), fresh-recompute discipline for the Replace path.
        // Then ensure prelude is LOADED so the fallback has a table to consult.
        ensure_prelude_bit(ctx, module, sexps, true);
        if let Some(dep) = inject_prelude_if_needed(ctx, module, sexps)? {
            return Ok(ClusterOnce::Gap { dep });
        }
    } else {
        // Additive (REPL eval): just set the active module. Module state
        // persists from previous evals — no clear, no re-injection.
        ctx.set_current_module(module.clone());

        // S78 §2.7 — the per-module prelude-fallback bit was set ON at the
        // entry module's startup compile and persists across REPL turns. If a
        // REPL form now explicitly references prelude (`(import [prelude []])`
        // refusal, or a selective `(import [prelude [...]])`), the implicit
        // fallback must turn OFF for this module (spec §8.8.1). Single-sourced
        // via `ensure_prelude_bit` (FIXME 0516 fold-in), incremental-delta
        // discipline for the Additive path — the SAME invariant the Replace arm
        // writes fresh, one helper.
        ensure_prelude_bit(ctx, module, sexps, false);

        // Static cycle gate for the eval path too (S93 Invariant PP). The eval
        // thread is the genuine barrier waiter; a REPL `(import …)` whose static
        // closure is cyclic is rejected up front, and the closure is reused by
        // the body-boundary barrier below.
        closure = dependency::static_import_closure(ctx, module, sexps)?;
    }

    // --- Pass 0: structural-form peel (import/export/mod/platform) ---
    // Imported symbols must be in scope before pass1_register checks trait
    // impl bodies. An unloaded dep is registered + blocked on, and the cluster
    // retries from the top once it is live.
    for sexp in sexps.iter() {
        match classify_form(sexp, module)? {
            // FIXME 0548 — record the persistence entry only AFTER `handle_*`
            // resolves successfully (`BlockAction::Continue`). A structural form
            // that FAILS resolution errors via `?` before we reach the record,
            // so it leaves no trace on the persistence list `save.rs` re-emits —
            // a failed import/export/mod/platform is never written into the
            // regenerated backing `.cl`. (`Block` is not a failure: the dep must
            // load and the cluster retries from the top, where the successful
            // resume records it.) Applied uniformly across all four forms.
            FormKind::Import(specs) => {
                match handle_import(ctx, module, specs.clone())? {
                    BlockAction::Continue => {
                        record_imports_on_symbol_table(ctx, module, &specs);
                    }
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            FormKind::Export(specs) => {
                match handle_export(ctx, module, &specs)? {
                    BlockAction::Continue => {
                        record_exports_on_symbol_table(ctx, module, &specs);
                    }
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            FormKind::Mod(decl) => {
                match handle_mod(ctx, module, &decl)? {
                    BlockAction::Continue => {
                        record_submodule_on_symbol_table(ctx, module, &decl);
                    }
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            FormKind::Platform(spec) => {
                match handle_platform(ctx, module, &spec)? {
                    BlockAction::Continue => {
                        record_platform_on_symbol_table(ctx, module, &spec);
                    }
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            _ => {} // Regular, Defmacro — handled in Pass 1 / Pass 2.
        }
    }

    // --- Signature barrier (S93 Invariant PP; BC §6 ruling B) ---
    // No body (Pass-1/Pass-2) is admitted until EVERY module in the static
    // import closure has published its signatures (reached a terminal typecheck
    // pool — the publication edge; FIXME 0452 removed the redundant
    // `signatures_ready` bit). This makes "a body never reads an
    // incompletely-published sibling" a structurally-verifiable property of
    // `process_cluster_once` (§3.3), rather than an invariant only emergent from
    // the per-dep Pass-0 convention — and it covers TRANSITIVE closure members
    // Pass-0's direct-import peel does not. The worker check-and-blocks ATOMICALLY
    // (single lock, no lost-wakeup gap) on the first unready member and frees its
    // thread back to the pool (Gap → requeue-when-ready, the requeue kernel); the
    // eval thread — the sole genuine waiter — blocks inside the scheduler and
    // proceeds when the barrier opens. A signature dependency therefore never
    // reaches the body as a half-published read.
    if let Some(ref c) = closure
        && let Some(member) = dependency::gate_body_on_signature_barrier(ctx, module, c)?
    {
        return Ok(ClusterOnce::Gap { dep: member });
    }

    // --- Pass 1: register signatures / macros / default methods ---
    let (regular_sexps, macro_infos) = separate_macros(sexps, module)?;

    // Build AST for regular (non-macro) forms. Build is mode-agnostic;
    // `(trace ...)` in `--link` standalone-binary mode fails at link time via
    // the architecture's natural missing-symbol detection.
    let program = build_program_compat(&regular_sexps)?;
    let working_program = wrap_exprs_as_defns(&program);

    pass1_register(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &working_program, &mut accumulator)?;

    let intr = ctx.introspection;
    for (name, info, sexp) in &macro_infos {
        // Direct top-level defmacro: the authored form IS the defmacro form.
        // CS-D2: capture the verbatim authored text (reader shorthand intact).
        let authored_source = verbatim_source_slice(ctx, module, sexp);
        register_macro_in_module(
            ctx.symbol_tables, intr, module, name, info, sexp, sexp, authored_source,
            ctx.module_aliases, ctx.prelude_fallback,
        )?;
    }

    let defaults = register_default_methods(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &mut accumulator)?;
    accumulator.default_method_defns = defaults;

    // --- Pass 2: per-sexp expand-then-check ---
    let pass2_result = pass2_check_bodies_with_expansion(
        ctx, module, sexps, &mut accumulator, &mut expanded_program,
    )?;

    match pass2_result {
        Pass2Result::Complete => {
            // Finalize: single `check_program_compat` over the expanded
            // cluster. A surviving FQ-auto-load gap is driven (register +
            // block) and surfaces as `Gap`; any other gap is a hard error.
            let outcome = finalize_cluster(
                ctx, module, &expanded_program, &mut accumulator,
            )?;
            // FIXME 0342 — only AFTER the parent's symbols are committed to live
            // (finalize_cluster done) do we drive declared submodules. This is
            // the deferral that lets a submodule's `(import [super [helper]])`
            // resolve the now-live parent symbol. A submodule that needs loading
            // surfaces as a `Gap`; the cluster retries from the top (idempotent —
            // already-loaded submodules are skipped). Both the worker entry
            // (`cluster::process_cluster`) and the REPL entry
            // (`session_v4::process_single_form`) drive this same core.
            if matches!(outcome, ClusterOnce::Done { .. })
                && let Some(dep) = drive_submodules(ctx, module)?
            {
                return Ok(ClusterOnce::Gap { dep });
            }
            Ok(outcome)
        }
        Pass2Result::BlockedOnFqModule { dep_module } => {
            // An FQ reference to an unloaded module surfaced during expansion
            // (Pass 2 macro recognition). Drive the dependency (register + block)
            // with import's file-resolution rules; the cluster retries from the
            // top once it is live (FIXME 0268). 0571 AL-3: attribute a
            // missing-module failure to the REFERENCE SITE (`dep_module/...` in
            // the cluster's forms), not the bogus module-head `0..0` span.
            let ref_span = working_program
                .iter()
                .find_map(|tl| match tl {
                    TopLevel::Expr(e) => find_module_qualified_ref_span(e, dep_module.as_ref()),
                    TopLevel::Defn(d) => d
                        .variants
                        .iter()
                        .find_map(|v| find_module_qualified_ref_span(&v.body, dep_module.as_ref())),
                    _ => None,
                })
                .unwrap_or(Span::SYNTHETIC);
            drive_module_dep(ctx, module, &dep_module, ref_span)?;
            Ok(ClusterOnce::Gap { dep: dep_module })
        }
    }
}

/// Finalize a fully expanded cluster: single `check_program_compat` dispatch,
/// then build the `Done` outcome (S78 — replaces the legacy `finalize_module`).
///
/// Per Decision 44's 2026-05-13 third amendment, the typecheck dispatch is one
/// `check_forms` call over `expanded_program` plus the accumulated
/// default-method defns. The cluster-mode staging path inside
/// `check_program_compat` commits per-symbol entries to live on `Ok` / discards
/// on `Err`.
///
/// FQ auto-loading (spec §8.5.4 / §9.3.6, FIXME 0268): a recoverable gap naming
/// an unloaded module is driven to readiness here (register + block, same
/// file-resolution rules as `import`) and surfaces as `ClusterOnce::Gap` — the
/// cluster retries from the top once the dep is live. No speculative function
/// JIT push; the synchronous dependency typecheck-and-compile is the only
/// mechanism.
fn finalize_cluster(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    expanded_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<ClusterOnce, CranelispError> {
    let mut final_working = wrap_exprs_as_defns(expanded_program);

    // Append default-method defns the trait-impl Pass-1 step had deferred.
    // Under collapsed `check_forms` they ride into the same dispatch alongside
    // the body forms. CLONE (not `take`) — `check_program_compat` may surface
    // an FQ-auto-load gap, in which case the whole cluster retries from the
    // top (a fresh `finalize_cluster` runs); draining here would lose them.
    for defn in &accumulator.default_method_defns {
        final_working.push(TopLevel::Defn(defn.clone()));
    }

    // Automatic IO scheduling (spec §10.12, FIXME 0367): transform `bind!`-derived
    // bind chains into `Expr::ParBind` nodes for data-independent, non-Sequential
    // platform effects. Runs over the post-Pass-2 `final_working` (after macro
    // expansion built the bind-chain shape), before typecheck sees the tree. This
    // is the single mode-uniform seam — all three modes (`--run`/`--link`/REPL)
    // flow through `process_cluster_once` → `finalize_cluster`.
    //
    // `CRANELISP_NO_IO_SCHEDULE` (presence-disables; default ON) is the escape
    // hatch — checked ONCE here, not per-defn (§5c). Unit tests call
    // `auto_schedule_defn` directly, bypassing this gate.
    if std::env::var("CRANELISP_NO_IO_SCHEDULE").is_err() {
        crate::session_setup::apply_bind_chain_analysis(
            &mut final_working,
            ctx.symbol_tables,
            module,
        );
    }

    let (maybe_gap, cluster_warnings, unresolved_dispatch, redefinitions) = check_program_compat(
        ctx.symbol_tables,
        ctx.module_aliases,
        ctx.prelude_fallback,
        module,
        &final_working,
        // S101: the session context carries the retention pool the commit
        // gate's ABI-epoch slot policy freezes superseded code into
        // (design/int/session-transaction.md §7.1).
        ctx.shared_state,
    )?;
    if let Some(gap) = maybe_gap {
        // FIXME 0490 — phantom-member diagnostic. typecheck's qualified-name
        // resolution (`checker::lookup`) probes a current-module-relative CHILD
        // path `<current>.<qualifier>` BEFORE the absolute module; when the
        // absolute module IS loaded but the MEMBER is missing, the absolute
        // candidate produces NO gap, so the CHILD gap (`user.primitives/…`)
        // survives and would drive here — hunting a phantom submodule and
        // reporting `module 'user.primitives' referenced by 'user.primitives/...'
        // not found` at `0..0` (three lies: phantom module, `'...'` placeholder,
        // bogus span). Detect the shape at this int seam and report
        // member-not-found against the REAL loaded module instead. (The deeper
        // ordering cure — typecheck preferring the loaded absolute module over
        // the phantom child — is a `/typecheck` FIXME.)
        if let Some(err) = phantom_member_diagnostic(ctx, module, &gap, expanded_program) {
            return Err(err);
        }
        // 0571 (B4/B5 + AL-3): the qualified-reference gap now fires
        // unconditionally on a member-absent abs module (typecheck
        // `resolve_qualified`). INT owns the decision from the module's LIVE
        // state (Principle 3/17 — typecheck stays scheduler-free). The
        // reference-site span makes every diagnostic actionable (AL-3), replacing
        // the `Span::SYNTHETIC` module-head span the wrap reported at.
        if let Some(dep) = gap_target_module(&gap) {
            let member = gap_member(&gap);
            // Module present AND terminal (`fq_module_is_loaded`) ⇒ its
            // signatures are fully published, so the member GENUINELY does not
            // exist ⇒ the honest "module X has no member Y" at the reference
            // site (§8.5.4). Authored via the single `module_has_no_member_error`
            // seam (I4, 0571.2 — the sole author of this diagnostic, shared with
            // `phantom_member_diagnostic`). Never re-drive a terminal module (the
            // member stays absent on every retry — an infinite loop).
            if fq_module_is_loaded(ctx, &dep) {
                return Err(module_has_no_member_error(expanded_program, &dep, &member));
            }
            // Absent OR present-but-non-terminal ⇒ drive it (register + park): a
            // not-yet-loaded module loads then re-drives; a present-but-non-
            // terminal module parks via `drive_module_dep`'s already-loaded /
            // `block_dep` arm, whose `block_for_typecheck` acyclicity check
            // converts a genuine FQ cycle into the honest circular-dependency
            // error (B4/B5). A missing-module file surfaces `drive_module_dep`'s
            // "module not found" at the reference span (AL-3).
            let ref_span = expanded_program
                .iter()
                .find_map(|tl| find_named_var_span_in_toplevel(tl, &format!("{dep}/{member}")))
                .unwrap_or(Span::SYNTHETIC);
            drive_module_dep(ctx, module, &dep, ref_span)?;
            return Ok(ClusterOnce::Gap { dep });
        }
        // Not an FQ-module gap we can act on — surface a hard error so the
        // failure is not silently swallowed.
        return Err(CranelispError::TypeError {
            message: format!("unresolved cross-module reference: {gap:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Defaults consumed successfully — drain them.
    accumulator.default_method_defns.clear();

    // Build a program view for codegen. The nice worker no longer reads program
    // contents — it enumerates via `defined_symbols()` — but a non-empty
    // `program` signals "has compilable defns" and drives `derive_codegen_batch`.
    let program: Vec<TopLevel> = expanded_program.to_vec();

    // Cluster-level metadata. The per-symbol staging entries already committed
    // to live inside `check_program_compat`; the typecheck warning channel
    // (FIXME 0365) flows back on the `Ok` path and is threaded onto
    // `ProcessedCluster.warnings` so the REPL driver renders each as a
    // `; warning: <message>` line. The `ProcessedCluster` carrier is committed
    // via `cluster::insert_cluster`.
    let mut processed = crate::cluster::ProcessedCluster::from_parts(
        Vec::new(),
        cluster_warnings,
        Vec::new(),
        Vec::new(),
    );
    // S101: the commit gate's redefinition classifications ride the cluster
    // carrier back to the driver; the eval path runs the dependent-
    // recompilation transaction for `AbiChanging` outcomes after the target's
    // own codegen succeeds (design §13).
    processed.set_redefinitions(redefinitions);
    // 0611 carrier — the return-poly dispatch sites still unresolved at
    // finalize (EMPTY for every valid program). The eval driver consults these
    // at the `__expr` eval-result boundary (class (b), Principle 19): a bare
    // `(zed)` reaching the eval path dies with the §3.11 ambiguity instead of
    // leaking the backend `__expr`-has-no-GOT-slot error.
    processed.set_unresolved_dispatch(unresolved_dispatch);

    Ok(ClusterOnce::Done { processed, program })
}

/// FIXME 0490 — turn a phantom-submodule resolution gap into an honest
/// member-not-found diagnostic against the REAL loaded module.
///
/// Fires only for the exact shape the mis-resolution produces: a gap whose
/// module is `<current>.<qualifier>` (a single-component child of the
/// referencing module — typecheck's `checker::lookup` synthesises this
/// current-module-relative probe) where `<qualifier>` names a REAL, loaded
/// module. That is precisely the "qualified reference to a loaded module whose
/// member does not exist" case: the loaded absolute-module candidate produced
/// no gap of its own, so the phantom child gap survived. Every other shape —
/// a genuine unloaded nested submodule (`<current>.<child>` where `<child>` is
/// NOT itself a loaded module), a bare-module gap, a non-child qualifier —
/// returns `None` and drives/errors normally.
fn phantom_member_diagnostic(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    gap: &ResolutionGap,
    program: &[TopLevel],
) -> Option<CranelispError> {
    let (gap_module, member) = match gap {
        ResolutionGap::SymbolTypechecked(fq) | ResolutionGap::MacroInMem(fq) => {
            (fq.module.clone(), fq.symbol.to_string())
        }
        ResolutionGap::Type(fqt) => (fqt.module.clone(), fqt.name.to_string()),
        _ => return None,
    };
    // Is `gap_module` a single-component child `<current>.<qualifier>` of the
    // referencing module? (A genuine dotted submodule path is not this shape.)
    let qualifier = gap_module.as_ref().strip_prefix(&format!("{module}."))?;
    if qualifier.is_empty() || qualifier.contains('.') {
        return None;
    }
    // Only fire when `<qualifier>` names a REAL loaded module — a genuine
    // missing submodule (`<qualifier>` not a loaded module) must still drive.
    if !fq_module_is_loaded(ctx, &ModuleFullPath::from(qualifier)) {
        return None;
    }
    // Locate the user's reference span so the diagnostic carries a real source
    // location (`<qualifier>/<member>` is the verbatim AST var name) rather
    // than the `0..0` the phantom-module path emitted.
    Some(module_has_no_member_error(
        program,
        &ModuleFullPath::from(qualifier),
        &member,
    ))
}

/// The single author of the §8.5.4 "module X has no member Y" diagnostic (I4,
/// 0571.2). BOTH the FQ-gap decision arm (`process_cluster_once`, a member-absent
/// terminal module) and `phantom_member_diagnostic` (the current-module-relative
/// mis-resolution shape) route the message + reference-span lookup through here,
/// so the diagnostic has exactly one authoring site — no display-envelope mirror
/// (Principle 7). Locates the user's verbatim `<module>/<member>` reference span
/// so the error carries a real source location, falling back to `Span::SYNTHETIC`
/// when the var name is not found in the program.
fn module_has_no_member_error(
    program: &[TopLevel],
    module: &ModuleFullPath,
    member: &str,
) -> CranelispError {
    let referenced = format!("{module}/{member}");
    let span = program
        .iter()
        .find_map(|tl| find_named_var_span_in_toplevel(tl, &referenced))
        .unwrap_or(Span::SYNTHETIC);
    CranelispError::ModuleError {
        message: format!("module '{module}' has no member '{member}'"),
        location: ErrorLocation::from_span_file(span, None),
    }
}

/// Find the span of an `Expr::Var` named `target` inside a top-level form (a
/// bare expression or a defn body). Used only by `phantom_member_diagnostic`
/// to attribute the member-not-found diagnostic to the user's reference.
fn find_named_var_span_in_toplevel(tl: &TopLevel, target: &str) -> Option<Span> {
    match tl {
        TopLevel::Expr(e) => find_named_var_span(e, target),
        TopLevel::Defn(d) => d
            .variants
            .iter()
            .find_map(|v| find_named_var_span(&v.body, target)),
        _ => None,
    }
}

/// Recursively search `expr` for an `Expr::Var` whose name equals `target`,
/// returning its span. Covers every child-bearing `Expr` variant.
fn find_named_var_span(expr: &Expr, target: &str) -> Option<Span> {
    find_var_span_matching(expr, &|name| name == target)
}

/// The span of the FIRST `Expr::Var` whose name is qualified by `module` (i.e.
/// `module/...`) — the reference-site span for a missing-module / member-absent
/// FQ diagnostic (0571 AL-3) when only the module (not the member) is known at
/// the seam (the expand-time `BlockedOnFqModule`).
fn find_module_qualified_ref_span(expr: &Expr, module: &str) -> Option<Span> {
    let prefix = format!("{module}/");
    find_var_span_matching(expr, &|name| name.starts_with(&prefix))
}

/// The span of the first `Expr::Var` whose name satisfies `pred`. The single
/// AST-walk both the exact-name ([`find_named_var_span`]) and module-prefix
/// ([`find_module_qualified_ref_span`]) reference-site lookups share (P7).
fn find_var_span_matching(expr: &Expr, pred: &impl Fn(&str) -> bool) -> Option<Span> {
    let arm = |e: &Expr| find_var_span_matching(e, pred);
    match expr {
        Expr::Var { name, span, .. } if pred(name.as_ref()) => Some(*span),
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => None,
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => bindings
            .iter()
            .find_map(|(_, e)| arm(e))
            .or_else(|| arm(body)),
        Expr::If { cond, then_branch, else_branch, .. } => {
            arm(cond).or_else(|| arm(then_branch)).or_else(|| arm(else_branch))
        }
        Expr::Lambda { body, .. } | Expr::Annotate { expr: body, .. } | Expr::Trace { body, .. } => {
            arm(body)
        }
        Expr::Apply { callee, args, .. } => {
            arm(callee).or_else(|| args.iter().find_map(&arm))
        }
        Expr::Match { scrutinee, arms, .. } => arm(scrutinee)
            .or_else(|| arms.iter().find_map(|a: &MatchArm| arm(&a.body))),
        Expr::VecLit { elements, .. } => elements.iter().find_map(&arm),
        Expr::ConstrADT { fields, .. } => fields.iter().find_map(&arm),
        Expr::LaunchContinue { launched, continuation, .. } => {
            arm(launched).or_else(|| arm(continuation))
        }
    }
}

/// Internal result from Pass 2 — either complete or blocked.
/// The expanded program is accumulated in the caller's mutable Vec.
enum Pass2Result {
    /// All forms processed. Expanded program is in the caller's Vec.
    Complete,
    // Note: Import/export/mod/platform blocking is now handled in Pass 0.
    /// An FQ macro reference (`mod/macro`) named a not-yet-loaded module during
    /// expansion. The caller drives the dependency and the cluster retries from
    /// the top once it is live (FIXME 0268, spec §9.3.6). S78: no `form_index`
    /// — the whole cluster re-runs (retry-from-top), so there is no Pass-2
    /// resume index to honour.
    BlockedOnFqModule {
        dep_module: ModuleFullPath,
    },
}

/// Pass 2: per-sexp expand-then-check, with inline macro compilation
/// and lazy dependency discovery (Step 5).
///
/// Iterates sexps from `start_form_index`. For each:
/// - Import: discover dep, register with scheduler, block if needed.
/// - Export: register export metadata.
/// - Mod: register submodule (write inline body to disk if present).
/// - Platform: load DLL and register type signatures.
/// - Defmacro: skip (already registered in Pass 1).
/// - Regular: try expand, build AST, typecheck body.
fn pass2_check_bodies_with_expansion(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<Pass2Result, CranelispError> {
    let mut idx = 0;
    while idx < sexps.len() {
        let sexp = &sexps[idx];

        match classify_form(sexp, module)? {
            // Import/export/mod/platform forms are processed in Pass 0
            // (before Pass 1). By the time Pass 2 runs, these have already
            // been handled. Skip them here — they are no-ops in Pass 2.
            FormKind::Import(_)
            | FormKind::Export(_)
            | FormKind::Mod(_)
            | FormKind::Platform(_) => {
                idx += 1;
            }
            FormKind::Defmacro => {
                // Registered in Pass 1. Compile eagerly in Pass 2 so type errors
                // in the macro body are caught at definition time (not deferred
                // until the macro is first called).
                let info = cranelisp_frontend::parse_defmacro(sexp)?;
                compile_macro_if_needed(ctx, module, &info, sexp.span(), accumulator)?;
                idx += 1;
            }
            FormKind::Regular => {
                // A leading `:Type` annotation binds the FOLLOWING form (BC §1
                // invariant 9). int groups the annotation prefix sexp(s) with
                // the bound form so the frontend's `build_forms` pairing fires;
                // only the bound form is macro-expanded (an annotation is never
                // a macro head). int decides the group boundary; the frontend
                // builds the `Expr::Annotate`. A trailing annotation with no
                // following form passes through as a one-sexp group so the
                // frontend surfaces `annotation missing expression`.
                let ann_len = leading_annotation_len(&sexps[idx..]);
                let (prefix, form_idx) = if ann_len > 0 && idx + ann_len < sexps.len() {
                    (&sexps[idx..idx + ann_len], idx + ann_len)
                } else {
                    (&sexps[idx..idx], idx)
                };
                let next = idx.max(form_idx) + 1;
                if let Some(dep_module) = process_regular_form(
                    ctx, module, prefix, &sexps[form_idx], accumulator, expanded_program,
                )? {
                    // FQ macro reference to an unloaded module (FIXME 0268).
                    // The cluster retries from the top after the dep is loaded.
                    return Ok(Pass2Result::BlockedOnFqModule { dep_module });
                }
                idx = next;
            }
        }
    }
    Ok(Pass2Result::Complete)
}

/// The verbatim authored text of `form`, sliced from the module's recorded
/// `source_text` by span and CONSISTENCY-GATED (S102 CS-D2, §15.4.7) via the
/// shared `save::verbatim_slice` gate (S102 W5R M-5 — Principle 7): the slice
/// must re-parse to exactly the recorded form (reader-desugar-aware, so
/// authored shorthand like `` `(… ~e) `` passes). Returns `None` — callers
/// fall back to `pretty_print` — when the module has no `source_text`, the
/// span is out of bounds / off a char boundary, or the slice does not match
/// (e.g. a REPL turn's fresh 0-based spans against the module's load-time
/// file text).
fn verbatim_source_slice(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    form: &Sexp,
) -> Option<String> {
    let tp = ctx.typecheck_products.get(module)?;
    let text = tp.source_text.as_ref()?;
    crate::save::verbatim_slice(form, text)
}

/// Process a regular (non-module-declaration) form in Pass 2.
///
/// Tries macro expansion via the SymbolTableMacroResolver, builds AST,
/// registers any new signatures (for begin-spliced defns), then typechecks
/// the body. New macros from expansion (e.g. const/def) are registered in
/// the symbol table and become visible to the resolver for subsequent forms.
///
/// Returns `Ok(Some(dep_module))` when expansion encountered an FQ macro head
/// whose module is not loaded — the caller loads `dep_module` and resumes this
/// form (FIXME 0268). Returns `Ok(None)` on normal completion.
fn process_regular_form(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    annotation_prefix: &[Sexp],
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<Option<ModuleFullPath>, CranelispError> {
    // Try macro expansion on the bound form (the annotation prefix is never a
    // macro head — it is the `:Type` token that binds this form per BC §1
    // invariant 9, and is prepended below so the frontend's `build_forms`
    // performs the `Expr::Annotate` pairing).
    let effective_sexp = match try_expand_sexp(ctx, module, sexp, accumulator)? {
        ExpandOutcome::Expanded(opt) => opt,
        ExpandOutcome::BlockedOnFqModule(dep) => {
            // Nothing has been appended to `expanded_program` for this form —
            // the caller will resume it after loading `dep`.
            return Ok(Some(dep));
        }
    };

    let sexp_to_build = match &effective_sexp {
        Some(expanded) => expanded,
        None => sexp,
    };

    let flattened = cranelisp_frontend::flatten_begin(sexp_to_build.clone());

    // Partition flattened forms: macro expansion (e.g. const, def) can produce
    // defmacro forms that must be routed through the macro pipeline, not the
    // AST builder which rejects them. A leading `:Type` annotation prefix is
    // carried through verbatim ahead of the (single) bound form so `build_forms`
    // pairs them; a prefix only ever accompanies a single non-`begin`,
    // non-`defmacro` bound form.
    let mut regular_sexps: Vec<Sexp> = annotation_prefix.to_vec();
    for form in flattened {
        if cranelisp_frontend::is_defmacro(&form) {
            let info = cranelisp_frontend::parse_defmacro(&form)?;
            let intr = ctx.introspection;
            // S102 CS-D1 (origin-uniform recording): a defmacro reaching this
            // loop is never the whole top-level form (direct defmacros route
            // through Pass 1's `separate_macros`) — it is an expansion product
            // or a literal-`begin` member. The regen authority is therefore
            // the ORIGINAL outer form `sexp`, exactly what the sibling defn
            // records below — one turn, one authored form, one emission.
            let authored_source = verbatim_source_slice(ctx, module, sexp);
            register_macro_in_module(
                ctx.symbol_tables, intr, module, &info.name, &info, &form, sexp, authored_source,
                ctx.module_aliases, ctx.prelude_fallback,
            )?;
            compile_macro_if_needed(ctx, module, &info, form.span(), accumulator)?;
        } else {
            regular_sexps.push(form);
        }
    }

    // If only the annotation prefix remains (the bound form expanded entirely
    // into defmacros), there is nothing to build — but that is a degenerate
    // shape that cannot arise (an annotation binds an expression form, not a
    // defmacro). Guard against an orphan prefix reaching `build_forms`.
    if regular_sexps.len() == annotation_prefix.len() {
        return Ok(None);
    }

    let built = build_program_compat(&regular_sexps)?;
    let working = wrap_exprs_as_defns(&built);

    // Per Decision 44's 2026-05-13 third amendment, the per-form
    // `check_form(Register)` + `check_form(CheckBody)` calls are no longer
    // exposed; typecheck is now driven once over the cluster via
    // `check_program_compat` in `finalize_module`. The per-form work loop
    // below remains in place for the introspection + scheduler-notification
    // bookkeeping (which is `int`-side, not typecheck-side) — accumulator
    // mutation is silenced here.
    let _ = accumulator;
    for form in &working {

        // Populate introspection for REPL slash commands (--repl only).
        if let Some(intr_map) = ctx.introspection
            && let TopLevel::Defn(defn) = form {
                let fq = cranelisp_types::FQSymbol {
                    module: module.clone(),
                    symbol: defn.name.clone(),
                };
                let mut entry = intr_map.entry(fq).or_default();
                // Source: extract VERBATIM from module source_text via sexp
                // span, consistency-gated (S102 CS-D2 — the slice must
                // re-parse to the recorded form; a stale `source_text` from a
                // previous load never mis-slices into the record). REPL eval
                // may overwrite with the actual input text later.
                if entry.source.is_none() {
                    let src = verbatim_source_slice(ctx, module, sexp);
                    entry.source = src.or_else(|| Some(crate::pretty::pretty_print_plain(sexp)));
                }
                entry.sexp = Some(sexp.clone());
                if let Some(ref expanded) = effective_sexp {
                    entry.expanded = Some(expanded.clone());
                }
                entry.ast = Some(defn.clone());
            }
        // S93 net-neutral subtraction (`signature-body-prepass.md` §6): the
        // former per-symbol `notify_symbol_typechecked(module, defn.name)` is
        // RETIRED. It satisfied only specific-symbol typecheck waiters, but every
        // live `block_for_typecheck` registers a `"*"` (whole-module) waiter
        // satisfied by `notify_typecheck_done`'s sweep — so the per-symbol notify
        // matched no waiter and was a no-op. Removing it deletes one of the two
        // signature-readiness protocols (Principle 7) that the module-atomic
        // barrier subsumes.
    }

    expanded_program.extend(built);
    Ok(None)
}

/// Clear codegen artifacts for a module's symbols at the start of Replace
/// (watcher-reload) processing.
///
/// S101 (design/int/session-transaction.md §7.3): this path **no longer
/// zeroes GOT slots**. The former zeroing opened a NULL window — a stale
/// closure calling mid-recompilation SIGSEGV'd — and provided no soundness
/// (per-slot `store_slot` writes are individually atomic). Old pointers now
/// stay live until each symbol's new pointer lands: ABI-preserving members
/// get gap-free late binding, and ABI-changing members are re-slotted by the
/// commit gate (fresh slot + freeze) like any other redefinition.
///
/// Displaced `Code` handles move into the session retention pool instead of
/// being `None`-d (§6.3): the former comment here claimed the `Arc<Jit>`
/// handles "in `kept_jits`" kept the old pages alive, but `kept_jits` was
/// dissolved in S58 (Decision 35) — `*code = None` could drop the LAST Arc
/// and free machine code still reachable from in-flight frames or heap
/// closures. With no session context (unit tests), the pre-S101 drop
/// behaviour is preserved (nothing executes concurrently there).
fn clear_module_codegen(ctx: &mut ModuleCompiler, module: &ModuleFullPath) {
    // Collect qualified symbol names for this module from the TC symbol table.
    let symbols: Vec<cranelisp_types::Symbol> = {
        let table = ctx.symbol_tables.get(&ctx.current_module).unwrap();
        table.all_symbols()
            .filter_map(|(name, entry)| {
                // Only clear codegen for definitions owned by this module,
                // not imports or special forms. Constructors are now
                // `Def { kind: DefKind::Constructor }`; macro parents
                // (`DefKind::Macro`) carry no callable codegen and are skipped.
                // Special forms live in `ModuleEntry::SpecialForm` (the `_`
                // arm). (S70/W-Absorb.)
                match entry {
                    cranelisp_types::ModuleEntry::Def { kind, .. } => {
                        if matches!(kind.as_ref(), cranelisp_types::DefKind::Macro { .. }) {
                            None
                        } else {
                            let qualified = cranelisp_types::Symbol::from(
                                format!("{}/{}", module, name)
                            );
                            Some(qualified)
                        }
                    }
                    _ => None,
                }
            })
            .collect()
    };

    // S101 §7.3: GOT slots are NOT zeroed. Each old pointer stays callable
    // (frozen-world-coherent) until the recompiled symbol's new pointer lands
    // via an atomic per-slot `store_slot` — no NULL window, nothing for a
    // stale closure to SIGSEGV through.

    // Displace compiled code on each `ModuleEntry::Def.code` into the session
    // retention pool (§6.3) so the pages stay mapped for in-flight frames and
    // heap closures; without a session context, fall back to dropping (the
    // pre-S101 behaviour — unit-test-only shapes).
    if let Some(mut st) = ctx.symbol_tables.get_mut(module) {
        let mut pool = ctx
            .shared_state
            .map(|s| s.retained_code.lock().unwrap_or_else(|e| e.into_inner()));
        for (name, entry) in st.symbols.iter_mut() {
            let slot = entry.callable_got_slot();
            if let cranelisp_types::ModuleEntry::Def { code, .. } = entry
                && let Some(displaced) = code.take()
                && let Some(pool) = pool.as_mut()
            {
                pool.push(crate::redefine::RetainedCode::frozen(
                    module, name, slot, displaced,
                ));
            }
        }
    }

    // Clear introspection entries for this module.
    let fq_keys: Vec<_> = symbols.iter().map(|sym| {
        let bare = sym.as_ref().rsplit('/').next().unwrap_or(sym.as_ref());
        cranelisp_types::FQSymbol {
            module: module.clone(),
            symbol: cranelisp_types::Symbol::from(bare),
        }
    }).collect();
    if let Some(intr_map) = ctx.introspection {
        for fq in &fq_keys {
            intr_map.remove(fq);
        }
    }
}


#[cfg(test)]
mod tests;
