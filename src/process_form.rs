//! Cluster / per-form processing — the gap-orchestration crossing point.
//!
//! Extracted from `worker.rs` (FIXME 0109 Wave C). This module hosts the
//! shared form-processing family: `process_cluster_once` (the structural
//! prologue, source-ordered macro checkpoints, and ordinary HM-cluster core
//! that `cluster::process_cluster` and the eval path drive) and
//! `process_regular_form` (per-form expand→build accumulation), plus their
//! family-private helpers — structural-form classification + handlers
//! (`classify_form`, `handle_import`/`handle_export`/`handle_mod`/
//! `handle_platform`), macro recognition + checkpoint compilation
//! (`SymbolTableMacroResolver`, `compile_macro_checkpoint`), source-ordered
//! expansion, dependency driving (`drive_module_dep`,
//! `register_dep`, cache-hit load), and module prep/cleanup
//! (`inject_prelude_if_needed`, `wrap_exprs_as_defns`).
//!
//! This is the sole crate-crossing where a `ResolutionGap` value becomes a
//! scheduler call (Principle 1, Principle 7). The codegen/cache subsystem and
//! the worker loops stay in `worker.rs` and call into this module across the
//! module boundary via `process_cluster_once` / `process_regular_form`.
//!
//! Shared infrastructure types (`ModuleCompiler`, `ClusterOnce`) and the
//! typecheck/commit helpers (`build_program_compat`, `check_program_compat*`,
//! `prepare_cluster_commit`) remain in `worker.rs`
//! (they are referenced by both this family and the codegen path / external
//! callers) and are reached here via `crate::worker::*`.

use cranelisp_types::{
    CranelispError, ErrorLocation, Expr, FQSymbol, MatchArm, ModuleAliases, ModuleFullPath,
    ModuleStrategy, Sexp, Span, TopLevel, TypeExpr, TypeRef,
};

use std::collections::BTreeSet;

use crate::scheduler::SourceContinuation;
use crate::worker::{
    ClusterOnce, ModuleCompiler, build_program_compat, check_program_compat, leading_annotation_len,
};

// ---------------------------------------------------------------------------
// Submodules (S87 §1 decomposition). The parent file holds the cluster spine
// (`process_cluster_once` / `finalize_cluster` / `pass2_*` / `process_regular_form`)
// + re-exports of the externally-cited public items so `crate::process_form::X`
// paths stay stable (the compatibility membrane, S87 §5).
// ---------------------------------------------------------------------------

mod cache_restore;
mod dependency;
pub(crate) mod form_dispatch;
mod macro_clause;
mod macro_resolution;
mod platform;

use self::dependency::{
    BlockAction, drive_module_dep, drive_submodules, ensure_prelude_bit, fq_module_is_loaded,
    handle_export, handle_import, handle_mod, inject_prelude_if_needed,
};
use self::platform::handle_platform;
// `register_dep` (the per-dep prologue) lives in `dependency`; `cache_restore`
// reaches it via `super::register_dep`, so it must be in the parent's scope.
use self::dependency::register_dep;
use self::form_dispatch::{
    FormKind, classify_form, record_exports_on_symbol_table, record_macro_introspection,
    record_platform_on_symbol_table, wrap_exprs_as_defns,
};
use self::macro_resolution::{ExpandOutcome, compile_macro_if_needed, try_expand_sexp};

// Re-export externally-cited items so `crate::process_form::X` paths stay stable
// (the compatibility membrane, S87 §1.2 / §5).
use self::dependency::gap_member;
pub(crate) use self::dependency::gap_target_module;
pub(crate) use self::form_dispatch::{
    record_imports_on_symbol_table, record_submodule_on_symbol_table,
};
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
use cranelisp_typecheck::CheckState;
#[cfg(test)]
use cranelisp_types::{Symbol, Visibility};
#[cfg(test)]
use std::path::Path;

// ---------------------------------------------------------------------------
// process_module_forms — source-ordered checkpoints + one ordinary HM cluster
// ---------------------------------------------------------------------------

/// Process one source continuation. A continuation starts at the top on its
/// first attempt and at the first unprocessed form after a committed macro on
/// later attempts.
///
/// Runs the structural prologue once, then walks `sexps` in source order while
/// accumulating ordinary forms on this call's stack frame:
///
/// - **Pass 0** — peel structural forms (`import`/`export`/`mod`/`platform`)
///   and the implicit prelude. A structural dep that is not yet loaded is
///   registered with the scheduler (its sexps ride the dep's work packet) and
///   blocked on (`block_for_typecheck`), then this function returns
///   `ClusterOnce::Gap` with the original source continuation.
/// - **Source walk** — expansion-produced and direct `defmacro` forms are
///   typechecked, compiled, and published immediately as complete checkpoints.
///   Ordinary forms on both sides remain accumulated for one final HM cluster.
///   A dependency gap carries only the already-expanded ordinary prefix and
///   unprocessed source suffix, so a committed macro is never replayed.
/// - **Finalize** — single `check_program_compat` (cluster-mode staging,
///   commit-on-Ok / discard-on-Err). A surviving FQ-auto-load gap is driven;
///   any other gap is a hard error.
///
/// On a `Gap` the worker stores the returned source continuation before it
/// parks, while the eval path carries it in its local retry loop. A gap before
/// the prologue completes retries the original source; a later gap resumes the
/// suffix without re-presenting an already-published macro.
///
/// On `Done` the cluster's expanded program is returned for codegen; the
/// cluster-level REPL/scheduler metadata rides on `ProcessedCluster` (committed
/// via `cluster::insert_cluster`). The per-symbol staging entries already
/// committed to live inside `check_program_compat`.
pub fn process_cluster_once(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    continuation: &SourceContinuation,
    strategy: ModuleStrategy,
    generation_started: bool,
    mut turn_definitions: Option<&mut crate::session_v4::TurnDefinitions>,
) -> Result<ClusterOnce, CranelispError> {
    // In-call-stack working state — rebuilt from the continuation every pass,
    // dropped on a gap. Never lands in a shared map (the S60–S62 heisenbug
    // substrate is gone). `expanded_program` accumulates within THIS pass only.
    let sexps = continuation.forms();
    let mut expanded_program: Vec<TopLevel> = Vec::new();
    let mut prefix = ExpandedPrefix::resuming(continuation);

    // §8.6.4 (FIXME 0514) — the definition-over-(import|export|prelude)
    // rejection is no longer mode-gated here: it moved to the shared typecheck
    // `check_forms` Pass-1 seam, where it fires identically in every mode (the
    // mode-parity MUST) and is the only place that also sees the prelude OUTER
    // scope. The former `additive` flag threaded into the two int-side reject
    // seams is retired; Pass-0 import/export install keeps only §8.6.5 ambiguity
    // detection (including the distinct-terminal prelude-overlap poison).

    // Prologue: strategy setup + static cycle gate + prelude fallback/inject +
    // Pass-0 structural peel + the signature barrier. Any of these can surface a
    // dependency gap; the in-progress frame is dropped (atomic discard, live
    // unchanged) and the caller drives the wait + retry-from-top.
    if !generation_started && let Some(dep) = run_cluster_prologue(ctx, module, sexps, strategy)? {
        return Ok(ClusterOnce::Gap {
            dep,
            continuation: continuation.clone(),
            generation_started: false,
        });
    }

    // --- Pass 2: per-sexp expand-then-check ---
    let pass2_result = pass2_check_bodies_with_expansion(
        ctx,
        module,
        sexps,
        &mut expanded_program,
        &mut prefix,
        &mut turn_definitions,
    )?;

    finish_pass2(
        ctx,
        module,
        sexps,
        &expanded_program,
        &prefix,
        pass2_result,
        &mut turn_definitions,
    )
}

/// What a cluster attempt has expanded so far: the ordinary forms and the
/// modules whose qualified macro heads that expansion recognised
/// (`design/int/int.md` §7.6.2). A resumed attempt starts from the set its
/// continuation carried and re-walks the continuation's forms.
struct ExpandedPrefix {
    forms: Vec<Sexp>,
    macro_lookup_dependencies: BTreeSet<ModuleFullPath>,
}

impl ExpandedPrefix {
    fn resuming(continuation: &SourceContinuation) -> Self {
        ExpandedPrefix {
            forms: Vec::new(),
            macro_lookup_dependencies: continuation.macro_lookup_dependencies().clone(),
        }
    }

    /// The continuation of a gap: this prefix, then `rest`, not yet expanded.
    fn continuation_with(&self, rest: impl IntoIterator<Item = Sexp>) -> SourceContinuation {
        let mut forms = self.forms.clone();
        forms.extend(rest);
        SourceContinuation::resumed(forms, self.macro_lookup_dependencies.clone())
    }
}

/// Cluster prologue: strategy-specific setup (active module, static import
/// closure, GOT clear + prelude fallback/inject on `Replace`), the Pass-0
/// structural-form peel, and the signature barrier. Returns `Some(dep)` when any
/// step surfaces a dependency gap (the caller drops the frame and retries from
/// the top); `None` to proceed to Pass 1.
fn run_cluster_prologue(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    strategy: ModuleStrategy,
) -> Result<Option<ModuleFullPath>, CranelispError> {
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

        // Prelude fallback bit (§8.8.1) — single-sourced via `ensure_prelude_bit`
        // (FIXME 0516 fold-in), fresh-recompute discipline for the Replace path.
        // Then ensure prelude is LOADED so the fallback has a table to consult.
        ensure_prelude_bit(ctx, module, sexps, true);
        if let Some(dep) = inject_prelude_if_needed(ctx, module, sexps)? {
            return Ok(Some(dep));
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
    if let Some(dep) = pass0_peel_structural(ctx, module, sexps)? {
        return Ok(Some(dep));
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
        return Ok(Some(member));
    }
    Ok(None)
}

/// Pass 0 — peel structural forms (`import`/`export`/`mod`/`platform`).
/// Imported symbols must be in scope before Pass-1 checks trait-impl bodies. An
/// unloaded dep is registered + blocked on inside `handle_*` and returned here
/// as `Some(dep)` so the cluster retries from the top once it is live.
fn pass0_peel_structural(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
) -> Result<Option<ModuleFullPath>, CranelispError> {
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
            FormKind::Import(specs) => match handle_import(ctx, module, specs.clone())? {
                BlockAction::Continue => {
                    record_imports_on_symbol_table(ctx, module, &specs);
                }
                BlockAction::Block { dep_module } => return Ok(Some(dep_module)),
            },
            FormKind::Export(specs) => match handle_export(ctx, module, &specs)? {
                BlockAction::Continue => {
                    record_exports_on_symbol_table(ctx, module, &specs);
                }
                BlockAction::Block { dep_module } => return Ok(Some(dep_module)),
            },
            FormKind::Mod(decl) => match handle_mod(ctx, module, &decl)? {
                BlockAction::Continue => {
                    record_submodule_on_symbol_table(ctx, module, &decl);
                }
                BlockAction::Block { dep_module } => return Ok(Some(dep_module)),
            },
            FormKind::Platform(spec) => match handle_platform(ctx, module, &spec)? {
                BlockAction::Continue => {
                    record_platform_on_symbol_table(ctx, module, &spec);
                }
                BlockAction::Block { dep_module } => return Ok(Some(dep_module)),
            },
            _ => {} // Regular, Defmacro — handled in Pass 1 / Pass 2.
        }
    }
    Ok(None)
}

/// Finalize Pass 2: on `Complete`, run `finalize_cluster` then drive declared
/// submodules (FIXME 0342); on `BlockedOnFqModule`, drive the unloaded FQ
/// dependency and surface a gap for retry-from-top.
fn finish_pass2(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    origin_sexps: &[Sexp],
    expanded_program: &[TopLevel],
    prefix: &ExpandedPrefix,
    pass2_result: Pass2Result,
    turn_definitions: &mut Option<&mut crate::session_v4::TurnDefinitions>,
) -> Result<ClusterOnce, CranelispError> {
    match pass2_result {
        Pass2Result::Complete => {
            // Finalize: single `check_program_compat` over the expanded
            // cluster. A surviving FQ-auto-load gap is driven (register +
            // block) and surfaces as `Gap`; any other gap is a hard error.
            let mut outcome =
                finalize_cluster(ctx, module, origin_sexps, expanded_program, prefix)?;
            if let ClusterOnce::Done { processed, .. } = &mut outcome
                && let Some(shared) = ctx.shared_state
            {
                crate::worker::compile_and_publish_processed_without_notify(processed, shared)?;
            }
            if matches!(outcome, ClusterOnce::Done { .. })
                && let Some(definitions) = turn_definitions.as_deref_mut()
            {
                let published: Vec<FQSymbol> = expanded_program
                    .iter()
                    .filter_map(|top| crate::session_v4::definition_result_symbol(module, top))
                    .collect();
                if !definitions.mark_published(&published) {
                    return Err(CranelispError::CodegenError {
                        message: "published definition was absent from the turn receipt"
                            .to_string(),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    });
                }
            }
            // FIXME 0342 — only AFTER the parent's symbols are committed to live
            // (finalize_cluster done) do we drive declared submodules. This is
            // the deferral that lets a submodule's `(import [super [helper]])`
            // resolve the now-live parent symbol. A submodule that needs loading
            // surfaces as a `Gap`; the cluster retries from the top (idempotent —
            // already-loaded submodules are skipped). Both the worker entry
            // (`cluster::process_cluster`) and the REPL entry
            // (`session_v4::process_single_form`) drive this same core.
            if matches!(outcome, ClusterOnce::Done { .. }) {
                let published = SourceContinuation::source(Vec::new());
                store_pool_continuation(ctx, module, &published, true);
                if let Some(dep) = drive_submodules(ctx, module)? {
                    return Ok(ClusterOnce::Gap {
                        dep,
                        continuation: published,
                        generation_started: true,
                    });
                }
            }
            Ok(outcome)
        }
        Pass2Result::BlockedOnFqModule {
            dep_module,
            continuation,
            ref_span: checkpoint_span,
        } => {
            // An FQ reference to an unloaded module surfaced during expansion
            // (Pass 2 macro recognition). Drive the dependency (register + block)
            // with import's file-resolution rules; the cluster retries from the
            // top once it is live (FIXME 0268). 0571 AL-3: attribute a
            // missing-module failure to the REFERENCE SITE (`dep_module/...` in
            // the cluster's forms), not the bogus module-head `0..0` span.
            let ref_span = expanded_program
                .iter()
                .find_map(|tl| match tl {
                    TopLevel::Expr(e) => find_module_qualified_ref_span(e, dep_module.as_ref()),
                    TopLevel::Defn(d) => d
                        .variants
                        .iter()
                        .find_map(|v| find_module_qualified_ref_span(&v.body, dep_module.as_ref())),
                    _ => None,
                })
                .unwrap_or(checkpoint_span);
            store_pool_continuation(ctx, module, &continuation, true);
            drive_module_dep(ctx, module, &dep_module, ref_span)?;
            Ok(ClusterOnce::Gap {
                dep: dep_module,
                continuation,
                generation_started: true,
            })
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
    origin_sexps: &[Sexp],
    expanded_program: &[TopLevel],
    prefix: &ExpandedPrefix,
) -> Result<ClusterOnce, CranelispError> {
    let mut final_working = wrap_exprs_as_defns(expanded_program);

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

    // FIXME 0650 §2.1 (macro-diagnostic-reanchoring.md) — the finalize/typecheck
    // application site of the SAME re-anchor transform the W4 build path uses.
    // A `def`/`const` (stdlib macros) whose EXPANSION typechecks with an error
    // surfaces it here carrying the macro output's SYNTHETIC span (marshal
    // `Span::SYNTHETIC` / `rewrite_spans_unique`'s ≥1M band), anchored at no
    // source byte with no `in expansion of …` provenance. Re-anchor a
    // synthetic-located finalize error to the origin form int holds. Keyed on
    // the SYNTHETIC-LOCATION predicate (outside EVERY origin form's real extent),
    // NEVER on error class — a native finalize error (its span within an origin
    // form) passes through unchanged.
    let mut prepared = None;
    let (maybe_gap, cluster_warnings, unresolved_dispatch, redefinitions) =
        if let Some(shared) = ctx.shared_state {
            match crate::worker::prepare_cluster_commit_with_demands(
                ctx.symbol_tables,
                ctx.module_aliases,
                ctx.prelude_fallback,
                module,
                &final_working,
                expanded_program,
                crate::worker::OwedFacts {
                    reload_demands: &ctx.reload_demands,
                    lookup_dependencies: &prefix.macro_lookup_dependencies,
                },
                shared,
            ) {
                Ok(None) => (None, Vec::new(), Vec::new(), Vec::new()),
                Ok(Some(Err(gap))) => (Some(gap), Vec::new(), Vec::new(), Vec::new()),
                Ok(Some(Ok((mut turn, check)))) => {
                    turn.unresolved_dispatch = check.unresolved_dispatch.clone();
                    prepared = Some(turn);
                    (None, check.warnings, check.unresolved_dispatch, Vec::new())
                }
                Err(error) => return Err(reanchor_finalize_error(error, origin_sexps)),
            }
        } else {
            match check_program_compat(
                ctx.symbol_tables,
                ctx.module_aliases,
                ctx.prelude_fallback,
                module,
                &final_working,
                None,
            ) {
                Ok(result) => result,
                Err(error) => return Err(reanchor_finalize_error(error, origin_sexps)),
            }
        };
    if let Some(gap) = maybe_gap {
        // 0571 (B4/B5 + AL-3): the qualified-reference gap now fires
        // unconditionally on a member-absent abs module (typecheck
        // `resolve_qualified`). INT owns the decision from the module's LIVE
        // state (Principle 3/17 — typecheck stays scheduler-free). The
        // reference-site span makes every diagnostic actionable (AL-3), replacing
        // the `Span::SYNTHETIC` module-head span the wrap reported at.
        //
        // Latent coupling (0609, shim removal): the deleted `phantom_member_diagnostic`
        // int shim once caught a current-module-relative CHILD gap
        // (`<current>.<qualifier>/<member>`) that typecheck's `checker::lookup`
        // synthesised BEFORE probing the absolute module — a member-absent loaded
        // module could survive as a phantom child gap. That shape is now
        // foreclosed: 0571 made member-absent gap unconditionally on the absolute
        // module, and Pass-1 macro recognition hard-errors on `PrivateInaccessible`
        // for a qualified non-macro atom (the de-facto privacy gate). The removal
        // relies on that hard-error path: `checker.rs` `lookup`'s `Err(_)` arm
        // swallows the absolute probe's privacy error into a phantom child gap, so
        // if recognition ever stops hard-erroring there, the honest cure is in
        // typecheck (surface the absolute probe's privacy error from `lookup`) —
        // NOT a re-grown int shim.
        if let Some(dep) = gap_target_module(&gap) {
            let member = gap_member(&gap);
            // Both decisions below report at this one reference site (int.md
            // §6.3.1); the typed gap alone chooses what to load.
            let ref_span = gap_reference_span(
                expanded_program,
                &GapReference {
                    module: &dep,
                    member: &member,
                    referring_module: module,
                    module_aliases: ctx.module_aliases,
                },
            );
            // Module present AND terminal (`fq_module_is_loaded`) ⇒ its
            // signatures are fully published, so the member GENUINELY does not
            // exist ⇒ the honest "module X has no member Y" at the reference
            // site (§8.5.4). Authored via the single `module_has_no_member_error`
            // seam (I4, 0571.2 — the sole author of this diagnostic, and now its
            // sole caller). Never re-drive a terminal module (the member stays
            // absent on every retry — an infinite loop).
            if fq_module_is_loaded(ctx, &dep) {
                return Err(module_has_no_member_error(&dep, &member, ref_span));
            }
            // Absent OR present-but-non-terminal ⇒ drive it (register + park): a
            // not-yet-loaded module loads then re-drives; a present-but-non-
            // terminal module parks via `drive_module_dep`'s already-loaded /
            // `block_dep` arm, whose `block_for_typecheck` acyclicity check
            // converts a genuine FQ cycle into the honest circular-dependency
            // error (B4/B5). A missing-module file surfaces `drive_module_dep`'s
            // "module not found" at the reference span (AL-3).
            let continuation = prefix.continuation_with([]);
            store_pool_continuation(ctx, module, &continuation, true);
            drive_module_dep(ctx, module, &dep, ref_span)?;
            return Ok(ClusterOnce::Gap {
                dep,
                continuation,
                generation_started: true,
            });
        }
        // Not an FQ-module gap we can act on — surface a hard error so the
        // failure is not silently swallowed.
        return Err(CranelispError::TypeError {
            message: format!("unresolved cross-module reference: {gap:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

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
    let mut processed =
        crate::cluster::ProcessedCluster::from_parts(cluster_warnings, Vec::new(), Vec::new());
    processed.set_redefinitions(redefinitions);
    // S101: the commit gate's redefinition classifications ride the cluster
    // carrier back to the driver; the eval path runs the dependent-
    // recompilation transaction for `AbiChanging` outcomes after the target's
    // own codegen succeeds (design §13).
    // 0611 carrier — the return-poly dispatch sites still unresolved at
    // finalize (EMPTY for every valid program). The eval driver consults these
    // at the `__expr` eval-result boundary (class (b), Principle 19): a bare
    // `(zed)` reaching the eval path dies with the §3.11 ambiguity instead of
    // leaking the backend `__expr`-has-no-GOT-slot error.
    processed.set_unresolved_dispatch(unresolved_dispatch);
    if let Some(prepared) = prepared {
        processed.set_prepared(prepared);
    } else if ctx.shared_state.is_some() {
        processed.pending_codegen_notification = Some((module.clone(), Vec::new()));
    }

    Ok(ClusterOnce::Done { processed, program })
}

/// The single author of the §8.5.4 "module X has no member Y" diagnostic (I4,
/// 0571.2). The FQ-gap decision arm (`finalize_cluster`, a member-absent
/// terminal module) is its sole caller, so the diagnostic has exactly one
/// authoring site — no display-envelope mirror (Principle 7). `span` is the
/// arm's [`gap_reference_span`].
fn module_has_no_member_error(module: &ModuleFullPath, member: &str, span: Span) -> CranelispError {
    CranelispError::ModuleError {
        message: format!("module '{module}' has no member '{member}'"),
        location: ErrorLocation::from_span_file(span, None),
    }
}

/// A gap's `module/member` identity together with the scope the cluster wrote
/// its reference in.
struct GapReference<'a> {
    module: &'a ModuleFullPath,
    member: &'a str,
    referring_module: &'a ModuleFullPath,
    module_aliases: &'a ModuleAliases,
}

impl GapReference<'_> {
    /// The gap's module is the qualifier as written (a member missing from a
    /// present module) or its alias substitution (an absent module, spec
    /// §8.6.6), and the gap does not say which, so either form matches.
    fn is_written_as(&self, written: WrittenRef<'_>) -> bool {
        written.qualified().is_some_and(|(qualifier, member)| {
            let qualifier = ModuleFullPath::from(qualifier);
            member == self.member
                && (qualifier == *self.module
                    || cranelisp_types::substitute_module_alias(
                        self.module_aliases,
                        self.referring_module,
                        &qualifier,
                    ) == *self.module)
        })
    }
}

/// A reference as the program wrote it, offered to a reference-site predicate.
#[derive(Clone, Copy)]
enum WrittenRef<'a> {
    /// A symbol spelling: an `Expr::Var` name or a trait-signature tail symbol.
    Spelled(&'a str),
    /// A type-position head with its as-written qualification.
    Type(&'a TypeRef),
}

impl<'a> WrittenRef<'a> {
    /// `(qualifier, member)` when the reference is qualified. A spelling splits
    /// at its first `/` with both halves non-empty, the value resolver's grammar
    /// (`cranelisp_types` `resolve::split_qualified`, Principle 16).
    fn qualified(self) -> Option<(&'a str, &'a str)> {
        match self {
            WrittenRef::Spelled(name) => name
                .split_once('/')
                .filter(|(qualifier, member)| !qualifier.is_empty() && !member.is_empty()),
            WrittenRef::Type(type_ref) => type_ref
                .module
                .as_ref()
                .map(|qualifier| (qualifier.as_ref(), type_ref.name.as_ref())),
        }
    }
}

/// The span of the first reference to `reference` in `program`, in value or
/// type position, or `Span::SYNTHETIC` when nothing matches (int.md §6.3.1).
fn gap_reference_span(program: &[TopLevel], reference: &GapReference<'_>) -> Span {
    let pred = |written: WrittenRef<'_>| reference.is_written_as(written);
    program
        .iter()
        .find_map(|tl| find_reference_span_in_toplevel(tl, &pred))
        .unwrap_or(Span::SYNTHETIC)
}

/// The first matching reference in a top-level form. A type reference carries
/// no span, so it reports its innermost spanned carrier. Trait references
/// (an impl's trait, bounds, constraints) raise no gap and are not searched.
fn find_reference_span_in_toplevel(
    tl: &TopLevel,
    pred: &impl Fn(WrittenRef<'_>) -> bool,
) -> Option<Span> {
    match tl {
        TopLevel::Expr(e) => find_reference_span(e, pred),
        TopLevel::Defn(d) => find_reference_span_in_defn(d, pred),
        TopLevel::TypeDef { constructors, .. } => constructors
            .iter()
            .flat_map(|ctor| &ctor.fields)
            .find(|field| type_expr_mentions(&field.type_expr, pred))
            .map(|field| field.span),
        TopLevel::TraitDecl(decl) => decl.methods.iter().find_map(|method| {
            if method
                .params
                .iter()
                .any(|(_, ty)| type_expr_mentions(ty, pred))
            {
                Some(method.span)
            } else {
                find_symbol_span(&method.tail, pred)
            }
        }),
        TopLevel::TraitImpl(impl_) => {
            if type_expr_mentions(&impl_.target, pred) {
                Some(impl_.span)
            } else {
                impl_
                    .methods
                    .iter()
                    .find_map(|method| find_reference_span_in_defn(method, pred))
            }
        }
    }
}

fn find_reference_span_in_defn(
    defn: &cranelisp_types::Defn,
    pred: &impl Fn(WrittenRef<'_>) -> bool,
) -> Option<Span> {
    defn.variants.iter().find_map(|variant| {
        if annotations_mention(&variant.params, pred) {
            Some(variant.span)
        } else {
            find_reference_span(&variant.body, pred)
        }
    })
}

fn annotations_mention(
    params: &[(cranelisp_types::Symbol, Option<TypeExpr>)],
    pred: &impl Fn(WrittenRef<'_>) -> bool,
) -> bool {
    params
        .iter()
        .filter_map(|(_, annotation)| annotation.as_ref())
        .any(|annotation| type_expr_mentions(annotation, pred))
}

fn type_expr_mentions(ty: &TypeExpr, pred: &impl Fn(WrittenRef<'_>) -> bool) -> bool {
    match ty {
        TypeExpr::Named(head) => pred(WrittenRef::Type(head)),
        TypeExpr::Applied(head, args) => {
            pred(WrittenRef::Type(head)) || args.iter().any(|arg| type_expr_mentions(arg, pred))
        }
        TypeExpr::FnType(params, ret) => {
            params.iter().any(|param| type_expr_mentions(param, pred))
                || type_expr_mentions(ret, pred)
        }
        TypeExpr::SelfType | TypeExpr::TypeVar(_) | TypeExpr::Bounds(_) => false,
    }
}

/// A trait method's still-unclassified tail: a matching symbol reports its own
/// span.
fn find_symbol_span(sexp: &Sexp, pred: &impl Fn(WrittenRef<'_>) -> bool) -> Option<Span> {
    match sexp {
        Sexp::Symbol(name, span) => pred(WrittenRef::Spelled(name)).then_some(*span),
        Sexp::List(items, _) | Sexp::Bracket(items, _) => {
            items.iter().find_map(|item| find_symbol_span(item, pred))
        }
        Sexp::Annotated {
            annotation,
            subject,
            ..
        } => find_symbol_span(annotation, pred).or_else(|| find_symbol_span(subject, pred)),
        Sexp::Int(..) | Sexp::Float(..) | Sexp::Bool(..) | Sexp::Str(..) | Sexp::Comment(..) => {
            None
        }
    }
}

/// The span of the FIRST `Expr::Var` whose name is qualified by `module` (i.e.
/// `module/...`) — the reference-site span for a missing-module / member-absent
/// FQ diagnostic (0571 AL-3) when only the module (not the member) is known at
/// the seam (the expand-time `BlockedOnFqModule`).
fn find_module_qualified_ref_span(expr: &Expr, module: &str) -> Option<Span> {
    let prefix = format!("{module}/");
    find_reference_span(
        expr,
        &|written| matches!(written, WrittenRef::Spelled(name) if name.starts_with(&prefix)),
    )
}

/// The span of the first reference in `expr` that satisfies `pred`, in program
/// order. The single expression walk both the gap ([`gap_reference_span`]) and
/// module-prefix ([`find_module_qualified_ref_span`]) lookups share (P7). A
/// lambda-parameter or inline annotation reports the lambda or annotation.
fn find_reference_span(expr: &Expr, pred: &impl Fn(WrittenRef<'_>) -> bool) -> Option<Span> {
    let arm = |e: &Expr| find_reference_span(e, pred);
    match expr {
        Expr::Var { name, span, .. } => pred(WrittenRef::Spelled(name.as_ref())).then_some(*span),
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. } => None,
        Expr::Lambda {
            params, body, span, ..
        } => {
            if annotations_mention(params, pred) {
                Some(*span)
            } else {
                arm(body)
            }
        }
        Expr::Annotate {
            annotation,
            expr: body,
            span,
            ..
        } => {
            if type_expr_mentions(annotation, pred) {
                Some(*span)
            } else {
                arm(body)
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => bindings
            .iter()
            .find_map(|(_, e)| arm(e))
            .or_else(|| arm(body)),
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => arm(cond)
            .or_else(|| arm(then_branch))
            .or_else(|| arm(else_branch)),
        Expr::Trace { body, .. } => arm(body),
        Expr::Apply { callee, args, .. } => arm(callee).or_else(|| args.iter().find_map(&arm)),
        Expr::Match {
            scrutinee, arms, ..
        } => arm(scrutinee).or_else(|| arms.iter().find_map(|a: &MatchArm| arm(&a.body))),
        Expr::VecLit { elements, .. } => elements.iter().find_map(&arm),
        Expr::ConstrADT { fields, .. } => fields.iter().find_map(&arm),
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => arm(launched).or_else(|| arm(continuation)),
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
        continuation: SourceContinuation,
        ref_span: Span,
    },
}

enum RegularFormResult {
    Complete(Vec<Sexp>),
    Blocked {
        dep_module: ModuleFullPath,
        continuation: Vec<Sexp>,
        ref_span: Span,
    },
}

enum DefinitionEmissionMarker {
    Ordinary,
    PublishedMacro(FQSymbol),
}

fn record_turn_definition(
    turn_definitions: &mut Option<&mut crate::session_v4::TurnDefinitions>,
    symbol: FQSymbol,
    published: bool,
) {
    if let Some(definitions) = turn_definitions.as_deref_mut() {
        definitions.record(symbol, published);
    }
}

/// Merge the typed ordinary forms and the already-published macro checkpoints
/// in their actual emitted order. `ordinary` markers correspond one-for-one
/// with the frontend-built top levels; macro markers already carry their
/// canonical identity from the checkpoint that published them.
fn record_definition_emissions(
    module: &ModuleFullPath,
    markers: &[DefinitionEmissionMarker],
    built: &[TopLevel],
    turn_definitions: &mut Option<&mut crate::session_v4::TurnDefinitions>,
) -> Result<(), CranelispError> {
    let mut ordinary = built.iter();
    for marker in markers {
        match marker {
            DefinitionEmissionMarker::Ordinary => {
                let Some(top) = ordinary.next() else {
                    return Err(CranelispError::CodegenError {
                        message: "definition emission order did not match the built program"
                            .to_string(),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    });
                };
                if let Some(symbol) = crate::session_v4::definition_result_symbol(module, top) {
                    record_turn_definition(turn_definitions, symbol, false);
                }
            }
            DefinitionEmissionMarker::PublishedMacro(symbol) => {
                record_turn_definition(turn_definitions, symbol.clone(), true);
            }
        }
    }
    if ordinary.next().is_some() {
        return Err(CranelispError::CodegenError {
            message: "built program contained an untracked definition emission".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }
    Ok(())
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
    expanded_program: &mut Vec<TopLevel>,
    prefix: &mut ExpandedPrefix,
    turn_definitions: &mut Option<&mut crate::session_v4::TurnDefinitions>,
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
                let info = cranelisp_frontend::parse_defmacro(sexp)?;
                if let Some(gap) = compile_macro_if_needed(
                    ctx,
                    module,
                    &info,
                    sexp,
                    &prefix.macro_lookup_dependencies,
                )? {
                    let dep_module = macro_checkpoint_gap_target(ctx, &gap, sexp.span())?;
                    return Ok(Pass2Result::BlockedOnFqModule {
                        dep_module,
                        continuation: prefix.continuation_with(sexps[idx..].iter().cloned()),
                        ref_span: sexp.span(),
                    });
                }
                let authored_source = verbatim_source_slice(ctx, module, sexp);
                record_macro_introspection(
                    ctx.introspection,
                    module,
                    &info.name,
                    sexp,
                    sexp,
                    authored_source,
                );
                record_turn_definition(
                    turn_definitions,
                    FQSymbol {
                        module: module.clone(),
                        symbol: info.name,
                    },
                    true,
                );
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
                let (annotation_prefix, form_idx) = if ann_len > 0 && idx + ann_len < sexps.len() {
                    (&sexps[idx..idx + ann_len], idx + ann_len)
                } else {
                    (&sexps[idx..idx], idx)
                };
                let next = idx.max(form_idx) + 1;
                match process_regular_form(
                    ctx,
                    module,
                    annotation_prefix,
                    &sexps[form_idx],
                    expanded_program,
                    &mut prefix.macro_lookup_dependencies,
                    turn_definitions,
                )? {
                    RegularFormResult::Complete(forms) => prefix.forms.extend(forms),
                    RegularFormResult::Blocked {
                        dep_module,
                        continuation: local,
                        ref_span,
                    } => {
                        let rest = local.into_iter().chain(sexps[next..].iter().cloned());
                        return Ok(Pass2Result::BlockedOnFqModule {
                            dep_module,
                            continuation: prefix.continuation_with(rest),
                            ref_span,
                        });
                    }
                }
                idx = next;
            }
        }
    }
    Ok(Pass2Result::Complete)
}

fn macro_checkpoint_gap_target(
    ctx: &ModuleCompiler,
    gap: &cranelisp_types::ResolutionGap,
    span: Span,
) -> Result<ModuleFullPath, CranelispError> {
    let dep = gap_target_module(gap).ok_or_else(|| CranelispError::TypeError {
        message: format!("unresolved cross-module reference: {gap:?}"),
        location: ErrorLocation::from_span(span),
    })?;
    if dependency::fq_module_is_loaded(ctx, &dep) {
        return Err(CranelispError::TypeError {
            message: format!("unresolved cross-module reference: {gap:?}"),
            location: ErrorLocation::from_span(span),
        });
    }
    Ok(dep)
}

fn store_pool_continuation(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    continuation: &SourceContinuation,
    generation_started: bool,
) {
    if !ctx.eval_driven {
        ctx.scheduler
            .set_source_continuation(module, continuation.clone(), generation_started);
    }
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

/// `true` iff `loc`'s byte range is OUTSIDE the origin form's real source extent
/// — the FIXME 0650 synthetic-location predicate (`macro-diagnostic-reanchoring.md`
/// §3). A synthetic span maps to no real source byte, so it is never a useful
/// diagnostic location; a real span WITHIN the origin form's extent passes the
/// predicate and is left untouched. Structural, NOT classificatory — it catches
/// BOTH synthetic flavours (`Span::SYNTHETIC` = `(0,0)`, and the
/// `rewrite_spans_unique` ≥1M band) without hard-coding the 1M constant: any
/// zero/negative-width span, or one starting before / ending after the origin's
/// `[start,end)`, is outside the extent.
fn location_outside_extent(loc: Span, origin: Span) -> bool {
    loc.end <= loc.start || loc.start < origin.start || loc.end > origin.end
}

/// Re-anchor a SYNTHETIC-located diagnostic from macro-expansion output to the
/// origin form's real span, appending expansion provenance (FIXME 0650,
/// `macro-diagnostic-reanchoring.md`). A diagnostic already located WITHIN the
/// origin extent (a native-form error) passes through UNCHANGED — the predicate
/// must not touch already-located diagnostics. int enriches the LOCATION and
/// APPENDS context; it never re-phrases the frontend message (Principle 7/19).
///
/// Pure `(error, origin_span, origin_form) → error` transform (Principle 5,
/// unit-testable with no session).
fn reanchor_expansion_diagnostic(
    err: CranelispError,
    origin: Span,
    origin_form: &Sexp,
) -> CranelispError {
    if !location_outside_extent(err.span(), origin) {
        return err; // already located within the origin form — leave verbatim
    }
    // Name the written form (the origin int holds), truncated so a large form
    // does not flood the diagnostic. Never the synthesized head — the origin.
    let mut head = origin_form.format_flat();
    if head.chars().count() > 48 {
        head = head.chars().take(45).collect::<String>() + "…";
    }
    let context = format!("\n  in expansion of `{head}`");
    let message = format!("{}{}", err.message(), context);
    // Re-anchor the location to the origin span; clear the stale synthetic
    // `line_col`/`context` so the formatter recomputes from the origin span.
    let mut location = err.location().clone();
    location.span = origin;
    location.line_col = None;
    location.context = None;
    rebuild_error_with(err, message, location)
}

/// Re-anchor a SYNTHETIC-located FINALIZE-path (typecheck) diagnostic to its
/// origin form (FIXME 0650 §2.1 — the `check_program_compat` application site of
/// the existing pure transform). The finalize check runs over the fully-expanded
/// cluster; an error whose `location` is SYNTHETIC (outside EVERY origin form's
/// real byte extent) came from macro-expansion output and is re-anchored to the
/// origin form int holds. An error located WITHIN some origin form's extent is a
/// native diagnostic — returned unchanged (the predicate must not touch located
/// diagnostics).
///
/// Origin attribution: a `def`/`const` cluster is a SINGLE origin form, so the
/// lone form is the exact anchor. For a rare multi-form cluster whose synthetic
/// node cannot be attributed to one form, fall back to the FIRST origin form (a
/// real, if coarse, location always beats a no-source-byte location, §2.1).
fn reanchor_finalize_error(err: CranelispError, origin_sexps: &[Sexp]) -> CranelispError {
    let loc = err.span();
    // Native: the error's span falls WITHIN some origin form's real extent — the
    // diagnostic is already located; leave it verbatim.
    if origin_sexps
        .iter()
        .any(|s| !location_outside_extent(loc, s.span()))
    {
        return err;
    }
    // Synthetic (outside every origin form) — it came from expansion output.
    // Re-anchor to the origin form (single-form cluster → that form; else first).
    match origin_sexps.first() {
        Some(origin) => reanchor_expansion_diagnostic(err, origin.span(), origin),
        None => err,
    }
}

/// Reconstruct `err` preserving its variant with a new message + location.
/// `Platform(p)` passes through unchanged (its coordinates are rewritten at the
/// loader seam, not here).
///
/// Every current variant is matched EXPLICITLY. `CranelispError` is
/// `#[non_exhaustive]` (it lives in `cranelisp-types`), so a wildcard arm is
/// mandatory — but it must not SILENTLY lose re-anchoring: a future message-
/// bearing variant reaching here trips a `debug_assert!` (so it is wired
/// explicitly) and still preserves the re-anchored diagnostic in release rather
/// than dropping the provenance (0667).
fn rebuild_error_with(
    err: CranelispError,
    message: String,
    location: ErrorLocation,
) -> CranelispError {
    match err {
        CranelispError::ParseError { .. } => CranelispError::ParseError { message, location },
        CranelispError::TypeError { .. } => CranelispError::TypeError { message, location },
        CranelispError::CodegenError { .. } => CranelispError::CodegenError { message, location },
        CranelispError::ModuleError { .. } => CranelispError::ModuleError { message, location },
        CranelispError::MacroError { .. } => CranelispError::MacroError { message, location },
        CranelispError::Platform(p) => CranelispError::Platform(p),
        _ => {
            debug_assert!(
                false,
                "rebuild_error_with: unhandled CranelispError variant — re-anchoring \
                 would be silently lost; add an explicit arm (0667)"
            );
            // Release: preserve the re-anchored diagnostic rather than drop it.
            CranelispError::ModuleError { message, location }
        }
    }
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
    expanded_program: &mut Vec<TopLevel>,
    macro_lookup_dependencies: &mut BTreeSet<ModuleFullPath>,
    turn_definitions: &mut Option<&mut crate::session_v4::TurnDefinitions>,
) -> Result<RegularFormResult, CranelispError> {
    process_regular_form_with_origin(
        ctx,
        module,
        annotation_prefix,
        sexp,
        sexp,
        expanded_program,
        macro_lookup_dependencies,
        turn_definitions,
    )
}

#[allow(clippy::too_many_arguments)] // within the src/ eight-parameter budget
fn process_regular_form_with_origin(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    annotation_prefix: &[Sexp],
    sexp: &Sexp,
    authored_origin: &Sexp,
    expanded_program: &mut Vec<TopLevel>,
    macro_lookup_dependencies: &mut BTreeSet<ModuleFullPath>,
    turn_definitions: &mut Option<&mut crate::session_v4::TurnDefinitions>,
) -> Result<RegularFormResult, CranelispError> {
    // A literal top-level `begin` is itself an ordinary syntactic form, but
    // its members are separate source-order checkpoint positions. Expanding
    // the whole list before walking its members would resolve later calls
    // against the pre-begin table and miss a defmacro committed by an earlier
    // member. Walk the recursively-flattened members here instead, retaining
    // the outer begin as their single persistence authority.
    if annotation_prefix.is_empty() && cranelisp_frontend::is_begin(sexp) {
        let forms = cranelisp_frontend::flatten_begin(sexp.clone());
        let mut ordinary = Vec::new();
        for (index, form) in forms.iter().enumerate() {
            if cranelisp_frontend::is_defmacro(form) {
                let info = cranelisp_frontend::parse_defmacro(form)?;
                if let Some(gap) =
                    compile_macro_if_needed(ctx, module, &info, form, macro_lookup_dependencies)?
                {
                    let mut continuation = ordinary;
                    continuation.extend_from_slice(&forms[index..]);
                    return Ok(RegularFormResult::Blocked {
                        dep_module: macro_checkpoint_gap_target(ctx, &gap, form.span())?,
                        continuation,
                        ref_span: form.span(),
                    });
                }
                record_macro_introspection(
                    ctx.introspection,
                    module,
                    &info.name,
                    form,
                    authored_origin,
                    verbatim_source_slice(ctx, module, authored_origin),
                );
                record_turn_definition(
                    turn_definitions,
                    FQSymbol {
                        module: module.clone(),
                        symbol: info.name,
                    },
                    true,
                );
                continue;
            }
            match process_regular_form_with_origin(
                ctx,
                module,
                &[],
                form,
                authored_origin,
                expanded_program,
                macro_lookup_dependencies,
                turn_definitions,
            )? {
                RegularFormResult::Complete(forms) => ordinary.extend(forms),
                RegularFormResult::Blocked {
                    dep_module,
                    continuation: local,
                    ref_span,
                } => {
                    ordinary.extend(local);
                    ordinary.extend_from_slice(&forms[index + 1..]);
                    return Ok(RegularFormResult::Blocked {
                        dep_module,
                        continuation: ordinary,
                        ref_span,
                    });
                }
            }
        }
        return Ok(RegularFormResult::Complete(ordinary));
    }

    // `deftype` and `deftrait` contain declaration binders and type syntax,
    // neither of which is an expression reference. Validate their raw shape
    // through the frontend before the recursive macro resolver sees any child.
    // This keeps the frontend's single qualified-binder diagnostic authority
    // while still allowing the ordinary expansion pass to visit genuine
    // expression positions in a valid declaration (for example, a default
    // trait-method body).
    if is_binder_rich_declaration(sexp) {
        build_program_compat(std::slice::from_ref(sexp))?;
    }

    // Try macro expansion on the bound form (the annotation prefix is never a
    // macro head — it is the `:Type` token that binds this form per BC §1
    // invariant 9, and is prepended below so the frontend's `build_forms`
    // performs the `Expr::Annotate` pairing).
    let effective_sexp = match try_expand_sexp(ctx, module, sexp)? {
        ExpandOutcome::Expanded {
            sexp: expanded,
            macro_lookup_dependencies: recognised,
        } => {
            macro_lookup_dependencies.extend(recognised);
            expanded
        }
        ExpandOutcome::BlockedOnFqModule(dep) => {
            // Nothing has been appended to `expanded_program` for this form —
            // the caller will resume it after loading `dep`.
            return Ok(RegularFormResult::Blocked {
                dep_module: dep,
                continuation: annotation_prefix
                    .iter()
                    .cloned()
                    .chain(std::iter::once(sexp.clone()))
                    .collect(),
                ref_span: sexp.span(),
            });
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
    let mut emission_markers = Vec::new();
    for (form_index, form) in flattened.iter().enumerate() {
        if cranelisp_frontend::is_defmacro(&form) {
            let info = cranelisp_frontend::parse_defmacro(&form)?;
            let intr = ctx.introspection;
            // S102 CS-D1 (origin-uniform recording): a defmacro reaching this
            // loop is never the whole top-level form (direct defmacros route
            // through Pass 1's `separate_macros`) — it is an expansion product
            // or a literal-`begin` member. The regen authority is therefore
            // the ORIGINAL outer form `sexp`, exactly what the sibling defn
            // records below — one turn, one authored form, one emission.
            let authored_source = verbatim_source_slice(ctx, module, authored_origin);
            if let Some(gap) =
                compile_macro_if_needed(ctx, module, &info, form, macro_lookup_dependencies)?
            {
                let built_prefix = if emission_markers
                    .iter()
                    .any(|marker| matches!(marker, DefinitionEmissionMarker::Ordinary))
                {
                    build_program_compat(&regular_sexps)?
                } else {
                    Vec::new()
                };
                record_definition_emissions(
                    module,
                    &emission_markers,
                    &built_prefix,
                    turn_definitions,
                )?;
                let mut continuation = regular_sexps.clone();
                continuation.extend_from_slice(&flattened[form_index..]);
                let dep_module = macro_checkpoint_gap_target(ctx, &gap, form.span())?;
                return Ok(RegularFormResult::Blocked {
                    dep_module,
                    continuation,
                    ref_span: form.span(),
                });
            }
            record_macro_introspection(
                intr,
                module,
                &info.name,
                form,
                authored_origin,
                authored_source,
            );
            emission_markers.push(DefinitionEmissionMarker::PublishedMacro(FQSymbol {
                module: module.clone(),
                symbol: info.name,
            }));
        } else {
            regular_sexps.push(form.clone());
            emission_markers.push(DefinitionEmissionMarker::Ordinary);
        }
    }

    // If only the annotation prefix remains (the bound form expanded entirely
    // into defmacros), there is nothing to build — but that is a degenerate
    // shape that cannot arise (an annotation binds an expression form, not a
    // defmacro). Guard against an orphan prefix reaching `build_forms`.
    if regular_sexps.len() == annotation_prefix.len() {
        return Ok(RegularFormResult::Complete(Vec::new()));
    }

    // FIXME 0650 (macro-diagnostic-reanchoring.md) — the int-side re-anchoring
    // seam. When this build is over MACRO-EXPANSION OUTPUT (`effective_sexp` is
    // `Some`), every sexp carries a SYNTHETIC span (marshal `Span::SYNTHETIC` +
    // `rewrite_spans_unique`'s ≥1M band), so a frontend fold reject (e.g. the W3
    // qualified-binder-head reject on `(defn fmt/x-def …)`) surfaces a diagnostic
    // whose `location` maps to no source byte. Re-anchor it to the ORIGIN form's
    // real span (`sexp`, the pre-expansion form int holds) and APPEND expansion
    // context — never re-phrase the frontend message (Principle 7/19). Keyed on
    // the SYNTHETIC-LOCATION predicate ("outside the origin form's real source
    // extent"), NEVER on error class/message sniffing (a `/review` REJECT). A
    // native form (`effective_sexp == None`) keeps its real span untouched.
    let built = match build_program_compat(&regular_sexps) {
        Ok(built) => built,
        Err(e) if effective_sexp.is_some() => {
            return Err(reanchor_expansion_diagnostic(e, sexp.span(), sexp));
        }
        Err(e) => return Err(e),
    };
    record_definition_emissions(module, &emission_markers, &built, turn_definitions)?;
    let working = wrap_exprs_as_defns(&built);

    // Per Decision 44's 2026-05-13 third amendment, the per-form
    // `check_form(Register)` + `check_form(CheckBody)` calls are no longer
    // exposed; typecheck is now driven once over the cluster via
    // `check_program_compat` in `finalize_module`. The per-form work loop
    // below remains in place for the introspection + scheduler-notification
    // bookkeeping (which is `int`-side, not typecheck-side) — accumulator
    // mutation is silenced here.
    for form in &working {
        // Populate introspection for REPL slash commands (--repl only).
        if let Some(intr_map) = ctx.introspection
            && let TopLevel::Defn(defn) = form
        {
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
                let src = verbatim_source_slice(ctx, module, authored_origin);
                entry.source =
                    src.or_else(|| Some(crate::pretty::pretty_print_plain(authored_origin)));
            }
            entry.sexp = Some(authored_origin.clone());
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
    Ok(RegularFormResult::Complete(regular_sexps))
}

/// Declaration forms whose binder/type slots must be validated before the
/// expression-oriented macro walk. Recognition is deliberately structural;
/// the frontend remains the sole authority for the declaration's grammar.
fn is_binder_rich_declaration(sexp: &Sexp) -> bool {
    let Sexp::List(items, _) = sexp else {
        return false;
    };
    matches!(
        items.first(),
        Some(Sexp::Symbol(head, _))
            if matches!(head.as_str(), "deftype" | "deftype-" | "deftrait" | "deftrait-")
    )
}

#[cfg(test)]
mod tests;
