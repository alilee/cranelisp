// Worker functions for the v4 scheduler-driven pipeline (Steps 3-5).
//
// `process_module_forms` — drives two-pass typecheck for a single module,
//   with per-sexp macro expansion interleaved in Pass 2 (Step 4).
//   Lazily discovers dependencies (imports, prelude, platform) in Step 5.
// `inline_jit_codegen_for_module` — unified JIT codegen entry point that
//   calls `cranelisp_backend::compile_to_module` (Sprint 56 Wave 2).
// `priority_worker_loop_shared` — dispatches work items from the scheduler;
//   runs on each spawned persistent priority worker thread. Sprint 59
//   Workstream A collapsed the inline variant onto this one.

use std::path::{Path, PathBuf};

#[cfg(test)]
use cranelisp_types::Defn;
use cranelisp_types::{
    Binding, CallableOrigin, CallableTarget, CranelispError, Decl, ErrorLocation, InstanceLink,
    Life, ModuleFullPath, MonoDemand, Realization, Sexp, Span, StagedPublicationDecision, Symbol,
    TopLevel,
};

use cranelisp_typecheck::CheckState;

pub(crate) struct PreparedCommit {
    module: ModuleFullPath,
    staging: crate::code::SessionSymbolTable,
    decisions: Vec<StagedPublicationDecision>,
    tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    targets: Vec<CallableTarget>,
    outcomes: Vec<crate::redefine::RedefinitionOutcome>,
    pub(crate) unresolved_dispatch: Vec<cranelisp_typecheck::UnresolvedDispatchSite>,
}

struct PreparedCompilation {
    jit: std::sync::Arc<cranelisp_backend::jit::Jit>,
    clif_ir: String,
    code_size: usize,
    drop_glues: std::collections::HashMap<
        cranelisp_types::ConcreteType,
        cranelisp_backend::DropGlueArtifact,
    >,
}

#[derive(Clone)]
#[allow(dead_code)] // consumed by the Sprint-116 result-owner seam
pub(crate) struct FreshJitDropGlue {
    pub(crate) artifact: cranelisp_backend::DropGlueArtifact,
    pub(crate) owner: crate::code::Code,
}

struct PreparedCheck {
    staging: crate::code::SessionSymbolTable,
    result: cranelisp_typecheck::CheckResult,
}

fn binding_is_definition(binding: &Binding<crate::code::Code>) -> bool {
    matches!(
        binding.declaration,
        Decl::Callable(_) | Decl::Overloaded(_) | Decl::Macro(_)
    )
}

fn binding_first_slot(binding: &Binding<crate::code::Code>) -> Option<usize> {
    let life_slot = |life: &Life<crate::code::Code>| match life {
        Life::Concrete { slot, .. } | Life::Broken { slot, .. } => Some(slot.index()),
        _ => None,
    };
    match &binding.declaration {
        Decl::Callable(callable) => life_slot(&callable.arm.life),
        Decl::Overloaded(declaration) => declaration
            .arms
            .iter()
            .find_map(|arm| life_slot(&arm.callable.life)),
        Decl::Macro(declaration) => declaration
            .clauses
            .iter()
            .find_map(|clause| life_slot(&clause.callable.life)),
        _ => None,
    }
}

fn callable_target_owner(target: &CallableTarget) -> Option<&cranelisp_types::FQSymbol> {
    match target {
        CallableTarget::Binding(owner)
        | CallableTarget::OverloadArm { owner, .. }
        | CallableTarget::MacroClause { owner, .. } => Some(owner),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Build-form + check-forms compatibility helpers (S66 Wave 3a-β)
// ---------------------------------------------------------------------------

/// Drop-in replacement for the retired `cranelisp_frontend::build_program`.
///
/// Flattens any `(begin …)` clusters (the orchestrator's contract — `build_form`
/// and `build_forms` both reject `begin`) then delegates the flattened form
/// slice to `cranelisp_frontend::build_forms`, which performs the per-form
/// dispatch AND the top-level `:Type`-pairing.
///
/// Annotation-pairing is frontend-owned in EVERY position (BC §1 invariant 9;
/// S81 ruling, FIXME 0329). int does NOT pair a leading `:Type` with the
/// following form in this loop — it flattens `begin` (its orchestration
/// contract) and hands the flattened slice to `build_forms`, which pairs a
/// leading `:Type` sexp with the form it precedes into a `TopLevel::Expr`
/// carrying an `Expr::Annotate`, and otherwise delegates per-sexp to
/// `build_form`/`build_expr`. This closes the prior split-across-two-crates
/// state where the pairing helper lived in frontend but the top-level driving
/// lived here per-sexp and never paired (Principle 7 — single source of truth).
///
/// Build is mode-agnostic. `(trace ...)` in `--link` standalone-binary mode
/// fails at link time via the architecture's natural missing-symbol detection
/// (the trace runtime is not bundled into the staticlib produced by
/// exe-bundle); no frontend pre-pass check is needed. See
/// spec/04-expressions.md §4.12.9.
pub(crate) fn build_program_compat(sexps: &[Sexp]) -> Result<Vec<TopLevel>, CranelispError> {
    // `(begin form₁ … formN)` clusters flatten into their inner forms — both
    // `build_form` and `build_forms` reject `begin` per their facade. This
    // preserves the pre-S66 `build_program` semantics where `flatten_begin`
    // ran before per-form dispatch. Flattening is int's orchestration contract;
    // the per-form dispatch + `:Type`-pairing it hands to `build_forms`.
    let mut flattened: Vec<Sexp> = Vec::with_capacity(sexps.len());
    for sexp in sexps {
        flattened.extend(cranelisp_frontend::flatten_begin(sexp.clone()));
    }
    cranelisp_frontend::build_forms(&flattened)
}

/// Legacy grouping query retained while the two callers keep their uniform
/// cluster loop. The reader now folds an annotation and its subject into one
/// `Sexp::Annotated`, so no annotation occupies a separate prefix in `sexps`.
pub(crate) fn leading_annotation_len(sexps: &[Sexp]) -> usize {
    let _ = sexps;
    0
}

/// Convert `Vec<TopLevel>` back into `Vec<ParsedEntry>` for handoff to
/// `cranelisp_typecheck::check_forms`. The worker pipeline still operates in
/// `TopLevel` shapes downstream of build_form for codegen + display info; we
/// transcode again here at the typecheck-dispatch boundary.
pub(crate) fn top_level_to_parsed_entries(
    program: &[TopLevel],
) -> Vec<cranelisp_types::ParsedEntry> {
    use cranelisp_types::ParsedEntry;

    let mut out = Vec::with_capacity(program.len());
    for tl in program {
        match tl {
            TopLevel::Defn(d) => out.push(ParsedEntry::Def {
                name: d.name.clone(),
                variants: d.variants.clone(),
                visibility: d.visibility,
                docstring: d.docstring.clone(),
                span: d.span,
            }),
            TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } => {
                // `ParsedEntry::TypeDef.type_params` is `Vec<Symbol>` (the
                // type-parameter binders, as written) — pass through directly.
                out.push(ParsedEntry::TypeDef {
                    name: name.clone(),
                    type_params: type_params.clone(),
                    constructors: constructors.clone(),
                    visibility: *visibility,
                    docstring: docstring.clone(),
                    span: *span,
                });
            }
            TopLevel::TraitDecl(decl) => out.push(ParsedEntry::TraitDecl { decl: decl.clone() }),
            TopLevel::TraitImpl(impl_) => out.push(ParsedEntry::TraitImpl {
                impl_: impl_.clone(),
            }),
            // Expression forms are wrapped by `wrap_exprs_as_defns` upstream;
            // any remaining `Expr` here would be a workflow bug, so skip silently
            // and let downstream catch the inconsistency. Note: `TopLevel` is
            // not `#[non_exhaustive]` to external callers — the four variants
            // above plus `Expr` are the full set; no wildcard arm required.
            TopLevel::Expr(_) => {}
        }
    }
    out
}

/// Single-call typecheck dispatch through `cranelisp_typecheck::check_forms`.
///
/// Replaces the retired pre-S66 multi-call sequence `check_form(Register)` +
/// `merge_form_result` + `check_form(CheckBody)` + `merge_form_result` +
/// `finalize_check_result`. Per Decision 44's 2026-05-13 third amendment,
/// `check_forms` performs both internal passes plus finalize on a single call
/// over a `Vec<ParsedEntry>`.
///
/// **Wave 3b-2c.3 — Cluster mode is the hot path.** FIXME 0179 (cluster-mode
/// read-union via `View::union(staging, live)`) has landed in typecheck.
/// `check_program_compat` now delegates unconditionally to
/// [`process_cluster_with_staging`], which builds
/// `ClusterContext::Cluster { staging, … }`, runs `check_forms`, and on
/// `Ok` drains staging into live atomically (commit) or on `Err` drops
/// staging (atomic discard, live unchanged).
pub(crate) fn check_program_compat(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    shared: Option<&crate::session_v4::SharedState>,
) -> Result<
    (
        Option<cranelisp_types::ResolutionGap>,
        Vec<cranelisp_types::Warning>,
        Vec<cranelisp_typecheck::UnresolvedDispatchSite>,
        Vec<crate::redefine::RedefinitionOutcome>,
    ),
    CranelispError,
> {
    // Wave 3b-2c.3: FIXME 0179 (cluster-mode read-union via View::union) has
    // landed in typecheck. Cluster mode is now activated as the hot path —
    // writes flow to a fresh staging table, reads union staging-first with
    // live, and on Ok the staging entries commit to live atomically. On Err
    // staging drops and live is unchanged.
    //
    // Returns `Ok(Some(gap))` when typecheck surfaces a recoverable
    // `CheckError::Gap` — the FQ-auto-load orchestration (spec §8.5.4 / §9.3.6,
    // FIXME 0268) catches an unloaded-module gap here and loads-and-retries.
    //
    // S101: `shared` carries the session retention pool for the commit gate's
    // ABI-epoch slot policy (design/int/session-transaction.md §7.1); the
    // returned `RedefinitionOutcome`s ride `ProcessedCluster` back to the
    // eval driver.
    process_cluster_with_staging(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        working_program,
        shared,
    )
}

/// Run `check_program_compat` and reject a surviving gap as a hard error.
///
/// Used by call sites that do NOT participate in the FQ-auto-load orchestration
/// (macro-clause compilation, cache-load typecheck, `/type` introspection,
/// the zero-caller `cluster::process_cluster` scaffold). These paths preserve
/// the pre-FIXME-0268 behaviour: a `CheckError::Gap` (now surfaced as
/// `Ok(Some(gap))`) becomes a `TypeError`. Only `finalize_module` and the
/// Pass-2 expand loop act on a gap by loading the named module and retrying.
pub(crate) fn check_program_compat_no_gap(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
) -> Result<(), CranelispError> {
    // These call sites (macro-clause compilation, cache-load typecheck,
    // `/type` introspection) do not participate in the REPL warning surface,
    // so the FIXME-0365 warning channel is discarded here.
    match check_program_compat(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        working_program,
        // No session context on these paths: the gate falls back to the
        // reuse-and-patch slot policy (no retention pool to freeze into) and
        // the redefinition outcomes are dropped. The internal-name shapes
        // these callers commit (`__expr`, `__macro_*` clauses) are
        // gate-exempt anyway (S101, `redefine::is_gate_exempt_internal`).
        None,
    )? {
        (None, _warnings, _dispatch, _redefs) => Ok(()),
        (Some(gap), _warnings, _dispatch, _redefs) => Err(CranelispError::TypeError {
            message: format!("unresolved cross-module reference: {gap:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

/// Process a cluster through `ClusterContext::Cluster` with a fresh staging
/// table and atomic commit/discard.
///
/// **Active path (Wave 3b-2c.3).** Per Decision 44 — `int` allocates the
/// staging `SymbolTable<Code, ()>` on the stack, hands it to `check_forms`
/// via `ClusterContext::Cluster`, and on `Ok` drains staging entries into
/// the live table atomically (per-symbol `DashMap::get_mut` write guard,
/// GOT slots re-allocated from live's allocator). On `Err`, the stack-drop
/// of `staging` discards it (atomic discard, live unchanged).
///
/// FIXME 0179 (cluster-mode read-union) is closed: typecheck reads in
/// cluster mode dispatch `View::union(staging, live)` staging-first, so
/// in-cluster forward references resolve through staging without leaking
/// writes to live.
pub(crate) fn process_cluster_with_staging(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    shared: Option<&crate::session_v4::SharedState>,
) -> Result<
    (
        Option<cranelisp_types::ResolutionGap>,
        Vec<cranelisp_types::Warning>,
        Vec<cranelisp_typecheck::UnresolvedDispatchSite>,
        Vec<crate::redefine::RedefinitionOutcome>,
    ),
    CranelispError,
> {
    use cranelisp_typecheck::{CheckError, SymbolTableAccess, check_forms};

    let parsed = top_level_to_parsed_entries(working_program);
    if parsed.is_empty() {
        return Ok((None, Vec::new(), Vec::new(), Vec::new()));
    }

    let mut staging: crate::code::SessionSymbolTable =
        cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(module.clone());
    let mut ctx: SymbolTableAccess<'_, crate::code::Code, ()> =
        SymbolTableAccess::cluster(symbol_tables, &mut staging, module.clone());
    let result = check_forms(
        parsed,
        &mut ctx,
        symbol_tables,
        module_aliases,
        prelude_fallback,
    );
    drop(ctx);

    match result {
        // On Ok: commit staging entries to live, carrying the cluster's
        // non-fatal warnings (FIXME 0365 warning channel) back to the caller
        // so int can thread them onto `ProcessedCluster.warnings` and the
        // REPL can render them as `; warning: <message>` lines.
        Ok(check_result) => {
            let redefs = commit_staging_to_live(symbol_tables, module, staging, shared)?;
            // 0611: persist THIS module's unresolved-return-poly-dispatch
            // carrier so `src/exe.rs::validate_main` can reject a `main` whose
            // body carries one (the `--run`/`--link` class-(b) leg, Principle
            // 19). EMPTY for every valid module; overwritten per re-check.
            if let Some(sh) = shared {
                sh.typecheck_products
                    .entry(module.clone())
                    .or_insert_with(|| crate::session_v4::TypecheckProduct {
                        file_path: None,
                        source_text: None,
                        unresolved_dispatch: Vec::new(),
                    })
                    .unresolved_dispatch = check_result.unresolved_dispatch.clone();
            }
            Ok((
                None,
                check_result.warnings,
                check_result.unresolved_dispatch,
                redefs,
            ))
        }
        // A recoverable resolution gap (e.g. an FQ reference to a module not
        // yet loaded). Staging drops here (atomic discard, live unchanged);
        // the gap is handed back to `finalize_module` for FQ-auto-load
        // orchestration (FIXME 0268). On retry a fresh staging frame runs.
        // No warnings on the gap path — the cluster re-runs from the top.
        Err(CheckError::Gap(gap)) => Ok((Some(gap), Vec::new(), Vec::new(), Vec::new())),
        // A genuine type error — staging drops, live unchanged.
        Err(e) => Err(check_error_to_cranelisp_error(e)),
    }
}

fn check_cluster_to_staging(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
) -> Result<Option<Result<PreparedCheck, cranelisp_types::ResolutionGap>>, CranelispError> {
    use cranelisp_typecheck::{CheckError, SymbolTableAccess, check_forms};

    let parsed = top_level_to_parsed_entries(working_program);
    if parsed.is_empty() {
        return Ok(None);
    }
    let mut staging =
        cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(module.clone());
    let mut access = SymbolTableAccess::cluster(symbol_tables, &mut staging, module.clone());
    let result = check_forms(
        parsed,
        &mut access,
        symbol_tables,
        module_aliases,
        prelude_fallback,
    );
    drop(access);
    match result {
        Ok(result) => Ok(Some(Ok(PreparedCheck { staging, result }))),
        Err(CheckError::Gap(gap)) => Ok(Some(Err(gap))),
        Err(error) => Err(check_error_to_cranelisp_error(error)),
    }
}

#[allow(clippy::type_complexity)]
#[cfg(test)]
pub(crate) fn prepare_cluster_commit(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    codegen_program: &[TopLevel],
    shared: &crate::session_v4::SharedState,
) -> Result<
    Option<
        Result<(PreparedCommit, cranelisp_typecheck::CheckResult), cranelisp_types::ResolutionGap>,
    >,
    CranelispError,
> {
    prepare_cluster_commit_with_demands(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        working_program,
        codegen_program,
        &[],
        shared,
    )
}

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare_cluster_commit_with_demands(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
    codegen_program: &[TopLevel],
    reload_demands: &[MonoDemand],
    shared: &crate::session_v4::SharedState,
) -> Result<
    Option<
        Result<(PreparedCommit, cranelisp_typecheck::CheckResult), cranelisp_types::ResolutionGap>,
    >,
    CranelispError,
> {
    let checked = check_cluster_to_staging(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        working_program,
    )?;
    let checked = match checked {
        Some(checked) => checked,
        None if reload_demands.is_empty() => return Ok(None),
        None => Ok(PreparedCheck {
            staging: cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(
                module.clone(),
            ),
            result: cranelisp_typecheck::CheckResult {
                warnings: Vec::new(),
                display: None,
                unresolved_dispatch: Vec::new(),
            },
        }),
    };
    let checked = match checked {
        Ok(checked) => checked,
        Err(gap) => return Ok(Some(Err(gap))),
    };
    validate_guarded_staging(symbol_tables, module, &checked.staging)?;
    let mut demands = capture_affected_mono_demands(symbol_tables, module, &checked.staging)?;
    extend_reload_demands(
        symbol_tables,
        module,
        &checked.staging,
        reload_demands,
        &mut demands,
    )?;
    finish_prepared_commit(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        codegen_program,
        checked,
        &demands,
        shared,
    )
}

#[allow(clippy::type_complexity)]
fn finish_prepared_commit(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    codegen_program: &[TopLevel],
    mut checked: PreparedCheck,
    demands: &[CapturedMonoDemand],
    shared: &crate::session_v4::SharedState,
) -> Result<
    Option<
        Result<(PreparedCommit, cranelisp_typecheck::CheckResult), cranelisp_types::ResolutionGap>,
    >,
    CranelispError,
> {
    if let Err(gap) = instantiate_captured_demands(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        &mut checked,
        demands,
    )? {
        return Ok(Some(Err(gap)));
    }
    let DemandPublicationPlan {
        targets,
        decisions,
        guard_exempt_symbols,
        authored_bases,
    } = plan_demand_publication(symbol_tables, module, &checked.staging, demands)?;
    // A top-level expression whose return-directed dispatch is still
    // unresolved deliberately survives typecheck so the REPL/executable entry
    // boundary can report the language-level ambiguity. It has no concrete
    // `__expr` body to compile, however. Keep every successfully checked
    // definition in this cluster eligible for codegen and omit only the
    // affected expression wrapper from the forced-enrollment input. Exact
    // demand targets are added to that complete batch below.
    let codegen_program: Vec<TopLevel> = codegen_program
        .iter()
        .filter(|top| match top {
            TopLevel::Expr(expr) => {
                crate::exe::first_dispatch_within(&checked.result.unresolved_dispatch, expr.span())
                    .is_none()
            }
            _ => true,
        })
        .cloned()
        .collect();
    let mut prepared = plan_staging_commit_inner(
        symbol_tables,
        module,
        checked.staging,
        &codegen_program,
        shared,
        &decisions,
        &guard_exempt_symbols,
    )?;
    prepared
        .outcomes
        .retain(|outcome| !authored_bases.contains(&outcome.fq.symbol));
    for target in targets {
        if !prepared.targets.contains(&target) {
            prepared.targets.push(target);
        }
    }
    Ok(Some(Ok((prepared, checked.result))))
}

fn instantiate_captured_demands(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    checked: &mut PreparedCheck,
    demands: &[CapturedMonoDemand],
) -> Result<Result<(), cranelisp_types::ResolutionGap>, CranelispError> {
    let already_materialized = materialize_settled_overload_demands(&mut checked.staging, demands)?;
    let target_clean_tables = dashmap::DashMap::new();
    for row in symbol_tables.iter() {
        if row.key() == module {
            let mut target = row.value().clone();
            for demand in demands {
                target
                    .retire_abi_changing(&demand.prior_key)
                    .map_err(|error| CranelispError::ModuleError {
                        message: error.to_string(),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    })?;
            }
            target_clean_tables.insert(module.clone(), target);
        } else {
            target_clean_tables.insert(row.key().clone(), row.value().clone());
        }
    }
    let demand_result = {
        let mut access = cranelisp_typecheck::SymbolTableAccess::cluster(
            &target_clean_tables,
            &mut checked.staging,
            module.clone(),
        );
        cranelisp_typecheck::instantiate_demands(
            demands
                .iter()
                .filter(|captured| {
                    captured
                        .staged_key
                        .as_ref()
                        .is_none_or(|key| !already_materialized.contains(key))
                })
                .filter_map(|captured| captured.demand.clone())
                .collect(),
            &mut access,
            &target_clean_tables,
            module_aliases,
            prelude_fallback,
        )
    };
    let demand_result = match demand_result {
        Ok(result) => result,
        Err(cranelisp_typecheck::CheckError::Gap(gap)) => return Ok(Err(gap)),
        Err(error) => return Err(check_error_to_cranelisp_error(error)),
    };
    checked.result.warnings.extend(demand_result.warnings);
    checked
        .result
        .warnings
        .extend(demands.iter().filter(|captured| captured.demand.is_none()).map(
            |captured| cranelisp_types::Warning {
                kind: cranelisp_types::WarningKind::Other,
                message: format!(
                    "declined stale monomorphisation demand for {:?} at ({}): replacement has no corresponding callable template",
                    captured.old_link.template,
                    captured
                        .old_link
                        .type_args
                        .iter()
                        .map(|arg| arg.to_type().to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                span: Span::SYNTHETIC,
            },
        ));
    Ok(Ok(()))
}

/// Materialize an exact demand directly from a replacement overload arm that
/// typecheck has already settled concrete in-place. This is the back-flow case:
/// there is no template left for `instantiate_demands` to replay, but the
/// checked arm carries the scheme, body and metadata needed for the generated
/// instance entry. Ordinary demand processing completes ownership before
/// publication planning.
fn materialize_settled_overload_demands(
    staging: &mut crate::code::SessionSymbolTable,
    demands: &[CapturedMonoDemand],
) -> Result<std::collections::HashSet<Symbol>, CranelispError> {
    let mut materialized = std::collections::HashSet::new();
    for captured in demands {
        let (Some(demand), Some(staged_key)) = (&captured.demand, &captured.staged_key) else {
            continue;
        };
        let expected_link = demand.instance_link();
        if staging.get(staged_key.as_ref()).is_some_and(|binding| {
            matches!(
                binding.callable().map(|callable| &callable.arm.life),
                Some(Life::Concrete {
                    minted_from: Some(link),
                    ..
                }) if link == &expected_link
            )
        }) {
            materialized.insert(staged_key.clone());
            continue;
        }
        let CallableTarget::OverloadArm { owner, arm } = &demand.template else {
            continue;
        };
        let Some(family) = staging.get(owner.symbol.as_ref()).cloned() else {
            continue;
        };
        let Decl::Overloaded(declaration) = &family.declaration else {
            continue;
        };
        let Some(selected) = declaration
            .arms
            .iter()
            .find(|candidate| candidate.id == *arm)
        else {
            continue;
        };
        let Life::Concrete {
            realization: Realization::Body { view, code: None },
            minted_from: None,
            ast,
            callees,
            value_use,
            mode_summary,
            ..
        } = &selected.callable.life
        else {
            continue;
        };
        if demand.instance_key(&selected.callable.scheme).ok().as_ref() != Some(staged_key) {
            continue;
        }

        let mut instance_view = view.clone();
        instance_view.name = staged_key.clone();
        instance_view.mode_summary = mode_summary.clone();
        let (installed_key, _) = staging
            .install_instance(
                expected_link,
                selected.callable.scheme.clone(),
                selected.callable.param_names.clone(),
                declaration.docstring.clone(),
                declaration.seq,
                CallableOrigin::Plain,
                Realization::Body {
                    view: instance_view.clone(),
                    code: None,
                },
                ast.clone(),
                callees.clone(),
                family.visibility,
            )
            .map_err(|error| CranelispError::ModuleError {
                message: format!(
                    "cannot stage settled overload realization '{staged_key}': {error}"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        if &installed_key != staged_key {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "settled overload realization key mismatch: expected '{staged_key}', installed '{installed_key}'"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        let target = CallableTarget::Binding(cranelisp_types::FQSymbol {
            module: staging.path.clone(),
            symbol: installed_key.clone(),
        });
        if let Some(summary) = mode_summary.clone() {
            staging
                .publish_body_ownership(&target, summary, instance_view)
                .map_err(|error| CranelispError::ModuleError {
                    message: format!(
                        "cannot publish ownership for settled overload realization '{staged_key}': {error}"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
        }
        if *value_use {
            staging
                .set_value_use(&installed_key, true)
                .map_err(|error| CranelispError::ModuleError {
                    message: format!(
                        "cannot preserve value use for settled overload realization '{staged_key}': {error}"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
        }
        materialized.insert(installed_key);
    }
    Ok(materialized)
}

struct CapturedMonoDemand {
    prior_key: Symbol,
    old_link: InstanceLink,
    demand: Option<cranelisp_types::MonoDemand>,
    staged_key: Option<Symbol>,
    policy: crate::redefine::InstanceRematerializationPolicy,
}

struct DemandPublicationPlan {
    targets: Vec<CallableTarget>,
    decisions: Vec<StagedPublicationDecision>,
    guard_exempt_symbols: Vec<Symbol>,
    authored_bases: Vec<Symbol>,
}

fn plan_demand_publication(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: &crate::code::SessionSymbolTable,
    demands: &[CapturedMonoDemand],
) -> Result<DemandPublicationPlan, CranelispError> {
    use crate::redefine::InstanceRematerializationPolicy::{
        CallerFreeLanguageTypeChange, SameLanguageType,
    };

    let mut targets = Vec::new();
    let mut decisions = Vec::new();
    let mut guard_exempt_symbols = Vec::new();
    let mut authored_bases = Vec::new();
    let live = symbol_tables.get(module);
    for captured in demands {
        if let Some(owner) = callable_target_owner(&captured.old_link.template)
            && &owner.module == module
            && !authored_bases.contains(&owner.symbol)
        {
            authored_bases.push(owner.symbol.clone());
        }
        let realized = captured.demand.as_ref().and_then(|demand| {
            let expected_link = demand.instance_link();
            staging.codegen_targets().find_map(|(target, arm)| {
                let owner = callable_target_owner(&target)?;
                (Some(&owner.symbol) == captured.staged_key.as_ref()
                    && matches!(
                        &arm.life,
                        Life::Concrete {
                            minted_from: Some(link),
                            ..
                        } if link == &expected_link
                    ))
                .then_some(target)
            })
        });
        if let Some(target) = realized {
            let symbol = callable_target_owner(&target)
                .map(|owner| owner.symbol.clone())
                .ok_or_else(|| CranelispError::ModuleError {
                    message: format!("rematerialized target '{target:?}' has no callable owner"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
            let prior = live
                .as_ref()
                .and_then(|table| table.get(captured.prior_key.as_ref()))
                .ok_or_else(|| rematerialization_error(captured, "prior instance disappeared"))?;
            let staged = staging
                .get(
                    captured
                        .staged_key
                        .as_ref()
                        .expect("realized demand has a staged key")
                        .as_ref(),
                )
                .ok_or_else(|| rematerialization_error(captured, "new instance disappeared"))?;
            let (kind, _) =
                crate::redefine::classify_redefinition(symbol.as_ref(), Some(prior), staged);
            let abi_compatible = kind != crate::redefine::RedefKind::AbiChanging
                && cranelisp_types::ModeSummary::abi_eq_opt(
                    prior.mode_summary(),
                    staged.mode_summary(),
                );
            let decision = match captured.policy {
                SameLanguageType
                    if captured.staged_key.as_ref() == Some(&captured.prior_key)
                        && abi_compatible =>
                {
                    StagedPublicationDecision::PreserveAbi {
                        symbol: symbol.clone(),
                    }
                }
                SameLanguageType => {
                    return Err(rematerialization_error(
                        captured,
                        "same-language-type replacement changed the realization key or ABI",
                    ));
                }
                CallerFreeLanguageTypeChange
                    if captured.staged_key.as_ref() == Some(&captured.prior_key)
                        && abi_compatible =>
                {
                    StagedPublicationDecision::PreserveAbi {
                        symbol: symbol.clone(),
                    }
                }
                CallerFreeLanguageTypeChange => StagedPublicationDecision::ChangeAbi {
                    symbol: symbol.clone(),
                },
            };
            if captured.staged_key.as_ref() == Some(&captured.prior_key) {
                decisions.push(decision);
            }
            if captured.staged_key.as_ref() != Some(&captured.prior_key)
                && !decisions.iter().any(|decision| {
                    matches!(
                        decision,
                        StagedPublicationDecision::ChangeAbi { symbol }
                            if symbol == &captured.prior_key
                    )
                })
            {
                decisions.push(StagedPublicationDecision::ChangeAbi {
                    symbol: captured.prior_key.clone(),
                });
            }
            if !targets.contains(&target) {
                targets.push(target);
            }
            if !guard_exempt_symbols.contains(&symbol) {
                guard_exempt_symbols.push(symbol);
            }
        } else {
            match captured.policy {
                SameLanguageType => {
                    return Err(rematerialization_error(
                        captured,
                        "same-language-type replacement declined the prior realization",
                    ));
                }
                CallerFreeLanguageTypeChange => {
                    if !decisions.iter().any(|decision| {
                        matches!(
                            decision,
                            StagedPublicationDecision::ChangeAbi { symbol: prior }
                                if prior == &captured.prior_key
                        )
                    }) {
                        decisions.push(StagedPublicationDecision::ChangeAbi {
                            symbol: captured.prior_key.clone(),
                        });
                    }
                }
            }
        }
    }
    Ok(DemandPublicationPlan {
        targets,
        decisions,
        guard_exempt_symbols,
        authored_bases,
    })
}

fn rematerialization_error(captured: &CapturedMonoDemand, reason: &str) -> CranelispError {
    CranelispError::TypeError {
        message: format!(
            "cannot rematerialize prior instance '{}' ({:?}) for replacement: {reason}",
            captured.prior_key, captured.old_link
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    }
}

struct HistoricalMonoInstance {
    prior_key: Symbol,
    link: InstanceLink,
}

/// Capture the typed identity of every concrete instance owned by one live
/// module generation.
fn capture_mono_demands(table: &crate::code::SessionSymbolTable) -> Vec<HistoricalMonoInstance> {
    fn capture_life(
        prior_key: &Symbol,
        life: &Life<crate::code::Code>,
        instances: &mut Vec<HistoricalMonoInstance>,
    ) {
        if let Life::Concrete {
            minted_from: Some(link),
            ..
        } = life
            && !instances
                .iter()
                .any(|instance| instance.prior_key == *prior_key)
        {
            instances.push(HistoricalMonoInstance {
                prior_key: prior_key.clone(),
                link: link.clone(),
            });
        }
    }

    let mut instances = Vec::new();
    for (name, binding) in table.all_symbols() {
        match &binding.declaration {
            Decl::Callable(callable) => capture_life(name, &callable.arm.life, &mut instances),
            Decl::Overloaded(declaration) => {
                for arm in &declaration.arms {
                    capture_life(name, &arm.callable.life, &mut instances);
                }
            }
            Decl::Macro(declaration) => {
                for clause in &declaration.clauses {
                    capture_life(name, &clause.callable.life, &mut instances);
                }
            }
            _ => {}
        }
    }
    instances
}

/// Project the concrete instantiations owned by one module table into the
/// immutable request packet carried by a persisted-source reload.
pub(crate) fn capture_reload_instantiation_demands(
    table: &crate::code::SessionSymbolTable,
) -> std::sync::Arc<[MonoDemand]> {
    capture_mono_demands(table)
        .into_iter()
        .map(|historical| {
            MonoDemand::from_type_args(
                historical.link.template,
                historical.link.type_args,
                Span::SYNTHETIC,
            )
        })
        .collect::<Vec<_>>()
        .into()
}

/// Add reload-carried historical instances that are not already covered by
/// an authored replacement in this cluster. A missing replacement template is
/// an explicit decline; its prior key retires only if the whole candidate
/// later publishes successfully.
fn extend_reload_demands(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: &crate::code::SessionSymbolTable,
    reload_demands: &[MonoDemand],
    captured: &mut Vec<CapturedMonoDemand>,
) -> Result<(), CranelispError> {
    let Some(live) = symbol_tables.get(module).map(|table| table.clone()) else {
        return Ok(());
    };
    let historical = capture_mono_demands(&live);
    for demand in reload_demands {
        let old_link = demand.instance_link();
        let Some(prior) = historical.iter().find(|prior| prior.link == old_link) else {
            continue;
        };
        if captured
            .iter()
            .any(|existing| existing.prior_key == prior.prior_key)
        {
            continue;
        }
        let Some(owner) = callable_target_owner(&demand.template) else {
            continue;
        };
        let remapped = if &owner.module == module {
            staging.callable_target(&demand.template).map(|arm| {
                demand
                    .instance_key(&arm.scheme)
                    .map(|key| (demand.clone(), key))
                    .map_err(|error| CranelispError::TypeError {
                        message: format!(
                            "cannot rematerialize persisted instance '{}': replacement key derivation failed: {error}",
                            prior.prior_key
                        ),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    })
            }).transpose()?
        } else {
            symbol_tables
                .get(&owner.module)
                .map(|table| remap_foreign_reload_demand(&table, demand, &prior.prior_key))
                .transpose()?
                .flatten()
        };
        let Some((staged_demand, staged_key)) = remapped else {
            captured.push(CapturedMonoDemand {
                prior_key: prior.prior_key.clone(),
                old_link,
                demand: None,
                staged_key: None,
                policy:
                    crate::redefine::InstanceRematerializationPolicy::CallerFreeLanguageTypeChange,
            });
            continue;
        };
        captured.push(CapturedMonoDemand {
            prior_key: prior.prior_key.clone(),
            old_link,
            demand: Some(staged_demand),
            staged_key: Some(staged_key),
            policy: crate::redefine::InstanceRematerializationPolicy::CallerFreeLanguageTypeChange,
        });
    }
    Ok(())
}

/// Resolve a reload-carried demand against the dependency generation visible
/// now. Overload arm ordinals are generation-local, so foreign replay matches
/// by the canonical concrete-signature key that the historical caller owns.
fn remap_foreign_reload_demand(
    table: &crate::code::SessionSymbolTable,
    demand: &MonoDemand,
    prior_key: &Symbol,
) -> Result<Option<(MonoDemand, Symbol)>, CranelispError> {
    let CallableTarget::OverloadArm { owner, .. } = &demand.template else {
        let Some(arm) = table.callable_target(&demand.template) else {
            return Ok(None);
        };
        let key = demand.instance_key(&arm.scheme).map_err(|error| {
            CranelispError::TypeError {
                message: format!(
                    "cannot rematerialize persisted instance '{prior_key}': replacement key derivation failed: {error}"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        return Ok(Some((demand.clone(), key)));
    };

    let Some(binding) = table.get(owner.symbol.as_ref()) else {
        return Ok(None);
    };
    let Decl::Overloaded(declaration) = &binding.declaration else {
        return Ok(None);
    };
    let mut matches = Vec::new();
    for (ordinal, replacement) in declaration.arms.iter().enumerate() {
        let Ok(arm) = cranelisp_types::CallableArmId::from_ordinal(ordinal) else {
            continue;
        };
        let remapped = MonoDemand::from_type_args(
            CallableTarget::OverloadArm {
                owner: owner.clone(),
                arm,
            },
            demand.type_args.clone(),
            Span::SYNTHETIC,
        );
        if remapped
            .instance_key(&replacement.callable.scheme)
            .is_ok_and(|key| key == *prior_key)
        {
            matches.push(remapped);
        }
    }
    match matches.len() {
        0 => Ok(None),
        1 => Ok(matches.pop().map(|remapped| (remapped, prior_key.clone()))),
        count => Err(CranelispError::TypeError {
            message: format!(
                "cannot rematerialize persisted instance '{prior_key}': replacement overload has {count} matching arms"
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

fn capture_affected_mono_demands(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: &crate::code::SessionSymbolTable,
) -> Result<Vec<CapturedMonoDemand>, CranelispError> {
    let Some(live) = symbol_tables.get(module).map(|table| table.clone()) else {
        return Ok(Vec::new());
    };
    let mut captured = Vec::new();
    let mut staged_keys = std::collections::HashMap::<Symbol, Symbol>::new();
    for historical in capture_mono_demands(&live) {
        let Some(owner) = callable_target_owner(&historical.link.template) else {
            continue;
        };
        if &owner.module != module {
            continue;
        }
        let Some(prior) = live.get(owner.symbol.as_ref()) else {
            continue;
        };
        let Some(replacement) = staging.get(owner.symbol.as_ref()) else {
            continue;
        };
        let Some(policy) = crate::redefine::instance_rematerialization_policy(
            symbol_tables,
            module,
            &owner.symbol,
            prior,
            replacement,
        ) else {
            continue;
        };
        let staged_template = match &historical.link.template {
            CallableTarget::Binding(owner) => Some(CallableTarget::Binding(owner.clone())),
            CallableTarget::OverloadArm { owner, arm } => {
                match crate::redefine::match_replacement_overload_arm(
                    owner,
                    prior,
                    replacement,
                    *arm,
                ) {
                    Ok(matched) => Some(CallableTarget::OverloadArm {
                        owner: owner.clone(),
                        arm: matched,
                    }),
                    Err(_)
                        if policy
                            == crate::redefine::InstanceRematerializationPolicy::CallerFreeLanguageTypeChange =>
                    {
                        None
                    }
                    Err(error) => return Err(error),
                }
            }
            CallableTarget::MacroClause { .. } => continue,
            _ => continue,
        };
        let (demand, staged_key) = if let Some(staged_template) = staged_template {
            let Some(staged_scheme) = staging
                .callable_target(&staged_template)
                .map(|arm| &arm.scheme)
            else {
                if policy
                    == crate::redefine::InstanceRematerializationPolicy::CallerFreeLanguageTypeChange
                {
                    captured.push(CapturedMonoDemand {
                        prior_key: historical.prior_key,
                        old_link: historical.link,
                        demand: None,
                        staged_key: None,
                        policy,
                    });
                    continue;
                }
                return Err(CranelispError::TypeError {
                    message: format!(
                        "cannot rematerialize prior instance '{}': matched staged template is absent",
                        historical.prior_key
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            let demand = cranelisp_types::MonoDemand::from_type_args(
                staged_template,
                historical.link.type_args.clone(),
                Span::SYNTHETIC,
            );
            let staged_key = match demand.instance_key(staged_scheme) {
                Ok(key) => Some(key),
                Err(_)
                    if policy
                        == crate::redefine::InstanceRematerializationPolicy::CallerFreeLanguageTypeChange =>
                {
                    None
                }
                Err(error) => {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "cannot rematerialize prior instance '{}': replacement key derivation failed: {error}",
                            historical.prior_key
                        ),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    });
                }
            };
            (Some(demand), staged_key)
        } else {
            (None, None)
        };
        if let Some(staged_key) = &staged_key {
            if let Some(other_prior) =
                staged_keys.insert(staged_key.clone(), historical.prior_key.clone())
                && other_prior != historical.prior_key
            {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "cannot rematerialize prior instances '{}' and '{}': both map to staged key '{}'",
                        other_prior, historical.prior_key, staged_key
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
        }
        captured.push(CapturedMonoDemand {
            prior_key: historical.prior_key,
            old_link: historical.link,
            demand,
            staged_key,
            policy,
        });
    }
    Ok(captured)
}

pub(crate) fn plan_staging_commit(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: crate::code::SessionSymbolTable,
    codegen_program: &[TopLevel],
    shared: &crate::session_v4::SharedState,
    additional_decisions: &[StagedPublicationDecision],
) -> Result<PreparedCommit, CranelispError> {
    plan_staging_commit_inner(
        symbol_tables,
        module,
        staging,
        codegen_program,
        shared,
        additional_decisions,
        &[],
    )
}

fn plan_staging_commit_inner(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: crate::code::SessionSymbolTable,
    codegen_program: &[TopLevel],
    shared: &crate::session_v4::SharedState,
    additional_decisions: &[StagedPublicationDecision],
    rematerialized_instances: &[Symbol],
) -> Result<PreparedCommit, CranelispError> {
    use crate::redefine::{RedefKind, RedefinitionOutcome, classify_redefinition};
    use cranelisp_types::FQSymbol;

    validate_guarded_staging_except(symbol_tables, module, &staging, rematerialized_instances)?;

    let tables = dashmap::DashMap::new();
    for row in symbol_tables.iter() {
        tables.insert(row.key().clone(), row.value().clone());
    }
    let declared = shared.declared_exports.get(module).map(|d| d.clone());
    let Some(mut candidate) = tables.get_mut(module) else {
        return Err(CranelispError::ModuleError {
            message: format!("module '{module}' disappeared while preparing a turn"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    };
    let mut decisions = additional_decisions.to_vec();
    let mut outcomes = Vec::new();
    for (name, exposure) in staging.all_name_candidates() {
        crate::imports::check_exposed_candidate_closure(
            module,
            name,
            &exposure.source,
            exposure.visibility,
            Span::SYNTHETIC,
            declared.as_ref(),
        )?;
    }
    for (name, binding) in staging.all_symbols() {
        let prior = candidate.get(name.as_ref());
        let prior_was_def = prior.is_some_and(binding_is_definition);
        let staged_is_def = binding_is_definition(binding);
        let prior_slot = prior.and_then(binding_first_slot);
        let staged_slot = binding_first_slot(binding);
        let (kind, per_symbol) = classify_redefinition(name.as_ref(), prior, binding);
        if prior_slot.is_some()
            && staged_slot.is_some()
            && !additional_decisions.iter().any(|decision| match decision {
                StagedPublicationDecision::PreserveAbi { symbol }
                | StagedPublicationDecision::ChangeAbi { symbol } => symbol == name,
            })
        {
            decisions.push(match kind {
                RedefKind::AbiChanging => StagedPublicationDecision::ChangeAbi {
                    symbol: name.clone(),
                },
                RedefKind::New | RedefKind::AbiPreserving => {
                    StagedPublicationDecision::PreserveAbi {
                        symbol: name.clone(),
                    }
                }
            });
        }
        if staged_is_def && (staged_slot.is_some() || prior_was_def) {
            outcomes.push(RedefinitionOutcome {
                fq: FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                },
                kind,
                per_symbol,
                prior_was_def,
                old_slot: prior_slot,
                new_slot: staged_slot,
            });
        }
    }
    let records = candidate
        .publish_staged(staging.clone(), &decisions)
        .map_err(|error| CranelispError::ModuleError {
            message: error.to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    for outcome in &mut outcomes {
        if let Some(record) = records
            .iter()
            .find(|record| record.symbol == outcome.fq.symbol)
        {
            outcome.new_slot = record
                .bodies
                .iter()
                .find_map(|body| body.published_slot.map(|slot| slot.index()));
        }
    }
    drop(candidate);
    let targets = derive_codegen_batch(module, codegen_program, &tables);
    for target in &targets {
        let valid = tables.get(module).is_some_and(|table| {
            table
                .callable_target(target)
                .is_some_and(|arm| matches!(arm.life, Life::Concrete { .. }))
        });
        if !valid {
            return Err(CranelispError::ModuleError {
                message: format!("prepared codegen target '{target:?}' is not callable"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
    }
    Ok(PreparedCommit {
        module: module.clone(),
        staging,
        decisions,
        tables,
        targets,
        outcomes,
        unresolved_dispatch: Vec::new(),
    })
}

/// The agent Build-mode pre-flight validator (`design/int/agent.md §16.1`,
/// Cluster B, S89): a **typecheck-only dry-run** that stages the proposed
/// forms, runs `check_forms` over them, and **always discards** — it NEVER
/// commits to live (the §16.1 discard-arm-without-commit). Returns `Ok(())`
/// when the forms parse+typecheck cleanly, `Err(compiler_error)` on **any**
/// failure (a resolution gap is folded into `Err` too — the validator wants a
/// *self-contained* clean form, not one that needs FQ-autoload orchestration).
///
/// **R3/R4 (binding):** reuses the EXACT build-staging + `check_forms` body of
/// [`process_cluster_with_staging`] minus `commit_staging_to_live`; `pub(crate)`,
/// int-internal, no facade/`cranelisp-types` change, no cache bump (the dry-run
/// never persists). **§20.3 (binding):** takes NO `auto_accept` parameter and
/// has no read path to it — the `--yes` flag is structurally unreachable from
/// here, so it can skip CONSENT but never this VALIDATION floor.
#[cfg(feature = "agent")]
pub(crate) fn validate_forms_dry_run(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    module: &ModuleFullPath,
    working_program: &[TopLevel],
) -> Result<(), CranelispError> {
    use cranelisp_typecheck::{CheckError, SymbolTableAccess};

    let parsed = top_level_to_parsed_entries(working_program);
    if parsed.is_empty() {
        // No checkable forms (e.g. a bare expression that built to nothing) —
        // treat as "nothing to validate", a clean pass. The submit path's own
        // `process_commands`→`eval` will still run for real on confirm.
        return Ok(());
    }

    let mut staging: crate::code::SessionSymbolTable =
        cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(module.clone());
    let mut ctx: SymbolTableAccess<'_, crate::code::Code, ()> =
        SymbolTableAccess::cluster(symbol_tables, &mut staging, module.clone());
    // §11.3(b) / §24 (CF.1) — the agent-robustness floor. `check_forms` runs on
    // the EVAL thread here, over model-proposed (uncontrolled) source. A
    // typechecker `debug_assert!`/`unreachable!`/`panic!` over arbitrary input
    // would otherwise unwind the eval thread and CRASH the REPL (the pool-worker
    // loop at `worker.rs:1483` already guards its `check_forms`; this eval-thread
    // seam did not). `checked_check_forms` mirrors that pool-worker `catch_unwind`
    // shape (reusing `panic_message`): a caught panic becomes a clean
    // `CheckError::TypeError`, which the discard arm below folds into the
    // validator's normal `Err` ("could not validate") → the agent's silent-repair
    // loop handles it (U5). The user NEVER sees a crash.
    let result = checked_check_forms(
        parsed,
        &mut ctx,
        symbol_tables,
        module_aliases,
        prelude_fallback,
    );
    drop(ctx);
    // `staging` is dropped at function end on EVERY path — never committed
    // (the §16.1 discard arm). A failed validation leaves live untouched; a
    // *clean* validation also discards (it is a dry run — the real commit
    // happens later through `process_commands`→`eval`, §15.3).
    match result {
        Ok(_check) => Ok(()),
        // A resolution gap is a not-yet-clean form for the validator's purpose;
        // surface it as an error so the repair loop re-prompts (U5 — no
        // error-classification; any non-Ok triggers repair).
        Err(CheckError::Gap(gap)) => Err(CranelispError::TypeError {
            message: format!("unresolved cross-module reference: {gap:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
        Err(e) => Err(check_error_to_cranelisp_error(e)),
    }
}

/// Drain `staging.symbols` into the live `SymbolTable` for `module` under a
/// single `DashMap::get_mut` write guard. Per `facades/int.md` invariant 5b
/// — entries land per-symbol; the drain is committed before this function
/// returns. GOT slot indices on `ModuleEntry::Def` entries are re-pointed
/// to live slots (staging's GOT is about to be dropped when `staging` falls
/// out of scope at the caller).
///
/// **This is the S101 commit gate — the single slot-policy authority**
/// (`design/int/session-transaction.md` §2/§7.1). Every staged callable `Def`
/// classifies against the prior live entry via the `AbiSurface` summary diff:
///
/// | Kind | Slot | Prior `Code` |
/// |---|---|---|
/// | `New` | fresh `allocate_got_slot` (exhaustion-guarded) | — |
/// | `AbiPreserving` | reuse prior slot; codegen patches in place | carried |
/// | `AbiChanging` | fresh slot; the old slot is never written again | pushed to `SharedState.retained_code` BEFORE `live.insert` |
///
/// A staged entry with NO callable slot displacing a slotted prior `Def`
/// with compiled code (concrete fn redefined as a polymorphic/overloaded
/// template — FIXME 0479) takes the complementary displacement arm: the
/// prior `Code` is retained in the pool (frozen supersession) so compiled
/// callers keep dispatching the frozen old chain through the still-populated
/// slot instead of a use-after-free. Since S102 (§9.1.1 gate widening) BOTH
/// slot-less-staged shapes — displacement and template-over-template — emit a
/// `RedefinitionOutcome` with `prior_was_def: true`, feeding the §18.1.1
/// downgrade (`stale:`) print (the T1 semantic cure itself is S103 —
/// design §10 T1).
///
/// The returned [`RedefinitionOutcome`]s ride `ProcessedCluster` back to the
/// eval driver, which runs the dependent-recompilation transaction for
/// `AbiChanging` outcomes (design §13). When `shared` is `None` (no session —
/// unit tests, dry-run shapes) there is no retention pool to freeze into, so
/// the gate degrades to the reuse-and-patch policy for every redefinition.
fn commit_staging_to_live(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: crate::code::SessionSymbolTable,
    shared: Option<&crate::session_v4::SharedState>,
) -> Result<Vec<crate::redefine::RedefinitionOutcome>, CranelispError> {
    let declared = shared.and_then(|s| s.declared_exports.get(module).map(|d| d.clone()));
    for (name, exposure) in staging.all_name_candidates() {
        crate::imports::check_exposed_candidate_closure(
            module,
            name,
            &exposure.source,
            exposure.visibility,
            Span::SYNTHETIC,
            declared.as_ref(),
        )?;
    }
    validate_guarded_staging(symbol_tables, module, &staging)?;
    let Some(mut live) = symbol_tables.get_mut(module) else {
        return Ok(Vec::new());
    };
    let (decisions, mut outcomes) = publication_plan(&live, &staging);
    let records =
        live.publish_staged(staging, &decisions)
            .map_err(|error| CranelispError::ModuleError {
                message: error.to_string(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
    for record in records {
        if let Some(shared) = shared {
            let mut retained = shared
                .retained_code
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            for body in record
                .bodies
                .iter()
                .filter(|body| body.displaced_owner.is_some())
            {
                retained.push(crate::redefine::RetainedCode::frozen(
                    module,
                    &record.symbol,
                    body.prior_slot.map(|slot| slot.index()),
                    body.displaced_owner
                        .clone()
                        .expect("owner presence was filtered"),
                ));
            }
        }
        if let Some(outcome) = outcomes
            .iter_mut()
            .find(|outcome| outcome.fq.symbol == record.symbol)
        {
            outcome.new_slot = record
                .bodies
                .iter()
                .find_map(|body| body.published_slot.map(|slot| slot.index()));
        }
    }
    Ok(outcomes)
}

fn validate_guarded_staging(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: &crate::code::SessionSymbolTable,
) -> Result<(), CranelispError> {
    validate_guarded_staging_except(symbol_tables, module, staging, &[])
}

fn validate_guarded_staging_except(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: &crate::code::SessionSymbolTable,
    rematerialized_instances: &[Symbol],
) -> Result<(), CranelispError> {
    let Some(live) = symbol_tables.get(module).map(|table| table.clone()) else {
        return Ok(());
    };
    for (name, staged) in staging.all_symbols() {
        if rematerialized_instances.contains(name) {
            continue;
        }
        crate::redefine::validate_guarded_redefinition(
            symbol_tables,
            module,
            name,
            &live,
            staging,
            live.get(name.as_ref()),
            staged,
        )?;
    }
    Ok(())
}

fn publication_plan(
    live: &crate::code::SessionSymbolTable,
    staging: &crate::code::SessionSymbolTable,
) -> (
    Vec<StagedPublicationDecision>,
    Vec<crate::redefine::RedefinitionOutcome>,
) {
    use crate::redefine::{RedefKind, RedefinitionOutcome, classify_redefinition};
    use cranelisp_types::FQSymbol;

    let mut decisions = Vec::new();
    let mut outcomes = Vec::new();
    for (name, binding) in staging.all_symbols() {
        let prior = live.get(name.as_ref());
        let prior_was_def = prior.is_some_and(binding_is_definition);
        let staged_is_def = binding_is_definition(binding);
        let old_slot = prior.and_then(binding_first_slot);
        let staged_slot = binding_first_slot(binding);
        let (kind, per_symbol) = classify_redefinition(name.as_ref(), prior, binding);
        if old_slot.is_some() && staged_slot.is_some() {
            decisions.push(match kind {
                RedefKind::AbiChanging => StagedPublicationDecision::ChangeAbi {
                    symbol: name.clone(),
                },
                RedefKind::New | RedefKind::AbiPreserving => {
                    StagedPublicationDecision::PreserveAbi {
                        symbol: name.clone(),
                    }
                }
            });
        }
        if staged_is_def && (staged_slot.is_some() || prior_was_def) {
            outcomes.push(RedefinitionOutcome {
                fq: FQSymbol {
                    module: live.path.clone(),
                    symbol: name.clone(),
                },
                kind,
                per_symbol,
                prior_was_def,
                old_slot,
                new_slot: staged_slot,
            });
        }
    }
    (decisions, outcomes)
}

/// Translate `CheckError` to the legacy `CranelispError` shape used by
/// the worker's error sites.
pub(crate) fn check_error_to_cranelisp_error(
    err: cranelisp_typecheck::CheckError,
) -> CranelispError {
    use cranelisp_typecheck::CheckError;
    match err {
        CheckError::TypeError { message, location } => {
            CranelispError::TypeError { message, location }
        }
        CheckError::Gap(gap) => CranelispError::TypeError {
            message: format!("typecheck gap: {gap:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        },
        // `CheckError` is `#[non_exhaustive]` per the typecheck facade —
        // future variants surface uniformly as a generic type error.
        _ => CranelispError::TypeError {
            message: "unknown CheckError variant".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        },
    }
}

use crate::scheduler::{CompileScheduler, PriorityWork};

// ---------------------------------------------------------------------------
// ModuleCompiler — bundled worker parameters (G-1)
// ---------------------------------------------------------------------------

/// Shared context for the priority worker loop and process_module_forms.
///
/// TypeChecker state (symbol_tables, next_type_id) lives on SharedState.
/// Workers create `TypeCheckEnv` on the stack from these references.
/// Sprint 57 Wave 3 G8: `platform_registry` is deleted. Platform function
/// pointers live in the per-module GOT, indexed by each entry's
/// `ModuleEntry::Def.got_slot`; DLL handles are retained in
/// `SharedState::kept_dlls` (Sprint 66 Wave 0 amendment — the prior
/// `ModuleEntry::Def.fn_ptr` field was redundant with the GOT and has been
/// removed).
pub struct ModuleCompiler<'a> {
    pub symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    pub next_type_id: &'a std::sync::atomic::AtomicU32,
    /// Session-level module-path alias table (int plan §1.4). The import
    /// installer writes `(import [(target alias) …])` aliases here; typecheck
    /// reads it read-only. Lives on `SharedState.module_aliases`.
    pub module_aliases: &'a cranelisp_types::ModuleAliases,
    /// Per-module prelude-outer-scope fallback flags (S78 §2.7). int's
    /// `inject_prelude_if_needed` sets `(module, true)` when a module gets
    /// the implicit prelude; typecheck reads it read-only at its bare-name
    /// resolution chokepoints. Lives on `SharedState.prelude_fallback`.
    pub prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
    /// Per-invocation typecheck state. For REPL: extracted from
    /// `CompilerSession.repl_check_state` (S77 W-SharedState — relocated off
    /// SharedState since it is initiator-only). For batch workers: created
    /// fresh per module.
    pub check_state: CheckState,
    /// Current module path. Mirrors check_state.current_module (which is pub(crate)).
    /// Updated alongside check_state by set_current_module().
    pub current_module: ModuleFullPath,
    pub scheduler: &'a CompileScheduler,
    /// Per-module typecheck products (GOT tables).
    pub typecheck_products:
        &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    /// Per-symbol introspection data (REPL slash commands). None in batch mode.
    pub introspection:
        Option<&'a dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    pub lib_dirs: &'a [PathBuf],
    pub platform_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
    /// Optional reference to v4 shared state for cache-hit loading and
    /// codegen input stashing for nice workers.
    /// None for REPL contexts where caching is not used.
    pub shared_state: Option<&'a crate::session_v4::SharedState>,
    /// Historical concrete instantiations captured atomically with a
    /// persisted-source re-registration. Empty for ordinary compilation.
    pub reload_demands: std::sync::Arc<[MonoDemand]>,
    /// **Eval-thread orchestration mode (S93, Invariant SW).** `true` ONLY on
    /// the REPL eval thread driving its own entry module (the Additive path in
    /// `eval.rs`). When set, a dependency gap records a *cycle-check* edge via
    /// `register_dep_edge_for_cycle_check` and leaves the orchestrated module in
    /// its terminal pool — the eval thread is the sole orchestrator and waits on
    /// the dependency itself (`register_dep_for_eval`), so the module must NEVER
    /// be moved to `TypecheckBlocked` (which would make it pool-reclaimable —
    /// the B1 dual-orchestration the retired `eval_owned` flag patched). `false`
    /// for every pool-orchestrated context (`--run`/`--link`, dependency
    /// modules, watcher reload), where `block_for_typecheck` + scheduler requeue
    /// is the correct discipline.
    pub eval_driven: bool,
}

impl<'a> ModuleCompiler<'a> {
    // `tc_env` deleted (W-Absorb): the sole former caller (`set_current_module`)
    // switched to the types-crate `ensure_module_exists` free fn.

    /// Set the current module on both the check_state and the mirror field.
    ///
    /// If the caller already holds a CheckState for this module (REPL
    /// Additive path where the same state is reused across form
    /// evaluations), the state is preserved unchanged — carrying
    /// overloads / resolved_overloads / substitution across evaluations.
    /// If the CheckState is for a different module, it is replaced with a
    /// fresh state so per-module state (overloads, pending resolutions)
    /// does not leak across module boundaries.
    pub fn set_current_module(&mut self, module: ModuleFullPath) {
        cranelisp_types::ensure_module_exists(self.symbol_tables, &module);
        if self.check_state.current_module() != &module {
            self.check_state = CheckState::new(module.clone());
        }
        self.current_module = module;
    }
}

// ---------------------------------------------------------------------------
// ProcessResult — suspension-aware return type
// ---------------------------------------------------------------------------

/// Result of one whole-cluster pass through `process_cluster_once`
/// (S78 in-call-stack restructure).
///
/// Either the cluster fully typechecked in this pass (`Done`), or it hit a
/// dependency gap (`Gap`). On `Gap` the dependency has ALREADY been registered
/// with the scheduler and the gapping module blocked on it
/// (`block_for_typecheck`) — the register-edge is recorded. The caller then
/// drives the wait: the worker wrapper frees back to the pool (the scheduler
/// requeues the gapping module when the dep completes), and the eval wrapper
/// blocks on `wait_module_inmem_complete_blocking(dep)` then retries. Either
/// way the next pass re-runs the cluster from the top with no saved state —
/// the gap does not recur for `dep` because `dep` is now in live.
///
/// There is no saved suspend state, no resume index, no parking map: the
/// in-progress cluster state (parsed forms, staging table, expand position)
/// lived only on this call's stack frame and was dropped when `Gap` returned.
#[allow(clippy::large_enum_variant)]
pub enum ClusterOnce {
    /// Cluster fully typechecked. `program` is the expanded `Vec<TopLevel>`
    /// the caller feeds to codegen (`inline_jit_codegen_for_module`); the
    /// `ProcessedCluster` carries the cluster-level REPL/scheduler metadata
    /// committed via `cluster::insert_cluster`.
    Done {
        processed: crate::cluster::ProcessedCluster,
        program: Vec<TopLevel>,
    },
    /// Hit a dependency gap. `dep` is the module that was registered + blocked
    /// on; the caller drives the wait + retry. (`dep` may already be loaded in
    /// the cache-hit / already-imported case — the block-then-unblock was
    /// issued so the scheduler requeues this module.)
    Gap {
        dep: ModuleFullPath,
        continuation: Vec<Sexp>,
        generation_started: bool,
    },
}

/// Ensure a `TypecheckProduct` entry exists for a module, creating an empty
/// one if needed.
///
/// Sprint 56 Wave 0 (§9.8 G7 pull-forward): the per-module GOT moved onto
/// `SymbolTable.got` — created by `SymbolTable::new` when the typechecker
/// registers the module. Callers that previously relied on this function
/// to seed a fresh GOT must now go through the typecheck module registration
/// path (which constructs `SymbolTable::new`).
pub(crate) fn ensure_typecheck_product(
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    module: &ModuleFullPath,
) {
    typecheck_products.entry(module.clone()).or_insert_with(|| {
        crate::session_v4::TypecheckProduct {
            file_path: None,
            source_text: None,
            unresolved_dispatch: Vec::new(),
        }
    });
}

// ---------------------------------------------------------------------------
// inline_jit_codegen_for_module — unified JIT codegen entry (Sprint 56 Wave 2)
// ---------------------------------------------------------------------------

// `collect_jit_setup` + `collect_jit_setup_public` — DELETED S76 W-Collapse.
// The hand-assembled platform-symbol + GOT-data-base collection is now done
// internally by `Jit::new(symbol_tables)` (backend, BC §3). int assembles no
// JIT symbols by hand.

/// The predicate behind `derive_codegen_batch`'s forced-enrollment
/// `debug_assert!` — "this name resolves to a live concrete body in the
/// module's table".
///
/// Split out as a named function so the instrument's DISCRIMINATION is itself
/// unit-testable without needing production code to be wrong (see
/// `worker::tests::forced_enrollment_predicate_discriminates`). `None` table =
/// the module is not in `tc_modules` yet; that is a legitimate no-table case,
/// not a dead lookup, so it answers `true`.
#[cfg(test)]
fn forced_enrollment_resolves(
    table: Option<&crate::code::SessionSymbolTable>,
    target: &CallableTarget,
) -> bool {
    let Some(table) = table else {
        return true;
    };
    table.callable_target(target).is_some_and(|arm| {
        matches!(
            arm.life,
            Life::Concrete {
                realization: Realization::Body { .. },
                ..
            }
        )
    })
}

/// Derive the typed codegen batch from a `program` and the module's symbol
/// table. Separated out from `inline_jit_codegen_for_module` so unit tests can
/// exercise the target-selection policy without standing up a full JIT
/// pipeline. See the sprint's testing ownership clause.
///
/// The batch includes:
/// - each `TopLevel::Defn`'s `name` (when the symbol-table entry has
///   `ast: Some(_)` and is not a constrained template, a `Polymorphic`
///   generic template (S84 Phase 4B, FIXME 0381 — its concrete mono
///   instances carry the bodies that codegen), or an `Overloaded` base);
/// - every mangled multi-sig variant whose base name appears in `program`;
/// - `__expr` when `program` contains a `TopLevel::Expr` and that wrapper is a
///   live concrete callable (a polymorphic value shown by REPL introspection is
///   a template and has no body to codegen);
/// - for each `TopLevel::TraitImpl`, every live mangled method `Def` of that
///   TRAIT (`{trait}.` prefix + a `$` in the remainder) — not only the methods
///   the impl explicitly provides, so a method whose source changes explicit ->
///   default re-enrolls too (FIXME 0791);
/// - any symbol-table entry with `$` in its name (mono specialisation or
///   other mangling) that is not already compiled (`code: Some(_)` on the
///   entry).
#[doc(hidden)]
pub fn derive_codegen_batch(
    module: &ModuleFullPath,
    program: &[TopLevel],
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
) -> Vec<cranelisp_types::CallableTarget> {
    let Some(table) = tc_modules.get(module) else {
        return Vec::new();
    };
    let mut candidates: Vec<_> = table
        .codegen_targets()
        .map(|(target, arm)| {
            let needs_codegen = matches!(
                arm.life,
                Life::Concrete {
                    realization: Realization::Body { code: None, .. },
                    ..
                }
            );
            (target, needs_codegen)
        })
        .collect();
    candidates.sort_by(|(left, _), (right, _)| left.cmp(right));

    let mut targets = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut push_matching = |predicate: &dyn Fn(&CallableTarget) -> bool| {
        for (target, _) in &candidates {
            if predicate(target) && seen.insert(target.clone()) {
                targets.push(target.clone());
            }
        }
    };

    // Source-present definitions are forced even if publication retained the
    // prior compiled owner for ABI-preserving replacement. For an owned
    // declaration family, matching the authored owner selects every concrete
    // arm without turning an emitted label back into semantic identity.
    for top in program {
        match top {
            TopLevel::Defn(defn) => {
                push_matching(&|target| {
                    callable_target_owner(target).is_some_and(|owner| owner.symbol == defn.name)
                });
            }
            TopLevel::Expr(_) => {
                push_matching(&|target| {
                    callable_target_owner(target)
                        .is_some_and(|owner| owner.symbol.as_ref() == SYNTHETIC_EXPR_WRAPPER)
                });
            }
            TopLevel::TraitImpl(impl_) => {
                // A re-impl must also recompile an omitted method restored from
                // its default body. Select every concrete implementation body
                // for the authored trait, as before, but return its typed
                // binding target. The generated storage spelling is compared
                // only as a private table key; it is never source-resolved.
                let prefix = format!("{}.", impl_.trait_name);
                push_matching(&|target| {
                    callable_target_owner(target).is_some_and(|owner| {
                        owner
                            .symbol
                            .as_ref()
                            .strip_prefix(&prefix)
                            .is_some_and(|rest| rest.contains('$'))
                    })
                });
            }
            _ => {}
        }
    }

    // Pick up newly synthesized constructors/accessors and monomorphic
    // instances which have no corresponding authored top-level form.
    for (target, needs_codegen) in candidates {
        if needs_codegen && seen.insert(target.clone()) {
            targets.push(target);
        }
    }
    targets
}
/// Compile the defined symbols of a module through the unified
/// `compile_to_module` entry point.
///
/// Sprint 56 Wave 2 replacement for `codegen_module_symbols`. Per
/// `design/int/int.md` §4.2 (worker-side per-symbol `Code` write, no merge
/// step) and §6.2 (worker dispatch), plus `pipeline-v4.md` §9.3, the worker:
///
/// 1. Derives `names` — a compilation batch — from `program`'s `TopLevel::Defn`
///    entries plus any mangled multi-sig variants that belong to those base
///    names. This preserves the REPL's incremental model: a new eval compiles
///    only what's new, not the entire module's symbol table.
/// 2. Builds a fresh `Jit` with intrinsic + platform symbols pre-registered
///    and defines `__cranelisp_got_{m}` literal-pool entries for every module.
/// 3. Calls `cranelisp_backend::compile_to_module` — the sole backend entry
///    point. No env, no mode discriminator.
/// 4. Finalizes the JIT inside `compile_to_module` (via the `CodeFinalizer`
///    trait). `compile_to_module` writes `code: Some(_)` onto each
///    `ModuleEntry::Def`. This function mirrors the finalised pointer into
///    the GOT slot and retains the `Arc<Jit>` on `SharedState.kept_jits`.
/// 5. Routes per-symbol `FunctionArtifacts` from `CompilationResult.artifacts`
///    into `SharedState.introspection` keyed by `FQSymbol` (`pipeline-v4.md`
///    §9.6).
/// 6. Notifies the scheduler per compiled symbol.
///
/// The JIT is wrapped in `Arc<Jit>` so a single compile call producing N
/// functions can store N `Code` entries sharing one JIT (see
/// `src/session_v4.rs` `Code` doc — /arch Phase 3a §3).
/// Compile an explicit list of already-registered symbols through the unified
/// `compile_to_module` entry point.
///
/// This is the shared core of `inline_jit_codegen_for_module`: it takes a
/// pre-computed `names` batch (each name must already live on the module's
/// symbol table with `ast: Some(_)` and `got_slot: Some(_)` — Wave 0
/// invariant) and performs steps 2–7 of the compile flow. It does NOT notify
/// the scheduler — the caller is responsible for that.
///
/// Used by:
/// - `inline_jit_codegen_for_module` (primary caller, derives `names` via
///   `derive_codegen_batch`, notifies after)
/// - Macro clause compilation (`compile_macro_clause_with_state`,
///   `compile_macro_clause_inline`) — passes a single-element `names` for the
///   synthesised `__macro_{name}_clause_{idx}` defn. Macro-clause callers
///   notify the scheduler themselves in their outer loop.
#[cfg(test)]
pub fn inline_jit_codegen_for_names(
    module: &ModuleFullPath,
    targets: &[CallableTarget],
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    introspection: Option<
        &dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>,
    >,
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<(), CranelispError> {
    if targets.is_empty() {
        return Ok(());
    }
    // The unified `Jit::new(symbol_tables)` derives the entire JIT symbol set —
    // intrinsics (incl. trace + the 2 parked test intrinsics are folded in
    // below), per-module GOT data symbols, platform-effect jit-names — so int
    // assembles nothing by hand; `shared_state` is threaded for future use by
    // this seam but not read here.
    let _ = shared_state;

    // 3. Build the JIT — the whole symbol set derives from `symbol_tables`
    //    (BC §3 / D41). The host-promised `discover-tests` extern
    //    (`DefKind::PrimitiveExtern`) is registered via `Jit::define_symbol`
    //    inside `build_session_jit`. `catch-runtime-error` resolves from the
    //    intrinsics catalog (no host promise needed). (FIXME 0271)
    let mut jit = build_session_jit(tc_modules)?;

    // 4. Unified codegen entry — S75 5-arg shape (BC §3 invariant 3).
    //    `compile_to_module` writes the GOT slot internally for each compiled
    //    name (D41 #2) and finalises definitions via the `CodeFinalizer`
    //    trait. It returns batch-level `CompilationArtifacts` (clif_ir,
    //    code_size, compile_duration) for introspection.
    // FIXME 0325: capture the CLIF-IR text only when introspection is live.
    // The presence of the introspection map IS the mode discriminator (REPL /
    // trace → Some; `--run`/`--link` batch → None — pipeline-v4 §1, Decision
    // 38). In batch the rendered CLIF would be dropped unread, so backend skips
    // the `func.display()` allocation entirely.
    let capture_clif = introspection.is_some();
    let result = cranelisp_backend::compile_to_module(
        module.clone(),
        targets,
        tc_modules,
        jit.jit_module(),
        capture_clif,
    )?;

    // 5. Decision 41 #1 / Decision 31 Scenario 2: int composes `Code::Jit`
    //    from its owned `Arc<Jit>` (backend only borrows `&mut M`, never owns
    //    the Arc). The per-entry `Arc::clone` is the lifetime root: when a
    //    REPL redefinition replaces an entry, the prior `Code::Jit` clone
    //    drops; when the last clone in the tables drops, `Jit::drop` reclaims
    //    the mmap'd pages.
    #[allow(clippy::arc_with_non_send_sync)]
    let jit_arc = std::sync::Arc::new(jit);

    // 6. For each compiled name: write `Code::Jit(Arc<Jit>)` onto the entry.
    //    The GOT slot is already populated by `compile_to_module` (backend's
    //    own write); int's only job is lifecycle-owner installation +
    //    redefinition observability.
    for target in targets {
        let prior_ptr: Option<*const u8> = read_got_addr(tc_modules, module, target);

        let Some(mut st) = tc_modules.get_mut(module) else {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "fresh-build codegen invariant violation: symbol table \
                     for module '{module}' disappeared during codegen while \
                     writing Code::Jit for '{target:?}'."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };
        let Some(slot) = st.callable_target(target).and_then(|arm| match &arm.life {
            Life::Concrete { slot, .. } => Some(slot.index()),
            _ => None,
        }) else {
            // Not every name in the batch is a Def on this module (e.g. an
            // Import alias); backend handles its own resolution. Skip
            // lifecycle installation for non-local names.
            continue;
        };
        st.publish_compiled_owner(
            target,
            crate::code::Code::jit(std::sync::Arc::clone(&jit_arc)),
        )
        .map_err(|rejection| {
            let (reason, _owner) = rejection.into_parts();
            CranelispError::ModuleError {
                message: reason.to_string(),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
        })?;
        if let Some(prior) = prior_ptr {
            let new_ptr = st.got.load_slot(slot);
            drop(st);
            if let Some(owner) = callable_target_owner(target) {
                crate::got_trace::emit_redefinition(module, &owner.symbol, slot, new_ptr, prior);
            }
        }
    }

    // 7. Route batch-level artifacts into introspection (REPL-only). The S75
    //    `CompilationArtifacts` is batch-grained (concatenated clif_ir +
    //    summed code_size); attribute it to each compiled name. Per-symbol
    //    disasm is on-demand via `cranelisp_backend::produce_disasm` (the
    //    `/disasm` handler reads it lazily).
    if let Some(intr_map) = introspection {
        for owner in targets.iter().filter_map(callable_target_owner) {
            let mut entry = intr_map.entry(owner.clone()).or_default();
            entry.clif_ir = Some(result.clif_ir.clone());
            entry.code_size = Some(result.code_size);
        }
    }

    Ok(())
}

fn compile_and_publish_prepared(
    processed: &mut crate::cluster::ProcessedCluster,
    shared: &crate::session_v4::SharedState,
    capture_clif: bool,
) -> Result<(), CranelispError> {
    compile_and_publish_prepared_with(
        processed,
        shared,
        capture_clif,
        |prepared, jit, capture_clif| {
            cranelisp_backend::compile_to_module(
                prepared.module.clone(),
                &prepared.targets,
                &prepared.tables,
                jit.jit_module(),
                capture_clif,
            )
            .map_err(Into::into)
        },
    )
}

fn compile_and_publish_prepared_with<Compile>(
    processed: &mut crate::cluster::ProcessedCluster,
    shared: &crate::session_v4::SharedState,
    capture_clif: bool,
    compile: Compile,
) -> Result<(), CranelispError>
where
    Compile: FnOnce(
        &PreparedCommit,
        &mut cranelisp_backend::jit::Jit,
        bool,
    ) -> Result<cranelisp_backend::CompilationArtifacts, CranelispError>,
{
    let Some(prepared) = processed.prepared.take() else {
        return Ok(());
    };
    let prepared = *prepared;

    // Construct the JIT from the live tables before taking the target write
    // guard. Its GOT data symbols therefore name the canonical session slabs,
    // including dependency-module slabs. The target slab itself is moved into
    // the prepared target table below without changing its base address.
    let mut jit = if prepared.targets.is_empty() {
        None
    } else {
        Some(build_session_jit(&shared.symbol_tables)?)
    };

    let Some(mut live) = shared.symbol_tables.get_mut(&prepared.module) else {
        return Err(CranelispError::ModuleError {
            message: format!(
                "prepared module '{}' disappeared before publication",
                prepared.module
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    };

    // Resolve every backend member to its final prepared slot before codegen.
    // Snapshot that cell from the canonical slab: reused cells carry the old
    // pointer, while fresh cells are null. The snapshots are the compensation
    // set if compiled publication later refuses.
    let mut got_snapshots = Vec::new();
    {
        let table =
            prepared
                .tables
                .get(&prepared.module)
                .ok_or_else(|| CranelispError::ModuleError {
                    message: format!("prepared module '{}' disappeared", prepared.module),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
        for target in &prepared.targets {
            let Some(arm) = table.callable_target(target) else {
                return Err(CranelispError::ModuleError {
                    message: format!("prepared target '{target:?}' is missing or not executable"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            let slot = match &arm.life {
                Life::Concrete {
                    slot,
                    realization: Realization::Body { .. },
                    ..
                } => slot.index(),
                _ => {
                    return Err(CranelispError::ModuleError {
                        message: format!("prepared target '{target:?}' has no concrete body slot"),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    });
                }
            };
            got_snapshots.push((target.clone(), slot, live.got.load_slot(slot) as usize));
        }
    }

    let prior_ptrs: std::collections::HashMap<_, _> = prepared
        .staging
        .codegen_targets()
        .filter_map(|(target, arm)| {
            let slot = match &arm.life {
                Life::Concrete { slot, .. } => slot.index(),
                _ => return None,
            };
            let ptr = got_snapshots
                .iter()
                .find(|(snapshot_target, snapshot_slot, _)| {
                    snapshot_target == &target && *snapshot_slot == slot
                })
                .map(|(_, _, ptr)| *ptr as *const u8)
                .unwrap_or_else(|| live.got.load_slot(slot));
            Some((target, (slot, ptr)))
        })
        .collect();

    // Backend must patch the canonical slab only after it has finalized the
    // complete batch, while this writer guard prevents a macro reader from
    // pairing the old binding/owner with a new reused-slot pointer. Moving the
    // slab preserves its base address, so code emitted by `jit` continues to
    // name the same cells after it is moved back into `live`.
    if jit.is_some() {
        let mut table = prepared.tables.get_mut(&prepared.module).ok_or_else(|| {
            CranelispError::ModuleError {
                message: format!("prepared module '{}' disappeared", prepared.module),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        std::mem::swap(&mut live.got, &mut table.got);
    }

    let compiled = if let Some(mut jit) = jit.take() {
        let result = compile(&prepared, &mut jit, capture_clif);
        let artifacts = match result {
            Ok(artifacts) => artifacts,
            Err(error) => {
                restore_prepared_got(
                    &prepared.module,
                    &prepared.tables,
                    &mut live,
                    &got_snapshots,
                )?;
                return Err(error);
            }
        };
        #[allow(clippy::arc_with_non_send_sync)]
        let jit = std::sync::Arc::new(jit);
        Some(PreparedCompilation {
            jit,
            clif_ir: artifacts.clif_ir,
            code_size: artifacts.code_size,
            drop_glues: artifacts.drop_glues,
        })
    } else {
        None
    };
    let compiled_owners = compiled
        .as_ref()
        .map(|compiled| {
            prepared
                .staging
                .codegen_targets()
                .map(|(target, _)| {
                    (
                        target,
                        crate::code::Code::jit(std::sync::Arc::clone(&compiled.jit)),
                    )
                })
                .collect()
        })
        .unwrap_or_default();

    let mut records = match live.publish_compiled_staged(
        prepared.staging,
        &prepared.decisions,
        compiled_owners,
    ) {
        Ok(records) => records,
        Err(rejection) => {
            let (reason, owners) = rejection.into_parts();
            retain_and_restore_rejected_compilation(
                shared,
                &prepared.module,
                owners,
                &got_snapshots,
                &prepared
                    .tables
                    .get(&prepared.module)
                    .ok_or_else(|| CranelispError::ModuleError {
                        message: format!("prepared module '{}' disappeared", prepared.module),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    })?
                    .got,
            );
            if compiled.is_some() {
                restore_prepared_got(&prepared.module, &prepared.tables, &mut live, &[])?;
            }
            return Err(CranelispError::ModuleError {
                message: format!("compiled publication refused: {reason}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
    };
    let mut retained = shared
        .retained_code
        .lock()
        .unwrap_or_else(|error| error.into_inner());
    for record in &mut records {
        for body in &mut record.bodies {
            if let Some(owner) = body.displaced_owner.take() {
                retained.push(crate::redefine::RetainedCode::frozen(
                    &prepared.module,
                    &record.symbol,
                    body.prior_slot.map(|slot| slot.index()),
                    owner,
                ));
            }
        }
    }
    drop(retained);
    if compiled.is_some() {
        // The canonical slab returns to the now-published live table before the
        // write guard is released. The prepared table receives the temporary
        // empty slab and can be dropped without invalidating emitted GOT bases.
        restore_prepared_got(&prepared.module, &prepared.tables, &mut live, &[])?;
    }
    let trace_facts: Vec<_> = records
        .iter()
        .flat_map(|record| {
            record.bodies.iter().map(|body| {
                let prior = body
                    .prior_target
                    .as_ref()
                    .and_then(|target| prior_ptrs.get(target))
                    .map(|(slot, ptr)| (*slot, *ptr));
                let published = body
                    .published_slot
                    .map(|slot| (slot.index(), live.got.load_slot(slot.index())));
                (record.symbol.clone(), prior, published)
            })
        })
        .collect();
    drop(live);

    for (name, prior, published) in trace_facts {
        if let (Some((old_slot, _)), Some((new_slot, _))) = (prior, published)
            && old_slot != new_slot
        {
            crate::got_trace::emit_slot_freeze(&prepared.module, &name, old_slot, new_slot);
        }
        if let (Some((old_slot, prior_ptr)), Some((_, new_ptr))) = (prior, published)
            && !prior_ptr.is_null()
        {
            crate::got_trace::emit_redefinition(
                &prepared.module,
                &name,
                old_slot,
                new_ptr,
                prior_ptr,
            );
        }
    }
    if let Some(compiled) = compiled {
        let owner = crate::code::Code::jit(std::sync::Arc::clone(&compiled.jit));
        for (ty, artifact) in compiled.drop_glues {
            shared.fresh_jit_drop_glues.insert(
                (prepared.module.clone(), ty),
                FreshJitDropGlue {
                    artifact,
                    owner: owner.clone(),
                },
            );
        }
        if let Some(introspection) = shared.introspection.as_ref() {
            let names: std::collections::BTreeSet<_> = prepared
                .targets
                .iter()
                .filter_map(callable_target_owner)
                .map(|owner| owner.symbol.clone())
                .collect();
            for name in names {
                let fq = cranelisp_types::FQSymbol {
                    module: prepared.module.clone(),
                    symbol: name,
                };
                let mut record = introspection.entry(fq).or_default();
                record.clif_ir = Some(compiled.clif_ir.clone());
                record.code_size = Some(compiled.code_size);
            }
        }
    }
    shared
        .typecheck_products
        .entry(prepared.module.clone())
        .or_insert_with(|| crate::session_v4::TypecheckProduct {
            file_path: None,
            source_text: None,
            unresolved_dispatch: Vec::new(),
        })
        .unresolved_dispatch = prepared.unresolved_dispatch;
    processed.set_redefinitions(prepared.outcomes);
    let notification_names = prepared
        .targets
        .iter()
        .filter_map(callable_target_owner)
        .map(|owner| owner.symbol.clone())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    processed.pending_codegen_notification = Some((prepared.module.clone(), notification_names));
    Ok(())
}

fn restore_prepared_got(
    module: &ModuleFullPath,
    tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    live: &mut crate::code::SessionSymbolTable,
    snapshots: &[(CallableTarget, usize, usize)],
) -> Result<(), CranelispError> {
    let mut table = tables
        .get_mut(module)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("prepared module '{module}' disappeared"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    for (_, slot, ptr) in snapshots {
        table.got.store_slot(*slot, *ptr as *const u8);
    }
    std::mem::swap(&mut live.got, &mut table.got);
    Ok(())
}

fn retain_and_restore_rejected_compilation(
    shared: &crate::session_v4::SharedState,
    module: &ModuleFullPath,
    owners: std::collections::HashMap<CallableTarget, crate::code::Code>,
    snapshots: &[(CallableTarget, usize, usize)],
    got: &cranelisp_types::GotTable,
) {
    // The recovered owner map stays in this frame while every cell is restored;
    // only after no canonical cell can name the rejected code do the owners
    // move into session retention.
    for (_, slot, ptr) in snapshots {
        got.store_slot(*slot, *ptr as *const u8);
    }
    let mut retained = shared
        .retained_code
        .lock()
        .unwrap_or_else(|error| error.into_inner());
    for (target, owner) in owners {
        let slot = snapshots
            .iter()
            .find(|(snapshot_target, _, _)| snapshot_target == &target)
            .map(|(_, slot, _)| *slot);
        let name = callable_target_owner(&target)
            .map(|owner| owner.symbol.clone())
            .unwrap_or_else(|| Symbol::from("<unknown-callable-target>"));
        retained.push(crate::redefine::RetainedCode::frozen(
            module, &name, slot, owner,
        ));
    }
}

pub(crate) fn compile_and_publish_processed_without_notify(
    processed: &mut crate::cluster::ProcessedCluster,
    shared: &crate::session_v4::SharedState,
) -> Result<(), CranelispError> {
    compile_and_publish_prepared(processed, shared, shared.introspection.is_some())
}

pub(crate) fn compile_and_publish_processed(
    processed: &mut crate::cluster::ProcessedCluster,
    shared: &crate::session_v4::SharedState,
) -> Result<(), CranelispError> {
    compile_and_publish_processed_without_notify(processed, shared)?;
    notify_processed_codegen(processed, shared);
    Ok(())
}

pub(crate) fn notify_processed_codegen(
    processed: &mut crate::cluster::ProcessedCluster,
    shared: &crate::session_v4::SharedState,
) {
    if let Some((module, names)) = processed.pending_codegen_notification.take() {
        if names.is_empty() {
            shared.scheduler.notify_inmem_codegen_complete(
                &module,
                &Symbol::from("__empty_module"),
                true,
            );
        } else {
            let total = names.len();
            for (index, name) in names.iter().enumerate() {
                shared
                    .scheduler
                    .notify_inmem_codegen_complete(&module, name, index + 1 == total);
            }
        }
    }
}

/// Publish a source module's complete scheduler readiness in the only valid
/// order: finish the post-publish in-memory notification first, then expose
/// `TypecheckDone` to dependent modules.
fn notify_processed_ready(
    processed: &mut crate::cluster::ProcessedCluster,
    shared: &crate::session_v4::SharedState,
    module: &ModuleFullPath,
) {
    notify_processed_codegen(processed, shared);
    shared.scheduler.notify_typecheck_done(module);
}

/// The ABI names of the `DefKind::PrimitiveExtern` symbols whose bodies are
/// **host-promised only in a live session** — int hands them to the JIT via
/// `Jit::define_symbol` (below), so they resolve in REPL / `--run` but have NO
/// AOT symbol under `--link` (the standalone executable has no live session to
/// scan). This is the single source of truth shared by two sites:
///
///   1. `build_session_jit` — promises each one to the live-session JIT.
///   2. `crate::exe::reject_dev_session_externs_in_link` — refuses a `--link`
///      build that references any of them, with a friendly compile-time
///      diagnostic instead of a raw `cc` `undefined reference` (FIXME 0406).
///
/// The list is the structural discriminator the friendly-rejection gate keys on
/// (test-discovery.md §4.5): a `PrimitiveExtern` named here is dev-session-only;
/// other `PrimitiveExtern`s (`catch-runtime-error`, `bind`, the intrinsic-type
/// accessors) resolve in `--link` from binary-exported / intrinsics-catalog
/// symbols and are NOT rejected. Prefer extending this list over a name match
/// elsewhere so any future REPL-only extern inherits both the promise and the
/// rejection from one edit.
pub(crate) const DEV_SESSION_ONLY_EXTERNS: &[&str] = &["discover-tests"];

/// The name of the synthetic zero-arg `Defn` that wraps a bare top-level
/// `TopLevel::Expr` for typecheck + codegen dispatch (see `wrap_exprs_as_defns`
/// in `process_form/form_dispatch.rs` and `derive_codegen_batch` above). It is
/// an internal compiler artifact, NOT a user definition — every user-facing
/// symbol listing (`/list`, `/exports`, the agent harvest) MUST exclude it, the
/// same way `$`-mangled internal names and `SpecialForm` entries are excluded
/// (`repl/spec.md §3.3`). Single source of the literal so the filters cannot
/// drift from the synthesis site.
pub(crate) const SYNTHETIC_EXPR_WRAPPER: &str = "__expr";

/// True when `name` is an internal compiler artifact that MUST NOT appear in a
/// user-facing symbol listing NOR in the persisted backing source — a
/// `$`-mangled overload/mono/specialisation name (these ride the `.meta`/`.o`
/// compiled-state channel, never source) or the synthetic top-level-expression
/// wrapper (`SYNTHETIC_EXPR_WRAPPER`, always EXACTLY `"__expr"` — a user symbol
/// like `__expr-helper` is a real definition and is NOT matched). Shared by
/// `/list`, `/exports`, the agent harvest, and `save::generate_fns_and_macros`
/// (FIXME 0549) so the exclusion is uniform (one predicate, not four drifting
/// copies).
pub(crate) fn is_internal_listing_name(name: &str) -> bool {
    name.contains('$') || name == SYNTHETIC_EXPR_WRAPPER
}

/// Classify generated callable rows using lifecycle provenance as well as the
/// legacy private spelling. Canonical instance keys no longer contain `$`, but
/// a concrete `minted_from` backlink still distinguishes them from authored
/// declarations without parsing their readable key.
pub(crate) fn is_internal_listing_entry<C: cranelisp_types::CodeStore>(
    name: &str,
    entry: &Binding<C>,
) -> bool {
    is_internal_listing_name(name)
        || entry.callable().is_some_and(|callable| {
            matches!(
                callable.arm.life,
                Life::Concrete {
                    minted_from: Some(_),
                    ..
                }
            )
        })
}

/// The single user-facing category of a symbol-table entry — the ONE
/// `ModuleEntry`/`DefKind` → category mapping shared by every int
/// listing/introspection surface (`/list`, `/exports`,
/// `list_user_definitions`, `describe_symbol`). Returns `None` for entries
/// that are never surfaced as a user definition (`Import`, `Ambiguous`,
/// `TraitImpl`).
///
/// Before FIXME 0440 each of those four sites transcribed this match
/// independently; a new `DefKind` variant or a "should constructors appear
/// in listing X" change was an N-site drift waiting to happen — the same
/// shape that produced the S91 `__expr` filter bug, one level up from the
/// `is_internal_listing_name` filter (Principle 7, single source of truth).
/// The callers keep ONLY their presentation concerns: `/list` drops the
/// `Constructor` category, `/exports` folds it into `Type`, and
/// `list_user_definitions` skips `SpecialForm`.
pub(crate) fn classify_listing_entry(
    entry: &Binding<crate::code::Code>,
) -> Option<crate::session_v4::SymbolCategory> {
    use crate::session_v4::SymbolCategory;
    Some(match &entry.declaration {
        Decl::Macro(_) => SymbolCategory::Macro,
        Decl::Overloaded(_) => SymbolCategory::Fn,
        Decl::Callable(callable) => match callable.origin {
            CallableOrigin::Ctor { .. } => SymbolCategory::Constructor,
            _ => SymbolCategory::Fn,
        },
        Decl::Type(_) => SymbolCategory::Type,
        Decl::Trait(_) => SymbolCategory::Trait,
        Decl::SpecialForm(_) => SymbolCategory::SpecialForm,
        Decl::TraitMethod(_) | Decl::ImplShell(_) => return None,
    })
}

/// Build the session JIT from the symbol tables (the unified `Jit::new`
/// boundary, BC §3), then register the host-promised dev-session-only externs.
///
/// `Jit::new` registers the full intrinsics catalog (incl. trace +
/// `catch-runtime-error`) + per-module GOT data symbols + platform-effect
/// jit-names. `discover-tests` is a `DefKind::PrimitiveExtern` whose body lives
/// in int (it reads the live typed session state — `cranelisp-intrinsics`
/// cannot name `Code`, Principle 18). int promises it here via the additive
/// `Jit::define_symbol` escape hatch (test-discovery.md §6; FIXME 0271/0269).
pub(crate) fn build_session_jit(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
) -> Result<cranelisp_backend::jit::Jit, CranelispError> {
    let jit = cranelisp_backend::jit::Jit::new(tc_modules)?;
    for name in DEV_SESSION_ONLY_EXTERNS {
        debug_assert_eq!(
            *name, "discover-tests",
            "the only dev-session-only extern body wired here is discover-tests; \
             a new entry in DEV_SESSION_ONLY_EXTERNS needs its own define_symbol",
        );
        jit.define_symbol(name, crate::session_v4::discover_tests_extern as *const u8);
    }
    Ok(jit)
}

/// Read the runtime GOT address for `name` in `module`, following Import
/// chains, or `None` if no slot / address is assigned. Used to capture the
/// prior pointer for redefinition observability.
#[cfg(test)]
fn read_got_addr(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    target: &CallableTarget,
) -> Option<*const u8> {
    let st = tc_modules.get(module)?;
    let slot = st.callable_target(target).and_then(|arm| match &arm.life {
        Life::Concrete { slot, .. } => Some(slot.index()),
        _ => None,
    })?;
    let ptr = st.got.load_slot(slot);
    if ptr.is_null() { None } else { Some(ptr) }
}

/// Follow a written binding name through candidate chains to its terminal
/// callable slot. Retained for the integration-level GOT routing tests; the
/// typed compilation path above does not use written names.
#[cfg(test)]
fn lookup_got_slot(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> Option<usize> {
    cranelisp_types::resolve_terminal_entry_and_home(tc_modules, module, name.as_ref())
        .and_then(|(binding, _)| binding.callable_got_slot())
}

// ---------------------------------------------------------------------------
// Linker-based loading for cached modules (Step 13 — cache-hit inmem codegen)
// ---------------------------------------------------------------------------

/// Register user-callable primitive externs that the cache-restore `Linker`
/// would otherwise be unable to resolve (FIXME 0299).
///
/// Primitive-ish entries fall into two groups:
///   1. Ring primitives (`add-i64`, `str-concat`, …) — `DefKind::Primitive`
///      entries living in the session `primitives` module with a populated GOT
///      slot (copied from `cranelisp_primitives::PRIMITIVES_TABLE` by
///      `populate_ring0_got_slots`), already registered by the GOT-pointer walk
///      below.
///   2. Synthetic slot-less externs (`sconcat`, the Trace accessors,
///      `catch-runtime-error`, …) — `DefKind::PrimitiveExtern` entries seeded by
///      `bootstrap.rs` with `code: None` and NO GOT slot (S83 reshape, FIXME
///      0356/0357/0360: these are by-ABI-name `Linkage::Import` callees, not
///      GOT-indirect). Their bodies are binary-exported symbols
///      (`#[unsafe(export_name = "…")]` in `cranelisp-primitives` /
///      `cranelisp-intrinsics`, statically linked into the host). The fresh JIT
///      resolves them through its exported-symbol fallback; the cache `Linker`
///      has none, so we resolve them here via the host's own symbol table
///      (`dlsym(RTLD_DEFAULT, name)`) and register the address.
///
/// We walk every `DefKind::PrimitiveExtern` and attempt a `dlsym` of its bare
/// name. A miss is silently skipped (the relocation pass surfaces a clear
/// `unresolved symbol` error if the `.o` actually needs it).
fn register_binary_exported_primitives(
    linker: &mut cranelisp_backend::cache::linker::Linker,
    shared_state: &crate::session_v4::SharedState,
) {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    for st_entry in shared_state.symbol_tables.iter() {
        let st = st_entry.value();
        for (name, entry) in st.all_symbols() {
            // Slot-less `PrimitiveExtern` entries are the synthetic externs
            // resolved by ABI name (S83 reshape, FIXME 0360). Ring
            // `DefKind::Primitive` entries carry a GOT slot and are registered
            // by the GOT-pointer walk — skip them here.
            if !matches!(
                entry.callable(),
                Some(callable)
                    if matches!(callable.origin, CallableOrigin::RustPrimitive)
                        && matches!(callable.arm.life, Life::HostPromised)
            ) {
                continue;
            }
            let bare = name.as_ref();
            if !seen.insert(bare.to_string()) {
                continue;
            }
            if let Some(ptr) = dlsym_host_symbol(bare) {
                linker.register_symbol(bare, ptr);
            }
        }
    }
}

/// Resolve a symbol exported by the host binary itself (RTLD_DEFAULT). Returns
/// `None` when the symbol is not exported. Used to register binary-exported
/// primitive externs with the cache-restore `Linker` (FIXME 0299).
pub(crate) fn dlsym_host_symbol(name: &str) -> Option<*const u8> {
    let c_name = std::ffi::CString::new(name).ok()?;
    // SAFETY: `dlsym(RTLD_DEFAULT, …)` searches the global symbol scope of the
    // running process for `name`. The returned pointer (when non-null) is the
    // address of a `'static` `extern "C"` fn statically linked into the host
    // (`cranelisp-primitives`), valid for the process lifetime.
    let ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_name.as_ptr()) };
    if ptr.is_null() {
        None
    } else {
        Some(ptr as *const u8)
    }
}

/// Load a cached module's `.o` file via Linker, wiring code pointers into
/// the per-module GOT. This is the inmem codegen fast-path for cache-hit
/// modules: one mmap + relocation pass loads all symbols at once.
///
/// Returns the list of symbol names that were loaded, for scheduler notification.
fn load_cached_module_via_linker(
    module: &ModuleFullPath,
    shared_state: &crate::session_v4::SharedState,
) -> Result<Vec<Symbol>, CranelispError> {
    use cranelisp_backend::cache;

    // Sprint 67 Cluster B sub-fire 3: cache dir via ObjectCache facade.
    let cache_dir = shared_state
        .cache
        .cache_dir()
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("no cache directory for cache-hit loading of '{}'", module),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })?;

    // Load metadata from disk.
    let cached = cache::try_load_cached_module(&cache_dir, module)?.ok_or_else(|| {
        CranelispError::ModuleError {
            message: format!("cache metadata missing for module '{}'", module),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        }
    })?;

    if !cached.has_object {
        return Err(CranelispError::ModuleError {
            message: format!("cached .o file missing for module '{}'", module),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        });
    }

    // Build Linker with all known symbols.
    let mut linker = cache::linker::Linker::new()?;

    // S76: register the full intrinsics catalog (incl. trace) from
    // `cranelisp_intrinsics::intrinsics_table()` — the same source `Jit::new`
    // consumes (backend's `intrinsic_symbols()` is retired).
    for entry in cranelisp_intrinsics::intrinsics_table() {
        linker.register_symbol(entry.name, entry.ptr);
    }

    // S77 W-MacroTrait (FIXME 0299): register user-callable primitive externs
    // that are NOT in the intrinsics catalog and have no GOT-stored pointer —
    // notably the synthetic `macros` module's `sconcat`/`quote-sexp` (seeded by
    // `bootstrap.rs` with `code: None` + no GOT slot). The fresh JIT resolves
    // these via its `symbol_lookup_fn` falling back to the binary's exported
    // symbols (each is `#[unsafe(export_name = "...")]` in `cranelisp-primitives`,
    // statically linked into the host). The cache-restore `Linker` has NO such
    // dlsym fallback (`cache/linker.rs` resolves only its registered maps), so a
    // cached `.o` referencing `sconcat` failed with `unresolved symbol: sconcat`
    // (the disk-cache gap noted in `src/CLAUDE.md`). Mirror the JIT by resolving
    // every `DefKind::Primitive` whose GOT slot is empty against the host's own
    // exported symbol and registering it with the linker.
    register_binary_exported_primitives(&mut linker, shared_state);

    // Register platform symbols by walking symbol tables. Every
    // `PlatformEffect` entry carries its DLL function pointer in the owning
    // module's GOT slot (`got.load_slot(got_slot)`); the symbol-table key IS
    // the JIT linker name (the retired `jit_name` field no longer exists —
    // `src/CLAUDE.md` §"JIT Symbol Names").
    for st_entry in shared_state.symbol_tables.iter() {
        let st = st_entry.value();
        for (name, entry) in st.all_symbols() {
            // The platform effect's GOT slot now rides on its variant (S83
            // reshape, FIXME 0358 — PlatformEffect IS GOT-callable).
            if matches!(
                entry.callable().map(|callable| &callable.origin),
                Some(CallableOrigin::PlatformEffect { .. })
            ) && let Some(got_slot) = entry.callable_got_slot()
            {
                let ptr = st.got.load_slot(got_slot);
                if !ptr.is_null() {
                    linker.register_symbol(name.as_ref(), ptr);
                }
            }
        }
    }

    // Register code pointers from already-compiled modules. The callable
    // address is the per-module GOT slot (the single source of truth — no
    // per-entry `ptr`). Read it via `got.load_slot(got_slot)`.
    for st_entry in shared_state.symbol_tables.iter() {
        let st = st_entry.value();
        for (name, entry) in st.all_symbols() {
            if matches!(
                entry.callable().map(|callable| &callable.arm.life),
                Some(Life::Concrete {
                    realization: Realization::Body { code: Some(_), .. },
                    ..
                })
            ) && let Some(slot) = entry.callable_got_slot()
            {
                let ptr = st.got.load_slot(slot);
                if !ptr.is_null() {
                    linker.register_symbol(name.as_ref(), ptr);
                }
            }
        }
    }

    // Register per-module GOT data symbols for cross-module GOT-indirect calls.
    // `got_data_symbol_name` is now types-owned.
    for st_entry in shared_state.symbol_tables.iter() {
        let name = cranelisp_types::got_data_symbol_name(st_entry.key());
        linker.register_symbol(&name, st_entry.value().got.base_ptr());
    }

    // Get this module's GOT table from the symbol table.
    let module_got = shared_state
        .symbol_tables
        .get(module)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("no symbol table for cached module '{}'", module),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })?
        .got
        .clone();

    // Load the .o file — one mmap + relocation pass.
    let fn_addrs = cache::load_cached_object(&mut linker, &cached)?;

    // Wire code pointers into the per-module GOT using slot assignments
    // from the symbol table.
    //
    // Sprint 58 Wave 2 (Decision 37 — "no swallowed failures"): each cached
    // symbol with a `got_slot` MUST resolve through the linker. Per
    // Decision 36, function symbols are bare-Local everywhere uniformly, so
    // `linker.get_symbol(bare)` succeeds for every defined function. A
    // resolution failure here means either (a) the cached `.o` is corrupt
    // / mismatched against the cached `.meta.json`, or (b) the `/backend`
    // contract was violated. Either way we surface a hard error rather
    // than silently produce an `inmem_done` state with empty GOT slots —
    // the latter is a Decision-31 safety-invariant violation (a slot that
    // resolves to NULL is reachable from the code path that calls it).
    let mut loaded_targets = Vec::new();
    for (target, arm) in cached.symbol_table().codegen_targets() {
        let Life::Concrete { slot, .. } = &arm.life else {
            continue;
        };
        let slot = slot.index();
        let Some(ptr) = fn_addrs.get(&target).copied() else {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "cache-hit symbol resolution failed for target '{target:?}' in '{module}': \
                     `.o` linker did not define its expected emitted symbol. \
                     This indicates a cache inconsistency — the cached `.meta.json` \
                     records a callable body whose code is missing from the `.o`."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };
        module_got.store_slot(slot, ptr);
        loaded_targets.push(target);
    }

    // Sprint 58 Step 5b §3.2 + Wave 3b (Decision 35 Cache-restore): after
    // fresh build, the integration layer writes `Code::Jit { jit, ptr }`
    // onto each `ModuleEntry::Def.code`; the cache-hit Linker path mirrors
    // that with `Code::Linker { linker, ptr }`, sharing one `Arc<Linker>`
    // across every entry the linker materialised. Reclamation of the
    // mmap'd `.o` pages happens when the last `Code::Linker` referencing
    // the Arc drops (per-module reclaim, dual of Scenario 2's per-batch
    // JIT reclaim).
    let linker_arc = std::sync::Arc::new(linker);
    if let Some(mut live_table) = shared_state.symbol_tables.get_mut(module) {
        let mut displaced_owners = Vec::new();
        for target in &loaded_targets {
            let owner = crate::code::Code::linker(std::sync::Arc::clone(&linker_arc));
            match live_table.publish_compiled_owner(target, owner) {
                Ok(Some(displaced)) => displaced_owners.push(displaced),
                Ok(None) => {}
                Err(rejection) => {
                    return Err(CranelispError::ModuleError {
                        message: format!(
                            "cache-hit owner publication failed for '{target:?}' in '{module}': {}",
                            rejection.reason()
                        ),
                        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                    });
                }
            }
        }
        drop(displaced_owners);
    }
    // Sprint 58 Wave 3b: `kept_linkers` dissolved per Decision 35 — the
    // `Arc<Linker>` retention root is now the per-entry `Code::Linker`.
    // No session-level push needed.
    drop(linker_arc);

    // S86 D5b: register the cache-restored `.o` into the `--link` set. The
    // only writer of `compiled_o_paths` was `compile_module_object` (the
    // freshly-compiled / cache-MISS path), so a module restored from a prior
    // `--run`'s cache (cache-HIT) was absent from `all_paths()` at `--link`
    // time — `cc` linked without it and `user.o`'s cross-module
    // `__cranelisp_got_{dep}` reference was undefined. The `.o` we just
    // mmap+relocated is `cached.object_path` (`has_object` is asserted above,
    // so this is the genuine on-disk object, not a generic-only no-codegen
    // module). `append_o_path` dedups, so a module that is both cache-restored
    // and later freshly recompiled is listed once.
    shared_state.cache.append_o_path(cached.object_path.clone());

    Ok(loaded_targets
        .iter()
        .filter_map(callable_target_owner)
        .map(|owner| owner.symbol.clone())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect())
}

/// Handle a cache-hit codegen work item: check if the module is cached
/// and load it via Linker, then notify the scheduler.
///
/// Shared helper for both `priority_worker_loop` (inline) and
/// `priority_worker_thread` (spawned). Returns Ok(true) if the module
/// was loaded, Ok(false) if it was not cached (no-op).
pub(crate) fn handle_cached_codegen(
    module: &ModuleFullPath,
    shared_state: Option<&crate::session_v4::SharedState>,
    scheduler: &CompileScheduler,
) -> Result<bool, CranelispError> {
    // Sprint 67 Cluster B sub-fire 2e: read via scheduler facade method.
    let is_cached = shared_state
        .map(|s| s.scheduler.cached_module_contains(module))
        .unwrap_or(false);

    if !is_cached {
        return Ok(false);
    }

    let shared = shared_state.ok_or_else(|| CranelispError::ModuleError {
        message: format!("no shared state for cache-hit loading of '{}'", module),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
    })?;

    // Sprint 57 Wave 2 G6: `codegen_products` deleted. The linker is retained
    // on `shared.kept_linkers` by `load_cached_module_via_linker`; compiled
    // code pointers come from `ModuleEntry::Def.code` on the symbol tables.
    // Sprint 57 Wave 3 G8: platform symbols are registered from the symbol
    // tables' `PlatformEffect` entries; the `PlatformRegistry` parameter is
    // gone.
    match load_cached_module_via_linker(module, shared) {
        Ok(symbols) => {
            scheduler.notify_inmem_codegen_batch_complete(module, &symbols);
            Ok(true)
        }
        Err(e) => {
            scheduler.notify_module_failed(module, e);
            // E3 failure-edge hook (FIXME 0562): complete the `/search` burn-down
            // for a module that fails at cache-hit `.o` loading after the index
            // was armed (armed-gated no-op otherwise).
            crate::session_v4::index_worker::on_module_failed(shared, module);
            Ok(false)
        }
    }
}

// ---------------------------------------------------------------------------
// priority_worker_loop — dispatch scheduler work items
// ---------------------------------------------------------------------------

// `ModuleSuspendState` — deleted in the S78 in-call-stack restructure. The
// per-module half-finished state (accumulator, expanded program, pass1-done
// flag) that used to be saved across a thread-hopping resume is gone: in the
// retry-from-top model the whole cluster re-runs from its packet sexps against
// now-larger live state, so there is nothing to save. All in-progress state
// lives on `process_cluster_once`'s stack frame and is dropped on a gap.

// `priority_worker_loop` — deleted Sprint 59 Workstream A §7 Step 5.
//
// This was the inline-variant worker loop used exclusively by
// `CompilerSession::compile_dep_inline` to run a session-side parallel
// orchestrator on the REPL eval thread. Its only caller is gone, so the
// function itself retires — `priority_worker_loop_shared` below is the
// single worker loop for every persistence entry point now.
//
// The header doc comment at the top of this file has been updated to
// reflect the single-worker-loop shape.

// ---------------------------------------------------------------------------
// Persistent priority worker loop (Sprint 57 Wave 4 G9)
// ---------------------------------------------------------------------------
//
// Per `design/int/persistent-workers.md` §4.2, priority workers are now
// session-persistent: spawned in `CompilerSession::new`, parked on the
// scheduler's `priority_work_available` condvar until work arrives or
// shutdown is signalled. This replaces the scoped-thread + `PriorityWorkerRefs`
// pattern of Wave 3.
//
// `module_sexps` and `suspend_states` now live on `SharedState` so that any
// worker can resume a blocked module (§5.3). `lib_dirs`, `platform_dirs`,
// and `project_root` are also on `SharedState` for direct worker access —
// the old borrowed-reference refs struct is gone.

/// Main loop for a spawned persistent priority worker thread.
///
/// Parks on `scheduler.take_priority_work_blocking()` (condvar) when no work
/// is available, and exits only when shutdown is signalled or all inmem
/// work is exhausted and no more modules could arrive. Workers process work
/// items for the full session lifetime.
///
/// Sprint 57 Wave 4 G9 per `persistent-workers.md` §4.1.
pub fn priority_worker_loop_shared(shared: &crate::session_v4::SharedState) {
    use std::panic::AssertUnwindSafe;
    loop {
        let work = shared.scheduler.take_priority_work_blocking();
        match work {
            Some(PriorityWork::Typecheck {
                module,
                sexps,
                instantiation_demands,
                generation_started,
            }) => {
                // FIXME 0285 defect 2 — worker-panic→park robustness. A panic
                // inside the work handler (e.g. an unresolved-symbol panic from
                // the JIT at finalize, or any `unreachable!`) would otherwise
                // unwind this worker thread WITHOUT marking the module Failed —
                // the main thread then parks on the completion condvar forever
                // (no notification ever fires) → a hang, not an error+exit.
                // Catch the unwind, convert it to a module failure, and notify
                // so `wait_inmem_complete_blocking` returns `ModuleFailed`.
                let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    handle_typecheck_work_shared(
                        shared,
                        &module,
                        &sexps,
                        instantiation_demands,
                        generation_started,
                    )
                }));
                match result {
                    Ok(Ok(())) => {}
                    Ok(Err(e)) => {
                        shared.scheduler.notify_module_failed(&module, e);
                        // E3 failure-edge hook (FIXME 0562): the symmetric peer of
                        // the `on_module_published` Done-arm call — a module popped
                        // in-flight and left pending by index branch (a) that then
                        // FAILS typecheck is marked skipped so the `/search`
                        // burn-down completes (armed-gated no-op otherwise).
                        crate::session_v4::index_worker::on_module_failed(shared, &module);
                    }
                    Err(panic) => {
                        let msg = panic_message(&panic);
                        shared.scheduler.notify_module_failed(
                            &module,
                            CranelispError::CodegenError {
                                message: format!(
                                    "worker thread panicked while compiling module \
                                     '{module}': {msg}"
                                ),
                                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                            },
                        );
                        crate::session_v4::index_worker::on_module_failed(shared, &module);
                    }
                }
            }
            Some(PriorityWork::JitCodegen(module, _symbol)) => {
                // Cache-hit module: load entire .o via Linker (batch load).
                // Sprint 57 Wave 3 G8: no PlatformRegistry lock — platform
                // symbols are read from the symbol tables inside the cache
                // loader. Same panic→Failed robustness (FIXME 0285 defect 2).
                let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    handle_cached_codegen(&module, Some(shared), &shared.scheduler)
                }));
                if let Err(panic) = result {
                    let msg = panic_message(&panic);
                    shared.scheduler.notify_module_failed(
                        &module,
                        CranelispError::CodegenError {
                            message: format!(
                                "worker thread panicked while loading cached \
                                 module '{module}': {msg}"
                            ),
                            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                        },
                    );
                    // E3 failure-edge hook (FIXME 0562) — armed-gated no-op in batch.
                    crate::session_v4::index_worker::on_module_failed(shared, &module);
                }
            }
            None => break, // Shutdown or all work done.
        }
    }
    // Observability: publish this worker thread's scheduler-trace ring
    // buffer so main-thread `flush_to_stderr` can merge-sort worker
    // events into the dump (design/int/observability.md §7). No-op when
    // the filter is disabled.
    crate::observability::publish_thread_buffer();
    // GOT trace events (FIXME 0099) — same pattern; worker threads emit
    // `JitWrite` from backend's `compile_to_module` so their thread-local
    // ring buffer must be published before the worker exits.
    crate::got_trace::publish_thread_buffer();
}

// Thread-local "the panic on THIS thread is an expected, caught validator
// panic — suppress the stderr banner" flag (S90 4R Important — replaces the
// former process-global panic-hook swap).
//
// The CF.1 catch-region in `checked_check_forms` runs `check_forms` over
// uncontrolled (model-proposed) source under `catch_unwind`; a typechecker
// panic there is converted to a clean `Err`, so the default unwinder's
// "thread … panicked at …" banner MUST NOT reach the transcript (§16.2 SILENT
// contract). The PRIOR implementation swapped a no-op into the process-global
// `std::panic::set_hook` slot around the catch — but the priority/nice worker
// threads (`priority_worker_loop_shared`, `worker.rs:1483`) run concurrently and
// CAN panic into their own `catch_unwind`; during the swap window they would (a)
// hit the no-op hook instead of the startup CHAINED hook → lost trace flushes,
// and (b) race on the global hook slot. This thread-local replaces that: it is
// set only on the eval thread for the duration of the catch, and the startup
// `io_trace::install_panic_hook` chain (the int-owned hook whose `previous` is
// the default banner-printer) checks it for the current thread. A
// concurrently-panicking WORKER thread sees the flag `false` on its own thread,
// so it flushes AND prints its banner normally — no global state is mutated, no
// race, no lost worker banner/flush.
#[cfg(feature = "agent")]
thread_local! {
    pub(crate) static SUPPRESS_PANIC_BANNER: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// RAII guard: sets [`SUPPRESS_PANIC_BANNER`] true for the current thread for
/// the lifetime of the guard, restoring the prior value on drop (so the scope
/// is exception-safe — the flag clears even if the guarded body unwinds past
/// the guard, which it does not here because the panic is caught inside).
#[cfg(feature = "agent")]
struct SuppressPanicBannerGuard {
    previous: bool,
}

#[cfg(feature = "agent")]
impl SuppressPanicBannerGuard {
    fn new() -> Self {
        let previous = SUPPRESS_PANIC_BANNER.with(|c| c.replace(true));
        Self { previous }
    }
}

#[cfg(feature = "agent")]
impl Drop for SuppressPanicBannerGuard {
    fn drop(&mut self) {
        let previous = self.previous;
        SUPPRESS_PANIC_BANNER.with(|c| c.set(previous));
    }
}

/// `catch_unwind`-floored `check_forms` — the §11.3(b) / §24 (CF.1)
/// agent-robustness floor (`design/int/agent.md §24.2`). Both
/// [`validate_forms_dry_run`] (the eval-thread S89 Build validator, today) and the
/// future Pillar-3 importable-symbol indexer (§25, next sprint) call THIS instead
/// of `check_forms` directly, so there is ONE catch site, not two divergent ones.
///
/// A typechecker panic (`debug_assert!`/`unreachable!`/`panic!`) over uncontrolled
/// (model-proposed or arbitrary-library) source would otherwise unwind the calling
/// thread. This wraps the `check_forms` call in
/// `catch_unwind(AssertUnwindSafe(..))` — **exactly** the pool-worker shape at
/// [`priority_worker_loop_shared`] (`worker.rs:1483`), reusing [`panic_message`]
/// — and converts a caught unwind into a clean `Err(CheckError::TypeError)`. The
/// callers fold any `Err` into their own graceful path (the validator's
/// silent-repair re-prompt; the indexer's "could not index" note), so a panicking
/// typecheck NEVER crashes the process.
///
/// **Test-only panic-injection seam (§24.3).** When the env lever
/// `CRANELISP_AGENT_FORCE_VALIDATOR_PANIC` is set, this forces a `panic!` in place
/// of the real `check_forms` call — so CF.1 (`tests/agent.rs`) durably exercises
/// the catch independent of whether any specific form (0432 or otherwise)
/// currently panics. The seam is `#[cfg(any(test, feature = "agent"))]`-gated and
/// env-driven (it must cross the e2e subprocess boundary); env-unset ⇒ normal
/// validation. It is INERT in a production / feature-off build.
#[cfg(feature = "agent")]
fn checked_check_forms(
    parsed: Vec<cranelisp_types::ParsedEntry>,
    ctx: &mut cranelisp_typecheck::SymbolTableAccess<'_, crate::code::Code, ()>,
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
) -> Result<cranelisp_typecheck::CheckResult, cranelisp_typecheck::CheckError> {
    use std::panic::AssertUnwindSafe;
    // §16.2 SILENT contract: a caught validator panic is converted to a clean
    // `Err`, so the default panic hook's stderr banner ("thread … panicked at …",
    // the backtrace note) MUST NOT reach the transcript — the user sees a graceful
    // validation outcome, never an internal-crash banner. We set a THREAD-LOCAL
    // suppression flag for the duration of the catch (RAII guard) and the startup
    // `io_trace::install_panic_hook` chain honours it for THIS thread, skipping the
    // banner while still flushing all traces. This replaces the former
    // process-global `set_hook`/`take_hook` swap, which raced with the concurrently
    // panic-capable priority/nice worker threads (`worker.rs:1483`) — they would
    // hit the no-op hook (losing their trace flushes) during the swap window (S90
    // 4R Important). The flag is thread-local, so a concurrent worker panic prints
    // and flushes normally; only this eval-thread's expected panic is silenced.
    let _suppress_guard = SuppressPanicBannerGuard::new();
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        // §24.3 test-only injection seam — forces the catch to fire so CF.1 is
        // not a vacuous-after-root-fix guard. OFF (env unset) ⇒ real validation;
        // gated out of production entirely.
        #[cfg(any(test, feature = "agent"))]
        if std::env::var_os("CRANELISP_AGENT_FORCE_VALIDATOR_PANIC").is_some() {
            panic!(
                "CRANELISP_AGENT_FORCE_VALIDATOR_PANIC — forced eval-thread \
                 validator panic (test-only injection seam, §24.3)"
            );
        }
        cranelisp_typecheck::check_forms(
            parsed,
            ctx,
            symbol_tables,
            module_aliases,
            prelude_fallback,
        )
    }));
    // The thread-local suppression flag is cleared by `_suppress_guard`'s Drop
    // (no global hook to restore — the chain is untouched).
    match result {
        // The inner `check_forms` ran to completion — propagate its own result.
        Ok(r) => r,
        // A panic unwound out of `check_forms` (or the injection seam). Mirror the
        // pool-worker conversion: a clean `CheckError::TypeError` carrying the
        // panic payload. The caller's discard arm folds this into its graceful
        // path; the thread (and REPL) survives.
        Err(panic) => {
            let msg = panic_message(&panic);
            Err(cranelisp_typecheck::CheckError::TypeError {
                message: format!(
                    "module/form failed to typecheck (compiler internal error): {msg}"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })
        }
    }
}

/// Extract a human-readable message from a caught panic payload (FIXME 0285
/// defect 2). `catch_unwind` yields `Box<dyn Any>`; the common payloads are
/// `&str` (from `panic!("…")`) and `String` (from formatted panics).
fn panic_message(panic: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = panic.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = panic.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic (non-string payload)".to_string()
    }
}

/// Handle a Typecheck work item on a persistent priority worker (S78
/// in-call-stack restructure).
///
/// The cluster sexps arrive ON the work packet (`sexps`), not from a shared
/// `module_sexps` map. Drives the single live orchestration
/// (`cluster::process_cluster`) and:
///
/// - on `Done` — runs `inline_jit_codegen_for_module`, commits the
///   cluster-level metadata via `cluster::insert_cluster`, and calls
///   `notify_typecheck_done`;
/// - on `Gap` — does NOTHING further. The dependency has already been
///   registered + blocked on inside `process_cluster`; this worker returns and
///   frees back to the pool. When `dep` completes,
///   `notify_typecheck_done(dep)` → `try_unblock_locked(module)` requeues this
///   module (its sexps persist on its `ModuleState`), and a worker re-runs the
///   cluster from the top against now-larger live state. No saved suspend
///   state, no parking map.
fn handle_typecheck_work_shared(
    shared: &crate::session_v4::SharedState,
    module: &ModuleFullPath,
    sexps: &std::sync::Arc<[Sexp]>,
    instantiation_demands: std::sync::Arc<[MonoDemand]>,
    generation_started: bool,
) -> Result<(), CranelispError> {
    match crate::cluster::process_cluster(
        shared,
        std::sync::Arc::clone(sexps),
        instantiation_demands,
        module,
        generation_started,
    )? {
        crate::cluster::ClusterOutcome::Done {
            mut processed,
            program: _,
        } => {
            // Unified JIT codegen via compile_to_module (Sprint 56 Wave 2).
            // D1b: the introspection store is REPL-only (`None` in batch).
            // `.as_ref()` threads its existence straight to the step-7 sink
            // guard (`inline_jit_codegen_for_names`); in batch the sink is
            // `None`, so no `Introspection` record is allocated and no CLIF is
            // retained — this is the core batch-leak fix.
            compile_and_publish_processed_without_notify(&mut processed, shared)?;

            // Sprint 58 Step 5b: nice workers walk
            // `symbol_tables[module].defined_symbols()` directly. The
            // `program` is consumed only by the inline JIT codegen above.
            // A dependency may invoke an imported helper immediately after the
            // TypecheckDone transition. The shared helper makes the required
            // post-publish InMemDone → TypecheckDone order one cadence.
            notify_processed_ready(&mut processed, shared, module);

            // Commit the cluster-level REPL/scheduler metadata. (Per-symbol
            // staging entries already published by the prepared turn.)
            crate::cluster::insert_cluster(shared, processed, module)?;

            // E3 publication-edge hook (`resolve-home-enumeration.md` §4): the
            // terminal typecheck transition is the signature-publication edge, so
            // a module that reaches terminal AFTER the importable index was armed
            // (late `/import`, watcher reload, or an in-flight-at-arm dep) feeds
            // its live-table public symbols into the `/search` index now. No-op
            // when the index is not armed (batch modes / pre-arm startup).
            crate::session_v4::index_worker::on_module_published(shared, module);
        }
        crate::cluster::ClusterOutcome::Gap {
            dep,
            continuation,
            generation_started,
        } => {
            // The dependency was registered + blocked on inside the cluster
            // pass; this worker frees back to the pool. The scheduler requeues
            // `module` (sexps persist on its ModuleState) when `dep` completes.
            shared.scheduler.set_source_continuation(
                module,
                std::sync::Arc::from(continuation),
                generation_started,
            );
            let _ = dep;
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Unit tests — priority-worker codegen path (Sprint 56 Wave 2)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
