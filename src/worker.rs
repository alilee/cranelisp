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

use cranelisp_types::{ErrorLocation,
    CranelispError, DefKind, Defn, ModuleEntry, ModuleFullPath,
    Sexp, Span, Symbol, TopLevel,
};

use cranelisp_typecheck::CheckState;

// Internal per-int compatibility shim for the (post-Decision-44, 2026-05-13
// third amendment) collapsed `check_forms` surface. The legacy multi-call
// shape (`check_form` + `merge_form_result` + `finalize_check_result` +
// `ModuleCheckAccumulator`) has been retired from typecheck's public API; the
// `accumulator` parameter that pre-S66 worker code threaded through 20+
// call sites is no longer required at the facade. The shim type below is a
// vestigial empty placeholder so the existing worker call signatures compile
// while we route the actual typecheck dispatch through `check_forms` (one
// call per cluster of `Vec<ParsedEntry>`). This is the migration scaffold
// described in `design/arch/facades/int.md` §"process_cluster" and the
// `2026-05-13 third amendment` block in Decision 44.
#[derive(Default)]
pub struct ModuleCheckAccumulator {
    /// Default-method defns deferred from trait-impl registration to the
    /// next pass. Kept for source compatibility with pre-S66 worker code;
    /// `check_forms` handles this internally and the worker side no longer
    /// drives it.
    pub default_method_defns: Vec<Defn>,
}

impl ModuleCheckAccumulator {
    pub fn new() -> Self {
        Self::default()
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
pub(crate) fn build_program_compat(
    sexps: &[Sexp],
) -> Result<Vec<TopLevel>, CranelispError> {
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

/// Number of sexps a leading `:Type` annotation occupies at the head of
/// `sexps`, or `0` if `sexps[0]` is not an annotation.
///
/// Mirrors the frontend's `try_consume_annotation` shape (the single source of
/// truth for what a `:Type` token is — BC §1 invariant 9) so the orchestrator
/// can GROUP an annotation with its bound form into one cluster/Pass-2 unit
/// WITHOUT itself performing the `Expr::Annotate` pairing (which stays
/// frontend-owned, done inside `build_forms`):
/// - `:Int`, `:a`, `:Num` — colon-prefixed symbol → 1 sexp.
/// - a bare `:` followed by a compound type sexp (`(Fn [a] a)`) → 2 sexps.
///
/// This is recognition-for-grouping only; the authoritative pairing +
/// validation (including the trailing-annotation parse error) happens in
/// `cranelisp_frontend::build_forms`. int only decides which span of sexps is
/// fed to the frontend as one form (BC §1 invariant 9; FIXME 0329).
pub(crate) fn leading_annotation_len(sexps: &[Sexp]) -> usize {
    match sexps.first() {
        // `:Int`, `:a`, `:Num` — colon-prefixed symbol (one sexp).
        Some(Sexp::Symbol(s, _)) if s.starts_with(':') && s.len() > 1 => 1,
        // bare `:` then a compound type sexp (`(Fn [...] ret)` etc).
        Some(Sexp::Symbol(s, _)) if s == ":" && sexps.len() >= 2 => 2,
        _ => 0,
    }
}

/// Convert `Vec<TopLevel>` back into `Vec<ParsedEntry>` for handoff to
/// `cranelisp_typecheck::check_forms`. The worker pipeline still operates in
/// `TopLevel` shapes downstream of build_form for codegen + display info; we
/// transcode again here at the typecheck-dispatch boundary.
pub(crate) fn top_level_to_parsed_entries(program: &[TopLevel]) -> Vec<cranelisp_types::ParsedEntry> {
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
            TopLevel::TypeDef { name, docstring, type_params, constructors, visibility, span } => {
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
            TopLevel::TraitImpl(impl_) => out.push(ParsedEntry::TraitImpl { impl_: impl_.clone() }),
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
        (None, _warnings, _redefs) => Ok(()),
        (Some(gap), _warnings, _redefs) => Err(CranelispError::TypeError {
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
        Vec<crate::redefine::RedefinitionOutcome>,
    ),
    CranelispError,
> {
    use cranelisp_typecheck::{check_forms, CheckError, SymbolTableAccess};

    let parsed = top_level_to_parsed_entries(working_program);
    if parsed.is_empty() {
        return Ok((None, Vec::new(), Vec::new()));
    }

    let mut staging: crate::code::SessionSymbolTable =
        cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(
            module.clone(),
        );
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
        Ok(warnings) => {
            let redefs = commit_staging_to_live(symbol_tables, module, staging, shared)?;
            Ok((None, warnings, redefs))
        }
        // A recoverable resolution gap (e.g. an FQ reference to a module not
        // yet loaded). Staging drops here (atomic discard, live unchanged);
        // the gap is handed back to `finalize_module` for FQ-auto-load
        // orchestration (FIXME 0268). On retry a fresh staging frame runs.
        // No warnings on the gap path — the cluster re-runs from the top.
        Err(CheckError::Gap(gap)) => Ok((Some(gap), Vec::new(), Vec::new())),
        // A genuine type error — staging drops, live unchanged.
        Err(e) => Err(check_error_to_cranelisp_error(e)),
    }
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
        Ok(_warnings) => Ok(()),
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
    use crate::redefine::{
        allocate_live_got_slot, classify_redefinition, RedefKind, RedefinitionOutcome,
        RetainedCode,
    };
    use cranelisp_types::{FQSymbol, ModuleEntry};

    // Drain staging into a Vec before acquiring the live write guard to
    // avoid simultaneous borrow paths on `staging`. `staging` is owned
    // here; we move its `symbols` field out by destructuring.
    let mut drained: Vec<(Symbol, ModuleEntry<crate::code::Code>)> =
        staging.symbols.into_iter().collect();

    // FIXME 0348 — DETERMINISTIC commit order, keyed on the STAGED got_slot.
    // `staging.symbols` is a `HashMap`; `into_iter()` yields entries in
    // hash-bucket order, which is non-deterministic across runs (randomised
    // seed). The drain
    // loop below re-allocates a fresh LIVE slot per `Def` *in iteration order*,
    // so a non-deterministic drain produced a non-deterministic staging→live
    // slot PERMUTATION (run-to-run: `a→0,b→1` one run, `a→1,b→0` the next). The
    // body codegen bakes intra-module calls against `resolve_got_target` (which
    // reads the live got_slot) and the GOT data is stored against the same live
    // got_slot — but a forward reference compiled in one pass against a slot map
    // that the OTHER pass reordered makes `main`'s baked call land on the wrong
    // function (returns the initial accumulator / 0 instead of the fold result).
    // Draining in staged-slot order makes the live allocation order — and hence
    // the staging→live slot mapping — STABLE and identity-preserving when live
    // starts empty (the fresh-build case). Entries with no staged slot
    // (non-`Def`) sort last, by name, so the whole commit is deterministic.
    drained.sort_by(|(a_name, a_entry), (b_name, b_entry)| {
        // The staged slot now rides on the callable `DefKind` variant (S83
        // reshape, FIXME 0356/0357) — read it through the single
        // `callable_got_slot()` chokepoint rather than the retired flat field.
        let slot_of = |e: &ModuleEntry<crate::code::Code>| e.callable_got_slot();
        match (slot_of(a_entry), slot_of(b_entry)) {
            (Some(sa), Some(sb)) => sa.cmp(&sb),
            (Some(_), None) => std::cmp::Ordering::Less,
            (None, Some(_)) => std::cmp::Ordering::Greater,
            (None, None) => a_name.as_ref().cmp(b_name.as_ref()),
        }
    });

    let Some(mut live) = symbol_tables.get_mut(module) else {
        // Live module disappeared between dispatch and commit — drop staging
        // silently. This shouldn't happen under normal Wave-3a-α
        // registration discipline (live exists for the current module
        // before `process_cluster` runs), but a no-op is safer than a
        // panic at commit.
        return Ok(Vec::new());
    };

    // §8.6.4 definition-over-(import|export|prelude) rejection now lives at the
    // shared typecheck seam (`check_forms` Pass-1, FIXME 0514) — the single
    // mode-uniform chokepoint both REPL/Additive and batch/Replace traverse,
    // and the only place that also sees the prelude OUTER scope. By the time a
    // cluster reaches this commit gate it has already passed `check_forms`
    // cleanly, so a colliding def never arrives here. The former Additive-gated
    // int-side pre-scan (retired e1fe4a8) is gone.

    let mut outcomes: Vec<RedefinitionOutcome> = Vec::new();

    for (name, mut entry) in drained.drain(..) {
        // The staged slot (read via the `callable_got_slot()` chokepoint —
        // the slot rides on the callable `DefKind` variant per the S83
        // reshape, FIXME 0356/0357) is meaningless in live's GOT (staging
        // holds a fresh GOT Arc). Re-point every callable `Def` to a live
        // slot before commit, applying the S101 slot policy.
        //
        // Redefinition slot authority (supersedes the pre-S101 "we must NOT
        // introduce a second allocation policy" invariant): typecheck's
        // Pass-1 `redef_slots` pin remains the fast-path identity — for an
        // `AbiPreserving` redefinition the staged slot already equals the
        // reused live slot — but THIS gate is the documented single
        // authority that overrides it on `AbiChanging`, allocating a fresh
        // live slot and freezing the old one (its code retained in the
        // session pool so stale closures and in-flight frames keep a
        // coherent old-ABI chain — design §4.3, no quiesce needed).
        //
        // `AbiPreserving` also CARRIES OVER the prior `code` field — codegen's
        // redefinition detection compares prior `code` against None to decide
        // whether to emit a `Redefinition` trace event, and Decision 31
        // Scenario 2's per-redefinition reclaim happens when codegen replaces
        // it. `AbiChanging` deliberately does NOT carry code: the fresh slot
        // is a new world, and the prior code's lifetime belongs to the pool.
        if entry.callable_got_slot().is_some() {
            let (prior_slot, prior_code, kind, per_symbol, prior_was_def) =
                match live.symbols.get(&name) {
                    Some(prior @ ModuleEntry::Def { code, .. }) => {
                        let (kind, per_symbol) =
                            classify_redefinition(name.as_ref(), Some(prior), &entry);
                        (prior.callable_got_slot(), code.clone(), kind, per_symbol, true)
                    }
                    prior => {
                        let (kind, per_symbol) =
                            classify_redefinition(name.as_ref(), prior, &entry);
                        (None, None, kind, per_symbol, false)
                    }
                };

            // Fresh-slot is unconditional on ABI change, independent of the
            // recorded caller set (invisible value captures exist — design
            // §7.1) — but freezing requires the retention pool: without it
            // the displaced `Code`'s pages would be freed while the frozen
            // slot still points at them, so a pool-less context degrades to
            // reuse-and-patch.
            let effective_kind = match kind {
                RedefKind::AbiChanging if shared.is_none() => RedefKind::AbiPreserving,
                k => k,
            };

            let new_slot = match effective_kind {
                RedefKind::New => match prior_slot {
                    // Defensive: a `New`-classified commit with a prior slot
                    // cannot arise (classification requires no prior Def
                    // slot), but reuse would be the safe answer.
                    Some(slot) => slot,
                    None => allocate_live_got_slot(&mut live, module)?,
                },
                RedefKind::AbiPreserving => match prior_slot {
                    Some(slot) => slot,
                    None => allocate_live_got_slot(&mut live, module)?,
                },
                RedefKind::AbiChanging => {
                    // Freeze: push the superseded `Code` into the retention
                    // pool BEFORE `live.insert` replaces the entry (the pool
                    // clone keeps the pages mapped; the old slot is never
                    // written again — Principle 20: after this commit no live
                    // entry carries the old index, so the illegal write is
                    // unreachable by representation).
                    let shared = shared.expect("AbiChanging requires a session (gated above)");
                    let old_slot = prior_slot.expect("AbiChanging requires a prior slot");
                    if let Some(code) = prior_code.clone() {
                        shared
                            .retained_code
                            .lock()
                            .unwrap_or_else(|e| e.into_inner())
                            .push(RetainedCode::frozen(module, &name, Some(old_slot), code));
                    }
                    let fresh = allocate_live_got_slot(&mut live, module)?;
                    crate::got_trace::emit_slot_freeze(module, &name, old_slot, fresh);
                    fresh
                }
            };

            if let ModuleEntry::Def { kind: def_kind, code, .. } = &mut entry {
                repoint_callable_slot(def_kind, new_slot);
                // Preserve the prior code handle on the reuse path if staging
                // didn't already write one (staging-side typecheck does not
                // run codegen, so `code` is normally `None` for staged Def
                // entries). `AbiChanging` starts its fresh slot code-less.
                if code.is_none() && effective_kind != RedefKind::AbiChanging {
                    *code = prior_code;
                }
            }

            outcomes.push(RedefinitionOutcome {
                fq: FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                },
                kind: effective_kind,
                per_symbol,
                prior_was_def,
                old_slot: prior_slot,
                new_slot: Some(new_slot),
            });
        } else if matches!(entry, ModuleEntry::Def { .. })
            && let Some(prior) = live.symbols.get(&name)
            && matches!(prior, ModuleEntry::Def { .. })
        {
            // The SLOT-LESS-staged redefinition arms — both T1 shapes
            // (S102 §9.1.1 gate widening: the gate emits an outcome for
            // EVERY staged `Def` whose name had a prior live `Def`, any slot
            // shape — outcomes are the only channel the driver sees, so a T1
            // shape that produces no outcome is invisible to the §18.1.1
            // downgrade print):
            //
            // (a) FIXME 0479 — a slotted prior with compiled code displaced
            //     by a slot-less staged Def (a concrete fn redefined as a
            //     polymorphic/constrained template or an `Overloaded` base).
            //     The `live.insert` below drops the prior entry — possibly
            //     the last `Code` Arc, freeing mapped JIT pages — while
            //     compiled callers still embed the prior's GOT slot: a
            //     use-after-free SIGSEGV on the next call. Retain the prior
            //     `Code` (frozen supersession, design §6.3) so the
            //     still-populated slot keeps dispatching the frozen old
            //     chain — memory-safe coherent-stale execution (the §4.3
            //     frozen-world argument). Pool-less contexts (`shared: None`
            //     — unit tests, dry-run shapes) keep the pre-S101 drop, as
            //     at the sibling displacement sites.
            //
            // (b) template-replacing-template (slot-less over slot-less
            //     prior `Def`) — nothing to retain, but the outcome still
            //     carries `prior_was_def` so the downgrade is not silent.
            //
            // The *semantic* cure for these T1-kind targets (module-grain
            // reload with end-of-turn sequencing; design §10 T1) is S103;
            // the outcome feeds the interim §18.1.1 `stale:` print.
            let (kind, per_symbol) = classify_redefinition(name.as_ref(), Some(prior), &entry);
            let prior_slot = prior.callable_got_slot();
            if let Some(shared) = shared
                && let Some(prior_slot) = prior_slot
                && let ModuleEntry::Def { code: Some(prior_code), .. } = prior
            {
                shared
                    .retained_code
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(RetainedCode::frozen(
                        module,
                        &name,
                        Some(prior_slot),
                        prior_code.clone(),
                    ));
            }
            outcomes.push(RedefinitionOutcome {
                fq: FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                },
                kind,
                per_symbol,
                prior_was_def: true,
                old_slot: prior_slot,
                new_slot: None,
            });
        }
        live.insert(name, entry);
    }

    Ok(outcomes)
}

/// Re-point the GOT slot carried on a callable [`DefKind`] variant
/// (`UserFn { fn_state: Concrete }`, `Primitive`, `Constructor`,
/// `PlatformEffect`) to `slot`, in place. The mutating peer of the read-only
/// [`ModuleEntry::callable_got_slot`] chokepoint — used by the staging→live
/// commit to re-point a staged slot (valid only in staging's fresh GOT) to a
/// live slot. Non-callable kinds carry no slot and are left untouched
/// (callers gate this on `callable_got_slot().is_some()`, S83 FIXME 0356/0357).
fn repoint_callable_slot(kind: &mut cranelisp_types::DefKind, slot: usize) {
    use cranelisp_types::{DefKind, PrimitiveBody, UserFnState};
    match kind {
        DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot, .. } } => *got_slot = slot,
        // Only the Extern arm carries a slot; an Inline primitive is
        // slot-less by construction (S102 FIXME 0476) and falls to `_`.
        DefKind::Primitive { body: PrimitiveBody::Extern { got_slot, .. }, .. } => {
            *got_slot = slot
        }
        DefKind::Constructor { got_slot, .. } => *got_slot = slot,
        DefKind::PlatformEffect { got_slot, .. } => *got_slot = slot,
        // Non-callable kinds carry no slot — nothing to re-point.
        _ => {}
    }
}

/// Translate `CheckError` to the legacy `CranelispError` shape used by
/// the worker's error sites.
fn check_error_to_cranelisp_error(err: cranelisp_typecheck::CheckError) -> CranelispError {
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
    pub typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    /// Per-symbol introspection data (REPL slash commands). None in batch mode.
    pub introspection: Option<&'a dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    pub lib_dirs: &'a [PathBuf],
    pub platform_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
    /// Optional reference to v4 shared state for cache-hit loading and
    /// codegen input stashing for nice workers.
    /// None for REPL contexts where caching is not used.
    pub shared_state: Option<&'a crate::session_v4::SharedState>,
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

/// Derive the codegen batch — a `Vec<Symbol>` — from a `program` and the
/// module's symbol table. Separated out from `inline_jit_codegen_for_module`
/// so unit tests can exercise the name-derivation logic without standing up
/// a full JIT pipeline. See the sprint's testing ownership clause.
///
/// The batch includes:
/// - each `TopLevel::Defn`'s `name` (when the symbol-table entry has
///   `ast: Some(_)` and is not a constrained template, a `Polymorphic`
///   generic template (S84 Phase 4B, FIXME 0381 — its concrete mono
///   instances carry the bodies that codegen), or an `Overloaded` base);
/// - every mangled multi-sig variant whose base name appears in `program`;
/// - `__expr` when `program` contains a `TopLevel::Expr`;
/// - each trait-impl method's mangled name;
/// - any symbol-table entry with `$` in its name (mono specialisation or
///   other mangling) that is not already compiled (`code: Some(_)` on the
///   entry).
#[doc(hidden)]
pub fn derive_codegen_batch(
    module: &ModuleFullPath,
    program: &[TopLevel],
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
) -> Vec<Symbol> {
    let mut names: Vec<Symbol> = Vec::new();
    let mut seen: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    let table_ref = tc_modules.get(module);

    let try_push = |name: &Symbol,
                        names: &mut Vec<Symbol>,
                        seen: &mut std::collections::HashSet<Symbol>|
     -> bool {
        if seen.contains(name) {
            return false;
        }
        let Some(ref table) = table_ref else {
            return false;
        };
        let Some(entry) = table.get(name.as_ref()) else {
            return false;
        };
        if let ModuleEntry::Def { kind, ast: Some(_), .. } = entry
            && !matches!(
                kind.as_ref(),
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Constrained(_) }
                    | DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Polymorphic(_) }
                    | DefKind::Overloaded { .. }
            )
        {
            names.push(name.clone());
            seen.insert(name.clone());
            return true;
        }
        false
    };

    for tl in program {
        match tl {
            TopLevel::Defn(defn) => {
                try_push(&defn.name, &mut names, &mut seen);

                if defn.is_multi_sig()
                    && let Some(ref table) = table_ref
                {
                    let mangled: Vec<Symbol> = table
                        .defined_symbols()
                        .filter_map(|(sym, _)| {
                            sym.as_ref().split_once('$').and_then(|(base, _)| {
                                if base == defn.name.as_ref() {
                                    Some(sym.clone())
                                } else {
                                    None
                                }
                            })
                        })
                        .collect();
                    for m in &mangled {
                        try_push(m, &mut names, &mut seen);
                    }
                }
            }
            TopLevel::Expr(_) => {
                try_push(&Symbol::from("__expr"), &mut names, &mut seen);
            }
            TopLevel::TraitImpl(impl_) => {
                for method in &impl_.methods {
                    try_push(&method.name, &mut names, &mut seen);
                }
            }
            _ => {}
        }
    }

    if let Some(ref table) = table_ref {
        let candidates: Vec<Symbol> = table
            .defined_symbols()
            .filter(|(sym, _)| !seen.contains(*sym))
            .map(|(sym, _)| sym.clone())
            .collect();
        for name in &candidates {
            // Sprint 57 Wave 2 G6: check `ModuleEntry::Def.code` instead of
            // the deleted `codegen_products` DashMap.
            let already_compiled = table
                .get(name.as_ref())
                .and_then(|e| match e {
                    ModuleEntry::Def { code, .. } => Some(code.is_some()),
                    _ => None,
                })
                .unwrap_or(false);
            if already_compiled {
                continue;
            }
            // S76 W-Enablement (0249-b): enumerate synthesised constructor
            // `Def`s into the codegen batch so their `Expr::ConstrADT` bodies
            // are lowered and their GOT slots (allocated by typecheck's
            // 0249-a `register_constructors`) are populated — making
            // `(map Some xs)` (constructor-as-value) reach the constructor via
            // its GOT slot. Mirror of the Decision 0048 primitives got-slotting.
            //
            // S76 W4b (FIXME 0285): the same uncovered-sibling treatment for
            // bootstrap-synthesised NON-constructor Defs carrying `ast: Some`
            // (the Trace field-accessor family — `nanos`/`name`/…). They are
            // function bodies (synthesised `match` extractions) that MUST be
            // lowered into the GOT for an accessor call to resolve GOT-indirect.
            // (Inline `DefKind::Primitive` entries with `ast: None`, e.g.
            // `bind`/`sconcat`, are excluded — they resolve from the intrinsics
            // archive and carry no body to compile.)
            //
            // S83 W2 (FIXME 0363): the spec §5.2.6 product field accessors that
            // typecheck synthesises in `register_constructors` are concrete
            // `DefKind::UserFn { fn_state: Concrete { got_slot } }` entries with
            // a single-arm `match` body (`ast: Some(_)`) born in the symbol
            // table WITHOUT a `TopLevel::Defn` in `program`. A normal user
            // `UserFn::Concrete` defn is already batched via the `program` loop
            // above (it enters `seen` at its `TopLevel::Defn`), so this sibling
            // arm only catches the body-carrying synthetic accessors — it does
            // NOT double-compile normal defns (they are skipped by the `seen`
            // guard at the top of this loop). Without this arm the accessor's
            // body is never lowered and its GOT slot stays empty, so `(v (Box
            // 5))` resolves the name but loads an empty slot → no value.
            let is_uncompiled_synth_def = table
                .get(name.as_ref())
                .map(|e| matches!(
                    &e,
                    ModuleEntry::Def { kind, ast: Some(_), .. }
                        if matches!(
                            kind.as_ref(),
                            DefKind::Constructor { .. }
                                | DefKind::Primitive { .. }
                                | DefKind::UserFn {
                                    fn_state: cranelisp_types::UserFnState::Concrete { .. }
                                }
                        )
                ))
                .unwrap_or(false);
            if name.as_ref().contains('$') || name.as_ref() == "__expr" || is_uncompiled_synth_def {
                try_push(name, &mut names, &mut seen);
            }
        }
    }

    drop(table_ref);
    names
}

/// Compile the defined symbols of a module through the unified
/// `compile_to_module` entry point.
///
/// Sprint 56 Wave 2 replacement for `codegen_module_symbols`. Per
/// `design/int/phase2-codegen-convergence.md` §5 and `pipeline-v4.md` §9.3,
/// the worker:
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
/// `extra_jit_symbols` carries additional JIT symbol registrations needed by
/// the REPL eval path (trace-runtime overrides, test-runner externs). Regular
/// worker invocations pass an empty slice.
///
/// The JIT is wrapped in `Arc<Jit>` so a single compile call producing N
/// functions can store N `Code` entries sharing one JIT (see
/// `src/session_v4.rs` `Code` doc — /arch Phase 3a §3).
#[allow(clippy::too_many_arguments)]
pub fn inline_jit_codegen_for_module(
    scheduler: &CompileScheduler,
    module: &ModuleFullPath,
    program: &[TopLevel],
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    introspection: Option<&dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    extra_jit_symbols: &[(String, *const u8)],
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<(), CranelispError> {
    // 1. Derive compilation batch from `program` and the module's symbol
    //    table — see `derive_codegen_batch` for the filter details.
    let names = derive_codegen_batch(module, program, tc_modules);

    if names.is_empty() {
        let dummy = Symbol::from("__empty_module");
        scheduler.notify_inmem_codegen_complete(module, &dummy, true);
        return Ok(());
    }

    // Delegate to the names-explicit helper and then notify the scheduler
    // once per compiled name (last-in-batch flag set for the final entry).
    inline_jit_codegen_for_names(
        module,
        &names,
        tc_modules,
        introspection,
        extra_jit_symbols,
        shared_state,
    )?;

    let total = names.len();
    for (i, name) in names.iter().enumerate() {
        let is_last = i + 1 == total;
        scheduler.notify_inmem_codegen_complete(module, name, is_last);
    }

    Ok(())
}

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
#[allow(clippy::too_many_arguments)]
pub fn inline_jit_codegen_for_names(
    module: &ModuleFullPath,
    names: &[Symbol],
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    introspection: Option<&dashmap::DashMap<cranelisp_types::FQSymbol, crate::session_v4::Introspection>>,
    extra_jit_symbols: &[(String, *const u8)],
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<(), CranelispError> {
    if names.is_empty() {
        return Ok(());
    }
    // S76 W-Collapse: `extra_jit_symbols` is retained for signature
    // compatibility (REPL eval path no longer threads trace symbols). The
    // unified `Jit::new(symbol_tables)` derives the entire JIT symbol set —
    // intrinsics (incl. trace + the 2 parked test intrinsics are folded in
    // below), per-module GOT data symbols, platform-effect jit-names — so int
    // assembles nothing by hand.
    let _ = (extra_jit_symbols, shared_state);

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
    let module_aliases = module_aliases_for(tc_modules);
    // FIXME 0325: capture the CLIF-IR text only when introspection is live.
    // The presence of the introspection map IS the mode discriminator (REPL /
    // trace → Some; `--run`/`--link` batch → None — pipeline-v4 §1, Decision
    // 38). In batch the rendered CLIF would be dropped unread, so backend skips
    // the `func.display()` allocation entirely.
    let capture_clif = introspection.is_some();
    let result = cranelisp_backend::compile_to_module(
        module.clone(),
        names,
        tc_modules,
        &module_aliases,
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
    for name in names {
        let prior_ptr: Option<*const u8> =
            read_got_addr(tc_modules, module, name);

        let Some(mut st) = tc_modules.get_mut(module) else {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "fresh-build codegen invariant violation: symbol table \
                     for module '{module}' disappeared during codegen while \
                     writing Code::Jit for '{name}'."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };
        let Some(entry) = st.symbols.get_mut(name.as_ref()) else {
            // Not every name in the batch is a Def on this module (e.g. an
            // Import alias); backend handles its own resolution. Skip
            // lifecycle installation for non-local names.
            continue;
        };
        // The callable slot now rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it through the `callable_got_slot()`
        // chokepoint before taking the mutable borrow for `code`.
        let slot = entry.callable_got_slot();
        let cranelisp_types::ModuleEntry::Def { code, .. } = entry else {
            continue;
        };
        *code = Some(crate::code::Code::jit(std::sync::Arc::clone(&jit_arc)));
        if let (Some(prior), Some(slot)) = (prior_ptr, slot) {
            let new_ptr = st.got.load_slot(slot);
            drop(st);
            crate::got_trace::emit_redefinition(module, name, slot, new_ptr, prior);
        }
    }

    // 7. Route batch-level artifacts into introspection (REPL-only). The S75
    //    `CompilationArtifacts` is batch-grained (concatenated clif_ir +
    //    summed code_size); attribute it to each compiled name. Per-symbol
    //    disasm is on-demand via `cranelisp_backend::produce_disasm` (the
    //    `/disasm` handler reads it lazily).
    if let Some(intr_map) = introspection {
        for name in names {
            let fq = cranelisp_types::FQSymbol {
                module: module.clone(),
                symbol: name.clone(),
            };
            let mut entry = intr_map.entry(fq).or_default();
            entry.clif_ir = Some(result.clif_ir.clone());
            entry.code_size = Some(result.code_size);
        }
    }

    Ok(())
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
    entry: &ModuleEntry<crate::code::Code>,
) -> Option<crate::session_v4::SymbolCategory> {
    use crate::session_v4::SymbolCategory;
    Some(match entry {
        ModuleEntry::Def { kind, .. } => match kind.as_ref() {
            DefKind::Macro { .. } => SymbolCategory::Macro,
            DefKind::Constructor { .. } => SymbolCategory::Constructor,
            _ => SymbolCategory::Fn,
        },
        ModuleEntry::TypeDef { .. } => SymbolCategory::Type,
        ModuleEntry::TraitDecl { .. } => SymbolCategory::Trait,
        ModuleEntry::SpecialForm { .. } => SymbolCategory::SpecialForm,
        _ => return None,
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
fn build_session_jit(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
) -> Result<cranelisp_backend::jit::Jit, CranelispError> {
    let jit = cranelisp_backend::jit::Jit::new(tc_modules)?;
    for name in DEV_SESSION_ONLY_EXTERNS {
        debug_assert_eq!(
            *name, "discover-tests",
            "the only dev-session-only extern body wired here is discover-tests; \
             a new entry in DEV_SESSION_ONLY_EXTERNS needs its own define_symbol",
        );
        jit.define_symbol(
            name,
            crate::session_v4::discover_tests_extern as *const u8,
        );
    }
    Ok(jit)
}

/// Read the runtime GOT address for `name` in `module`, following Import
/// chains, or `None` if no slot / address is assigned. Used to capture the
/// prior pointer for redefinition observability.
fn read_got_addr(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> Option<*const u8> {
    let slot = lookup_got_slot(tc_modules, module, name)?;
    let st = tc_modules.get(module)?;
    let ptr = st.got.load_slot(slot);
    if ptr.is_null() { None } else { Some(ptr) }
}

/// Assemble a `ModuleAliases` snapshot for `compile_to_module`. The aliases
/// are session-scoped; the worker reads them from any module's table is not
/// where they live — they are passed through `SharedState`. The codegen path
/// does not consult aliases for in-module name lowering (GOT-indirect calls
/// use the per-module GOT directly), so an empty alias map is the correct
/// argument for the per-symbol JIT batch (cross-module references resolve via
/// `__cranelisp_got_{M}` data symbols, not alias substitution).
fn module_aliases_for(
    _tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
) -> cranelisp_types::ModuleAliases {
    dashmap::DashMap::new()
}

/// Follow Import/Reexport chains to find a symbol's GOT slot.
fn lookup_got_slot(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> Option<usize> {
    fn walk(
        tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        module: &ModuleFullPath,
        name: &str,
        depth: usize,
    ) -> Option<usize> {
        if depth > 10 {
            return None;
        }
        let st = tables.get(module)?;
        let entry = st.get(name)?;
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357); read it through the `callable_got_slot()`
        // chokepoint. A non-callable / slot-less Def yields `None` and falls
        // through to the import-chain walk / `None` terminal below.
        if let Some(slot) = entry.callable_got_slot() {
            return Some(slot);
        }
        match entry {
            ModuleEntry::Import { source, .. } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                walk(tables, &source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }
    walk(tc_modules, module, name.as_ref(), 0)
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
            let ModuleEntry::Def { kind, .. } = entry else {
                continue;
            };
            // Slot-less `PrimitiveExtern` entries are the synthetic externs
            // resolved by ABI name (S83 reshape, FIXME 0360). Ring
            // `DefKind::Primitive` entries carry a GOT slot and are registered
            // by the GOT-pointer walk — skip them here.
            if !matches!(kind.as_ref(), DefKind::PrimitiveExtern) {
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
    let cache_dir = shared_state.cache.cache_dir().ok_or_else(|| CranelispError::ModuleError {
        message: format!("no cache directory for cache-hit loading of '{}'", module),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
    })?;

    // Load metadata from disk.
    let cached = cache::try_load_cached_module(&cache_dir, module)?
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("cache metadata missing for module '{}'", module),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
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
            if let ModuleEntry::Def { kind, .. } = entry
                && let DefKind::PlatformEffect { got_slot, .. } = kind.as_ref()
            {
                let ptr = st.got.load_slot(*got_slot);
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
            if let ModuleEntry::Def { code: Some(_), .. } = entry
                && let Some(slot) = entry.callable_got_slot()
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
    let module_got = shared_state.symbol_tables.get(module)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("no symbol table for cached module '{}'", module),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })?.got.clone();

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
    let mut loaded_symbols = Vec::new();
    for (name, entry) in cached.symbol_table().all_symbols() {
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint;
        // slot-less entries are skipped.
        let Some(slot) = entry.callable_got_slot() else {
            continue;
        };
        let Some(ptr) = fn_addrs.get(name.as_ref()).copied() else {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "cache-hit symbol resolution failed for '{module}/{name}': \
                     `.o` linker did not define expected bare symbol '{name}'. \
                     This indicates a cache inconsistency — the cached `.meta.json` \
                     records a defined function whose code is missing from the `.o`."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };
        module_got.store_slot(slot, ptr);
        loaded_symbols.push(name.clone());
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
        for (name, entry) in live_table.symbols.iter_mut() {
            // `Code::linker` is now lifecycle-owner only (D41/D35 — the GOT
            // slot, populated above, is the single source of the address; no
            // per-entry `ptr`). Install the Arc on every entry the linker
            // materialised (presence in `fn_addrs` is the membership test).
            if let ModuleEntry::Def { code, .. } = entry
                && fn_addrs.contains_key(name.as_ref())
            {
                *code = Some(crate::code::Code::linker(std::sync::Arc::clone(&linker_arc)));
            }
        }
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

    Ok(loaded_symbols)
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
            Some(PriorityWork::Typecheck { module, sexps }) => {
                // FIXME 0285 defect 2 — worker-panic→park robustness. A panic
                // inside the work handler (e.g. an unresolved-symbol panic from
                // the JIT at finalize, or any `unreachable!`) would otherwise
                // unwind this worker thread WITHOUT marking the module Failed —
                // the main thread then parks on the completion condvar forever
                // (no notification ever fires) → a hang, not an error+exit.
                // Catch the unwind, convert it to a module failure, and notify
                // so `wait_inmem_complete_blocking` returns `ModuleFailed`.
                let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    handle_typecheck_work_shared(shared, &module, &sexps)
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
                                location: ErrorLocation::from_span_file(
                                    Span::SYNTHETIC,
                                    None,
                                ),
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
) -> Result<Vec<cranelisp_types::Warning>, cranelisp_typecheck::CheckError> {
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
) -> Result<(), CranelispError> {
    match crate::cluster::process_cluster(shared, std::sync::Arc::clone(sexps), module)? {
        crate::cluster::ClusterOutcome::Done { processed, program } => {
            // Unified JIT codegen via compile_to_module (Sprint 56 Wave 2).
            // D1b: the introspection store is REPL-only (`None` in batch).
            // `.as_ref()` threads its existence straight to the step-7 sink
            // guard (`inline_jit_codegen_for_names`); in batch the sink is
            // `None`, so no `Introspection` record is allocated and no CLIF is
            // retained — this is the core batch-leak fix.
            inline_jit_codegen_for_module(
                &shared.scheduler,
                module,
                &program,
                &shared.symbol_tables,
                shared.introspection.as_ref(),
                &[],
                Some(shared),
            )?;

            // Commit the cluster-level REPL/scheduler metadata. (Per-symbol
            // staging entries already committed to live inside
            // `check_program_compat`; this drains introspection records.)
            crate::cluster::insert_cluster(shared, processed, module);

            // Sprint 58 Step 5b: nice workers walk
            // `symbol_tables[module].defined_symbols()` directly. The
            // `program` is consumed only by the inline JIT codegen above.
            shared.scheduler.notify_typecheck_done(module);

            // E3 publication-edge hook (`resolve-home-enumeration.md` §4): the
            // terminal typecheck transition is the signature-publication edge, so
            // a module that reaches terminal AFTER the importable index was armed
            // (late `/import`, watcher reload, or an in-flight-at-arm dep) feeds
            // its live-table public symbols into the `/search` index now. No-op
            // when the index is not armed (batch modes / pre-arm startup).
            crate::session_v4::index_worker::on_module_published(shared, module);
        }
        crate::cluster::ClusterOutcome::Gap { dep } => {
            // The dependency was registered + blocked on inside the cluster
            // pass; this worker frees back to the pool. The scheduler requeues
            // `module` (sexps persist on its ModuleState) when `dep` completes.
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
