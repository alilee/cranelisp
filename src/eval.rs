// REPL eval — the form-chain wrapper (FIXME 0109 Wave D).
//
// Extracted from `session_v4.rs` per `design/int/int.md` §3.3. Hosts the REPL
// eval entry (`eval`) + the per-cluster trampoline + the eval-thread dep-retry
// loop (`process_form_cluster` / `process_single_form`) + codegen-and-execute
// + the bare-symbol introspection gate. These are `impl CompilerSession`
// methods reaching the (now `pub(crate)`) session fields; they call the shared
// gap-orchestration core `process_form::process_cluster_once` exactly as the
// worker path does. Pure relocation — no behavioural change.

use cranelisp_types::{
    Binding, CallableOrigin, CranelispError, Decl, ErrorLocation, FQSymbol, ModuleFullPath,
    ModuleStrategy, Sexp, Span, Symbol, TopLevel, Type, Warning,
};

use cranelisp_typecheck::{CheckResult, CheckState};

use crate::code::Code;
use crate::repl::SpecialFormTail;
use crate::session_v4::{
    CompilerSession, EvalResult, Introspection, intrinsic_type_from_name, is_comment_only,
    set_test_runner_state,
};
use crate::worker::ModuleCompiler;

/// Record the turn's verbatim source text on the defined symbol's
/// introspection record — for GENUINE definition turns only (Matrix E
/// recording rule; FIXME 0486, `design/int/s102-defect-wave.md` §7.3).
///
/// A bare-symbol lookup (`EvalResult::Candidates`) MUST NOT touch the record:
/// the lookup text (`"solo"`) would clobber the authored `(defn …)` form that
/// `/info`/`/source` serve (introspection-first precedence in
/// `info_definition_source`). For real definition turns the write is
/// load-bearing: it records the authored text that §4.2's source-first
/// regeneration emits — coordinate any change with that seam (same authorship
/// invariant).
///
/// `introspection` is `Some` only under `RunMode::Repl` (D1b ctor gate) —
/// `None` in batch, no second discriminator to drift.
pub(crate) fn record_defining_turn_source(
    introspection: Option<&dashmap::DashMap<FQSymbol, Introspection>>,
    result: &EvalResult,
    src: &str,
) {
    let EvalResult::Definitions { symbols, .. } = result else {
        return;
    };
    if let Some(m) = introspection {
        for symbol in symbols {
            let fq = FQSymbol {
                module: symbol.module.clone(),
                symbol: symbol.symbol.clone(),
            };
            m.entry(fq).or_default().source = Some(src.to_string());
        }
    }
}

/// The implementing type NAME for a trait-impl registration echo
/// (`impl <trait> for <type>`, repl/spec.md §1.1).
///
/// For the settled echo-the-head HKT form `(impl (Functor f) (Functor Option)
/// …)` (spec §7.3.5 Case 2), slot-2 `t.target` is the pairing
/// `Applied(Functor, [Option])` and the RESOLVED implementing type is the
/// constructor ARGUMENT `Option`, NOT the pairing head `Functor`. This mirrors
/// typecheck's Case-3 effective-target extraction (`traits/impl_check.rs` Step
/// 4), which registers the impl under the constructor
/// (`ModuleEntry::TraitImpl.impl_type = home/Option`) — so the echo names the
/// type dispatch actually registered the impl under. Re-deriving from the raw
/// head (`t.target.head_ref()`) printed the pairing head — the S112 W5
/// `impl user/Functor for user/Functor` display defect (Principle 26 — render
/// from settled state, not a re-derivation of the surface syntax).
///
/// The discriminator is `head_con_var.is_some()`, the parser's echo-the-head
/// bit: on a well-typed impl it is `Some` iff the trait is higher-kinded
/// (Case-3 rejects the two mismatched shapes), and this echo runs only after a
/// successful typecheck. The conventional / bare-head form — and any target
/// already rewritten to `Named` — falls through to the plain head.
impl CompilerSession {
    /// Block the REPL-eval thread on the persistent worker pool driving a
    /// dependency (and its transitive deps) to `inmem_done`, then return so the
    /// eval retry loop re-runs the cluster from the top (S78 in-call-stack
    /// restructure).
    ///
    /// The dep has ALREADY been registered with the scheduler (its sexps ride
    /// the dep's work packet) and blocked on (`block_for_typecheck`) inside
    /// `process_cluster_once`. This function does NOT re-register, re-publish,
    /// or republish caller sexps — the cross-thread `module_sexps` map that
    /// those steps fed is deleted, and the caller's cluster state lives on the
    /// eval thread's own stack frame (no worker reads it). Its sole job is the
    /// scoped wait.
    pub(crate) fn register_dep_for_eval(
        &mut self,
        dep_module: &ModuleFullPath,
    ) -> Result<(), CranelispError> {
        // S78 Step 3 (OQ-3): the `eval_in_flight` guard is GONE. The
        // in-call-stack model keeps the caller's cluster state on the eval
        // thread's own stack frame — no worker reads it — so there is no race
        // for the guard to suppress. The H5-replay gate confirms the parity
        // outcome stays deterministic under stress after this deletion.

        // Ensure the dep has a CheckState slot the persistent worker can
        // populate via `ensure_module_exists` — idempotent.
        cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, dep_module);

        // Block on the persistent worker pool driving THIS dep (and every
        // transitive dep it blocks on) to inmem_done. Decision 37 §3.1 — the
        // single synchronisation primitive, scoped to the target dep. We cannot
        // use `wait_inmem_complete_blocking` (whole-world wait) here: the caller
        // (user module) is in TypecheckBlocked state and can only be resumed by
        // the eval thread's retry loop, not by a persistent worker — so a
        // whole-world wait would deadlock on the user module.
        let result = self
            .shared
            .scheduler
            .wait_module_inmem_complete_blocking(dep_module);

        // S93 Invariant SW: the eval thread recorded a `current → dep`
        // cycle-check edge (`register_dep_edge_for_cycle_check`, via `block_dep`)
        // but never moved its entry to `TypecheckBlocked`. The wait is over —
        // clear the forward edge so the terminal entry carries no stale
        // `blocked_on` into the next REPL form (which could otherwise mislead a
        // future reverse-direction cycle check).
        self.shared
            .scheduler
            .clear_dep_edge(&self.current_module_path());

        match result {
            Ok(()) => Ok(()),
            Err(e) => {
                self.reset_failed_modules();
                Err(CranelispError::from(e))
            }
        }
    }

    /// Evaluate source text in the current REPL module.
    ///
    /// Parses source into sexps, processes each form through the v4 worker
    /// path with Additive strategy, and returns the result for display.
    /// On error, the TypeChecker is restored to its pre-input snapshot.
    pub fn eval(&mut self, source: &str) -> Result<Option<EvalResult>, CranelispError> {
        let trimmed = source.trim();
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return Ok(None);
        }

        let sexps = cranelisp_frontend::parse(source)?;
        if sexps.is_empty() {
            return Ok(None);
        }

        let mut last_result: Option<EvalResult> = None;
        let mut all_warnings = Vec::new();

        // A top-level `:Type` annotation binds the FOLLOWING form (BC §1
        // invariant 9; FIXME 0329). int groups the annotation sexp(s) with the
        // form they precede into a single cluster; the frontend's `build_forms`
        // (reached via `process_form_cluster` → `build_program_compat`) performs
        // the actual `Expr::Annotate` pairing. int does NOT pair here — it only
        // decides the cluster boundary. A trailing annotation with no following
        // form falls through as a one-sexp cluster, surfacing the frontend's
        // `annotation missing expression` parse error.
        let mut i = 0;
        while i < sexps.len() {
            let ann_len = crate::worker::leading_annotation_len(&sexps[i..]);
            let cluster_end = if ann_len > 0 && i + ann_len < sexps.len() {
                // annotation sexp(s) + the single form they bind
                i + ann_len + 1
            } else {
                i + 1
            };
            let cluster = &sexps[i..cluster_end];
            // The span used for `/source` capture covers the whole cluster.
            let cluster_span = {
                let start = cluster[0].span().start;
                let end = cluster[cluster.len() - 1].span().end;
                Span::new(start, end)
            };
            i = cluster_end;

            let outcome = if cluster.len() == 1 {
                self.eval_one_form(&cluster[0])
            } else {
                self.process_form_cluster(cluster)
            };
            match outcome {
                Ok(Some(result)) => {
                    // Store source text for /source command — extract from
                    // original input using the cluster's span.
                    {
                        let span = cluster_span;
                        let src = if span.start < span.end && (span.end as usize) <= source.len() {
                            &source[span.start as usize..span.end as usize]
                        } else {
                            source.trim()
                        };
                        // D1b: the store is REPL-only; absent in batch.
                        record_defining_turn_source(
                            self.shared.introspection.as_ref(),
                            &result,
                            src,
                        );
                    }
                    // S102 CS-0489 (repl/spec/15-session-persistence.md §15.2.3 repair direction): a genuine
                    // definition turn removes its symbol from the module's
                    // degraded-load failed set; when the set empties the
                    // module leaves the §14.4 error-blocked state.
                    self.clear_repaired_failed_form(&result);
                    all_warnings.extend(result.warnings().iter().cloned());
                    last_result = Some(result);
                }
                Ok(None) => {}
                Err(e) => {
                    // §17.1 sequential-eval-abandon (no-agent path): a REPL line
                    // that reaches `eval` — a single form, or (with no active
                    // agent) a multi-form line — is evaluated form-by-form and
                    // ABANDONS on the FIRST error, surfacing it as a real
                    // `Error:` result (E7 fix, USER RULING 2026-07-12). Return the
                    // error directly: do NOT continue to later forms, and do NOT
                    // synthesize a fake `Val{0}` carrying the error as a warning
                    // that the trailing `warnings_mut` assignment would clobber
                    // (the swallow that surfaced a silent `:Int 0`).
                    return Err(e);
                }
            }
        }

        if let Some(ref mut r) = last_result {
            *r.warnings_mut() = all_warnings;
        }
        Ok(last_result)
    }

    /// Evaluate a single sexp.
    ///
    /// W-Macro (S76, fire B): the no-op `tc_snapshot`/`tc_restore` carrier is
    /// deleted. The cluster-atomic staging model (Decision 44) is the rollback
    /// mechanism — a failed form discards its staging table, leaving live
    /// byte-identical (the snapshot/restore primitives it replaced were already
    /// no-ops). Errors propagate directly.
    pub(crate) fn eval_one_form(
        &mut self,
        sexp: &Sexp,
    ) -> Result<Option<EvalResult>, CranelispError> {
        // Bare symbol introspection (macros, special forms).
        if let Some(result) = self.check_bare_symbol_introspection(sexp) {
            return Ok(Some(result));
        }
        self.process_single_form(sexp)
    }

    /// Process a single REPL sexp as a one-form cluster (Additive), then
    /// codegen (S78 in-call-stack restructure).
    ///
    /// The eval-path retry-from-top loop: each pass runs the shared
    /// `worker::process_cluster_once` core over `[sexp]` with a fresh
    /// expansion against now-larger live state. On a dependency gap the dep has
    /// already been registered + blocked on inside the core; this thread waits
    /// for the pool to bring it to inmem-done (`register_dep_for_eval`) then
    /// loops. No saved suspend state — the gap does not recur for that dep
    /// because it is now live.
    pub(crate) fn process_single_form(
        &mut self,
        sexp: &Sexp,
    ) -> Result<Option<EvalResult>, CranelispError> {
        self.process_form_cluster(std::slice::from_ref(sexp))
    }

    /// Process a REPL sexp cluster (one or more sexps) as a single Additive
    /// cluster, then codegen. A cluster is normally a single sexp, but a
    /// leading `:Type` annotation sexp groups with the following form sexp so
    /// the frontend's `build_forms` pairing (`Expr::Annotate`) fires — int
    /// orchestrates the cluster boundary; the frontend decides what one form is
    /// (BC §1 invariant 9; FIXME 0329). Definition results are collected from
    /// the typed/emitted forms rather than reconstructed from this entered
    /// cluster's spelling.
    pub(crate) fn process_form_cluster(
        &mut self,
        cluster: &[Sexp],
    ) -> Result<Option<EvalResult>, CranelispError> {
        use crate::process_form;
        use crate::worker::ClusterOnce;

        const MAX_DEP_RETRIES: usize = 100;

        // For an annotation pair the meaningful input form is the final sexp,
        // not the leading `:Type`. It is used only for the display-only
        // polymorphic-value check below; definition identities come from the
        // stack-owned emitted-definition receipt.
        let head_sexp = match cluster.last() {
            Some(s) => s,
            None => return Ok(None),
        };
        let mut pending = cluster.to_vec();
        let mut generation_started = false;
        let mut turn_definitions = crate::session_v4::TurnDefinitions::default();

        for retry in 0..MAX_DEP_RETRIES {
            // 0571 D2: a bare QUALIFIED symbol (`mathx/gcount`) is introspectable
            // only once its module is live — which happens on the FQ-autoload
            // RETRY (`eval_one_form`'s pre-pass ran while the module was still
            // absent ⇒ `None`). Re-check each pass so the bare FQ display takes
            // the introspection path (no codegen) the moment the module loads,
            // instead of compiling a value-position FQ ref to a codegen leak.
            if pending.len() == 1
                && let Some(result) = self.check_bare_symbol_introspection(&pending[0])
            {
                return Ok(Some(result));
            }

            let module = self.current_module_path();
            let single_sexp = pending.clone();

            let result = {
                // Extract REPL check_state for worker use, restore after.
                cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &module);
                let repl_cs = self
                    .repl_check_state
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .take()
                    .unwrap_or_else(|| CheckState::new(module.clone()));
                let lib_dirs_snap = self.lib_dirs();
                let platform_dirs_snap = self.platform_dirs();
                let mut wctx = ModuleCompiler {
                    symbol_tables: &self.shared.symbol_tables,
                    next_type_id: &self.shared.next_type_id,
                    module_aliases: &self.shared.module_aliases,
                    prelude_fallback: &self.shared.prelude_fallback,
                    check_state: repl_cs,
                    current_module: module.clone(),
                    scheduler: &self.shared.scheduler,
                    typecheck_products: &self.shared.typecheck_products,
                    // D1/D1b: introspection is REPL-only. The store is `Some`
                    // only under `RunMode::Repl` (D1b ctor gate), so `.as_ref()`
                    // is the single adaptor — `None` in batch, no second
                    // discriminator to drift.
                    introspection: self.shared.introspection.as_ref(),
                    lib_dirs: &lib_dirs_snap,
                    platform_dirs: &platform_dirs_snap,
                    project_root: &self.shared.project_root,
                    shared_state: Some(&self.shared),
                    reload_demands: std::sync::Arc::from([]),
                    // S93 Invariant SW: the REPL eval thread is the sole
                    // orchestrator of its entry module — a dependency gap must
                    // NOT move the entry to TypecheckBlocked (the eval thread
                    // waits on the dep itself and re-runs from the top).
                    eval_driven: true,
                };

                let res = process_form::process_cluster_once(
                    &mut wctx,
                    &module,
                    &single_sexp,
                    ModuleStrategy::Additive,
                    generation_started,
                    Some(&mut turn_definitions),
                );
                // Restore REPL check_state.
                *self
                    .repl_check_state
                    .lock()
                    .unwrap_or_else(|e| e.into_inner()) = Some(wctx.check_state);
                res?
            };

            match result {
                ClusterOnce::Done {
                    mut processed,
                    program,
                } => {
                    crate::worker::compile_and_publish_processed(&mut processed, &self.shared)?;
                    // S83 W2 (FIXME 0363): carry the cluster's accumulated
                    // typecheck warnings out to the `EvalResult`. They are
                    // committed onto `ProcessedCluster.warnings` by the
                    // cluster driver (e.g. the §5.2.6 accessor/binding
                    // `ShadowedName` collision); previously this site dropped
                    // them with a hardcoded empty `Vec`, so they never reached
                    // `format_eval_result`.
                    let cluster_warnings = processed.warnings().to_vec();
                    // S101: the commit gate's redefinition classifications —
                    // consumed AFTER the target's own codegen succeeds
                    // (design/int/session-transaction.md §13).
                    let redefinitions = processed.redefinitions().to_vec();
                    let definition_symbols = turn_definitions.published_symbols();
                    // If program is empty, the form was handled during expansion
                    // (defmacro, import, platform, mod). Return every definition
                    // actually published by this turn; structural forms remain
                    // silent.
                    if program.is_empty() {
                        // F5a (S103, FIXME 0507 Issue 3): the defmacro exit
                        // returns BEFORE the ordinary `apply_redefinition_outcomes`
                        // call below, so the §10 T1 full-cure driver must be
                        // reachable here too. Macro invocations do not create
                        // stable runtime dependency edges, but ordinary
                        // redefinition outcomes collected alongside an
                        // expansion-only result must still reach the sink.
                        self.apply_redefinition_outcomes(&redefinitions);
                        return if definition_symbols.is_empty() {
                            // import/platform/mod — no visible result.
                            Ok(None)
                        } else {
                            Ok(Some(EvalResult::Definitions {
                                symbols: definition_symbols,
                                warnings: cluster_warnings,
                            }))
                        };
                    }
                    let check = CheckResult {
                        warnings: cluster_warnings,
                        display: None,
                        // 0611 carrier — the eval driver consults these at the
                        // `__expr` eval-result boundary (class (b)) so a bare
                        // `(zed)` dies with the §3.11 ambiguity instead of
                        // leaking the backend `__expr`-has-no-GOT-slot error.
                        unresolved_dispatch: processed.unresolved_dispatch().to_vec(),
                    };
                    // §3.11.2 / REPL §1.5.1: a bare polymorphic value is a
                    // display-only result. Publication correctly leaves its
                    // synthetic `__expr` as a slot-less Template; carry the
                    // authored value form and inferred result type to the
                    // formatter instead of pretending that a runtime word was
                    // produced. Keep this deliberately narrow: calls (including
                    // unresolved return-directed dispatch) and annotations do
                    // not qualify.
                    if check.unresolved_dispatch.is_empty()
                        && let Some(display) = self.display_only_polymorphic_value(
                            &module,
                            head_sexp,
                            check.warnings.clone(),
                        )
                    {
                        self.apply_redefinition_outcomes(&redefinitions);
                        return Ok(Some(display));
                    }
                    let eval_result =
                        self.codegen_and_execute(&module, &program, &definition_symbols, &check)?;
                    // S101 dependent-recompilation transaction: clears broken
                    // records for recovered symbols (§18.6 direction 1) and
                    // runs the affected-set walk for AbiChanging redefinitions,
                    // stashing the §18.3 cascade report for the REPL printer.
                    self.apply_redefinition_outcomes(&redefinitions);
                    return Ok(Some(eval_result));
                }
                ClusterOnce::Gap {
                    dep,
                    continuation,
                    generation_started: started,
                } => {
                    // The dep has already been registered + blocked on inside
                    // `process_cluster_once`; block on the persistent worker
                    // pool driving it to completion, then retry from the top.
                    self.register_dep_for_eval(&dep)?;
                    pending = continuation;
                    generation_started = started;
                    if retry == MAX_DEP_RETRIES - 1 {
                        return Err(CranelispError::ModuleError {
                            message: format!(
                                "dependency chain too deep (>{} retries) while resolving '{}'",
                                MAX_DEP_RETRIES, dep,
                            ),
                            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                        });
                    }
                }
            }
        }

        Err(CranelispError::ModuleError {
            message: "dependency retry limit exhausted".to_string(),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })
    }

    /// Build the non-runtime carrier for the two bare polymorphic value forms
    /// governed by §3.11.2 / REPL §1.5.1. The lifecycle check is authoritative:
    /// a concrete `__expr` must execute normally, while a template has neither
    /// a GOT slot nor a runtime value to own.
    fn display_only_polymorphic_value(
        &self,
        module: &ModuleFullPath,
        form: &Sexp,
        warnings: Vec<Warning>,
    ) -> Option<EvalResult> {
        match form {
            Sexp::Symbol(_, _) => {}
            Sexp::Bracket(items, _) if items.is_empty() => {}
            _ => return None,
        }

        let table = self.shared.symbol_tables.get(module)?;
        let callable = table
            .get(crate::worker::SYNTHETIC_EXPR_WRAPPER)?
            .callable()?;
        if !matches!(callable.arm.life, cranelisp_types::Life::Template { .. }) {
            return None;
        }
        let Type::Fn(params, result) = &callable.arm.scheme.ty else {
            return None;
        };
        if !params.is_empty() || result.is_concrete() {
            return None;
        }

        Some(EvalResult::DisplayValue {
            ty: result.as_ref().clone(),
            form: form.clone(),
            warnings,
        })
    }

    /// Run codegen for definitions, then execute if there is a trailing expression.
    pub(crate) fn codegen_and_execute(
        &mut self,
        module: &ModuleFullPath,
        program: &[TopLevel],
        definition_symbols: &[FQSymbol],
        check: &CheckResult,
    ) -> Result<EvalResult, CranelispError> {
        // Ensure typecheck product exists for this module.
        crate::worker::ensure_typecheck_product(&self.shared.typecheck_products, module);

        // 0611 class-(b) leg (Principle 19): typecheck records the
        // unresolved-return-poly-dispatch signal but never rejects the synthetic
        // `__expr` eval wrapper (which may legitimately hold a poly VALUE for
        // introspection display, §3.11.2). When the REPL must EVALUATE `__expr`
        // to produce a value and its body carries an unresolved return dispatch
        // (`(zed)`, `:Zeroable (zed)`), that is the §3.11 ambiguity — emit it
        // here, BEFORE codegen, instead of leaking `__expr entry has no GOT
        // slot`. Filtered to `__expr`'s own body span (a sibling poly defn in
        // the same program is legitimate and untouched).
        if !check.unresolved_dispatch.is_empty()
            && let Some(eval_body_span) = program.iter().find_map(|t| match t {
                // The evaluated top-level expression — a bare `TopLevel::Expr`
                // OR the synthetic `__expr` wrapper defn (whichever form the
                // upstream peel produced).
                TopLevel::Expr(e) => Some(e.span()),
                TopLevel::Defn(d) if d.name.as_ref() == crate::worker::SYNTHETIC_EXPR_WRAPPER => {
                    d.variants.first().map(|v| v.body.span())
                }
                _ => None,
            })
            && let Some(site) =
                crate::exe::first_dispatch_within(&check.unresolved_dispatch, eval_body_span)
        {
            return Err(crate::exe::unresolved_dispatch_error(site));
        }

        // Sprint 66 Wave 3a-γ: the `discover-tests` / `run-test` /
        // `cranelisp_trace_format` intrinsics are registered unconditionally
        // at JIT setup inside `inline_jit_codegen_for_names` (and inside the
        // expression-eval JIT in `pipeline.rs`). No per-program scan, no
        // conditional plumbing. See FIXME 0178 for the architectural
        // principle (no conditional registration of intrinsics — uniform
        // dispatch through `JITBuilder::symbol()`).
        //
        // The intrinsics dereference `TestRunnerState` / `TraceDisplayState`
        // at call time. The `TestRunnerState` allocation lives on
        // `SharedState` (built once in `CompilerSession::new`); the
        // thread-local pointer is set just-in-time below before invoking
        // compiled code. The trace-display state is set per-eval when
        // `(trace ...)` is present in the expression.
        set_test_runner_state(&self.shared.test_runner_state);

        let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

        if has_expr {
            // S76 W-Collapse: REPL expression eval flows through the SAME
            // unified `compile_to_module` path as every other defn —
            // `inline_jit_codegen_for_module` (called above) already compiled
            // the synthetic `__expr` defn into the module's symbol table with
            // a populated GOT slot + `Code::Jit` lifecycle owner. We read the
            // GOT address and call it directly; no second hand-rolled JIT.
            // (`pipeline::compile_and_execute_expr` + its trace twin are
            // deleted.) The `Arc<Jit>` retention lives on the `__expr` entry's
            // `Code::Jit`, so the code stays mapped for the duration of the
            // call + the IO trampoline below.
            // A runtime TRAP (broken-symbol stub, exhaustiveness failure, empty
            // `(select [])`, …) is NOT a compiler error — it surfaces as
            // `ExprOutcome::Trap` and becomes an `EvalResult::RuntimeError` the
            // printer renders per repl/spec.md §18.5 (`runtime error: {payload}`,
            // no wrapper chain). Genuine compiler/platform faults still `?`.
            match crate::pipeline::execute_compiled_expr(
                check.display.as_ref(),
                &self.shared,
                module,
            )? {
                crate::pipeline::ExprOutcome::Value(result) => Ok(EvalResult::Val {
                    result,
                    warnings: check.warnings.clone(),
                }),
                crate::pipeline::ExprOutcome::Trap { message } => Ok(EvalResult::RuntimeError {
                    message,
                    warnings: check.warnings.clone(),
                }),
            }
        } else {
            if definition_symbols.is_empty() {
                return Err(CranelispError::CodegenError {
                    message: "definition-only program produced no definition result".to_string(),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
            Ok(EvalResult::Definitions {
                symbols: definition_symbols.to_vec(),
                warnings: check.warnings.clone(),
            })
        }
    }

    // `build_traced_fns` — DELETED S76 (FIXME 0256, trace ruling 2026-06-04).
    // Trace-target discovery is now backend-internal
    // (`trace_codegen::discover_traced_fns_from_tables`); int no longer
    // populates a `traced_fns` list nor threads it into the eval path.

    // `compile_dep_inline` — deleted Sprint 59 Workstream A (the dual-path
    // persistence collapse; its design record is retired, recoverable with
    // `git show 7f834bf6:design/int/dual-path-persistence-collapse.md`).
    //
    // The session-side second orchestrator (an inline `priority_worker_loop`
    // running on the eval thread in parallel with the persistent priority
    // worker pool) has been replaced by `register_dep_for_eval` above: the
    // persistent worker pool is now the single orchestrator for every
    // dep, and the eval thread blocks on `wait_module_inmem_complete_blocking`
    // scoped to the dep. See `design/int/int.md` §6.1 (the single
    // `register_module` recursion and its dep-registration sites, including
    // `register_dep_for_eval`) and §7.1 (Decision 37 — cache-hit-or-fresh is a
    // branch inside that recursion, not a parallel orchestrator).

    /// The candidate listing an entered spelling displays instead of
    /// evaluating — `None` when the turn is not an introspection turn and must
    /// fall through to the value/eval path.
    ///
    /// The set is the shared candidate query, so the prompt and `/sig` answer
    /// from ONE resolution (§3.8) and a spelling denoting several declarations
    /// lists them all (§4.1.11) instead of showing a tier winner or falling
    /// through to the §8.6.5 use-site rejection. Every result is display-only:
    /// a bare lookup is never recorded as a symbol's source (FIXME 0486).
    ///
    /// A turn lists only when EVERY candidate is listable, and SET SIZE decides
    /// a value-path member (`design/int/int.md` §3.3). Alone, a
    /// result-only-polymorphic nullary constructor takes the turn to the §1.5.1
    /// value display; among several it is listed by its own §4.1.2 constructor
    /// line, since that display is the sole-candidate disposition and routing a
    /// listed member through it would re-resolve the spelling tier-first inside
    /// the listing. A zero-argument macro takes the turn to expansion (§4.1.6)
    /// at any set size (`describes_at_lookup` / `lists_at_lookup`).
    ///
    /// 0571 D2: a QUALIFIED spelling (`mathx/gcount`) takes this same path —
    /// mode+name-uniform, NO codegen, since a value-position FQ ref would
    /// otherwise reach the backend slot-less as the `undefined variable`
    /// codegen leak. Its module is present on the FQ-autoload RETRY (the first
    /// pass gaps → `drive_module_dep` loads it → re-runs this gate), and the
    /// §8.7.3 visibility gate a `--run` reference hits is the resolver's, so an
    /// inaccessible member falls through to the same mode-uniform error.
    pub(crate) fn check_bare_symbol_introspection(&self, sexp: &Sexp) -> Option<EvalResult> {
        let name = match sexp {
            Sexp::Symbol(name, _) => name.as_str(),
            _ => return None,
        };

        // Must be a single bare identifier (no parens, no spaces, no brackets).
        if name
            .contains(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']')
        {
            return None;
        }

        // Primitive type names — Int, Bool, Float, String (spec §4.1.3) —
        // have no symbol-table declaration to describe.
        if intrinsic_type_from_name(name).is_some() {
            return Some(EvalResult::Candidates {
                symbols: vec![FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from(name),
                }],
                warnings: Vec::new(),
            });
        }

        // `SpecialFormTail::Skipped` keeps the two-tier reach: a bare
        // special-form name is not a value, so it falls through here and
        // reaches the §4.1.9 feedback path — only the introspection COMMANDS
        // consult the root table.
        let symbols = self.resolve_candidates(name, SpecialFormTail::Skipped);
        if symbols.is_empty()
            || !symbols.iter().all(|symbol| {
                self.entry_at(symbol)
                    .is_some_and(|entry| lists_at_lookup(&entry, symbols.len()))
            })
        {
            return None;
        }
        Some(EvalResult::Candidates {
            symbols,
            warnings: Vec::new(),
        })
    }
}

/// Whether a declaration answers a lookup with an introspection line
/// (spec §4.1) rather than belonging to the value/eval path.
fn describes_at_lookup(entry: &Binding<Code>) -> bool {
    match &entry.declaration {
        // A zero-arg macro is expanded, not described.
        Decl::Macro(declaration) => !declaration
            .clauses
            .iter()
            .any(|clause| clause.params.is_empty() && clause.rest_param.is_none()),
        // An overload with no arm has no signature to show.
        Decl::Overloaded(declaration) => !declaration.arms.is_empty(),
        // D2 (S108): a concrete nullary constructor (user `Red : user/Color`)
        // describes through `format_def_entry`'s Constructor arm as the §4.1.2
        // line `:user/Color user/Color.Red ; deftype`; a result-only-polymorphic
        // one alone takes the §1.5.1 value display instead. Non-nullary ctors,
        // primitives and user functions display per §4.1.1, §4.1.2.
        Decl::Callable(_) => !is_polymorphic_nullary_ctor(entry),
        Decl::TraitMethod(_) | Decl::SpecialForm(_) | Decl::Type(_) | Decl::Trait(_) => true,
        Decl::ImplShell(_) => false,
    }
}

/// A nullary constructor whose result type is not concrete — bare
/// `None : ∀a. (Option a)`, as against the concrete `Red : user/Color`.
///
/// `Type::is_concrete` is the single-source concreteness predicate (D2, S108);
/// false for every other declaration, including non-nullary constructors.
fn is_polymorphic_nullary_ctor(entry: &Binding<Code>) -> bool {
    entry.callable().is_some_and(|callable| {
        matches!(
            &callable.origin,
            CallableOrigin::Ctor { field_count: 0, .. }
        ) && !callable.arm.scheme.ty.is_concrete()
    })
}

/// Whether a declaration can be LISTED at a bare lookup denoting `candidates`
/// declarations.
///
/// One candidate is `describes_at_lookup`'s disposition unchanged. Several make
/// the turn a §4.1.11 listing, where a result-only-polymorphic nullary
/// constructor is rendered by its own §4.1.2 constructor line — the §1.5.1
/// value display it takes alone is keyed on nothing canonical, so listing
/// through it would reintroduce a tier-first read inside the listing
/// (`design/int/int.md` §3.3). A zero-argument macro remains unlistable: the
/// turn is an expansion (§4.1.6), not a display.
fn lists_at_lookup(entry: &Binding<Code>, candidates: usize) -> bool {
    describes_at_lookup(entry) || (candidates > 1 && is_polymorphic_nullary_ctor(entry))
}

// ---------------------------------------------------------------------------
// Unit tests — the Matrix E recording rule at the writer seam (FIXME 0486)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session_v4::Introspection;

    fn fq(module: &str, name: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(name),
        }
    }

    fn defining_turn(module: &str, name: &str) -> EvalResult {
        EvalResult::Definitions {
            symbols: vec![fq(module, name)],
            warnings: Vec::new(),
        }
    }

    fn lookup_turn(module: &str, name: &str) -> EvalResult {
        EvalResult::Candidates {
            symbols: vec![fq(module, name)],
            warnings: Vec::new(),
        }
    }

    fn store_with(fq_key: &FQSymbol, source: &str) -> dashmap::DashMap<FQSymbol, Introspection> {
        let m: dashmap::DashMap<FQSymbol, Introspection> = dashmap::DashMap::new();
        m.entry(fq_key.clone()).or_default().source = Some(source.to_string());
        m
    }

    // spec: repl/spec.md §3.6 (FIXME 0486) / design/int/s102-defect-wave.md
    // §7.3 Matrix E — a GENUINE definition turn records the turn's authored
    // text: creates the record on first definition, updates it on
    // redefinition (the load-bearing half §4.2's source-first regeneration
    // reads).
    #[test]
    fn defining_turn_creates_and_updates_source_record() {
        let solo = fq("user", "solo");
        let m: dashmap::DashMap<FQSymbol, Introspection> = dashmap::DashMap::new();
        record_defining_turn_source(
            Some(&m),
            &defining_turn("user", "solo"),
            "(defn solo [x] (mul-i64 x 3))",
        );
        assert_eq!(
            m.get(&solo).unwrap().source.as_deref(),
            Some("(defn solo [x] (mul-i64 x 3))"),
            "definition turn creates the record"
        );
        record_defining_turn_source(
            Some(&m),
            &defining_turn("user", "solo"),
            "(defn solo [x] (mul-i64 x 4))",
        );
        assert_eq!(
            m.get(&solo).unwrap().source.as_deref(),
            Some("(defn solo [x] (mul-i64 x 4))"),
            "redefinition turn updates the record"
        );
    }

    // spec: repl/spec.md §3.6 + §18.4 (FIXME 0486) — Matrix E negative cells:
    // a bare lookup (a candidate listing, healthy or broken alike) MUST NOT
    // touch an existing record and MUST NOT create one; an expression turn
    // (`Val`) never writes.
    #[test]
    fn bare_lookup_neg_never_touches_or_creates_source_record() {
        let solo = fq("user", "solo");
        let m = store_with(&solo, "(defn solo [x] (mul-i64 x 3))");
        // The corrupting shape: the bare-lookup turn's text is the bare name.
        record_defining_turn_source(Some(&m), &lookup_turn("user", "solo"), "solo");
        assert_eq!(
            m.get(&solo).unwrap().source.as_deref(),
            Some("(defn solo [x] (mul-i64 x 3))"),
            "a lookup turn must NOT overwrite the authored source"
        );
        // No record → no creation either (e.g. bare lookup of a prelude name
        // must not seed a bogus record under the resolved primitive's FQ).
        record_defining_turn_source(Some(&m), &lookup_turn("primitives", "add-i64"), "add-i64");
        assert!(
            !m.contains_key(&fq("primitives", "add-i64")),
            "a lookup turn must NOT create a record"
        );
        // Expression turns never write.
        record_defining_turn_source(
            Some(&m),
            &EvalResult::Val {
                result: crate::result_owner::OwnedProgramResult::inert(1, Type::Int),
                warnings: Vec::new(),
            },
            "(solo 2)",
        );
        assert_eq!(m.len(), 1, "Val results never write");
        // Batch mode (store absent): a defining result is a silent no-op.
        record_defining_turn_source(None, &defining_turn("user", "solo"), "(defn solo [x] x)");
    }

    // -----------------------------------------------------------------------
    // S112 W5 — the trait-impl registration echo names the RESOLVED
    // implementing type (`impl <trait> for <type>`, repl/spec.md §1.1 /
    // §4.1.4), NOT the settled echo-the-head pairing head. The label
    // `impl_echo_type_name` mints is the `Trait.Type` key that format.rs's
    // §1.1 echo splits into `impl <trait> for <type>`.
    // -----------------------------------------------------------------------
    mod impl_echo_display {
        use crate::session_v4::impl_echo_type_name;
        use cranelisp_types::{
            Span, Symbol, TraitImpl, TraitName, TraitRef, TypeExpr, TypeName, TypeRef,
        };

        fn tref(name: &str) -> TypeRef {
            TypeRef::new(None, TypeName::from(name))
        }

        // spec: repl/spec.md §1.1/§4.1.4 (spec §7.3.5 Case 2) — the echo-the-head
        // HKT impl `(impl (Functor f) (Functor Option) …)` echoes the implementing
        // CONSTRUCTOR `Option` (slot-2 pairing's argument), NOT the pairing head
        // `Functor`. Guards the S112 `impl user/Functor for user/Functor` defect.
        #[test]
        fn echo_head_hkt_impl_names_the_constructor_not_the_pairing_head() {
            let t = TraitImpl {
                trait_name: TraitRef::new(None, TraitName::from("Functor")),
                head_con_var: Some(Symbol::from("f")),
                // slot-2 `(Functor Option)` — the settled pairing form.
                target: TypeExpr::Applied(tref("Functor"), vec![TypeExpr::Named(tref("Option"))]),
                type_constraints: vec![],
                methods: vec![],
                span: Span::default(),
            };
            assert_eq!(
                impl_echo_type_name(&t),
                "Option",
                "the HKT echo-the-head impl MUST resolve to the implementing \
                 constructor `Option`, never the pairing head `Functor`"
            );
            // The composed label is what the §1.1 echo splits on `.` into
            // `impl <trait> for <type>` — MUST be `Functor.Option`.
            let label = format!("{}.{}", t.trait_name.name, impl_echo_type_name(&t));
            assert_eq!(label, "Functor.Option");
            let (trait_seg, type_seg) = label.split_once('.').unwrap();
            assert_eq!((trait_seg, type_seg), ("Functor", "Option"));
        }

        // spec: repl/spec.md §1.1 — a conventional (kind-`*`) impl
        // `(impl Sizeable Circle …)` is UNCHANGED: slot-2 is the bare type head.
        #[test]
        fn conventional_impl_names_the_bare_target_head() {
            let t = TraitImpl {
                trait_name: TraitRef::new(None, TraitName::from("Sizeable")),
                head_con_var: None,
                target: TypeExpr::Named(tref("Circle")),
                type_constraints: vec![],
                methods: vec![],
                span: Span::default(),
            };
            assert_eq!(impl_echo_type_name(&t), "Circle");
            let label = format!("{}.{}", t.trait_name.name, impl_echo_type_name(&t));
            assert_eq!(label, "Sizeable.Circle");
        }

        // A target already rewritten to `Named` while `head_con_var` is set
        // (defence in depth: if the settled-target rewrite ever reaches this
        // seam) falls through to the plain head — still the constructor.
        #[test]
        fn rewritten_named_target_falls_through_to_the_head() {
            let t = TraitImpl {
                trait_name: TraitRef::new(None, TraitName::from("Functor")),
                head_con_var: Some(Symbol::from("f")),
                target: TypeExpr::Named(tref("Option")),
                type_constraints: vec![],
                methods: vec![],
                span: Span::default(),
            };
            assert_eq!(impl_echo_type_name(&t), "Option");
        }
    }

    // -----------------------------------------------------------------------
    // D2 (S108) — the concreteness discriminator in the bare-symbol gate.
    // A nullary ctor routes to introspection ONLY when its scheme is concrete
    // (spec §4.1.2, e.g. user `Red`); a non-concrete nullary ctor (result-only-
    // polymorphic, e.g. `None`) returns `None` and falls through to the §1.5.1
    // value display. Non-nullary ctors always introspect.
    // -----------------------------------------------------------------------

    use crate::code::SessionSymbolTable;
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::{
        CallableOrigin, CodegenBehaviour, DefnVariant, FQTypeName, Realization, Scheme, SynthSpec,
        TemplateBody, TemplateKind, TypeName, Visibility,
    };
    use std::collections::HashMap as StdHashMap;

    fn d2_session() -> CompilerSession {
        let tmp = tempfile::tempdir().unwrap();
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 1,
            run_mode: RunMode::Repl,
        };
        CompilerSession::new(settings, tmp.keep(), "user").expect("test session bootstrap")
    }

    /// Build a nullary `DefKind::Constructor` Def whose scheme type is the ADT
    /// `type_name` applied to `args` — `args` empty ⇒ concrete, a `Var` arg ⇒
    /// non-concrete.
    fn install_in_user(s: &CompilerSession, name: &str, type_name: &str, args: Vec<Type>) {
        let user = s.current_module_path();
        let fqtn = FQTypeName::new(ModuleFullPath::from("user"), TypeName::from(type_name));
        let scheme = Scheme {
            type_vars: if args.iter().any(|arg| matches!(arg, Type::Var(0))) {
                vec![0]
            } else {
                Vec::new()
            },
            constraints: StdHashMap::new(),
            ty: Type::ADT(fqtn.clone(), args),
        };
        let origin = CallableOrigin::Ctor {
            type_name: fqtn,
            tag: 0,
            field_count: 0,
            internal: false,
            type_def: None,
        };
        let variant = DefnVariant {
            params: Vec::new(),
            body: cranelisp_types::Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: None,
            },
            span: Span::SYNTHETIC,
        };
        let install = |table: &mut SessionSymbolTable| {
            if scheme.ty.is_concrete() {
                let view = cranelisp_types::MonoDefnVariant {
                    name: Symbol::from(name),
                    params: Vec::new(),
                    body: cranelisp_types::MonoExpr::lenient_from_expr(
                        &variant.body,
                        &Default::default(),
                        &Default::default(),
                        &Default::default(),
                    ),
                    span: Span::SYNTHETIC,
                    mode_summary: None,
                };
                table
                    .install_concrete(
                        Symbol::from(name),
                        scheme.clone(),
                        Vec::new(),
                        None,
                        0,
                        origin.clone(),
                        Realization::Body { view, code: None },
                        Some(variant.clone()),
                        Vec::new(),
                        Visibility::Public,
                    )
                    .map(|_| ())
            } else {
                table.install_template(
                    Symbol::from(name),
                    scheme.clone(),
                    Vec::new(),
                    None,
                    0,
                    origin.clone(),
                    TemplateBody::Synth(SynthSpec::new(variant.clone())),
                    TemplateKind::Parametric,
                    Vec::new(),
                    Visibility::Public,
                )
            }
        };
        if let Some(mut table) = s.shared.symbol_tables.get_mut(&user) {
            install(&mut table).expect("constructor fixture installs");
        } else {
            let mut table = SessionSymbolTable::new_with_params(user.clone());
            install(&mut table).expect("constructor fixture installs");
            s.shared.symbol_tables.insert(user, table);
        }
    }

    // A CONCRETE nullary ctor (`Red : user/Color`, no type args) routes to the
    // introspection path — one candidate, never a defining turn — so the caller
    // formats the §4.1.2 definition line `:user/Color user/Color.Red ; deftype`.
    #[test]
    fn concrete_nullary_ctor_routes_to_introspection() {
        let s = d2_session();
        install_in_user(&s, "Red", "Color", Vec::new());
        let out = s.check_bare_symbol_introspection(&Sexp::Symbol("Red".into(), Span::SYNTHETIC));
        match out {
            Some(EvalResult::Candidates { symbols, .. }) => {
                assert_eq!(
                    symbols.iter().map(FQSymbol::to_string).collect::<Vec<_>>(),
                    vec!["user/Red".to_string()],
                    "the concrete nullary ctor lists under its canonical identity"
                );
            }
            Some(_) => panic!("concrete nullary ctor `Red` must introspect, not evaluate"),
            None => {
                panic!("concrete nullary ctor `Red` MUST introspect, not fall to the value path")
            }
        }
    }

    // A NON-CONCRETE nullary ctor (`Nada : ∀a. (user/Opt a)`) is NOT
    // introspected — the gate returns `None`, so the caller falls through to
    // the §1.5.1 polymorphic value display (preserving bare `None`'s behaviour).
    #[test]
    fn non_concrete_nullary_ctor_falls_through_to_value_path() {
        let s = d2_session();
        install_in_user(&s, "Nada", "Opt", vec![Type::Var(0)]);
        let out = s.check_bare_symbol_introspection(&Sexp::Symbol("Nada".into(), Span::SYNTHETIC));
        assert!(
            out.is_none(),
            "non-concrete nullary ctor `Nada` MUST NOT introspect (falls to §1.5.1 \
             value display)"
        );
    }

    // spec: repl/spec/04-self-documentation.md §4.1.11 — SET SIZE decides a
    // value-path member. The same non-concrete nullary ctor that takes the
    // value path alone is LISTED once the spelling denotes several
    // declarations, so a mixed set never reaches the §8.6.5 use-site ambiguity
    // (`design/int/int.md` §3.3). Both legs run over one fixture, so the cell
    // discriminates the set-size condition itself, not two unrelated setups.
    #[test]
    fn polymorphic_nullary_ctor_lists_among_several_candidates() {
        let s = d2_session();
        install_in_user(&s, "Nada", "Opt", vec![Type::Var(0)]);
        assert!(
            s.check_bare_symbol_introspection(&Sexp::Symbol("Nada".into(), Span::SYNTHETIC))
                .is_none(),
            "sole candidate: the non-concrete nullary ctor still takes the value path"
        );

        // A second declaration under the same spelling, imported from `n`.
        let n = ModuleFullPath::from("n");
        let mut table = SessionSymbolTable::new_with_params(n.clone());
        let _ = crate::repl::test_support::install_userfn(
            &mut table,
            "Nada",
            Some("function candidate for Nada"),
            Visibility::Public,
        );
        s.shared.symbol_tables.insert(n, table);
        crate::repl::test_support::expose_import(&s, "Nada", "n", "Nada");

        match s.check_bare_symbol_introspection(&Sexp::Symbol("Nada".into(), Span::SYNTHETIC)) {
            Some(EvalResult::Candidates { symbols, .. }) => assert_eq!(
                symbols.iter().map(FQSymbol::to_string).collect::<Vec<_>>(),
                vec!["n/Nada".to_string(), "user/Nada".to_string()],
                "every candidate lists, the ctor under its own canonical identity"
            ),
            _ => panic!(
                "a several-candidate set including a non-concrete nullary ctor MUST list \
                 (§4.1.11), not fall through to the §8.6.5 use-site ambiguity"
            ),
        }
    }

    // -----------------------------------------------------------------------
    // E7 (S108) — §17.1 sequential-eval-abandon on the no-agent multi-form
    // path. A multi-form REPL line reaching `eval` (the no-agent path — the
    // classifier routes multi-form to the agent when one is active) is
    // evaluated form-by-form and ABANDONS on the FIRST error, surfacing it as
    // a real `Err` — NOT a fake `Val{0}` whose error-carrying warning the
    // trailing `warnings_mut` assignment then clobbers (the swallow that
    // produced a silent `:Int 0`). An all-green multi-form line evaluates
    // without error.
    // -----------------------------------------------------------------------

    // spec: repl/spec.md §17.1 — a multi-form line whose FIRST form errors
    // returns that form's error directly (not a swallowed value), and abandons
    // before the later form.
    #[test]
    fn multi_form_error_in_first_form_returns_that_error_not_fake_val() {
        let mut s = d2_session();
        match s.eval("foo bar") {
            Err(e) => {
                let msg = e.to_string();
                assert!(
                    msg.contains("undefined variable: foo"),
                    "form-1 error MUST surface `undefined variable: foo`; got: {msg}"
                );
                assert!(
                    !msg.contains("bar"),
                    "abandon-on-first: the later form `bar` MUST NOT be reached/reported; \
                     got: {msg}"
                );
            }
            Ok(_) => panic!(
                "a multi-form line with an error in form 1 MUST return the form-1 error \
                 (Err), not swallow it into a fake `Val{{0}}`"
            ),
        }
    }

    // spec: repl/spec.md §17.1 — abandon-on-FIRST when a GREEN form precedes
    // the error: `2 foo` evaluates `2`, then the undefined-`foo` error MUST
    // still surface as a real `Err` (not a fabricated trailing value line).
    #[test]
    fn multi_form_error_in_second_form_after_green_returns_that_error() {
        let mut s = d2_session();
        match s.eval("2 foo") {
            Err(e) => {
                let msg = e.to_string();
                assert!(
                    msg.contains("undefined variable: foo"),
                    "the form-2 error MUST surface even though a green form precedes it; \
                     got: {msg}"
                );
            }
            Ok(_) => panic!(
                "`2 foo` MUST return the form-2 error (Err), not a swallowed \
                 fake `Val{{0}}` after the green `2`"
            ),
        }
    }

    // spec: repl/spec.md §17.1 — all-green multi-form control: `1 2 3`
    // evaluates without error (the display shape is NOT pinned by §17.1; this
    // asserts only that no error is raised — Wave C must not change the green
    // path).
    #[test]
    fn multi_form_all_green_returns_no_error() {
        let mut s = d2_session();
        assert!(
            s.eval("1 2 3").is_ok(),
            "an all-green multi-form line `1 2 3` MUST evaluate without error"
        );
    }
}
