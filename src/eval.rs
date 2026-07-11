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
    CranelispError, DefKind, ErrorLocation, FQSymbol, ModuleEntry, ModuleFullPath,
    ModuleStrategy, Sexp, Span, Symbol, TopLevel, Type, Warning,
};

use cranelisp_typecheck::{CheckResult, CheckState};

use crate::session_v4::{
    extract_def_name_from_sexp, intrinsic_type_from_name, is_comment_only,
    set_test_runner_state, CompilerSession, EvalResult, Introspection,
};
use crate::worker::ModuleCompiler;

/// Record the turn's verbatim source text on the defined symbol's
/// introspection record — for GENUINE definition turns only (Matrix E
/// recording rule; FIXME 0486, `design/int/s102-defect-wave.md` §7.3).
///
/// A display-only `EvalResult::Def` (`defined: false` — bare-symbol lookup)
/// MUST NOT touch the record: the lookup text (`"solo"`) would clobber the
/// authored `(defn …)` form that `/info`/`/source` serve (introspection-first
/// precedence in `info_definition_source`). For real definition turns the
/// write is load-bearing: it records the authored text that §4.2's
/// source-first regeneration emits — coordinate any change with that seam
/// (same authorship invariant).
///
/// `introspection` is `Some` only under `RunMode::Repl` (D1b ctor gate) —
/// `None` in batch, no second discriminator to drift.
pub(crate) fn record_defining_turn_source(
    introspection: Option<&dashmap::DashMap<FQSymbol, Introspection>>,
    result: &EvalResult,
    src: &str,
) {
    let EvalResult::Def { symbol, defined: true, .. } = result else {
        return;
    };
    if let Some(m) = introspection {
        let fq = FQSymbol {
            module: symbol.module.clone(),
            symbol: symbol.symbol.clone(),
        };
        m.entry(fq).or_default().source = Some(src.to_string());
    }
}

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
        let result = self.shared.scheduler.wait_module_inmem_complete_blocking(dep_module);

        // S93 Invariant SW: the eval thread recorded a `current → dep`
        // cycle-check edge (`register_dep_edge_for_cycle_check`, via `block_dep`)
        // but never moved its entry to `TypecheckBlocked`. The wait is over —
        // clear the forward edge so the terminal entry carries no stale
        // `blocked_on` into the next REPL form (which could otherwise mislead a
        // future reverse-direction cycle check).
        self.shared.scheduler.clear_dep_edge(&self.current_module_path());

        match result {
            Ok(()) => Ok(()),
            Err(e) => {
                self.shared.scheduler.reset_all_failed_modules();
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
                    // S102 CS-0489 (§18.8 repair direction): a genuine
                    // definition turn removes its symbol from the module's
                    // degraded-load failed set; when the set empties the
                    // module leaves the §14.4 error-blocked state.
                    self.clear_repaired_failed_form(&result);
                    all_warnings.extend(result.warnings().iter().cloned());
                    last_result = Some(result);
                }
                Ok(None) => {}
                Err(e) => {
                    // Propagate when the whole input was a single cluster (one
                    // form, or one `:Type`+form annotation pair); otherwise
                    // report inline and continue with the next cluster.
                    if cluster.len() == sexps.len() {
                        return Err(e);
                    }
                    // Multi-form: report error inline but continue.
                    // TODO: multi-form error handling — for now, wrap as Val.
                    last_result = Some(EvalResult::Val {
                        value: 0,
                        ty: Type::Int,
                        warnings: vec![Warning {
                            kind: cranelisp_types::WarningKind::Other,
                            message: format!("Error: {e}"),
                            span: Span::SYNTHETIC,
                        }],
                    });
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
    pub(crate) fn eval_one_form(&mut self, sexp: &Sexp) -> Result<Option<EvalResult>, CranelispError> {
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
    pub(crate) fn process_single_form(&mut self, sexp: &Sexp) -> Result<Option<EvalResult>, CranelispError> {
        self.process_form_cluster(std::slice::from_ref(sexp))
    }

    /// Process a REPL sexp cluster (one or more sexps) as a single Additive
    /// cluster, then codegen. A cluster is normally a single sexp, but a
    /// leading `:Type` annotation sexp groups with the following form sexp so
    /// the frontend's `build_forms` pairing (`Expr::Annotate`) fires — int
    /// orchestrates the cluster boundary; the frontend decides what one form is
    /// (BC §1 invariant 9; FIXME 0329). The `cluster_head` sexp is the one used
    /// for `Def`-name extraction and `/source` span when the cluster collapses
    /// to a single definition during expansion.
    pub(crate) fn process_form_cluster(&mut self, cluster: &[Sexp]) -> Result<Option<EvalResult>, CranelispError> {
        use crate::worker::ClusterOnce;
        use crate::process_form;

        const MAX_DEP_RETRIES: usize = 100;

        // The "head" sexp drives `Def`-name extraction when the cluster
        // collapses to a single handled-during-expansion form (defmacro,
        // import, mod, …). For an annotation pair the meaningful head is the
        // form being annotated (the last sexp), not the leading `:Type`.
        // `cluster` is always non-empty (the eval loop never builds an empty
        // span), so `last()` is `Some`.
        let head_sexp = match cluster.last() {
            Some(s) => s,
            None => return Ok(None),
        };

        for retry in 0..MAX_DEP_RETRIES {
            let module = self.current_module_path();
            let single_sexp = cluster.to_vec();

            let result = {
                // Extract REPL check_state for worker use, restore after.
                cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &module);
                let repl_cs = self.repl_check_state.lock()
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
                );
                // Restore REPL check_state.
                *self.repl_check_state.lock()
                    .unwrap_or_else(|e| e.into_inner()) = Some(wctx.check_state);
                res?
            };

            match result {
                ClusterOnce::Done { processed, program } => {
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
                    // If program is empty, the form was handled during expansion
                    // (defmacro, import, platform, mod). Return Def with name
                    // extracted from the original sexp.
                    if program.is_empty() {
                        // F5a (S103, FIXME 0507 Issue 3): the defmacro exit
                        // returns BEFORE the ordinary `apply_redefinition_outcomes`
                        // call below, so the §10 T1 full-cure driver must be
                        // reachable here too. Currently moot (macro heads carry
                        // no reverse edges, so a redefined-macro target produces
                        // an empty stale set and no reload), but the driver MUST
                        // be reachable from BOTH exits — a redefined macro whose
                        // dependents use it is cured by the dependent cascade.
                        self.apply_redefinition_outcomes(&redefinitions);
                        return match extract_def_name_from_sexp(head_sexp) {
                            Some(symbol_name) => Ok(Some(EvalResult::Def {
                                symbol: FQSymbol {
                                    module: module.clone(),
                                    symbol: Symbol::from(symbol_name),
                                },
                                ty: Type::Int,
                                warnings: cluster_warnings,
                                // Handled-during-expansion forms (defmacro)
                                // are genuine definitions.
                                defined: true,
                            })),
                            // import/platform/mod — no visible result.
                            None => Ok(None),
                        };
                    }
                    let check = CheckResult { warnings: cluster_warnings, display: None };
                    let eval_result = self.codegen_and_execute(&module, &program, &check)?;
                    // S101 dependent-recompilation transaction: clears broken
                    // records for recovered symbols (§18.6 direction 1) and
                    // runs the affected-set walk for AbiChanging redefinitions,
                    // stashing the §18.3 cascade report for the REPL printer.
                    self.apply_redefinition_outcomes(&redefinitions);
                    return Ok(Some(eval_result));
                }
                ClusterOnce::Gap { dep } => {
                    // The dep has already been registered + blocked on inside
                    // `process_cluster_once`; block on the persistent worker
                    // pool driving it to completion, then retry from the top.
                    self.register_dep_for_eval(&dep)?;
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

        unreachable!("invariant: loop always returns or errors before exhausting iterations")
    }

    /// Run codegen for definitions, then execute if there is a trailing expression.
    pub(crate) fn codegen_and_execute(
        &mut self,
        module: &ModuleFullPath,
        program: &[TopLevel],
        check: &CheckResult,
    ) -> Result<EvalResult, CranelispError> {
        // Ensure typecheck product exists for this module.
        crate::worker::ensure_typecheck_product(&self.shared.typecheck_products, module);

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

        // Unified JIT codegen via compile_to_module (Sprint 56 Wave 2).
        // Derives the compilation batch from `program`, compiles through the
        // single backend entry point, and populates `ModuleEntry::Def.code`
        // (Sprint 57 Wave 2 G6) + introspection. No env, no mode
        // discriminator — see design/int/phase2-codegen-convergence.md §5.
        crate::worker::inline_jit_codegen_for_module(
            &self.shared.scheduler,
            module,
            program,
            &self.shared.symbol_tables,
            self.shared.introspection.as_ref(),
            &[],
            Some(&self.shared),
        )?;

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
                &self.shared.symbol_tables,
                module,
            )? {
                crate::pipeline::ExprOutcome::Value { value, ty } => Ok(EvalResult::Val {
                    value,
                    ty,
                    warnings: check.warnings.clone(),
                }),
                crate::pipeline::ExprOutcome::Trap { message } => Ok(EvalResult::RuntimeError {
                    message,
                    warnings: check.warnings.clone(),
                }),
            }
        } else {
            // Definition-only: extract the defined symbol name from the last
            // user-visible form. Inlined defns (mono, default methods, trait
            // impl mangled methods) are appended after the original forms by
            // finalize_module — skip them by finding the last non-Defn form
            // (TraitDecl, TraitImpl, TypeDef) or the first Defn.
            let last = program.iter().rev().find(|tl| matches!(tl,
                TopLevel::TraitDecl(_) | TopLevel::TraitImpl(_) | TopLevel::TypeDef { .. }
            )).or_else(|| program.iter().find(|tl| matches!(tl, TopLevel::Defn(_))))
              .or(program.last());

            let symbol_name = last.map(|tl| match tl {
                TopLevel::Defn(d) => d.name.to_string(),
                TopLevel::TraitDecl(t) => t.name.to_string(),
                TopLevel::TraitImpl(t) => {
                    // `target` is a `TypeExpr` (no Display); use its head
                    // TypeRef name for the impl's display label.
                    let target = t
                        .target
                        .head_ref()
                        .map(|r| r.name.to_string())
                        .unwrap_or_else(|| "_".to_string());
                    format!("{}.{}", t.trait_name.name, target)
                }
                TopLevel::TypeDef { name, .. } => name.to_string(),
                TopLevel::Expr(_) => unreachable!("has_expr was false"),
            }).unwrap_or_default();

            let ty = check.display.as_ref()
                .map(|d| d.ty.clone())
                .unwrap_or(Type::Int);

            Ok(EvalResult::Def {
                symbol: FQSymbol {
                    module: module.clone(),
                    symbol: Symbol::from(symbol_name),
                },
                ty,
                warnings: check.warnings.clone(),
                // The definition-only codegen turn — the genuine writer.
                defined: true,
            })
        }
    }

    // `build_traced_fns` — DELETED S76 (FIXME 0256, trace ruling 2026-06-04).
    // Trace-target discovery is now backend-internal
    // (`trace_codegen::discover_traced_fns_from_tables`); int no longer
    // populates a `traced_fns` list nor threads it into the eval path.

    // `compile_dep_inline` — deleted Sprint 59 Workstream A §7 Step 5.
    //
    // The session-side second orchestrator (an inline `priority_worker_loop`
    // running on the eval thread in parallel with the persistent priority
    // worker pool) has been replaced by `register_dep_for_eval` above: the
    // persistent worker pool is now the single orchestrator for every
    // dep, and the eval thread blocks on `wait_module_inmem_complete_blocking`
    // scoped to the dep. See `design/int/dual-path-persistence-collapse.md`
    // §§2–3 (Decision 37 alignment) and §7 Step 5.

    /// Check if a bare symbol should produce introspection display instead of eval.
    ///
    /// Handles special forms, macros, builtin types, user types, traits,
    /// and non-nullary constructors (spec §4.1). Returns None for symbols
    /// that should be evaluated normally (variables, functions, and
    /// non-concrete nullary ctors — after S108 D2, concrete nullary ctors
    /// introspect; only result-only-polymorphic nullary ctors fall through
    /// to the value path).
    pub(crate) fn check_bare_symbol_introspection(&self, sexp: &Sexp) -> Option<EvalResult> {
        let name = match sexp {
            Sexp::Symbol(name, _) => name.as_str(),
            _ => return None,
        };

        // Must be a single bare identifier (no parens, no spaces, no brackets).
        if name.contains(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']') {
            return None;
        }

        // Check primitive type names: Int, Bool, Float, String (spec §4.1.3).
        // ALL results below are display-only (`defined: false`) — a bare
        // lookup MUST NOT be recorded as the symbol's source (FIXME 0486).
        if intrinsic_type_from_name(name).is_some() {
            return Some(EvalResult::Def {
                symbol: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from(name),
                },
                ty: Type::Int,
                warnings: Vec::new(),
                defined: false,
            });
        }

        let module = self.current_module_path();
        // S78 §2.7.6 — prelude is an OUTER SCOPE, not flattened into the
        // current table. A bare prelude-provided name (e.g. `add-i64`) is no
        // longer an `Import` entry here, so the current-table lookup misses;
        // when the per-module fallback bit is ON, hop to prelude's own table
        // (where `add-i64` is the `(export …)` re-export Import edge) so the
        // bare-value display still chains to `primitives/add-i64`. The hop
        // returns the entry from prelude's table, then `resolve_entry_for_display`
        // chains it the rest of the way (prelude → primitives).
        let (entry, lookup_module) = {
            let guard = self.current_symbol_table();
            match guard.get(name) {
                Some(e) => (e.clone(), module.clone()),
                None => {
                    drop(guard);
                    let prelude_path = ModuleFullPath::from("prelude");
                    let prelude_on = module != prelude_path
                        && self
                            .shared
                            .prelude_fallback
                            .get(&module)
                            .map(|b| *b)
                            .unwrap_or(false);
                    if !prelude_on {
                        return None;
                    }
                    let pe = self
                        .shared
                        .symbol_tables
                        .get(&prelude_path)?
                        .get(name)?
                        .clone();
                    (pe, prelude_path)
                }
            }
        };

        // Resolve import/reexport chains fully. Sprint 61 Slice 1: the
        // resolver now chases the full chain (user → prelude → primitives)
        // so re-exported primitives land on a terminal `Def` here instead
        // of an intermediate `Reexport` that the match below would drop
        // through `_ => None`. See
        // `design/int/bare-primitive-value-path.md` candidate 2.
        let (resolved_entry, resolved_module) =
            self.resolve_entry_for_display(&entry, &lookup_module);

        // Use the resolved module for re-export provenance (spec §8.9:
        // introspection MUST display the original defining module). The
        // downstream `format_eval_result` re-resolves and relies on
        // `format_def_entry`'s `module` parameter, so this is primarily
        // for FQSymbol consumers that read the symbol metadata directly.
        let fq_module = resolved_module;

        match &resolved_entry {
            ModuleEntry::Def { kind, scheme, .. } => match kind.as_ref() {
                DefKind::Macro { clauses_meta, .. } => {
                    // Zero-arg macros should be expanded, not introspected.
                    let has_zero_arg = clauses_meta
                        .iter()
                        .any(|c| c.params.is_empty() && c.rest_param.is_none());
                    if has_zero_arg {
                        return None;
                    }
                    Some(EvalResult::Def {
                        symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                        ty: Type::Int,
                        warnings: Vec::new(),
                        defined: false,
                    })
                }
                DefKind::Constructor { field_count, .. } => {
                    // D2 (S108): a nullary ctor's disposition splits by
                    // CONCRETENESS (`Type::is_concrete()`, the single-source
                    // predicate, types.rs:92):
                    // - non-concrete nullary (result-only-polymorphic, e.g. bare
                    //   `None`: `∀a. (Option a)`) → `None`, falling through to the
                    //   §1.5.1 value display `:(prelude/Option a) Option.None`
                    //   with NO `; deftype`.
                    // - concrete nullary (e.g. user `Red`: `user/Color`) →
                    //   introspection, routed via `format_def_entry`'s Constructor
                    //   arm to the §4.1.2 definition line
                    //   `:user/Color user/Color.Red ; deftype`.
                    // Non-nullary ctors always introspect. This collapses the
                    // former duplicate value-vs-introspection path for concrete
                    // nullary ctors while preserving §1.5.1 for polymorphic ones.
                    if *field_count == 0 && !scheme.ty.is_concrete() {
                        None
                    } else {
                        Some(EvalResult::Def {
                            symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                            ty: Type::Int,
                            warnings: Vec::new(),
                            defined: false,
                        })
                    }
                }
                // Primitives + user functions get introspection display per
                // spec §4.1.1, §4.1.2.
                _ => Some(EvalResult::Def {
                    symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                    ty: scheme.ty.clone(),
                    warnings: Vec::new(),
                    defined: false,
                }),
            },
            ModuleEntry::SpecialForm { scheme, .. } => Some(EvalResult::Def {
                symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                ty: scheme.ty.clone(),
                warnings: Vec::new(),
                defined: false,
            }),
            ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. } => {
                Some(EvalResult::Def {
                    symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                    ty: Type::Int,
                    warnings: Vec::new(),
                    defined: false,
                })
            }
            _ => None,
        }
    }
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

    fn def_result(module: &str, name: &str, defined: bool) -> EvalResult {
        EvalResult::Def {
            symbol: fq(module, name),
            ty: Type::Int,
            warnings: Vec::new(),
            defined,
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
            &def_result("user", "solo", true),
            "(defn solo [x] (mul-i64 x 3))",
        );
        assert_eq!(
            m.get(&solo).unwrap().source.as_deref(),
            Some("(defn solo [x] (mul-i64 x 3))"),
            "definition turn creates the record"
        );
        record_defining_turn_source(
            Some(&m),
            &def_result("user", "solo", true),
            "(defn solo [x] (mul-i64 x 4))",
        );
        assert_eq!(
            m.get(&solo).unwrap().source.as_deref(),
            Some("(defn solo [x] (mul-i64 x 4))"),
            "redefinition turn updates the record"
        );
    }

    // spec: repl/spec.md §3.6 + §18.4 (FIXME 0486) — Matrix E negative cells:
    // a bare lookup (display-only Def, healthy or broken alike) MUST NOT
    // touch an existing record and MUST NOT create one; an expression turn
    // (`Val`) never writes.
    #[test]
    fn bare_lookup_neg_never_touches_or_creates_source_record() {
        let solo = fq("user", "solo");
        let m = store_with(&solo, "(defn solo [x] (mul-i64 x 3))");
        // The corrupting shape: the bare-lookup turn's text is the bare name.
        record_defining_turn_source(Some(&m), &def_result("user", "solo", false), "solo");
        assert_eq!(
            m.get(&solo).unwrap().source.as_deref(),
            Some("(defn solo [x] (mul-i64 x 3))"),
            "display-only Def must NOT overwrite the authored source"
        );
        // No record → no creation either (e.g. bare lookup of a prelude name
        // must not seed a bogus record under the resolved primitive's FQ).
        record_defining_turn_source(Some(&m), &def_result("primitives", "add-i64", false), "add-i64");
        assert!(
            !m.contains_key(&fq("primitives", "add-i64")),
            "display-only Def must NOT create a record"
        );
        // Expression turns never write.
        record_defining_turn_source(
            Some(&m),
            &EvalResult::Val { value: 1, ty: Type::Int, warnings: Vec::new() },
            "(solo 2)",
        );
        assert_eq!(m.len(), 1, "Val results never write");
        // Batch mode (store absent): a defining result is a silent no-op.
        record_defining_turn_source(None, &def_result("user", "solo", true), "(defn solo [x] x)");
    }

    // -----------------------------------------------------------------------
    // D2 (S108) — the concreteness discriminator in the bare-symbol gate.
    // A nullary ctor routes to introspection ONLY when its scheme is concrete
    // (spec §4.1.2, e.g. user `Red`); a non-concrete nullary ctor (result-only-
    // polymorphic, e.g. `None`) returns `None` and falls through to the §1.5.1
    // value display. Non-nullary ctors always introspect.
    // -----------------------------------------------------------------------

    use crate::code::SessionSymbolTable;
    use crate::session_v4::{CompilerSession, SessionSettings, RunMode};
    use cranelisp_types::{
        CodegenBehaviour, FQTypeName, Scheme, TypeName, Visibility,
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
        CompilerSession::new(settings, tmp.keep(), "user")
    }

    /// Build a nullary `DefKind::Constructor` Def whose scheme type is the ADT
    /// `type_name` applied to `args` — `args` empty ⇒ concrete, a `Var` arg ⇒
    /// non-concrete.
    fn nullary_ctor_entry(type_name: &str, args: Vec<Type>) -> ModuleEntry<crate::code::Code> {
        let fqtn = FQTypeName::new(ModuleFullPath::from("user"), TypeName::from(type_name));
        let scheme = Scheme {
            type_vars: Vec::new(),
            constraints: StdHashMap::new(),
            ty: Type::ADT(fqtn.clone(), args),
        };
        ModuleEntry::def(
            scheme,
            DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn,
                tag: 0,
                field_count: 0,
                internal: false,
                type_def: None,
                mode_summary: None,
            },
        )
        .visibility(Visibility::Public)
        .build()
    }

    fn install_in_user(s: &CompilerSession, name: &str, entry: ModuleEntry<crate::code::Code>) {
        let user = s.current_module_path();
        if let Some(mut table) = s.shared.symbol_tables.get_mut(&user) {
            table.insert(Symbol::from(name), entry);
        } else {
            let mut table = SessionSymbolTable::new_with_params(user.clone());
            table.insert(Symbol::from(name), entry);
            s.shared.symbol_tables.insert(user, table);
        }
    }

    // A CONCRETE nullary ctor (`Red : user/Color`, no type args) routes to the
    // introspection path — a display-only `EvalResult::Def` — so the caller
    // formats the §4.1.2 definition line `:user/Color user/Color.Red ; deftype`.
    #[test]
    fn concrete_nullary_ctor_routes_to_introspection() {
        let s = d2_session();
        install_in_user(&s, "Red", nullary_ctor_entry("Color", Vec::new()));
        let out = s.check_bare_symbol_introspection(&Sexp::Symbol("Red".into(), Span::SYNTHETIC));
        match out {
            Some(EvalResult::Def { defined, symbol, .. }) => {
                assert!(!defined, "bare lookup must be display-only (defined:false)");
                assert_eq!(symbol.symbol.as_ref(), "Red");
            }
            Some(_) => panic!("concrete nullary ctor `Red` must introspect as a Def, not a Val"),
            None => panic!(
                "concrete nullary ctor `Red` MUST introspect (Some(Def)), not fall to \
                 the value path"
            ),
        }
    }

    // A NON-CONCRETE nullary ctor (`Nada : ∀a. (user/Opt a)`) is NOT
    // introspected — the gate returns `None`, so the caller falls through to
    // the §1.5.1 polymorphic value display (preserving bare `None`'s behaviour).
    #[test]
    fn non_concrete_nullary_ctor_falls_through_to_value_path() {
        let s = d2_session();
        install_in_user(&s, "Nada", nullary_ctor_entry("Opt", vec![Type::Var(0)]));
        let out = s.check_bare_symbol_introspection(&Sexp::Symbol("Nada".into(), Span::SYNTHETIC));
        assert!(
            out.is_none(),
            "non-concrete nullary ctor `Nada` MUST NOT introspect (falls to §1.5.1 \
             value display)"
        );
    }
}
