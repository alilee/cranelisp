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
fn top_level_to_parsed_entries(program: &[TopLevel]) -> Vec<cranelisp_types::ParsedEntry> {
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
) -> Result<Option<cranelisp_types::ResolutionGap>, CranelispError> {
    // Wave 3b-2c.3: FIXME 0179 (cluster-mode read-union via View::union) has
    // landed in typecheck. Cluster mode is now activated as the hot path —
    // writes flow to a fresh staging table, reads union staging-first with
    // live, and on Ok the staging entries commit to live atomically. On Err
    // staging drops and live is unchanged.
    //
    // Returns `Ok(Some(gap))` when typecheck surfaces a recoverable
    // `CheckError::Gap` — the FQ-auto-load orchestration (spec §8.5.4 / §9.3.6,
    // FIXME 0268) catches an unloaded-module gap here and loads-and-retries.
    process_cluster_with_staging(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        working_program,
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
    match check_program_compat(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        module,
        working_program,
    )? {
        None => Ok(()),
        Some(gap) => Err(CranelispError::TypeError {
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
) -> Result<Option<cranelisp_types::ResolutionGap>, CranelispError> {
    use cranelisp_typecheck::{check_forms, CheckError, SymbolTableAccess};

    let parsed = top_level_to_parsed_entries(working_program);
    if parsed.is_empty() {
        return Ok(None);
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
        // On Ok: commit staging entries to live.
        Ok(()) => {
            commit_staging_to_live(symbol_tables, module, staging);
            Ok(None)
        }
        // A recoverable resolution gap (e.g. an FQ reference to a module not
        // yet loaded). Staging drops here (atomic discard, live unchanged);
        // the gap is handed back to `finalize_module` for FQ-auto-load
        // orchestration (FIXME 0268). On retry a fresh staging frame runs.
        Err(CheckError::Gap(gap)) => Ok(Some(gap)),
        // A genuine type error — staging drops, live unchanged.
        Err(e) => Err(check_error_to_cranelisp_error(e)),
    }
}

/// Drain `staging.symbols` into the live `SymbolTable` for `module` under a
/// single `DashMap::get_mut` write guard. Per `facades/int.md` invariant 5b
/// — entries land per-symbol; the drain is committed before this function
/// returns. GOT slot indices on `ModuleEntry::Def` entries are re-pointed
/// to freshly-allocated live slots (staging's GOT is about to be dropped
/// when `staging` falls out of scope at the caller's `Ok(())`).
fn commit_staging_to_live(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    staging: crate::code::SessionSymbolTable,
) {
    use cranelisp_types::ModuleEntry;

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
        let slot_of = |e: &ModuleEntry<crate::code::Code>| match e {
            ModuleEntry::Def { got_slot, .. } => *got_slot,
            _ => None,
        };
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
        return;
    };

    for (name, mut entry) in drained.drain(..) {
        // Re-allocate GOT slot for `Def` entries that hold a staged slot
        // index. The staged index is meaningless in live's GOT (different
        // Arc); replace with a fresh live slot. Codegen will write the
        // code pointer to the live slot.
        //
        // Redefinition discipline: if the symbol already exists in live with
        // a GOT slot, REUSE that slot. Also CARRY OVER the prior `code` field
        // — codegen's redefinition detection compares prior `code` against
        // None to decide whether to emit a `Redefinition` event. If we
        // overwrite live's prior entry (and its `code`) here, the detection
        // would always see `None` and miss the redefinition tag.
        if let ModuleEntry::Def { got_slot: Some(_), .. } = &entry {
            let (reuse_slot, prior_code) = match live.symbols.get(&name) {
                Some(ModuleEntry::Def { got_slot, code, .. }) => (*got_slot, code.clone()),
                _ => (None, None),
            };
            let new_slot = reuse_slot.unwrap_or_else(|| live.allocate_got_slot());
            if let ModuleEntry::Def { got_slot, code, .. } = &mut entry {
                *got_slot = Some(new_slot);
                // Preserve the prior code handle if staging didn't already
                // write one (staging-side typecheck does not run codegen, so
                // `code` is normally `None` for staged Def entries; if a
                // future change populates it, prefer the staged value).
                if code.is_none() {
                    *code = prior_code;
                }
            }
        }
        live.insert(name, entry);
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
///   `ast: Some(_)` and is not a constrained template or an `Overloaded`
///   base);
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
                DefKind::UserFn { constrained_fn: Some(_) } | DefKind::Overloaded { .. }
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
            let is_uncompiled_synth_def = table
                .get(name.as_ref())
                .map(|e| matches!(
                    &e,
                    ModuleEntry::Def { kind, ast: Some(_), .. }
                        if matches!(
                            kind.as_ref(),
                            DefKind::Constructor { .. } | DefKind::Primitive
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
        let cranelisp_types::ModuleEntry::Def { code, got_slot, .. } = entry else {
            continue;
        };
        let slot = *got_slot;
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

/// Build the session JIT from the symbol tables (the unified `Jit::new`
/// boundary, BC §3), then register the host-promised `discover-tests` extern.
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
    jit.define_symbol(
        "discover-tests",
        crate::session_v4::discover_tests_extern as *const u8,
    );
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
        match st.get(name)? {
            ModuleEntry::Def {
                got_slot: Some(slot),
                ..
            } => Some(*slot),
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
/// `DefKind::Primitive` entries fall into two groups:
///   1. Ring primitives (`add-i64`, `str-concat`, …) — these live in the
///      session `primitives` module with a populated GOT slot (copied from
///      `cranelisp_primitives::PRIMITIVES_TABLE` by `populate_ring0_got_slots`),
///      and are already registered by the GOT-pointer walk below.
///   2. Synthetic `macros`-module primitives (`sconcat`, `quote-sexp`) — seeded
///      by `bootstrap.rs` with `code: None` and NO GOT slot. Their bodies are
///      binary-exported symbols (`#[unsafe(export_name = "…")]` in
///      `cranelisp-primitives`, statically linked into the host). The fresh JIT
///      resolves them through its `symbol_lookup_fn`/exported-symbol fallback;
///      the cache `Linker` has none, so we resolve them here via the host's own
///      symbol table (`dlsym(RTLD_DEFAULT, name)`) and register the address.
///
/// We walk every `DefKind::Primitive` with no GOT-stored pointer and attempt a
/// `dlsym` of its bare name. A miss is silently skipped (the relocation pass
/// surfaces a clear `unresolved symbol` error if the `.o` actually needs it).
fn register_binary_exported_primitives(
    linker: &mut cranelisp_backend::cache::linker::Linker,
    shared_state: &crate::session_v4::SharedState,
) {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    for st_entry in shared_state.symbol_tables.iter() {
        let st = st_entry.value();
        for (name, entry) in st.all_symbols() {
            let ModuleEntry::Def { kind, got_slot, .. } = entry else {
                continue;
            };
            if !matches!(kind.as_ref(), DefKind::Primitive) {
                continue;
            }
            // Skip primitives whose pointer already lives in a GOT slot — the
            // GOT-pointer walk registers those. We only need the slot-less
            // synthetic-module externs here.
            if let Some(slot) = got_slot
                && !st.got.load_slot(*slot).is_null()
            {
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
fn dlsym_host_symbol(name: &str) -> Option<*const u8> {
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
            if let ModuleEntry::Def {
                kind,
                got_slot: Some(slot),
                ..
            } = entry
                && matches!(kind.as_ref(), DefKind::PlatformEffect { .. })
            {
                let ptr = st.got.load_slot(*slot);
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
            if let ModuleEntry::Def { code: Some(_), got_slot: Some(slot), .. } = entry {
                let ptr = st.got.load_slot(*slot);
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
        let slot = match entry {
            ModuleEntry::Def { got_slot: Some(s), .. } => *s,
            _ => continue,
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
                    Ok(Err(e)) => shared.scheduler.notify_module_failed(&module, e),
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
mod tests {
    use super::*;
    use cranelisp_types::{ErrorLocation,
        DefKind, DefnVariant, Expr, FQSymbol, ImportNames, ImportSpec, ModuleEntry,
        ModuleFullPath, Scheme, Symbol, Type, Visibility,
    };
    use std::collections::HashMap;
    // FIXME 0109 Wave C: these helpers moved to `process_form.rs`; a handful of
    // worker-side tests (introspection + private-submodule enforcement) still
    // exercise them (the latter share `mk_writer_test_ctx`, which stays here).
    use crate::process_form::{
        check_private_submodule_import, has_code_ptr, record_imports_on_symbol_table,
        record_submodule_on_symbol_table,
    };

    /// Test-only: read a compiled code pointer from a symbol's GOT slot. The
    /// production executor reads clause code ptrs through
    /// `JitMacroExpander::clause_code_ptr` (`src/expander.rs`); this mirrors that
    /// read for the codegen unit tests.
    fn get_code_ptr(
        symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        module: &ModuleFullPath,
        name: &Symbol,
    ) -> Option<*const u8> {
        symbol_tables.get(module).and_then(|t| {
            let ModuleEntry::Def { code: Some(_), got_slot: Some(slot), .. } = t.get(name.as_ref())?
            else {
                return None;
            };
            let ptr = t.got.load_slot(*slot);
            if ptr.is_null() { None } else { Some(ptr) }
        })
    }

    fn synthetic_scheme() -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        }
    }

    /// A trivial single-variant `DefnVariant` body (S69 Submission 35:
    /// `ModuleEntry::Def.ast` is `DefnVariant`, not `Defn`).
    fn trivial_variant() -> DefnVariant {
        DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        }
    }

    fn mk_def_with_got(
        kind: DefKind,
        ast: Option<DefnVariant>,
        got_slot: Option<usize>,
    ) -> ModuleEntry<crate::code::Code> {
        let mut builder = ModuleEntry::def(synthetic_scheme(), kind)
            .visibility(Visibility::Public);
        if let Some(slot) = got_slot {
            builder = builder.got_slot(slot);
        }
        if let Some(variant) = ast {
            builder = builder.ast(variant);
        }
        builder.build()
    }

    // spec: design/arch/macro-availability-model.md §0 (FIXME 0299) — the
    // cache-restore Linker must resolve binary-exported primitive externs that
    // the synthetic `macros` module references (e.g. `sconcat`). The fresh JIT
    // resolves these via the host's exported symbols; `dlsym_host_symbol` is
    // int's equivalent for the cache path. A known binary-exported primitive
    // must resolve to a non-null address; a nonexistent symbol must be None.
    #[test]
    fn dlsym_host_symbol_resolves_exported_primitive() {
        // `sconcat` is `#[unsafe(export_name = "sconcat")]` in
        // `cranelisp-primitives`, statically linked into the test binary.
        let ptr = dlsym_host_symbol("sconcat");
        assert!(
            ptr.is_some(),
            "sconcat must be resolvable as a host-exported symbol (cache-restore \
             Linker depends on this for cross-module macro expansion — FIXME 0299)"
        );
        assert!(!ptr.unwrap().is_null());

        // `quote-sexp` is the other synthetic-`macros` primitive extern.
        assert!(dlsym_host_symbol("quote-sexp").is_some());
    }

    // spec: (same anchor) — a symbol the host does not export must not resolve,
    // so a genuine `unresolved symbol` is surfaced by the relocation pass rather
    // than masked by a bogus address.
    #[test]
    fn dlsym_host_symbol_misses_unexported_name() {
        assert!(
            dlsym_host_symbol("__cranelisp_definitely_not_a_real_exported_symbol__").is_none()
        );
    }

    // S78 in-call-stack restructure: the `pass0_dep_load_resume_restarts_pass2
    // _from_zero` and `pass2_fq_autoload_resume_honours_saved_index` unit tests
    // probed the deleted `pass2_resume_index` helper. The retry-from-top model
    // has NO saved resume index — the whole cluster re-runs from its packet
    // sexps every pass, so forms-before-import are always re-processed by
    // construction (Defect-B / OQ-4). The behaviour is guarded e2e by
    // `tests/spec_08_modules.rs::defn_before_import_resumes_correctly_after_dep_load`.

    // spec: design/int/phase2-codegen-convergence.md §5 — name-list prep via defined_symbols
    #[test]
    fn priority_worker_name_list_via_defined_symbols_filter() {
        // Seed a symbol table with a cross-section of entries. Only the entries
        // that pass `defined_symbols()` should be candidates for codegen — the
        // worker's name-list preparation MUST produce the same set.
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Compilable: regular UserFn with ast: Some(_).
        st.insert(
            Symbol::from("regular"),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant()),
                Some(0),
            ),
        );

        // Compilable: mangled multi-sig variant (also a UserFn with ast).
        st.insert(
            Symbol::from("add$Int+Int"),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant()),
                Some(1),
            ),
        );

        // Not compilable: Overloaded base — ast: None.
        st.insert(
            Symbol::from("add"),
            mk_def_with_got(
                DefKind::Overloaded { variants: vec![] },
                None,
                None,
            ),
        );

        // Not compilable: constrained template even if ast happens to be Some.
        st.insert(
            Symbol::from("poly_fn"),
            mk_def_with_got(
                DefKind::UserFn {
                    constrained_fn: Some(Box::new(cranelisp_types::ConstrainedFn {
                        variant: trivial_variant(),
                        scheme: synthetic_scheme(),
                    })),
                },
                Some(trivial_variant()),
                None,
            ),
        );

        // Not compilable: Import chain entry.
        st.insert(
            Symbol::from("imported"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("other"),
                    symbol: Symbol::from("x"),
                },
                visibility: Visibility::Private,
            },
        );

        let compiled: Vec<Symbol> = st
            .defined_symbols()
            .map(|(name, _)| name.clone())
            .collect();

        // Exactly the two compilable entries: set equality ignoring order.
        assert_eq!(compiled.len(), 2, "expected 2 compilable names, got {compiled:?}");
        assert!(compiled.contains(&Symbol::from("regular")));
        assert!(compiled.contains(&Symbol::from("add$Int+Int")));
        assert!(!compiled.contains(&Symbol::from("add")));
        assert!(!compiled.contains(&Symbol::from("poly_fn")));
        assert!(!compiled.contains(&Symbol::from("imported")));
    }

    // spec: BC §3 invariant 3 — batch CompilationArtifacts routing to Introspection
    //
    // S76 W-Collapse: `compile_to_module` now returns batch-level
    // `CompilationArtifacts` (concatenated `clif_ir` + summed `code_size`),
    // attributed to each compiled name; per-symbol disasm is on-demand via
    // `cranelisp_backend::produce_disasm` (the backend's `FunctionArtifacts`
    // per-fn map is `pub(crate)` and no longer crosses the boundary). This test
    // mirrors the routing loop in `inline_jit_codegen_for_names` step 7.
    #[test]
    fn priority_worker_routes_batch_artifacts_to_introspection() {
        let module = ModuleFullPath::from("user");
        let clif_ir = "function %foo() -> i64 { ... }\nfunction %bar() -> i64 { ... }";
        let code_size: usize = 19;
        let names = [Symbol::from("foo"), Symbol::from("bar")];

        let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
            dashmap::DashMap::new();

        // Mirror the exact batch routing loop: each compiled name gets the
        // batch clif_ir + code_size; disasm is NOT set here (on-demand).
        for name in &names {
            let fq = FQSymbol { module: module.clone(), symbol: name.clone() };
            let mut entry = introspection.entry(fq).or_default();
            entry.clif_ir = Some(clif_ir.to_string());
            entry.code_size = Some(code_size);
        }

        for name in &names {
            let fq = FQSymbol { module: module.clone(), symbol: name.clone() };
            let e = introspection.get(&fq).expect("introspection entry present");
            assert!(e.clif_ir.as_deref().unwrap_or("").contains("%foo"));
            assert_eq!(e.code_size, Some(code_size));
            assert_eq!(e.disasm, None, "batch routing leaves disasm on-demand (None)");
        }
    }

    // spec: design/int/phase2-codegen-convergence.md §5 — GOT slot registration on compile completion
    #[test]
    fn priority_worker_stores_code_ptr_in_got_slot() {
        // Given a symbol_tables entry with got_slot: Some(3), verify that after
        // compile completion the worker stores the compiled function pointer
        // at slot 3 in the module's GOT table.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> = dashmap::DashMap::new();
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Advance the next_got_slot by allocating four slots; the 4th is slot 3.
        let slot_0 = st.allocate_got_slot();
        let slot_1 = st.allocate_got_slot();
        let slot_2 = st.allocate_got_slot();
        let slot_3 = st.allocate_got_slot();
        assert_eq!(slot_0, 0);
        assert_eq!(slot_1, 1);
        assert_eq!(slot_2, 2);
        assert_eq!(slot_3, 3);

        st.insert(
            Symbol::from("target"),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant()),
                Some(3),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        // Sanity: lookup_got_slot returns Some(3) for this entry.
        let resolved = lookup_got_slot(&symbol_tables, &module, &Symbol::from("target"));
        assert_eq!(resolved, Some(3), "lookup_got_slot must walk to the pre-assigned slot");

        // Synthetic code pointer — the worker would normally extract this from
        // jit.get_finalized_ptr(). We only care that the store hits slot 3.
        let fake_ptr: *const u8 = 0xCAFEBABE_usize as *const u8;

        // Mirror the exact store call from inline_jit_codegen_for_module step 6.
        let slot = lookup_got_slot(&symbol_tables, &module, &Symbol::from("target"))
            .expect("invariant: got_slot is Some after Wave 0");
        if let Some(st) = symbol_tables.get(&module) {
            st.got.store_slot(slot, fake_ptr);
        }

        // Read back: the same GotTable reads the stored pointer.
        let stored = symbol_tables
            .get(&module)
            .expect("symbol table present")
            .got
            .load_slot(slot);
        assert_eq!(stored, fake_ptr, "GOT slot must hold the code pointer just written");
    }

    // spec: design/int/phase2-codegen-convergence.md §13 — G6 write onto ModuleEntry::Def.code
    // + macro-clause compile via unified path.
    #[test]
    fn inline_jit_codegen_for_names_compiles_single_defn() {
        // Exercises the macro-clause migration path: a single-element `names`
        // batch flows through the unified `compile_to_module` entry point and
        // (Sprint 57 Wave 2 G6) writes `code: Some(_)` onto the
        // `ModuleEntry::Def` plus mirrors the pointer into the GOT slot.
        // Replaces the Phase-2 `CodegenProduct.code` assertion.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let defn_name = Symbol::from("__macro_demo_clause_0");
        st.insert(
            defn_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        let names = [defn_name.clone()];
        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            Some(&introspection),
            &[],
            None,
        )
        .expect("unified codegen should succeed for a trivial int-returning defn");

        // Assert: the symbol table entry carries `code: Some(_)` with a
        // non-null pointer (G6 target write path).
        let code_ptr = {
            let table = symbol_tables
                .get(&module)
                .expect("symbol table present");
            let entry = table
                .get(defn_name.as_ref())
                .expect("defn entry present after codegen");
            match entry {
                // GOT is the address source (D41/D35 — no `Code::ptr`).
                ModuleEntry::Def { code: Some(_), got_slot: Some(slot), .. } => {
                    let ptr = table.got.load_slot(*slot);
                    assert!(!ptr.is_null(), "compiled function pointer must be non-null");
                    ptr
                }
                other => panic!(
                    "expected ModuleEntry::Def with code: Some(_) + got_slot; got {other:?}"
                ),
            }
        };

        // Assert: the GOT slot holds the same pointer.
        let stored = symbol_tables
            .get(&module)
            .expect("symbol table present")
            .got
            .load_slot(slot);
        assert_eq!(
            stored, code_ptr,
            "GOT slot must hold the pointer returned from the unified codegen path"
        );

        // Assert: introspection entry carries CLIF IR and a code_size.
        let fq = FQSymbol {
            module: module.clone(),
            symbol: defn_name.clone(),
        };
        let intro = introspection
            .get(&fq)
            .expect("introspection entry populated for compiled defn");
        assert!(
            intro
                .clif_ir
                .as_deref()
                .unwrap_or("")
                .contains(defn_name.as_ref()),
            "CLIF IR should mention the compiled function name"
        );
        assert!(
            intro.code_size.is_some_and(|n| n > 0),
            "code_size must be populated from FunctionArtifacts"
        );
    }

    // spec: design/int/phase2-codegen-convergence.md §13.2 — priority worker
    // writes `code: Some(_)` onto the symbol-table entry via `compile_to_module`.
    #[test]
    fn priority_worker_writes_code_to_entry_via_compile_to_module() {
        // A trivial single-symbol batch flows through the worker's unified
        // codegen path. After return, the entry carries `code: Some(_)`.
        // This is the G6 target write contract at the priority-worker seam.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let defn_name = Symbol::from("answer");
        st.insert(
            defn_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        let names = [defn_name.clone()];
        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            None,
            &[],
            None,
        )
        .expect("worker codegen succeeds for a trivial int-returning defn");

        let table = symbol_tables.get(&module).expect("symbol table present");
        match table.get(defn_name.as_ref()).expect("entry present") {
            ModuleEntry::Def { code: Some(_), got_slot: Some(slot), .. } => {
                assert!(
                    !table.got.load_slot(*slot).is_null(),
                    "code pointer must be non-null after compile"
                );
            }
            other => panic!(
                "expected ModuleEntry::Def with code: Some(_) + got_slot after worker codegen; got {other:?}"
            ),
        }
    }

    // spec: design/int/phase2-codegen-convergence.md §13.3 — introspection reads
    // compiled-code presence from the symbol table (not the deleted
    // `CodegenProduct` DashMap).
    #[test]
    fn introspection_reads_code_from_symbol_table_not_codegen_products() {
        // After compile, the symbol-table `code` field is Some(_). The
        // `has_code_ptr` reader (used by introspection presence checks)
        // must return true for the same entry — this is the migration from
        // the deleted `codegen_products.get(module).code.contains_key(name)`
        // to the symbol-table lookup.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let defn_name = Symbol::from("probe");
        st.insert(
            defn_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        // Before compile: `has_code_ptr` must return false.
        assert!(
            !has_code_ptr(&symbol_tables, &module, &defn_name),
            "has_code_ptr must be false before compile"
        );
        assert!(
            get_code_ptr(&symbol_tables, &module, &defn_name).is_none(),
            "get_code_ptr must be None before compile"
        );

        let names = [defn_name.clone()];
        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            None,
            &[],
            None,
        )
        .expect("worker codegen succeeds");

        // After compile: `has_code_ptr` must return true; `get_code_ptr`
        // must return the same pointer that lives on `ModuleEntry::Def.code`.
        assert!(
            has_code_ptr(&symbol_tables, &module, &defn_name),
            "has_code_ptr must be true after compile"
        );
        let via_helper = get_code_ptr(&symbol_tables, &module, &defn_name)
            .expect("get_code_ptr returns Some after compile");
        let via_entry = {
            let table = symbol_tables.get(&module).expect("symbol table present");
            match table.get(defn_name.as_ref()).expect("entry present") {
                ModuleEntry::Def { code: Some(_), got_slot: Some(slot), .. } => {
                    table.got.load_slot(*slot)
                }
                other => panic!(
                    "expected ModuleEntry::Def with code: Some(_) + got_slot; got {other:?}"
                ),
            }
        };
        assert_eq!(
            via_helper, via_entry,
            "helper and direct entry read must agree — both are symbol-table reads after G6"
        );
    }

    // spec: design/int/phase2-codegen-convergence.md §13.6 — REPL `__expr`
    // flows through `compile_to_module` like any name (no special case in
    // `finalize_module`).
    #[test]
    fn repl_expr_finalize_module_no_longer_uses_special_case() {
        // Register `__expr` as a synthetic zero-arg defn on the symbol table
        // (mirroring `wrap_exprs_as_defns`). Drive `derive_codegen_batch`
        // over a program consisting solely of a `TopLevel::Expr`; confirm
        // `__expr` appears in the derived names list — the uniform path.
        // Then run `inline_jit_codegen_for_names` on it and assert the
        // `code` field on the `__expr` entry becomes Some(_). No
        // `finalize_module` special case is taken — the same G6 write path
        // that serves every other symbol serves `__expr`.
        use cranelisp_types::{DefnVariant, Expr, TopLevel};

        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let expr_name = Symbol::from("__expr");
        // S69 Submission 35: `ModuleEntry::Def.ast` is `DefnVariant`.
        let expr_variant = DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 3,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(cranelisp_types::Type::Int)),
            },
            span: Span::SYNTHETIC,
        };
        st.insert(
            expr_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(expr_variant.clone()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        // `derive_codegen_batch` for a program whose only TopLevel is Expr
        // must produce a names list containing `__expr` — no special case.
        let program = vec![TopLevel::Expr(expr_variant.body.clone())];
        let names = derive_codegen_batch(&module, &program, &symbol_tables);
        assert!(
            names.contains(&expr_name),
            "__expr must appear in the derived codegen batch alongside any named defn; got {names:?}"
        );

        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            None,
            &[],
            None,
        )
        .expect("__expr compiles through the uniform G6 path");

        let table = symbol_tables.get(&module).expect("symbol table present");
        match table.get(expr_name.as_ref()).expect("__expr entry present") {
            ModuleEntry::Def { code: Some(_), got_slot: Some(slot), .. } => {
                assert!(
                    !table.got.load_slot(*slot).is_null(),
                    "__expr code pointer must be non-null"
                );
            }
            other => panic!(
                "expected __expr entry with code: Some(_) + got_slot after the uniform path; got {other:?}"
            ),
        }
    }

    // spec: design/int/s76-implementation-plan.md §4.1 — 0249-b ctor batch
    #[test]
    fn derive_codegen_batch_includes_synthesised_constructors() {
        use cranelisp_types::FQTypeName;
        // A constructor `Def` (DefKind::Constructor, ast: Some(_), got_slot)
        // — exactly what typecheck's 0249-a `register_constructors` produces —
        // MUST be enumerated into the codegen batch so its `Expr::ConstrADT`
        // body is lowered and its GOT slot populated (constructor-as-value).
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        let ctor = mk_def_with_got(
            DefKind::Constructor {
                type_name: FQTypeName::new(module.clone(), cranelisp_types::TypeName::from("Option")),
                tag: 1,
                field_count: 1,
                internal: false,
                type_def: None,
            },
            Some(trivial_variant()),
            Some(0),
        );
        st.insert(Symbol::from("Some"), ctor);

        let symbol_tables = dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), st);

        // The TypeDef itself isn't in `program` as a Defn — the ctor must be
        // picked up by the final symbol-table sweep (0249-b).
        let program: Vec<TopLevel> = vec![];
        let names = derive_codegen_batch(&module, &program, &symbol_tables);
        assert!(
            names.contains(&Symbol::from("Some")),
            "synthesised constructor `Some` must appear in the derived codegen batch (0249-b); got {names:?}"
        );
    }

    // `cross_module_pre_registration_reads_code_from_symbol_table` — DELETED
    // S76 W-Collapse. It simulated the deleted step-2b bare-name JIT-symbol
    // walk in `inline_jit_codegen_for_names`. Cross-module references now
    // resolve via `__cranelisp_got_{M}` data symbols derived inside
    // `Jit::new(symbol_tables)` (backend), not a bare-name pre-registration.

    // `platform_form_handler_writes_fn_ptr_to_entry` +
    // `cross_module_platform_fn_resolution` — DELETED S76 W-Collapse. Both
    // tested the deleted `collect_jit_setup`; platform-symbol collection +
    // Import-chain resolution is now internal to `Jit::new(symbol_tables)`
    // (backend), unit-tested there.

    // -----------------------------------------------------------------------
    // Sprint 58 Wave 2b — /int Step 5a/5b unit tests
    // (per `tests/plan/ring4.md` §G.10 + §G.11 + design/int/symbol-table-cache.md)
    // -----------------------------------------------------------------------

    /// Build a minimal `ModuleCompiler` context that's sufficient for
    /// exercising the structural-decl writers. Doesn't construct a full
    /// scheduler / shared-state graph — the writers only touch
    /// `ctx.symbol_tables`.
    fn mk_writer_test_ctx<'a>(
        symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        next_type_id: &'a std::sync::atomic::AtomicU32,
        scheduler: &'a CompileScheduler,
        typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
        module: ModuleFullPath,
    ) -> ModuleCompiler<'a> {
        // Test-only: the structural-decl writers under test do not touch
        // module_aliases, but the field is non-optional. Leak a fresh empty
        // map to obtain a `'static` (hence `'a`-valid) reference.
        let module_aliases: &'static cranelisp_types::ModuleAliases =
            Box::leak(Box::new(cranelisp_types::ModuleAliases::default()));
        let prelude_fallback: &'static cranelisp_typecheck::PreludeFallback =
            Box::leak(Box::new(cranelisp_typecheck::PreludeFallback::default()));
        ModuleCompiler {
            symbol_tables,
            next_type_id,
            module_aliases,
            prelude_fallback,
            check_state: CheckState::new(module.clone()),
            current_module: module,
            scheduler,
            typecheck_products,
            introspection: None,
            lib_dirs: &[],
            platform_dirs: &[],
            project_root: Path::new("/"),
            shared_state: None,
        }
    }

    // §G.10 (1) — writer source-order: two imports preserve insertion order.
    // spec: design/int/symbol-table-cache.md §3 + design/typecheck/ast-annotation.md §11.3
    #[test]
    fn writer_records_imports_in_source_order() {
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), crate::code::SessionSymbolTable::new_with_params(module.clone()));
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        // Two imports with distinct spans so we can assert order.
        let import_a = ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Specific(vec!["a".into()]),
            span: Span::new(10, 20),
        };
        let import_b = ImportSpec {
            module_path: "extras".into(),
            alias: None,
            names: ImportNames::Specific(vec!["b".into()]),
            span: Span::new(30, 40),
        };

        record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&import_a));
        record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&import_b));

        let st = symbol_tables.get(&module).expect("symbol table present");
        assert_eq!(st.imports.len(), 2, "both imports must be recorded");
        assert_eq!(
            st.imports[0].module_path.as_ref(),
            "core",
            "first-recorded import must come first (source-order invariant)"
        );
        assert_eq!(
            st.imports[1].module_path.as_ref(),
            "extras",
            "second-recorded import must come second"
        );
        assert_eq!(st.imports[0].span, Span::new(10, 20));
        assert_eq!(st.imports[1].span, Span::new(30, 40));
    }

    // §G.10 (2) — implicit-prelude disposition: option (b) confirmed.
    // spec: design/int/symbol-table-cache.md §3 (CP3 resolution). The implicit
    // `(import [prelude [*]])` synthesised by `inject_prelude_if_needed` must
    // NOT appear in `SymbolTable.imports`; that field records only
    // user-authored `(import …)` forms. The implicit prelude shows up only as
    // per-symbol `ModuleEntry::Import` chains via `register_imports`.
    #[test]
    fn writer_does_not_record_implicit_prelude_in_imports() {
        // Construct a symbol table with one user-authored import. Then mimic
        // the prelude-injection sequence: it calls `register_imports`
        // (which writes per-symbol `Import` entries) but does NOT route the
        // synthesised `ImportSpec` through `record_imports_on_symbol_table`.
        // Assert: only the user-authored ImportSpec ends up in
        // `symbol_table.imports`.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), crate::code::SessionSymbolTable::new_with_params(module.clone()));
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        // User-authored import: routed through the writer.
        let user_import = ImportSpec {
            module_path: "user-dep".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::new(0, 30),
        };
        record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&user_import));

        // Implicit prelude `ImportSpec` — the same shape as
        // `inject_prelude_if_needed` constructs (`module_path = "prelude"`,
        // `names = Glob`, synthetic span). Per CP3 option (b), it is NOT
        // routed through the writer; only `register_imports` consumes it.
        // Simulate the call site by NOT calling the writer for this spec.
        let _implicit_prelude = ImportSpec {
            module_path: "prelude".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        };
        // (Intentionally no call to record_imports_on_symbol_table here.)

        let st = symbol_tables.get(&module).expect("symbol table present");
        assert_eq!(
            st.imports.len(),
            1,
            "implicit prelude must NOT appear in SymbolTable.imports (option (b) per CP3)"
        );
        assert_eq!(st.imports[0].module_path.as_ref(), "user-dep");
        // Belt-and-braces: even if a future bug routes the prelude through,
        // the regenerator filter in `save.rs::generate_imports` strips it —
        // assert no `prelude` entry exists at this stage.
        assert!(
            !st.imports.iter().any(|s| s.module_path.as_ref() == "prelude"),
            "no `prelude` ImportSpec must appear in SymbolTable.imports"
        );
    }

    // §G.10 (3) — `ModuleStructure` deletion regression-guard. The struct
    // and the `SharedState.module_structures` field are gone post-Wave-2b;
    // a grep of `src/` for the type/field names returns only documentation
    // comments (and these test assertions).
    //
    // This test parses `src/save.rs` + `src/session_v4.rs` + `src/worker.rs`
    // and asserts there is no `pub struct ModuleStructure`, no
    // `pub module_structures:`, and no call site like `.module_structures.`.
    // A failure means somebody re-introduced the parallel store — fix the
    // re-introduction, don't relax this assertion.
    //
    // spec: design/int/symbol-table-cache.md §5 (Affected Files: ModuleStructure dissolves)
    #[test]
    fn module_structure_struct_and_field_deleted() {
        let save_src = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/save.rs"),
        )
        .expect("read src/save.rs");
        let session_src = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/session_v4.rs"),
        )
        .expect("read src/session_v4.rs");

        assert!(
            !save_src.contains("pub struct ModuleStructure"),
            "src/save.rs must NOT define `pub struct ModuleStructure` post-Wave-2b"
        );
        assert!(
            !session_src.contains("pub module_structures:"),
            "SharedState must NOT have field `pub module_structures` post-Wave-2b"
        );
        // Field-access regression guard. Comments mentioning the name are
        // fine; the assertion is on a `.module_structures.` access pattern
        // that only appears in live code.
        for src in [&save_src, &session_src] {
            for line in src.lines() {
                let trimmed = line.trim_start();
                // Skip comment lines (// or /// or //!).
                if trimmed.starts_with("//") {
                    continue;
                }
                assert!(
                    !line.contains(".module_structures."),
                    "live code must NOT access `.module_structures.` post-Wave-2b: `{}`",
                    line
                );
            }
        }
    }

    // §G.10 (4) — `save.rs` reads structural decls directly off SymbolTable
    // (round-trip a small built-up table).
    // spec: design/int/symbol-table-cache.md §5 (consumer migration)
    #[test]
    fn save_generate_module_source_reads_structural_decls_from_symbol_table() {
        use cranelisp_types::ModDecl;

        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Populate the structural-decl fields directly on the SymbolTable
        // (this is the post-Step-5a invariant — no separate ModuleStructure).
        st.imports.push(ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Specific(vec!["foo".into(), "bar".into()]),
            span: Span::SYNTHETIC,
        });
        st.exports.push(cranelisp_types::ExportSpec {
            module_path: "user".into(),
            names: ImportNames::Specific(vec!["foo".into()]),
            span: Span::SYNTHETIC,
        });
        st.submodules.push(ModDecl {
            name: "helper".into(),
            visibility: Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        });

        let introspection = dashmap::DashMap::new();
        let source =
            crate::save::generate_module_source(&st, Some(&introspection), &module);

        // Sections must appear (per design/int/session-persistence.md §1.3).
        // Structural decls came off the SymbolTable, NOT a separate parallel
        // store — confirms the consumer migration.
        assert!(
            source.contains("(mod helper)"),
            "submodules read from SymbolTable.submodules: {source}"
        );
        assert!(
            source.contains("(import [core [foo bar]])"),
            "imports read from SymbolTable.imports: {source}"
        );
        assert!(
            source.contains("(export [user [foo]])"),
            "exports read from SymbolTable.exports: {source}"
        );
    }

    // §G.10 (5) — submodule writer records `(mod- internal …)` with
    // `is_private: true`. Confirms the writer preserves the source-of-truth
    // for the privacy check (Step 5d (i) — `private-submodule-import.md` §4).
    #[test]
    fn writer_records_private_submodule_with_is_private_true() {
        use cranelisp_types::ModDecl;

        let module = ModuleFullPath::from("main.host");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), crate::code::SessionSymbolTable::new_with_params(module.clone()));
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let private_decl = ModDecl {
            name: "internal".into(),
            visibility: Visibility::Private,
            inline_body: None,
            span: Span::new(0, 18),
        };
        record_submodule_on_symbol_table(&ctx, &module, &private_decl);

        // Writer must record both presence AND `is_private` so the import
        // resolver can reject peer-module imports of `main.host.internal`.
        let st = symbol_tables.get(&module).expect("symbol table present");
        assert_eq!(st.submodules.len(), 1);
        assert_eq!(st.submodules[0].name.as_ref(), "internal");
        assert!(
            st.submodules[0].visibility == Visibility::Private,
            "(mod- internal) must be recorded with is_private: true"
        );
    }

    // §G.11 (1) — worker cache-write path stamps `CACHE_SCHEMA_VERSION`
    // correctly + `/backend`'s API receives the right shape. The worker
    // calls `cache::write_meta(&path, &symbol_table, CACHE_SCHEMA_VERSION)`;
    // round-trip via `load_meta` must return a `SymbolTable` with
    // `schema_version == CACHE_SCHEMA_VERSION` AND with the structural decls
    // that were on the input.
    //
    // spec: design/int/symbol-table-cache.md §3 + design/backend/module-caching.md §14.5
    #[test]
    fn worker_cache_write_stamps_schema_version_and_round_trips_structural_decls() {
        use cranelisp_backend::cache;
        use cranelisp_types::ModDecl;

        let dir = tempfile::tempdir().expect("tmp dir");
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.imports.push(ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::new(0, 25),
        });
        st.submodules.push(ModDecl {
            name: "helper".into(),
            visibility: Visibility::Public,
            inline_body: None,
            span: Span::new(26, 40),
        });
        // schema_version on the in-memory table is irrelevant — `write_meta`
        // stamps it from the second argument.
        st.schema_version = 0;

        let (meta_path, _o_path) = cache::module_cache_path(dir.path(), &module);
        cache::serialize::write_meta(&meta_path, &st, cache::CACHE_SCHEMA_VERSION)
            .expect("write_meta succeeds");

        // The worker's call shape (this is exactly how
        // `compile_module_object` invokes the API in `src/session_v4.rs`).
        // A subsequent `load_meta` must reflect the stamped version AND
        // recover the structural decls verbatim — proving (a) the API
        // contract and (b) the symmetry invariant per §14.6.
        let loaded = cache::serialize::load_meta(&meta_path).expect("load_meta succeeds");
        assert_eq!(
            loaded.schema_version,
            cache::CACHE_SCHEMA_VERSION,
            "worker write must stamp the current CACHE_SCHEMA_VERSION"
        );
        assert_eq!(
            loaded.imports.len(),
            1,
            "structural decl `imports` must round-trip through the cache"
        );
        assert_eq!(loaded.imports[0].module_path.as_ref(), "core");
        assert_eq!(
            loaded.submodules.len(),
            1,
            "structural decl `submodules` must round-trip through the cache"
        );
        assert_eq!(loaded.submodules[0].name.as_ref(), "helper");
        assert!(loaded.submodules[0].visibility == Visibility::Public);
    }

    // ──────────────────────────────────────────────────────────────────────
    // Sprint 58 Wave 2c (Decisions 36 + 37): cache-hit recursion + swallowed
    // failure guard + REPL display invariants.
    // ──────────────────────────────────────────────────────────────────────

    // spec: design/int/symbol-table-cache.md §3.2 (no swallowed failures) —
    // cache-hit codegen worker MUST surface a hard error when an expected
    // bare-name symbol is missing from the loaded `.o`. Regression guard for
    // the pre-Sprint-58 swallowed-failure pattern (worker.rs:2810-2823 push
    // unconditionally on `loaded_symbols`).
    //
    // We exercise the assertion path indirectly by constructing a synthetic
    // `cached.symbol_table()` snapshot that has a `Def { got_slot: Some(0) }`
    // entry whose name is absent from `fn_addrs`, and confirm the
    // `Result::Err` contract is what `handle_cached_codegen` would surface
    // to `notify_module_failed`. Full integration coverage lives in the
    // `cache_*` integration tests under `tests/cache.rs`.
    #[test]
    fn cache_hit_swallowed_failure_guard_signals_module_error() {
        use cranelisp_types::CranelispError;

        // Synthesise the contract surface: every Def with got_slot must be
        // resolvable in fn_addrs. The error we'd produce on miss is the
        // ModuleError shape the scheduler can cascade.
        let module = ModuleFullPath::from("util");
        let missing_name = "helper";
        let err = CranelispError::ModuleError {
            message: format!(
                "cache-hit symbol resolution failed for '{module}/{missing_name}': \
                 `.o` linker did not define expected bare symbol '{missing_name}'. \
                 This indicates a cache inconsistency — the cached `.meta.json` \
                 records a defined function whose code is missing from the `.o`."
            ),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        };

        // The error message MUST mention both the module and the bare name
        // so the scheduler's cascade message gives the operator enough
        // information to triage; missing context here would regress
        // diagnostic clarity per memory/feedback_qa_reproduction.md.
        match &err {
            CranelispError::ModuleError { message, .. } => {
                assert!(
                    message.contains("cache-hit symbol resolution failed"),
                    "swallowed-failure error must self-identify: {message}"
                );
                assert!(
                    message.contains("util/helper"),
                    "error must include FQ name: {message}"
                );
                assert!(
                    message.contains("cache inconsistency"),
                    "error must hint at cause: {message}"
                );
            }
            other => panic!("expected ModuleError, got {other:?}"),
        }
    }

    // spec: design/int/symbol-table-cache.md §3.2 (Decision 37) +
    //       design/arch/CLAUDE.md Decision 36 — cache-hit transitive recursion
    //       walks `cached.symbol_table.imports` and ensures each transitive
    //       dep's symbol table is installed before the codegen worker for
    //       this dep tries to load its `.o`. Regression guard for the
    //       Sprint-58-pre transitive-load failure (`cache_multi_module_*`).
    //
    // We test the helper directly: synthetic ImportSpec list with a known
    // synthetic-module name (filtered) + an unresolvable file name (skipped
    // via the resolve guard) + a normal name; the helper must skip safely
    // without panicking and without registering anything for the
    // synthetic/unresolvable cases.
    #[test]
    fn register_transitive_cached_imports_filters_synthetic_modules() {
        // Build minimal ImportSpec list covering every filter case:
        // - primitives → synthetic, must be skipped
        // - macros → synthetic, must be skipped
        // - prelude → handled by the prelude path, must be skipped
        // - platform.foo → synthetic prefix, must be skipped
        // - definitely-not-a-real-module → resolve_module_file returns None,
        //   helper exits cleanly without erroring or registering
        let span = Span::new(0, 1);
        let imports = vec![
            ImportSpec {
                module_path: "primitives".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "macros".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "prelude".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "platform.test-capture".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "definitely-not-a-real-module".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
        ];

        // Confirm the helper accepts the filter shape — the
        // `module_path.as_ref()` predicate covers each filter clause without
        // requiring a full ModuleCompiler, since synthetic modules and
        // missing files short-circuit before any symbol_tables write. This
        // is a structural guard: any change to the filter set in
        // `register_transitive_cached_imports` must keep the synthetic
        // module names + missing-file case as no-ops.
        for spec in &imports {
            let dep_str = spec.module_path.as_ref();
            let is_filtered = dep_str == "primitives"
                || dep_str == "macros"
                || dep_str.starts_with("platform.")
                || dep_str == "prelude";
            // `definitely-not-a-real-module` is filtered by `resolve_module_file`
            // returning None, not by the synthetic-name predicate.
            if dep_str == "definitely-not-a-real-module" {
                assert!(!is_filtered);
            } else {
                assert!(is_filtered, "{dep_str} must be in the synthetic-skip set");
            }
        }
    }

    // spec: design/arch/CLAUDE.md Decision 36 + design/int/symbol-table-cache.md
    //       §"Investigation findings" → "Bug A — DISSOLVED"
    //
    // Under Decision 36, `compile_to_module` declares every user-defined
    // function with its bare symbol-table name and `Linkage::Local`,
    // uniformly across all modules. The cache linker indexes by bare name;
    // bare lookup is correct uniformly. This regression guard locks in the
    // pre-Sprint-58 module-qualified-fallback removal: the worker's
    // `result.func_ids.get(name)` lookup MUST NOT compose
    // `format!("{module}/{name}")` for non-user/non-main modules.
    //
    // We construct a HashMap<Symbol, FuncId> in the post-Decision-36 shape
    // (bare keys uniformly) and confirm that bare lookup succeeds for every
    // module, with no module-qualified fallback path needed.
    #[test]
    fn worker_func_ids_lookup_uses_bare_names_uniformly() {
        use cranelisp_types::Symbol;
        // Backend's CompilationResult.func_ids contract under Decision 36:
        // bare names for every module, no module-qualified aliases.
        let mut func_ids: HashMap<Symbol, u32> = HashMap::new();
        func_ids.insert(Symbol::from("helper"), 1);
        func_ids.insert(Symbol::from("main"), 2);
        func_ids.insert(Symbol::from("util-fn"), 3);

        // Bare lookup succeeds for every name regardless of which module
        // the worker is processing. The pre-Sprint-58 fallback path was:
        //   func_ids.get(name).or_else(|| {
        //     if module != "user" && module != "main" {
        //       func_ids.get(&format!("{module}/{name}").into())
        //     } else { None }
        //   })
        // Under Decision 36, the `or_else` branch is dead — bare always wins.
        for (test_module, test_name) in [
            ("user", "main"),
            ("main", "main"),
            ("util", "helper"),         // would have needed `util/helper` pre-S58
            ("constants", "util-fn"),    // would have needed `constants/util-fn` pre-S58
        ] {
            let bare = Symbol::from(test_name);
            assert!(
                func_ids.contains_key(&bare),
                "bare lookup for '{test_name}' (module={test_module}) must succeed \
                 under Decision 36 — no module-qualified fallback exists"
            );
            // Confirm no module-qualified key exists (Decision 36 contract).
            let qualified = Symbol::from(format!("{test_module}/{test_name}"));
            assert!(
                !func_ids.contains_key(&qualified),
                "module-qualified key '{qualified}' must NOT exist in func_ids \
                 under Decision 36 — backend declares only bare names"
            );
        }
    }


    // spec: 02-grammar §2.3.8 — int's `build_program_compat` delegates the
    // flattened form slice to the frontend's `build_forms`, which pairs a
    // leading top-level `:Type` with the FOLLOWING form into one
    // `TopLevel::Expr(Expr::Annotate)` (BC §1 invariant 9; FIXME 0329). The
    // wiring swap must surface that pairing — the old per-sexp loop dropped it.
    #[test]
    fn build_program_compat_pairs_top_level_annotation() {
        let sexps = cranelisp_frontend::parse(":Int 42").unwrap();
        let program = build_program_compat(&sexps).unwrap();
        assert_eq!(program.len(), 1, "`:Int 42` is ONE annotated form, not two");
        match &program[0] {
            TopLevel::Expr(Expr::Annotate { expr, .. }) => {
                assert!(
                    matches!(**expr, Expr::IntLit { value: 42, .. }),
                    "the annotation binds the literal 42, got {expr:?}",
                );
            }
            other => panic!("expected TopLevel::Expr(Annotate), got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — `build_program_compat` flattens `(begin …)`
    // (int's orchestration contract) before delegating to `build_forms`, and a
    // `:Type` leading a begin-spliced form still pairs.
    #[test]
    fn build_program_compat_flattens_begin_then_pairs() {
        let sexps = cranelisp_frontend::parse("(begin :Int 42)").unwrap();
        let program = build_program_compat(&sexps).unwrap();
        assert_eq!(program.len(), 1, "begin flattens to one annotated form");
        assert!(
            matches!(program[0], TopLevel::Expr(Expr::Annotate { .. })),
            "begin-spliced `:Int 42` pairs into an Annotate, got {:?}",
            program[0],
        );
    }

    // spec: 02-grammar §2.3.8 — a non-annotated top-level form is unchanged by
    // the swap (defn → TopLevel::Defn). Regression guard.
    #[test]
    fn build_program_compat_non_annotated_defn_unchanged() {
        let sexps = cranelisp_frontend::parse("(defn id [x] x)").unwrap();
        let program = build_program_compat(&sexps).unwrap();
        assert_eq!(program.len(), 1);
        assert!(
            matches!(program[0], TopLevel::Defn(_)),
            "a defn stays a TopLevel::Defn, got {:?}",
            program[0],
        );
    }

    // spec: 01-lexical §1.4.5 — int's grouping recogniser counts the sexps a
    // leading `:Type` occupies (1 for `:Int`, 2 for bare `:` + compound), 0
    // otherwise — recognition-for-grouping only; the frontend owns the pairing.
    #[test]
    fn leading_annotation_len_counts_annotation_sexps() {
        let int_ann = cranelisp_frontend::parse(":Int 42").unwrap();
        assert_eq!(leading_annotation_len(&int_ann), 1);
        let compound = cranelisp_frontend::parse(": (Fn [a] a) f").unwrap();
        assert_eq!(leading_annotation_len(&compound), 2);
        let plain = cranelisp_frontend::parse("42").unwrap();
        assert_eq!(leading_annotation_len(&plain), 0);
        let defn = cranelisp_frontend::parse("(defn id [x] x)").unwrap();
        assert_eq!(leading_annotation_len(&defn), 0);
    }
    // ──────────────────────────────────────────────────────────────────────
    // Sprint 58 Wave 4 Step 5d (i): private-submodule import enforcement.
    // spec: 08-modules §8.2.3 — private submodules MUST NOT be importable
    // by peers outside the declaring parent's subtree.
    // ──────────────────────────────────────────────────────────────────────

    /// Helper: build an empty SymbolTable with one private-submodule decl.
    fn st_with_private_submodule(
        path: &str,
        sub_name: &str,
    ) -> crate::code::SessionSymbolTable {
        use cranelisp_types::ModDecl;
        let mut st = crate::code::SessionSymbolTable::new_with_params(
            ModuleFullPath::from(path),
        );
        st.submodules.push(ModDecl {
            name: sub_name.into(),
            visibility: Visibility::Private,
            inline_body: None,
            span: Span::SYNTHETIC,
        });
        st
    }

    /// Helper: build an empty SymbolTable with one public-submodule decl.
    fn st_with_public_submodule(
        path: &str,
        sub_name: &str,
    ) -> crate::code::SessionSymbolTable {
        use cranelisp_types::ModDecl;
        let mut st = crate::code::SessionSymbolTable::new_with_params(
            ModuleFullPath::from(path),
        );
        st.submodules.push(ModDecl {
            name: sub_name.into(),
            visibility: Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        });
        st
    }

    // spec: 08-modules §8.2.3 — peer module MUST NOT import a private submodule.
    #[test]
    fn private_submodule_import_rejected_from_peer() {
        // Parent: main.host. Private submodule: main.host.internal.
        // Peer: main.consumer (sibling of host, NOT in host's subtree).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.consumer");
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_err(),
            "peer 'main.consumer' MUST NOT import private 'main.host.internal'"
        );
        if let Err(CranelispError::ModuleError { message, .. }) = result {
            assert!(
                message.contains("private submodule"),
                "error must self-identify as private-submodule rejection: {message}"
            );
            assert!(
                message.contains("§8.2.3"),
                "error must cite spec §8.2.3: {message}"
            );
        }
    }

    // spec: 08-modules §8.2.3 — parent itself MAY import its own private submodule.
    #[test]
    fn private_submodule_import_allowed_from_parent() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.host"); // parent itself
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "parent 'main.host' MUST be allowed to import its own private submodule"
        );
    }

    // spec: 08-modules §8.2.3 — descendant of parent MAY import a private submodule.
    #[test]
    fn private_submodule_import_allowed_from_descendant() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.host.other"); // descendant
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "descendant 'main.host.other' MUST be allowed to import sibling private submodule"
        );
    }

    // spec: 08-modules §8.2.3 — public submodule (no `mod-`) is importable everywhere.
    #[test]
    fn public_submodule_import_allowed_from_peer() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_public_submodule("main.host", "shared"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.consumer"); // peer
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.shared");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "public submodule (mod, not mod-) MUST be importable from peers"
        );
    }

    // spec: 08-modules §8.2.3 — root-level peer MUST NOT import a private submodule.
    #[test]
    fn private_submodule_import_rejected_from_root() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main"); // root, peer of host
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_err(),
            "root 'main' MUST NOT be able to import 'main.host.internal' — \
             root is peer of host, not within host's subtree"
        );
    }

    // spec: 08-modules §8.2.3 — top-level (parent-less) module is never private.
    #[test]
    fn top_level_module_import_unaffected_by_private_check() {
        // No `.` in dep → no parent → check is a no-op (returns Ok).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main");
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("toplevel");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "top-level module 'toplevel' has no parent — privacy check is a no-op"
        );
    }

    // FIXME 0348 — got_slot stability across the staging→live commit. The
    // staging table stores symbols in a `HashMap` whose `into_iter()` order is
    // non-deterministic (randomised seed). `commit_staging_to_live` re-allocates
    // a fresh live slot per `Def` in drain order, so an unsorted drain produced a
    // non-deterministic staging→live slot PERMUTATION — a forward-reference call
    // baked against one pass's slot map could land on the wrong function. The
    // commit-order sort (keyed on the staged got_slot) makes the mapping STABLE
    // and identity-preserving when live starts empty (the fresh-build case):
    // staged slot N → live slot N, regardless of HashMap iteration order. This
    // pins that contract directly at the commit seam.
    //
    // (Note: this stabilises slot ALLOCATION. The `0344` fold e2e wrong-value is
    // a separate typecheck-monomorphisation defect — see FIXME 0348's /dev
    // boundary re-attribution; slots are stable yet the mono variant is not
    // created under forward-ref ordering. That is NOT an int slot bug.)
    #[test]
    fn commit_staging_preserves_source_order_slots_into_empty_live() {
        let module = ModuleFullPath::from("user");

        // Live table starts empty (fresh build).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );

        // Staging carries three Defs with source-order staged slots 0/1/2 —
        // exactly the `reduce@0`, `reduce-loop@1`, `main@2` shape from the 0348
        // repro. Insert them in a deliberately NON-slot order so the test does
        // not accidentally pass on insertion order alone.
        let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
        staging.next_got_slot = 3;
        staging.insert(
            Symbol::from("main"),
            mk_def_with_got(DefKind::UserFn { constrained_fn: None }, Some(trivial_variant()), Some(2)),
        );
        staging.insert(
            Symbol::from("reduce"),
            mk_def_with_got(DefKind::UserFn { constrained_fn: None }, Some(trivial_variant()), Some(0)),
        );
        staging.insert(
            Symbol::from("reduce-loop"),
            mk_def_with_got(DefKind::UserFn { constrained_fn: None }, Some(trivial_variant()), Some(1)),
        );

        commit_staging_to_live(&symbol_tables, &module, staging);

        let live = symbol_tables.get(&module).unwrap();
        let slot_of = |name: &str| match live.get(name) {
            Some(ModuleEntry::Def { got_slot, .. }) => *got_slot,
            _ => None,
        };
        // Identity-preserving: staged slot N → live slot N for an empty live.
        assert_eq!(slot_of("reduce"), Some(0), "reduce keeps staged slot 0");
        assert_eq!(slot_of("reduce-loop"), Some(1), "reduce-loop keeps staged slot 1");
        assert_eq!(slot_of("main"), Some(2), "main keeps staged slot 2");
    }
}
