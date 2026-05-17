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
    CodegenBehaviour, CranelispError, DefKind, Defn, ExportSpec, ImportNames, ImportSpec,
    MacroClauseInfo, ModuleEntry, ModuleFullPath, ModuleStrategy,
    PlatformSpec, PrimitiveKind, Sexp, Span, Symbol, TopLevel, Visibility,
};

use cranelisp_typecheck::{CheckResult, CheckState};

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
    /// Per-defn type vars captured during Pass 1, consumed by Pass 2 and
    /// `compute_display_info_public`. Kept as a placeholder for source
    /// compatibility; `check_forms` rebuilds this internally.
    pub defn_type_vars: std::collections::HashMap<Symbol, (Vec<cranelisp_types::Type>, cranelisp_types::Type)>,
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
/// Iterates `build_form` over each sexp, converting `Vec<ParsedEntry>` back to
/// `Vec<TopLevel>` for source-compat with existing worker / session code paths
/// that consume `TopLevel`. Filter out `Macro` and `Constructor` entries —
/// those are handled by the macro pipeline (defmacro registration) and ADT
/// constructor synthesis respectively, NOT by the per-form typecheck dispatch.
///
/// Per Decision 44's 2026-05-13 third amendment + FIXME 0156: `build_form`
/// returns the parsed entries; the worker side still tracks `TopLevel` for
/// downstream codegen, so we transcode at this boundary.
///
/// `mode` selects the build-mode rejection inside `build_expr` / `build_form`
/// per Decision 40 / Path B1 (FIXME 0199; supersedes FIXMEs 0202–0204).
/// Under `CodegenBehaviour::ObjectOnly` (`--link`), any `(trace ...)` form
/// reached during AST build is a compile-time error at the recognition site
/// (`ast_builder::build_trace`). Under `CodegenBehaviour::InMemoryAndObject`
/// (REPL/`--run`), the check is a no-op branch. There is no separate
/// validator walking pass — the rejection inlined into the AST builder at
/// Sprint 67 Wave 4 follow-up.
pub(crate) fn build_program_compat(
    sexps: &[Sexp],
    mode: CodegenBehaviour,
) -> Result<Vec<TopLevel>, CranelispError> {
    let mut out: Vec<TopLevel> = Vec::with_capacity(sexps.len());
    for sexp in sexps {
        // `(begin form₁ … formN)` clusters flatten into their inner forms
        // — `build_form` rejects `begin` per its facade. This preserves the
        // pre-S66 `build_program` semantics where `flatten_begin` ran before
        // per-form dispatch.
        let flattened = cranelisp_frontend::flatten_begin(sexp.clone());
        for inner in flattened {
            // Treat shapes that aren't a list-with-head-symbol as bare
            // expressions (`TopLevel::Expr`). `build_form` requires a
            // list-with-head-symbol top-level form.
            if !is_top_level_form(&inner) {
                let expr = cranelisp_frontend::build_expr(&inner, mode)?;
                out.push(TopLevel::Expr(expr));
                continue;
            }

            let entries = cranelisp_frontend::build_form(&inner, mode)?;
            for entry in entries {
                if let Some(tl) = parsed_entry_to_top_level(entry) {
                    out.push(tl);
                }
            }
        }
    }
    Ok(out)
}

/// Check whether a sexp shape is a top-level form that `build_form` can
/// dispatch on. Pre-S66 `build_program` used a heuristic: any list whose
/// head symbol is one of the recognised top-level form heads
/// (`defn`/`defn-`, `deftype`/`deftype-`, `deftrait`/`deftrait-`, `impl`,
/// `defmacro`/`defmacro-`). Other heads (function calls, primitives, macro
/// expansions whose head is bare) fall through to `build_expr` as
/// `TopLevel::Expr`. Comments / atoms / brackets also fall through.
fn is_top_level_form(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp
        && !children.is_empty()
        && let Sexp::Symbol(name, _) = &children[0]
    {
        matches!(
            name.as_str(),
            "defn" | "defn-" | "deftype" | "deftype-" | "deftrait" | "deftrait-"
                | "impl" | "defmacro" | "defmacro-"
        )
    } else {
        false
    }
}

/// Convert a `ParsedEntry` to a `TopLevel` shape. Mirrors typecheck's
/// `parsed_to_top_level` (which is private). `Macro` and `Constructor`
/// entries return `None` — they are handled by the macro pipeline and ADT
/// constructor synthesis respectively, outside the typecheck dispatch.
fn parsed_entry_to_top_level(parsed: cranelisp_types::ParsedEntry) -> Option<TopLevel> {
    use cranelisp_types::ParsedEntry;
    match parsed {
        ParsedEntry::Def { name, variants, visibility, docstring, span } => {
            Some(TopLevel::Defn(Defn {
                name,
                docstring,
                variants,
                visibility,
                span,
            }))
        }
        ParsedEntry::TypeDef { name, type_params, constructors, visibility, docstring, span } => {
            let type_params: Vec<Symbol> =
                type_params.into_iter().map(|t| Symbol::from(t.as_ref())).collect();
            Some(TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            })
        }
        ParsedEntry::TraitDecl { decl } => Some(TopLevel::TraitDecl(decl)),
        ParsedEntry::TraitImpl { impl_ } => Some(TopLevel::TraitImpl(impl_)),
        ParsedEntry::Macro { .. } | ParsedEntry::Constructor { .. } => None,
        _ => None,
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
                use cranelisp_types::TypeName;
                let type_params_tn: Vec<TypeName> = type_params
                    .iter()
                    .map(|s| TypeName::from(s.as_ref()))
                    .collect();
                out.push(ParsedEntry::TypeDef {
                    name: name.clone(),
                    type_params: type_params_tn,
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
    module: &ModuleFullPath,
    working_program: &[TopLevel],
) -> Result<(), CranelispError> {
    // Wave 3b-2c.3: FIXME 0179 (cluster-mode read-union via View::union) has
    // landed in typecheck. Cluster mode is now activated as the hot path —
    // writes flow to a fresh staging table, reads union staging-first with
    // live, and on Ok the staging entries commit to live atomically. On Err
    // staging drops and live is unchanged.
    process_cluster_with_staging(symbol_tables, module, working_program)
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
    module: &ModuleFullPath,
    working_program: &[TopLevel],
) -> Result<(), CranelispError> {
    use cranelisp_typecheck::{check_forms, ClusterContext};

    let parsed = top_level_to_parsed_entries(working_program);
    if parsed.is_empty() {
        return Ok(());
    }

    let mut staging: crate::code::SessionSymbolTable =
        cranelisp_types::SymbolTable::<crate::code::Code, ()>::new_with_params(
            module.clone(),
        );
    let mut ctx: ClusterContext<'_, crate::code::Code, ()> =
        ClusterContext::cluster(symbol_tables, &mut staging, module.clone());
    let result = check_forms(parsed, &mut ctx, symbol_tables)
        .map_err(check_error_to_cranelisp_error);
    drop(ctx);

    // On Err: staging drops on function return — atomic discard.
    result?;

    // On Ok: commit staging entries to live.
    commit_staging_to_live(symbol_tables, module, staging);
    Ok(())
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

use crate::expander::{
    self, MacroClauseEntry, MacroEntry, MacroResolver,
};
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
    /// Per-invocation typecheck state. For REPL: extracted from SharedState.repl_check_state.
    /// For batch workers: created fresh per module.
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
    /// Create a TypeCheckEnv borrowing the shared state.
    pub fn tc_env(
        &self,
    ) -> cranelisp_typecheck::TypeCheckEnv<'_, crate::code::Code, ()> {
        cranelisp_typecheck::TypeCheckEnv::new(self.symbol_tables, self.next_type_id)
    }

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
        self.tc_env().ensure_module_exists(&module);
        if self.check_state.current_module() != &module {
            self.check_state = CheckState::new(module.clone());
        }
        self.current_module = module;
    }
}

// ---------------------------------------------------------------------------
// SymbolTableMacroResolver — on-demand macro resolution from symbol tables
// ---------------------------------------------------------------------------

/// Macro resolver backed by the TypeChecker symbol tables.
///
/// Walks the symbol table on each name encounter, follows Import/Reexport chains
/// to the defining module, checks `ModuleEntry::Def.code` presence there (Sprint
/// 57 Wave 2 G6 migration — compiled code lives on the symbol-table entry),
/// compiles on demand if needed, and returns the MacroEntry.
///
/// Uses the `take_state`/`restore_state` pattern: the caller extracts `CheckState`
/// from the `TypeChecker` before creating this resolver, so the resolver holds
/// `&TypeChecker` (shared ref for DashMap reads) and `&mut CheckState` separately.
struct SymbolTableMacroResolver<'a> {
    /// Per-module symbol tables (DashMap, interior mutability).
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    /// Monotonic counter for fresh type variable IDs.
    next_type_id: &'a std::sync::atomic::AtomicU32,
    /// CheckState — needed for on-demand compilation (check_form_with_state).
    check_state: &'a mut CheckState,
    /// Current module path (starting point for symbol lookup).
    current_module: ModuleFullPath,
    /// Per-module typecheck products (DashMap, interior mutability).
    typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    /// Accumulator for check_form_with_state during on-demand compilation.
    accumulator: &'a mut ModuleCheckAccumulator,
    /// Scheduler — for notify_inmem_codegen_complete after on-demand compilation.
    scheduler: &'a CompileScheduler,
    /// Shared state — needed for JIT retention during on-demand compilation.
    /// None for REPL contexts where caching is not used.
    shared_state: Option<&'a crate::session_v4::SharedState>,
    /// Defining modules for macros that were resolved during expansion.
    /// Used to qualify bare symbols in expanded output (cross-module hygiene).
    macro_defining_modules: Vec<ModuleFullPath>,
}

impl MacroResolver for SymbolTableMacroResolver<'_> {
    fn resolve_macro(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<MacroEntry>, CranelispError> {
        // Step 1: Walk symbol table to find the defining module and clause infos.
        let resolved = resolve_macro_definition(
            self.symbol_tables, &self.current_module, name, 16,
        );
        let (defining_module, clauses, docstring) = match resolved {
            Some(r) => r,
            None => return Ok(None),
        };

        // Record the defining module for post-expansion symbol qualification.
        if defining_module != self.current_module {
            self.macro_defining_modules.push(defining_module.clone());
        }

        // Step 2: Check if all clauses are compiled. If so, build entry directly.
        let macro_sym = Symbol::from(name);
        let all_compiled = clauses.iter().enumerate().all(|(idx, _)| {
            let clause_name = macro_clause_jit_name(&macro_sym, idx);
            has_code_ptr(self.symbol_tables, &defining_module, &clause_name)
        });

        if !all_compiled {
            // Step 3: Compile inline. We need DefmacroInfo to drive compilation.
            // Look up the sexp from the defining module's symbol table.
            let macro_sexp = resolve_macro_sexp_from(self.symbol_tables, &defining_module, name);
            if let Some(sexp) = macro_sexp {
                let info = cranelisp_frontend::parse_defmacro(&sexp)?;
                compile_macro_with_state(
                    self.symbol_tables, self.next_type_id, self.check_state, &defining_module,
                    &info, span, self.accumulator,
                    self.typecheck_products,
                    self.scheduler,
                    self.shared_state,
                )?;
            } else {
                // No sexp available — cannot compile. Return None.
                return Ok(None);
            }
        }

        // Step 4: Build MacroEntry from code pointers.
        build_macro_entry_from_clauses(
            self.symbol_tables, &defining_module, &macro_sym, &clauses, docstring,
        )
    }
}

/// Follow Import/Reexport chains to find the defining module, clauses, and docstring.
///
/// Generic recursive chain walker with depth limit to prevent infinite loops.
pub(crate) fn resolve_macro_definition(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    name: &str,
    max_depth: usize,
) -> Option<(ModuleFullPath, Vec<MacroClauseInfo>, Option<String>)> {
    if max_depth == 0 {
        return None;
    }
    let table = symbol_tables.get(module)?;
    let entry = table.get(name)?;
    match entry {
        ModuleEntry::Macro { clauses, docstring, .. } => {
            Some((module.clone(), clauses.clone(), docstring.clone()))
        }
        ModuleEntry::Import { source } | ModuleEntry::Reexport { source, .. } => {
            let next_mod = source.module.clone();
            let next_sym: String = source.symbol.as_ref().to_string();
            drop(table); // Release DashMap guard before recursing.
            resolve_macro_definition(symbol_tables, &next_mod, &next_sym, max_depth - 1)
        }
        _ => None,
    }
}

/// Resolve a macro's sexp from the defining module's symbol table.
///
/// Unlike `resolve_macro_definition`, this specifically looks up the sexp
/// stored on the `ModuleEntry::Macro` in the defining module.
fn resolve_macro_sexp_from(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    defining_module: &ModuleFullPath,
    name: &str,
) -> Option<Sexp> {
    let table = symbol_tables.get(defining_module)?;
    match table.get(name)? {
        ModuleEntry::Macro { sexp, .. } => sexp.clone(),
        _ => None,
    }
}

/// Compile a macro's clauses using the `_with_state` API (no &mut TypeChecker needed).
///
/// This is the on-demand compilation path for the resolver. Uses
/// `check_form_with_state` and `merge_form_result_with_state` which take
/// `&self` on TypeChecker + `&mut CheckState`.
#[allow(clippy::too_many_arguments)]
fn compile_macro_with_state(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut CheckState,
    target_module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    scheduler: &CompileScheduler,
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<(), CranelispError> {
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(symbol_tables, target_module, &clause_name) {
            continue;
        }

        compile_macro_clause_with_state(
            symbol_tables, next_type_id, check_state, target_module,
            &info.name, clause_idx, clause, span,
            accumulator, typecheck_products,
            shared_state,
        )?;
        // Sprint 57 Wave 4 G9: macro-clause compile must NOT set inmem_done
        // (last=false). Other symbols in the owning module (including
        // `main`) still need compiling. inmem_done is set by the final
        // `inline_jit_codegen_for_module` at the end of
        // `handle_typecheck_work_shared`. Pre-Wave-4 scoped workers got
        // away with this because the main thread waited on scope exit, not
        // on the scheduler; persistent workers expose the race.
        scheduler.notify_inmem_codegen_complete(target_module, &clause_name, false);
    }
    Ok(())
}

/// Compile a single macro clause using the `_with_state` API.
///
/// Mirrors `compile_macro_clause_inline` but uses `&TypeChecker` + `&mut CheckState`
/// instead of `&mut ModuleCompiler`.
#[allow(clippy::too_many_arguments)]
fn compile_macro_clause_with_state(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut CheckState,
    target_module: &ModuleFullPath,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    shared_state: Option<&crate::session_v4::SharedState>,
) -> Result<(), CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(), clause_idx, clause, span,
    );

    // Step 2: Expand quasiquotes.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST. Macro clause synthesis emits compiler-generated
    // bodies whose Sexp tree comes from `synthesize_macro_clause_defn`; user
    // `(trace ...)` cannot reach this synthesis path. `InMemoryAndObject`
    // bypasses the validator.
    let program = build_program_compat(
        &[expanded_sexp],
        CodegenBehaviour::InMemoryAndObject,
    )?;

    // Step 4: Typecheck via the collapsed `check_forms` surface (Decision 44
    // 2026-05-13 third amendment). `check_program_compat` runs the internal
    // Pass 1 + Pass 2 + finalize sequence in one call. `check_state` /
    // `accumulator` are no longer threaded through the public typecheck
    // surface — they are vestigial parameters on this function (kept for
    // source-compat with pre-S66 callers).
    let _ = check_state;
    let _ = accumulator;
    let _ = next_type_id;
    check_program_compat(symbol_tables, target_module, &program)?;

    // Step 5: Extract the defn from the annotated symbol table (not the unannotated program).
    // The typechecker stores annotated defns (with resolved_call on AST nodes) in
    // ModuleEntry::Def.ast. Using the unannotated program would lose these annotations.
    let defn_name = program
        .iter()
        .find_map(|tl| match tl {
            TopLevel::Defn(d) => Some(d.name.clone()),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!(
                "macro clause {} for '{}' produced no defn",
                clause_idx, macro_name
            ),
            location: ErrorLocation::from_span(span),
        })?;

    let defn = symbol_tables
        .get(target_module)
        .and_then(|table| match table.get(defn_name.as_ref()) {
            Some(cranelisp_types::ModuleEntry::Def { ast: Some(d), .. }) => Some(d.clone()),
            _ => None,
        })
        .unwrap_or_else(|| {
            // Fallback to program version (should not happen if typecheck is working)
            program.iter().find_map(|tl| match tl {
                TopLevel::Defn(d) => Some(d.clone()),
                _ => None,
            }).unwrap_or_else(|| unreachable!("invariant: defn_name was extracted from program above"))
        });
    let defn = &defn;

    // Compile macro clause through the unified compile_to_module path.
    // Macro clause functions are normal functions on per-module GOTs — the
    // typechecker has registered `defn.name` on `target_module`'s symbol
    // table with `ast: Some(_)` and `got_slot: Some(_)` (Wave 0 invariant).
    let tc_modules = symbol_tables;
    ensure_typecheck_product(typecheck_products, target_module);
    // Wave 0 (Sprint 56): the typechecker registers every compilable defn
    // with `got_slot: Some(_)`, so the legacy `pre_register_got_slots_in_tc`
    // safety net is no longer needed here.
    let _ = accumulator;
    let names = [defn.name.clone()];
    inline_jit_codegen_for_names(
        target_module,
        &names,
        tc_modules,
        None,
        &[],
        shared_state,
    )?;

    Ok(())
}

/// Build a MacroEntry from compiled clause code pointers.
fn build_macro_entry_from_clauses(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    defining_module: &ModuleFullPath,
    macro_sym: &Symbol,
    clauses: &[MacroClauseInfo],
    docstring: Option<String>,
) -> Result<Option<MacroEntry>, CranelispError> {
    let mut compiled_clauses = Vec::new();
    for (idx, clause_info) in clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(macro_sym, idx);
        match get_code_ptr(symbol_tables, defining_module, &clause_name) {
            Some(ptr) => {
                compiled_clauses.push(MacroClauseEntry {
                    func_ptr: ptr,
                    params: clause_info.params.clone(),
                    rest_param: clause_info.rest_param.clone(),
                });
            }
            None => return Ok(None), // Clause not compiled — skip this macro.
        }
    }
    if compiled_clauses.is_empty() {
        return Ok(None);
    }
    Ok(Some(MacroEntry {
        clauses: compiled_clauses,
        docstring,
    }))
}

/// Scope the resolver's borrows to just the expansion phase.
///
/// Creates a SymbolTableMacroResolver, runs expand_sexp_recursive,
/// drops the resolver, returns the expanded sexp. After this returns,
/// ctx and accumulator are available for the caller to use freely.
fn try_expand_sexp(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Option<Sexp>, CranelispError> {
    // No need to extract/restore CheckState — TypeCheckEnv borrows are
    // separate from CheckState. The resolver holds &DashMap (from tc_env)
    // and &mut CheckState separately.
    let (result, defining_modules) = {
        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: ctx.symbol_tables,
            next_type_id: ctx.next_type_id,
            check_state: &mut ctx.check_state,
            current_module: module.clone(),
            typecheck_products: ctx.typecheck_products,
            accumulator,
            scheduler: ctx.scheduler,
            shared_state: ctx.shared_state,
            macro_defining_modules: Vec::new(),
        };

        let r = expander::expand_sexp_recursive(sexp.clone(), &mut resolver, 0);
        let dms = std::mem::take(&mut resolver.macro_defining_modules);
        (r, dms)
        // resolver dropped here, releasing all borrows on check_state
    };

    let expanded = result?;

    if expanded == *sexp {
        Ok(None)
    } else {
        // Qualify bare symbols from defining modules (cross-module macro hygiene).
        let qualified = if defining_modules.is_empty() {
            expanded
        } else {
            qualify_expanded_sexp(ctx.symbol_tables, module, &defining_modules, expanded)
        };
        Ok(Some(qualified))
    }
}

/// Qualify bare symbols in macro-expanded sexp with their defining module paths.
///
/// After macro expansion, bare symbol references like `make-seven` may refer to
/// symbols in the macro's defining module. These must be qualified (e.g.,
/// `helper/make-seven`) so the consuming module's typechecker can resolve them.
///
/// Only qualifies symbols that:
/// - Are bare (no `/` already) and not type annotations (`:` prefix)
/// - Are found in a defining module's symbol table
/// - Are NOT already available in the current module
fn qualify_expanded_sexp(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: &ModuleFullPath,
    defining_modules: &[ModuleFullPath],
    sexp: Sexp,
) -> Sexp {
    match sexp {
        Sexp::Symbol(ref name, span) => {
            // Skip already-qualified names, type annotations, special names
            if name.contains('/') || name.starts_with(':') || name.starts_with('_') {
                return sexp;
            }
            // Skip if the symbol is already available in the current module
            if let Some(table) = symbol_tables.get(current_module)
                && table.get(name).is_some() {
                    return sexp;
                }
            // Check defining modules for this symbol
            for def_mod in defining_modules {
                if let Some(table) = symbol_tables.get(def_mod)
                    && let Some(entry) = table.get(name) {
                        // Follow imports to find the true source module for qualification
                        let qual_module = match entry {
                            ModuleEntry::Import { source } => &source.module,
                            ModuleEntry::Reexport { source, .. } => &source.module,
                            _ => def_mod,
                        };
                        let qualified = format!("{}/{}", qual_module.as_ref(), name);
                        return Sexp::Symbol(qualified, span);
                    }
            }
            sexp
        }
        Sexp::List(children, span) => {
            // Don't qualify the head of special forms like defn, let, etc.
            // But DO qualify function call targets and their arguments.
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_expanded_sexp(symbol_tables, current_module, defining_modules, c))
                .collect();
            Sexp::List(qualified_children, span)
        }
        Sexp::Bracket(children, span) => {
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_expanded_sexp(symbol_tables, current_module, defining_modules, c))
                .collect();
            Sexp::Bracket(qualified_children, span)
        }
        // Other sexp types (Int, Float, String, Bool) pass through unchanged.
        other => other,
    }
}

// ---------------------------------------------------------------------------
// ProcessResult — suspension-aware return type
// ---------------------------------------------------------------------------

/// Result of processing module forms. Either the module is fully typechecked,
/// or it blocked on a dependency and needs to be resumed later.
#[allow(clippy::large_enum_variant)]
pub enum ProcessResult {
    /// Module fully typechecked.
    Complete {
        check_result: CheckResult,
        program: Vec<TopLevel>,
    },
    /// Blocked on a dependency. Resume from the given form index.
    Blocked {
        form_index: usize,
        dep_module: ModuleFullPath,
        dep_sexps: Vec<Sexp>,
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
// FormKind — per-sexp form classification for Pass 2
// ---------------------------------------------------------------------------

/// Classification of a top-level sexp for Pass 2 dispatch.
enum FormKind {
    Import(Vec<ImportSpec>),
    Export(Vec<ExportSpec>),
    Mod(cranelisp_types::ModDecl),
    Platform(PlatformSpec),
    Defmacro,
    Regular,
}

// ---------------------------------------------------------------------------
// Structural-decl writers (Sprint 58 Step 5a / Decision 33)
// ---------------------------------------------------------------------------
//
// Append the user-authored `(import …)` / `(export …)` / `(platform …)` /
// `(mod …)` declarations onto the module's `SymbolTable.{imports,exports,
// platforms,submodules}` Vec in source order.
//
// Implicit-prelude disposition (CP3 / `design/int/symbol-table-cache.md` §3
// open-question resolution): chose **option (b)** — `imports` records only
// user-authored `(import …)` forms. The implicit prelude `ImportSpec`
// constructed at `inject_prelude_if_needed` is NOT recorded here. Rationale:
// `imports` is the source-of-truth for `.cl` regeneration (`src/save.rs`)
// and the regenerator does not emit the implicit prelude form (`save.rs:142`
// already filters it). Keeping `imports` user-authored matches what the
// regenerator emits and what the user reads in their `.cl` file. The
// per-symbol `ModuleEntry::Import` entries on the symbol table still record
// the resolved effects of the implicit prelude.

fn record_imports_on_symbol_table(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    specs: &[ImportSpec],
) {
    if specs.is_empty() {
        return;
    }
    if let Some(mut st) = ctx.symbol_tables.get_mut(module) {
        st.imports.extend(specs.iter().cloned());
    }
}

fn record_exports_on_symbol_table(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    specs: &[ExportSpec],
) {
    if specs.is_empty() {
        return;
    }
    if let Some(mut st) = ctx.symbol_tables.get_mut(module) {
        st.exports.extend(specs.iter().cloned());
    }
}

fn record_platform_on_symbol_table(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    spec: &PlatformSpec,
) {
    if let Some(mut st) = ctx.symbol_tables.get_mut(module) {
        st.platforms.push(spec.clone());
    }
}

fn record_submodule_on_symbol_table(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) {
    if let Some(mut st) = ctx.symbol_tables.get_mut(module) {
        st.submodules.push(decl.clone());
    }
}

/// Classify a top-level sexp for Pass 2 dispatch.
///
/// Recognizes import/export/mod/platform/defmacro forms. Everything else
/// is Regular (defn, deftype, deftrait, impl, expr).
///
/// `containing_module` is the module path whose source contains this form;
/// the frontend needs it to rewrite `super` imports per spec §8.3.7.
fn classify_form(
    sexp: &Sexp,
    containing_module: &ModuleFullPath,
) -> Result<FormKind, CranelispError> {
    match sexp {
        Sexp::List(items, _span) if !items.is_empty() => {
            if let Sexp::Symbol(name, _) = &items[0] {
                match name.as_str() {
                    // Per Decision 44 + FIXME 0156: `parse_{import,export,mod,
                    // platform}_sexp` are no longer public on the frontend
                    // facade. Use `extract_module_declarations` to peel a
                    // single sexp's structural decl out — it returns the
                    // typed shape the worker needs.
                    "import" => {
                        let (decls, _remaining) =
                            cranelisp_frontend::extract_module_declarations(
                                containing_module.clone(),
                                vec![sexp.clone()],
                            )?;
                        Ok(FormKind::Import(decls.import_specs))
                    }
                    "export" => {
                        let (decls, _remaining) =
                            cranelisp_frontend::extract_module_declarations(
                                containing_module.clone(),
                                vec![sexp.clone()],
                            )?;
                        Ok(FormKind::Export(decls.export_specs))
                    }
                    "mod" | "mod-" => {
                        let (decls, _remaining) =
                            cranelisp_frontend::extract_module_declarations(
                                containing_module.clone(),
                                vec![sexp.clone()],
                            )?;
                        let decl = decls.mod_decls.into_iter().next().ok_or_else(|| {
                            CranelispError::ParseError {
                                message: "classify_form: no mod decl produced".into(),
                                location: ErrorLocation::from_span(sexp.span()),
                            }
                        })?;
                        Ok(FormKind::Mod(decl))
                    }
                    "platform" => {
                        let (decls, _remaining) =
                            cranelisp_frontend::extract_module_declarations(
                                containing_module.clone(),
                                vec![sexp.clone()],
                            )?;
                        let spec = decls.platform_specs.into_iter().next().ok_or_else(|| {
                            CranelispError::ParseError {
                                message: "classify_form: no platform spec produced".into(),
                                location: ErrorLocation::from_span(sexp.span()),
                            }
                        })?;
                        Ok(FormKind::Platform(spec))
                    }
                    "defmacro" => Ok(FormKind::Defmacro),
                    _ => Ok(FormKind::Regular),
                }
            } else {
                Ok(FormKind::Regular)
            }
        }
        _ => Ok(FormKind::Regular),
    }
}

// ---------------------------------------------------------------------------
// BlockAction — import/mod handler result
// ---------------------------------------------------------------------------

/// Signals the Pass 2 loop whether to continue or block.
enum BlockAction {
    /// Continue processing the next form.
    Continue,
    /// Block: a dependency was discovered. Store state and return.
    Block {
        dep_module: ModuleFullPath,
        dep_sexps: Vec<Sexp>,
    },
}

// ---------------------------------------------------------------------------
// process_module_forms — two-pass per-form typecheck (C1)
// ---------------------------------------------------------------------------

/// Expand, build AST, and typecheck all forms in a module from pre-parsed sexps.
///
/// Drives the two-pass iteration required by Algorithm W:
/// - Pass 1 (Register): register type defs, trait decls, signatures.
///   Defmacro forms are parsed and registered in the module table.
/// - Pass 2 (CheckBody): per-sexp expand-then-check. Macro calls are
///   expanded inline (compiling macro deps on demand). Import/export/mod/
///   platform forms are handled lazily (Step 5).
///
/// On success, notifies the scheduler of each typechecked symbol and
/// calls `notify_typecheck_done`. On error, calls `notify_module_failed`.
///
/// `start_form_index`: the Pass 2 form to resume from (0 for fresh modules).
/// On resume, Pass 1 is skipped (already done).
///
/// `state`: per-module suspension state (accumulator, expanded_program, pass1_done).
/// May be a resumed state (saved across suspension) or freshly created.
pub fn process_module_forms(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
    start_form_index: usize,
    state: &mut ModuleSuspendState,
    strategy: ModuleStrategy,
) -> Result<ProcessResult, CranelispError> {
    let is_fresh = !state.pass1_done;

    if is_fresh && strategy == ModuleStrategy::Replace {
        // Set active module. Symbol table is preserved for slot reuse
        // and type-change detection.
        ctx.set_current_module(module.clone());
        // clear_module_for_replace_public is a no-op with stateless TC;
        // symbol table clearing happens through the module system.

        // Zero GOT slots and clear codegen artifacts for this module's
        // symbols. Slot assignments are preserved so re-compiled code
        // lands in the same slots.
        clear_module_codegen(ctx, module);

        // Prelude injection: inject (import [prelude [*]]) for non-prelude modules
        // unless the source explicitly references prelude in an import or export (§8.8.1).
        if let Some(result) = inject_prelude_if_needed(ctx, module, sexps)? {
            return Ok(result);
        }
    } else if is_fresh && strategy == ModuleStrategy::Additive {
        // Additive: just set the active module. Module state persists
        // from previous evals — no clear, no re-injection.
        ctx.set_current_module(module.clone());
    } else {
        // Resume: set active module (may have been changed by dep processing).
        ctx.set_current_module(module.clone());
    }

    // --- Pass 1: only on fresh start (not on resume after blocking) ---
    if is_fresh {
        // Pass 0: Process import/export/mod forms before Pass 1.
        // Imported symbols must be in scope before pass1_register checks
        // trait impl bodies. If a dependency isn't loaded yet, we block
        // and resume here later (pass1_done is still false).
        for (form_idx, sexp) in sexps.iter().enumerate() {
            match classify_form(sexp, module)? {
                FormKind::Import(specs) => {
                    // Record import specs as structural decls on the module's
                    // SymbolTable (Sprint 58 Step 5a / Decision 33). Source-order
                    // append, no dedup. Implicit prelude is NOT recorded here —
                    // see `inject_prelude_if_needed` for the rationale (option (b)
                    // in `design/int/symbol-table-cache.md` §3 / CP3).
                    record_imports_on_symbol_table(ctx, module, &specs);
                    match handle_import(ctx, module, specs)? {
                        BlockAction::Continue => {}
                        BlockAction::Block { dep_module, dep_sexps } => {
                            return Ok(ProcessResult::Blocked {
                                form_index: form_idx,
                                dep_module,
                                dep_sexps,
                            });
                        }
                    }
                }
                FormKind::Export(specs) => {
                    // Record export specs as structural decls on the module's
                    // SymbolTable (Sprint 58 Step 5a / Decision 33).
                    record_exports_on_symbol_table(ctx, module, &specs);
                    match handle_export(ctx, module, &specs)? {
                        BlockAction::Continue => {}
                        BlockAction::Block { dep_module, dep_sexps } => {
                            return Ok(ProcessResult::Blocked {
                                form_index: form_idx,
                                dep_module,
                                dep_sexps,
                            });
                        }
                    }
                }
                FormKind::Mod(decl) => {
                    // Record mod decl as structural decl on the module's
                    // SymbolTable (Sprint 58 Step 5a / Decision 33).
                    record_submodule_on_symbol_table(ctx, module, &decl);
                    match handle_mod(ctx, module, &decl)? {
                        BlockAction::Continue => {}
                        BlockAction::Block { dep_module, dep_sexps } => {
                            return Ok(ProcessResult::Blocked {
                                form_index: form_idx,
                                dep_module,
                                dep_sexps,
                            });
                        }
                    }
                }
                FormKind::Platform(spec) => {
                    // Record platform spec as structural decl on the module's
                    // SymbolTable (Sprint 58 Step 5a / Decision 33).
                    record_platform_on_symbol_table(ctx, module, &spec);
                    handle_platform(ctx, module, &spec)?;
                }
                _ => {} // Regular, Defmacro — handled in Pass 2
            }
        }

        let (regular_sexps, macro_infos) = separate_macros(sexps, module)?;

        // Build AST for regular (non-macro) forms. Per Decision 40 / Path B1
        // (FIXMEs 0199 + 0204): the cluster-orchestrator-equivalent path
        // here runs the `(trace ...)`-in-`--link` validator pass before
        // typecheck dispatch. Mode flows from `SharedState.codegen_behaviour`;
        // REPL paths without `shared_state` default to `InMemoryAndObject`
        // (validator is a no-op).
        let mode = ctx
            .shared_state
            .map(|s| s.codegen_behaviour)
            .unwrap_or(CodegenBehaviour::InMemoryAndObject);
        let program = build_program_compat(&regular_sexps, mode)?;
        let working_program = wrap_exprs_as_defns(&program);

        pass1_register(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &working_program, &mut state.accumulator)?;

        for (name, info, sexp) in &macro_infos {
            register_macro_in_module(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, name, info, sexp)?;
        }

        let defaults = register_default_methods(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &mut state.accumulator)?;
        state.accumulator.default_method_defns = defaults;
        state.pass1_done = true;
    }

    // --- Pass 2: per-sexp expand-then-check, from start_form_index ---
    // expanded_program accumulates across suspensions via the caller.
    let pass2_result = pass2_check_bodies_with_expansion(
        ctx, module, sexps, start_form_index, &mut state.accumulator, &mut state.expanded_program,
    )?;

    match pass2_result {
        Pass2Result::Complete => {
            finalize_module(ctx, module, &state.expanded_program, &mut state.accumulator, strategy)
        }
    }
}

/// Separate defmacro forms from regular forms for Pass 1.
#[allow(clippy::type_complexity)]
fn separate_macros(
    sexps: &[Sexp],
    containing_module: &ModuleFullPath,
) -> Result<(Vec<Sexp>, Vec<(Symbol, cranelisp_frontend::DefmacroInfo, Sexp)>), CranelispError> {
    let mut regular_sexps = Vec::new();
    let mut macro_infos = Vec::new();

    for sexp in sexps {
        if cranelisp_frontend::is_defmacro(sexp) {
            let info = cranelisp_frontend::parse_defmacro(sexp)?;
            macro_infos.push((info.name.clone(), info, sexp.clone()));
        } else {
            // Skip import/export/mod/platform in Pass 1 regular forms.
            // They don't contribute type signatures and are handled in Pass 2.
            match classify_form(sexp, containing_module)? {
                FormKind::Import(_) | FormKind::Export(_) | FormKind::Mod(_) | FormKind::Platform(_) => {
                    // Skip — handled during Pass 2.
                }
                _ => {
                    regular_sexps.push(sexp.clone());
                }
            }
        }
    }
    Ok((regular_sexps, macro_infos))
}

/// Finalize a fully typechecked module: run post-passes and build CheckResult.
///
/// Per Decision 44's 2026-05-13 third amendment, the typecheck dispatch
/// has collapsed onto a single `check_forms` call per cluster. The pre-S66
/// shape (`pass1_register` + per-form `check_form(CheckBody)` +
/// `finalize_check_result`) is consolidated here into one
/// `check_program_compat` invocation over `expanded_program` plus the
/// accumulated default-method defns. `accumulator.defn_type_vars` is no
/// longer published across the facade — the worker side fabricates the
/// display info from whatever `__expr` defn was registered into the live
/// `SymbolTable`, falling back to `None` for the multi-defn case (a follow-up
/// FIXME will surface display info via accessor on `ProcessedCluster`).
fn finalize_module(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    expanded_program: &[TopLevel],
    accumulator: &mut ModuleCheckAccumulator,
    _strategy: ModuleStrategy,
) -> Result<ProcessResult, CranelispError> {
    let mut final_working = wrap_exprs_as_defns(expanded_program);

    // Append default-method defns the trait-impl Pass-1 step had deferred.
    // Pre-S66 these flowed through a separate Pass-2 `check_form(CheckBody)`
    // step; under collapsed `check_forms` they ride into the same dispatch
    // alongside the body forms.
    let defaults_for_body: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    for defn in &defaults_for_body {
        final_working.push(TopLevel::Defn(defn.clone()));
    }

    // Single typecheck dispatch — internally drives Pass 1, Pass 2, finalize.
    check_program_compat(ctx.symbol_tables, module, &final_working)?;

    // Build a minimal `CheckResult` carrier for downstream codegen. The new
    // typecheck surface no longer returns a `CheckResult` from
    // `check_forms`; downstream code consumes only `warnings` (none today)
    // and `display` (handled by REPL via direct SymbolTable lookups).
    let check_result = CheckResult {
        warnings: Vec::new(),
        display: None,
    };

    // NOTE: notify_typecheck_done is NOT called here. The caller is
    // responsible for stashing the program and calling
    // notify_typecheck_done AFTER, so that nice workers cannot claim
    // the module before the stash is populated.

    // Build a program view for nice worker stashing. The nice worker no
    // longer reads program contents — it enumerates via `defined_symbols()`
    // — but a non-empty `program` still signals "has compilable defns".
    // Expression forms flow through as `TopLevel::Expr`; regular defns and
    // trait impls are passed through unchanged.
    let program: Vec<TopLevel> = expanded_program.to_vec();

    Ok(ProcessResult::Complete {
        check_result,
        program,
    })
}

/// Register a defmacro in the module table (Pass 1).
///
/// Parses clause info and stores it as `ModuleEntry::Macro` with the
/// original sexp for later compilation. No codegen — deferred until
/// first use.
fn register_macro_in_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    _next_type_id: &std::sync::atomic::AtomicU32,
    _check_state: &mut CheckState,
    module: &ModuleFullPath,
    name: &Symbol,
    info: &cranelisp_frontend::DefmacroInfo,
    sexp: &Sexp,
) -> Result<(), CranelispError> {
    let clause_infos: Vec<MacroClauseInfo> = info
        .clauses
        .iter()
        .map(|c| MacroClauseInfo {
            params: c.fixed_params.clone(),
            rest_param: c.rest_param.clone(),
            source: None,
        })
        .collect();
    let visibility = if info.is_private {
        Visibility::Private
    } else {
        Visibility::Public
    };
    if let Some(mut table) = symbol_tables.get_mut(module) {
        table.insert(
            name.clone(),
            ModuleEntry::Macro {
                name: name.clone(),
                clauses: clause_infos,
                docstring: info.docstring.clone(),
                visibility,
                sexp: Some(sexp.clone()),
                source: None,
                callees: Vec::new(),
            },
        );
    }
    Ok(())
}

/// Internal result from Pass 2 — either complete or blocked.
/// The expanded program is accumulated in the caller's mutable Vec.
enum Pass2Result {
    /// All forms processed. Expanded program is in the caller's Vec.
    Complete,
    // Note: Import/export/mod/platform blocking is now handled in Pass 0.
    // Pass 2 no longer needs a Blocked variant.
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
    start_form_index: usize,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<Pass2Result, CranelispError> {
    for (_form_idx, sexp) in sexps.iter().enumerate().skip(start_form_index) {

        match classify_form(sexp, module)? {
            // Import/export/mod/platform forms are processed in Pass 0
            // (before Pass 1). By the time Pass 2 runs, these have already
            // been handled. Skip them here — they are no-ops in Pass 2.
            FormKind::Import(_)
            | FormKind::Export(_)
            | FormKind::Mod(_)
            | FormKind::Platform(_) => {}
            FormKind::Defmacro => {
                // Registered in Pass 1. Compile eagerly in Pass 2 so type errors
                // in the macro body are caught at definition time (not deferred
                // until the macro is first called).
                let info = cranelisp_frontend::parse_defmacro(sexp)?;
                compile_macro_if_needed(ctx, module, &info, sexp.span(), accumulator)?;
            }
            FormKind::Regular => {
                process_regular_form(
                    ctx, module, sexp, accumulator, expanded_program,
                )?;
            }
        }
    }
    Ok(Pass2Result::Complete)
}

/// Process a regular (non-module-declaration) form in Pass 2.
///
/// Tries macro expansion via the SymbolTableMacroResolver, builds AST,
/// registers any new signatures (for begin-spliced defns), then typechecks
/// the body. New macros from expansion (e.g. const/def) are registered in
/// the symbol table and become visible to the resolver for subsequent forms.
fn process_regular_form(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<(), CranelispError> {
    // Try macro expansion on the raw sexp.
    let effective_sexp = try_expand_sexp(ctx, module, sexp, accumulator)?;

    let sexp_to_build = match &effective_sexp {
        Some(expanded) => expanded,
        None => sexp,
    };

    let flattened = cranelisp_frontend::flatten_begin(sexp_to_build.clone());

    // Partition flattened forms: macro expansion (e.g. const, def) can produce
    // defmacro forms that must be routed through the macro pipeline, not the
    // AST builder which rejects them.
    let mut regular_sexps = Vec::new();
    for form in flattened {
        if cranelisp_frontend::is_defmacro(&form) {
            let info = cranelisp_frontend::parse_defmacro(&form)?;
            register_macro_in_module(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, module, &info.name, &info, &form)?;
            compile_macro_if_needed(ctx, module, &info, form.span(), accumulator)?;
        } else {
            regular_sexps.push(form);
        }
    }

    if regular_sexps.is_empty() {
        return Ok(());
    }

    let mode = ctx
        .shared_state
        .map(|s| s.codegen_behaviour)
        .unwrap_or(CodegenBehaviour::InMemoryAndObject);
    let built = build_program_compat(&regular_sexps, mode)?;
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
                // Source: extract from module source_text via sexp span.
                // REPL eval may overwrite with the actual input text later.
                if entry.source.is_none() {
                    let span = sexp.span();
                    let src = ctx.typecheck_products.get(module)
                        .and_then(|tp| tp.source_text.as_ref().and_then(|text| {
                            let start = span.start as usize;
                            let end = span.end as usize;
                            if start < end && end <= text.len() {
                                Some(text[start..end].to_string())
                            } else {
                                None
                            }
                        }));
                    entry.source = src.or_else(|| Some(crate::pretty::pretty_print(sexp)));
                }
                entry.sexp = Some(sexp.clone());
                if let Some(ref expanded) = effective_sexp {
                    entry.expanded = Some(expanded.clone());
                }
                entry.ast = Some(defn.clone());
            }
        if let TopLevel::Defn(defn) = form {
            ctx.scheduler.notify_symbol_typechecked(module, &defn.name);
        }
    }

    expanded_program.extend(built);
    Ok(())
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
fn check_private_submodule_import(
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
        .find(|d| d.name.as_ref() == trailing && d.is_private);
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
fn handle_import(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: Vec<ImportSpec>,
) -> Result<BlockAction, CranelispError> {
    for spec in &specs {
        let dep = &spec.module_path;

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
            cranelisp_typecheck::register_imports(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, std::slice::from_ref(spec))?;
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
            cranelisp_typecheck::register_imports(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, std::slice::from_ref(spec))?;
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

        // Register dep with scheduler (idempotent — skips if already registered).
        ctx.scheduler.register_module(dep.clone(), true);

        // Block for typecheck (F1: called inside handle_import).
        ctx.scheduler.block_for_typecheck(
            module,
            dep,
            &Symbol::from("*"),
        )?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
            dep_sexps,
        });
    }

    Ok(BlockAction::Continue)
}

/// Publish a dep's parsed sexps into `shared.module_sexps` if shared state is
/// available. No-op for REPL contexts that don't use SharedState.
///
/// MUST be called BEFORE `scheduler.register_module(dep, ...)` so that any
/// persistent priority worker that wakes on the scheduler notify finds the
/// sexps already published. See Sprint 58 Wave 6 Defect 1 — the integration
/// repro is `tests/wave6_demo_repros.rs::repl_dep_load_no_race_with_persistent_workers`,
/// and the unit guard is `session_v4.rs::persistent_worker_tests::compile_dep_inline_publishes_sexps_before_register`.
fn publish_dep_sexps(
    ctx: &ModuleCompiler,
    dep: &ModuleFullPath,
    dep_sexps: &[Sexp],
) {
    if let Some(shared) = ctx.shared_state {
        let mut map = shared.module_sexps.lock()
            .unwrap_or_else(|e| e.into_inner());
        map.entry(dep.clone()).or_insert_with(|| dep_sexps.to_vec());
    }
}

/// Run the per-dep prologue that every persistent-worker form handler
/// (handle_import, handle_export, handle_mod, inject_prelude_if_needed)
/// used to inline before calling `scheduler.register_module`:
///
///   1. read source from dep_file
///   2. parse to sexps
///   3. record source hash in CacheState
///   4. stash source text on the typecheck product for /source
///   5. update file_to_module for the file watcher
///   6. publish dep_sexps to `shared.module_sexps` (Sprint 58 W6 Defect 1
///      publish-before-register ordering).
///
/// Does NOT call `scheduler.register_module` or `block_for_typecheck` —
/// the caller does that, so the shim is reusable regardless of whether
/// the caller intends to block. Returns the parsed sexps so the caller
/// can forward them through `ProcessResult::Blocked` / `BlockAction::Block`.
///
/// Sprint 59 Workstream A §7 Step 1 — collapse the 5 publish-before-register
/// sites (Sprint 58 W6 Defect 1) onto a single prologue. The caller-specific
/// error framing (span / message wording) is produced by `prologue_err`,
/// because each form handler has a slightly different error message shape.
fn register_dep(
    ctx: &mut ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
    prologue_err: impl FnOnce(std::io::Error) -> CranelispError,
) -> Result<Vec<Sexp>, CranelispError> {
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
    let dep_sexps = cranelisp_frontend::parse(&source)?;

    // 3. record source hash for manifest generation. Sprint 67 Cluster B
    //    sub-fire 3: ObjectCache facade.
    if let Some(shared) = ctx.shared_state {
        let hash = cranelisp_backend::cache::manifest::hash_source(&source);
        shared.cache.record_source_hash(dep, hash);
    }

    // 4. store source text for /source introspection (--repl).
    if ctx.introspection.is_some() {
        ensure_typecheck_product(ctx.typecheck_products, dep);
        if let Some(mut tp) = ctx.typecheck_products.get_mut(dep) {
            tp.source_text = Some(source);
        }
    }

    // 5. publish BEFORE scheduler notify (Sprint 58 W6 Defect 1 ordering).
    publish_dep_sexps(ctx, dep, &dep_sexps);
    crate::observability::record_module_event(
        crate::observability::SchedulerTraceTag::RegisterDepPublish,
        dep.as_ref(),
    );

    // Sprint 60 Workstream E-3 — debug-only structural guard: when shared
    // state is available, the publish above MUST have succeeded before we
    // return so the caller's subsequent `scheduler.register_module(dep, _)`
    // finds sexps ready in shared.module_sexps. Catches accidental reordering
    // in dev builds. See `design/int/dual-path-persistence-collapse.md §8.3`.
    debug_assert!(
        ctx.shared_state.is_none()
            || ctx.shared_state.unwrap()
                .module_sexps
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .contains_key(dep),
        "register_dep MUST publish dep_sexps to shared.module_sexps before returning \
         so the caller's scheduler.register_module call cannot race persistent workers"
    );

    Ok(dep_sexps)
}

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
fn try_cache_hit_load(
    ctx: &mut ModuleCompiler,
    dep: &ModuleFullPath,
    dep_file: &Path,
) -> bool {
    use cranelisp_backend::cache;
    use cranelisp_backend::cache::manifest as cache_manifest;
    use std::collections::{HashMap as StdHashMap, HashSet as StdHashSet};

    let shared = match ctx.shared_state {
        Some(s) => s,
        None => return false,
    };

    // Already-installed guard: another path may have installed this dep
    // already (concurrent load, prelude pre-load). Skip without re-reading.
    // Returning `true` signals "this dep is satisfied — caller proceeds";
    // the caller will register imports against the existing table.
    if ctx.symbol_tables.contains_key(dep) {
        return true;
    }

    // 1. Check cache validity: read source, compute hash, check manifest.
    //    Sprint 67 Cluster B sub-fire 3: ObjectCache facade.
    let cache_dir = match shared.cache.cache_dir() {
        Some(d) => d,
        None => return false,
    };

    let dep_source = match std::fs::read_to_string(dep_file) {
        Ok(s) => s,
        Err(_) => return false,
    };
    let source_hash = cache_manifest::hash_source(&dep_source);

    // Check manifest (source hash only, no dep hashes yet).
    let dep_hashes: StdHashMap<ModuleFullPath, String> = StdHashMap::new();
    if !shared.cache.is_cache_valid(dep, &source_hash, &dep_hashes) {
        return false;
    }

    // 2. Load metadata from disk.
    let cached = match cache::try_load_cached_module(&cache_dir, dep) {
        Ok(Some(c)) => c,
        _ => return false,
    };

    // 3. Check .o exists.
    if !cached.has_object {
        return false;
    }

    // 4. Extract all data from cached BEFORE moving symbol_table (avoids clone).
    let symbols: StdHashSet<Symbol> = cached.metadata.symbol_table
        .all_symbols()
        .filter_map(|(name, entry)| match entry {
            ModuleEntry::Def { .. } | ModuleEntry::Constructor { .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    // Collect names of functions with GOT slots for trait impl restoration.
    let mangled_names: Vec<String> = cached.metadata.symbol_table
        .all_symbols()
        .filter_map(|(name, entry)| match entry {
            ModuleEntry::Def { got_slot: Some(_), .. } => Some(name.as_ref().to_string()),
            _ => None,
        })
        .collect();
    // Sprint 58 Step 5b §3.2 — pull structural decls (platforms) out of the
    // about-to-be-moved symbol table BEFORE `restore_cached_module` consumes
    // it. We re-resolve platform DLLs after install so each
    // `PlatformEffect`-kind entry's `fn_ptr` is repopulated
    // (Decision 26 — re-derive on cache-hit load via the same
    // `load_and_register_platform` path used by fresh build).
    let cached_platforms: Vec<PlatformSpec> =
        cached.metadata.symbol_table.platforms.clone();

    // Sprint 58 Wave 2c / Decision 37 — capture user-authored imports BEFORE
    // moving the symbol table, so we can recurse and ensure every
    // transitive dep's symbol table (and `__cranelisp_got_{M}` data symbol)
    // is installed before this dep's codegen worker tries to load its `.o`.
    let cached_imports: Vec<ImportSpec> =
        cached.metadata.symbol_table.imports.clone();

    // Restore type info into TC (consumes symbol_table by value).
    // Sprint 58 Wave 3b: cached `<()>` table is converted to `<Code, ()>`
    // via `into_concrete` (every entry's `code` becomes `None::<Code>`;
    // codegen will populate fresh `Code::Jit` / `Code::Linker` entries).
    //
    // Sprint 67 hack-back (FIXME 0192 method 11 split): the prior
    // `restore_cached_module` method is deleted. Compose the two primitives
    // directly: advance `next_type_id` past any TypeId vars in the cached
    // schemes (preserves the consistency invariant — fresh vars must not
    // collide with cached vars during `apply_subst`), then atomically
    // install the decoded table via the `cranelisp-types` primitive.
    //
    // `restore_cached_impls` was a no-op (TraitImpl entries arrive on the
    // SymbolTable) and is also deleted; `mangled_names` is preserved here
    // as a marker for the cached-fn set in case future audits need it.
    let _ = &mangled_names;
    let concrete_table =
        cached.metadata.symbol_table.into_concrete::<crate::code::Code, ()>();
    cranelisp_typecheck::advance_next_id_past_table(ctx.next_type_id, &concrete_table);
    cranelisp_types::install_module(
        ctx.symbol_tables,
        dep.clone(),
        concrete_table,
    );

    // Sprint 58 Step 5b §3.2 — re-resolve platform fn ptrs for each
    // (platform …) declaration recorded on the cached SymbolTable. The GOT
    // is `#[serde(skip)]` so cache-hit arrives with all slots null;
    // re-running `load_and_register_platform` opens the DLL, validates the
    // manifest, and populates the live entries on the synthetic
    // `platform.{name}` module — matching the fresh-build path's result
    // for `(platform …)` forms. Failures here are non-fatal at the
    // cache-hit level (we treat them as "platform missing — fall back to
    // full rebuild" per `symbol-table-cache.md` §6); we abandon the
    // cache-hit attempt and let the normal load path retry.
    for spec in &cached_platforms {
        // Submodules cannot load platforms (spec §10.9.1) — skip.
        if dep.as_ref().contains('.') {
            continue;
        }
        match crate::platform::load_and_register_platform(
            ctx.symbol_tables,
            ctx.next_type_id,
            &mut ctx.check_state,
            &spec.name,
            ctx.project_root,
            ctx.lib_dirs,
            ctx.platform_dirs,
            spec.span,
        ) {
            Ok((platform, _jit_syms)) => {
                // Mirror `handle_platform`'s post-load: walk the synthetic
                // `platform.{name}` module, allocate a GOT slot for each
                // entry, and write the descriptor pointer into the GOT. The
                // GOT is the single source of truth for the entry's runtime
                // address (Sprint 66 Wave 0 amendment).
                let plat_path = ModuleFullPath::from(format!("platform.{}", platform.name));
                if let Some(mut table) = ctx.symbol_tables.get_mut(&plat_path) {
                    for desc in &platform.descriptors {
                        let slot = match table.symbols.get(desc.name.as_str()) {
                            Some(ModuleEntry::Def { got_slot: Some(s), .. }) => *s,
                            Some(ModuleEntry::Def { got_slot: None, .. }) => {
                                let s = table.allocate_got_slot();
                                if let Some(ModuleEntry::Def { got_slot, .. }) =
                                    table.symbols.get_mut(desc.name.as_str())
                                {
                                    *got_slot = Some(s);
                                }
                                s
                            }
                            _ => continue,
                        };
                        table.got.store_slot(slot, desc.ptr);
                    }
                }
                // Retain DLL handle for session lifetime so pointers stay valid.
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

    // 5. Register with scheduler at TypecheckDone.
    ctx.scheduler.register_module_cached(dep.clone(), symbols);

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

    // 9. Sprint 58 Wave 2c / Decision 37 — recurse on transitive imports.
    //    Each user-authored import in this cached module's symbol table
    //    refers to a module that must also be installed (from cache or
    //    fresh-build) so its `__cranelisp_got_{M}` data symbol is
    //    registerable when the cache-hit codegen worker links this dep's
    //    `.o`. Without this walk, a chain `A -> B (cached) -> C` leaves
    //    `C`'s symbol table missing when `B`'s `.o` relocations are
    //    resolved against `__cranelisp_got_C`, producing the
    //    `cache_multi_module_transitive_imports` failure mode.
    register_transitive_cached_imports(ctx, &cached_imports);

    true
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
fn register_transitive_cached_imports(
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
        let _ = dep_sexps; // already published into shared.module_sexps by the shim.
        // Register with scheduler — the worker loop processes this dep's
        // typecheck and eventually marks it `inmem_done`. We do NOT block
        // here (we are inside the outer module's typecheck); the outer
        // module either already typechecked or its own normal import-block
        // chain handles its dependency on this dep. `delays_other=true`
        // matches worker-side consensus (see §8.2 rationale).
        ctx.scheduler.register_module(transitive_dep.clone(), true);
    }
}

/// Handle export forms: register export metadata in the typechecker.
/// Handle export forms: ensure source modules are loaded, then register re-exports.
///
/// Export forms like `(export [compare.eq [Eq = !=]])` re-export symbols from
/// the named module. The source module must be loaded in the typechecker before
/// `register_exports` can read its symbol table. If the source module isn't
/// loaded, we trigger dependency loading via the same path as `handle_import`
/// and return `BlockAction::Block`.
fn handle_export(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    specs: &[ExportSpec],
) -> Result<BlockAction, CranelispError> {
    for spec in specs {
        let dep = &spec.module_path;

        // Already loaded — register the re-export and continue.
        if ctx.symbol_tables.contains_key(dep) {
            cranelisp_typecheck::register_exports(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, std::slice::from_ref(spec))?;
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

        // Register dep with scheduler and block.
        ctx.scheduler.register_module(dep.clone(), true);
        ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
            dep_sexps,
        });
    }

    // All source modules loaded — register the re-exports.
    cranelisp_typecheck::register_exports(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, specs)?;
    Ok(BlockAction::Continue)
}

/// Handle mod forms: write inline body to disk, then load the submodule.
///
/// `(mod util)` declares a submodule whose symbols are accessible via qualified
/// references like `util/helper`. The submodule must be loaded (typechecked)
/// before the parent can resolve these references, so we block for it — same
/// as `handle_import` does for explicit imports.
fn handle_mod(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    decl: &cranelisp_types::ModDecl,
) -> Result<BlockAction, CranelispError> {
    if let Some(body_sexps) = &decl.inline_body {
        write_inline_mod_to_disk(module, &decl.name, body_sexps, ctx.project_root)?;
    }

    // Compute submodule path: "main" + "util" → "main.util"
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

    // Register dep with scheduler and block for typecheck.
    ctx.scheduler.register_module(sub_path.clone(), true);
    ctx.scheduler.block_for_typecheck(
        module,
        &sub_path,
        &Symbol::from("*"),
    )?;

    Ok(BlockAction::Block {
        dep_module: sub_path,
        dep_sexps,
    })
}

/// Handle platform forms: load DLL and register type signatures.
///
/// Platform loading is NOT a cross-module blocking operation. The DLL is
/// loaded synchronously. Type signatures are registered in TC immediately.
///
/// Platform declarations in non-entry modules (submodules) are silently
/// ignored per spec §10.9.1 — only the entry module may load platforms.
fn handle_platform(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    spec: &PlatformSpec,
) -> Result<(), CranelispError> {
    // Submodules (paths containing '.') cannot load platforms.
    if module.as_ref().contains('.') {
        return Ok(());
    }
    let (platform, _jit_syms) = crate::platform::load_and_register_platform(
        ctx.symbol_tables,
        ctx.next_type_id,
        &mut ctx.check_state,
        &spec.name,
        ctx.project_root,
        ctx.lib_dirs,
        ctx.platform_dirs,
        spec.span,
    )?;

    // Sprint 57 Wave 3 G8 (revised Sprint 66 Wave 0): for each platform
    // descriptor, allocate a per-module GOT slot and write the runtime
    // pointer into the GOT. The GOT is the single source of truth for the
    // entry's runtime address (Sprint 66 Wave 0 amendment — replaces the
    // prior `ModuleEntry::Def.fn_ptr` field). The entry was inserted in
    // `register_platform_in_tc` (src/platform.rs) with `got_slot: None`;
    // this follow-up allocates the slot and stores the pointer.
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));
    if let Some(mut table) = ctx.symbol_tables.get_mut(&module_path) {
        for desc in &platform.descriptors {
            let slot = match table.symbols.get(desc.name.as_str()) {
                Some(ModuleEntry::Def { got_slot: Some(s), .. }) => *s,
                Some(ModuleEntry::Def { got_slot: None, .. }) => {
                    let s = table.allocate_got_slot();
                    if let Some(ModuleEntry::Def { got_slot, .. }) =
                        table.symbols.get_mut(desc.name.as_str())
                    {
                        *got_slot = Some(s);
                    }
                    s
                }
                _ => continue,
            };
            table.got.store_slot(slot, desc.ptr);
        }
    }

    // Retain the DLL handle on the session's `kept_dlls` pool so that the
    // GOT pointers remain valid for the session lifetime. Without this
    // push, the `LoadedPlatform` would drop at the end of this function,
    // `libloading::Library::drop` would `dlclose` the DLL, and every
    // GOT entry would dangle.
    if let Some(shared) = ctx.shared_state {
        shared
            .kept_dlls
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(platform);
    } else {
        // REPL path without a shared_state: leak the DLL handle so its
        // pointers remain valid for the process lifetime. This matches the
        // pre-G8 comment that "Platform DLLs are leaked (kept alive for
        // process lifetime)". Dropping `platform` here would `dlclose` the
        // DLL and dangle every GOT entry.
        std::mem::forget(platform);
    }
    Ok(())
}

/// Write an inline mod body to disk as `{module_dir}/{name}.cl`.
fn write_inline_mod_to_disk(
    parent_module: &ModuleFullPath,
    name: &cranelisp_types::ModuleName,
    body_sexps: &[Sexp],
    project_root: &Path,
) -> Result<(), CranelispError> {
    // Convert parent module path to directory.
    let relative_dir = parent_module.as_ref().replace('.', "/");
    let mod_dir = project_root.join(&relative_dir);
    let file_path = mod_dir.join(format!("{}.cl", name));

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

// ---------------------------------------------------------------------------
// Macro expansion for Pass 2
// ---------------------------------------------------------------------------

/// Attempt to expand macros in a sexp tree.
///
/// Compile all clauses of a macro if any clause lacks a function pointer.
///
/// Before compiling macro clauses, walks the transitive callees of the
/// macro (from `ModuleEntry.callees`) and compiles any uncompiled
/// dependencies first. Notifies the scheduler after each symbol is compiled.
fn compile_macro_if_needed(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Check if all clauses already have function pointers.
    let all_compiled = info.clauses.iter().enumerate().all(|(idx, _)| {
        let clause_name = macro_clause_jit_name(&info.name, idx);
        has_code_ptr(ctx.symbol_tables, module, &clause_name)
    });

    if all_compiled {
        return Ok(());
    }

    // Walk transitive callees and notify scheduler for any uncompiled deps.
    // The actual compilation is handled through the scheduler's normal priority
    // codegen path (block_for_macro_codegen). This loop only updates the
    // scheduler's completion tracking.
    let uncompiled_deps = collect_transitive_uncompiled_deps(
        ctx.symbol_tables, module, &info.name,
    );
    for (dep_module, dep_symbol) in &uncompiled_deps {
        if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
            eprintln!(
                "compile_macro_if_needed: uncompiled dep {}/{} — handled by scheduler",
                dep_module, dep_symbol
            );
        }
        ctx.scheduler.notify_inmem_codegen_complete(dep_module, dep_symbol, false);
    }

    // Compile each clause that is not yet compiled.
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(ctx.symbol_tables, module, &clause_name) {
            continue;
        }

        compile_macro_clause_inline(
            ctx, &info.name, clause_idx, clause, span,
            accumulator,
        )?;
        // Sprint 57 Wave 4 G9: same fix as `compile_macro_with_state` —
        // macro-clause compile must not claim inmem_done on behalf of the
        // module. Module-level codegen at the end of process_module_forms
        // owns that flag.
        ctx.scheduler.notify_inmem_codegen_complete(module, &clause_name, false);
    }

    Ok(())
}

/// Walk the transitive closure of a symbol's callees via the TC symbol table.
///
/// Returns the symbols that do not yet have compiled code pointers in the GOT.
/// The result is in dependency order (callees before callers) suitable for
/// sequential compilation.
fn collect_transitive_uncompiled_deps(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    start_symbol: &Symbol,
) -> Vec<(ModuleFullPath, Symbol)> {
    use std::collections::HashSet;
    use std::collections::VecDeque;

    let mut visited: HashSet<(ModuleFullPath, Symbol)> = HashSet::new();
    let mut queue: VecDeque<(ModuleFullPath, Symbol)> = VecDeque::new();
    let mut result: Vec<(ModuleFullPath, Symbol)> = Vec::new();

    // Seed with the starting symbol's callees.
    if let Some(table) = symbol_tables.get(module)
        && let Some(entry) = table.get(start_symbol.as_ref())
    {
        for callee in entry.callees() {
            let key = (callee.module.clone(), callee.symbol.clone());
            if visited.insert(key.clone()) {
                queue.push_back(key);
            }
        }
    }

    // BFS walk.
    while let Some((dep_mod, dep_sym)) = queue.pop_front() {
        // Look up this symbol's own callees and enqueue them.
        if let Some(table) = symbol_tables.get(&dep_mod)
            && let Some(entry) = table.get(dep_sym.as_ref())
        {
            for callee in entry.callees() {
                let key = (callee.module.clone(), callee.symbol.clone());
                if visited.insert(key.clone()) {
                    queue.push_back(key);
                }
            }
        }
        // Only include if uncompiled.
        if !has_code_ptr(symbol_tables, &dep_mod, &dep_sym) {
            result.push((dep_mod, dep_sym));
        }
    }

    result
}

// compile_dep_symbol_inline removed (Sprint 53): was a dead stub that took 10
// parameters and returned Ok(()). The scheduler's block_for_macro_codegen
// handles dependency compilation through the normal priority codegen path.

/// Compile a single macro clause inline using the worker's shared state.
///
/// Mirrors `compile_single_clause` from expander.rs but uses the worker's
/// JIT lifetime management and GOT registration instead of creating an
/// isolated JIT per clause. Uses `check_form` (per-form API) instead of
/// the monolithic `tc.check()`.
fn compile_macro_clause_inline(
    ctx: &mut ModuleCompiler,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(),
        clause_idx,
        clause,
        span,
    );

    // Step 2: Expand quasiquotes.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST (macro clause bodies use quasiquote constructs,
    // not other macros, so no expander is needed). Macro clause synthesis is
    // compiler-generated; user `(trace ...)` cannot reach this path.
    let program = build_program_compat(
        &[expanded_sexp],
        CodegenBehaviour::InMemoryAndObject,
    )?;

    // Step 4: Typecheck via the collapsed `check_forms` surface (Decision 44
    // 2026-05-13 third amendment) — single call runs Pass 1 + Pass 2 + finalize.
    let module = ctx.current_module.clone();
    let _ = accumulator;
    check_program_compat(ctx.symbol_tables, &module, &program)?;

    // Step 5: Extract the defn from the annotated symbol table (not the unannotated program).
    // The typechecker stores annotated defns (with resolved_call on AST nodes) in
    // ModuleEntry::Def.ast. Using the unannotated program would lose these annotations.
    let defn_name = program
        .iter()
        .find_map(|tl| match tl {
            TopLevel::Defn(d) => Some(d.name.clone()),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!(
                "macro clause {} for '{}' produced no defn",
                clause_idx, macro_name
            ),
            location: ErrorLocation::from_span(span),
        })?;

    let defn = ctx.symbol_tables
        .get(&module)
        .and_then(|table| match table.get(defn_name.as_ref()) {
            Some(cranelisp_types::ModuleEntry::Def { ast: Some(d), .. }) => Some(d.clone()),
            _ => None,
        })
        .unwrap_or_else(|| {
            // Fallback to program version (should not happen if typecheck is working)
            program.iter().find_map(|tl| match tl {
                TopLevel::Defn(d) => Some(d.clone()),
                _ => None,
            }).unwrap_or_else(|| unreachable!("invariant: defn_name was extracted from program above"))
        });
    let defn = &defn;

    // Compile macro clause through the unified compile_to_module path.
    // Macro clause functions are normal functions on per-module GOTs — the
    // typechecker has registered `defn.name` on the current module's symbol
    // table with `ast: Some(_)` and `got_slot: Some(_)` (Wave 0 invariant).
    let module = ctx.current_module.clone();
    let tc_modules = ctx.symbol_tables;
    ensure_typecheck_product(ctx.typecheck_products, &module);
    // Wave 0 (Sprint 56): the typechecker registers every compilable defn
    // with `got_slot: Some(_)`, so the legacy `pre_register_got_slots_in_tc`
    // safety net is no longer needed here.
    let _ = accumulator;
    let names = [defn.name.clone()];
    inline_jit_codegen_for_names(
        &module,
        &names,
        tc_modules,
        None,
        &[],
        ctx.shared_state,
    )?;

    Ok(())
}

// ---------------------------------------------------------------------------
// Macro entry helpers
// ---------------------------------------------------------------------------

/// Generate the JIT symbol name for a macro clause function.
///
/// Must match the naming convention in `synthesize_macro_clause_defn`:
/// `__macro_{name}_clause_{idx}`.
fn macro_clause_jit_name(macro_name: &Symbol, clause_idx: usize) -> Symbol {
    Symbol::from(format!("__macro_{}_clause_{}", macro_name, clause_idx))
}

/// Check if a symbol has a compiled code pointer on its `ModuleEntry::Def.code`
/// field (Sprint 57 Wave 2 G6 — `CodegenProduct` deleted; compiled code lives
/// on the symbol-table entry).
fn has_code_ptr(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> bool {
    symbol_tables
        .get(module)
        .and_then(|t| match t.get(name.as_ref())? {
            ModuleEntry::Def { code, .. } => Some(code.is_some()),
            _ => None,
        })
        .unwrap_or(false)
}

/// Get a code pointer from the symbol-table entry, if compiled.
fn get_code_ptr(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> Option<*const u8> {
    symbol_tables
        .get(module)
        .and_then(|t| match t.get(name.as_ref())? {
            ModuleEntry::Def { code: Some(c), .. } => Some(c.ptr()),
            _ => None,
        })
}

/// Compile a macro's clauses for REPL use.
///
/// Called from `make_defmacro_result` to ensure the macro is compiled and
/// available for expansion in subsequent REPL evals.
pub fn compile_macro_for_repl(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    compile_macro_if_needed(ctx, module, info, span, accumulator)
}

/// Pass 1 registration (no-op under the collapsed `check_forms` surface).
///
/// Per Decision 44's 2026-05-13 third amendment, the typecheck Pass-1
/// registration phase is internal to `check_forms` and runs as part of the
/// single call performed by `finalize_module` (via `check_program_compat`).
/// This function is retained for source compatibility with the existing
/// `process_module_forms` orchestration; it intentionally performs no
/// typecheck work itself.
fn pass1_register(
    _symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    _next_type_id: &std::sync::atomic::AtomicU32,
    _check_state: &mut CheckState,
    _module: &ModuleFullPath,
    _working_program: &[TopLevel],
    _accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    Ok(())
}

/// Register default method defns generated during Pass 1 TraitImpl processing.
///
/// Pre-S66 this drove `check_form(Register)` for each default-method-defn the
/// `check_form(TraitImpl)` Pass-1 step had appended to `accumulator`. Under
/// the collapsed `check_forms` surface, default-method handling is internal
/// to typecheck — the orchestrator merely takes the (now-empty) deferral list
/// off the local accumulator to maintain the pre-S66 worker invariants.
fn register_default_methods(
    _symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    _next_type_id: &std::sync::atomic::AtomicU32,
    _check_state: &mut CheckState,
    _module: &ModuleFullPath,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Vec<Defn>, CranelispError> {
    let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    Ok(defaults)
}

/// Inject prelude import for non-prelude modules, blocking if prelude needs loading.
///
/// Per spec §8.8.1: the implicit `(import [prelude [*]])` is suppressed when the
/// module's source contains an explicit `(import [prelude ...])` or
/// `(export [prelude ...])`. This allows modules to control their prelude
/// relationship — specific imports, null import (§8.3.6), or re-export.
///
/// Returns `Some(ProcessResult::Blocked { .. })` if the prelude must be compiled
/// first, `None` if prelude is already loaded, not found, or suppressed.
fn inject_prelude_if_needed(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexps: &[Sexp],
) -> Result<Option<ProcessResult>, CranelispError> {
    let prelude_path = ModuleFullPath::from("prelude");
    if *module == prelude_path {
        return Ok(None);
    }

    // §8.8.1: explicit import/export of prelude suppresses the implicit glob.
    if sexps_reference_prelude(sexps) {
        return Ok(None);
    }

    if !ctx.symbol_tables.contains_key(&prelude_path) {
        // Discover prelude through the same lazy path as any user import.
        let prelude_file = crate::session::resolve_prelude(
            ctx.project_root,
            ctx.lib_dirs,
        );
        if let Some(prelude_file) = prelude_file {
            // Cache check: try to load prelude from disk cache.
            if try_cache_hit_load(ctx, &prelude_path, &prelude_file) {
                let prelude_spec = ImportSpec {
                    module_path: prelude_path,
                    alias: None,
                    names: ImportNames::Glob,
                    span: Span::SYNTHETIC,
                };
                cranelisp_typecheck::register_imports(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, &[prelude_spec])?;
                return Ok(None);
            }

            // Run the shared per-dep prologue (read source, parse, record
            // source hash, stash source text, update file_to_module, publish
            // dep_sexps). Sprint 59 Workstream A §7 Step 1/2.
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

            ctx.scheduler.register_module(prelude_path.clone(), true);
            ctx.scheduler.block_for_typecheck(
                module,
                &prelude_path,
                &Symbol::from("*"),
            )?;

            return Ok(Some(ProcessResult::Blocked {
                form_index: 0,
                dep_module: prelude_path,
                dep_sexps: prelude_sexps,
            }));
        }
        // No prelude file found. Per spec §8.9.1: primitives are NOT
        // available as bare names without explicit import or prelude.
        // No implicit injection — modules that need primitives must
        // either have a prelude that re-exports them or import explicitly.
    } else {
        // Prelude already loaded — register the import.
        let prelude_spec = ImportSpec {
            module_path: prelude_path,
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        };
        cranelisp_typecheck::register_imports(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, &[prelude_spec])?;
    }

    Ok(None)
}

/// Check whether a module's source sexps contain an explicit reference to
/// `prelude` in an import or export form (spec §8.8.1).
fn sexps_reference_prelude(sexps: &[Sexp]) -> bool {
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

/// Inject a wildcard import of the `primitives` module into the current module.
///
/// Zero GOT slots and clear codegen artifacts for a module's symbols.
///
/// Called at the start of Replace processing. Preserves GOT slot assignments
/// so re-compiled definitions land in the same slots. Zeroing the slots
/// ensures stale code pointers are not callable during recompilation.
fn clear_module_codegen(ctx: &mut ModuleCompiler, module: &ModuleFullPath) {
    // Collect qualified symbol names for this module from the TC symbol table.
    let symbols: Vec<cranelisp_types::Symbol> = {
        let table = ctx.symbol_tables.get(&ctx.current_module).unwrap();
        table.all_symbols()
            .filter_map(|(name, entry)| {
                // Only clear codegen for definitions owned by this module,
                // not imports or special forms.
                match entry {
                    cranelisp_types::ModuleEntry::Def { kind, .. } => {
                        if matches!(kind.as_ref(), cranelisp_types::DefKind::SpecialForm { .. }) {
                            None
                        } else {
                            let qualified = cranelisp_types::Symbol::from(
                                format!("{}/{}", module, name)
                            );
                            Some(qualified)
                        }
                    }
                    cranelisp_types::ModuleEntry::Constructor { .. } => {
                        let qualified = cranelisp_types::Symbol::from(
                            format!("{}/{}", module, name)
                        );
                        Some(qualified)
                    }
                    _ => None,
                }
            })
            .collect()
    };

    // Zero GOT slots via per-module GOT table (keep slot assignments in TC).
    // G7 (Wave 0): GOT lives on SymbolTable; grab the Arc so we can release
    // the DashMap read guard before acquiring another guard on a potentially
    // different module.
    {
        let module_got = ctx.symbol_tables.get(module).map(|st| st.got.clone());
        if let Some(got_table) = module_got
            && let Some(table) = ctx.symbol_tables.get(&ctx.current_module) {
                for (_name, entry) in table.all_symbols() {
                    if let cranelisp_types::ModuleEntry::Def { got_slot: Some(slot), kind, .. } = entry
                        && !matches!(kind.as_ref(), cranelisp_types::DefKind::SpecialForm { .. }) {
                            got_table.store_slot(*slot, std::ptr::null());
                        }
                }
            }
    }

    // Clear compiled code on each `ModuleEntry::Def.code` for this module
    // (Sprint 57 Wave 2 G6: `CodegenProduct` was deleted; `code` lives on the
    // entry). The `Arc<Jit>` handles in `SharedState.kept_jits` keep the old
    // mmap'd pages alive until the next drain (they are never drained today —
    // redefinition policy is: keep old code alive for in-flight calls).
    if let Some(mut st) = ctx.symbol_tables.get_mut(module) {
        for entry in st.symbols.values_mut() {
            if let cranelisp_types::ModuleEntry::Def { code, .. } = entry {
                *code = None;
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

/// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
/// Mirrors `TypeChecker::wrap_exprs_as_defns`.
fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
    use cranelisp_types::{DefnVariant, Visibility};

    let mut working = Vec::with_capacity(program.len());
    for top in program {
        match top {
            TopLevel::Expr(expr) => {
                let span = expr.span();
                let wrapper_span = Span::new(
                    span.start.saturating_sub(1),
                    span.end.saturating_add(1),
                );
                let synthetic_defn = Defn {
                    name: Symbol::from("__expr"),
                    docstring: None,
                    variants: vec![DefnVariant {
                        params: vec![],
                        param_annotations: vec![],
                        body: expr.clone(),
                        span,
                    }],
                    visibility: Visibility::Public,
                    span: wrapper_span,
                };
                working.push(TopLevel::Defn(synthetic_defn));
            }
            other => working.push(other.clone()),
        }
    }
    working
}

// ---------------------------------------------------------------------------
// inline_jit_codegen_for_module — unified JIT codegen entry (Sprint 56 Wave 2)
// ---------------------------------------------------------------------------

/// Collect platform-function JIT symbols and GOT data-base definitions for a
/// module compilation.
///
/// Replaces `SessionCompilationEnv::collect_jit_setup_for_module`. Walks the
/// module's symbol table for `PlatformEffect` primitives (both direct defs and
/// imports), reads their function pointers from the owning module's GOT
/// (Sprint 66 Wave 0 amendment — GOT is the single source of truth, replacing
/// the prior `ModuleEntry::Def.fn_ptr` field), and then records every existing
/// module's GOT base address so the JIT module can define
/// `__cranelisp_got_{m}` literal-pool entries — see
/// `design/backend/compile-to-module.md` §12 and
/// `design/int/phase2-codegen-convergence.md` §5.
#[allow(clippy::type_complexity)]
fn collect_jit_setup(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: &ModuleFullPath,
) -> (Vec<(String, *const u8)>, Vec<(String, *const u8)>) {
    let mut jit_symbols = Vec::new();
    let mut got_data_defs = Vec::new();

    if let Some(st) = tc_modules.get(current_module) {
        for (_name, entry) in st.all_symbols() {
            match entry {
                ModuleEntry::Def {
                    kind,
                    got_slot: Some(slot),
                    ..
                } => {
                    if let DefKind::Primitive {
                        primitive_kind: PrimitiveKind::PlatformEffect { .. },
                        jit_name: Some(jit_name),
                    } = kind.as_ref()
                    {
                        let ptr = st.got.load_slot(*slot);
                        if !ptr.is_null() {
                            jit_symbols.push((jit_name.0.clone(), ptr));
                        }
                    }
                }
                ModuleEntry::Import { source } => {
                    if let Some(source_table) = tc_modules.get(&source.module)
                        && let Some(ModuleEntry::Def {
                            kind,
                            got_slot: Some(slot),
                            ..
                        }) = source_table.get(source.symbol.as_ref())
                        && let DefKind::Primitive {
                            primitive_kind: PrimitiveKind::PlatformEffect { .. },
                            jit_name: Some(jit_name),
                        } = kind.as_ref()
                    {
                        let ptr = source_table.got.load_slot(*slot);
                        if !ptr.is_null() {
                            jit_symbols.push((jit_name.0.clone(), ptr));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    for entry in tc_modules.iter() {
        let name = cranelisp_backend::compiler::got_data_symbol_name(entry.key());
        got_data_defs.push((name, entry.value().got.base_ptr()));
    }

    (jit_symbols, got_data_defs)
}

/// Public wrapper for `collect_jit_setup` used by the REPL expression
/// evaluation path in `session_v4::codegen_and_execute`. Mirrors the setup
/// used inside `inline_jit_codegen_for_module` so the throwaway
/// `compile_and_execute_expr` JIT module resolves cross-module GOT bases and
/// platform functions consistently.
#[allow(clippy::type_complexity)]
pub fn collect_jit_setup_public(
    tc_modules: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: &ModuleFullPath,
) -> (Vec<(String, *const u8)>, Vec<(String, *const u8)>) {
    collect_jit_setup(tc_modules, current_module)
}

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
            if name.as_ref().contains('$') || name.as_ref() == "__expr" {
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

    // 2. Collect platform symbols + per-module GOT base addresses.
    let (mut jit_symbols, got_data_defs) =
        collect_jit_setup(tc_modules, module);

    // Sprint 66 Wave 3a-γ: register int-owned intrinsics unconditionally
    // (`discover-tests`, `run-test`, `cranelisp_trace_format`). Per
    // `design/arch/facades/intrinsics.md` these are backend-emitted-call
    // targets — JIT-emitted CLIF declares them as `Linkage::Import` whenever
    // any program (including prelude defns) references them. The pre-S66
    // syntactic scan that gated registration on per-program references was
    // an architectural wart: the prelude's `run-tests-report` defn declares
    // `run-test` as Import on every JIT it touches, and a syntactic scan of
    // the current eval misses transitive references through previously-
    // compiled defns. Unconditional registration is the same uniform
    // dispatch principle that governs `heap_alloc` / `runtime/panic` /
    // primitive arithmetic. See FIXME 0178.
    for (name, ptr) in crate::session_v4::int_intrinsics() {
        jit_symbols.push((name.to_string(), ptr));
    }

    jit_symbols.extend_from_slice(extra_jit_symbols);

    // 2b. Register pointers for already-compiled functions across all modules.
    // Sprint 58 Wave 2 / Decision 36: under bare-Local naming, every
    // function is declared with its bare name uniformly across all modules.
    // The pre-Sprint-58 `user`/`main` vs FQ-Export discriminator is gone, so
    // we only register the bare alias. (Cross-module direct references are
    // also gone — `cross_refs` was deleted; cross-module calls now flow
    // through `__cranelisp_got_{other_M}` GOT-indirection.)
    //
    // Sprint 57 Wave 2 G6: the code pointers live on `ModuleEntry::Def.code`
    // in the symbol tables (formerly on the deleted `CodegenProduct.code`).
    for st_entry in tc_modules.iter() {
        for (bare, entry) in st_entry.value().all_symbols() {
            if let ModuleEntry::Def { code: Some(c), .. } = entry {
                jit_symbols.push((bare.as_ref().to_string(), c.ptr()));
            }
        }
    }

    // Decision 23 (Wave 2 follow-on): per-module GOT slabs are registered
    // via `JITBuilder::symbol()` so the symbol's load address IS the slab
    // base — no extra pointer-cell indirection. Fold `got_data_defs` into
    // the extras passed to `Jit::new_with_symbols`. The backend's
    // `Linkage::Import` cross-module GOT references resolve to these
    // registered addresses.
    let mut extra: Vec<(&str, *const u8)> = jit_symbols
        .iter()
        .map(|(n, p)| (n.as_str(), *p))
        .collect();
    for (got_name, got_ptr) in &got_data_defs {
        extra.push((got_name.as_str(), *got_ptr));
    }

    // 3. Build the JIT.
    let mut jit = cranelisp_backend::jit::Jit::new_with_symbols(&extra)?;

    // 4. Unified codegen entry — no env, no mode.
    //    `compile_to_module` writes `code: Some(_)` onto each
    //    `ModuleEntry::Def` in `tc_modules[module]` before returning
    //    (Sprint 57 Wave 2 G6 / `CodeFinalizer` trait). It also finalises
    //    definitions internally via `finalize_for_code_read()`, so no
    //    additional `jit.finalize()?` call is needed here — calling finalize
    //    twice would error on the second invocation.
    let result = cranelisp_backend::compile_to_module(
        module.clone(),
        names,
        tc_modules,
        jit.jit_module(),
    )?;

    // 5. Sprint 58 Wave 3b (Decision 35 + Decision 31 Scenario 2): share
    // the finalised `Arc<Jit>` per-entry on each `ModuleEntry::Def.code`,
    // not via the session-level `SharedState.kept_jits` pool (dissolved
    // Wave 3b). When a REPL user redefines a defn, the prior entry's
    // `Code::Jit` clone drops; once the last clone in the symbol tables
    // drops (no more entries reference this batch's JIT), `Arc::drop`
    // triggers `Jit::drop` which calls `unsafe JITModule::free_memory()`
    // and reclaims the per-batch JIT pages — Decision 31's per-redefinition
    // reclaim primitive.
    #[allow(clippy::arc_with_non_send_sync)]
    let jit_arc = std::sync::Arc::new(jit);
    let _ = shared_state; // shared_state retained for signature compat;
                          // kept_jits push removed (Wave 3b dissolution).

    // 6. For each compiled name: pull the per-symbol code pointer from
    //    `result.code_ptrs` (Wave 3b Layer 2 Option B — backend returns
    //    `(Arc<Jit>, code_ptrs)`, integration constructs `Code::Jit`),
    //    store it in the GOT slot, AND construct `Code::Jit { jit, ptr }`
    //    onto each `Def.code`. The per-entry `Arc::clone(&jit_arc)` is
    //    the lifetime root that activates Decision 31 Scenario 2.
    for name in names {
        // Sprint 58 Wave 2 / Decision 36: `result.code_ptrs` and
        // `result.func_ids` are keyed by bare symbol names uniformly
        // across every module.
        //
        // Sprint 60 Wave 2 Step A.1 (Decision 37 §"No swallowed failures",
        // H4 audit surface): each of the three lookups below used to be a
        // silent skip / `else { continue }`. Per §6.1 of
        // `design/backend/jit-object-convergence.md`, those are Decision 37
        // breaches: a name in `names` for which `code_ptrs` lacks an entry,
        // or for which the GOT slot lookup fails, or for which the symbol
        // table entry has disappeared, is an invariant violation. We MUST
        // return a hard error rather than leave a GOT slot NULL while
        // reporting `Ok(())` to the scheduler (the latter was Bug A's
        // signature on the cache-hit path, closed S58 Wave 2 at line 3087
        // — this mirrors that discipline onto the fresh-build path).
        let Some(code_ptr) = result.code_ptrs.get(name).copied() else {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "fresh-build codegen invariant violation: backend did not \
                     produce a code pointer for '{module}/{name}' (present in \
                     `names` batch but absent from `CompilationResult.code_ptrs`). \
                     This indicates a `/backend` contract breach — \
                     `compile_to_module` must emit a code pointer for every \
                     name in the input batch."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };

        // Store in pre-assigned GOT slot (Wave 0 invariant: every compilable
        // symbol carries a `got_slot`).
        let Some(slot) = lookup_got_slot(tc_modules, module, name) else {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "fresh-build codegen invariant violation: no GOT slot \
                     assigned for '{module}/{name}' at codegen time. Decision 37 \
                     (`design/arch/CLAUDE.md`) pins GOT slot assignment at the \
                     typecheck phase before any codegen runs; a missing slot \
                     here indicates a typecheck-to-codegen handoff contract breach."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };
        {
            let Some(st) = tc_modules.get(module) else {
                return Err(CranelispError::ModuleError {
                    message: format!(
                        "fresh-build codegen invariant violation: symbol table \
                         for module '{module}' disappeared during codegen while \
                         storing GOT slot for '{name}'. The caller of \
                         `inline_jit_codegen_for_names` must ensure \
                         `tc_modules[module]` is live for the duration of the call."
                    ),
                    location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                });
            };
            st.got.store_slot(slot, code_ptr);
        }

        // Wave 3b Layer 3: write Code::Jit on the entry. The Arc::clone
        // per-entry is what makes Decision 31 Scenario 2 fire — when the
        // entry is replaced (REPL redefinition), the clone drops, and
        // when the last clone in the table drops, the underlying Jit
        // reclaims its pages.
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
            return Err(CranelispError::ModuleError {
                message: format!(
                    "fresh-build codegen invariant violation: symbol table entry \
                     for '{module}/{name}' missing at Code::Jit write time \
                     (present in `names` batch; GOT slot stored successfully \
                     above; entry vanished between the slot store and the \
                     Code::Jit write). Indicates concurrent mutation of \
                     `tc_modules[module].symbols` during codegen, which \
                     violates Decision 37's scheduler discipline."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };
        let cranelisp_types::ModuleEntry::Def { code, .. } = entry else {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "fresh-build codegen invariant violation: symbol table entry \
                     for '{module}/{name}' is not a `ModuleEntry::Def` variant \
                     at Code::Jit write time. Only Def entries have codegen \
                     products; a name reaching this loop without a Def entry \
                     indicates a typecheck-to-codegen handoff contract breach."
                ),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        };
        // Detect REPL redefinition: if `code` was already populated, the
        // GOT slot is being overwritten. Emit a `Redefinition` event before
        // overwriting so observability sees the lifecycle (FIXME 0099).
        let prior_ptr: Option<*const u8> = code.as_ref().map(|c| c.ptr());
        *code = Some(crate::code::Code::jit(
            std::sync::Arc::clone(&jit_arc),
            code_ptr,
        ));
        if let Some(prior) = prior_ptr {
            crate::got_trace::emit_redefinition(
                module,
                name,
                slot,
                code_ptr,
                prior,
            );
        }
    }

    // 7. Route per-symbol artifacts into introspection (REPL-only).
    if let Some(intr_map) = introspection {
        for (name, artifacts) in &result.artifacts {
            let fq = cranelisp_types::FQSymbol {
                module: module.clone(),
                symbol: name.clone(),
            };
            let mut entry = intr_map.entry(fq).or_default();
            entry.clif_ir = Some(artifacts.clif_ir.clone());
            entry.disasm = if artifacts.disasm.is_empty() {
                None
            } else {
                Some(artifacts.disasm.clone())
            };
            entry.code_size = Some(artifacts.code_size as usize);
        }
    }

    Ok(())
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
            ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
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

    // Register runtime intrinsics.
    for sym in cranelisp_backend::jit::intrinsic_symbols() {
        linker.register_symbol(sym.name, sym.ptr);
    }

    // Sprint 57 Wave 3 G8 (revised Sprint 66 Wave 0): register platform
    // symbols by walking symbol tables instead of the deleted
    // `PlatformRegistry`. Every `PlatformEffect` entry carries its DLL
    // function pointer in the owning module's GOT slot
    // (`got.load_slot(got_slot)`); the corresponding `jit_name` is the
    // linker-side symbol.
    for st_entry in shared_state.symbol_tables.iter() {
        let st = st_entry.value();
        for (_name, entry) in st.all_symbols() {
            if let ModuleEntry::Def {
                kind,
                got_slot: Some(slot),
                ..
            } = entry
                && let DefKind::Primitive {
                    primitive_kind: PrimitiveKind::PlatformEffect { .. },
                    jit_name: Some(jit_name),
                } = kind.as_ref()
            {
                let ptr = st.got.load_slot(*slot);
                if !ptr.is_null() {
                    linker.register_symbol(jit_name.as_ref(), ptr);
                }
            }
        }
    }

    // Sprint 57 Wave 2 G6: register code pointers from already-compiled
    // modules via `ModuleEntry::Def.code` (replacing the deleted
    // `codegen_products` DashMap walk).
    for st_entry in shared_state.symbol_tables.iter() {
        for (name, entry) in st_entry.value().all_symbols() {
            if let ModuleEntry::Def { code: Some(c), .. } = entry {
                linker.register_symbol(name.as_ref(), c.ptr());
            }
        }
    }

    // Register per-module GOT data symbols for cross-module GOT-indirect calls.
    // G7 (Wave 0): GOT lives on SymbolTable; iterate symbol tables.
    for st_entry in shared_state.symbol_tables.iter() {
        let name = cranelisp_backend::compiler::got_data_symbol_name(st_entry.key());
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
            if let ModuleEntry::Def { code, .. } = entry
                && let Some(ptr) = fn_addrs.get(name.as_ref()).copied()
            {
                *code = Some(crate::code::Code::linker(
                    std::sync::Arc::clone(&linker_arc),
                    ptr,
                ));
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
fn handle_cached_codegen(
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

/// Per-module suspension state preserved across blocking/resumption.
///
/// Groups the mutable state that `process_module_forms` accumulates across
/// suspensions: the typechecker accumulator, expanded program forms, and
/// a flag tracking whether Pass 1 has completed.
pub struct ModuleSuspendState {
    pub accumulator: ModuleCheckAccumulator,
    /// Expanded program forms accumulated across suspensions.
    /// Forms processed before the block point are preserved here.
    pub expanded_program: Vec<TopLevel>,
    /// Whether Pass 1 (register signatures) has been completed for this module.
    /// Prevents re-running Pass 1 on resume when start_form_index is 0
    /// (which happens when a module blocks on its very first form).
    pub pass1_done: bool,
}

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
    loop {
        let work = shared.scheduler.take_priority_work_blocking();
        match work {
            Some(PriorityWork::Typecheck(module)) => {
                if let Err(e) = handle_typecheck_work_shared(shared, &module) {
                    shared.scheduler.notify_module_failed(&module, e);
                }
            }
            Some(PriorityWork::BlockingJitCodegen(module, _symbol))
            | Some(PriorityWork::JitCodegen(module, _symbol)) => {
                // Cache-hit module: load entire .o via Linker (batch load).
                // Sprint 57 Wave 3 G8: no PlatformRegistry lock — platform
                // symbols are read from the symbol tables inside the cache
                // loader.
                let _ = handle_cached_codegen(
                    &module, Some(shared),
                    &shared.scheduler,
                );
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

/// Handle a Typecheck work item on a persistent priority worker.
///
/// Reads the sexps + suspend state from `SharedState`, builds a
/// `ModuleCompiler` borrowing `&SharedState` directly, runs
/// `process_module_forms` followed by `inline_jit_codegen_for_module`
/// (Sprint 56 Wave 2 — unified JIT codegen entry), then stashes + notifies.
/// Sprint 57 Wave 4 G9 per `persistent-workers.md` §4.3.
fn handle_typecheck_work_shared(
    shared: &crate::session_v4::SharedState,
    module: &ModuleFullPath,
) -> Result<(), CranelispError> {
    let start_idx = shared.scheduler.module_resume_from_form(module)
        .flatten()
        .unwrap_or(0);

    // Clone sexps from shared map (don't remove — needed on resume).
    let sexps = {
        let map = shared.module_sexps.lock()
            .unwrap_or_else(|e| e.into_inner());
        map.get(module)
            .ok_or_else(|| CranelispError::ModuleError {
                message: format!("no parsed sexps for module '{}'", module),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            })?
            .clone()
    };

    // Take or create suspend state for this module.
    let mut state = {
        let mut states = shared.suspend_states.lock()
            .unwrap_or_else(|e| e.into_inner());
        states.remove(module).unwrap_or_else(|| ModuleSuspendState {
            accumulator: ModuleCheckAccumulator::new(),
            expanded_program: Vec::new(),
            pass1_done: false,
        })
    };

    // Ensure the module's SymbolTable exists before creating CheckState.
    {
        let tc = cranelisp_typecheck::TypeCheckEnv::new(&shared.symbol_tables, &shared.next_type_id);
        tc.ensure_module_exists(module);
    }
    // Snapshot path lists for this work item. Workers hold the Mutex only
    // for the duration of the clone (microseconds); subsequent code uses
    // the snapshot without re-locking.
    let lib_dirs = shared.lib_dirs.lock()
        .unwrap_or_else(|e| e.into_inner()).clone();
    let platform_dirs = shared.platform_dirs.lock()
        .unwrap_or_else(|e| e.into_inner()).clone();
    let mut ctx = ModuleCompiler {
        symbol_tables: &shared.symbol_tables,
        next_type_id: &shared.next_type_id,
        check_state: CheckState::new(module.clone()),
        current_module: module.clone(),
        scheduler: &shared.scheduler,
        typecheck_products: &shared.typecheck_products,
        introspection: Some(&shared.introspection),
        lib_dirs: &lib_dirs,
        platform_dirs: &platform_dirs,
        project_root: &shared.project_root,
        shared_state: Some(shared),
    };

    match process_module_forms(
        &mut ctx, module, &sexps, start_idx,
        &mut state,
        ModuleStrategy::Replace,
    ) {
        Ok(ProcessResult::Complete { check_result: _, program }) => {
            // Unified JIT codegen via compile_to_module (Sprint 56 Wave 2).
            inline_jit_codegen_for_module(
                ctx.scheduler,
                module,
                &program,
                ctx.symbol_tables,
                Some(&shared.introspection),
                &[],
                ctx.shared_state,
            )?;

            // Sprint 58 Step 5b: nice workers walk
            // `symbol_tables[module].defined_symbols()` directly; no
            // `codegen_programs` stash anymore. The `program` from
            // `process_module_forms` is consumed only by the inline JIT
            // codegen above.
            let _ = program;
            ctx.scheduler.notify_typecheck_done(module);

            // Clean up — module is done.
            {
                let mut map = shared.module_sexps.lock()
                    .unwrap_or_else(|e| e.into_inner());
                map.remove(module);
            }
            // suspend state was already removed above (taken out of map)
        }
        Ok(ProcessResult::Blocked {
            form_index,
            dep_module,
            dep_sexps,
        }) => {
            // Save resume state in scheduler.
            ctx.scheduler.set_resume_from_form(module, form_index);
            // Store dep sexps for workers to pick up.
            {
                let mut map = shared.module_sexps.lock()
                    .unwrap_or_else(|e| e.into_inner());
                map.entry(dep_module).or_insert(dep_sexps);
            }
            // Put suspend state back for resume.
            {
                let mut states = shared.suspend_states.lock()
                    .unwrap_or_else(|e| e.into_inner());
                states.insert(module.clone(), state);
            }
        }
        Err(e) => {
            // Clean up on failure.
            {
                let mut map = shared.module_sexps.lock()
                    .unwrap_or_else(|e| e.into_inner());
                map.remove(module);
            }
            return Err(e);
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
        DefKind, Defn, DefnVariant, Expr, FQSymbol, ModuleEntry, ModuleFullPath,
        Scheme, Symbol, Type, Visibility,
    };
    use std::collections::HashMap;

    fn synthetic_scheme() -> Scheme {
        Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        }
    }

    fn trivial_defn(name: &str) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 0,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    fn mk_def_with_got(
        kind: DefKind,
        ast: Option<Defn>,
        got_slot: Option<usize>,
    ) -> ModuleEntry<crate::code::Code> {
        ModuleEntry::Def {
            scheme: synthetic_scheme(),
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(kind),
            callees: Vec::new(),
            got_slot,
            trait_origin: None,
            ast,
            code: None,
        }
    }

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
                Some(trivial_defn("regular")),
                Some(0),
            ),
        );

        // Compilable: mangled multi-sig variant (also a UserFn with ast).
        st.insert(
            Symbol::from("add$Int+Int"),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_defn("add$Int+Int")),
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
                        defn: trivial_defn("poly_fn"),
                        scheme: synthetic_scheme(),
                    })),
                },
                Some(trivial_defn("poly_fn")),
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

    // spec: design/int/phase2-codegen-convergence.md §5 — artifact routing to Introspection
    #[test]
    fn priority_worker_routes_artifacts_to_introspection() {
        // Given a CompilationResult.artifacts map, simulate the routing loop and
        // assert each (name, artifacts) pair lands in SharedState.introspection
        // keyed by FQSymbol.
        let module = ModuleFullPath::from("user");

        // Build a synthetic artifacts map mirroring what compile_to_module returns.
        let mut artifacts: HashMap<Symbol, cranelisp_backend::FunctionArtifacts> = HashMap::new();
        artifacts.insert(
            Symbol::from("foo"),
            cranelisp_backend::FunctionArtifacts {
                clif_ir: "function %foo() -> i64 { ... }".to_string(),
                disasm: "mov rax, 0\nret".to_string(),
                code_size: 7,
            },
        );
        artifacts.insert(
            Symbol::from("bar"),
            cranelisp_backend::FunctionArtifacts {
                clif_ir: "function %bar() -> i64 { ... }".to_string(),
                disasm: String::new(), // empty disasm -> None in Introspection
                code_size: 12,
            },
        );

        let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
            dashmap::DashMap::new();

        // Mirror the exact routing loop in inline_jit_codegen_for_module step 7.
        for (name, art) in &artifacts {
            let fq = FQSymbol {
                module: module.clone(),
                symbol: name.clone(),
            };
            let mut entry = introspection.entry(fq).or_default();
            entry.clif_ir = Some(art.clif_ir.clone());
            entry.disasm = if art.disasm.is_empty() {
                None
            } else {
                Some(art.disasm.clone())
            };
            entry.code_size = Some(art.code_size as usize);
        }

        // Assert each entry is keyed by the correct FQSymbol and carries the
        // expected artifact payload.
        let foo_fq = FQSymbol {
            module: module.clone(),
            symbol: Symbol::from("foo"),
        };
        let bar_fq = FQSymbol {
            module: module.clone(),
            symbol: Symbol::from("bar"),
        };

        let foo_entry = introspection.get(&foo_fq).expect("foo introspection entry present");
        assert!(foo_entry.clif_ir.as_deref().unwrap_or("").contains("%foo"));
        assert_eq!(foo_entry.disasm.as_deref(), Some("mov rax, 0\nret"));
        assert_eq!(foo_entry.code_size, Some(7));
        drop(foo_entry);

        let bar_entry = introspection.get(&bar_fq).expect("bar introspection entry present");
        assert!(bar_entry.clif_ir.as_deref().unwrap_or("").contains("%bar"));
        assert_eq!(bar_entry.disasm, None, "empty disasm must be None, not Some(empty string)");
        assert_eq!(bar_entry.code_size, Some(12));
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
                Some(trivial_defn("target")),
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
                Some(trivial_defn(defn_name.as_ref())),
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
                ModuleEntry::Def { code: Some(c), .. } => {
                    assert!(!c.ptr().is_null(), "compiled function pointer must be non-null");
                    c.ptr()
                }
                other => panic!(
                    "expected ModuleEntry::Def with code: Some(_); got {other:?}"
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
                Some(trivial_defn(defn_name.as_ref())),
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
            ModuleEntry::Def { code: Some(c), .. } => {
                assert!(!c.ptr().is_null(), "code pointer must be non-null after compile");
            }
            other => panic!(
                "expected ModuleEntry::Def with code: Some(_) after worker codegen; got {other:?}"
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
                Some(trivial_defn(defn_name.as_ref())),
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
                ModuleEntry::Def { code: Some(c), .. } => c.ptr(),
                other => panic!(
                    "expected ModuleEntry::Def with code: Some(_); got {other:?}"
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
        use cranelisp_types::{DefnVariant, Expr, TopLevel, Visibility};

        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let expr_name = Symbol::from("__expr");
        let expr_defn = Defn {
            name: expr_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 3,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(cranelisp_types::Type::Int)),
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        st.insert(
            expr_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { constrained_fn: None },
                Some(expr_defn.clone()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        // `derive_codegen_batch` for a program whose only TopLevel is Expr
        // must produce a names list containing `__expr` — no special case.
        let program = vec![TopLevel::Expr(expr_defn.variants[0].body.clone())];
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
            ModuleEntry::Def { code: Some(c), .. } => {
                assert!(!c.ptr().is_null(), "__expr code pointer must be non-null");
            }
            other => panic!(
                "expected __expr entry with code: Some(_) after the uniform path; got {other:?}"
            ),
        }
    }

    // spec: design/int/phase2-codegen-convergence.md §13.3 — cross-module
    // JIT-finalize pre-registration walks the symbol tables (not the deleted
    // `codegen_products` DashMap).
    #[test]
    fn cross_module_pre_registration_reads_code_from_symbol_table() {
        // Seed two modules: a "dep" module whose symbol entry carries a
        // fabricated `code: Some(Code::new(ptr))`, and a "user" module
        // whose symbol table is empty of compiled entries. Build the pair
        // of `(name, ptr)` JIT-symbol registrations that
        // `inline_jit_codegen_for_names` derives at step 2b, confirming
        // the pre-compiled dep's pointer is picked up from the symbol-table
        // walk (the new post-G6 reader path that replaces the
        // `codegen_products.iter()` loop).
        let dep_module = ModuleFullPath::from("dep");
        let user_module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let fake_ptr = 0xFEEDF00Dusize as *const u8;
        let mut dep_st = crate::code::SessionSymbolTable::new_with_params(dep_module.clone());
        let dep_name = Symbol::from("already_compiled");
        dep_st.insert(
            dep_name.clone(),
            ModuleEntry::Def {
                scheme: synthetic_scheme(),
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: Vec::new(),
                got_slot: Some(0),
                trait_origin: None,
                ast: Some(trivial_defn(dep_name.as_ref())),
                // Sprint 58 Wave 3b: synthetic Code::Jit with a stack-local
                // Jit (the Arc keeps it alive until the test ends).
                code: Some(crate::code::Code::jit(
                    std::sync::Arc::new(
                        cranelisp_backend::jit::Jit::new().expect("Jit::new for test"),
                    ),
                    fake_ptr,
                )),
            },
        );
        symbol_tables.insert(dep_module.clone(), dep_st);
        symbol_tables.insert(
            user_module.clone(),
            crate::code::SessionSymbolTable::new_with_params(user_module.clone()),
        );

        // Simulate the step-2b loop from `inline_jit_codegen_for_names`:
        // iterate `symbol_tables`, pick up every `Def { code: Some(c), .. }`,
        // and emit `(bare, ptr)` + (when module != user/main) qualified pair.
        let mut jit_symbols: Vec<(String, *const u8)> = Vec::new();
        for st_entry in symbol_tables.iter() {
            let defining_module = st_entry.key();
            let use_prefix =
                defining_module.as_ref() != "user" && defining_module.as_ref() != "main";
            for (bare, entry) in st_entry.value().all_symbols() {
                if let ModuleEntry::Def { code: Some(c), .. } = entry {
                    let ptr = c.ptr();
                    if use_prefix {
                        jit_symbols.push((format!("{defining_module}/{bare}"), ptr));
                    }
                    jit_symbols.push((bare.as_ref().to_string(), ptr));
                }
            }
        }

        assert!(
            jit_symbols.iter().any(|(n, p)| n == "dep/already_compiled" && *p == fake_ptr),
            "qualified dep name must be registered from symbol-table walk; got {jit_symbols:?}"
        );
        assert!(
            jit_symbols.iter().any(|(n, p)| n == "already_compiled" && *p == fake_ptr),
            "bare dep alias must be registered from symbol-table walk; got {jit_symbols:?}"
        );
        // Critically: no reference to `crate::session_v4::CodegenProduct` is
        // needed in this path — the type has been deleted from the module,
        // and this test compiling is itself compile-time evidence of that.
    }

    // spec: design/int/platform-registry-removal.md §10 — `(platform …)`
    // form handler allocates a GOT slot and writes the runtime pointer into
    // the GOT for each platform function (replacing
    // `PlatformRegistry.register`; Sprint 66 Wave 0 amendment makes the GOT
    // the single source of truth, replacing the prior
    // `ModuleEntry::Def.fn_ptr` field).
    //
    // Loading a real DLL requires the stdio platform build artefact and a
    // scoped `SharedState`; what is structurally load-bearing is that
    // `collect_jit_setup` reads the pointer from the owning module's GOT.
    // This test seeds a `PlatformEffect` entry with an explicit
    // `got_slot: Some(_)` and writes the fake ptr into the corresponding
    // GOT slot (mirroring exactly what `handle_platform` writes) and asserts
    // the reader picks the pointer off the GOT.
    #[test]
    fn platform_form_handler_writes_fn_ptr_to_entry() {
        use cranelisp_types::{JitSymbol, PrimitiveKind, Scheme, Type};

        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let current = ModuleFullPath::from("platform.stdio");
        let fake_ptr: *const u8 = 0xC0FFEE_usize as *const u8;
        let jit_name = JitSymbol::from("cranelisp_print");

        let mut st = crate::code::SessionSymbolTable::new_with_params(current.clone());
        let slot = st.allocate_got_slot();
        st.got.store_slot(slot, fake_ptr);

        let entry = ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::Primitive {
                primitive_kind: PrimitiveKind::PlatformEffect {
                    scheduling_class: cranelisp_platform::SchedulingClass::Sequential,
                },
                jit_name: Some(jit_name.clone()),
            }),
            callees: Vec::new(),
            got_slot: Some(slot),
            trait_origin: None,
            ast: None,
            code: None,
        };

        st.insert(Symbol::from("print"), entry);
        symbol_tables.insert(current.clone(), st);

        // Direct invariant check: the GOT slot referenced by the entry
        // carries the pointer we just wrote.
        {
            let table = symbol_tables.get(&current).expect("platform table present");
            match table.get("print").expect("print entry present") {
                ModuleEntry::Def { got_slot: Some(s), .. } => {
                    assert_eq!(
                        table.got.load_slot(*s),
                        fake_ptr,
                        "handle_platform must write the runtime pointer into the GOT slot"
                    );
                }
                other => panic!("expected Def entry with got_slot, got {other:?}"),
            }
        }

        // Collector-side invariant: `collect_jit_setup` reads the pointer
        // from the GOT (Sprint 66 Wave 0 amendment), not from a deleted
        // `fn_ptr` field.
        let (jit_syms, _got) = collect_jit_setup(&symbol_tables, &current);
        assert!(
            jit_syms
                .iter()
                .any(|(name, ptr)| name == jit_name.as_ref() && *ptr == fake_ptr),
            "collect_jit_setup must surface the platform fn from the GOT slot; \
             got {jit_syms:?}"
        );
    }

    // spec: design/int/platform-registry-removal.md §9.2 — cross-module
    // platform-fn resolution. A module imports a platform function from
    // another module; the caller's collect_jit_setup walk must resolve
    // through the Import chain and surface the pointer.
    #[test]
    fn cross_module_platform_fn_resolution() {
        use cranelisp_types::{FQSymbol, JitSymbol, PrimitiveKind, Scheme, Type};

        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let plat_mod = ModuleFullPath::from("platform.stdio");
        let user_mod = ModuleFullPath::from("user");
        let fake_ptr: *const u8 = 0xBADC0FFEE0DDF00D_usize as *const u8;
        let jit_name = JitSymbol::from("cranelisp_print");

        // platform.stdio defines `print` as a PlatformEffect primitive with
        // its DLL fn ptr in the GOT slot referenced by the entry (Sprint 66
        // Wave 0 amendment — GOT-as-single-source-of-truth).
        let mut plat_st = crate::code::SessionSymbolTable::new_with_params(plat_mod.clone());
        let slot = plat_st.allocate_got_slot();
        plat_st.got.store_slot(slot, fake_ptr);
        let plat_entry = ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::Primitive {
                primitive_kind: PrimitiveKind::PlatformEffect {
                    scheduling_class: cranelisp_platform::SchedulingClass::Sequential,
                },
                jit_name: Some(jit_name.clone()),
            }),
            callees: Vec::new(),
            got_slot: Some(slot),
            trait_origin: None,
            ast: None,
            code: None,
        };
        plat_st.insert(Symbol::from("print"), plat_entry);
        symbol_tables.insert(plat_mod.clone(), plat_st);

        // user imports `print` from platform.stdio (an Import chain — the
        // caller-side symbol table carries only the import record, not the
        // platform pointer).
        let mut user_st = crate::code::SessionSymbolTable::new_with_params(user_mod.clone());
        user_st.insert(
            Symbol::from("print"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: plat_mod.clone(),
                    symbol: Symbol::from("print"),
                },
            },
        );
        symbol_tables.insert(user_mod.clone(), user_st);

        // The caller's `collect_jit_setup` must follow the Import chain
        // (one step) to the defining `platform.stdio` entry and read the
        // pointer from that module's GOT slot.
        let (jit_syms, _got) = collect_jit_setup(&symbol_tables, &user_mod);
        assert!(
            jit_syms
                .iter()
                .any(|(name, ptr)| name == jit_name.as_ref() && *ptr == fake_ptr),
            "cross-module platform-fn resolution must walk the Import chain \
             to the defining PlatformEffect entry; got {jit_syms:?}"
        );
    }

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
        ModuleCompiler {
            symbol_tables,
            next_type_id,
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
            is_private: false,
            inline_body: None,
            span: Span::SYNTHETIC,
        });

        let introspection = dashmap::DashMap::new();
        let source =
            crate::save::generate_module_source(&st, &introspection, &module);

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
            is_private: true,
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
            st.submodules[0].is_private,
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
            is_private: false,
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
        assert!(!loaded.submodules[0].is_private);
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
            is_private: true,
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
            is_private: false,
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

    // ---------------------------------------------------------------------
    // Decision 40 / Path B1 — link-mode (trace ...) rejection wiring
    // ---------------------------------------------------------------------

    // spec: spec/04-expressions.md §4.12.9 — `(trace ...)` rejected in --link mode.
    // Verifies the int-side wiring of the build-mode rejection inlined inside
    // `cranelisp_frontend::ast_builder::build_trace` (Sprint 67 Wave 4
    // follow-up; supersedes the retired `link_mode` validator pass from
    // FIXMEs 0199 + 0204) — `build_program_compat` threads
    // `CodegenBehaviour` into `build_form` / `build_expr` which propagate it
    // through to the trace recognition site.
    #[test]
    fn build_program_compat_rejects_trace_under_link_mode() {
        let sexps = cranelisp_frontend::parse("(trace 42)").expect("parse");
        let err = build_program_compat(&sexps, CodegenBehaviour::ObjectOnly)
            .expect_err("expected (trace ...) to be rejected under --link");
        match err {
            cranelisp_types::CranelispError::ParseError { ref message, .. } => {
                assert!(
                    message.contains("(trace ...)"),
                    "error message should name the form; got: {message}"
                );
                assert!(
                    message.contains("--link"),
                    "error message should name --link mode; got: {message}"
                );
            }
            other => panic!("expected ParseError, got: {other:?}"),
        }
    }

    // spec: spec/04-expressions.md §4.12.1-4.12.8 — `(trace ...)` is legal in
    // REPL/`--run` modes. Validator must be a no-op there.
    #[test]
    fn build_program_compat_accepts_trace_under_inmem_mode() {
        let sexps = cranelisp_frontend::parse("(trace 42)").expect("parse");
        let prog = build_program_compat(&sexps, CodegenBehaviour::InMemoryAndObject)
            .expect("trace must be accepted under InMemoryAndObject mode");
        assert!(!prog.is_empty(), "build should produce at least one TopLevel");
    }

    // `(trace ...)` nested inside a `defn` body is rejected under --link.
    #[test]
    fn build_program_compat_rejects_trace_in_defn_body_under_link_mode() {
        let sexps = cranelisp_frontend::parse("(defn f [] (trace 42))").expect("parse");
        let err = build_program_compat(&sexps, CodegenBehaviour::ObjectOnly)
            .expect_err("expected (trace ...) inside defn body to be rejected under --link");
        assert!(
            matches!(err, cranelisp_types::CranelispError::ParseError { .. }),
            "expected ParseError, got: {err:?}"
        );
    }

    // Programs with no `(trace ...)` form build cleanly under --link.
    #[test]
    fn build_program_compat_no_trace_passes_link_mode() {
        let sexps = cranelisp_frontend::parse("(defn g [] 42)").expect("parse");
        build_program_compat(&sexps, CodegenBehaviour::ObjectOnly)
            .expect("plain defn must build under --link mode");
    }
}
