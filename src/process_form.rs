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

use std::path::Path;

use cranelisp_types::{ErrorLocation,
    CranelispError, DefKind, Defn, ExportSpec, FQSymbol, ImportNames, ImportSpec,
    MacroClauseInfo, ModuleEntry, ModuleFullPath, ModuleStrategy,
    PlatformSpec, Sexp, Span, Symbol, TopLevel, Visibility,
};

use cranelisp_typecheck::CheckState;

use crate::expander::{self, MacroResolver};
use crate::scheduler::CompileScheduler;
use crate::worker::{
    ModuleCheckAccumulator, ModuleCompiler, ClusterOnce,
    build_program_compat, check_program_compat, check_program_compat_no_gap,
    ensure_typecheck_product, leading_annotation_len,
    inline_jit_codegen_for_names, handle_cached_codegen,
};

// ---------------------------------------------------------------------------
// SymbolTableMacroResolver — on-demand macro resolution from symbol tables
// ---------------------------------------------------------------------------

/// Recognition driver for the live in-place expansion walk
/// (`expand_sexp_recursive`).
///
/// `recognize` calls the LOCKED `cranelisp_types::resolve_macro_head` primitive
/// (via `expander::recognize_macro_head`) to recognize a macro head, then
/// ensures the recognized macro's clause code is in memory (on-demand inline
/// compile via `compile_macro_with_state`). Execution is NOT this resolver's
/// job — the walk runs the single `JitMacroExpander` over the returned `FQSymbol`
/// (S76 W-Macro, fire B; `macro-availability-model.md` §0.7).
///
/// Holds `&CheckState` (mut, for on-demand compilation) + the committed
/// symbol-table set + module aliases (for `resolve_macro_head`).
struct SymbolTableMacroResolver<'a> {
    /// Per-module symbol tables (DashMap, interior mutability).
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    /// Monotonic counter for fresh type variable IDs.
    next_type_id: &'a std::sync::atomic::AtomicU32,
    /// CheckState — needed for on-demand compilation (check_form_with_state).
    check_state: &'a mut CheckState,
    /// Current module path (starting point for symbol lookup).
    current_module: ModuleFullPath,
    /// Module-path aliases — fed to `resolve_macro_head` for qualified refs.
    module_aliases: &'a cranelisp_types::ModuleAliases,
    /// Per-module prelude-fallback bits — fed to `recognize_macro_head` so a
    /// prelude-provided macro (`cond`/`when`/`str`/…) is recognized from a user
    /// module via the implicit outer scope (S78 §2; public-only per I-1).
    prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
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
    /// FQ auto-loading (FIXME 0268, spec §9.3.6): set when `recognize`
    /// encounters an FQ macro head `mod/macro` whose `mod` is not yet loaded.
    /// `try_expand_sexp` reads this after the walk and signals the worker loop
    /// to load the dependency and resume the referencing form. `recognize`
    /// returns `Ok(None)` in this case (treats the head as an ordinary call for
    /// the duration of this aborted walk), so the captured module is the
    /// only signal that a block is needed.
    blocked_on_fq_module: Option<ModuleFullPath>,
}

impl MacroResolver for SymbolTableMacroResolver<'_> {
    fn symbol_tables(
        &self,
    ) -> &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
        self.symbol_tables
    }

    fn recognize(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<FQSymbol>, CranelispError> {
        // FQ auto-loading (FIXME 0268, spec §9.3.6): an FQ head `mod/macro`
        // whose `mod` is not yet loaded cannot be recognised as a macro yet —
        // `resolve_macro_head` would surface `QualifiedModuleUnknown`. Capture
        // the unloaded module so `try_expand_sexp` can signal the worker loop
        // to load it and resume; return `Ok(None)` for this aborted walk. The
        // module is loaded with import's file-resolution rules (orchestrator-
        // owned). Once loaded, the resumed walk recognises the macro normally.
        // A `:`-prefixed symbol is a TYPE ANNOTATION (`:Int`, `:primitives/Int`,
        // `:core.option/Option`), NOT a module-qualified value reference — it
        // must never be treated as an FQ-autoload candidate. Without this skip,
        // `:primitives/Int` splits into `mod_part = ":primitives"` and the
        // recogniser registers a bogus blocked FQ-module dep `:primitives`,
        // contaminating resolution (the field type then fails with
        // `unknown type 'primitives' (from module '')`). The sibling
        // `qualify_expanded_sexp` already guards this exact case (FIXME 0322).
        if !name.starts_with(':')
            && let Some((mod_part, _sym_part)) = name.split_once('/')
        {
            // Resolve the module part through the session alias table FIRST
            // (§8.6.6). A `(mod util)` declaration registers a short-name
            // alias `util -> <parent>.util` (and `(import [(target alias)])`
            // registers `<owner>.alias -> target`); the loaded module's
            // identity is its full path (§8.1), so the verbatim `mod_part`
            // need not be a stored module path. Substituting before the
            // contains-key check means a bare submodule qualified ref
            // (`util/helper`) loads/finds `<parent>.util` rather than hunting
            // a non-existent module literally named `util` (FIXME 0121).
            let dep = resolve_module_alias(self.module_aliases, mod_part);
            if !self.symbol_tables.contains_key(&dep) {
                self.blocked_on_fq_module = Some(dep);
                return Ok(None);
            }
        }

        // Step 1: RECOGNITION via the LOCKED types primitive
        // (`cranelisp_types::resolve_macro_head` over a committed `View`,
        // `macro-availability-model.md` §0.7). Zero int→typecheck dependency;
        // handles imports/reexports/aliases/visibility uniformly. A non-macro
        // or forward reference yields `Ok(None)` (head flows on as an ordinary
        // call per the locked defmacro-before-use rule).
        let fq = match expander::recognize_macro_head(
            self.symbol_tables,
            self.module_aliases,
            self.prelude_fallback,
            &self.current_module,
            name,
            span,
        )? {
            Some(fq) => fq,
            None => return Ok(None),
        };
        // The home module + canonical symbol the primitive resolved to. Read
        // the clause metadata directly from the canonical entry.
        let defining_module = fq.module.clone();
        let clauses = match read_macro_meta(self.symbol_tables, &fq) {
            Some((clauses, _docstring)) => clauses,
            None => return Ok(None),
        };

        // Record the defining module for post-expansion symbol qualification.
        if defining_module != self.current_module {
            self.macro_defining_modules.push(defining_module.clone());
        }

        // Step 2: Ensure the clause code is in memory (on-demand compile). The
        // executor (`JitMacroExpander::invoke`) reads clause code ptrs from the
        // GOT, so they must be compiled before the walk executes the macro.
        let all_compiled = clauses.iter().enumerate().all(|(idx, _)| {
            let clause_name = macro_clause_jit_name(&fq.symbol, idx);
            has_code_ptr(self.symbol_tables, &defining_module, &clause_name)
        });

        if !all_compiled {
            // Step 2a (S77 W-MacroTrait, FIXME 0299): cache-restore parity.
            //
            // When `defining_module` is an imported module restored from the
            // disk cache, `try_cache_hit_load` installs its symbol table at
            // `TypecheckDone` with `code: None` + empty GOT — the macro's
            // `DefKind::Macro` entry (recognised above) is present, but the
            // clause code's `.o` has not been linked into the GOT yet (that is
            // a separate deferred codegen step, `load_cached_module_via_linker`,
            // dispatched via the scheduler's cached-codegen work item). On a
            // fresh build the clause is JIT-codegened inline during the home
            // module's Pass 2, so it is already in memory; on cache-restore it
            // is not, and `resolve_macro_sexp_from` returns `None` because the
            // introspection record (the on-demand recompile source) is never
            // populated for a cache-restored module. Drive the cached codegen
            // synchronously here so the clause GOT slot is populated before the
            // executor reads it. This is the cross-module macro half of the
            // disk-cache gap noted in `src/CLAUDE.md` ("clause N is not in
            // memory") and is the RT5 root for `mode_equiv_macro_user_defined`
            // (repl_cached/run_cached) and the persist-restart macro tests.
            if defining_module != self.current_module
                && self.scheduler.cached_module_contains(&defining_module)
            {
                let _ = handle_cached_codegen(
                    &defining_module,
                    self.shared_state,
                    self.scheduler,
                );
                let now_compiled = clauses.iter().enumerate().all(|(idx, _)| {
                    let clause_name = macro_clause_jit_name(&fq.symbol, idx);
                    has_code_ptr(self.symbol_tables, &defining_module, &clause_name)
                });
                if now_compiled {
                    return Ok(Some(fq));
                }
            }

            // Step 3: Compile inline. We need DefmacroInfo to drive compilation;
            // read the macro's original sexp back from the symbol-table
            // `DefKind::Macro.macro_sexp` field (D1 ruling §6 — re-sourced off
            // the symbol table, not introspection; this is what makes the
            // cache-restored cross-module macro recompile here).
            //
            // S77 W-MacroTrait (FIXME 0299): the on-demand recompile is for
            // CROSS-MODULE macros only (an imported macro lives in a dependency,
            // always-available at expansion per `macro-availability-model.md`
            // §0.1). For a SAME-MODULE macro, a not-yet-compiled clause at the
            // point a use is recognised means the use precedes the `defmacro` in
            // source order — a FORWARD reference, which §0.2 (defmacro-before-use
            // is normative) REJECTS: the use is a plain unresolved reference, not
            // a macro call. Same-module backward uses never reach here, because
            // Pass 2's `compile_macro_if_needed` already JIT-compiled the clause
            // when it processed the (earlier) `defmacro` form. Guarding the
            // recompile to cross-module preserves the §0.2 rejection that
            // `macro_used_before_defmacro_is_unresolved_neg` asserts — without
            // the guard, the now-always-present symbol-table `macro_sexp` would
            // let a forward same-module use recompile its clause and expand,
            // silently hoisting the macro. The §0.2 guard (`defining_module !=
            // self.current_module`) stays load-bearing after the D1 re-sourcing.
            let macro_sexp = if defining_module != self.current_module {
                resolve_macro_sexp_from(self.symbol_tables, &defining_module, fq.symbol.as_ref())
            } else {
                None
            };
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
                // No sexp available to compile from. The clauses may already be
                // compiled by the batch Pass-2 path; recognition still succeeds
                // so the executor can attempt the GOT-resolved invoke (which
                // surfaces a clear `Aborted` if the code is genuinely absent).
                return Ok(Some(fq));
            }
        }

        Ok(Some(fq))
    }
}

/// Read a macro's clause metadata + docstring from its **already-resolved**
/// canonical entry. `fq` addresses the home module + canonical symbol that
/// `cranelisp_types::resolve_macro_head` chain-followed to (imports/aliases/
/// visibility already applied) — so this is a single direct lookup, no
/// chain-walk. Returns `None` when the entry is absent or not a `DefKind::Macro`
/// (a forward reference or a non-macro shadowing the name).
fn read_macro_meta(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    fq: &FQSymbol,
) -> Option<(Vec<MacroClauseInfo>, Option<String>)> {
    let table = symbol_tables.get(&fq.module)?;
    match table.get(fq.symbol.as_ref())? {
        ModuleEntry::Def { kind, docstring, .. }
            if matches!(kind.as_ref(), DefKind::Macro { .. }) =>
        {
            let DefKind::Macro { clauses_meta, .. } = kind.as_ref() else {
                unreachable!("invariant: guard matched DefKind::Macro");
            };
            Some((clauses_meta.clone(), docstring.clone()))
        }
        _ => None,
    }
}

/// Resolve a macro's original sexp for on-demand clause compilation.
///
/// D1 ruling (S80, `design/arch/d1-introspection-repl-only.md` §2/§6): the
/// macro's original `(defmacro …)` form is re-sourced from the **symbol table**
/// `DefKind::Macro.macro_sexp` field, NOT `SharedState.introspection`. This is
/// the load-bearing fix for **cache-restored** macros: introspection is a
/// REPL-only facility and is NEVER populated for a cache-restored module, so
/// the prior introspection read returned `None` for exactly the case this
/// recompile path serves (cross-module macro whose clause `.o` was not linked
/// inline). `macro_sexp` serializes (no `#[serde(skip)]`), so a cache-restored
/// macro entry carries it directly off the deserialized symbol table — no
/// rehydration step. FQ-autoloaded (fresh-build) macros populate it through the
/// normal `register_macro_in_module` register path before this runs.
///
/// Returns `None` when the entry is absent or is not a `DefKind::Macro` (a
/// forward reference or a non-macro shadowing the name).
fn resolve_macro_sexp_from(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    defining_module: &ModuleFullPath,
    name: &str,
) -> Option<Sexp> {
    let table = symbol_tables.get(defining_module)?;
    match table.get(name)? {
        ModuleEntry::Def { kind, .. } => match kind.as_ref() {
            DefKind::Macro { macro_sexp, .. } => Some(macro_sexp.clone()),
            _ => None,
        },
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
    let program = build_program_compat(&[expanded_sexp])?;

    // Step 4: Typecheck via the collapsed `check_forms` surface (Decision 44
    // 2026-05-13 third amendment). `check_program_compat` runs the internal
    // Pass 1 + Pass 2 + finalize sequence in one call. `check_state` /
    // `accumulator` are no longer threaded through the public typecheck
    // surface — they are vestigial parameters on this function (kept for
    // source-compat with pre-S66 callers).
    let _ = check_state;
    let _ = accumulator;
    let _ = next_type_id;
    // module_aliases lives on SharedState; this `_with_state` macro-clause path
    // is slated for deletion in the W-Macro Pass-1 rewrite (fire B). When
    // shared_state is absent (unit-test paths), an empty leaked alias map is a
    // safe stand-in (macro clause bodies do not use alias imports).
    let module_aliases: &cranelisp_types::ModuleAliases = match shared_state {
        Some(s) => &s.module_aliases,
        None => Box::leak(Box::new(cranelisp_types::ModuleAliases::default())),
    };
    // Same Option<&SharedState> handling as `module_aliases`: a macro clause
    // body does not use prelude bare-name fallback (its synthesised body uses
    // qualified `macros/*` refs), so an empty map (all-OFF) is a safe stand-in.
    let prelude_fallback: &cranelisp_typecheck::PreludeFallback = match shared_state {
        Some(s) => &s.prelude_fallback,
        None => Box::leak(Box::new(
            cranelisp_typecheck::PreludeFallback::default(),
        )),
    };
    check_program_compat_no_gap(
        symbol_tables,
        module_aliases,
        prelude_fallback,
        target_module,
        &program,
    )?;

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

    // Compile macro clause through the unified compile_to_module path.
    // Macro clause functions are normal functions on per-module GOTs — the
    // typechecker has registered `defn_name` on `target_module`'s symbol
    // table with `ast: Some(_)` and `got_slot: Some(_)` (Wave 0 invariant).
    // S69 Submission 35: `ModuleEntry::Def.ast` is now `DefnVariant` (no
    // `name` field); the codegen `names` array is keyed off the already-
    // extracted `defn_name`, so the prior `Defn` reconstruction is dropped.
    let tc_modules = symbol_tables;
    ensure_typecheck_product(typecheck_products, target_module);
    let _ = accumulator;
    let names = [defn_name.clone()];
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

/// Scope the resolver's borrows to just the expansion phase.
///
/// Creates a SymbolTableMacroResolver, runs expand_sexp_recursive,
/// drops the resolver, returns the expanded sexp. After this returns,
/// ctx and accumulator are available for the caller to use freely.
/// Outcome of attempting macro expansion on a single Pass-2 form.
enum ExpandOutcome {
    /// Expansion ran to fixpoint. `Some(sexp)` = expanded result (differs from
    /// input); `None` = no expansion (input was not a macro call).
    Expanded(Option<Sexp>),
    /// Expansion encountered an FQ macro head `mod/macro` whose module is not
    /// yet loaded (FIXME 0268). The caller loads `dep_module` and resumes the
    /// referencing form. No partial expansion is committed.
    BlockedOnFqModule(ModuleFullPath),
}

fn try_expand_sexp(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<ExpandOutcome, CranelispError> {
    // No need to extract/restore CheckState — TypeCheckEnv borrows are
    // separate from CheckState. The resolver holds &DashMap (from tc_env)
    // and &mut CheckState separately.
    let (result, defining_modules, blocked_on) = {
        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: ctx.symbol_tables,
            next_type_id: ctx.next_type_id,
            check_state: &mut ctx.check_state,
            current_module: module.clone(),
            module_aliases: ctx.module_aliases,
            prelude_fallback: ctx.prelude_fallback,
            typecheck_products: ctx.typecheck_products,
            accumulator,
            scheduler: ctx.scheduler,
            shared_state: ctx.shared_state,
            macro_defining_modules: Vec::new(),
            blocked_on_fq_module: None,
        };

        let r = expander::expand_sexp_recursive(sexp.clone(), &mut resolver, 0);
        let dms = std::mem::take(&mut resolver.macro_defining_modules);
        let blocked = resolver.blocked_on_fq_module.take();
        (r, dms, blocked)
        // resolver dropped here, releasing all borrows on check_state
    };

    // An FQ macro head named an unloaded module — signal the worker loop to
    // load it and resume (FIXME 0268). Surface this before propagating any
    // expansion error, since the aborted walk may itself have errored on the
    // unrecognised FQ head.
    if let Some(dep) = blocked_on {
        return Ok(ExpandOutcome::BlockedOnFqModule(dep));
    }

    let expanded = result?;

    if expanded == *sexp {
        Ok(ExpandOutcome::Expanded(None))
    } else {
        // Qualify bare symbols from defining modules (cross-module macro hygiene).
        let qualified = if defining_modules.is_empty() {
            expanded
        } else {
            qualify_expanded_sexp(ctx.symbol_tables, module, &defining_modules, expanded)
        };
        Ok(ExpandOutcome::Expanded(Some(qualified)))
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
                            ModuleEntry::Import { source, .. } => &source.module,
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

pub(crate) fn record_imports_on_symbol_table(
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

pub(crate) fn record_submodule_on_symbol_table(
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
                                &containing_module,
                                std::slice::from_ref(sexp),
                            )?;
                        Ok(FormKind::Import(decls.import_specs))
                    }
                    "export" => {
                        let (decls, _remaining) =
                            cranelisp_frontend::extract_module_declarations(
                                &containing_module,
                                std::slice::from_ref(sexp),
                            )?;
                        Ok(FormKind::Export(decls.export_specs))
                    }
                    "mod" | "mod-" => {
                        let (decls, _remaining) =
                            cranelisp_frontend::extract_module_declarations(
                                &containing_module,
                                std::slice::from_ref(sexp),
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
                                &containing_module,
                                std::slice::from_ref(sexp),
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

/// Signals the structural-peel (Pass 0) whether to continue or that a
/// dependency was registered + blocked on.
///
/// S78: the `Block` arm no longer carries `dep_sexps` — the structural
/// handler has already parsed the dep and handed its sexps to
/// `scheduler.register_module(dep, sexps, true)` (the sexps ride the dep's
/// work packet, not a shared `module_sexps` map). The handler has also called
/// `block_for_typecheck`, recording the register-edge. The caller
/// (`process_cluster_once`) returns `ClusterOnce::Gap { dep }`.
enum BlockAction {
    /// Continue processing the next form.
    Continue,
    /// A dependency was discovered, registered, and blocked on.
    Block {
        dep_module: ModuleFullPath,
    },
}

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

    if strategy == ModuleStrategy::Replace {
        // Set active module. Symbol table is preserved for slot reuse
        // and type-change detection.
        ctx.set_current_module(module.clone());

        // Zero GOT slots and clear codegen artifacts for this module's
        // symbols. Slot assignments are preserved so re-compiled code
        // lands in the same slots.
        clear_module_codegen(ctx, module);

        // Prelude injection: inject (import [prelude [*]]) for non-prelude
        // modules unless the source explicitly references prelude (§8.8.1).
        if let Some(dep) = inject_prelude_if_needed(ctx, module, sexps)? {
            return Ok(ClusterOnce::Gap { dep });
        }
    } else {
        // Additive (REPL eval): just set the active module. Module state
        // persists from previous evals — no clear, no re-injection.
        ctx.set_current_module(module.clone());

        // S78 §2.7 — the per-module prelude-fallback bit was set ON at the
        // entry module's startup compile. If a REPL form now explicitly
        // references prelude (`(import [prelude []])` refusal, or a selective
        // `(import [prelude [...]])`), the implicit fallback must turn OFF for
        // this module (spec §8.8.1) — matching the Replace-path gate. The bit
        // is OFF iff the module references prelude (absence-is-OFF).
        if sexps_reference_prelude(sexps) {
            ctx.prelude_fallback.insert(module.clone(), false);
        }
    }

    // --- Pass 0: structural-form peel (import/export/mod/platform) ---
    // Imported symbols must be in scope before pass1_register checks trait
    // impl bodies. An unloaded dep is registered + blocked on, and the cluster
    // retries from the top once it is live.
    for sexp in sexps.iter() {
        match classify_form(sexp, module)? {
            FormKind::Import(specs) => {
                record_imports_on_symbol_table(ctx, module, &specs);
                match handle_import(ctx, module, specs)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            FormKind::Export(specs) => {
                record_exports_on_symbol_table(ctx, module, &specs);
                match handle_export(ctx, module, &specs)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            FormKind::Mod(decl) => {
                record_submodule_on_symbol_table(ctx, module, &decl);
                match handle_mod(ctx, module, &decl)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            FormKind::Platform(spec) => {
                record_platform_on_symbol_table(ctx, module, &spec);
                match handle_platform(ctx, module, &spec)? {
                    BlockAction::Continue => {}
                    BlockAction::Block { dep_module } => {
                        return Ok(ClusterOnce::Gap { dep: dep_module });
                    }
                }
            }
            _ => {} // Regular, Defmacro — handled in Pass 1 / Pass 2.
        }
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
        register_macro_in_module(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, intr, module, name, info, sexp)?;
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
            finalize_cluster(
                ctx, module, &expanded_program, &mut accumulator,
            )
        }
        Pass2Result::BlockedOnFqModule { dep_module } => {
            // An FQ macro reference to an unloaded module surfaced during
            // expansion (Pass 2). Drive the dependency (register + block) with
            // import's file-resolution rules; the cluster retries from the top
            // once it is live (FIXME 0268).
            drive_module_dep(ctx, module, &dep_module, Span::SYNTHETIC)?;
            Ok(ClusterOnce::Gap { dep: dep_module })
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

    if let Some(gap) =
        check_program_compat(
            ctx.symbol_tables,
            ctx.module_aliases,
            ctx.prelude_fallback,
            module,
            &final_working,
        )?
    {
        // Map the gap to its target module and drive it (register + block) if
        // it is a not-yet-loaded module we can act on.
        if let Some(dep) = gap_target_module(&gap)
            && !fq_module_is_loaded(ctx, &dep)
        {
            drive_module_dep(ctx, module, &dep, Span::SYNTHETIC)?;
            return Ok(ClusterOnce::Gap { dep });
        }
        // The gap names a module that IS already loaded (or is not an
        // FQ-module gap we can act on) — surface it as a hard error so the
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
    // to live inside `check_program_compat`; introspection/warnings flow back
    // through the calling driver (REPL) / are empty (worker). The
    // `ProcessedCluster` carrier is committed via `cluster::insert_cluster`.
    let processed = crate::cluster::ProcessedCluster::empty();

    Ok(ClusterOnce::Done { processed, program })
}

/// Register a defmacro in the module table (Pass 1).
///
/// Parses clause info and stores it as `ModuleEntry::Macro` with the
/// original sexp for later compilation. No codegen — deferred until
/// first use.
#[allow(clippy::too_many_arguments)]
fn register_macro_in_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    _next_type_id: &std::sync::atomic::AtomicU32,
    _check_state: &mut CheckState,
    introspection: Option<&dashmap::DashMap<FQSymbol, crate::session_v4::Introspection>>,
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
        })
        .collect();
    let visibility = if info.is_private {
        Visibility::Private
    } else {
        Visibility::Public
    };
    // S70 macro-unification (W-Absorb): the macro parent is a
    // `ModuleEntry::Def` with `kind: DefKind::Macro { clauses_meta }` — no
    // callable address (`got_slot: None`), no AST. The `sexp` argument used to
    // ride on the entry; per Decision 41 macro `sexp` lives on the int-layer
    // `Introspection` record keyed by `FQSymbol`.
    //
    // S77 W-MacroTrait (FIXME 0299): route the macro sexp into Introspection
    // (REPL mode only — `introspection` is `Some` only when `--repl`). This is
    // the single source the macro round-trip needs in two places:
    //   1. `resolve_macro_sexp_from` — the on-demand clause recompile path
    //      (`SymbolTableMacroResolver::recognize` step 3) reads it back to
    //      rebuild the clause code when a recognised macro's GOT slot is empty.
    //   2. `crate::save::generate_module_source` — `regenerate_backing_file`
    //      writes the live session to `user.cl`; without the macro sexp the
    //      regenerated file silently DROPS every `defmacro`, so on a cached
    //      REPL restart a `(defn main [] (twice 21))` body fails with
    //      `undefined variable: twice`. This was the `mode_equiv_macro_user_
    //      defined` [repl_cached] + `persist_bug_macro_usage_in_defn` root.
    // Mirrors the regular-defn introspection population in `process_regular_form`
    // (worker.rs ~1670). Only sets `sexp`/`source` when absent so a later REPL
    // eval that captures the verbatim input text can still override `source`.
    if let Some(intr_map) = introspection {
        let fq = FQSymbol {
            module: module.clone(),
            symbol: name.clone(),
        };
        let mut entry = intr_map.entry(fq).or_default();
        if entry.sexp.is_none() {
            entry.sexp = Some(sexp.clone());
        }
        if entry.source.is_none() {
            entry.source = Some(crate::pretty::pretty_print(sexp));
        }
    }
    if let Some(mut table) = symbol_tables.get_mut(module) {
        // Macro parents carry no meaningful type scheme (not callable); use a
        // placeholder monomorphic scheme, as the legacy `ModuleEntry::Macro`
        // path effectively did (it had no scheme field at all).
        let placeholder_scheme = cranelisp_types::Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: cranelisp_types::Type::Int,
        };
        let mut builder = ModuleEntry::def(
            placeholder_scheme,
            DefKind::Macro {
                clauses_meta: clause_infos,
                // D1 ruling §2/§6: the macro's original `(defmacro …)` form is
                // compile-path data — it lives on the symbol-table entry, NOT
                // introspection (which is REPL-only and absent on cache
                // restore). Set UNCONDITIONALLY (all modes): the on-demand
                // clause recompile (`resolve_macro_sexp_from`) and the REPL
                // backing-file regeneration (`save::generate_module_source`)
                // both re-source it from here, and it serializes (no
                // `#[serde(skip)]`) so it round-trips the disk cache.
                macro_sexp: sexp.clone(),
            },
        )
        .visibility(visibility);
        if let Some(doc) = &info.docstring {
            builder = builder.docstring(doc.clone());
        }
        table.insert(name.clone(), builder.build());
    }
    Ok(())
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
            register_macro_in_module(ctx.symbol_tables, ctx.next_type_id, &mut ctx.check_state, intr, module, &info.name, &info, &form)?;
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
    Ok(None)
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
            crate::imports::install_imports(ctx.symbol_tables, &ctx.current_module, ctx.module_aliases, std::slice::from_ref(spec))?;
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
            crate::imports::install_imports(ctx.symbol_tables, &ctx.current_module, ctx.module_aliases, std::slice::from_ref(spec))?;
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

        // Block for typecheck (F1: called inside handle_import).
        ctx.scheduler.block_for_typecheck(
            module,
            dep,
            &Symbol::from("*"),
        )?;

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
fn fq_module_is_loaded(ctx: &ModuleCompiler, dep: &ModuleFullPath) -> bool {
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
fn drive_module_dep(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    dep: &ModuleFullPath,
    span: Span,
) -> Result<(), CranelispError> {
    // Already loaded — block-then-unblock to re-queue the referencing module
    // without a file load (no future notify sweep would fire).
    if fq_module_is_loaded(ctx, dep) {
        ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;
        ctx.scheduler.unblock_module(module);
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
        ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;
        ctx.scheduler.unblock_module(module);
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

    // Register dep with scheduler (sexps ride the packet) and block on it.
    // `block_for_typecheck` runs the acyclicity check, so a transitive cycle
    // back to `module` is rejected with the standard error.
    ctx.scheduler.register_module(dep.clone(), dep_sexps, true);
    ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;

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
fn register_dep(
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

    crate::observability::record_module_event(
        crate::observability::SchedulerTraceTag::RegisterDepPublish,
        dep.as_ref(),
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
            ModuleEntry::Def { .. } => Some(name.clone()),
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
    // `platform.{name}` module. Unlike the fresh-build `handle_platform`
    // path, this cache-restore composition INTENTIONALLY skips the §7.2
    // associated-`.cl`-type-module pre-resolve (FIXME 0323): the cached
    // sigs were already FQ-resolved at build time and decoded into the
    // restored SymbolTable above, so there is no unresolved type-ref to
    // drive a dependency for — only the fn-ptr GOT slots (`#[serde(skip)]`)
    // need re-populating. Failures here are non-fatal at the
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
            ctx.module_aliases,
            &spec.name,
            ctx.project_root,
            ctx.lib_dirs,
            ctx.platform_dirs,
            spec.span,
        ) {
            Ok(platform) => {
                // `register_platform_in_tc` already wrapped the DLL's exported
                // GOT in place and set `got_slot = manifest index` per entry
                // (platform-interface.md §6.4); no per-slot allocation / fn-ptr
                // store is needed on cache-hit either. Retain the DLL handle for
                // session lifetime so the wrapped slab + pointers stay valid.
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
        // Register with scheduler — the sexps ride the dep's work packet (S78).
        // The worker loop processes this dep's typecheck and eventually marks
        // it `inmem_done`. We do NOT block here (we are inside the outer
        // module's typecheck); the outer module either already typechecked or
        // its own normal import-block chain handles its dependency on this dep.
        // `delays_other=true` matches worker-side consensus (see §8.2 rationale).
        ctx.scheduler.register_module(transitive_dep.clone(), dep_sexps, true);
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
            crate::imports::install_exports(ctx.symbol_tables, &ctx.current_module, std::slice::from_ref(spec))?;
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

        // Register dep with scheduler (sexps ride the packet) and block.
        ctx.scheduler.register_module(dep.clone(), dep_sexps, true);
        ctx.scheduler.block_for_typecheck(module, dep, &Symbol::from("*"))?;

        return Ok(BlockAction::Block {
            dep_module: dep.clone(),
        });
    }

    // All source modules loaded — register the re-exports.
    crate::imports::install_exports(ctx.symbol_tables, &ctx.current_module, specs)?;
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

/// §8.6.6 step 5 longest-prefix module-alias substitution, int-side.
///
/// Mirrors `cranelisp_types::resolve::substitute_module_alias` (which is
/// crate-private to `cranelisp-types`): find the longest alias-table key that
/// is a dot-segment prefix of `module_part`, substitute its target, and carry
/// any remaining dot-segments through. No match → the bare `module_part`.
///
/// Needed at the int FQ-autoload boundary, which computes the dependency
/// module to load from a raw `mod/sym` reference *before* typecheck runs — so
/// it must apply the same alias resolution typecheck would, or a bare
/// submodule reference (`util/...` after `(mod util)`) would try to load a
/// module literally named `util`.
pub(crate) fn resolve_module_alias(
    module_aliases: &cranelisp_types::ModuleAliases,
    module_part: &str,
) -> ModuleFullPath {
    let mut best: Option<(usize, ModuleFullPath)> = None;
    for entry in module_aliases.iter() {
        let key: &str = entry.key().as_ref();
        let is_prefix = module_part == key
            || (module_part.len() > key.len()
                && module_part.as_bytes()[key.len()] == b'.'
                && module_part.starts_with(key));
        if is_prefix {
            let take = best.as_ref().map(|(len, _)| key.len() > *len).unwrap_or(true);
            if take {
                best = Some((key.len(), entry.value().target.clone()));
            }
        }
    }
    match best {
        None => ModuleFullPath::from(module_part),
        Some((matched_len, target)) => {
            let remainder = &module_part[matched_len..];
            if remainder.is_empty() {
                target
            } else {
                ModuleFullPath::from(format!("{target}{remainder}"))
            }
        }
    }
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
        // Step 1 (§8.2.2): write the inline body to the submodule backing file.
        write_inline_mod_to_disk(module, &decl.name, body_sexps, ctx.project_root)?;
        // Step 2 (§8.2.2, FIXME 0217): rewrite the PARENT source file, replacing
        // the inline `(mod name form…)` form with a bare `(mod name)` reference,
        // then drop `inline_body` from the in-memory ModDecl so the persistent
        // symbol-table shape matches a manually-created submodule (the §8.2.2
        // "indistinguishable" + "one-time creation syntax" invariants). Failures
        // to locate/rewrite the parent file are non-fatal — step 1 already
        // created the backing file, so loading proceeds; the rewrite is the
        // durable-shape cleanup, not a correctness gate for this run.
        rewrite_parent_inline_mod(ctx, module, decl);
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

    // Register dep with scheduler (sexps ride the packet) and block.
    ctx.scheduler.register_module(sub_path.clone(), dep_sexps, true);
    ctx.scheduler.block_for_typecheck(
        module,
        &sub_path,
        &Symbol::from("*"),
    )?;

    Ok(BlockAction::Block {
        dep_module: sub_path,
    })
}

/// Outcome of the layout-hash gate (platform-interface.md §5.5.4).
///
/// Separating the decision from its enaction (`eprintln!` / `return Err`) makes
/// the gate's three branches unit-testable without capturing stderr or
/// dlopening a real DLL: a matching pair → `Accept`, a mismatched pair in the
/// REPL → `WarnAndLoad` (the regeneration bootstrap), a mismatched pair in
/// `--run`/`--link` → `Refuse` carrying `PlatformError::LayoutHashMismatch`.
pub(crate) enum LayoutHashGate {
    /// Hashes match (or the host hash is empty — first-build/absent tolerated).
    Accept,
    /// Mismatch in the REPL: warn and load anyway (the only place the schema
    /// can be regenerated). Carries the warning text.
    WarnAndLoad(String),
    /// Mismatch in `--run`/`--link`: hard refusal carrying both hashes.
    Refuse(CranelispError),
}

/// Decide the layout-hash gate outcome from a (DLL hash, host-regenerated hash)
/// pair (platform-interface.md §5.5.4). Extracted from `handle_platform` as the
/// smallest pure owner of the compare + REPL/`--run` branch — the surrounding
/// `handle_platform` needs a full `ModuleCompiler` (and dlopens the platform),
/// so the dual-gate decision cannot otherwise be driven with a mismatched pair.
/// Minimum mechanism, no behaviour change: the load path and the unit test call
/// the same decision.
pub(crate) fn layout_hash_gate(
    dll_hash: &str,
    host_hash: &str,
    platform_name: &str,
    is_repl: bool,
    span: cranelisp_types::Span,
) -> LayoutHashGate {
    // A matching pair, or an empty host hash (the host regenerated nothing —
    // first-build/absent, §5.5.4), accepts.
    if host_hash == dll_hash || host_hash.is_empty() {
        return LayoutHashGate::Accept;
    }
    if is_repl {
        LayoutHashGate::WarnAndLoad(format!(
            "warning: platform '{platform_name}' layout hash mismatch (DLL embedded \
             {dll_hash}, host regenerated {host_hash}); loading anyway — run \
             `/platform-schema {platform_name}` and rebuild the platform to refresh \
             its embedded schema."
        ))
    } else {
        LayoutHashGate::Refuse(CranelispError::Platform(
            cranelisp_types::PlatformError::LayoutHashMismatch {
                dll: std::path::PathBuf::from(format!("platform.{platform_name}")),
                platform: platform_name.to_string(),
                expected: host_hash.to_string(),
                found: dll_hash.to_string(),
                location: cranelisp_types::ErrorLocation::from_span(span),
            },
        ))
    }
}

/// Handle platform forms: load DLL, pre-resolve associated type modules, and
/// register type signatures.
///
/// Platform loading is NOT a cross-module blocking operation for the DLL load
/// itself (it is synchronous). But a platform whose function signatures name
/// types from a user `.cl` type-module (`shapes/Rectangle`) MUST have those
/// modules resolved + registered BEFORE its sigs are checked
/// (platform-interface.md §7.2 "q-assoc-discovery (c); BEFORE sigs"). An
/// unresolved FQ sig type-ref surfaces as a `ModuleError`, NOT a
/// `ResolutionGap`, so the ordinary FQ-autoload retry (FIXME 0268) never fires
/// for platform sigs — this function closes that gap by driving each referenced
/// type module via the same dependency mechanism as `import`, blocking the
/// referencing cluster and retrying from the top once the dep is live.
///
/// Returns `BlockAction::Block { dep }` when a referenced type module is not yet
/// loaded (the cluster retries; this fn re-runs once the dep is live, at which
/// point all sigs resolve and it proceeds to register). Returns
/// `BlockAction::Continue` once every referenced type module is present and the
/// platform is fully registered.
///
/// Platform declarations in non-entry modules (submodules) are silently
/// ignored per spec §10.9.1 — only the entry module may load platforms.
fn handle_platform(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    spec: &PlatformSpec,
) -> Result<BlockAction, CranelispError> {
    // Submodules (paths containing '.') cannot load platforms.
    if module.as_ref().contains('.') {
        return Ok(BlockAction::Continue);
    }

    // Load + validate the DLL (without registering sigs yet) so we can read its
    // descriptor sig strings to discover the associated type modules.
    let platform = crate::platform::load_platform_checked(
        &spec.name,
        ctx.project_root,
        ctx.lib_dirs,
        ctx.platform_dirs,
        spec.span,
    )?;

    // §7.2 pre-resolve: for each EXTERNAL type module a sig references
    // (`shapes` from `shapes/Rectangle`), drive it as a dependency BEFORE the
    // sig-check loop runs. If any is not yet loaded, block + retry-from-top —
    // the DLL handle drops at this return; the next pass re-dlopens (OS-cached)
    // and finds the now-loaded module, so the sigs resolve.
    for dep in crate::platform::referenced_sig_modules(&platform.descriptors) {
        if !fq_module_is_loaded(ctx, &dep) {
            drive_module_dep(ctx, module, &dep, spec.span)?;
            return Ok(BlockAction::Block { dep_module: dep });
        }
    }

    // All referenced type modules are live — register the platform's sigs (GOT
    // wrap in place + FQ-resolved schemes + got_slot = manifest index).
    crate::platform::register_platform_in_tc(
        ctx.symbol_tables,
        ctx.module_aliases,
        &platform,
    )?;

    // The platform module's `SymbolTable` now wraps the DLL's exported GOT in
    // place (`register_platform_in_tc`, platform-interface.md §6.4) and carries
    // `got_slot = manifest index` per entry — the GOT-indirect dispatch arm in
    // backend (`apply.rs`) reaches the platform fns identically to any user
    // module. No per-slot allocation / fn-ptr store is needed here anymore (the
    // DLL owns + populated the slab); the old G8 slot-allocation loop is gone.
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));

    // Layout-hash gate (platform-interface.md §5.5.4, §6.4): regenerate the
    // schema from the live tables (the same backend generator the DLL ran at
    // /platform-schema time) and compare its canonical hash to the DLL's
    // exported `__cranelisp_layout_hash_<name>`. REPL warns-and-loads (the
    // regeneration bootstrap, §5.5.1); `--run` (non-REPL) hard-refuses. A
    // platform that declared no schema (scalar-only, no ADTs) exports no hash —
    // tolerated (first-build/absent, §5.5.4).
    if let Some(dll_hash) = &platform.layout_hash {
        let roots = ctx
            .symbol_tables
            .get(&module_path)
            .map(|t| cranelisp_backend::schema::platform_effect_roots(&t))
            .unwrap_or_default();
        let host_hash =
            cranelisp_backend::schema::compute_layout_hash(ctx.symbol_tables, &roots);
        // is_repl: the explicit run-mode signal (D1 ruling §4). REPL warns-and-
        // loads on layout-hash drift (the regeneration bootstrap, §5.5.1);
        // `--run`/`--link` hard-refuse. Read from `SharedState.run_mode` — the
        // single source of truth — replacing the former `introspection.is_some()`
        // proxy (introspection became always-`Some` under S78, conflating a REPL
        // facility with the batch discriminator). Absent shared state (unit-test
        // paths that never load a real platform) defaults to non-REPL = refuse.
        let is_repl = ctx
            .shared_state
            .map(|s| s.run_mode.is_repl())
            .unwrap_or(false);
        match layout_hash_gate(dll_hash, &host_hash, &platform.name, is_repl, spec.span) {
            LayoutHashGate::Accept => {}
            LayoutHashGate::WarnAndLoad(msg) => eprintln!("{msg}"),
            LayoutHashGate::Refuse(err) => return Err(err),
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
    Ok(BlockAction::Continue)
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
    // "leave the file untouched" (synthetic/out-of-range span or already-bare —
    // the idempotence case). Only write when the content actually changes.
    if let Some(rewritten) = splice_inline_mod_to_bare(&source, decl.span, decl.name.as_ref()) {
        // Atomic-ish write (best-effort; a failure leaves step 1's backing file
        // in place and the in-memory body already dropped, so the run is
        // unaffected).
        let _ = std::fs::write(&parent_file, rewritten);
    }
}

/// Pure parent-file rewrite (spec §8.2.2 step 2): splice the inline
/// `(mod name form…)` byte range identified by `span` down to a bare
/// `(mod name)` reference, preserving all surrounding whitespace and comments.
///
/// Returns `Some(new_source)` when a rewrite is warranted, `None` when the file
/// MUST be left untouched:
/// - the span is synthetic / out-of-range / not on char boundaries (e.g. a
///   REPL-entered `(mod …)` with no backing byte range, or a stale span);
/// - the form at the range is ALREADY the bare reference (idempotence — avoids a
///   spurious mtime bump on re-load of an already-extracted file).
///
/// Extracted as the pure owner of the transformation so the parent-rewrite
/// logic is unit-testable without an FS harness or a `ModuleCompiler` (mirrors
/// the `layout_hash_gate` extraction; `src/CLAUDE.md` testability discipline).
pub(crate) fn splice_inline_mod_to_bare(source: &str, span: Span, name: &str) -> Option<String> {
    let start = span.start as usize;
    let end = span.end as usize;
    if start >= end
        || end > source.len()
        || !source.is_char_boundary(start)
        || !source.is_char_boundary(end)
    {
        return None;
    }
    let replacement = format!("(mod {name})");
    if &source[start..end] == replacement {
        return None;
    }
    let mut rewritten = String::with_capacity(source.len());
    rewritten.push_str(&source[..start]);
    rewritten.push_str(&replacement);
    rewritten.push_str(&source[end..]);
    Some(rewritten)
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

    // S76 W-Macro (fire B): the dead `block_for_macro_codegen` dep-walk
    // (`collect_transitive_uncompiled_deps` + the notify-loop) is DELETED, not
    // wired (`macro-availability-model.md` §0.7). The locked decision FORBIDS a
    // macro clause from calling a same-module non-macro definition at expansion
    // time (round-trip safety, §0.3), so a clause's callees are dependency
    // functions (compiled before, by ordinary module compilation) or same-module
    // macros (compiled in source order) — there is no same-module-`defn`-callee
    // with an empty GOT slot to pre-compile here.

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

// compile_dep_symbol_inline removed (Sprint 53): was a dead stub that took 10
// parameters and returned Ok(()). The (now-deleted) scheduler block_for_macro_codegen
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
    let program = build_program_compat(&[expanded_sexp])?;

    // Step 4: Typecheck via the collapsed `check_forms` surface (Decision 44
    // 2026-05-13 third amendment) — single call runs Pass 1 + Pass 2 + finalize.
    let module = ctx.current_module.clone();
    let _ = accumulator;
    check_program_compat_no_gap(
        ctx.symbol_tables,
        ctx.module_aliases,
        ctx.prelude_fallback,
        &module,
        &program,
    )?;

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

    // Compile macro clause through the unified compile_to_module path.
    // Macro clause functions are normal functions on per-module GOTs — the
    // typechecker has registered `defn_name` on the current module's symbol
    // table with `ast: Some(_)` and `got_slot: Some(_)` (Wave 0 invariant).
    // S69 Submission 35: `ast` is `DefnVariant` (no `name`); the codegen
    // `names` array keys off `defn_name` directly (Defn reconstruction dropped).
    let module = ctx.current_module.clone();
    let tc_modules = ctx.symbol_tables;
    ensure_typecheck_product(ctx.typecheck_products, &module);
    let _ = accumulator;
    let names = [defn_name.clone()];
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
pub(crate) fn has_code_ptr(
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
/// Returns `Some(dep_module)` (the prelude path) if the prelude was registered
/// + blocked on and the cluster must retry once it is live; `None` if prelude
/// is already loaded, not found, or suppressed (S78 in-call-stack shape).
fn inject_prelude_if_needed(
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
            ctx.scheduler.block_for_typecheck(
                module,
                &prelude_path,
                &Symbol::from("*"),
            )?;

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
                        && !matches!(kind.as_ref(), cranelisp_types::DefKind::Macro { .. }) {
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

#[cfg(test)]
mod tests {
    use super::*;


    // -----------------------------------------------------------------------
    // FQ auto-loading gap→load→retry mechanism (FIXME 0268, spec §8.5.4/§9.3.6)
    // -----------------------------------------------------------------------

    // spec: spec/08-modules.md §8.5.4 — the typecheck gap for an FQ value/fn
    // reference to an unloaded module (`SymbolTypechecked`) names the module
    // the orchestrator must load.
    #[test]
    fn gap_target_module_symbol_typechecked_names_module() {
        let gap = cranelisp_types::ResolutionGap::SymbolTypechecked(FQSymbol {
            module: ModuleFullPath::from("mac"),
            symbol: Symbol::from("helper"),
        });
        assert_eq!(gap_target_module(&gap), Some(ModuleFullPath::from("mac")));
    }

    // spec: spec/09-macros.md §9.3.6 — the expand-phase macro gap (`MacroInMem`)
    // also reduces to "load `fq.module`".
    #[test]
    fn gap_target_module_macro_in_mem_names_module() {
        let gap = cranelisp_types::ResolutionGap::MacroInMem(FQSymbol {
            module: ModuleFullPath::from("mac"),
            symbol: Symbol::from("twice"),
        });
        assert_eq!(gap_target_module(&gap), Some(ModuleFullPath::from("mac")));
    }

    // spec: spec/08-modules.md §8.5.4 — an FQ type reference to an unloaded
    // module (`Type`) names the module via its `FQTypeName`.
    #[test]
    fn gap_target_module_type_names_module() {
        let gap = cranelisp_types::ResolutionGap::Type(cranelisp_types::FQTypeName::new(
            ModuleFullPath::from("shapes"),
            cranelisp_types::TypeName::from("Point"),
        ));
        assert_eq!(gap_target_module(&gap), Some(ModuleFullPath::from("shapes")));
    }

    // spec: spec/09-macros.md §9.3.6 — `recognize` captures an FQ macro head
    // whose module is not loaded as a block signal (returns `Ok(None)` for the
    // aborted walk so the head flows on as an ordinary reference). This is the
    // expand-side half of the gap→load→retry mechanism: the captured module
    // drives `load_fq_dep_module`.
    #[test]
    fn recognize_captures_unloaded_fq_macro_module() {
        use crate::expander::MacroResolver;
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();
        let mut check_state = CheckState::new(module.clone());
        let mut accumulator = ModuleCheckAccumulator::new();

        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: &symbol_tables,
            next_type_id: &next_type_id,
            check_state: &mut check_state,
            current_module: module.clone(),
            module_aliases: &module_aliases,
            prelude_fallback: &prelude_fallback,
            typecheck_products: &typecheck_products,
            accumulator: &mut accumulator,
            scheduler: &scheduler,
            shared_state: None,
            macro_defining_modules: Vec::new(),
            blocked_on_fq_module: None,
        };

        // `mac` is not loaded — recognising an FQ head `mac/twice` captures it.
        let r = resolver
            .recognize("mac/twice", Span::SYNTHETIC)
            .expect("recognition does not hard-error on an unloaded FQ module");
        assert!(r.is_none(), "aborted walk treats the head as a non-macro");
        assert_eq!(
            resolver.blocked_on_fq_module,
            Some(ModuleFullPath::from("mac")),
            "the unloaded FQ module is captured for the worker loop to load"
        );
    }

    // spec: spec/09-macros.md §9.3.6 — a bare (non-`/`) head is not an
    // FQ-module block signal even when unresolved.
    #[test]
    fn recognize_bare_head_is_not_fq_block() {
        use crate::expander::MacroResolver;
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();
        let mut check_state = CheckState::new(module.clone());
        let mut accumulator = ModuleCheckAccumulator::new();

        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: &symbol_tables,
            next_type_id: &next_type_id,
            check_state: &mut check_state,
            current_module: module.clone(),
            module_aliases: &module_aliases,
            prelude_fallback: &prelude_fallback,
            typecheck_products: &typecheck_products,
            accumulator: &mut accumulator,
            scheduler: &scheduler,
            shared_state: None,
            macro_defining_modules: Vec::new(),
            blocked_on_fq_module: None,
        };

        let r = resolver
            .recognize("plain-fn", Span::SYNTHETIC)
            .expect("bare unresolved head is Ok(None)");
        assert!(r.is_none());
        assert_eq!(
            resolver.blocked_on_fq_module, None,
            "a bare head never triggers FQ-module auto-load"
        );
    }

    // spec: spec/09-macros.md §9.3.6 (FIXME 0322) — a `:`-prefixed symbol is a
    // TYPE ANNOTATION (`:primitives/Int`), never a module-qualified value/macro
    // reference. The FQ-autoload pre-scan in `recognize` must NOT split it on
    // `/` and treat `:primitives` as an unloaded module: doing so registers a
    // bogus `:primitives` block dep and contaminates resolution (the field type
    // then fails with `unknown type 'primitives' (from module '')`). The sibling
    // `qualify_expanded_sexp` already guards this with a `starts_with(':')` skip.
    #[test]
    fn recognize_skips_colon_prefixed_type_annotation() {
        use crate::expander::MacroResolver;
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();
        let mut check_state = CheckState::new(module.clone());
        let mut accumulator = ModuleCheckAccumulator::new();

        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: &symbol_tables,
            next_type_id: &next_type_id,
            check_state: &mut check_state,
            current_module: module.clone(),
            module_aliases: &module_aliases,
            prelude_fallback: &prelude_fallback,
            typecheck_products: &typecheck_products,
            accumulator: &mut accumulator,
            scheduler: &scheduler,
            shared_state: None,
            macro_defining_modules: Vec::new(),
            blocked_on_fq_module: None,
        };

        // The FQ type annotation `:primitives/Int` must NOT be mis-split into a
        // `:primitives` block dep — it is a type leaf, not a value reference.
        let r = resolver
            .recognize(":primitives/Int", Span::SYNTHETIC)
            .expect("a `:`-prefixed annotation is Ok(None), not a hard error");
        assert!(r.is_none(), "a type annotation is never a macro head");
        assert_eq!(
            resolver.blocked_on_fq_module, None,
            "a `:`-prefixed type annotation must NOT register an FQ-module block \
             dep (FIXME 0322 — `:primitives` is not a module qualifier)"
        );

        // A bare `:Int` annotation (no `/`) is likewise inert.
        let r = resolver
            .recognize(":Int", Span::SYNTHETIC)
            .expect("a bare `:`-prefixed annotation is Ok(None)");
        assert!(r.is_none());
        assert_eq!(resolver.blocked_on_fq_module, None);
    }

    /// FIXME 0121: a `(mod util)` declaration registers the short-name alias
    /// `util -> <parent>.util` (via `register_submodule_alias`). The
    /// int-side FQ-autoload boundary must substitute that alias when computing
    /// the dependency module for a bare qualified ref `util/...`, mirroring
    /// typecheck's §8.6.6 longest-prefix substitution — otherwise it tries to
    /// load a module literally named `util`, which does not exist.
    #[test]
    fn resolve_module_alias_substitutes_short_submodule_name() {
        let aliases = cranelisp_types::ModuleAliases::default();
        aliases.insert(
            ModuleFullPath::from("util"),
            cranelisp_types::ModuleAliasEntry::new(
                ModuleFullPath::from("main.util"),
                Visibility::Private,
                Span::SYNTHETIC,
            ),
        );

        // Exact match → the alias target.
        assert_eq!(
            resolve_module_alias(&aliases, "util"),
            ModuleFullPath::from("main.util"),
        );
        // A dot-segment remainder is carried through after substitution.
        assert_eq!(
            resolve_module_alias(&aliases, "util.inner"),
            ModuleFullPath::from("main.util.inner"),
        );
        // No matching alias → the bare module part unchanged.
        assert_eq!(
            resolve_module_alias(&aliases, "other"),
            ModuleFullPath::from("other"),
        );
        // A non-segment-boundary prefix MUST NOT match (`util` is not a
        // dot-segment prefix of `utility`).
        assert_eq!(
            resolve_module_alias(&aliases, "utility"),
            ModuleFullPath::from("utility"),
        );
    }

    /// Longest-prefix wins when multiple alias keys are dot-segment prefixes
    /// of the queried module part (§8.6.6 step 5).
    #[test]
    fn resolve_module_alias_prefers_longest_prefix() {
        let aliases = cranelisp_types::ModuleAliases::default();
        aliases.insert(
            ModuleFullPath::from("a"),
            cranelisp_types::ModuleAliasEntry::new(
                ModuleFullPath::from("x"),
                Visibility::Private,
                Span::SYNTHETIC,
            ),
        );
        aliases.insert(
            ModuleFullPath::from("a.b"),
            cranelisp_types::ModuleAliasEntry::new(
                ModuleFullPath::from("y"),
                Visibility::Private,
                Span::SYNTHETIC,
            ),
        );
        // `a.b.c` matches both `a` and `a.b`; the longer key wins.
        assert_eq!(
            resolve_module_alias(&aliases, "a.b.c"),
            ModuleFullPath::from("y.c"),
        );
    }

    // -----------------------------------------------------------------
    // Layout-hash gate (platform-interface.md §5.5.4) — drives the WIRED
    // type-definition-drift detection (handle_platform) with mismatched and
    // matching (dll_hash, host_hash) pairs without dlopening a real DLL. The
    // dual gate: matching → Accept; mismatch in `--run`/`--link` → Refuse with
    // PlatformError::LayoutHashMismatch carrying both hashes; mismatch in the
    // REPL → WarnAndLoad (the regeneration bootstrap).
    // -----------------------------------------------------------------

    // spec: design/arch/platform-interface.md §5.5.4 — a stale schema in
    // `--run`/`--link` is REFUSED, carrying both hashes + the platform name so
    // the message directs the user to `/platform-schema` and rebuild.
    #[test]
    fn layout_hash_drift_refuses_in_run_mode() {
        let outcome = layout_hash_gate(
            "dll_baked_hash",
            "host_live_hash",
            "shapes",
            /* is_repl */ false,
            Span::SYNTHETIC,
        );
        match outcome {
            LayoutHashGate::Refuse(CranelispError::Platform(
                cranelisp_types::PlatformError::LayoutHashMismatch {
                    platform,
                    expected,
                    found,
                    ..
                },
            )) => {
                assert_eq!(platform, "shapes");
                // `expected` = host-regenerated (canonical) hash; `found` =
                // DLL-exported hash (error.rs PlatformError::LayoutHashMismatch).
                assert_eq!(expected, "host_live_hash");
                assert_eq!(found, "dll_baked_hash");
            }
            other => panic!(
                "expected Refuse(LayoutHashMismatch), got {}",
                match other {
                    LayoutHashGate::Accept => "Accept",
                    LayoutHashGate::WarnAndLoad(_) => "WarnAndLoad",
                    LayoutHashGate::Refuse(_) => "Refuse(other error)",
                }
            ),
        }
    }

    // spec: design/arch/platform-interface.md §5.5.4 — in the REPL a stale
    // schema WARNS and loads (the regeneration bootstrap), naming both hashes
    // and the `/platform-schema` rebuild guidance.
    #[test]
    fn layout_hash_drift_warns_and_loads_in_repl() {
        let outcome = layout_hash_gate(
            "dll_baked_hash",
            "host_live_hash",
            "shapes",
            /* is_repl */ true,
            Span::SYNTHETIC,
        );
        match outcome {
            LayoutHashGate::WarnAndLoad(msg) => {
                assert!(msg.contains("shapes"), "warning names the platform");
                assert!(msg.contains("dll_baked_hash"), "warning names the DLL hash");
                assert!(msg.contains("host_live_hash"), "warning names the host hash");
                assert!(
                    msg.contains("/platform-schema"),
                    "warning gives the rebuild guidance"
                );
            }
            _ => panic!("expected WarnAndLoad in REPL on mismatch"),
        }
    }

    // spec: design/arch/platform-interface.md §5.5.4 — a matching pair ACCEPTS
    // (no warning, no refusal), in both REPL and `--run`.
    #[test]
    fn layout_hash_match_accepts_in_both_modes() {
        for is_repl in [false, true] {
            assert!(
                matches!(
                    layout_hash_gate("same_hash", "same_hash", "shapes", is_repl, Span::SYNTHETIC),
                    LayoutHashGate::Accept
                ),
                "matching hashes must Accept (is_repl={is_repl})"
            );
        }
    }

    // spec: design/arch/platform-interface.md §5.5.4 — an empty host hash (the
    // host regenerated nothing: a scalar-only platform / first build / absent
    // schema) is TOLERATED — Accept, never Refuse, regardless of the DLL hash.
    #[test]
    fn layout_hash_empty_host_hash_accepts() {
        assert!(matches!(
            layout_hash_gate("dll_baked_hash", "", "shapes", false, Span::SYNTHETIC),
            LayoutHashGate::Accept
        ));
    }

    // spec: spec/08-modules.md §8.2.2 — parent-file rewrite (FIXME 0217). The
    // pure splice replaces the inline `(mod child form…)` byte range identified
    // by the ModDecl span with a bare `(mod child)`, preserving surrounding
    // forms + whitespace + comments.
    #[test]
    fn splice_inline_mod_rewrites_to_bare_reference() {
        let source = "(mod child (defn helper [] 7))\n(defn main [] 0)\n";
        // span covers the `(mod child …)` form exactly (offsets 0..30).
        let span = Span::new(0, 30);
        let rewritten = splice_inline_mod_to_bare(source, span, "child")
            .expect("an inline (mod child …) form MUST be rewritten to bare");
        assert_eq!(
            rewritten,
            "(mod child)\n(defn main [] 0)\n",
            "the inline body MUST be spliced out, surrounding forms/whitespace \
             preserved (spec §8.2.2 step 2)",
        );
    }

    // spec: spec/08-modules.md §8.2.2 — idempotence. Re-running over a file
    // whose form is ALREADY the bare `(mod child)` reference MUST NOT rewrite
    // (returns None — no spurious mtime bump on reload of an extracted file).
    #[test]
    fn splice_inline_mod_is_idempotent_on_bare_reference() {
        let source = "(mod child)\n(defn main [] 0)\n";
        let span = Span::new(0, 11); // "(mod child)" is 11 bytes.
        assert!(
            splice_inline_mod_to_bare(source, span, "child").is_none(),
            "an already-bare (mod child) reference MUST NOT be rewritten \
             (idempotence — spec §8.2.2 step 2)",
        );
    }

    // spec: spec/08-modules.md §8.2.2 — a synthetic / out-of-range span (e.g. a
    // REPL-entered `(mod …)` with no backing byte range) MUST leave the file
    // untouched rather than panicking or splicing at a bogus offset.
    #[test]
    fn splice_inline_mod_skips_out_of_range_span() {
        let source = "(mod child (defn helper [] 7))";
        assert!(
            splice_inline_mod_to_bare(source, Span::SYNTHETIC, "child").is_none(),
            "a synthetic/out-of-range span MUST be a no-op",
        );
        // end past the source length is also a no-op.
        assert!(
            splice_inline_mod_to_bare(source, Span::new(0, 9999), "child").is_none(),
            "an out-of-range end MUST be a no-op",
        );
    }
}
