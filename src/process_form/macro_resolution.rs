//! On-demand macro recognition + clause-compile + expansion-walk (S87 §1.1
//! extraction from `process_form.rs`).
//!
//! The macro family threaded through Pass-2: `SymbolTableMacroResolver` (the
//! recognition driver for `expand_sexp_recursive`, with the prelude outer-scope
//! fallback), `try_expand_sexp` (scopes the resolver borrows to the expansion
//! phase), `qualify_expanded_sexp` (cross-module hygiene), the on-demand clause
//! compile (`compile_macro_with_state` / `compile_macro_if_needed` /
//! `compile_macro_clause_inline`), and the shared name/probe primitives
//! (`macro_clause_jit_name` / `has_code_ptr`). Single concern: recognize a macro
//! head and ensure its clause code is in memory, then expand. The clause
//! *codegen* lives in `macro_clause.rs`; this module drives it.

use cranelisp_types::{
    CranelispError, DefKind, FQSymbol, MacroClauseInfo, ModuleEntry,
    ModuleFullPath, Sexp, Span, Symbol,
};

use cranelisp_typecheck::CheckState;

use crate::expander::{self, MacroResolver};
use crate::scheduler::CompileScheduler;
use crate::worker::{ModuleCompiler, ModuleCheckAccumulator, handle_cached_codegen};

use super::macro_clause::{compile_macro_clause_core, compile_macro_clause_with_state};

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
pub(super) struct SymbolTableMacroResolver<'a> {
    /// Per-module symbol tables (DashMap, interior mutability).
    pub(super) symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    /// Monotonic counter for fresh type variable IDs.
    pub(super) next_type_id: &'a std::sync::atomic::AtomicU32,
    /// CheckState — needed for on-demand compilation (check_form_with_state).
    pub(super) check_state: &'a mut CheckState,
    /// Current module path (starting point for symbol lookup).
    pub(super) current_module: ModuleFullPath,
    /// Module-path aliases — fed to `resolve_macro_head` for qualified refs.
    pub(super) module_aliases: &'a cranelisp_types::ModuleAliases,
    /// Per-module prelude-fallback bits — fed to `recognize_macro_head` so a
    /// prelude-provided macro (`cond`/`when`/`str`/…) is recognized from a user
    /// module via the implicit outer scope (S78 §2; public-only per I-1).
    pub(super) prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
    /// Per-module typecheck products (DashMap, interior mutability).
    pub(super) typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    /// Accumulator for check_form_with_state during on-demand compilation.
    pub(super) accumulator: &'a mut ModuleCheckAccumulator,
    /// Scheduler — for notify_inmem_codegen_complete after on-demand compilation.
    pub(super) scheduler: &'a CompileScheduler,
    /// Shared state — needed for JIT retention during on-demand compilation.
    /// None for REPL contexts where caching is not used.
    pub(super) shared_state: Option<&'a crate::session_v4::SharedState>,
    /// Defining modules for macros that were resolved during expansion.
    /// Used to qualify bare symbols in expanded output (cross-module hygiene).
    pub(super) macro_defining_modules: Vec<ModuleFullPath>,
    /// FQ auto-loading (FIXME 0268, spec §9.3.6): set when `recognize`
    /// encounters an FQ macro head `mod/macro` whose `mod` is not yet loaded.
    /// `try_expand_sexp` reads this after the walk and signals the worker loop
    /// to load the dependency and resume the referencing form. `recognize`
    /// returns `Ok(None)` in this case (treats the head as an ordinary call for
    /// the duration of this aborted walk), so the captured module is the
    /// only signal that a block is needed.
    pub(super) blocked_on_fq_module: Option<ModuleFullPath>,
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
            let dep = cranelisp_types::substitute_module_alias(
                self.module_aliases,
                &ModuleFullPath::from(mod_part),
            );
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

/// Scope the resolver's borrows to just the expansion phase.
///
/// Creates a SymbolTableMacroResolver, runs expand_sexp_recursive,
/// drops the resolver, returns the expanded sexp. After this returns,
/// ctx and accumulator are available for the caller to use freely.
/// Outcome of attempting macro expansion on a single Pass-2 form.
pub(super) enum ExpandOutcome {
    /// Expansion ran to fixpoint. `Some(sexp)` = expanded result (differs from
    /// input); `None` = no expansion (input was not a macro call).
    Expanded(Option<Sexp>),
    /// Expansion encountered an FQ macro head `mod/macro` whose module is not
    /// yet loaded (FIXME 0268). The caller loads `dep_module` and resumes the
    /// referencing form. No partial expansion is committed.
    BlockedOnFqModule(ModuleFullPath),
}

pub(super) fn try_expand_sexp(
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

        let r = expander::expand_sexp_recursive(sexp.clone(), &mut resolver, 0, None);
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
pub(super) fn qualify_expanded_sexp(
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
// Macro expansion for Pass 2
// ---------------------------------------------------------------------------

/// Compile all clauses of a macro if any clause lacks a function pointer.
///
/// No dependency pre-walk: the former transitive-callee walk was deleted in
/// S76 (see the in-body note below) — the locked macro-availability model
/// forbids a clause from calling a same-module non-macro definition at
/// expansion time, so a clause's callees are either dependency-module
/// functions (already compiled by ordinary module compilation) or same-module
/// macros (compiled in source order). Notifies the scheduler per compiled
/// clause (never claiming module-level `inmem_done`).
pub(super) fn compile_macro_if_needed(
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

/// Compile a single macro clause inline using the worker's `&mut ModuleCompiler`.
/// Thin adapter over [`compile_macro_clause_core`] (FIXME 0109 Wave D collapse)
/// — sources the references from `ctx` directly (its `module_aliases` /
/// `prelude_fallback` are the live worker maps, no leaked-default fallback).
/// `accumulator` is vestigial under the collapsed `check_forms` surface.
fn compile_macro_clause_inline(
    ctx: &mut ModuleCompiler,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError> {
    let _ = accumulator;
    let module = ctx.current_module.clone();
    compile_macro_clause_core(
        ctx.symbol_tables,
        ctx.module_aliases,
        ctx.prelude_fallback,
        &module,
        macro_name,
        clause_idx,
        clause,
        span,
        ctx.typecheck_products,
        ctx.shared_state,
    )
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
