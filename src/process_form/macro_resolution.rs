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

use crate::expander::{self, MacroResolver};
use crate::scheduler::CompileScheduler;
use crate::worker::{ModuleCompiler, ModuleCheckAccumulator, handle_cached_codegen};

use super::macro_clause::{compile_macro_clause_core, MacroClauseEnv};

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
                    self.symbol_tables,
                    self.typecheck_products,
                    self.shared_state,
                    &defining_module,
                    &info,
                    span,
                    self.scheduler,
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

/// Compile a macro's clauses on demand for the resolver (no `&mut TypeChecker`).
///
/// This is the on-demand compilation path for the resolver. The `module_aliases`
/// / `prelude_fallback` resolution scope derives from `shared_state` — when
/// absent (unit-test paths) an empty leaked default is a safe stand-in (macro
/// clause bodies use qualified `macros/*` refs, never aliases or the prelude
/// bare-name fallback). Built once into a [`MacroClauseEnv`] shared across the
/// clause loop.
fn compile_macro_with_state(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    typecheck_products: &dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    shared_state: Option<&crate::session_v4::SharedState>,
    target_module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    scheduler: &CompileScheduler,
) -> Result<(), CranelispError> {
    let module_aliases: &cranelisp_types::ModuleAliases = match shared_state {
        Some(s) => &s.module_aliases,
        None => Box::leak(Box::new(cranelisp_types::ModuleAliases::default())),
    };
    let prelude_fallback: &cranelisp_typecheck::PreludeFallback = match shared_state {
        Some(s) => &s.prelude_fallback,
        None => Box::leak(Box::new(cranelisp_typecheck::PreludeFallback::default())),
    };
    let env = MacroClauseEnv {
        symbol_tables,
        module_aliases,
        prelude_fallback,
        typecheck_products,
        shared_state,
    };
    for (clause_idx, clause) in info.clauses.iter().enumerate() {
        let clause_name = macro_clause_jit_name(&info.name, clause_idx);
        if has_code_ptr(symbol_tables, target_module, &clause_name) {
            continue;
        }

        compile_macro_clause_core(
            &env, target_module, &info.name, clause_idx, clause, span,
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
/// ctx is available for the caller to use freely.
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
) -> Result<ExpandOutcome, CranelispError> {
    // The resolver borrows only the symbol tables + resolution scope (macro
    // recognition/drive); it does not touch `CheckState` or the accumulator.
    let (result, defining_modules, blocked_on) = {
        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: ctx.symbol_tables,
            current_module: module.clone(),
            module_aliases: ctx.module_aliases,
            prelude_fallback: ctx.prelude_fallback,
            typecheck_products: ctx.typecheck_products,
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
/// **Scope-aware (FIXME 0670).** Qualification is a **resolution-product**
/// operation — only a **free reference** carries resolved identity. A **binder**
/// (defn/fn param, `let` name, `match` var-pattern) INTRODUCES a name and is
/// never qualified; a **local read** of a bound name refers to that binder, not
/// a defining-module symbol, and is also held verbatim (`/arch` path-1 ruling,
/// Principle 24 corollary; `expansion-qualification-scope.md`). This walk is the
/// P7 mirror of the expander's own `expand_scoped` binder handling — the two
/// share ONE binder-slot enumeration (`expander::is_binding_form`/`params_scope`/
/// `pattern_binders`/`is_annotation_symbol`), never a second copy.
///
/// A symbol is qualified iff it is a FREE reference — not lexically bound — AND:
/// - bare (no `/` already) and not a type annotation (`:` prefix) / `_`,
/// - found in a defining module's symbol table,
/// - NOT already available in the current module.
pub(super) fn qualify_expanded_sexp(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: &ModuleFullPath,
    defining_modules: &[ModuleFullPath],
    sexp: Sexp,
) -> Sexp {
    let ctx = QualifyCtx {
        symbol_tables,
        current_module,
        defining_modules,
    };
    // Public entry seeds an empty lexical scope.
    qualify_scoped(&ctx, sexp, &std::collections::HashSet::new())
}

/// The threaded qualify-walk context (mirrors the expander's resolver-threading;
/// keeps the recursive helpers under the 8-param `src/CLAUDE.md` budget).
struct QualifyCtx<'a> {
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    current_module: &'a ModuleFullPath,
    defining_modules: &'a [ModuleFullPath],
}

/// Scope-aware qualify core. `shadows` is the set of names lexically bound by an
/// enclosing binding form (`expand_scoped`'s `shadows`, one-to-one).
fn qualify_scoped(
    ctx: &QualifyCtx,
    sexp: Sexp,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    match sexp {
        Sexp::Symbol(ref name, _span) => {
            // FIRST guard (FIXME 0670): a lexically-bound name — a binder or a
            // local read of one — is never a free reference; held verbatim.
            if shadows.contains(name.as_str()) {
                return sexp;
            }
            qualify_free_symbol(ctx, sexp)
        }
        Sexp::List(children, span) => {
            // A binding special form establishes a lexical scope: its binder
            // slots are held verbatim and its value/body children are qualified
            // under the EXTENDED scope. Dispatch through the SHARED enumeration
            // (`expander::is_binding_form`) so both walks stay in lockstep.
            if let Some(Sexp::Symbol(head, _)) = children.first()
                && crate::expander::is_binding_form(head)
            {
                let head = head.clone();
                return qualify_binding_form(ctx, &head, children, span, shadows);
            }
            // Non-binding head — recurse into every child under the current
            // (unchanged) scope, qualifying call targets and arguments.
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_scoped(ctx, c, shadows))
                .collect();
            Sexp::List(qualified_children, span)
        }
        Sexp::Bracket(children, span) => {
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_scoped(ctx, c, shadows))
                .collect();
            Sexp::Bracket(qualified_children, span)
        }
        // Other sexp types (Int, Float, String, Bool) pass through unchanged.
        other => other,
    }
}

/// Qualify a FREE bare symbol (already known not to be lexically bound). The
/// original scope-blind body — the already-qualified/annotation/`_`/
/// current-module-availability skips, then the defining-module lookup.
fn qualify_free_symbol(ctx: &QualifyCtx, sexp: Sexp) -> Sexp {
    let Sexp::Symbol(ref name, span) = sexp else {
        return sexp;
    };
    // Skip already-qualified names, type annotations, special names.
    if name.contains('/') || name.starts_with(':') || name.starts_with('_') {
        return sexp;
    }
    // Skip if the symbol is already available in the current module.
    if let Some(table) = ctx.symbol_tables.get(ctx.current_module)
        && table.get(name).is_some()
    {
        return sexp;
    }
    // Check defining modules for this symbol.
    for def_mod in ctx.defining_modules {
        if let Some(table) = ctx.symbol_tables.get(def_mod)
            && let Some(entry) = table.get(name)
        {
            // Follow imports to find the true source module for qualification.
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

/// Dispatch a binding special form to its scope-aware qualifier — the one-to-one
/// mirror of `expander::expand_binding_form` (FIXME 0670). Each arm holds its
/// binder slots verbatim, accumulates the introduced names into the scope, and
/// qualifies the value/body children under the extended scope.
fn qualify_binding_form(
    ctx: &QualifyCtx,
    head: &str,
    children: Vec<Sexp>,
    span: Span,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    match head {
        "let" => qualify_let(ctx, children, span, shadows),
        "fn" | "lambda" => qualify_fn(ctx, children, span, shadows),
        "defn" | "defn-" => qualify_defn(ctx, children, span, shadows),
        "match" => qualify_match(ctx, children, span, shadows),
        _ => unreachable!("invariant: is_binding_form gates qualify_binding_form"),
    }
}

/// Fallback: qualify every child under the unchanged scope (the shape did not
/// match the binding form's expected structure; the AST builder reports it).
fn qualify_children_unchanged(
    ctx: &QualifyCtx,
    children: Vec<Sexp>,
    span: Span,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    let qc: Vec<Sexp> = children
        .into_iter()
        .map(|c| qualify_scoped(ctx, c, shadows))
        .collect();
    Sexp::List(qc, span)
}

/// `(let [name val …] body)` — each binding NAME is a binder (held verbatim),
/// each VALUE qualified in the scope so far (sequential `let*`), body qualified
/// with every bound name shadowing. Mirrors `expander::expand_let`.
fn qualify_let(
    ctx: &QualifyCtx,
    children: Vec<Sexp>,
    span: Span,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    if children.len() != 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let Sexp::Bracket(bind_items, bracket_span) = children[1].clone() else {
        return qualify_children_unchanged(ctx, children, span, shadows);
    };
    let mut scope = shadows.clone();
    let mut new_items: Vec<Sexp> = Vec::with_capacity(bind_items.len());
    let mut i = 0;
    while i < bind_items.len() {
        // Binding NAME — a fresh local binder; held verbatim, never qualified.
        let binder = match &bind_items[i] {
            Sexp::Symbol(n, _) => Some(n.clone()),
            _ => None,
        };
        new_items.push(bind_items[i].clone());
        i += 1;
        // Optional `:Type` annotations on the value are held verbatim.
        while i < bind_items.len() && crate::expander::is_annotation_symbol(&bind_items[i]) {
            new_items.push(bind_items[i].clone());
            i += 1;
        }
        // The value expression is qualified in the scope so far (the binder is
        // NOT yet in scope for its own RHS — sequential `let`).
        if i < bind_items.len() {
            let v = qualify_scoped(ctx, bind_items[i].clone(), &scope);
            new_items.push(v);
            i += 1;
        }
        // The binder now shadows subsequent bindings and the body.
        if let Some(b) = binder {
            scope.insert(b);
        }
    }
    let body = qualify_scoped(ctx, children[2].clone(), &scope);
    Sexp::List(
        vec![children[0].clone(), Sexp::Bracket(new_items, bracket_span), body],
        span,
    )
}

/// `(fn [params] body)` / `(lambda [params] body)` — param bracket held verbatim
/// (binder names), body qualified with the params shadowing. Mirrors
/// `expander::expand_fn`.
fn qualify_fn(
    ctx: &QualifyCtx,
    children: Vec<Sexp>,
    span: Span,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    if children.len() != 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let Sexp::Bracket(param_items, _) = &children[1] else {
        return qualify_children_unchanged(ctx, children, span, shadows);
    };
    let scope = crate::expander::params_scope(param_items, shadows);
    let body = qualify_scoped(ctx, children[2].clone(), &scope);
    Sexp::List(vec![children[0].clone(), children[1].clone(), body], span)
}

/// `(defn name "doc"? [params] body…)` / multi-arity `(defn name (…) …)` — head,
/// name, docstring held verbatim; each variant's params verbatim and its body
/// qualified with the params shadowing. Mirrors `expander::expand_defn`.
fn qualify_defn(
    ctx: &QualifyCtx,
    children: Vec<Sexp>,
    span: Span,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    if children.len() < 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let mut out: Vec<Sexp> = Vec::with_capacity(children.len());
    out.push(children[0].clone()); // defn / defn-
    out.push(children[1].clone()); // name (a binder — verbatim)
    let mut idx = 2;
    if let Some(Sexp::Str(..)) = children.get(idx) {
        out.push(children[idx].clone()); // docstring
        idx += 1;
    }
    match children.get(idx) {
        // Single arity: [params] followed by the body form(s).
        Some(Sexp::Bracket(param_items, _)) => {
            let scope = crate::expander::params_scope(param_items, shadows);
            out.push(children[idx].clone()); // params verbatim
            for c in &children[idx + 1..] {
                out.push(qualify_scoped(ctx, c.clone(), &scope));
            }
        }
        // Multi arity: each remaining child is a `([params] body)` variant.
        Some(Sexp::List(..)) => {
            for c in &children[idx..] {
                out.push(qualify_defn_variant(ctx, c, shadows));
            }
        }
        // Unexpected shape — qualify generically (the AST builder reports it).
        _ => {
            for c in &children[idx..] {
                out.push(qualify_scoped(ctx, c.clone(), shadows));
            }
        }
    }
    Sexp::List(out, span)
}

/// A single multi-arity `defn` variant `([params] body)` — params verbatim, body
/// qualified with the params shadowing. Mirrors `expander::expand_defn_variant`.
fn qualify_defn_variant(
    ctx: &QualifyCtx,
    sexp: &Sexp,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    let Sexp::List(items, vspan) = sexp else {
        return qualify_scoped(ctx, sexp.clone(), shadows);
    };
    let Some(Sexp::Bracket(param_items, _)) = items.first() else {
        return qualify_scoped(ctx, sexp.clone(), shadows);
    };
    if items.len() != 2 {
        return qualify_scoped(ctx, sexp.clone(), shadows);
    }
    let scope = crate::expander::params_scope(param_items, shadows);
    let body = qualify_scoped(ctx, items[1].clone(), &scope);
    Sexp::List(vec![items[0].clone(), body], *vspan)
}

/// `(match scrutinee… [pat body …])` — scrutinee qualified in the current scope;
/// each arm PATTERN held verbatim (its variables are binders), each arm BODY
/// qualified with those pattern variables shadowing. Mirrors
/// `expander::expand_match`.
fn qualify_match(
    ctx: &QualifyCtx,
    children: Vec<Sexp>,
    span: Span,
    shadows: &std::collections::HashSet<String>,
) -> Sexp {
    if children.len() < 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let last = children.len() - 1;
    let Sexp::Bracket(arm_items, arms_span) = children[last].clone() else {
        return qualify_children_unchanged(ctx, children, span, shadows);
    };
    let mut out: Vec<Sexp> = Vec::with_capacity(children.len());
    out.push(children[0].clone()); // match
    // Scrutinee region (possibly a `:Type form` pair) — ordinary reads.
    for c in &children[1..last] {
        out.push(qualify_scoped(ctx, c.clone(), shadows));
    }
    if !arm_items.len().is_multiple_of(2) {
        // Malformed arms — qualify generically (the AST builder reports it).
        let qualified: Vec<Sexp> = arm_items
            .into_iter()
            .map(|c| qualify_scoped(ctx, c, shadows))
            .collect();
        out.push(Sexp::Bracket(qualified, arms_span));
        return Sexp::List(out, span);
    }
    let mut new_arms: Vec<Sexp> = Vec::with_capacity(arm_items.len());
    let mut i = 0;
    while i + 1 < arm_items.len() {
        let pattern = &arm_items[i];
        let body = &arm_items[i + 1];
        let mut scope = shadows.clone();
        scope.extend(crate::expander::pattern_binders(pattern));
        new_arms.push(pattern.clone()); // pattern verbatim (binders, not reads)
        new_arms.push(qualify_scoped(ctx, body.clone(), &scope));
        i += 2;
    }
    out.push(Sexp::Bracket(new_arms, arms_span));
    Sexp::List(out, span)
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
    let env = MacroClauseEnv {
        symbol_tables: ctx.symbol_tables,
        module_aliases: ctx.module_aliases,
        prelude_fallback: ctx.prelude_fallback,
        typecheck_products: ctx.typecheck_products,
        shared_state: ctx.shared_state,
    };
    compile_macro_clause_core(&env, &module, macro_name, clause_idx, clause, span)
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

#[cfg(test)]
mod tests {
    use super::*;

    // spec: src/CLAUDE.md §"Macro expansion" — the clause GOT-slot JIT name is
    // `__macro_{name}_clause_{idx}`. `JitMacroExpander` loads the clause fn's
    // code pointer by this exact name, so the format is an ABI contract between
    // the macro compiler (which registers the slot) and the executor (which
    // reads it) — a drift here silently breaks macro expansion with an
    // "…not in memory…" abort.
    #[test]
    fn macro_clause_jit_name_format() {
        assert_eq!(
            macro_clause_jit_name(&Symbol::from("when"), 0).as_ref(),
            "__macro_when_clause_0"
        );
        assert_eq!(
            macro_clause_jit_name(&Symbol::from("cond"), 3).as_ref(),
            "__macro_cond_clause_3"
        );
    }

    // Distinct macros / distinct clause indices produce distinct slot names
    // (no collision in the shared flat JIT namespace).
    #[test]
    fn macro_clause_jit_name_is_injective_over_name_and_index() {
        let a = macro_clause_jit_name(&Symbol::from("m"), 0);
        let b = macro_clause_jit_name(&Symbol::from("m"), 1);
        let c = macro_clause_jit_name(&Symbol::from("n"), 0);
        assert_ne!(a.as_ref(), b.as_ref());
        assert_ne!(a.as_ref(), c.as_ref());
    }

    // -----------------------------------------------------------------------
    // FIXME 0670 — the expansion-seam qualify pass is scope-aware.
    //
    // Live-defect demonstration (the RED→GREEN unit flip that replaces the
    // evaporated e2e flip, `tests/plan/s114-test-plan.md` §4.3): the fixture's
    // `defining_modules`/table state is constructed so the incidental
    // "available in the current module" skip-guard does NOT fire — the binder
    // name `name` is present in a DEFINING module but absent from the current
    // module. Against the scope-BLIND pass every one of these mis-qualifies the
    // binder (`name` → `dm/name`, which the frontend then rejects at the param
    // "a binder must be bare"); the scope-aware pass holds binders + local reads
    // verbatim and qualifies only free defining-module references.
    // -----------------------------------------------------------------------

    fn empty_scheme() -> cranelisp_types::Scheme {
        cranelisp_types::Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: cranelisp_types::Type::Int,
        }
    }

    /// A one-module table set whose `module` publicly defines each of `names`
    /// (as slot-less user fns — the qualify pass only reads presence + kind).
    fn tables_with_defs(
        module: &str,
        names: &[&str],
    ) -> dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
        let path = ModuleFullPath::from(module);
        let mut st = crate::code::SessionSymbolTable::new_with_params(path.clone());
        for n in names {
            let entry = ModuleEntry::def(
                empty_scheme(),
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::NotDetermined },
            )
            .visibility(cranelisp_types::Visibility::Public)
            .build();
            st.insert(Symbol::from(*n), entry);
        }
        let tables = dashmap::DashMap::new();
        tables.insert(path, st);
        tables
    }

    /// Parse `src` to its single top-level sexp (the expanded-shape fixture).
    fn parse_one(src: &str) -> Sexp {
        cranelisp_frontend::parse(src).unwrap().remove(0)
    }

    // spec: expansion-qualification-scope.md §3 —
    // `qualify_skips_value_binders_and_local_reads`.
    #[test]
    fn qualify_skips_value_binders_and_local_reads() {
        // `dm` defines both the colliding binder name `name` AND the foreign
        // helper `wrap`; the current module `user` defines NEITHER, so the
        // availability skip cannot mask the binder mis-qualification.
        let tables = tables_with_defs("dm", &["name", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = vec![ModuleFullPath::from("dm")];
        let input = parse_one("(defn greet [name] (wrap \"hi\" name))");

        let out = qualify_expanded_sexp(&tables, &current, &dms, input);
        let flat = out.format_flat();

        // The param BINDER stays bare and the body LOCAL READ stays bare.
        assert!(
            !flat.contains("dm/name"),
            "binder/local-read `name` must NOT be qualified: {flat}"
        );
        // The FREE foreign-helper reference IS qualified to its defining module.
        assert!(
            flat.contains("dm/wrap"),
            "free reference `wrap` must be qualified: {flat}"
        );
    }

    // spec: expansion-qualification-scope.md §3 —
    // `qualify_skips_let_and_match_binders`.
    #[test]
    fn qualify_skips_let_and_match_binders() {
        let tables = tables_with_defs("dm", &["name", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = vec![ModuleFullPath::from("dm")];

        // let: binding NAME `name` + its body local read held bare; `wrap` free.
        let let_out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(let [name 1] (wrap name))"),
        );
        let lf = let_out.format_flat();
        assert!(!lf.contains("dm/name"), "let binder/read must stay bare: {lf}");
        assert!(lf.contains("dm/wrap"), "free `wrap` must qualify (let): {lf}");

        // match: var-pattern `name` + arm body local read held bare; `wrap` free.
        let match_out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(match 0 [name (wrap name)])"),
        );
        let mf = match_out.format_flat();
        assert!(!mf.contains("dm/name"), "match binder/read must stay bare: {mf}");
        assert!(mf.contains("dm/wrap"), "free `wrap` must qualify (match): {mf}");
    }

    // Completeness twin (the shared-enumeration matrix): one cell per value-level
    // binder form. A per-form fix that greened one but diverged a sibling would
    // fail its cell — the matrix pressures the ONE shared enumeration.
    // spec: expansion-qualification-scope.md §3 — completeness twin.
    #[test]
    fn qualify_binder_completeness_matrix_defn_fn_let_match() {
        let tables = tables_with_defs("dm", &["x", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = vec![ModuleFullPath::from("dm")];
        // (form-source, label) — each binds `x` and reads it; `wrap` is free.
        let cells = [
            ("(defn f [x] (wrap x))", "defn"),
            ("(fn [x] (wrap x))", "fn"),
            ("(lambda [x] (wrap x))", "lambda"),
            ("(let [x 1] (wrap x))", "let"),
            ("(match 0 [x (wrap x)])", "match"),
        ];
        for (src, label) in cells {
            let out =
                qualify_expanded_sexp(&tables, &current, &dms, parse_one(src));
            let flat = out.format_flat();
            assert!(
                !flat.contains("dm/x"),
                "[{label}] binder/local-read `x` must stay bare: {flat}"
            );
            assert!(
                flat.contains("dm/wrap"),
                "[{label}] free `wrap` must be qualified: {flat}"
            );
        }
    }

    // Negative-direction fence: a genuinely FREE defining-module reference (not
    // shadowed by any binder) still qualifies — the fix must not over-shield.
    // spec: expansion-qualification-scope.md §2.1 — free references qualify.
    #[test]
    fn qualify_still_qualifies_free_reference_not_shadowed() {
        let tables = tables_with_defs("dm", &["helper"]);
        let current = ModuleFullPath::from("user");
        let dms = vec![ModuleFullPath::from("dm")];
        // No binder introduces `helper`; it is a free defining-module reference.
        let out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(let [y 1] (helper y))"),
        );
        let flat = out.format_flat();
        assert!(
            flat.contains("dm/helper"),
            "a free defining-module reference must still qualify: {flat}"
        );
    }
}
