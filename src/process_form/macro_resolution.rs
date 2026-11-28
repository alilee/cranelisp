//! Macro recognition + source-checkpoint compilation + expansion walk (S87 §1.1
//! extraction from `process_form.rs`).
//!
//! The macro family threaded through Pass-2: `SymbolTableMacroResolver` (the
//! recognition driver for `expand_sexp_recursive`, with the prelude outer-scope
//! fallback), `try_expand_sexp` (scopes the resolver borrows to the expansion
//! phase; cross-module hygiene is the expander's), source checkpoint
//! compilation (`compile_macro_if_needed`), and the exact-clause compiled-owner
//! probe (`has_code_ptr`). Single concern: recognize a macro
//! head and ensure its clause code is in memory, then expand. The clause
//! *codegen* lives in `macro_clause.rs`; this module drives it.

use std::collections::BTreeSet;

use cranelisp_types::{
    CranelispError, Decl, FQSymbol, Life, ModuleFullPath, Realization, Sexp, Span,
};

use crate::expander::{self, MacroResolver};
use crate::scheduler::{CachedLoadAnswer, CompileScheduler};
use crate::session_v4::MacroCall;
use crate::worker::{ModuleCompiler, handle_cached_codegen};

use super::macro_clause::{MacroCheckpoint, MacroClauseEnv, compile_macro_checkpoint};

// ---------------------------------------------------------------------------
// SymbolTableMacroResolver — on-demand macro resolution from symbol tables
// ---------------------------------------------------------------------------

/// Recognition driver for the live in-place expansion walk
/// (`expand_sexp_recursive`).
///
/// `recognize` recognizes a macro head through `expander::recognize_macro_head`.
/// It never compiles clauses from source. Its one side effect: when the
/// macro's home module was restored from cache and its object is not yet
/// loaded, it claims and runs that load, or waits for the restore or another
/// claimant to finish it, before returning.
/// Execution is the walk's single `JitMacroExpander`
/// (`design/int/int.md` §6.8).
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
    /// Scheduler — identifies a cache-restored home module and receives the
    /// completion of its object load.
    pub(super) scheduler: &'a CompileScheduler,
    /// Shared state for the cached-object load. `None` disables that load.
    pub(super) shared_state: Option<&'a crate::session_v4::SharedState>,
    /// FQ auto-loading (FIXME 0268, spec §9.3.6): set when `recognize`
    /// encounters an FQ macro head `mod/macro` whose `mod` is not yet loaded.
    /// `try_expand_sexp` reads this after the walk and signals the worker loop
    /// to load the dependency and resume the referencing form. `recognize`
    /// returns `Ok(None)` in this case (treats the head as an ordinary call for
    /// the duration of this aborted walk), so the captured module is the
    /// only signal that a block is needed.
    pub(super) blocked_on_fq_module: Option<ModuleFullPath>,
    /// The alias-substituted module of every qualified head recognised as a
    /// macro (`design/int/int.md` §7.6.2): the expansion leaves no reference
    /// to it, so typecheck cannot record it.
    pub(super) macro_lookup_dependencies: BTreeSet<ModuleFullPath>,
    /// The span of the walked form's own head: a recognition there makes the
    /// form a macro call (`design/int/s125-binary-clean.md` §4.4).
    pub(super) form_head: Option<Span>,
    /// The macro the walked form's own head resolved to, recorded at
    /// recognition.
    pub(super) form_call: Option<FQSymbol>,
    /// Every macro recognised during the walk, by canonical identity.
    pub(super) recognised_macros: BTreeSet<FQSymbol>,
}

impl MacroResolver for SymbolTableMacroResolver<'_> {
    fn symbol_tables(&self) -> &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
        self.symbol_tables
    }

    fn current_module(&self) -> &ModuleFullPath {
        &self.current_module
    }

    fn recognize(&mut self, name: &str, span: Span) -> Result<Option<FQSymbol>, CranelispError> {
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
        let mut qualifier = None;
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
                &self.current_module,
                &ModuleFullPath::from(mod_part),
            );
            if !self.symbol_tables.contains_key(&dep) {
                self.blocked_on_fq_module = Some(dep);
                return Ok(None);
            }
            qualifier = Some(dep);
        }

        // Step 1: RECOGNITION via the LOCKED types primitive
        // (`cranelisp_types::ResolutionScope::resolve_macro_head` over a committed `View`,
        // `macro-availability-model.md` §5). Zero int→typecheck dependency;
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
        self.macro_lookup_dependencies.extend(qualifier);
        if self.form_call.is_none() && self.form_head == Some(span) {
            self.form_call = Some(fq.clone());
        }
        self.recognised_macros.insert(fq.clone());

        // Step 2: the executor reads clause code from the home module's GOT.
        // A published checkpoint compiled every clause, but a home module
        // restored from cache has no bodies until its object loads. Take that
        // load through the scheduler's one claim, or wait for the restore or
        // the claimed load to finish (`design/int/int.md` §7.1). Any clause
        // still missing fails execution with `MacroInvokeError::Aborted`;
        // resolution never recompiles a clause from source.
        let all_compiled = (0..clauses).all(|idx| has_code_ptr(self.symbol_tables, &fq, idx));
        if !all_compiled
            && defining_module != self.current_module
            && let Some(shared) = self.shared_state
            && self.scheduler.cached_module_contains(&defining_module)
            && let CachedLoadAnswer::Claimed(claim) =
                self.scheduler.claim_or_await_cached_load(&defining_module)
        {
            handle_cached_codegen(claim, shared);
        }

        Ok(Some(fq))
    }
}

/// Read a macro's clause metadata + docstring from its **already-resolved**
/// canonical entry. `fq` addresses the home module + canonical symbol that
/// `cranelisp_types::ResolutionScope::resolve_macro_head` chain-followed to (imports/aliases/
/// visibility already applied) — so this is a single direct lookup, no
/// chain-walk. Returns `None` when the entry is absent or not a `DefKind::Macro`
/// (a forward reference or a non-macro shadowing the name).
fn read_macro_meta(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    fq: &FQSymbol,
) -> Option<(usize, Option<String>)> {
    let table = symbol_tables.get(&fq.module)?;
    let Decl::Macro(declaration) = &table.get(fq.symbol.as_ref())?.declaration else {
        return None;
    };
    Some((declaration.clauses.len(), declaration.docstring.clone()))
}

/// Outcome of attempting macro expansion on a single Pass-2 form.
pub(super) enum ExpandOutcome {
    /// Expansion ran to fixpoint. `sexp` is `Some` when the result differs
    /// from the input and `None` when the input was not a macro call.
    /// `macro_lookup_dependencies` are the qualified heads' modules.
    Expanded {
        sexp: Option<Sexp>,
        macro_lookup_dependencies: BTreeSet<ModuleFullPath>,
        /// The macro call the form itself is, when its head was recognised.
        call: Option<MacroCall>,
        /// The macros of the form's own module recognised in the walk.
        same_module_macros: Vec<FQSymbol>,
    },
    /// Expansion encountered an FQ macro head `mod/macro` whose module is not
    /// yet loaded (FIXME 0268). The caller loads `dep_module` and resumes the
    /// referencing form. No partial expansion is committed, and the modules
    /// recognised by the aborted walk are discarded with it.
    BlockedOnFqModule(ModuleFullPath),
}

/// Expand one form with a resolver whose borrows end before this returns.
///
/// The resolver is dropped before the caller builds or checks the expanded
/// form, so `ctx` is free again on return
/// (`design/int/int.md` §6.8).
pub(super) fn try_expand_sexp(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
) -> Result<ExpandOutcome, CranelispError> {
    // The resolver borrows only the symbol tables + resolution scope (macro
    // recognition/drive); it does not touch `CheckState` or the accumulator.
    let (result, blocked_on, macro_lookup_dependencies, recognition) = {
        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: ctx.symbol_tables,
            current_module: module.clone(),
            module_aliases: ctx.module_aliases,
            prelude_fallback: ctx.prelude_fallback,
            scheduler: ctx.scheduler,
            shared_state: ctx.shared_state,
            blocked_on_fq_module: None,
            macro_lookup_dependencies: BTreeSet::new(),
            form_head: form_head_span(sexp),
            form_call: None,
            recognised_macros: BTreeSet::new(),
        };

        let r = expander::expand_sexp_recursive(sexp.clone(), &mut resolver, 0, None);
        let blocked = resolver.blocked_on_fq_module.take();
        let recognised = std::mem::take(&mut resolver.macro_lookup_dependencies);
        let recognition = (
            resolver.form_call.take(),
            std::mem::take(&mut resolver.recognised_macros),
        );
        (r, blocked, recognised, recognition)
        // resolver dropped here, releasing its borrows of `ctx`
    };

    // An FQ macro head named an unloaded module — signal the worker loop to
    // load it and resume (FIXME 0268). Surface this before propagating any
    // expansion error, since the aborted walk may itself have errored on the
    // unrecognised FQ head.
    if let Some(dep) = blocked_on {
        return Ok(ExpandOutcome::BlockedOnFqModule(dep));
    }

    let expanded = result?;

    // Each expansion was qualified at its own macro inside the walk
    // (`expander::expand_recognized_macro`).
    let expanded = (expanded != *sexp).then_some(expanded);
    let (form_call, recognised_macros) = recognition;
    Ok(ExpandOutcome::Expanded {
        sexp: expanded,
        macro_lookup_dependencies,
        call: form_call.map(|macro_name| MacroCall::of(macro_name, sexp)),
        same_module_macros: recognised_macros
            .into_iter()
            .filter(|fq| fq.module == *module)
            .collect(),
    })
}

/// The span of `form`'s own head: its first element, or the form itself when
/// it is a bare symbol (a zero-argument call). A synthetic span identifies no
/// written head.
fn form_head_span(form: &Sexp) -> Option<Span> {
    let head = match form {
        Sexp::List(children, _) => children.first()?,
        Sexp::Symbol(..) => form,
        _ => return None,
    };
    Some(head.span()).filter(|span| *span != Span::SYNTHETIC)
}

// ---------------------------------------------------------------------------
// Macro expansion for Pass 2
// ---------------------------------------------------------------------------

/// Compile and publish one complete source-ordered macro checkpoint.
///
/// No dependency pre-walk: the former transitive-callee walk was deleted in
/// S76 (see the in-body note below) — the locked macro-availability model
/// forbids a clause from calling a same-module non-macro definition at
/// expansion time, so a clause's callees are either dependency-module
/// functions (already compiled by ordinary module compilation) or same-module
/// macros (compiled in source order). The ordinary prepared-commit publisher
/// installs the parent and all active clauses together.
pub(super) fn compile_macro_if_needed(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    macro_sexp: &Sexp,
    facts: &super::AuthoredFacts,
    attempt: &super::AttemptFacts,
) -> Result<Option<ModuleFullPath>, CranelispError> {
    // The checkpoint is a publication point: a macro over a live
    // macro-generated definition is refused before it publishes
    // (`design/int/s125-binary-clean.md` §4.6, R2).
    super::refuse_generated_redefinition(
        ctx.introspection,
        attempt,
        &FQSymbol {
            module: module.clone(),
            symbol: info.name.clone(),
        },
        &facts.origin,
        macro_sexp.span(),
    )?;
    // S76 W-Macro (fire B): the dead `block_for_macro_codegen` dep-walk
    // (`collect_transitive_uncompiled_deps` + the notify-loop) is DELETED, not
    // wired (`macro-availability-model.md` §5). The locked decision FORBIDS a
    // macro clause from calling a same-module non-macro definition at expansion
    // time (round-trip safety, §2), so a clause's callees are dependency
    // functions (compiled before, by ordinary module compilation) or same-module
    // macros (compiled in source order) — there is no same-module-`defn`-callee
    // with an empty GOT slot to pre-compile here.

    let env = MacroClauseEnv {
        symbol_tables: ctx.symbol_tables,
        module_aliases: ctx.module_aliases,
        prelude_fallback: ctx.prelude_fallback,
        shared_state: ctx.shared_state,
    };
    match compile_macro_checkpoint(&env, module, info, macro_sexp, attempt)? {
        MacroCheckpoint::Published => Ok(None),
        MacroCheckpoint::Gap(gap) => {
            super::macro_checkpoint_gap_target(ctx, &gap, macro_sexp.span()).map(Some)
        }
        MacroCheckpoint::AwaitMember(member) => Ok(Some(member)),
    }
}

// ---------------------------------------------------------------------------
// Macro entry helpers
// ---------------------------------------------------------------------------

/// Check if an exact owned clause has a compiled body owner.
pub(crate) fn has_code_ptr(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    macro_fq: &FQSymbol,
    clause_index: usize,
) -> bool {
    symbol_tables
        .get(&macro_fq.module)
        .and_then(|t| {
            let Decl::Macro(declaration) = &t.get(macro_fq.symbol.as_ref())?.declaration else {
                return Some(false);
            };
            match &declaration.clauses.get(clause_index)?.callable.life {
                Life::Concrete {
                    realization: Realization::Body { code, .. },
                    ..
                } => Some(code.is_some()),
                _ => Some(false),
            }
        })
        .unwrap_or(false)
}
