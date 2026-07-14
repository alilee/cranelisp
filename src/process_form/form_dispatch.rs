//! Form classification + Pass-1 registration (S87 §1.1 extraction from
//! `process_form.rs`).
//!
//! The pre-typecheck shaping of a cluster's forms: classify raw sexps into
//! `FormKind`, write the structural-decl Vecs onto the table
//! (`record_*_on_symbol_table`), separate macros, register defmacro entries +
//! the (now no-op) Pass-1 / default-method shims, and wrap bare exprs as
//! synthetic defns. One concern: turning raw sexps into the shapes Pass-2 +
//! `check_forms` consume.

use cranelisp_types::{
    CranelispError, DefKind, Defn, ErrorLocation, ExportSpec, FQSymbol,
    ImportSpec, MacroClauseInfo, ModuleAliases, ModuleEntry, ModuleFullPath, PlatformSpec,
    ResolutionScope, Sexp, Span, Symbol, TopLevel, View, Visibility,
};

use cranelisp_typecheck::{CheckState, PreludeFallback};

use crate::worker::{ModuleCompiler, ModuleCheckAccumulator};

// ---------------------------------------------------------------------------
// FormKind — per-sexp form classification for Pass 2
// ---------------------------------------------------------------------------

/// Classification of a top-level sexp for Pass 2 dispatch.
pub(super) enum FormKind {
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

pub(super) fn record_exports_on_symbol_table(
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

pub(super) fn record_platform_on_symbol_table(
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
pub(super) fn classify_form(
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

/// Separate defmacro forms from regular forms for Pass 1.
#[allow(clippy::type_complexity)]
pub(super) fn separate_macros(
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

/// The implicit-prelude module (§8.8.1) that a module with its `prelude_fallback`
/// bit ON resolves bare-name misses against.
const PRELUDE_MODULE: &str = "prelude";

/// The §8.6.4 defmacro definition gate (S108 Wave-G CS2,
/// `design/arch/prelude-import-convergence.md` §4.2): construct the int
/// resolution scope over `module`'s committed view — the prelude fallback
/// decided ONCE here from the session-side `prelude_fallback` bit — and delegate
/// to the ONE types-owned `reject_def_over_binding` seam. Rejects a `defmacro`
/// of `name` over an in-scope explicit import/export or a prelude-provided name;
/// the module's OWN prior definition (home == current — a REPL macro redefine)
/// and a miss (name free to define) both pass. Behaviourally the int-side twin
/// of typecheck's `reject_def_over_binding` adapter (checker.rs) — same seam,
/// same diagnostic — reached without a typecheck dependency because the seam and
/// the scope both live in `cranelisp-types`.
fn reject_defmacro_over_binding(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,
    module: &ModuleFullPath,
    name: &Symbol,
    span: Span,
) -> Result<(), CranelispError> {
    // No table yet for this module ⇒ nothing is in scope to conflict with.
    let Some(table_ref) = symbol_tables.get(module) else {
        return Ok(());
    };
    let view: View<'_, crate::code::Code, ()> = View::single(&table_ref);
    // Fallback ON iff the module's bit is set and it is not prelude itself
    // (absence-is-OFF; never self-fallback — `ResolutionScope::new` also collapses
    // a self-fallback defensively).
    let prelude_module = ModuleFullPath::from(PRELUDE_MODULE);
    let prelude = if module.as_ref() != PRELUDE_MODULE
        && prelude_fallback.get(module).map(|b| *b).unwrap_or(false)
    {
        Some(&prelude_module)
    } else {
        None
    };
    let scope = ResolutionScope::new(symbol_tables, module_aliases, &view, module, prelude);
    cranelisp_types::reject_def_over_binding(&scope, name, span)
}

/// Register a defmacro in the module table (Pass 1).
///
/// Parses clause info and stores it as `ModuleEntry::Macro` with the
/// original sexp for later compilation. No codegen — deferred until
/// first use.
///
/// `authored` is the turn's ORIGINAL authored form — the regeneration
/// authority (S102 CS-D1, `design/int/s102-defect-wave.md` §4.2 rule 1:
/// origin-uniform recording). For a direct top-level `(defmacro …)` it is the
/// defmacro form itself (same as `sexp`); for a macro-expansion-produced
/// defmacro (a macro-defining macro like stdlib `def`) it is the outer call
/// form (e.g. `(mdef x 1)`), so ALL introspection records created by one turn
/// carry the SAME authored sexp and `save::generate_fns_and_macros` can dedup
/// to a single emission. The expanded `(defmacro …)` artifact stays on
/// `.expanded` (introspection) and on the entry's `macro_sexp` (the
/// clause-recompile authority — that role is unchanged); persisting it as
/// regen source alongside the original was the D1 directory poison (the two
/// forms do not co-load).
#[allow(clippy::too_many_arguments)]
pub(crate) fn register_macro_in_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    introspection: Option<&dashmap::DashMap<FQSymbol, crate::session_v4::Introspection>>,
    module: &ModuleFullPath,
    name: &Symbol,
    info: &cranelisp_frontend::DefmacroInfo,
    sexp: &Sexp,
    authored: &Sexp,
    authored_source: Option<String>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,
) -> Result<(), CranelispError> {
    // §8.6.4 definition seam (S108 Wave-G CS2): a `defmacro` over a name already
    // in scope — an explicit import/export head OR a prelude-provided name — is
    // a compile-time conflict, never a shadow (spec §8.6.4/§8.8.1). Route the
    // defmacro binding through the SAME types-owned seam every other definition
    // form uses (`defn`/`deftype` at the typecheck arm, `deftrait` at its arm),
    // so int's macro path rejects on identical terms with no typecheck
    // dependency. A rejected form has NO effect: this gate runs BEFORE any
    // introspection or symbol-table write, so the error propagates through the
    // normal form-error path with nothing registered.
    reject_defmacro_over_binding(
        symbol_tables, module_aliases, prelude_fallback, module, name, sexp.span(),
    )?;
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
    //
    // S102 CS-D1: the regen-facing `sexp` is the AUTHORED form; when the
    // defmacro arrived via expansion (`authored` ≠ `sexp` — compared by span,
    // expansion output carries synthetic rewritten spans) the expanded
    // artifact rides `.expanded` for `/sexp` display.
    if let Some(intr_map) = introspection {
        let fq = FQSymbol {
            module: module.clone(),
            symbol: name.clone(),
        };
        let mut entry = intr_map.entry(fq).or_default();
        if entry.sexp.is_none() {
            entry.sexp = Some(authored.clone());
        }
        if entry.expanded.is_none() && authored.span() != sexp.span() {
            entry.expanded = Some(sexp.clone());
        }
        if entry.source.is_none() {
            // S102 CS-D2: prefer the verbatim authored text (the caller's
            // consistency-gated `source_text` span slice — preserves reader
            // shorthand like `` `(… ~e) ``); fall back to the pretty render.
            entry.source =
                Some(authored_source.unwrap_or_else(|| crate::pretty::pretty_print_plain(authored)));
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

/// Pass 1 registration (no-op under the collapsed `check_forms` surface).
///
/// Per Decision 44's 2026-05-13 third amendment, the typecheck Pass-1
/// registration phase is internal to `check_forms` and runs as part of the
/// single call performed by `finalize_module` (via `check_program_compat`).
/// This function is retained for source compatibility with the existing
/// `process_module_forms` orchestration; it intentionally performs no
/// typecheck work itself.
pub(super) fn pass1_register(
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
pub(super) fn register_default_methods(
    _symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    _next_type_id: &std::sync::atomic::AtomicU32,
    _check_state: &mut CheckState,
    _module: &ModuleFullPath,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Vec<Defn>, CranelispError> {
    let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    Ok(defaults)
}

/// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
/// Mirrors `TypeChecker::wrap_exprs_as_defns`.
pub(super) fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
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
