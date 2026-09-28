//! Form classification + source-presentation recording (S87 §1.1 extraction from
//! `process_form.rs`).
//!
//! The pre-typecheck shaping of a cluster's forms: classify raw sexps into
//! `FormKind`, write the structural-decl Vecs onto the table
//! (`record_*_on_symbol_table`), record already-published macro introspection,
//! and wrap bare exprs as synthetic defns. One concern: turning raw sexps into
//! the shapes the source walk and
//! `check_forms` consume.

use cranelisp_types::{
    CranelispError, Defn, ErrorLocation, ExportSpec, FQSymbol, ImportSpec, ModuleFullPath,
    PlatformSpec, Sexp, Span, Symbol, TopLevel,
};

use crate::worker::ModuleCompiler;

// ---------------------------------------------------------------------------
// FormKind — per-sexp form classification for Pass 2
// ---------------------------------------------------------------------------

/// Classification of a top-level sexp for Pass 2 dispatch.
pub(crate) enum FormKind {
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
// Implicit-prelude disposition (CP3 / `design/int/int.md` §6.5
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
pub(crate) fn classify_form(
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
                        let (decls, _remaining) = cranelisp_frontend::extract_module_declarations(
                            &containing_module,
                            std::slice::from_ref(sexp),
                        )?;
                        Ok(FormKind::Import(decls.import_specs))
                    }
                    "export" => {
                        let (decls, _remaining) = cranelisp_frontend::extract_module_declarations(
                            &containing_module,
                            std::slice::from_ref(sexp),
                        )?;
                        Ok(FormKind::Export(decls.export_specs))
                    }
                    "mod" | "mod-" => {
                        let (decls, _remaining) = cranelisp_frontend::extract_module_declarations(
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
                        let (decls, _remaining) = cranelisp_frontend::extract_module_declarations(
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

/// Record presentation for a macro whose complete checkpoint is already live.
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
///
/// Every caller runs after the checkpoint published this generation, so the
/// record's form, expansion and text are REPLACED: a replacement is what
/// regeneration persists (`repl/spec/18-redefinition.md` §18.8), and an
/// expansion the new generation lacks is cleared
/// (`design/int/session-persistence.md` §2.4.1). A REPL turn's verbatim text
/// still overrides `source` afterwards (`eval::record_defining_turn_source`).
pub(crate) fn record_macro_introspection(
    introspection: Option<&dashmap::DashMap<FQSymbol, crate::session_v4::Introspection>>,
    module: &ModuleFullPath,
    name: &Symbol,
    sexp: &Sexp,
    authored: &Sexp,
    authored_source: Option<String>,
) {
    // `introspection` is `Some` only in REPL mode. Expansion output carries
    // synthetic rewritten spans, so a span difference marks an expansion.
    if let Some(intr_map) = introspection {
        let fq = FQSymbol {
            module: module.clone(),
            symbol: name.clone(),
        };
        let mut entry = intr_map.entry(fq).or_default();
        entry.sexp = Some(authored.clone());
        entry.expanded = (authored.span() != sexp.span()).then(|| sexp.clone());
        entry.source =
            Some(authored_source.unwrap_or_else(|| crate::pretty::pretty_print_plain(authored)));
    }
}

/// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
/// Mirrors `TypeChecker::wrap_exprs_as_defns`.
pub(crate) fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
    use cranelisp_types::{DefnVariant, Visibility};

    let mut working = Vec::with_capacity(program.len());
    for top in program {
        match top {
            TopLevel::Expr(expr) => {
                let span = expr.span();
                let wrapper_span =
                    Span::new(span.start.saturating_sub(1), span.end.saturating_add(1));
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
