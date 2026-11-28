//! `/type`: the turn's own per-form steps, stopped before publication
//! (`design/int/s125-binary-clean.md` §2).
//!
//! The form is expanded by the evaluated turn's expansion, must build to one
//! expression, and is checked into a staging table that is dropped: nothing is
//! committed, and no module is loaded.

use cranelisp_types::{
    CranelispError, ErrorLocation, ModuleFullPath, ResolutionGap, Sexp, Span, TopLevel, Type,
};

use crate::scheduler::OriginatedForm;
use crate::worker::{ModuleCompiler, build_program_compat, check_cluster_to_staging};

use super::dependency::{fq_module_is_loaded, gap_member, gap_target_module};
use super::form_dispatch::wrap_exprs_as_defns;
use super::macro_resolution::{ExpandOutcome, try_expand_sexp};
use super::{
    GapReference, gap_reference_span, module_has_no_member_error, reanchor_expansion_diagnostic,
    reanchor_finalize_error,
};

/// The type `sexp` would have if `module` evaluated it, without evaluating,
/// defining or loading anything. A definition, `defmacro` or structural form,
/// before or after expansion, is a located error.
pub(crate) fn type_of_expression(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
) -> Result<Type, CranelispError> {
    refuse_definition_head(sexp)?;
    let (expanded, is_expansion) = match try_expand_sexp(ctx, module, sexp)? {
        ExpandOutcome::Expanded {
            sexp: Some(expanded),
            ..
        } => (expanded, true),
        ExpandOutcome::Expanded { sexp: None, .. } => (sexp.clone(), false),
        ExpandOutcome::BlockedOnFqModule(dep) => {
            return Err(module_not_loaded_error(&dep, sexp.span()));
        }
    };
    for form in cranelisp_frontend::flatten_begin(expanded.clone()) {
        // An expansion carries synthetic spans; the authored form locates.
        refuse_definition_head(&form).map_err(|_| definition_error(sexp.span()))?;
    }
    // Build and check errors are re-anchored exactly as the evaluated turn
    // re-anchors them (`process_regular_form`, `finalize_cluster`).
    let program = match build_program_compat(std::slice::from_ref(&expanded)) {
        Ok(program) => program,
        Err(error) if is_expansion => {
            return Err(reanchor_expansion_diagnostic(error, sexp.span(), sexp));
        }
        Err(error) => return Err(error),
    };
    if !matches!(program.as_slice(), [TopLevel::Expr(_)]) {
        return Err(definition_error(sexp.span()));
    }
    let working = wrap_exprs_as_defns(&program);
    match check_cluster_to_staging(
        ctx.symbol_tables,
        ctx.module_aliases,
        ctx.prelude_fallback,
        module,
        &working,
    )
    .map_err(|error| {
        let pair = OriginatedForm {
            form: expanded.clone(),
            authored: sexp.clone(),
        };
        reanchor_finalize_error(error, &[pair])
    })? {
        Some(Ok(prepared)) => prepared
            .staging
            .get("__expr")
            .and_then(|binding| binding.callable())
            .map(|callable| crate::pipeline::zero_arg_result(&callable.arm.scheme.ty).clone())
            .ok_or_else(|| missing_expr_error(sexp.span())),
        Some(Err(gap)) => Err(gap_error(ctx, module, &program, &gap, sexp.span())),
        None => Err(missing_expr_error(sexp.span())),
    }
}

/// Refuse a form whose head makes it a definition or a structural form.
fn refuse_definition_head(sexp: &Sexp) -> Result<(), CranelispError> {
    let Sexp::List(items, span) = sexp else {
        return Ok(());
    };
    match items.first() {
        Some(Sexp::Symbol(head, _))
            if matches!(
                head.as_str(),
                "defn"
                    | "defn-"
                    | "defmacro"
                    | "defmacro-"
                    | "deftype"
                    | "deftype-"
                    | "deftrait"
                    | "deftrait-"
                    | "impl"
                    | "import"
                    | "export"
                    | "mod"
                    | "mod-"
                    | "platform"
            ) =>
        {
            Err(definition_error(*span))
        }
        _ => Ok(()),
    }
}

fn definition_error(span: Span) -> CranelispError {
    CranelispError::TypeError {
        message: "a definition form has no type: `/type` takes one expression".into(),
        location: ErrorLocation::from_span(span),
    }
}

/// A clean check of one expression stages its `__expr`; this reports the
/// invariant's violation at the query rather than defaulting a type
/// (`design/int/result-owner.md` §4.3.1).
fn missing_expr_error(span: Span) -> CranelispError {
    CranelispError::TypeError {
        message: "`/type` staged no `__expr` to read a type from".into(),
        location: ErrorLocation::from_span(span),
    }
}

fn module_not_loaded_error(module: &ModuleFullPath, span: Span) -> CranelispError {
    CranelispError::ModuleError {
        message: format!("module '{module}' is not loaded, and `/type` loads no module"),
        location: ErrorLocation::from_span(span),
    }
}

/// A gap the evaluated turn would load and retry. `/type` reports it at the
/// reference site instead: a loaded module lacks the member, any other is not
/// loaded.
fn gap_error(
    ctx: &ModuleCompiler,
    module: &ModuleFullPath,
    program: &[TopLevel],
    gap: &ResolutionGap,
    form_span: Span,
) -> CranelispError {
    let Some(dep) = gap_target_module(gap) else {
        return CranelispError::TypeError {
            message: super::unresolved_reference_message(gap),
            location: ErrorLocation::from_span(form_span),
        };
    };
    let member = gap_member(gap);
    let reference_span = gap_reference_span(
        program,
        &GapReference {
            module: &dep,
            member: &member,
            referring_module: module,
            module_aliases: ctx.module_aliases,
        },
    );
    let span = if reference_span == Span::SYNTHETIC {
        form_span
    } else {
        reference_span
    };
    if fq_module_is_loaded(ctx, &dep) {
        module_has_no_member_error(&dep, &member, span)
    } else {
        module_not_loaded_error(&dep, span)
    }
}
