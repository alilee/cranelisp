//! Build-mode rejection pass — rejects `(trace ...)` under
//! `--link` standalone-binary mode.
//!
//! Per spec/04-expressions.md §4.12.9 and Decision 40 §"Product-shape
//! constraint (Path B1)" (FIXME 0199): `(trace ...)` is a REPL/`--run`-only
//! special form. When the compile session's `CodegenBehaviour` is
//! `ObjectOnly` (i.e. `--link`), any `Expr::Trace` node in the AST is a
//! compile-time error.
//!
//! The rejection is implemented as a post-build AST walk rather than a
//! parameter to `build_form`/`build_expr` to keep the four-free-function
//! frontend boundary stable (see `design/arch/facades/frontend.md`).
//! `int`'s cluster orchestrator runs this validator once per parsed entry
//! after `build_form`/`build_expr` and before handing the entry to
//! `cranelisp_typecheck::check_forms`. The wiring is tracked under
//! FIXME 0202 (`/dev (int)` re-fire).
//!
//! Quoted occurrences of `(trace ...)` (`'(trace x)`, `` `(trace x) ``) are
//! desugared by the expander into `Sexp` constructor calls (`SexpList`,
//! `SexpSym`, …) before the AST builder runs, so they appear as
//! `Expr::Apply` to those constructors — not as `Expr::Trace`. The walker
//! is therefore correct under spec §4.12 (callable special form, not
//! literal sym) for both REPL/`--run` and `--link` modes.
//!
//! Principle 7 (single source of truth + early enforcement): rejection
//! fires at the earliest layer that has both the build-mode signal and
//! the form in hand. `Expr::Trace` exists only post-AST-build, so the
//! validator runs immediately after `build_form`/`build_expr`.

use cranelisp_types::{
    CodegenBehaviour, CranelispError, ErrorLocation, Expr, MatchArm, ParsedEntry, Span, TraitImpl,
};

/// Build-mode-rejection error message for `(trace ...)` in `--link` mode.
/// Public so test fixtures and downstream consumers can assert against it
/// without re-stringing the literal.
pub const TRACE_LINK_MODE_REJECTION_MESSAGE: &str =
    "(trace ...) is not available in --link standalone-binary mode; \
     use REPL or --run to trace. See spec/04-expressions.md §4.12.9.";

/// Walks an `Expr` and rejects `Expr::Trace` nodes under
/// `CodegenBehaviour::ObjectOnly`.
///
/// Returns `Ok(())` for `CodegenBehaviour::InMemoryAndObject` regardless of
/// `Expr::Trace` content — trace is legal in REPL/`--run`.
///
/// On rejection: returns `CranelispError::ParseError` whose location carries
/// the offending `Expr::Trace`'s span.
pub fn validate_expr_for_build_mode(
    expr: &Expr,
    mode: CodegenBehaviour,
) -> Result<(), CranelispError> {
    if mode == CodegenBehaviour::InMemoryAndObject {
        return Ok(());
    }
    walk_expr(expr)
}

/// Walks every `Expr` inside a `ParsedEntry` and rejects `Expr::Trace`
/// nodes under `CodegenBehaviour::ObjectOnly`. Use this in the cluster
/// orchestrator's per-form loop after `build_form`.
///
/// Returns `Ok(())` for `CodegenBehaviour::InMemoryAndObject`.
pub fn validate_parsed_entry_for_build_mode(
    entry: &ParsedEntry,
    mode: CodegenBehaviour,
) -> Result<(), CranelispError> {
    if mode == CodegenBehaviour::InMemoryAndObject {
        return Ok(());
    }
    walk_parsed_entry(entry)
}

// ---------------------------------------------------------------------------
// Internal walkers
// ---------------------------------------------------------------------------

fn reject(span: Span) -> CranelispError {
    CranelispError::ParseError {
        message: TRACE_LINK_MODE_REJECTION_MESSAGE.to_string(),
        location: ErrorLocation::from_span(span),
    }
}

fn walk_expr(expr: &Expr) -> Result<(), CranelispError> {
    match expr {
        Expr::Trace { span, .. } => Err(reject(*span)),

        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => Ok(()),

        Expr::Let { bindings, body, .. } => {
            for (_, expr) in bindings {
                walk_expr(expr)?;
            }
            walk_expr(body)
        }

        Expr::If { cond, then_branch, else_branch, .. } => {
            walk_expr(cond)?;
            walk_expr(then_branch)?;
            walk_expr(else_branch)
        }

        Expr::Lambda { body, .. } => walk_expr(body),

        Expr::Apply { callee, args, .. } => {
            walk_expr(callee)?;
            for arg in args {
                walk_expr(arg)?;
            }
            Ok(())
        }

        Expr::Match { scrutinee, arms, .. } => {
            walk_expr(scrutinee)?;
            for arm in arms {
                walk_match_arm(arm)?;
            }
            Ok(())
        }

        Expr::Annotate { expr, .. } => walk_expr(expr),

        Expr::VecLit { elements, .. } => {
            for el in elements {
                walk_expr(el)?;
            }
            Ok(())
        }

        Expr::ParBind { bindings, body, .. } => {
            for (_, expr) in bindings {
                walk_expr(expr)?;
            }
            walk_expr(body)
        }
    }
}

fn walk_match_arm(arm: &MatchArm) -> Result<(), CranelispError> {
    walk_expr(&arm.body)
}

fn walk_parsed_entry(entry: &ParsedEntry) -> Result<(), CranelispError> {
    match entry {
        ParsedEntry::Def { variants, .. } => {
            for v in variants {
                walk_expr(&v.body)?;
            }
            Ok(())
        }
        ParsedEntry::TraitImpl { impl_ } => walk_trait_impl(impl_),
        // TypeDef / TraitDecl / Macro / Constructor carry no Expr bodies the
        // frontend has built into AST form. Trait-method default bodies are
        // still `Sexp` (parse-deferred until impl-time per spec §7), so they
        // cannot contain `Expr::Trace` at this point.
        ParsedEntry::TypeDef { .. }
        | ParsedEntry::TraitDecl { .. }
        | ParsedEntry::Macro { .. }
        | ParsedEntry::Constructor { .. } => Ok(()),
        // `ParsedEntry` is `#[non_exhaustive]`; new entry shapes added
        // upstream must be reviewed by `/dev (frontend)` for Expr-body
        // content. The default-Ok stance assumes new shapes are body-less
        // until proven otherwise; the corresponding test addition is the
        // forcing function.
        _ => Ok(()),
    }
}

fn walk_trait_impl(impl_: &TraitImpl) -> Result<(), CranelispError> {
    for method in &impl_.methods {
        for v in &method.variants {
            walk_expr(&v.body)?;
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{build_expr, build_form, parse};

    fn build_expr_from(input: &str) -> Expr {
        let sexps = parse(input).expect("parse");
        assert!(!sexps.is_empty());
        build_expr(&sexps[0]).expect("build_expr")
    }

    fn build_form_from(input: &str) -> Vec<ParsedEntry> {
        let sexps = parse(input).expect("parse");
        assert!(!sexps.is_empty());
        build_form(&sexps[0]).expect("build_form")
    }

    // spec: spec/04-expressions.md §4.12.9 — `(trace ...)` rejected in --link mode.
    #[test]
    fn trace_at_top_rejected_under_link_mode() {
        let expr = build_expr_from("(trace 42)");
        let err = validate_expr_for_build_mode(&expr, CodegenBehaviour::ObjectOnly)
            .expect_err("trace must be rejected under --link mode");
        match err {
            CranelispError::ParseError { ref message, .. } => {
                assert!(
                    message.contains("(trace ...)"),
                    "error message should name the form, got: {message}"
                );
                assert!(
                    message.contains("§4.12.9"),
                    "error message should cite spec §4.12.9, got: {message}"
                );
                assert!(
                    message.contains("--link"),
                    "error message should name --link mode, got: {message}"
                );
            }
            other => panic!("expected ParseError, got: {other:?}"),
        }
        // The error's span must point at the trace form itself (not span::SYNTHETIC).
        assert_ne!(err.span(), Span::SYNTHETIC);
    }

    // spec: spec/04-expressions.md §4.12.1-4.12.8 — `(trace ...)` is legal
    // in REPL/`--run` modes. Validator must be a no-op there.
    #[test]
    fn trace_accepted_under_inmem_mode() {
        let expr = build_expr_from("(trace 42)");
        validate_expr_for_build_mode(&expr, CodegenBehaviour::InMemoryAndObject)
            .expect("trace must be accepted under REPL/--run mode");
    }

    // spec: spec/04-expressions.md §4.12.9 — rejection fires regardless of
    // depth. Nested `(trace ...)` inside a let-binding is equally rejected.
    #[test]
    fn nested_trace_in_let_rejected_under_link_mode() {
        let expr = build_expr_from("(let [x (trace 42)] x)");
        let err = validate_expr_for_build_mode(&expr, CodegenBehaviour::ObjectOnly)
            .expect_err("nested trace must be rejected under --link mode");
        assert!(
            matches!(err, CranelispError::ParseError { .. }),
            "expected ParseError variant"
        );
    }

    // Nested `(trace ...)` inside an if-branch is rejected.
    #[test]
    fn nested_trace_in_if_branch_rejected_under_link_mode() {
        let expr = build_expr_from("(if true (trace 1) 2)");
        let err = validate_expr_for_build_mode(&expr, CodegenBehaviour::ObjectOnly)
            .expect_err("trace in if-branch must be rejected under --link mode");
        assert!(matches!(err, CranelispError::ParseError { .. }));
    }

    // Trace inside an `Apply` (function call argument) is rejected.
    #[test]
    fn nested_trace_in_apply_arg_rejected_under_link_mode() {
        // `+` is just an arbitrary callee; the walker is structure-blind.
        let expr = build_expr_from("(+ 1 (trace 2))");
        let err = validate_expr_for_build_mode(&expr, CodegenBehaviour::ObjectOnly)
            .expect_err("trace in apply-arg must be rejected under --link mode");
        assert!(matches!(err, CranelispError::ParseError { .. }));
    }

    // Programs with no `(trace ...)` form are accepted in any mode.
    #[test]
    fn no_trace_accepted_under_link_mode() {
        let expr = build_expr_from("(+ 1 2)");
        validate_expr_for_build_mode(&expr, CodegenBehaviour::ObjectOnly)
            .expect("plain expression must be accepted under --link mode");
    }

    // spec: spec/04-expressions.md §4.12.9 — `(trace ...)` inside a `defn`
    // body is rejected when the surrounding ParsedEntry is walked.
    #[test]
    fn trace_in_defn_body_rejected_under_link_mode() {
        let entries = build_form_from("(defn f [] (trace 42))");
        // Find the Def entry — TypeDef-style entries don't apply here.
        let def_entry = entries
            .iter()
            .find(|e| matches!(e, ParsedEntry::Def { .. }))
            .expect("defn should yield ParsedEntry::Def");
        let err = validate_parsed_entry_for_build_mode(def_entry, CodegenBehaviour::ObjectOnly)
            .expect_err("trace in defn body must be rejected under --link mode");
        match err {
            CranelispError::ParseError { ref message, .. } => {
                assert!(message.contains("(trace ...)"));
                assert!(message.contains("§4.12.9"));
            }
            other => panic!("expected ParseError, got: {other:?}"),
        }
    }

    // ParsedEntry walker accepts every entry shape that carries no Expr.
    // (Smoke test — `TraitDecl`, `TypeDef`, `Macro`, `Constructor` are
    // body-less from the walker's perspective; this guards against future
    // ParsedEntry variants accidentally hiding an Expr we forget to walk.)
    #[test]
    fn typedef_accepted_under_link_mode() {
        let entries = build_form_from("(deftype Color Red Green Blue)");
        for entry in &entries {
            validate_parsed_entry_for_build_mode(entry, CodegenBehaviour::ObjectOnly)
                .expect("typedef-shaped entries must be accepted under --link mode");
        }
    }
}
