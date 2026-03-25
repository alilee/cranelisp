// Pipeline v2: unified compilation pipeline.
//
// `compile_unit()` is the single entry point for all compilation:
// batch programs, REPL forms, and module loading all flow through
// the same stages with the same types. Mode differences are expressed
// via `CompileContext` parameters.
//
// Stages:
//   1. Build AST:    Vec<Sexp> -> Vec<TopLevel>   (sexps already parsed + expanded)
//   2. Typecheck:    Vec<TopLevel> -> CheckResult  (unified multi-pass)
//   3. Codegen:      TopLevel + CheckResult -> JIT (mode-dependent)
//   4. Execute:      call entry fn -> i64          (mode-dependent)
//
// Parsing (Stage 1 of the full pipeline) and expansion (Stage 3) happen
// before `compile_unit()` is called. The caller is responsible for parsing
// source text and running macro expansion. This keeps `compile_unit()`
// focused on the type-check → codegen → execute core.

use cranelisp_types::{
    CheckResult, CompileContext, CompileMode, CranelispError, Sexp, Type, Warning,
};

use crate::pipeline::CompilationSession;

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of compiling a unit through the v2 pipeline.
///
/// Carries everything the caller needs: typecheck results, execution
/// outcome, and accumulated warnings.
pub struct CompileUnitResult {
    /// The typecheck result (method resolutions, expr_types, display info, etc.).
    /// Needed by callers for display formatting and introspection.
    pub check_result: CheckResult,

    /// If execution occurred, the raw i64 result value.
    /// None when the unit was a module load (no execution) or contained
    /// only type/trait definitions with no entry point.
    pub value: Option<i64>,

    /// Inferred type of the executed expression or entry function's return.
    /// None when no execution occurred.
    pub result_type: Option<Type>,

    /// All warnings accumulated across typecheck and codegen.
    pub warnings: Vec<Warning>,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Compile a unit of source through the unified v2 pipeline.
///
/// Takes pre-parsed, pre-expanded sexps and a `CompileContext` that
/// specifies the target module, integration strategy, and codegen mode.
///
/// # Pipeline stages
///
/// 1. **Build AST** — converts sexps to `Vec<TopLevel>` via the frontend.
/// 2. **Typecheck** — `TypeChecker::check()` runs the multi-pass pipeline
///    (register signatures → check bodies → constrained fns → mono → curry).
/// 3. **Codegen** — compiles to JIT code. Mode-dependent:
///    - `Batch`: whole-program codegen with direct calls.
///    - `Interactive`: per-defn GOT-indirect compilation.
///    - `Release`: future whole-program optimisation.
/// 4. **Execute** — calls the entry function and returns the result.
///
/// # Errors
///
/// Returns `CranelispError` for parse, type, or codegen errors.
/// Non-fatal diagnostics are accumulated in `CompileUnitResult::warnings`.
pub fn compile_unit(
    session: &mut CompilationSession,
    sexps: &[Sexp],
    ctx: &CompileContext,
) -> Result<CompileUnitResult, CranelispError> {
    // Stage 1: Build AST from expanded sexps.
    let program = cranelisp_frontend::build_program(sexps, &mut session.expander)?;

    // Stage 2: Unified multi-pass typecheck.
    let check_result = session.tc.check(&program, ctx)?;

    let mut all_warnings: Vec<Warning> = check_result.warnings.clone();

    // Stage 3 + 4: Codegen and execute, mode-dependent.
    let (value, result_type) = match ctx.compile_mode {
        CompileMode::Batch => {
            compile_and_execute_batch(&program, &check_result, &mut all_warnings)?
        }
        CompileMode::Interactive => {
            compile_and_execute_interactive(
                session,
                &program,
                &check_result,
                &mut all_warnings,
            )?
        }
        CompileMode::Release => {
            // Release mode is future work (Phase H).
            return Err(CranelispError::CodegenError {
                message: "Release compile mode not yet implemented".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }
    };

    Ok(CompileUnitResult {
        check_result,
        value,
        result_type,
        warnings: all_warnings,
    })
}

// ---------------------------------------------------------------------------
// Batch mode: whole-program codegen with direct calls
// ---------------------------------------------------------------------------

/// Compile and execute in batch mode (direct calls, whole-program).
///
/// Returns `(Option<value>, Option<result_type>)`.
fn compile_and_execute_batch(
    program: &cranelisp_types::Program,
    check: &CheckResult,
    warnings: &mut Vec<Warning>,
) -> Result<(Option<i64>, Option<Type>), CranelispError> {
    let compiled = cranelisp_backend::compile_program(program, check, CompileMode::Batch)?;
    warnings.extend(compiled.warnings.iter().cloned());

    // Determine the result type from the last zero-arg defn.
    let result_type = infer_batch_result_type(program, check);

    // SAFETY: compiled code was just generated and finalized by our JIT.
    let value = unsafe { compiled.execute()? };

    Ok((Some(value), Some(result_type)))
}

// ---------------------------------------------------------------------------
// Interactive mode: GOT-indirect per-defn compilation
// ---------------------------------------------------------------------------

/// Compile and execute in interactive mode (GOT-indirect calls).
///
/// Compiles definitions via the session's GOT state and compiles/executes
/// any bare expressions.
///
/// Returns `(Option<value>, Option<result_type>)`.
fn compile_and_execute_interactive(
    session: &mut CompilationSession,
    program: &cranelisp_types::Program,
    check: &CheckResult,
    warnings: &mut Vec<Warning>,
) -> Result<(Option<i64>, Option<Type>), CranelispError> {
    use cranelisp_types::TopLevel;

    // Separate expressions from definitions. `compile_checked_program`
    // handles Defn/TraitImpl/TypeDef/TraitDecl but skips Expr.
    let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

    // Compile definitions first (GOT registration, mono defns, etc.).
    let form_result = session.compile_checked_program(program, check)?;
    if let Some(ref result) = form_result {
        warnings.extend(result.warnings.iter().cloned());
    }

    // If there are bare expressions, compile and execute them.
    if has_expr {
        let (value, ty) = compile_and_execute_expr(session, program, check)?;
        return Ok((Some(value), Some(ty)));
    }

    let value = form_result.as_ref().map(|r| r.value);
    let result_type = form_result.map(|r| r.ty);
    Ok((value, result_type))
}

/// Compile and execute a bare expression in interactive mode.
///
/// Finds the last `TopLevel::Expr` in the program, compiles it via
/// `compile_expr_with_got_and_symbols`, and executes it.
fn compile_and_execute_expr(
    session: &mut CompilationSession,
    program: &cranelisp_types::Program,
    check: &CheckResult,
) -> Result<(i64, Type), CranelispError> {
    use cranelisp_types::{Span, TopLevel};

    // Find the last expression in the program.
    let expr = program.iter().rev().find_map(|tl| {
        if let TopLevel::Expr(e) = tl { Some(e) } else { None }
    }).ok_or_else(|| CranelispError::CodegenError {
        message: "no expression found in program".into(),
        span: Span::SYNTHETIC,
    })?;

    let extra_syms: Vec<(&str, *const u8)> = session.platform_symbols
        .iter()
        .map(|(name, ptr)| (name.as_str(), *ptr))
        .collect();

    let compiled = cranelisp_backend::compile_expr_with_got_and_symbols(
        expr,
        check,
        CompileMode::Interactive,
        Some(&mut session.got_state),
        &extra_syms,
    )?;

    // Determine the result type from display info or expr_types.
    let ty = check.display.as_ref()
        .map(|d| d.ty.clone())
        .or_else(|| check.expr_types.get(&expr.span()).cloned())
        .unwrap_or(Type::Int);

    // SAFETY: compiled code was just generated and finalized by our JIT.
    let value = unsafe { compiled.execute() };

    Ok((value, ty))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Determine the result type from the last zero-arg function in a batch program.
///
/// Mirrors the backend's entry_fn selection: last zero-arg defn.
fn infer_batch_result_type(
    program: &cranelisp_types::Program,
    check: &CheckResult,
) -> Type {
    use cranelisp_types::TopLevel;

    let last_nullary = program.iter().rev().find_map(|tl| match tl {
        TopLevel::Defn(defn) if !defn.is_multi_sig() && defn.params().is_empty() => Some(defn),
        _ => None,
    });

    if let Some(defn) = last_nullary {
        if let Some(ty) = check.expr_types.get(&defn.body().span()) {
            return ty.clone();
        }
    }

    // Fallback: Int (convention for unknown result types).
    Type::Int
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{CompileContext, CompileMode, ModuleFullPath, ModuleStrategy};

    /// Helper: parse source text into sexps.
    fn parse(source: &str) -> Vec<Sexp> {
        cranelisp_frontend::parse(source).expect("parse failed")
    }

    /// Helper: build a batch compile context targeting the "user" module.
    ///
    /// Uses Additive strategy because the "user" module is pre-populated
    /// with builtins by TypeChecker::new(). Replace would wipe those.
    fn batch_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            strategy: ModuleStrategy::Additive,
            compile_mode: CompileMode::Batch,
        }
    }

    /// Helper: build an additive (REPL-like) compile context.
    fn additive_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("user"),
            strategy: ModuleStrategy::Additive,
            compile_mode: CompileMode::Interactive,
        }
    }

    // spec: design/arch/pipeline-v2.md §2 — unified pipeline stages
    #[test]
    fn batch_defn_main_returns_value() {
        let sexps = parse("(defn main [] (if true 3 0))");
        let mut session = CompilationSession::new();
        let result = compile_unit(&mut session, &sexps, &batch_ctx())
            .expect("compile_unit failed");

        assert_eq!(result.value, Some(3));
    }

    // spec: design/arch/pipeline-v2.md §5.5 — Expr handling via synthetic defn
    #[test]
    fn additive_bare_expression() {
        let sexps = parse("(if true 3 0)");
        let mut session = CompilationSession::new();
        let result = compile_unit(&mut session, &sexps, &additive_ctx())
            .expect("compile_unit failed");

        assert_eq!(result.value, Some(3));
    }
}
