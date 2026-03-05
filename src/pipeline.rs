// Pipeline orchestration: source text -> parse -> build -> typecheck -> codegen -> execute.
//
// Single pipeline function for both batch and REPL usage.
// No `unwrap()` in this module -- all errors use `?`.

use cranelisp_types::{
    CheckResult, CompileMode, CranelispError, NoOpExpander, Program, Type, Warning,
};

/// Result of compiling and executing a source program.
pub struct PipelineResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the last expression or main function's return.
    pub ty: Type,
    /// Non-fatal warnings accumulated during compilation.
    pub warnings: Vec<Warning>,
}

/// Compile and execute source text in batch mode.
///
/// Pipeline stages:
/// 1. Parse source -> Vec<Sexp>
/// 2. Build program -> Vec<TopLevel>
/// 3. Type check -> CheckResult
/// 4. Codegen -> CompiledProgram
/// 5. Execute -> i64
pub fn compile_and_run(
    source: &str,
    mode: CompileMode,
) -> Result<PipelineResult, CranelispError> {
    // Stage 1: Parse
    let sexps = cranelisp_frontend::parse(source)?;

    // Stage 2: Build AST
    let mut expander = NoOpExpander;
    let program = cranelisp_frontend::build_program(&sexps, &mut expander)?;

    // Stage 3: Type check
    let mut tc = cranelisp_typecheck::TypeChecker::new();
    let check = tc.check_program(&program)?;

    // Determine the result type from the last defn's return type.
    let result_type = infer_result_type(&program, &check);

    // Accumulate warnings from typecheck and codegen.
    let mut all_warnings: Vec<Warning> = check.warnings.clone();

    // Stage 4: Codegen
    let compiled = cranelisp_backend::compile_program(&program, &check, mode)?;
    all_warnings.extend(compiled.warnings.iter().cloned());

    // Stage 5: Execute
    // SAFETY: compiled code was just generated and finalized by our JIT.
    let value = unsafe { compiled.execute()? };

    Ok(PipelineResult {
        value,
        ty: result_type,
        warnings: all_warnings,
    })
}

/// Determine the result type from the last zero-arg function in the program.
/// This mirrors the backend's entry_fn selection: last zero-arg defn.
fn infer_result_type(program: &Program, check: &CheckResult) -> Type {
    use cranelisp_types::TopLevel;

    // Find the last zero-arg defn (same logic as backend entry_fn).
    let last_nullary = program.iter().rev().find_map(|tl| match tl {
        TopLevel::Defn(defn) if defn.params.is_empty() => Some(defn),
        _ => None,
    });

    if let Some(defn) = last_nullary {
        // Look up the resolved return type from expr_types or method_resolutions.
        // The defn's body span should have its type recorded.
        if let Some(ty) = check.expr_types.get(&defn.body.span()) {
            return ty.clone();
        }
    }

    // Fallback: Int (convention for unknown result types).
    Type::Int
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pipeline_simple_int() {
        let result = compile_and_run("(defn main [] 42)", CompileMode::Batch).unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_pipeline_bool_true() {
        let result = compile_and_run("(defn main [] true)", CompileMode::Batch).unwrap();
        assert_eq!(result.value, 1);
        assert_eq!(result.ty, Type::Bool);
    }

    #[test]
    fn test_pipeline_parse_error() {
        let result = compile_and_run("(defn main [] ", CompileMode::Batch);
        assert!(result.is_err());
    }

    #[test]
    fn test_pipeline_interactive_mode() {
        let result = compile_and_run("(defn main [] 42)", CompileMode::Interactive).unwrap();
        assert_eq!(result.value, 42);
    }
}
