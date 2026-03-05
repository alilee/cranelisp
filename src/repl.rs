// REPL session: interactive read-eval-print loop with persistent state.
//
// The TypeChecker and ModuleCodegenState persist across inputs so that
// function definitions and type definitions accumulate. Each input is
// parsed, type-checked, compiled, and executed independently.
//
// Error recovery: on any error, the TypeChecker is restored to its
// pre-input snapshot so the session remains usable.
//
// No `unwrap()` in this module -- all errors use `?`.

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use cranelisp_backend::got::ModuleCodegenState;
use cranelisp_backend::jit::Jit;
use cranelisp_typecheck::TypeChecker;
use cranelisp_types::{
    CompileMode, CranelispError, NoOpExpander, ReplCheckResult, ReplInput, Symbol, Type, Warning,
};

/// Result of evaluating one REPL input.
pub struct ReplResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the input.
    pub ty: Type,
    /// Whether this was a definition (defn/deftype) rather than an expression.
    pub is_definition: bool,
    /// Non-fatal warnings.
    pub warnings: Vec<Warning>,
}

/// Persistent REPL session state.
pub struct ReplSession {
    /// Type checker state (persists across inputs).
    pub tc: TypeChecker,
    /// Backend GOT state (persists across inputs for function redefinition).
    pub got_state: ModuleCodegenState,
    /// JIT instances that must stay alive (their code is referenced via GOT).
    /// Each defn compilation creates a new JIT; we keep them alive here.
    jit_modules: Vec<Jit>,
}

impl ReplSession {
    /// Create a new REPL session.
    pub fn new() -> Self {
        ReplSession {
            tc: TypeChecker::new(),
            got_state: ModuleCodegenState::new(),
            jit_modules: Vec::new(),
        }
    }

    /// Evaluate a single source input, returning the result.
    ///
    /// On error, restores the TypeChecker to its pre-input state.
    pub fn eval(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
        // Parse the source into sexps.
        let sexps = cranelisp_frontend::parse(source)?;

        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty input".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }

        // Build REPL input from the first sexp.
        let mut expander = NoOpExpander;
        let input = cranelisp_frontend::build_repl_input(&sexps[0], &mut expander)?;

        // Snapshot for error recovery.
        let snapshot = self.tc.snapshot();

        // Type check the input.
        let check_result = match self.tc.check_repl_input(&input) {
            Ok(r) => r,
            Err(e) => {
                self.tc.restore(snapshot);
                return Err(e);
            }
        };

        // Compile and execute.
        match self.compile_and_execute(&input, &check_result) {
            Ok(result) => Ok(result),
            Err(e) => {
                self.tc.restore(snapshot);
                Err(e)
            }
        }
    }

    /// Compile and execute a checked REPL input.
    fn compile_and_execute(
        &mut self,
        input: &ReplInput,
        check_result: &ReplCheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let warnings: Vec<Warning> = check_result.warnings.clone();

        match input {
            ReplInput::Expr(expr) => {
                // Build a CheckResult for the backend.
                let check = self.build_check_for_backend(check_result);
                let value = cranelisp_backend::compile_and_run_expr_with_got(
                    expr,
                    &check,
                    CompileMode::Interactive,
                    Some(&mut self.got_state),
                )?;
                Ok(ReplResult {
                    value,
                    ty: check_result.ty.clone(),
                    is_definition: false,
                    warnings,
                })
            }

            ReplInput::Defn(defn) => {
                // Compile the defn using a fresh JIT but the existing GOT state.
                let check = self.build_check_for_backend(check_result);
                let mut jit = Jit::new()?;

                // Declare just this function.
                let func_ids = jit.declare_functions(&[defn])?;

                // Ensure a GOT slot exists for this function.
                let slot = self.got_state.ensure_slot_for(&defn.name)?;

                // Build GOT slot map from existing state + this new function.
                let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
                for (name, dc) in &self.got_state.def_codegen {
                    if let Some(s) = dc.got_slot {
                        got_slots.insert(name.clone(), s);
                    }
                }
                got_slots.insert(defn.name.clone(), slot);

                let got_base = self.got_state.got_base_ptr() as i64;

                // Compile the function with awareness of existing GOT.
                let _clif_ir = jit.compile_defn(
                    defn,
                    &check,
                    CompileMode::Interactive,
                    &func_ids,
                    Some(&got_slots),
                    Some(got_base),
                )?;

                // Finalize and get the code pointer.
                let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params.len())?;

                // Update the GOT slot with the new code pointer.
                self.got_state.update_slot(slot, code_ptr);

                // Record codegen info.
                let entry = self.got_state.def_codegen.entry(defn.name.clone()).or_default();
                entry.code_ptr = Some(code_ptr);
                entry.got_slot = Some(slot);
                entry.param_count = Some(defn.params.len());

                // Keep JIT alive so code pointer remains valid.
                self.jit_modules.push(jit);

                // For defn, execute if it's zero-arg, otherwise return 0.
                let value = if defn.params.is_empty() {
                    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
                    func()
                } else {
                    0
                };

                Ok(ReplResult {
                    value,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                })
            }

            ReplInput::TypeDef { .. } => {
                // Type definitions don't produce a runtime value.
                Ok(ReplResult {
                    value: 0,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                })
            }

            // Not supported in Ring 0.
            ReplInput::DefnMulti { span, .. } => Err(CranelispError::TypeError {
                message: "multi-signature functions not supported in Ring 0".into(),
                span: *span,
            }),
            ReplInput::TraitDecl(decl) => Err(CranelispError::TypeError {
                message: "trait declarations not supported in Ring 0".into(),
                span: decl.span,
            }),
            ReplInput::TraitImpl(impl_) => Err(CranelispError::TypeError {
                message: "trait implementations not supported in Ring 0".into(),
                span: impl_.span,
            }),
        }
    }

    /// Build a CheckResult suitable for the backend from a ReplCheckResult.
    fn build_check_for_backend(
        &self,
        repl_check: &ReplCheckResult,
    ) -> cranelisp_types::CheckResult {
        cranelisp_types::CheckResult {
            method_resolutions: repl_check.method_resolutions.clone(),
            constrained_fn_names: std::collections::HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: repl_check.expr_types.clone(),
            default_method_defns: Vec::new(),
            warnings: repl_check.warnings.clone(),
            type_defs: repl_check.type_defs.clone(),
            constructor_to_type: repl_check.constructor_to_type.clone(),
        }
    }
}

impl Default for ReplSession {
    fn default() -> Self {
        Self::new()
    }
}

/// Format a result value for REPL display.
///
/// Format: `:Type value`
/// - Bool: `true` / `false`
/// - Float: reinterpret i64 bits as f64
/// - Int: decimal integer
/// - Other: decimal integer (fallback)
pub fn format_result(value: i64, ty: &Type) -> String {
    match ty {
        Type::Bool => {
            let display_val = if value != 0 { "true" } else { "false" };
            format!(":Bool {display_val}")
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            format!(":Float {f}")
        }
        Type::Int => format!(":Int {value}"),
        other => format!(":{other} {value}"),
    }
}

/// Run the interactive REPL loop.
///
/// Reads lines from stdin, evaluates them, prints results.
/// Errors are printed without crashing the session.
pub fn run_repl() {
    let mut session = ReplSession::new();
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    let _ = write!(stdout, "> ");
    let _ = stdout.flush();

    let mut buffer = String::new();

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        buffer.push_str(&line);

        // Check for balanced parentheses for multi-line input.
        if !parens_balanced(&buffer) {
            buffer.push('\n');
            let _ = write!(stdout, "  ");
            let _ = stdout.flush();
            continue;
        }

        let input = buffer.trim();
        if input.is_empty() {
            buffer.clear();
            let _ = write!(stdout, "> ");
            let _ = stdout.flush();
            continue;
        }

        match session.eval(input) {
            Ok(result) => {
                // Print warnings first.
                for w in &result.warnings {
                    let _ = writeln!(stdout, "warning: {}", w.message);
                }
                // Print the result.
                let _ = writeln!(stdout, "{}", format_result(result.value, &result.ty));
            }
            Err(e) => {
                let _ = writeln!(stdout, "error: {e}");
            }
        }

        buffer.clear();
        let _ = write!(stdout, "> ");
        let _ = stdout.flush();
    }

    let _ = writeln!(stdout);
}

/// Check if parentheses are balanced in the input.
fn parens_balanced(input: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut prev_char = '\0';

    for ch in input.chars() {
        match ch {
            '"' if prev_char != '\\' => in_string = !in_string,
            '(' if !in_string => depth += 1,
            ')' if !in_string => depth -= 1,
            _ => {}
        }
        prev_char = ch;
    }

    depth <= 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_result_int() {
        assert_eq!(format_result(42, &Type::Int), ":Int 42");
    }

    #[test]
    fn test_format_result_bool_true() {
        assert_eq!(format_result(1, &Type::Bool), ":Bool true");
    }

    #[test]
    fn test_format_result_bool_false() {
        assert_eq!(format_result(0, &Type::Bool), ":Bool false");
    }

    #[test]
    fn test_format_result_float() {
        let bits = 1.234_f64.to_bits() as i64;
        let result = format_result(bits, &Type::Float);
        assert!(result.starts_with(":Float 1.234"));
    }

    #[test]
    fn test_parens_balanced_simple() {
        assert!(parens_balanced("(+ 1 2)"));
        assert!(!parens_balanced("(+ 1 2"));
        assert!(parens_balanced("42"));
    }

    #[test]
    fn test_parens_balanced_nested() {
        assert!(parens_balanced("(defn main [] (+ 1 2))"));
        assert!(!parens_balanced("(defn main [] (+ 1 2)"));
    }

    #[test]
    fn test_parens_balanced_string() {
        assert!(parens_balanced("\"hello (world\""));
    }

    #[test]
    fn test_session_eval_int() {
        let mut session = ReplSession::new();
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_session_error_recovery() {
        let mut session = ReplSession::new();
        // This should error (parse error).
        let err = session.eval("(+ 1");
        assert!(err.is_err());
        // Session should still work after error.
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }
}
