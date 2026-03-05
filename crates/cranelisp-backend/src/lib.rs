// cranelisp-backend: Cranelift IR codegen, JIT, RC emission, caching, linking.
//
// Public API:
// - compile_program: batch compilation of a full program
// - compile_and_run_expr_with_got: compile and execute a single expression (REPL)
// - Jit, ModuleCodegenState: exposed for REPL session management

pub mod codegen_types;
pub mod compiler;
pub mod got;
pub mod jit;
pub mod operators;

use std::collections::HashMap;

use cranelisp_types::{
    CheckResult, CompileMode, CranelispError, Defn, Expr, Program, Span, Symbol, TopLevel,
    Warning,
};

use crate::jit::Jit;

/// Result of compiling a batch program. Holds the JIT and entry point
/// so the caller can execute and then drop the JIT.
pub struct CompiledProgram {
    // Kept alive so JIT-compiled code pointers remain valid.
    #[allow(dead_code)]
    jit: Jit,
    entry_ptr: *const u8,
    // Kept alive for Interactive mode GOT lifetime.
    #[allow(dead_code)]
    _got_state: Option<got::ModuleCodegenState>,
    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

impl CompiledProgram {
    /// Execute the compiled program.
    ///
    /// # Safety
    ///
    /// The entry_ptr must point to valid JIT-compiled code with the signature
    /// `extern "C" fn() -> i64`. This is guaranteed when CompiledProgram was
    /// produced by `compile_program`.
    pub unsafe fn execute(&self) -> Result<i64, CranelispError> {
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(self.entry_ptr) };
        Ok(func())
    }
}

/// Compile a batch program: declare all functions, compile them, finalize.
///
/// The last zero-arg function in the program is the entry point.
/// Returns a CompiledProgram that can be executed.
pub fn compile_program(
    program: &Program,
    check: &CheckResult,
    mode: CompileMode,
) -> Result<CompiledProgram, CranelispError> {
    let mut jit = Jit::new()?;

    // Collect all defns from the program.
    let defns: Vec<&Defn> = program
        .iter()
        .filter_map(|tl| match tl {
            TopLevel::Defn(defn) => Some(defn),
            _ => None,
        })
        .collect();

    if defns.is_empty() {
        return Err(CranelispError::CodegenError {
            message: "no function definitions in program".into(),
            span: Span::SYNTHETIC,
        });
    }

    // Declare all functions first (so they can reference each other).
    let func_ids = jit.declare_functions(&defns)?;

    // In Interactive mode, set up a temporary GOT so GOT-indirect calls work.
    let (got_slots, mut got_state) = if mode == CompileMode::Interactive {
        let mut state = got::ModuleCodegenState::new();
        let mut slots = HashMap::new();
        for defn in &defns {
            let slot = state.ensure_slot_for(&defn.name)?;
            slots.insert(defn.name.clone(), slot);
        }
        (Some(slots), Some(state))
    } else {
        (None, None)
    };

    let got_base_ptr = got_state.as_mut().map(|s| s.got_base_ptr() as i64);

    // Compile each function.
    for defn in &defns {
        jit.compile_defn(
            defn,
            check,
            mode,
            &func_ids,
            got_slots.as_ref(),
            got_base_ptr,
        )?;
    }

    // Find the entry function (last zero-arg defn).
    let entry_defn = defns
        .iter()
        .rev()
        .find(|d| d.params.is_empty())
        .ok_or_else(|| CranelispError::CodegenError {
            message: "no zero-arg function to use as entry point".into(),
            span: Span::SYNTHETIC,
        })?;

    let entry_ptr = jit.finalize_and_get_ptr(&entry_defn.name, 0)?;

    // In Interactive mode, populate GOT slots with finalized function pointers.
    if let (Some(slots), Some(state)) = (&got_slots, &mut got_state) {
        for (name, &slot) in slots {
            if let Some(&func_id) = func_ids.get(name) {
                let ptr = jit.get_finalized_ptr(func_id);
                state.update_slot(slot, ptr);
            }
        }
    }

    Ok(CompiledProgram {
        jit,
        entry_ptr,
        // Keep GOT state alive alongside the JIT so code pointers remain valid.
        _got_state: got_state,
        warnings: Vec::new(),
    })
}

/// Compile and execute a single expression in Interactive mode.
///
/// Wraps the expression in a synthetic zero-arg function, compiles it,
/// executes it, and returns the i64 result.
///
/// If `got_state` is provided, GOT-indirect calls are used.
pub fn compile_and_run_expr_with_got(
    expr: &Expr,
    check: &CheckResult,
    mode: CompileMode,
    got_state: Option<&mut got::ModuleCodegenState>,
) -> Result<i64, CranelispError> {
    let mut jit = Jit::new()?;

    // Wrap expression in a synthetic zero-arg function.
    let wrapper_name = Symbol::from("__repl_expr__");
    let wrapper_defn = Defn {
        name: wrapper_name.clone(),
        params: vec![],
        param_annotations: vec![],
        visibility: cranelisp_types::Visibility::Public,
        body: expr.clone(),
        docstring: None,
        span: expr.span(),
    };

    let func_ids = jit.declare_functions(&[&wrapper_defn])?;

    // Get GOT info if available.
    let (got_slots, got_base_ptr) = if let Some(state) = got_state {
        let mut slots: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &state.def_codegen {
            if let Some(slot) = dc.got_slot {
                slots.insert(name.clone(), slot);
            }
        }
        let base = state.got_base_ptr() as i64;
        (Some(slots), Some(base))
    } else {
        (None, None)
    };

    jit.compile_defn(
        &wrapper_defn,
        check,
        mode,
        &func_ids,
        got_slots.as_ref(),
        got_base_ptr,
    )?;

    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    // SAFETY: code_ptr points to a just-compiled zero-arg function returning i64.
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    Ok(func())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        CheckResult, CompileMode, Defn, Expr, Span, Symbol, TopLevel,
    };
    use std::collections::{HashMap, HashSet};

    fn empty_check() -> CheckResult {
        CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        }
    }

    #[test]
    fn test_compile_program_simple() {
        let defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit {
                value: 42,
                span: Span::new(0, 2),
            },
            docstring: None,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Batch).unwrap();
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 42);
    }

    #[test]
    fn test_compile_program_no_defns() {
        let program: Program = vec![];
        let check = empty_check();

        let result = compile_program(&program, &check, CompileMode::Batch);
        assert!(result.is_err());
    }

    #[test]
    fn test_compile_and_run_expr() {
        let expr = Expr::IntLit {
            value: 99,
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None).unwrap();
        assert_eq!(value, 99);
    }

    #[test]
    fn test_compile_program_interactive_mode() {
        let defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit {
                value: 7,
                span: Span::new(0, 1),
            },
            docstring: None,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Interactive).unwrap();
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 7);
    }

    #[test]
    fn test_compile_and_run_expr_with_got_state() {
        let expr = Expr::IntLit {
            value: 55,
            span: Span::new(0, 2),
        };
        let check = empty_check();
        let mut got = got::ModuleCodegenState::new();

        let value = compile_and_run_expr_with_got(
            &expr,
            &check,
            CompileMode::Interactive,
            Some(&mut got),
        ).unwrap();
        assert_eq!(value, 55);
    }

    #[test]
    fn test_compile_program_multiple_defns() {
        // Two functions: helper and main. Main returns 100.
        let helper = Defn {
            name: Symbol::from("helper"),
            params: vec![Symbol::from("x")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(20, 21),
            },
            docstring: None,
            span: Span::new(10, 30),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit {
                value: 100,
                span: Span::new(40, 43),
            },
            docstring: None,
            span: Span::new(35, 50),
        };

        let program: Program = vec![TopLevel::Defn(helper), TopLevel::Defn(main_defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Batch).unwrap();
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 100);
    }

    #[test]
    fn test_compile_and_run_expr_bool() {
        let expr = Expr::BoolLit {
            value: true,
            span: Span::new(0, 4),
        };
        let check = empty_check();

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None).unwrap();
        assert_eq!(value, 1);
    }
}
