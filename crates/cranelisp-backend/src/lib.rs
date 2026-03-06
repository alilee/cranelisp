// cranelisp-backend: Cranelift IR codegen, JIT, RC emission, caching, linking.
//
// Public API:
// - compile_program: batch compilation of a full program
// - compile_and_run_expr_with_got: compile and execute a single expression (REPL)
// - Jit, ModuleCodegenState: exposed for REPL session management

pub mod codegen_types;
pub mod compiler;
pub mod got;
pub mod heap;
pub mod jit;
pub mod operators;

use std::collections::HashMap;

use cranelift_module::FuncId;

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

    // Declare runtime intrinsics (Ring 1 heap infrastructure).
    jit.declare_intrinsics()?;

    // Collect all defns from the program, skipping constrained fn base definitions.
    // Constrained fns are templates — only their monomorphised specializations
    // (in check.mono_defns) are compiled.
    let defns: Vec<&Defn> = program
        .iter()
        .filter_map(|tl| match tl {
            TopLevel::Defn(defn) => {
                if check.constrained_fn_names.contains(&defn.name) {
                    None // Skip constrained fn base defs — templates only
                } else {
                    Some(defn)
                }
            }
            _ => None,
        })
        .collect();

    // Collect additional defns: default method impls and mono specializations.
    let extra_defns = collect_extra_defns(check);

    if defns.is_empty() && extra_defns.is_empty() {
        return Err(CranelispError::CodegenError {
            message: "no function definitions in program".into(),
            span: Span::SYNTHETIC,
        });
    }

    // Build full list of defn references for declaration.
    let mut all_defn_refs: Vec<&Defn> = defns.clone();
    for d in &extra_defns {
        all_defn_refs.push(d);
    }

    // Declare all functions first (so they can reference each other).
    let func_ids = jit.declare_functions(&all_defn_refs)?;

    // Build function arity map for named-function-as-value closure wrappers.
    let func_arities: HashMap<Symbol, usize> = all_defn_refs
        .iter()
        .map(|d| (d.name.clone(), d.params.len()))
        .collect();

    // In Interactive mode, set up a temporary GOT so GOT-indirect calls work.
    let (got_slots, mut got_state) = if mode == CompileMode::Interactive {
        let mut state = got::ModuleCodegenState::new();
        let mut slots = HashMap::new();
        for defn in &all_defn_refs {
            let slot = state.ensure_slot_for(&defn.name)?;
            slots.insert(defn.name.clone(), slot);
        }
        (Some(slots), Some(state))
    } else {
        (None, None)
    };

    let got_base_ptr = got_state.as_mut().map(|s| s.got_base_ptr() as i64);

    // Build the compilation context once for all functions.
    let compile_ctx = jit.build_compile_context(
        check,
        mode,
        &func_ids,
        &func_arities,
        got_slots.as_ref(),
        got_base_ptr,
    );

    // Compile each regular function.
    for defn in &defns {
        jit.compile_defn(defn, compile_ctx)?;
    }

    // Compile default method defns with the main resolutions.
    for defn in &check.default_method_defns {
        jit.compile_defn(defn, compile_ctx)?;
    }

    // Compile mono specializations with their per-specialization resolutions.
    compile_mono_defns(&mut jit, check, mode, &func_ids, &func_arities,
                       got_slots.as_ref(), got_base_ptr)?;

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

/// Collect extra defns from CheckResult: default method impls and mono specializations.
///
/// These are additional functions that need to be declared and compiled alongside
/// the regular program defns.
fn collect_extra_defns(check: &CheckResult) -> Vec<Defn> {
    let mut extras = Vec::new();
    for d in &check.default_method_defns {
        extras.push(d.clone());
    }
    for mono in &check.mono_defns {
        extras.push(mono.defn.clone());
    }
    extras
}

/// Compile monomorphised specializations with their per-specialization resolutions.
///
/// Each MonoDefn carries its own method_resolutions (from the specific type
/// instantiation). We build a temporary CheckResult overlay for each one.
fn compile_mono_defns(
    jit: &mut Jit,
    check: &CheckResult,
    mode: CompileMode,
    func_ids: &HashMap<Symbol, FuncId>,
    func_arities: &HashMap<Symbol, usize>,
    got_slots: Option<&HashMap<Symbol, usize>>,
    got_base_ptr: Option<i64>,
) -> Result<(), CranelispError> {
    for mono in &check.mono_defns {
        // Merge base resolutions with per-specialization resolutions.
        let mut merged = check.method_resolutions.clone();
        merged.extend(mono.resolutions.clone());

        // I5 fix: Use the per-mono expr_types subset instead of cloning the
        // full program expr_types map. Falls back to the full map if the
        // per-mono subset is empty (before /typecheck populates it).
        let expr_types = if mono.expr_types.is_empty() {
            check.expr_types.clone()
        } else {
            mono.expr_types.clone()
        };

        let mono_check = CheckResult {
            method_resolutions: merged,
            constrained_fn_names: check.constrained_fn_names.clone(),
            mono_defns: Vec::new(),
            expr_types,
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: check.type_defs.clone(),
            constructor_to_type: check.constructor_to_type.clone(),
        };

        let ctx = jit.build_compile_context(
            &mono_check, mode, func_ids, func_arities, got_slots, got_base_ptr,
        );
        jit.compile_defn(&mono.defn, ctx)?;
    }
    Ok(())
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

    // Declare runtime intrinsics (Ring 1 heap infrastructure).
    jit.declare_intrinsics()?;

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

    // Get GOT info and function arities if available.
    let (got_slots, got_base_ptr, func_arities) = if let Some(state) = got_state {
        let mut slots: HashMap<Symbol, usize> = HashMap::new();
        let mut arities: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &state.def_codegen {
            if let Some(slot) = dc.got_slot {
                slots.insert(name.clone(), slot);
            }
            if let Some(pc) = dc.param_count {
                arities.insert(name.clone(), pc);
            }
        }
        let base = state.got_base_ptr() as i64;
        (Some(slots), Some(base), arities)
    } else {
        (None, None, HashMap::new())
    };

    let compile_ctx = jit.build_compile_context(
        check,
        mode,
        &func_ids,
        &func_arities,
        got_slots.as_ref(),
        got_base_ptr,
    );

    jit.compile_defn(&wrapper_defn, compile_ctx)?;

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

    // --- Ring 1 tests ---

    #[test]
    fn test_compile_string_literal() {
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: Span::new(0, 7),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "string literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Read back the string content via runtime API.
        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "hello");

        // Clean up the allocation.
        cranelisp_runtime::heap_dealloc(ptr);
    }

    #[test]
    fn test_compile_empty_string_literal() {
        let expr = Expr::StringLit {
            value: String::new(),
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "empty string should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "");

        cranelisp_runtime::heap_dealloc(ptr);
    }

    #[test]
    fn test_compile_adt_data_constructor() {
        use cranelisp_types::{ConstructorInfo, FieldInfo, Type, TypeDefInfo, TypeName};

        // Define Option type with None (tag 0) and Some (tag 1, one field).
        let type_name = TypeName::from("Option");
        let mut type_defs = HashMap::new();
        type_defs.insert(
            type_name.clone(),
            TypeDefInfo {
                name: type_name.clone(),
                type_params: vec![],
                constructors: vec![
                    ConstructorInfo {
                        name: Symbol::from("None"),
                        tag: 0,
                        fields: vec![],
                        docstring: None,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Some"),
                        tag: 1,
                        fields: vec![FieldInfo {
                            name: Symbol::from("val"),
                            ty: Type::Int,
                        }],
                        docstring: None,
                    },
                ],
                docstring: None,
            },
        );

        let mut constructor_to_type = HashMap::new();
        constructor_to_type.insert(Symbol::from("None"), type_name.clone());
        constructor_to_type.insert(Symbol::from("Some"), type_name.clone());

        // Expression: (Some 42)
        let some_span = Span::new(0, 10);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(1, 5),
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: Span::new(6, 8),
            }],
            span: some_span,
        };

        let check = CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs,
            constructor_to_type,
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "ADT constructor should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify the heap layout: [header(16) | tag(1) | field(42)]
        unsafe {
            let base = ptr as *const u8;
            let tag = *(base.add(16) as *const i64);
            assert_eq!(tag, 1, "tag should be 1 for Some");
            let val = *(base.add(24) as *const i64);
            assert_eq!(val, 42, "field should be 42");
        }

        cranelisp_runtime::heap_dealloc(ptr);
    }

    #[test]
    fn test_compile_match_with_fields() {
        use cranelisp_types::{
            ConstructorInfo, FieldInfo, MatchArm, Pattern, Type, TypeDefInfo, TypeName,
        };

        // Option type as above.
        let type_name = TypeName::from("Option");
        let mut type_defs = HashMap::new();
        type_defs.insert(
            type_name.clone(),
            TypeDefInfo {
                name: type_name.clone(),
                type_params: vec![],
                constructors: vec![
                    ConstructorInfo {
                        name: Symbol::from("None"),
                        tag: 0,
                        fields: vec![],
                        docstring: None,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Some"),
                        tag: 1,
                        fields: vec![FieldInfo {
                            name: Symbol::from("val"),
                            ty: Type::Int,
                        }],
                        docstring: None,
                    },
                ],
                docstring: None,
            },
        );

        let mut constructor_to_type = HashMap::new();
        constructor_to_type.insert(Symbol::from("None"), type_name.clone());
        constructor_to_type.insert(Symbol::from("Some"), type_name.clone());

        // (match (Some 99) [(Some x) x (None) 0])
        let some_span = Span::new(10, 20);
        let match_span = Span::new(0, 50);
        let scrutinee = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(11, 15),
            }),
            args: vec![Expr::IntLit {
                value: 99,
                span: Span::new(16, 18),
            }],
            span: some_span,
        };

        let expr = Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Some"),
                        bindings: vec![Symbol::from("x")],
                        span: Span::new(22, 30),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: Span::new(31, 32),
                    },
                    span: Span::new(22, 32),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("None"),
                        bindings: vec![],
                        span: Span::new(34, 40),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: Span::new(41, 42),
                    },
                    span: Span::new(34, 42),
                },
            ],
            span: match_span,
            compiler_generated: false,
        };

        let check = CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs,
            constructor_to_type,
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "match with fields should compile: {result:?}");
        assert_eq!(result.unwrap(), 99, "match should extract field value");
    }

    #[test]
    fn test_compile_lambda_closure() {
        // (let [n 5] ((fn [x] (+ n x)) 10))
        // This tests: lambda capture of 'n', closure allocation, closure call.
        use cranelisp_types::ResolvedCall;

        let add_span = Span::new(30, 37);
        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("n"),
                Expr::IntLit {
                    value: 5,
                    span: Span::new(5, 6),
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: Span::new(31, 32),
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: Span::new(33, 34),
                            },
                            Expr::Var {
                                name: Symbol::from("x"),
                                span: Span::new(35, 36),
                            },
                        ],
                        span: add_span,
                    }),
                    span: Span::new(10, 40),
                }),
                args: vec![Expr::IntLit {
                    value: 10,
                    span: Span::new(42, 44),
                }],
                span: Span::new(10, 45),
            }),
            span: Span::new(0, 46),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "closure should compile: {result:?}");
        assert_eq!(result.unwrap(), 15, "5 + 10 = 15");
    }

    // --- Vec codegen tests ---

    #[test]
    fn test_compile_empty_vec_literal() {
        let expr = Expr::VecLit {
            elements: vec![],
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "empty vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 0.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 0);

        // Clean up.
        cranelisp_runtime::vec_drop(ptr, 0);
    }

    #[test]
    fn test_compile_vec_literal_with_ints() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 10, span: Span::new(1, 3) },
                Expr::IntLit { value: 20, span: Span::new(4, 6) },
                Expr::IntLit { value: 30, span: Span::new(7, 9) },
            ],
            span: Span::new(0, 10),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 3.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        // Verify element values from data buffer.
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(heap::HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64);
            assert_eq!(*data_ptr, 10);
            assert_eq!(*data_ptr.add(1), 20);
            assert_eq!(*data_ptr.add(2), 30);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    #[test]
    fn test_compile_vec_literal_single_element() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1, 3) },
            ],
            span: Span::new(0, 4),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "single-element vec should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 42);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    #[test]
    fn test_compile_vec_literal_with_bool_elements() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: Span::new(1, 5) },
                Expr::BoolLit { value: false, span: Span::new(6, 11) },
            ],
            span: Span::new(0, 12),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "bool vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 2);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1); // true
            assert_eq!(*data_ptr.add(1), 0); // false
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    #[test]
    fn test_compile_vec_len_inline() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [10 20 30])
        let vec_span = Span::new(10, 20);
        let apply_span = Span::new(0, 25);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            apply_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1, 8),
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 10, span: Span::new(11, 13) },
                    Expr::IntLit { value: 20, span: Span::new(14, 16) },
                    Expr::IntLit { value: 30, span: Span::new(17, 19) },
                ],
                span: vec_span,
            }],
            span: apply_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-len should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_compile_vec_get_inline() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-get v 1))
        let vec_span = Span::new(8, 18);
        let get_span = Span::new(21, 35);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(9, 11) },
                        Expr::IntLit { value: 20, span: Span::new(12, 14) },
                        Expr::IntLit { value: 30, span: Span::new(15, 17) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(22, 29),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(30, 31),
                    },
                    Expr::IntLit { value: 1, span: Span::new(32, 33) },
                ],
                span: get_span,
            }),
            span: Span::new(0, 36),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get should compile: {result:?}");
        assert_eq!(result.unwrap(), 20);
    }

    #[test]
    fn test_compile_vec_get_first_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(100, 110);
        let get_span = Span::new(120, 135);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(101, 104) },
                        Expr::IntLit { value: 200, span: Span::new(105, 108) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(121, 128),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(129, 130),
                    },
                    Expr::IntLit { value: 0, span: Span::new(131, 132) },
                ],
                span: get_span,
            }),
            span: Span::new(99, 136),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get index 0 should work: {result:?}");
        assert_eq!(result.unwrap(), 100);
    }

    #[test]
    fn test_compile_vec_get_last_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(200, 210);
        let get_span = Span::new(220, 235);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(201, 202) },
                        Expr::IntLit { value: 2, span: Span::new(203, 204) },
                        Expr::IntLit { value: 3, span: Span::new(205, 206) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(221, 228),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(229, 230),
                    },
                    Expr::IntLit { value: 2, span: Span::new(231, 232) },
                ],
                span: get_span,
            }),
            span: Span::new(199, 236),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get last index should work: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_compile_vec_set_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-len (vec-set v 1 99)))
        // Since v is used twice (vec-set and vec-len), vec-set takes the copy path.
        let vec_span = Span::new(300, 310);
        let set_span = Span::new(320, 340);
        let len_span = Span::new(315, 345);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(301, 303) },
                        Expr::IntLit { value: 20, span: Span::new(304, 306) },
                        Expr::IntLit { value: 30, span: Span::new(307, 309) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(316, 323),
                }),
                args: vec![Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("vec-set"),
                        span: Span::new(321, 328),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("v"),
                            span: Span::new(329, 330),
                        },
                        Expr::IntLit { value: 1, span: Span::new(331, 332) },
                        Expr::IntLit { value: 99, span: Span::new(333, 335) },
                    ],
                    span: set_span,
                }],
                span: len_span,
            }),
            span: Span::new(299, 346),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-set should compile: {result:?}");
        // vec-set returns a new Vec with same length.
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_compile_vec_push_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [10 20] 30))
        let vec_span = Span::new(400, 410);
        let push_span = Span::new(415, 435);
        let len_span = Span::new(410, 440);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(411, 418),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(416, 424),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(401, 403) },
                            Expr::IntLit { value: 20, span: Span::new(404, 406) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 30, span: Span::new(425, 427) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-push should compile: {result:?}");
        // [10 20] pushed 30 -> len 3
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_compile_vec_literal_in_let() {
        // (let [v [1 2 3]] (vec-len v))
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(500, 510);
        let len_span = Span::new(515, 530);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(501, 502) },
                        Expr::IntLit { value: 2, span: Span::new(503, 504) },
                        Expr::IntLit { value: 3, span: Span::new(505, 506) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(516, 523),
                }),
                args: vec![Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(524, 525),
                }],
                span: len_span,
            }),
            span: Span::new(499, 531),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec in let should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_compile_vec_literal_with_computed_elements() {
        use cranelisp_types::ResolvedCall;

        // [1 (+ 2 3) 10]
        let add_span = Span::new(603, 610);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: Span::new(601, 602) },
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: Span::new(604, 605),
                    }),
                    args: vec![
                        Expr::IntLit { value: 2, span: Span::new(606, 607) },
                        Expr::IntLit { value: 3, span: Span::new(608, 609) },
                    ],
                    span: add_span,
                },
                Expr::IntLit { value: 10, span: Span::new(611, 613) },
            ],
            span: Span::new(600, 614),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec with computed elements should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1);
            assert_eq!(*data_ptr.add(1), 5); // 2 + 3
            assert_eq!(*data_ptr.add(2), 10);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    #[test]
    fn test_compile_vec_in_function_defn() {
        // (defn make-vec [] [1 2 3])
        // Returns a Vec literal.
        let defn = Defn {
            name: Symbol::from("make-vec"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: Span::new(701, 702) },
                    Expr::IntLit { value: 2, span: Span::new(703, 704) },
                    Expr::IntLit { value: 3, span: Span::new(705, 706) },
                ],
                span: Span::new(700, 707),
            },
            docstring: None,
            span: Span::new(700, 710),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let compiled = compile_program(&program, &check, CompileMode::Batch).unwrap();
        let ptr = unsafe { compiled.execute().unwrap() };
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    #[test]
    fn test_compile_vec_get_verify_value() {
        use cranelisp_types::ResolvedCall;

        // (let [v [100 200 300]] (vec-get v 2))
        let vec_span = Span::new(808, 818);
        let get_span = Span::new(821, 840);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(809, 812) },
                        Expr::IntLit { value: 200, span: Span::new(813, 816) },
                        Expr::IntLit { value: 300, span: Span::new(817, 820) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(822, 829),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(830, 831),
                    },
                    Expr::IntLit { value: 2, span: Span::new(832, 833) },
                ],
                span: get_span,
            }),
            span: Span::new(807, 841),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-get value should compile: {result:?}");
        assert_eq!(result.unwrap(), 300);
    }

    #[test]
    fn test_compile_vec_push_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [1] 2))
        // vec-push on a temporary VecLit — will take COW path (temp = unique).
        let vec_span = Span::new(900, 905);
        let push_span = Span::new(910, 925);
        let len_span = Span::new(905, 930);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(906, 913),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(911, 919),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 1, span: Span::new(901, 902) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 2, span: Span::new(920, 921) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-push on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 2);
    }

    #[test]
    fn test_compile_vec_set_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-set [10 20 30] 0 99))
        let vec_span = Span::new(1000, 1010);
        let set_span = Span::new(1015, 1035);
        let len_span = Span::new(1010, 1040);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1011, 1018),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-set"),
                    span: Span::new(1016, 1023),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(1001, 1003) },
                            Expr::IntLit { value: 20, span: Span::new(1004, 1006) },
                            Expr::IntLit { value: 30, span: Span::new(1007, 1009) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 0, span: Span::new(1024, 1025) },
                    Expr::IntLit { value: 99, span: Span::new(1026, 1028) },
                ],
                span: set_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "vec-set on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_compile_vec_literal_interactive_mode() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1101, 1103) },
            ],
            span: Span::new(1100, 1104),
        };
        let check = empty_check();
        let mut got = got::ModuleCodegenState::new();

        let result = compile_and_run_expr_with_got(
            &expr, &check, CompileMode::Interactive, Some(&mut got),
        );
        assert!(result.is_ok(), "vec in interactive mode should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    #[test]
    fn test_compile_vec_empty_len() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [])
        let vec_span = Span::new(1200, 1202);
        let len_span = Span::new(1195, 1210);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1196, 1203),
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: vec_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "empty vec len should compile: {result:?}");
        assert_eq!(result.unwrap(), 0);
    }

    #[test]
    fn test_compile_vec_push_empty_vec() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [] 42))
        let vec_span = Span::new(1300, 1302);
        let push_span = Span::new(1305, 1320);
        let len_span = Span::new(1300, 1325);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1301, 1308),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(1306, 1314),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 42, span: Span::new(1315, 1317) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "push to empty vec should compile: {result:?}");
        assert_eq!(result.unwrap(), 1);
    }

    #[test]
    fn test_compile_vec_len_empty_vec() {
        use cranelisp_types::ResolvedCall;

        let len_span = Span::new(1400, 1420);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1401, 1408),
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: Span::new(1409, 1411),
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        };

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0);
    }

    #[test]
    fn test_compile_nested_vec_literals() {
        // [[1 2] [3 4]] — a Vec of Vecs (nested heap values)
        let expr = Expr::VecLit {
            elements: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(1502, 1503) },
                        Expr::IntLit { value: 2, span: Span::new(1504, 1505) },
                    ],
                    span: Span::new(1501, 1506),
                },
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 3, span: Span::new(1508, 1509) },
                        Expr::IntLit { value: 4, span: Span::new(1510, 1511) },
                    ],
                    span: Span::new(1507, 1512),
                },
            ],
            span: Span::new(1500, 1513),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "nested vec should compile: {result:?}");
        let outer_ptr = result.unwrap();
        assert!(outer_ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(outer_ptr), 2);

        // First inner vec.
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            let inner1 = *data;
            assert!(inner1 > 1024, "inner vec should be heap pointer");
            assert_eq!(cranelisp_runtime::vec_len(inner1), 2);
        }

        // Clean up (inner vecs need manual cleanup since no drop glue yet).
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            cranelisp_runtime::vec_drop(*data, 0);
            cranelisp_runtime::vec_drop(*data.add(1), 0);
        }
        cranelisp_runtime::vec_drop(outer_ptr, 0);
    }

    #[test]
    fn test_compile_vec_large_literal() {
        // [0 1 2 3 4 5 6 7 8 9] — 10 elements
        let elements: Vec<Expr> = (0..10)
            .map(|i| Expr::IntLit {
                value: i,
                span: Span::new(1600 + (i as u32) * 2, 1602 + (i as u32) * 2),
            })
            .collect();

        let expr = Expr::VecLit {
            elements,
            span: Span::new(1600, 1620),
        };
        let check = empty_check();

        let result = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None);
        assert!(result.is_ok(), "large vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 10);

        unsafe {
            let base = ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            for i in 0..10 {
                assert_eq!(*data.add(i), i as i64);
            }
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // --- Ring 2A: TraitMethod dispatch tests ---

    #[test]
    fn test_trait_method_dispatch_inline_add() {
        // (+ 3 4) resolved as TraitMethod Num.+ on Int → should inline as iadd.
        let apply_span = Span::new(100, 110);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: Span::new(101, 102),
            }),
            args: vec![
                Expr::IntLit { value: 3, span: Span::new(103, 104) },
                Expr::IntLit { value: 4, span: Span::new(105, 106) },
            ],
            span: apply_span,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::TraitName::from("Num"),
                method_name: Symbol::from("+"),
                impl_type: cranelisp_types::TypeName::from("Int"),
                mangled_name: cranelisp_types::JitSymbol::from("Num.+$Int"),
            },
        );

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None)
            .expect("TraitMethod inline add should compile");
        assert_eq!(value, 7);
    }

    #[test]
    fn test_trait_method_dispatch_eq_bool() {
        // (= true true) resolved as TraitMethod Eq.= on Bool → eq-bool.
        let apply_span = Span::new(200, 210);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("="),
                span: Span::new(201, 202),
            }),
            args: vec![
                Expr::BoolLit { value: true, span: Span::new(203, 207) },
                Expr::BoolLit { value: true, span: Span::new(208, 212) },
            ],
            span: apply_span,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::TraitName::from("Eq"),
                method_name: Symbol::from("="),
                impl_type: cranelisp_types::TypeName::from("Bool"),
                mangled_name: cranelisp_types::JitSymbol::from("Eq.=$Bool"),
            },
        );

        let value = compile_and_run_expr_with_got(&expr, &check, CompileMode::Batch, None)
            .expect("TraitMethod eq-bool should compile");
        assert_eq!(value, 1); // true == true → true (1)
    }

    #[test]
    fn test_constrained_fn_skipped_in_compile_program() {
        // A constrained fn should be skipped (not compiled).
        let defn = Defn {
            name: Symbol::from("add"),
            params: vec![Symbol::from("x"), Symbol::from("y")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 0, span: Span::new(10, 11) },
            docstring: None,
            span: Span::new(0, 20),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            params: vec![],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 42, span: Span::new(30, 32) },
            docstring: None,
            span: Span::new(25, 40),
        };

        let program: Program = vec![
            TopLevel::Defn(defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Mark "add" as constrained — should be skipped during compilation.
        check.constrained_fn_names.insert(Symbol::from("add"));

        let compiled = compile_program(&program, &check, CompileMode::Batch)
            .expect("should compile with constrained fn skipped");
        let value = unsafe { compiled.execute().unwrap() };
        assert_eq!(value, 42);
    }

    #[test]
    fn test_collect_extra_defns_empty() {
        let check = empty_check();
        let extras = collect_extra_defns(&check);
        assert!(extras.is_empty());
    }

    #[test]
    fn test_collect_extra_defns_with_defaults() {
        let mut check = empty_check();
        check.default_method_defns.push(Defn {
            name: Symbol::from("!="),
            params: vec![Symbol::from("x"), Symbol::from("y")],
            param_annotations: vec![],
            visibility: cranelisp_types::Visibility::Public,
            body: Expr::IntLit { value: 0, span: Span::new(0, 1) },
            docstring: None,
            span: Span::new(0, 10),
        });

        let extras = collect_extra_defns(&check);
        assert_eq!(extras.len(), 1);
        assert_eq!(extras[0].name, Symbol::from("!="));
    }
}
