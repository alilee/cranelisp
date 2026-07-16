//! Relocated crate-root Vec-codegen tests (FIXME 0495 step 1). Pure relocation from `src/tests.rs`; verbatim bodies, harness via `crate::test_support`.

use crate::test_support::*;


// --- Vec codegen tests ---

// spec: 04-expressions §4.10 — empty Vec literal codegen
#[test]
fn test_compile_empty_vec_literal() {
    let expr = Expr::VecLit {
        elements: vec![],
        span: Span::new(0, 2),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "empty vec literal should compile: {result:?}");
    let ptr = result.unwrap();
    // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Verify len == 0.
    assert_eq!(vec_len_for_test(ptr), 0);

    // Clean up.
    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}


// spec: 04-expressions §4.10 — Vec literal with integer elements
#[test]
fn test_compile_vec_literal_with_ints() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::IntLit { value: 10, span: Span::new(1, 3), inferred_type: None },
            Expr::IntLit { value: 20, span: Span::new(4, 6), inferred_type: None },
            Expr::IntLit { value: 30, span: Span::new(7, 9), inferred_type: None },
        ],
        span: Span::new(0, 10),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec literal should compile: {result:?}");
    let ptr = result.unwrap();
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Verify len == 3.
    assert_eq!(vec_len_for_test(ptr), 3);

    // Verify element values from data buffer.
    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(heap::HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64);
        assert_eq!(*data_ptr, 10);
        assert_eq!(*data_ptr.add(1), 20);
        assert_eq!(*data_ptr.add(2), 30);
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}


// spec: 04-expressions §4.10 — single-element Vec literal
#[test]
fn test_compile_vec_literal_single_element() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::IntLit { value: 42, span: Span::new(1, 3), inferred_type: None },
        ],
        span: Span::new(0, 4),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "single-element vec should compile: {result:?}");
    let ptr = result.unwrap();

    assert_eq!(vec_len_for_test(ptr), 1);

    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(32) as *const *const i64);
        assert_eq!(*data_ptr, 42);
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}


// spec: 04-expressions §4.10 — Vec literal with boolean elements
#[test]
fn test_compile_vec_literal_with_bool_elements() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::BoolLit { value: true, span: Span::new(1, 5), inferred_type: None },
            Expr::BoolLit { value: false, span: Span::new(6, 11), inferred_type: None },
        ],
        span: Span::new(0, 12),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "bool vec should compile: {result:?}");
    let ptr = result.unwrap();
    assert_eq!(vec_len_for_test(ptr), 2);

    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(32) as *const *const i64);
        assert_eq!(*data_ptr, 1); // true
        assert_eq!(*data_ptr.add(1), 0); // false
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}


// spec: appendix-a-builtins §A.3 — vec-len inline primitive codegen
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
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 10, span: Span::new(11, 13), inferred_type: None },
                Expr::IntLit { value: 20, span: Span::new(14, 16), inferred_type: None },
                Expr::IntLit { value: 30, span: Span::new(17, 19), inferred_type: None },
            ],
            span: vec_span,
            inferred_type: None,
        }],
        span: apply_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-len should compile: {result:?}");
    assert_eq!(result.unwrap(), 3);
}


// spec: appendix-a-builtins §A.3 — vec-get bounds-checked index codegen
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
                    Expr::IntLit { value: 10, span: Span::new(9, 11), inferred_type: None },
                    Expr::IntLit { value: 20, span: Span::new(12, 14), inferred_type: None },
                    Expr::IntLit { value: 30, span: Span::new(15, 17), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(22, 29),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(30, 31),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 1, span: Span::new(32, 33), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(0, 36),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get should compile: {result:?}");
    assert_eq!(result.unwrap(), 20);
}


// spec: appendix-a-builtins §A.3 — vec-get index 0 boundary
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
                    Expr::IntLit { value: 100, span: Span::new(101, 104), inferred_type: None },
                    Expr::IntLit { value: 200, span: Span::new(105, 108), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(121, 128),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(129, 130),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 0, span: Span::new(131, 132), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(99, 136),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get index 0 should work: {result:?}");
    assert_eq!(result.unwrap(), 100);
}


// spec: appendix-a-builtins §A.3 — vec-get last index boundary
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
                    Expr::IntLit { value: 1, span: Span::new(201, 202), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(203, 204), inferred_type: None },
                    Expr::IntLit { value: 3, span: Span::new(205, 206), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(221, 228),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(229, 230),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 2, span: Span::new(231, 232), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(199, 236),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get last index should work: {result:?}");
    assert_eq!(result.unwrap(), 3);
}


// spec: 12-runtime §12.3.3 — vec-set copy-on-write path codegen
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
                    Expr::IntLit { value: 10, span: Span::new(301, 303), inferred_type: None },
                    Expr::IntLit { value: 20, span: Span::new(304, 306), inferred_type: None },
                    Expr::IntLit { value: 30, span: Span::new(307, 309), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(316, 323),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-set"),
                    span: Span::new(321, 328),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(329, 330),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 1, span: Span::new(331, 332), inferred_type: None },
                    Expr::IntLit { value: 99, span: Span::new(333, 335), inferred_type: None },
                ],
                span: set_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(299, 346),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-set should compile: {result:?}");
    // vec-set returns a new Vec with same length.
    assert_eq!(result.unwrap(), 3);
}


// spec: 12-runtime §12.3.3 — vec-push copy-on-write path codegen
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
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-push"),
                span: Span::new(416, 424),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(401, 403), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(404, 406), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 30, span: Span::new(425, 427), inferred_type: None },
            ],
            span: push_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-push should compile: {result:?}");
    // [10 20] pushed 30 -> len 3
    assert_eq!(result.unwrap(), 3);
}


// spec: 04-expressions §4.3, §4.10 — Vec literal bound in let, accessed via vec-len
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
                    Expr::IntLit { value: 1, span: Span::new(501, 502), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(503, 504), inferred_type: None },
                    Expr::IntLit { value: 3, span: Span::new(505, 506), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(516, 523),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Var {
                name: Symbol::from("v"),
                span: Span::new(524, 525),
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(499, 531),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec in let should compile: {result:?}");
    assert_eq!(result.unwrap(), 3);
}


// spec: 04-expressions §4.10, §4.11 — Vec literal with computed elements, left-to-right eval
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
            Expr::IntLit { value: 1, span: Span::new(601, 602), inferred_type: None },
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("+"),
                    span: Span::new(604, 605),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 2, span: Span::new(606, 607), inferred_type: None },
                    Expr::IntLit { value: 3, span: Span::new(608, 609), inferred_type: None },
                ],
                span: add_span,
                resolved_call: None,
                inferred_type: None,
            },
            Expr::IntLit { value: 10, span: Span::new(611, 613), inferred_type: None },
        ],
        span: Span::new(600, 614),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec with computed elements should compile: {result:?}");
    let ptr = result.unwrap();

    assert_eq!(vec_len_for_test(ptr), 3);
    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(32) as *const *const i64);
        assert_eq!(*data_ptr, 1);
        assert_eq!(*data_ptr.add(1), 5); // 2 + 3
        assert_eq!(*data_ptr.add(2), 10);
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}


// spec: 05-definitions §5.1, 04-expressions §4.10 — Vec literal as function return value
#[test]
fn test_compile_vec_in_function_defn() {
    // (defn make-vec [] [1 2 3])
    // Returns a Vec literal.
    let defn = Defn {
        name: Symbol::from("make-vec"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::VecLit {
            elements: vec![
            Expr::IntLit { value: 1, span: Span::new(701, 702), inferred_type: None },
            Expr::IntLit { value: 2, span: Span::new(703, 704), inferred_type: None },
            Expr::IntLit { value: 3, span: Span::new(705, 706), inferred_type: None },
            ],
            span: Span::new(700, 707),
            inferred_type: None,
            },
            span: Span::new(700, 710),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(700, 710),
    };

    let program: Program = vec![TopLevel::Defn(defn)];
    let check = empty_check();

    let ptr = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");
    assert_eq!(vec_len_for_test(ptr), 3);

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}


// spec: appendix-a-builtins §A.3 — vec-get returns correct element value
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
                    Expr::IntLit { value: 100, span: Span::new(809, 812), inferred_type: None },
                    Expr::IntLit { value: 200, span: Span::new(813, 816), inferred_type: None },
                    Expr::IntLit { value: 300, span: Span::new(817, 820), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(822, 829),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(830, 831),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 2, span: Span::new(832, 833), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(807, 841),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get value should compile: {result:?}");
    assert_eq!(result.unwrap(), 300);
}


// spec: 12-runtime §12.3.3 — vec-push on temporary Vec (COW in-place path)
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
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-push"),
                span: Span::new(911, 919),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(901, 902), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 2, span: Span::new(920, 921), inferred_type: None },
            ],
            span: push_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-push on temp should compile: {result:?}");
    assert_eq!(result.unwrap(), 2);
}


// spec: 12-runtime §12.3.3 — vec-set on temporary Vec (COW in-place path)
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
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-set"),
                span: Span::new(1016, 1023),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(1001, 1003), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(1004, 1006), inferred_type: None },
                        Expr::IntLit { value: 30, span: Span::new(1007, 1009), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 0, span: Span::new(1024, 1025), inferred_type: None },
                Expr::IntLit { value: 99, span: Span::new(1026, 1028), inferred_type: None },
            ],
            span: set_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-set on temp should compile: {result:?}");
    assert_eq!(result.unwrap(), 3);
}


// ===== FIXME 0134 harvest (backend slice): Vec-COW value-correctness +
// RC-balance kernels of the quarantined `tests/legacy/{ring1,ring2,e2e}.rs`
// GAPs. The existing `test_compile_vec_set_{copy_path,on_temp}` tests prove
// vec-set COMPILES and RUNS but assert only the result LENGTH (=3). The
// disposition (`s82-harvest-conformance_bulk.md` flag 1: backend =
// `assert_rc_balanced` + Vec-COW edge cases) names the uncovered angles:
// (a) the COPY path leaves the ORIGINAL vec untouched
//     (legacy `vec_set_cow_preserves_original`);
// (b) a set preserves OTHER positions' values
//     (legacy `vec_set_preserves_other_elements`);
// (c) RC balance — a vec lifecycle returns live bytes to baseline
//     (legacy `assert_rc_balanced`).
// These run at the backend unit layer via `test_compile_and_run` (full
// codegen + JIT execute), reading element VALUES via vec-get — the durable
// value-level guards the length-only tests lack. =====

/// Build `(vec-get <vec_expr> idx)` against a fresh span. Helper for the
/// COW value-correctness guards below.
fn vec_get(
    vec_expr: Expr,
    idx: i64,
    get_span: Span,
    resolutions: &mut HashMap<Span, cranelisp_types::ResolvedCall>,
) -> Expr {
    resolutions.insert(
        get_span,
        cranelisp_types::ResolvedCall::BuiltinFn { name: Symbol::from("vec-get") },
    );
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-get"),
            span: Span::new(get_span.start + 1, get_span.end - 1),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            vec_expr,
            Expr::IntLit { value: idx, span: Span::new(get_span.end - 1, get_span.end), inferred_type: None },
        ],
        span: get_span,
        resolved_call: None,
        inferred_type: None,
    }
}


fn vec_lit(elems: &[i64], base: u32) -> Expr {
    Expr::VecLit {
        elements: elems
            .iter()
            .enumerate()
            .map(|(i, &v)| {
                let i = i as u32;
                Expr::IntLit {
                    value: v,
                    span: Span::new(base + i * 3 + 1, base + i * 3 + 3),
                    inferred_type: None,
                }
            })
            .collect(),
        span: Span::new(base, base + elems.len() as u32 * 3 + 1),
        inferred_type: None,
    }
}


// spec: spec/12-runtime.md §12.3.3 — vec-set on a NON-last-use vec takes
//       the COPY path; the ORIGINAL vec is untouched. Backend kernel of the
//       legacy `vec_set_cow_preserves_original` reg-guard. The original `v`
//       is read AFTER the set (so the set is NOT at last use → copy path),
//       and its index-1 value must still be the original 20, not 99.
#[test]
fn vec_set_copy_path_preserves_original() {
    use cranelisp_types::ResolvedCall;
    let mut res = HashMap::new();
    let set_span = Span::new(2010, 2030);
    res.insert(set_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-set") });

    // (let [v [10 20 30]]
    //   (let [_ (vec-set v 1 99)]   ; copy path: v not at last use
    //     (vec-get v 1)))            ; original v's index 1 still = 20
    let set_expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-set"),
            span: Span::new(2011, 2018),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::Var { name: Symbol::from("v"), span: Span::new(2019, 2020), resolved_call: None, inferred_type: None },
            Expr::IntLit { value: 1, span: Span::new(2021, 2022), inferred_type: None },
            Expr::IntLit { value: 99, span: Span::new(2023, 2025), inferred_type: None },
        ],
        span: set_span,
        resolved_call: None,
        inferred_type: None,
    };
    let read_original = vec_get(
        Expr::Var { name: Symbol::from("v"), span: Span::new(2040, 2041), resolved_call: None, inferred_type: None },
        1,
        Span::new(2042, 2060),
        &mut res,
    );
    let expr = Expr::Let {
        bindings: vec![(Symbol::from("v"), vec_lit(&[10, 20, 30], 2001))],
        body: Box::new(Expr::Let {
            bindings: vec![(Symbol::from("_unused"), set_expr)],
            body: Box::new(read_original),
            span: Span::new(2005, 2061),
            inferred_type: None,
        }),
        span: Span::new(2000, 2062),
        inferred_type: None,
    };
    let check = TestCheckResult {
        method_resolutions: res,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    };
    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert_eq!(
        result.expect("vec-set copy-path program compiles+runs"),
        20,
        "vec-set on a non-last-use vec MUST copy — the original vec's \
         index-1 value must remain 20 (COW preserves the original)"
    );
}


// spec: spec/12-runtime.md §12.3.3 — a vec-set preserves the values at
//       OTHER positions. Backend kernel of the legacy
//       `vec_set_preserves_other_elements` GAP (distinct from the
//       length-only `test_compile_vec_set_*`). Read index 2 of the SET
//       result — it must still be the original 30 (only index 0 changed).
#[test]
fn vec_set_preserves_other_elements() {
    use cranelisp_types::ResolvedCall;
    let mut res = HashMap::new();
    let set_span = Span::new(2110, 2130);
    res.insert(set_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-set") });

    // (vec-get (vec-set [10 20 30] 0 99) 2)  →  30 (index 2 untouched)
    let set_expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-set"),
            span: Span::new(2111, 2118),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            vec_lit(&[10, 20, 30], 2101),
            Expr::IntLit { value: 0, span: Span::new(2121, 2122), inferred_type: None },
            Expr::IntLit { value: 99, span: Span::new(2123, 2125), inferred_type: None },
        ],
        span: set_span,
        resolved_call: None,
        inferred_type: None,
    };
    let expr = vec_get(set_expr, 2, Span::new(2140, 2160), &mut res);
    let check = TestCheckResult {
        method_resolutions: res,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    };
    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert_eq!(
        result.expect("vec-set preserves-other program compiles+runs"),
        30,
        "vec-set at index 0 MUST leave index 2 holding the original 30"
    );
}


// spec: spec/12-runtime.md §12.3 — RC balance: a complete Vec lifecycle
//       (allocate literal, set, drop) returns live bytes to baseline — no
//       leak, no double-free. Backend kernel of the legacy
//       `assert_rc_balanced` discipline, lifted to the unit layer via the
//       `cranelisp_intrinsics::{alloc_count,dealloc_count}` counters (the
//       same atomics `/mem` reports). RC-counter tests are process-global,
//       so this reads a delta, not an absolute. NOTE: nextest runs each
//       test in its own process, so the counter is uncontended here.
#[test]
fn vec_lifecycle_is_rc_balanced() {
    use cranelisp_types::ResolvedCall;
    let allocs_before = cranelisp_intrinsics::alloc_count();
    let deallocs_before = cranelisp_intrinsics::dealloc_count();

    // (vec-len (vec-set [10 20 30] 0 99))  — temp vec → COW path; the
    // whole temporary lifecycle (literal alloc, COW copy if any, drop)
    // must balance. We read length so the result is a scalar.
    let mut res = HashMap::new();
    let set_span = Span::new(2210, 2230);
    let len_span = Span::new(2240, 2260);
    res.insert(set_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-set") });
    res.insert(len_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-len") });
    let set_expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-set"),
            span: Span::new(2211, 2218),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            vec_lit(&[10, 20, 30], 2201),
            Expr::IntLit { value: 0, span: Span::new(2221, 2222), inferred_type: None },
            Expr::IntLit { value: 99, span: Span::new(2223, 2225), inferred_type: None },
        ],
        span: set_span,
        resolved_call: None,
        inferred_type: None,
    };
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(2241, 2248),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![set_expr],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };
    let check = TestCheckResult {
        method_resolutions: res,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    };
    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert_eq!(result.expect("rc-balance program runs"), 3);

    let allocs = cranelisp_intrinsics::alloc_count() - allocs_before;
    let deallocs = cranelisp_intrinsics::dealloc_count() - deallocs_before;
    assert_eq!(
        allocs, deallocs,
        "Vec lifecycle must be RC-balanced: {allocs} allocs vs {deallocs} \
         deallocs across the temp-vec set+len+drop. An imbalance means a \
         leak (allocs>deallocs) or a double-free (deallocs>allocs) in the \
         vec-set COW codegen."
    );
}


// spec: 04-expressions §4.10 — Vec literal in interactive (REPL) mode
#[test]
fn test_compile_vec_literal_interactive_mode() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::IntLit { value: 42, span: Span::new(1101, 1103), inferred_type: None },
        ],
        span: Span::new(1100, 1104),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(
        &expr, &check, &empty_tables(),
    );
    assert!(result.is_ok(), "vec in interactive mode should compile: {result:?}");
    let ptr = result.unwrap();
    assert!(ptr > 1024);
    assert_eq!(vec_len_for_test(ptr), 1);

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}


// spec: appendix-a-builtins §A.3 — vec-len on empty Vec returns 0
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
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::VecLit {
            elements: vec![],
            span: vec_span,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "empty vec len should compile: {result:?}");
    assert_eq!(result.unwrap(), 0);
}


// spec: appendix-a-builtins §A.3 — vec-push on empty Vec
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
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-push"),
                span: Span::new(1306, 1314),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 42, span: Span::new(1315, 1317), inferred_type: None },
            ],
            span: push_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "push to empty vec should compile: {result:?}");
    assert_eq!(result.unwrap(), 1);
}


// spec: appendix-a-builtins §A.3 — vec-len on empty Vec (duplicate boundary check)
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
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::VecLit {
            elements: vec![],
            span: Span::new(1409, 1411),
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        resolved_targets: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 0);
}


// spec: 04-expressions §4.10 — nested Vec literals (Vec of Vecs)
#[test]
fn test_compile_nested_vec_literals() {
    // [[1 2] [3 4]] — a Vec of Vecs (nested heap values)
    let expr = Expr::VecLit {
        elements: vec![
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: Span::new(1502, 1503), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(1504, 1505), inferred_type: None },
                ],
                span: Span::new(1501, 1506),
                inferred_type: None,
            },
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 3, span: Span::new(1508, 1509), inferred_type: None },
                    Expr::IntLit { value: 4, span: Span::new(1510, 1511), inferred_type: None },
                ],
                span: Span::new(1507, 1512),
                inferred_type: None,
            },
        ],
        span: Span::new(1500, 1513),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "nested vec should compile: {result:?}");
    let outer_ptr = result.unwrap();
    assert!(outer_ptr > 1024);
    assert_eq!(vec_len_for_test(outer_ptr), 2);

    // First inner vec.
    unsafe {
        let base = outer_ptr as *const u8;
        let data = *(base.add(32) as *const *const i64);
        let inner1 = *data;
        assert!(inner1 > 1024, "inner vec should be heap pointer");
        assert_eq!(vec_len_for_test(inner1), 2);
    }

    // Clean up (inner vecs need manual cleanup since no drop glue yet).
    unsafe {
        let base = outer_ptr as *const u8;
        let data = *(base.add(32) as *const *const i64);
        cranelisp_intrinsics::vec_runtime::vec_drop(*data, 0);
        cranelisp_intrinsics::vec_runtime::vec_drop(*data.add(1), 0);
    }
    cranelisp_intrinsics::vec_runtime::vec_drop(outer_ptr, 0);
}


// spec: 04-expressions §4.10 — large Vec literal (10 elements)
#[test]
fn test_compile_vec_large_literal() {
    // [0 1 2 3 4 5 6 7 8 9] — 10 elements
    let elements: Vec<Expr> = (0..10)
        .map(|i| Expr::IntLit {
            value: i,
            span: Span::new(1600 + (i as u32) * 2, 1602 + (i as u32) * 2),
            inferred_type: None,
        })
        .collect();

    let expr = Expr::VecLit {
        elements,
        span: Span::new(1600, 1620),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "large vec should compile: {result:?}");
    let ptr = result.unwrap();
    assert_eq!(vec_len_for_test(ptr), 10);

    unsafe {
        let base = ptr as *const u8;
        let data = *(base.add(32) as *const *const i64);
        for i in 0..10 {
            assert_eq!(*data.add(i), i as i64);
        }
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}
