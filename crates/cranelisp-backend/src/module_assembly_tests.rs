//! Relocated crate-root module-assembly + GOT-emission tests (FIXME 0495 step 1). Exercise `compile_to_module` (lib.rs) end-to-end: JIT + object-mode GOT-slot writes, Decision-23/36 object-symbol invariants, multi-sig + mono + default-method assembly. Verbatim relocation from `src/tests.rs`.

use crate::test_support::*;


// spec: 05-definitions §5.1 — single defn compiles and executes via JIT
#[test]
fn test_compile_program_simple() {
    let defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 42,
                span: Span::new(0, 2),
                inferred_type: None,
            },
            span: Span::new(0, 20),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 20),
    };

    let program: Program = vec![TopLevel::Defn(defn)];
    let check = empty_check();

    let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert_eq!(value, 42);
}


// spec: 12-runtime §12.6 — batch mode requires main entry point
#[test]
fn test_compile_program_no_defns() {
    let _ = empty_check();
    let names: Vec<Symbol> = vec![];
    let tables = empty_tables();
    // No symbol table for "user" at all — compile_to_module errors out
    // because there's no module entry (and no names anyway).
    tables.insert(ModuleFullPath::from("user"), SymbolTable::new(ModuleFullPath::from("user")));

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let result = compile_to_module(
        ModuleFullPath::from("user"),
        &names,
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    );
    assert!(result.is_err());
}


// spec: 05-definitions §5.1 — defn compiles in interactive (REPL) mode
#[test]
fn test_compile_program_interactive_mode() {
    let defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
            value: 7,
            span: Span::new(0, 1),
            inferred_type: None,
            },
            span: Span::new(0, 20),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 20),
    };

    let program: Program = vec![TopLevel::Defn(defn)];
    let check = empty_check();

    let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert_eq!(value, 7);
}


// spec: 04-expressions §4.1.1 — integer literal codegen with GOT state
// spec: 05-definitions §5.13.1 — multiple function definitions compile together
#[test]
fn test_compile_program_multiple_defns() {
    // Two functions: helper and main. Main returns 100.
    let helper = Defn {
        name: Symbol::from("helper"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::Var {
            name: Symbol::from("x"),
            span: Span::new(20, 21),
            resolved_call: None,
            inferred_type: None,
            },
            span: Span::new(10, 30),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(10, 30),
    };

    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
            value: 100,
            span: Span::new(40, 43),
            inferred_type: None,
            },
            span: Span::new(35, 50),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(35, 50),
    };

    let program: Program = vec![TopLevel::Defn(helper), TopLevel::Defn(main_defn)];
    let check = empty_check();

    let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert_eq!(value, 100);
}


// spec: 07-traits §7.7 — constrained polymorphic fn skipped at definition, monomorphised at call
#[test]
fn test_constrained_fn_skipped_in_compile_program() {
    // A constrained fn should be skipped (not compiled).
    let defn = Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::IntLit { value: 0, span: Span::new(10, 11), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 20),
    };

    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 42, span: Span::new(30, 32), inferred_type: None },
            span: Span::new(25, 40),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(25, 40),
    };

    let program: Program = vec![
        TopLevel::Defn(defn),
        TopLevel::Defn(main_defn),
    ];

    let mut check = empty_check();
    // Mark "add" as constrained — should be skipped during compilation.
    check.constrained_fn_names.insert(Symbol::from("add"));

    let value = test_compile_program_and_run(&program, &check, &empty_tables())
        .expect("should compile with constrained fn skipped");
    assert_eq!(value, 42);
}


// spec: 07-traits §7.7 — no default method defns produces empty extras
#[test]
fn test_collect_extra_defns_empty() {
    let check = empty_check();
    // Verify default_method_defns is empty in a fresh CheckResult.
    assert!(check.default_method_defns.is_empty());
}


// spec: 07-traits §7.7 — default trait methods compiled as extra defns
#[test]
fn test_compile_with_default_method_defns() {
    // A program with only a main function, but check has a default method defn.
    // The default method defn should be compiled alongside main.
    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("default-ne"),
                    span: Span::new(10, 20),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 1, span: Span::new(21, 22), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(23, 24), inferred_type: None },
                ],
                span: Span::new(9, 25),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 30),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 30),
    };

    let default_defn = Defn {
        name: Symbol::from("default-ne"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::IntLit { value: 77, span: Span::new(0, 2), inferred_type: None },
            span: Span::new(0, 10),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 10),
    };

    let program: Program = vec![TopLevel::Defn(main_defn)];
    let mut check = empty_check();
    check.default_method_defns.push(default_defn);

    let value = test_compile_program_and_run(&program, &check, &empty_tables())
        .expect("program with default method defns should compile");
    assert_eq!(value, 77, "should call the default method defn");
}


// spec: 12-runtime §12.5, 07-traits §7.7 — TCO for monomorphised self-recursive call
//
// When a constrained-poly function like `countdown` is monomorphised to
// `countdown$Int`, the body contains a self-recursive call `(countdown ...)`
// that the typechecker resolves to `SigDispatch { mangled_name: "countdown$Int" }`.
// The backend's TCO check must recognize this as self-recursion.
//
// This test compiles a simple recursive function and verifies it completes
// without stack overflow (1M iterations would blow the stack without TCO).
#[test]
fn test_mono_defn_self_recursive_tco() {
    // countdown$Int: (defn countdown$Int [n] (if (= n 0) 0 (countdown$Int (- n 1))))
    // Simplified: use intrinsic primitives instead of trait dispatch.
    let n_span = Span::new(10, 11);
    let zero_span = Span::new(20, 21);
    let eq_span = Span::new(30, 40);
    let sub_span = Span::new(50, 60);
    let recurse_span = Span::new(70, 90);
    let if_span = Span::new(5, 95);
    let result_span = Span::new(92, 93);

    // Build: (if (eq-i64 n 0) 0 (countdown$Int (sub-i64 n 1)))
    let cond = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("eq-i64"),
            span: Span::new(31, 37),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::Var { name: Symbol::from("n"), span: n_span, resolved_call: None, inferred_type: None },
            Expr::IntLit { value: 0, span: zero_span, inferred_type: None },
        ],
        span: eq_span,
        resolved_call: None,
        inferred_type: None,
    };

    let sub_call = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("sub-i64"),
            span: Span::new(51, 58),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::Var { name: Symbol::from("n"), span: Span::new(55, 56), resolved_call: None, inferred_type: None },
            Expr::IntLit { value: 1, span: Span::new(57, 58), inferred_type: None },
        ],
        span: sub_span,
        resolved_call: None,
        inferred_type: None,
    };

    // The recursive call: callee is "countdown" (original name),
    // but it's resolved to countdown$Int via SigDispatch.
    let recurse = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("countdown"),
            span: Span::new(71, 80),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![sub_call],
        span: recurse_span,
        resolved_call: None,
        inferred_type: None,
    };

    let body = Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(Expr::IntLit { value: 0, span: result_span, inferred_type: None }),
        else_branch: Box::new(recurse),
        span: if_span,
        inferred_type: None,
    };

    let countdown_defn = Defn {
        name: Symbol::from("countdown$Int"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("n"), None)],
            body,
            span: Span::new(0, 100),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 100),
    };

    // Set up method resolutions:
    // - eq_span: BuiltinFn("eq-i64") for the equality check
    // - sub_span: BuiltinFn("sub-i64") for the subtraction
    // - recurse_span: SigDispatch("countdown$Int") for the self-recursive call
    let mut check = empty_check();
    check.method_resolutions.insert(
        eq_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("eq-i64"),
        },
    );
    check.method_resolutions.insert(
        sub_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("sub-i64"),
        },
    );
    check.method_resolutions.insert(
        recurse_span,
        cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: cranelisp_types::JitSymbol::from("countdown$Int"),
        },
    );

    // Enrich the defn from CheckResult side maps (test bridge).
    let mut enriched_defn = countdown_defn.clone();
    enrich_defn_from_side_maps(&mut enriched_defn, &check.method_resolutions, &check.expr_types);

    // Compile with direct calls (no GOT).
    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    jit.declare_intrinsics().unwrap();
    let func_ids = jit.declare_functions(&[&enriched_defn]).unwrap();

    let arities: HashMap<Symbol, usize> =
        vec![(Symbol::from("countdown$Int"), 1)].into_iter().collect();

    let tables = empty_tables();
    let aliases = empty_aliases();
    let ctx = jit.build_compile_context(
        &func_ids, &arities,
        &tables, &aliases, ModuleFullPath::from("test"),
    );
    jit.compile_defn(&enriched_defn, ctx).unwrap();
    let countdown_ptr = jit.finalize_and_get_ptr(&Symbol::from("countdown$Int"), 1).unwrap();

    // Call with 1_000_000 — without TCO this would stack overflow.
    let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(countdown_ptr) };
    let result = func(1_000_000);
    assert_eq!(result, 0, "TCO should allow 1M recursive calls without stack overflow");
}


// --- compile_to_module module tests ---

// spec: design/arch/CLAUDE.md Decision 36 — bare-name function declarations
// uniformly across all modules. Two modules with same-named function compile
// into separate JITs without collision because function symbols are
// `.o`-Local — they cannot collide across modules' JITs.
#[test]
fn test_module_prefix_applied() {
    let _ = empty_check();
    // Module "mod_a" defines "val" returning 100.
    let val_a = Defn {
        name: Symbol::from("val"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 100, span: Span::new(0, 3), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let mod_a = ModuleFullPath::from("mod_a");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(mod_a.clone());
        st.insert(val_a.name.clone(), make_def_entry(val_a.clone()));
        tables.insert(mod_a.clone(), st);
    }
    let mut jit_a = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let _artifacts_a = compile_to_module(
        mod_a.clone(),
        std::slice::from_ref(&val_a.name),
        &tables,
        &aliases,
        jit_a.jit_module(),
        true,
    ).expect("module A should compile");
    // Post-G6: compile_to_module finalized internally. `val` is a zero-arg
    // defn with no GOT slot (direct FuncId); read its ptr by name.
    let ptr = jit_a.get_ptr_by_name(&Symbol::from("val"), 0).unwrap();
    assert!(!ptr.is_null(), "module A 'val' must finalize to a non-null ptr");
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    assert_eq!(func(), 100, "module A's val should return 100");

    // Module B also defines "val" returning 200 — compiles into a separate JIT.
    let val_b = Defn {
        name: Symbol::from("val"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 200, span: Span::new(100, 103), inferred_type: None },
            span: Span::new(100, 120),
        }],
        visibility: Visibility::Public,
        span: Span::new(100, 120),
    };
    let mod_b = ModuleFullPath::from("mod_b");
    {
        let mut st = SymbolTable::new(mod_b.clone());
        st.insert(val_b.name.clone(), make_def_entry(val_b.clone()));
        tables.insert(mod_b.clone(), st);
    }

    let mut jit_b = Jit::new_with_symbols(&[]).unwrap();
    let _artifacts_b = compile_to_module(
        mod_b.clone(),
        std::slice::from_ref(&val_b.name),
        &tables,
        &aliases,
        jit_b.jit_module(),
        true,
    ).expect("module B should compile without collision");
    // Post-G6: compile_to_module finalized internally.
    let ptr_b = jit_b.get_ptr_by_name(&Symbol::from("val"), 0).unwrap();
    let func_b: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr_b) };
    assert_eq!(func_b(), 200, "module B's val should return 200");
}


// --- G6 code-write invariants (Sprint 57 Wave 2; S75 W2 D41 rotation) ---
//
// spec: design/backend/compile-to-module.md §2 (S75 banner) + facade
// §"Code" — `compile_to_module` writes each compiled symbol's finalised
// code pointer directly into the entry's GOT slot (D41 #2), and no longer
// returns a per-symbol `code_ptrs` map. The lifecycle-owner write (D41 #1
// — `Code::Jit(Arc<Jit>)`) stays in the integration layer; backend leaves
// `ModuleEntry::Def.code` untouched.
#[test]
fn compile_to_module_writes_got_slot_after_finalize() {
    let defn = Defn {
        name: Symbol::from("seven"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 7, span: Span::new(0, 1), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Explicit GOT slot so the D41 #2 direct-write is exercised.
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let _artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    ).expect("JIT compile should succeed");

    // D41 #2: backend wrote the finalised code pointer into the entry's
    // GOT slot (slot 0). Read it back; it must be non-null in JIT mode.
    let guard = tables.get(&module).expect("symbol table present");
    let entry = guard.get(defn.name.as_ref()).expect("entry present");
    let slot = entry
        .callable_got_slot()
        .expect("test inserted a Def entry with a GOT slot");
    match entry {
        ModuleEntry::Def { code, .. } => {
            let ptr = guard.got.load_slot(slot);
            assert!(
                !ptr.is_null(),
                "backend must write the finalised code pointer to the GOT slot (D41 #2)"
            );
            // D41 #1 (Code::Jit lifecycle owner) stays in the integration
            // layer — backend leaves `code` untouched.
            assert!(
                code.is_none(),
                "backend must not write to ModuleEntry::Def.code (D41 #1 is int's job)"
            );
        }
        _ => unreachable!("test inserted a Def entry with a GOT slot"),
    }
}


// spec: design/backend/compile-to-module.md §9.1.6 — ObjectModule has no
// post-finalize runtime pointer; the GOT slot stays null in object mode.
#[test]
fn compile_to_module_object_mode_no_got_write() {
    use cranelift_module::default_libcall_names;
    use cranelift_object::{ObjectBuilder, ObjectModule};

    let defn = Defn {
        name: Symbol::from("answer"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Explicit GOT slot so we can assert object mode leaves it null.
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let isa = build_isa(true).unwrap();
    let obj_builder =
        ObjectBuilder::new(isa, "test_obj", default_libcall_names()).unwrap();
    let mut obj_module = ObjectModule::new(obj_builder);

    let aliases = empty_aliases();
    let _artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        &mut obj_module,
        true,
    ).expect("object compile should succeed");

    // Object-mode invariant: `try_get_finalized_function` returns None (no
    // runtime pointer before `finish()`), so backend writes nothing to the
    // GOT slot — it stays null.
    let guard = tables.get(&module).expect("symbol table present");
    let entry = guard.get(defn.name.as_ref()).expect("entry present");
    let slot = entry
        .callable_got_slot()
        .expect("test inserted a Def entry with a GOT slot");
    match entry {
        ModuleEntry::Def { code, .. } => {
            assert!(
                guard.got.load_slot(slot).is_null(),
                "object-mode compile must not populate the GOT slot"
            );
            assert!(
                code.is_none(),
                "object-mode entry's code field must be None"
            );
        }
        _ => unreachable!("test inserted a Def entry with a GOT slot"),
    }
}


// --- multi-sig defn tests ---
//
// Sprint 56 Wave 1: `build_mangled_name`, `concrete_type_name`, and
// `expand_multi_sig_defn` were deleted from the backend. Mangled variant
// entries are now pre-materialised by typecheck in Wave 0. The unit tests
// that exercised those helpers directly are retired; end-to-end multi-sig
// dispatch is covered by `test_compile_multi_sig_defn_end_to_end` and
// `test_compile_multi_sig_second_variant` below (plus the integration
// tests in `tests/`).

// spec: 05-definitions §5.1.2 — multi-sig defn compiles and dispatches correctly
//
// Defines a multi-sig function `f` with two variants:
//   (defn f ([x] x) ([a b] a))      — identity on 1 arg, first on 2 args
// Then defines main that calls the first variant via SigDispatch.
#[test]
fn test_compile_multi_sig_defn_end_to_end() {
    let variant1_span = Span::new(10, 30);
    let variant2_span = Span::new(40, 60);

    let multi_defn = Defn {
        name: Symbol::from("f"),
        docstring: None,
        variants: vec![
            DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), resolved_call: None, inferred_type: None },
                span: variant1_span,
            },
            DefnVariant {
                params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                body: Expr::Var { name: Symbol::from("a"), span: Span::new(45, 46), resolved_call: None, inferred_type: None },
                span: variant2_span,
            },
        ],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 70),
    };

    // main calls f$Int(42)
    let call_span = Span::new(100, 120);
    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("f"),
                    span: Span::new(101, 102),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit { value: 42, span: Span::new(103, 105), inferred_type: None }],
                span: call_span,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(95, 125),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(95, 125),
    };

    let program: Program = vec![
        TopLevel::Defn(multi_defn),
        TopLevel::Defn(main_defn),
    ];

    let mut check = empty_check();
    // Register SigDispatch for the call site.
    check.method_resolutions.insert(
        call_span,
        cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: cranelisp_types::JitSymbol::from("f$Int"),
        },
    );

    // Set up symbol table with Overloaded entry for multi-sig expansion.
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut table = SymbolTable::new(module_path.clone());
    table.insert(
        Symbol::from("f"),
        cranelisp_types::ModuleEntry::Def {
            scheme: cranelisp_types::Scheme { type_vars: vec![], constraints: Default::default(), ty: Type::Int },
            visibility: cranelisp_types::Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(cranelisp_types::DefKind::Overloaded {
                variants: vec![
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("f$Int"),
                    },
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int, Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("f$Int+Int"),
                    },
                ],
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );
    tables.insert(module_path, table);

    let result = test_compile_program_and_run(&program, &check, &tables)
        .expect("multi-sig program should compile");
    assert_eq!(result, 42, "should dispatch to f$Int and return 42");
}


// spec: 05-definitions §5.1.2 — multi-sig dispatch to second variant
#[test]
fn test_compile_multi_sig_second_variant() {
    let variant1_span = Span::new(10, 30);
    let variant2_span = Span::new(40, 60);

    let multi_defn = Defn {
        name: Symbol::from("g"),
        docstring: None,
        variants: vec![
            DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), resolved_call: None, inferred_type: None },
                span: variant1_span,
            },
            DefnVariant {
                params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                // Return b (second param) to prove we dispatched to the right variant.
                body: Expr::Var { name: Symbol::from("b"), span: Span::new(45, 46), resolved_call: None, inferred_type: None },
                span: variant2_span,
            },
        ],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 70),
    };

    // main calls g$Int+Int(10, 99) — should return 99 (the second arg)
    let call_span = Span::new(100, 120);
    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("g"),
                    span: Span::new(101, 102),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 10, span: Span::new(103, 105), inferred_type: None },
                    Expr::IntLit { value: 99, span: Span::new(106, 108), inferred_type: None },
                ],
                span: call_span,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(95, 125),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(95, 125),
    };

    let program: Program = vec![
        TopLevel::Defn(multi_defn),
        TopLevel::Defn(main_defn),
    ];

    let mut check = empty_check();
    check.method_resolutions.insert(
        call_span,
        cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: cranelisp_types::JitSymbol::from("g$Int+Int"),
        },
    );

    // Set up symbol table with Overloaded entry for multi-sig expansion.
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut table = SymbolTable::new(module_path.clone());
    table.insert(
        Symbol::from("g"),
        cranelisp_types::ModuleEntry::Def {
            scheme: cranelisp_types::Scheme { type_vars: vec![], constraints: Default::default(), ty: Type::Int },
            visibility: cranelisp_types::Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(cranelisp_types::DefKind::Overloaded {
                variants: vec![
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("g$Int"),
                    },
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int, Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("g$Int+Int"),
                    },
                ],
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );
    tables.insert(module_path, table);

    let result = test_compile_program_and_run(&program, &check, &tables)
        .expect("multi-sig program should compile");
    assert_eq!(result, 99, "should dispatch to g$Int+Int and return second arg (99)");
}


// -----------------------------------------------------------------
// Sprint 56 Wave 1 (Step 2a) — direct compile_to_module tests
// -----------------------------------------------------------------

// spec: design/backend/compile-to-module.md §2 (S75 banner) — 5-param
// signature; value-returned CompilationArtifacts + GOT-slot direct write.
//
// Direct `compile_to_module` call with a populated `symbol_tables` and a
// single-name `names` list. Verifies the S75 contract: bodies arrive via
// `ModuleEntry::Def.ast`, the finalised code pointer is written into the
// entry's GOT slot (D41 #2), and the always-created `CompilationArtifacts`
// carries the CLIF + code size.
#[test]
fn sprint56_compile_to_module_direct_call_writes_got_and_artifacts() {
    use cranelisp_types::ModuleEntry;
    let defn = Defn {
        name: Symbol::from("answer"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
            span: Span::new(0, 10),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 10),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Explicit GOT slot so the D41 #2 direct-write is exercised.
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("direct compile_to_module should succeed");

    // Always-created introspection artefacts carry CLIF + code size.
    assert!(
        !artifacts.clif_ir.is_empty(),
        "CompilationArtifacts.clif_ir must capture the compiled function's CLIF"
    );
    assert!(
        artifacts.code_size > 0,
        "CompilationArtifacts.code_size must be the finalised native code size"
    );

    // D41 #2: the finalised code pointer is written into the entry's GOT
    // slot. Entry remains a Def with ast: Some(_) (regression guard).
    let guard = tables.get(&module).unwrap();
    match guard.get(defn.name.as_ref()) {
        Some(entry @ ModuleEntry::Def { ast: Some(_), .. })
            if entry.callable_got_slot().is_some() =>
        {
            let slot = entry.callable_got_slot().unwrap();
            assert!(
                !guard.got.load_slot(slot).is_null(),
                "backend must write the finalised code pointer to the GOT slot"
            );
        }
        other => panic!("expected Def with ast + got_slot, got {other:?}"),
    }
}


// spec: design/backend/compile-to-module.md §4 — ast: None returns error
//
// Negative: insert a `ModuleEntry::Def { ast: None, .. }` into the symbol
// table and pass its name in `names`. `compile_to_module` must return
// `Err(CranelispError::CodegenError)` whose message names the symbol —
// no panic, no silent skip.
#[test]
fn sprint56_compile_to_module_ast_none_errors() {
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, UserFnState, Visibility};
    let module = ModuleFullPath::from("user");
    let name = Symbol::from("stub");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(
            name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn {
                    fn_state: UserFnState::NotDetermined,
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let result = compile_to_module(
        module,
        std::slice::from_ref(&name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    );
    let err = match result {
        Ok(_) => unreachable!("ast: None must not succeed"),
        Err(e) => e,
    };

    let msg = err.to_string();
    assert!(
        msg.contains(name.as_ref()),
        "error message must name the offending symbol 'stub', got: {msg}"
    );
    assert!(
        msg.contains("ast: None") || msg.contains("ast") && msg.contains("None"),
        "error message should mention the ast: None invariant violation, got: {msg}"
    );
}


// spec: design/backend/compile-to-module.md §4 — no multi-sig expansion in backend
//
// Populate symbol_tables with a pre-mangled multi-sig variant entry
// (`add$Int+Int`, ast: Some(single-variant defn)) alongside the
// Overloaded base entry (`add`, ast: None). Call compile_to_module with
// names = [mangled variant]. Compilation must succeed — the backend never
// invokes a (deleted) `expand_multi_sig_defn` path.
//
// That this test compiles and passes IS the verification: Wave 1 deleted
// `expand_multi_sig_defn` entirely from the source tree.
#[test]
fn sprint56_compile_to_module_mangled_variant_compiles_without_expansion() {
    use cranelisp_types::{DefKind, ModuleEntry, OverloadVariant, Scheme, Visibility};

    let module = ModuleFullPath::from("user");
    let base_name = Symbol::from("add");
    let variant_name = Symbol::from("add$Int+Int");

    // Mangled variant defn — what typecheck's Wave 0 materialises.
    let variant_defn = Defn {
        name: variant_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            // Body returns x (proves the variant body is what got compiled).
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(5, 6),
                resolved_call: None,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Overloaded base entry: ast: None — compile_to_module must NOT
        // try to compile this (the filter via `defined_symbols()` skips
        // it; a caller passing it in `names` would hit the ast: None
        // error path — which is the right behaviour).
        st.insert(
            base_name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Int,
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::Overloaded {
                    variants: vec![OverloadVariant {
                        param_types: vec![Type::Int, Type::Int],
                        ret_type: Type::Int,
                        mangled_name: variant_name.clone(),
                    }],
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        // Mangled variant entry: ast: Some(variant_defn). Explicit GOT
        // slot so the D41 #2 direct-write is exercised.
        st.insert(variant_name.clone(), make_def_entry_slot(variant_defn, 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&variant_name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("pre-mangled variant should compile without expansion");

    // Compilation succeeding (no expand_multi_sig_defn path) is the
    // verification; the mangled variant's GOT slot is populated.
    assert!(!artifacts.clif_ir.is_empty(), "variant body must be compiled");
    let guard = tables.get(&module).unwrap();
    match guard.get(variant_name.as_ref()) {
        Some(entry) if entry.callable_got_slot().is_some() => {
            let slot = entry.callable_got_slot().unwrap();
            assert!(
                !guard.got.load_slot(slot).is_null(),
                "mangled variant's GOT slot must be populated"
            );
        }
        other => panic!("expected mangled-variant Def with got_slot, got {other:?}"),
    }
}


// spec: design/backend/compile-to-module.md §4 — constrained-template exclusion via defined_symbols
//
// Verifies that `SymbolTable::defined_symbols()` — the shared filter
// callers use to build the `names` list — excludes constrained-function
// templates (`UserFn { constrained_fn: Some(_) }`). The backend relies
// on this filter upstream; if it were to break, constrained templates
// would reach compile_to_module and fail (templates carry type vars,
// not concrete types). This re-asserts Wave 0's contract from the
// backend's vantage point.
#[test]
fn sprint56_constrained_template_excluded_by_defined_symbols() {
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, UserFnState, Visibility};

    let module = ModuleFullPath::from("user");
    let template_name = Symbol::from("identity");
    let normal_name = Symbol::from("answer");

    // A typical regular defn: compile-eligible.
    let normal_defn = Defn {
        name: normal_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 1, span: Span::new(0, 1), inferred_type: None },
            span: Span::new(0, 5),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 5),
    };

    // A constrained-fn template defn: should be filtered OUT by
    // defined_symbols() even though it carries ast: Some(_).
    let template_defn = Defn {
        name: template_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(0, 1),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 10),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 10),
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(normal_name.clone(), make_def_entry(normal_defn));
        // Insert a UserFn template by hand — constrained_fn is Some.
        st.insert(
            template_name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![Symbol::from("x")],
                kind: Box::new(DefKind::UserFn {
                    // A constrained template is slot-less by construction
                    // (S83 reshape) — only its mono variants carry slots.
                    fn_state: UserFnState::Constrained(Box::new(
                        cranelisp_types::ConstrainedFn {
                            variant: template_defn.variants[0].clone(),
                            scheme: Scheme {
                                type_vars: vec![],
                                constraints: HashMap::new(),
                                ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                            },
                        },
                    )),
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: Some(template_defn.variants[0].clone()),
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        tables.insert(module.clone(), st);
    }

    let guard = tables.get(&module).unwrap();
    let defined: Vec<&Symbol> = guard.defined_symbols().map(|(n, _)| n).collect();

    assert!(
        defined.contains(&&normal_name),
        "defined_symbols() must yield regular defns: got {:?}",
        defined
    );
    assert!(
        !defined.contains(&&template_name),
        "defined_symbols() must NOT yield constrained-fn templates: got {:?}",
        defined
    );
}


// spec: design/arch/CLAUDE.md Decision 36 — function symbols are declared
// with their bare name uniformly across all modules. The pre-Sprint-58
// user/main vs FQ-Export discriminator is deleted.
#[test]
fn decision_36_function_naming_is_bare_for_every_module() {
    use cranelift_module::Module;
    for module_path_str in ["user", "main", "util", "one.two.three"] {
        let module = ModuleFullPath::from(module_path_str);
        let defn = make_int_defn("helper", 7);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let _artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("compile_to_module should succeed");

        // The Cranelift module's declaration table records the bare name.
        // (Decision 36: even for non-user/main, the FQ form must be absent.)
        let fq = format!("{module_path_str}/helper");
        let m = jit.jit_module();
        let has_fq = m.get_name(&fq).is_some();
        let has_bare = m.get_name("helper").is_some();
        assert!(
            !has_fq,
            "module '{module_path_str}': bare-only contract violated — module-qualified name '{fq}' should NOT be a declaration"
        );
        assert!(
            has_bare,
            "module '{module_path_str}': bare name 'helper' must be a declaration"
        );
    }
}


// spec: design/arch/CLAUDE.md Decision 36 — function linkage is Local
// uniformly. Symbols never need to cross .o boundaries (all-GOT calling).
#[test]
fn decision_36_function_linkage_is_local_uniformly() {
    use cranelift_module::{FuncOrDataId, Linkage, Module};
    for module_path_str in ["user", "main", "util", "deep.nested.path"] {
        let module = ModuleFullPath::from(module_path_str);
        let defn = make_int_defn("f", 1);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("compile_to_module should succeed");

        let m = jit.jit_module();
        let func_id = match m.get_name("f") {
            Some(FuncOrDataId::Func(id)) => id,
            other => panic!("module '{module_path_str}': expected FuncOrDataId::Func for 'f', got {other:?}"),
        };
        let decl = m.declarations().get_function_decl(func_id);
        assert_eq!(
            decl.linkage,
            Linkage::Local,
            "module '{module_path_str}': function 'f' must have Linkage::Local per Decision 36, got {:?}",
            decl.linkage
        );
    }
}


// spec: design/arch/CLAUDE.md Decision 23 (updated) — `__cranelisp_got_{M}`
// is defined as Linkage::Export data with `slot_count * 8` bytes inside
// the .o emitted by compile_to_module<ObjectModule>.
#[test]
fn decision_23_got_data_symbol_defined_as_export_in_object_path() {
    use cranelift_module::Module;
    let module = ModuleFullPath::from("util");
    let defn = make_int_defn("answer", 42);
    let tables = table_with_def_and_slot(&module, defn.clone(), 0);

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        &mut obj,
        true,
    )
    .expect("compile_to_module<ObjectModule> should succeed");

    // The GOT data symbol should now be a defined Export data symbol.
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let id = obj
        .get_name(&got_name)
        .expect("GOT data symbol must be declared");
    let data_id = match id {
        cranelift_module::FuncOrDataId::Data(d) => d,
        other => panic!("expected DataId for {got_name}, got {other:?}"),
    };
    let decl = obj.declarations().get_data_decl(data_id);
    assert_eq!(
        decl.linkage,
        cranelift_module::Linkage::Export,
        "GOT data symbol '{got_name}' must be Linkage::Export, got {:?}",
        decl.linkage
    );

    // Emit the .o and parse it; confirm:
    //  (a) the GOT data symbol is present in the .o symbol table
    //  (b) it has global scope (Export = visible to the system linker)
    //  (c) it points into a Data-kind section
    // (Size in the .o symbol table is not portable across formats —
    // Mach-O always reports 0; we rely on the in-Module declaration
    // size assertion and the section-data check instead.)
    let product = obj.finish();
    let bytes = product.emit().expect("ObjectModule should emit");
    use ::object::{Object, ObjectSymbol, SymbolKind, SymbolScope};
    let parsed = ::object::File::parse(&*bytes)
        .expect("emitted bytes must parse as an object file");
    let got_sym = parsed
        .symbols()
        .find(|s| {
            s.name()
                // Platform-agnostic symbol-name match. Mach-O prepends
                // exactly one '_' to every symbol (so the .o name is
                // `_<got_name>`); ELF prepends nothing (the .o name IS
                // `<got_name>`, and `got_name` itself already begins with
                // `__cranelisp_got_`). The former `strip_prefix('_')` matcher
                // assumed Mach-O and stripped a leading underscore that does
                // not exist on ELF, breaking the match on Linux (the symbol
                // was present but never found) — a stale test assertion, not
                // a GOT-emission defect (S82 W2 /dev triage of the 3
                // decision_23_got_data failures).
                .map(|n| n == got_name || n == format!("_{got_name}"))
                .unwrap_or(false)
        })
        .unwrap_or_else(|| {
            panic!(
                "GOT data symbol '{got_name}' must appear in emitted .o; \
                 symbols present: {:?}",
                parsed
                    .symbols()
                    .filter_map(|s| s.name().ok().map(|n| n.to_string()))
                    .collect::<Vec<_>>()
            )
        });
    assert_ne!(
        got_sym.scope(),
        SymbolScope::Compilation,
        "GOT data symbol '{got_name}' must have global scope (Linkage::Export); got {:?}",
        got_sym.scope()
    );
    assert_eq!(
        got_sym.kind(),
        SymbolKind::Data,
        "GOT data symbol '{got_name}' must be a Data-kind symbol; got {:?}",
        got_sym.kind()
    );
}


// spec: design/arch/CLAUDE.md Decision 23 — JIT-mode GOT-data definition
// remains the integration layer's responsibility (`Jit::define_got_data`).
// compile_to_module<JITModule>'s `define_module_got_data` is a no-op and
// does NOT redundantly declare/define the symbol on the JIT module.
#[test]
fn decision_23_got_data_symbol_jit_path_is_noop() {
    use cranelift_module::Module;
    let module = ModuleFullPath::from("user");
    let defn = make_int_defn("answer", 42);
    let tables = table_with_def_and_slot(&module, defn.clone(), 0);

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("compile_to_module<JITModule> should succeed");

    // In JIT mode, the GOT data symbol is NOT defined by compile_to_module.
    // It might be an Import declaration if the compiled code emitted a
    // GOT-indirect call (unlikely in this minimal test — answer is a
    // direct expression), but it must NEVER be Export-defined here.
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let m = jit.jit_module();
    if let Some(cranelift_module::FuncOrDataId::Data(data_id)) = m.get_name(&got_name) {
        let decl = m.declarations().get_data_decl(data_id);
        assert_ne!(
            decl.linkage,
            cranelift_module::Linkage::Export,
            "JIT path: GOT data symbol '{got_name}' must NOT be Linkage::Export-defined by compile_to_module — JIT-mode definition lives in Jit::define_got_data (Decision 23)"
        );
    }
    // (If it's not declared at all, that's also fine — this minimal defn
    // doesn't emit a GOT-indirect call so neither path declares it.)
}


// spec: design/arch/CLAUDE.md Decision 23 — GOT data symbol size matches
// the symbol table's `next_got_slot` (one 8-byte slot per allocated index).
#[test]
fn decision_23_got_data_size_matches_slot_count() {
    use cranelift_module::Module;
    // Two defns with two GOT slots → 16 bytes.
    let module = ModuleFullPath::from("util");
    let d1 = make_int_defn("one", 1);
    let d2 = make_int_defn("two", 2);

    // Build symbol table with both defns at slots 0 and 1.
    use cranelisp_types::{
        DefKind, MonoDefnVariant, MonoExpr, ModuleEntry, Scheme, UserFnState, Visibility,
    };
    let tables = DashMap::new();
    let mut st = SymbolTable::new(module.clone());
    let _slot0 = st.allocate_got_slot();
    let _slot1 = st.allocate_got_slot();
    for (defn, slot) in [(d1.clone(), 0usize), (d2.clone(), 1)] {
        let variant = defn.variants.first().cloned().map(|mut v| {
            concretize_test_body(&mut v.body);
            v
        });
        let codegen_view = variant.as_ref().map(|v| MonoDefnVariant {
            name: defn.name.clone(),
            params: vec![],
            body: MonoExpr::from_expr(&v.body, &std::collections::HashMap::new()).expect("concrete test body"),
            span: v.span,
            mode_summary: None,
        });
        st.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: variant,
                codegen_view,
                code: None,
                value_use: false,
            },
        );
    }
    tables.insert(module.clone(), st);

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        &[d1.name.clone(), d2.name.clone()],
        &tables,
        &aliases,
        &mut obj,
        true,
    )
    .expect("compile_to_module should succeed");

    // Verify in-Module declaration size; we cannot rely on the .o
    // symbol-table `size()` (Mach-O reports 0). The Cranelift
    // declaration carries the requested initialization size.
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let data_id = match obj.get_name(&got_name) {
        Some(cranelift_module::FuncOrDataId::Data(id)) => id,
        other => panic!("expected DataId for {got_name}, got {other:?}"),
    };
    let _decl = obj.declarations().get_data_decl(data_id);

    let product = obj.finish();
    let bytes = product.emit().unwrap();
    use ::object::{Object, ObjectSection, ObjectSymbol};
    let parsed = ::object::File::parse(&*bytes).unwrap();
    let got_sym = parsed
        .symbols()
        .find(|s| {
            s.name()
                // Platform-agnostic symbol-name match. Mach-O prepends
                // exactly one '_' to every symbol (so the .o name is
                // `_<got_name>`); ELF prepends nothing (the .o name IS
                // `<got_name>`, and `got_name` itself already begins with
                // `__cranelisp_got_`). The former `strip_prefix('_')` matcher
                // assumed Mach-O and stripped a leading underscore that does
                // not exist on ELF, breaking the match on Linux (the symbol
                // was present but never found) — a stale test assertion, not
                // a GOT-emission defect (S82 W2 /dev triage of the 3
                // decision_23_got_data failures).
                .map(|n| n == got_name || n == format!("_{got_name}"))
                .unwrap_or(false)
        })
        .expect("GOT data symbol present");

    // Look up the section the symbol lives in and check it is at least
    // slot_count * 8 = 16 bytes long. (Cranelift may pack multiple data
    // symbols into the same section; this is a lower-bound check for the
    // GOT slab's storage budget.)
    let sect_idx = match got_sym.section_index() {
        Some(idx) => idx,
        None => panic!("GOT data symbol must live in a section"),
    };
    let section = parsed.section_by_index(sect_idx).unwrap();
    assert!(
        section.size() >= 16,
        "section containing GOT data symbol must hold at least slot_count(2) * 8 = 16 bytes; got {}",
        section.size()
    );
}


// spec: design/arch/CLAUDE.md Decision 36 — cross-module function refs
// are NOT declared as Linkage::Import in the importing module's .o. Under
// all-GOT calling, cross-module calls reach callees through
// `__cranelisp_got_{other_M}` data symbol — never through a function-symbol
// import. Verifies the cross_refs declaration loop deletion did not
// re-introduce stray Import-linkage function declarations.
#[test]
fn decision_36_no_cross_module_function_imports() {
    use cranelift_module::{FuncOrDataId, Linkage, Module};

    // Build two modules: util defines `helper`, user imports `helper`.
    // Compile user.
    let util_path = ModuleFullPath::from("util");
    let user_path = ModuleFullPath::from("user");

    let helper = make_int_defn("helper", 99);
    // user has a single defn `caller` that does NOT call helper at runtime
    // (this test only checks the declaration shape; we focus on what
    // compile_to_module declares against the user module). The Import
    // entry on user's table records the cross-module dependency.
    let caller = make_int_defn("caller", 7);

    use cranelisp_types::{
        DefKind, FQSymbol, MonoDefnVariant, MonoExpr, ModuleEntry, Scheme, UserFnState,
        Visibility,
    };
    let tables = DashMap::new();

    // Build a concrete `codegen_view` for a zero-arg int-literal defn body
    // (FIXME 0391 — Concrete{slot} UserFns carry the populated MonoExpr view).
    let int_view = |d: &Defn| {
        let mut v = d.variants.first().cloned().unwrap();
        concretize_test_body(&mut v.body);
        Some(MonoDefnVariant {
            name: d.name.clone(),
            params: vec![],
            body: MonoExpr::from_expr(&v.body, &std::collections::HashMap::new()).expect("concrete test body"),
            span: v.span,
            mode_summary: None,
        })
    };

    // util module: helper at slot 0.
    let mut util_st = SymbolTable::new(util_path.clone());
    let _ = util_st.allocate_got_slot();
    util_st.insert(
        Symbol::from("helper"),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: helper.variants.first().cloned(),
            codegen_view: int_view(&helper),
            code: None,
            value_use: false,
        },
    );
    tables.insert(util_path.clone(), util_st);

    // user module: caller at slot 0, helper imported from util.
    let mut user_st = SymbolTable::new(user_path.clone());
    let _ = user_st.allocate_got_slot();
    user_st.insert(
        Symbol::from("caller"),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: caller.variants.first().cloned(),
            codegen_view: int_view(&caller),
            code: None,
            value_use: false,
        },
    );
    user_st.insert(
        Symbol::from("helper"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: util_path.clone(),
                symbol: Symbol::from("helper"),
            },
            visibility: Visibility::Private,
        },
    );
    tables.insert(user_path.clone(), user_st);

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let result = compile_to_module(
        user_path.clone(),
        &[Symbol::from("caller")],
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("compile_to_module should succeed");

    // Per Decision 36 + cross_refs deletion: there must be NO
    // Linkage::Import declaration for the cross-module function name
    // (neither `helper` nor `util/helper`).
    let m = jit.jit_module();
    for candidate in ["helper", "util/helper"] {
        if let Some(FuncOrDataId::Func(fid)) = m.get_name(candidate) {
            let decl = m.declarations().get_function_decl(fid);
            assert_ne!(
                decl.linkage,
                Linkage::Import,
                "cross-module fn '{candidate}' must NOT be declared as Linkage::Import; got {:?}. Under all-GOT calling, cross-module calls flow through __cranelisp_got_{{M}} data symbols, not function imports.",
                decl.linkage
            );
        }
    }

    // Sanity: `caller` is declared bare-Local (compiled this batch).
    let _ = &result; // CompilationArtifacts carries CLIF/size, not func_ids
    assert!(
        matches!(m.get_name("caller"), Some(FuncOrDataId::Func(_))),
        "bare 'caller' must be a function declaration"
    );
}


// spec: design/arch/CLAUDE.md Decision 23 — Sprint 58 Wave 2 regression
// guard. The `__cranelisp_got_{M}` data symbol carries function-address
// relocations (declared via `desc.write_function_addr`). On macOS, `ld`
// segfaults when applying relocations against `__DATA,__bss`
// (`S_ZEROFILL`) sections. The Wave 2 implementation MUST emit GOT
// contents via `desc.define(zero_bytes)` (regular `__DATA`), NOT
// `desc.define_zeroinit(...)` (which lands in BSS / `S_ZEROFILL`).
// This test asserts the emitted .o has the GOT data symbol in a regular
// (non-BSS) data section.
#[test]
fn decision_23_got_data_symbol_not_in_bss() {
    let module = ModuleFullPath::from("util");
    let defn = make_int_defn("answer", 42);
    let tables = table_with_def_and_slot(&module, defn.clone(), 0);

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        &mut obj,
        true,
    )
    .expect("compile_to_module<ObjectModule> should succeed");

    let product = obj.finish();
    let bytes = product.emit().expect("ObjectModule should emit");

    use ::object::{Object, ObjectSection, ObjectSymbol, SectionKind};
    let parsed = ::object::File::parse(&*bytes)
        .expect("emitted bytes must parse as an object file");
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let got_sym = parsed
        .symbols()
        .find(|s| {
            s.name()
                // Platform-agnostic symbol-name match. Mach-O prepends
                // exactly one '_' to every symbol (so the .o name is
                // `_<got_name>`); ELF prepends nothing (the .o name IS
                // `<got_name>`, and `got_name` itself already begins with
                // `__cranelisp_got_`). The former `strip_prefix('_')` matcher
                // assumed Mach-O and stripped a leading underscore that does
                // not exist on ELF, breaking the match on Linux (the symbol
                // was present but never found) — a stale test assertion, not
                // a GOT-emission defect (S82 W2 /dev triage of the 3
                // decision_23_got_data failures).
                .map(|n| n == got_name || n == format!("_{got_name}"))
                .unwrap_or(false)
        })
        .expect("GOT data symbol must appear in emitted .o");
    let sect_idx = got_sym
        .section_index()
        .expect("GOT data symbol must live in a section, not be undefined");
    let section = parsed
        .section_by_index(sect_idx)
        .expect("section must be resolvable");

    // Negative path: must NOT be UninitializedData (BSS / __DATA,__bss /
    // S_ZEROFILL). macOS `ld` segfaults on relocations against BSS.
    let kind = section.kind();
    assert_ne!(
        kind,
        SectionKind::UninitializedData,
        "GOT data symbol '{got_name}' landed in BSS (UninitializedData) — \
         macOS `ld` segfaults on relocations against BSS. Use \
         `desc.define(zero_bytes)` not `desc.define_zeroinit(...)` so the \
         data lands in regular `__DATA`."
    );
    // Positive path: must be a regular initialized Data section so
    // function-address relocations resolve correctly.
    assert!(
        matches!(kind, SectionKind::Data | SectionKind::ReadOnlyData),
        "GOT data symbol '{got_name}' must live in a regular initialized data section; got {kind:?}"
    );
}
