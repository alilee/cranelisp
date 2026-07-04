//! Relocated crate-root fn-as-value + value-use tests (FIXME 0495 step 1): constructor-as-value fallthrough, value-position trait-method dispatch, and the vec-query value-use wrapper trio + curry seam. Verbatim relocation from `src/tests.rs`.

use crate::test_support::*;


// spec: design/backend/compile-to-module.md §2.6.6 — constructor-as-value
// through the generic fn-as-value GOT path (S75 W4 closure deletion).
//
// This is the durable regression guard for deleting the bespoke
// `compile_data_constructor_as_value` + `compile_ctor_wrapper_body` family.
// It proves the corrected `compile_var` dispatch: a *data* constructor
// referenced as a value (`(let [f Some] (f 3))`) is no longer special-cased;
// it falls through to `is_known_function` → `compile_fn_as_value` over the
// got-slotted constructor `Def` — the SAME GOT/fn-as-value mechanism
// `compile_operator_as_value` uses for primitives (§2.6.1, Decision 48).
//
// Two-stage `make_def_entry_slot` pattern (§2.6.6):
//   Stage 1 — got-slot + compile the constructor `Def` (its `Expr::ConstrADT`
//             body → `compile_constr_adt` → `emit_adt_construct`) so the GOT
//             slot holds a live callable.
//   Stage 2 — compile a consumer that references the constructor as a value;
//             `compile_fn_as_value`'s `emit_wrapper_call` GOT-indirects to
//             slot 0. Run end-to-end (slab base registered via
//             `Jit::new_with_symbols`, the precedent set by
//             `jit_got_symbol_address_is_slab_base` /
//             `test_extern_primitive_with_resolved_call`) and assert the
//             constructed ADT's field round-trips.
//
// Backend EXPECTS the constructor's GOT slot to be populated; the harness
// populates it the way int will at S77 (§2.6.5). Backend does not got-slot
// constructors itself — that is typecheck + int's job, exactly as primitives'
// GOT entries are not backend's.
#[test]
fn constructor_as_value_falls_through_to_fn_as_value() {
    use cranelisp_types::{
        DefKind, FQTypeName, ModuleEntry, Scheme, TypeName,
    };

    let module = ModuleFullPath::from("user");
    let fqtn = FQTypeName::new(module.clone(), TypeName::from("Option"));

    // The constructor `Some`'s synthesised body: ConstrADT { tag: 1,
    // fields: [Var("v")] } — the exact shape typecheck produces at S77.
    let ctor_body = Expr::ConstrADT {
        type_name: fqtn.clone(),
        tag: 1,
        fields: vec![Expr::Var {
            name: Symbol::from("v"),
            span: Span::new(10, 11),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }],
        span: Span::new(0, 12),
        inferred_type: Some(Box::new(Type::ADT(fqtn.clone(), vec![]))),
    };
    let ctor_defn = Defn {
        name: Symbol::from("Some"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("v"), None)],
            body: ctor_body,
            span: Span::new(0, 12),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 12),
    };
    // make_def_entry_slot stamps kind = UserFn; override to Constructor so
    // `lookup_constructor` / `data_constructor_info` recognise it AND
    // `resolve_got_target` finds the got slot (slot 0).
    let base_entry = make_def_entry_slot(ctor_defn.clone(), 0);
    // The slot now rides on the callable variant; carry it onto the
    // Constructor we re-stamp (slot 0).
    let ctor_slot = base_entry
        .callable_got_slot()
        .expect("make_def_entry_slot stamps a slot");
    let ctor_entry = match base_entry {
        ModuleEntry::Def {
            visibility,
            docstring,
            param_names,
            callees,
            trait_origin,
            seq,
            ast,
            code,
            ..
        } => ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![]))),
            },
            visibility,
            docstring,
            param_names,
            kind: Box::new(DefKind::Constructor {
                got_slot: ctor_slot,
                type_name: fqtn.clone(),
                tag: 1,
                field_count: 1,
                internal: false,
                type_def: None,
                mode_summary: None,
            }),
            callees,
            trait_origin,
            seq,
            ast,
            codegen_view: None,
            code,
            value_use: false,
        },
        _ => unreachable!("make_def_entry_slot builds a Def"),
    };

    // Consumer: (let [f Some] (f 3)) — references `Some` as a value, then
    // calls the bound closure. The `[f Some]` binding compiles `Some` via
    // `compile_var` → fall-through → `compile_fn_as_value` (the path under
    // test); `(f 3)` is a local-var closure call.
    let consumer_body = Expr::Let {
        bindings: vec![(
            Symbol::from("f"),
            Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(100, 104),
                resolved_call: None,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("f"),
                span: Span::new(110, 111),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 3,
                span: Span::new(112, 113),
                inferred_type: None,
            }],
            span: Span::new(109, 114),
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(90, 115),
        inferred_type: None,
    };
    let consumer_defn = Defn {
        name: Symbol::from("useit"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: consumer_body,
            span: Span::new(90, 115),
        }],
        visibility: Visibility::Public,
        span: Span::new(90, 115),
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(ctor_defn.name.clone(), ctor_entry);
        st.insert(consumer_defn.name.clone(), make_def_entry_slot(consumer_defn.clone(), 1));
        st.next_got_slot = 2;
        tables.insert(module.clone(), st);
    }

    // Register __cranelisp_got_user → the table's GOT slab base BEFORE
    // building the JIT (base_ptr is stable for the GotTable's lifetime).
    let got_data_name = crate::compiler::got_data_symbol_name(&module);
    let got_base = tables
        .get(&module)
        .map(|st| st.got.base_ptr())
        .expect("user table just inserted");
    let extras: Vec<(&str, *const u8)> = vec![(got_data_name.as_str(), got_base)];

    let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
    let aliases = empty_aliases();
    let names = vec![ctor_defn.name.clone(), consumer_defn.name.clone()];
    compile_to_module(module.clone(), &names, &tables, &aliases, jit.jit_module(), true)
        .expect("constructor Def + consumer compile (closure deletion regression guard)");

    // Stage 1 assertion: the constructor `Def`'s body compiled into a live
    // callable at slab slot 0 (non-null after finalize — the same write
    // `compile_to_module_writes_got_slot_after_finalize` asserts).
    {
        let guard = tables.get(&module).expect("table present");
        match guard.get("Some") {
            Some(entry) if entry.callable_got_slot().is_some() => {
                let slot = entry.callable_got_slot().unwrap();
                assert!(
                    !guard.got.load_slot(slot).is_null(),
                    "constructor body must finalize to a live callable in its GOT slot (Stage 1)"
                );
            }
            other => panic!("expected got-slotted constructor Def, got {other:?}"),
        }
    }

    // Stage 2 assertion: run the consumer end-to-end. It builds `(Some 3)`
    // through the GOT-indirect fn-as-value wrapper and returns the heap
    // pointer to `[.., tag=1, field=3]`. Read the field back.
    let ptr = jit.get_ptr_by_name(&consumer_defn.name, 0).expect("finalize consumer");
    assert!(!ptr.is_null(), "consumer must finalize to a non-null fn ptr");
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let adt_ptr = func();
    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        panic!("runtime panic running consumer: {msg}");
    }
    assert!(adt_ptr != 0, "constructor-as-value must allocate a heap ADT");
    // Field 0 lives at HeapAdt::field_offset(0) from the base pointer.
    let field0 = unsafe {
        let field_addr = (adt_ptr as usize
            + crate::heap::HeapAdt::field_offset(0) as usize)
            as *const i64;
        *field_addr
    };
    assert_eq!(
        field0, 3,
        "constructor-as-value (map-style first-class use) must construct the ADT \
         with the passed field; got {field0}"
    );
}


// spec: 07-traits §7.6 — a trait method used as a first-class value
// dispatches to the impl chosen by typecheck for the value's type, NOT a
// hard-coded default. This is the backend half of FIXME 0300 Symptom B.
//
// `(let [f +] (f 1.0 2.0))` where typecheck has annotated the value-position
// `+` Var with `resolved_call: Some(BuiltinFn { name: "add-f64" })` and
// `inferred_type: Fn([Float, Float], Float)`. The new `compile_var` early
// branch emits a zero-capture dispatch-wrapper that calls `add-f64` (float
// add). The OLD hard-coded `compile_operator_as_value` path mapped `+` →
// `add-i64` unconditionally — integer add on the two float bit-patterns —
// which yields a garbage / `inf.0`-shaped result, never `3.0`. So a `3.0`
// result proves the resolution is honored and the Int path is bypassed.
//
// `add-f64` is an INLINE builtin (`primitives_inline`), so this runs
// end-to-end inside the backend unit-test JIT with no `cranelisp-primitives`
// dependency (Decision 48) and no extern symbol.
#[test]
fn value_position_plus_float_dispatches_add_f64_not_add_i64() {
    // The value-position `+` reference, fully annotated as typecheck's
    // value-position resolution pass produces (FIXME 0300 Step 2/3).
    let plus_as_value = Expr::Var {
        name: Symbol::from("+"),
        span: Span::new(100, 101),
        resolved_call: Some(Box::new(
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("add-f64"),
            },
        )),
        inferred_type: Some(Box::new(Type::Fn(
            vec![Type::Float, Type::Float],
            Box::new(Type::Float),
        ))),
    };

    // Consumer: (let [f +] (f 1.0 2.0)) — binds the dispatch-wrapper closure
    // to `f`, then applies it. `(f 1.0 2.0)` is a local-var closure call.
    let consumer_body = Expr::Let {
        bindings: vec![(Symbol::from("f"), plus_as_value)],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("f"),
                span: Span::new(110, 111),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: Span::new(112, 115),
                    inferred_type: Some(Box::new(Type::Float)),
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: Span::new(116, 119),
                    inferred_type: Some(Box::new(Type::Float)),
                },
            ],
            span: Span::new(109, 120),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Float)),
        }),
        span: Span::new(90, 121),
        inferred_type: Some(Box::new(Type::Float)),
    };

    let value = test_compile_and_run(
        &consumer_body,
        &empty_check(),
        &empty_tables(),
    )
    .expect("value-position + (add-f64) should compile and run");

    let result = f64::from_bits(value as u64);
    assert_eq!(
        result, 3.0,
        "value-position `+` on Floats must dispatch to add-f64 (→ 3.0); \
         a non-3.0 result means the hard-coded add-i64 path leaked \
         (FIXME 0300 Symptom B)"
    );
}


// spec: 07-traits §7.6 — value-position trait method resolved to a TraitMethod
// (mangled impl) emits a dispatch-wrapper that calls the *mangled name*, NOT
// the hard-coded operator primitive. We assert this WITHOUT a GOT slot for
// the impl (which is the int-binary's concern; the four e2e tests cover the
// run side after the int slice): the wrapper's `emit_wrapper_call` resolves
// the mangled name `Eq.=$String` and — because no slot is registered in this
// minimal table — fails with an error naming `Eq.=$String`. That error is
// proof-positive that `compile_var` took the resolved-call branch and tried
// to dispatch to the typecheck-chosen impl, rather than silently emitting
// the hard-coded `eq-i64` (`operator_primitive_name`) which would have
// compiled "successfully" to the WRONG impl (Symptom B).
#[test]
fn value_position_eq_string_dispatches_to_mangled_impl_not_eq_i64() {
    let module = ModuleFullPath::from("user");

    // `=` on String resolved to the mangled trait-impl name (the non-
    // primitive TraitMethod path). The wrapper must call this name, not
    // emit the hard-coded `eq-i64`.
    let eq_as_value = Expr::Var {
        name: Symbol::from("="),
        span: Span::new(50, 51),
        resolved_call: Some(Box::new(
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::FQTraitName::new(
                    module.clone(),
                    cranelisp_types::TraitName::from("Eq"),
                ),
                method_name: Symbol::from("="),
                impl_type: cranelisp_types::FQTypeName::new(
                    ModuleFullPath::from("primitives"),
                    cranelisp_types::TypeName::from("String"),
                ),
                mangled_name: cranelisp_types::JitSymbol::from("Eq.=$String"),
            },
        )),
        inferred_type: Some(Box::new(Type::Fn(
            vec![Type::String, Type::String],
            Box::new(Type::Bool),
        ))),
    };
    let defn = Defn {
        name: Symbol::from("__expr__"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: eq_as_value,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(defn.name.clone(), make_def_entry(defn.clone()));
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).expect("jit init");
    let aliases = empty_aliases();
    let names = vec![defn.name.clone()];
    let result = compile_to_module(
        module.clone(),
        &names,
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    );
    // `CompilationArtifacts` is not `Debug`, so match rather than `expect_err`.
    let err = match result {
        Ok(_) => panic!(
            "without a registered GOT slot for the impl, the dispatch-wrapper's \
             call to the mangled name must fail — a clean compile means the \
             hard-coded eq-i64 path leaked (FIXME 0300 Symptom B)"
        ),
        Err(e) => e,
    };

    let msg = format!("{err:?}");
    assert!(
        msg.contains("Eq.=$String"),
        "the codegen error must name the typecheck-chosen mangled impl \
         `Eq.=$String` (proving the wrapper dispatched to the resolved \
         target); a silent success or an `eq-i64` reference would mean the \
         hard-coded operator path leaked (FIXME 0300 Symptom B). Got: {msg}"
    );
}


// spec: design/backend/ownership-codegen.md §12.7 — `vec-get` used as a VALUE
// wraps via `compile_fn_as_value` → `emit_wrapper_call`; the wrapper must
// inline-emit the bounds-checked read (element type plumbed from the Var's
// concrete `inferred_type`), never `call_indirect` through the NULL
// primitives-table slot. RED on HEAD: SIGSEGV (jump to address 0).
#[test]
fn vec_get_as_value_wrapper_inline_emits_and_returns_element() {
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let prim_ty = Type::Fn(vec![vec_int.clone(), Type::Int], Box::new(Type::Int));
    let consumer = vec_query_value_consumer(
        "vec-get",
        prim_ty,
        vec![
            vec_int_lit(&[10, 20, 30], 30),
            Expr::IntLit {
                value: 1,
                span: Span::new(40, 41),
                inferred_type: Some(Box::new(Type::Int)),
            },
        ],
        Type::Int,
    );
    assert_eq!(run_vec_query_value_consumer(consumer), 20);
}


// spec: design/backend/ownership-codegen.md §12.7 — `vec-set` as a VALUE: the
// wrapper takes the owned-temporary polarity (no consuming inc on the new
// element; vec trivially at last use ⇒ COW rc==1 mutate-in-place). RED on
// HEAD: SIGSEGV.
#[test]
fn vec_set_as_value_wrapper_inline_emits_and_updates_element() {
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let prim_ty = Type::Fn(
        vec![vec_int.clone(), Type::Int, Type::Int],
        Box::new(vec_int.clone()),
    );
    let consumer = vec_query_value_consumer(
        "vec-set",
        prim_ty,
        vec![
            vec_int_lit(&[10, 20, 30], 30),
            Expr::IntLit {
                value: 1,
                span: Span::new(40, 41),
                inferred_type: Some(Box::new(Type::Int)),
            },
            Expr::IntLit {
                value: 99,
                span: Span::new(42, 44),
                inferred_type: Some(Box::new(Type::Int)),
            },
        ],
        vec_int,
    );
    let vec_ptr = run_vec_query_value_consumer(consumer);
    assert!(vec_ptr != 0, "vec-set-as-value must return a Vec pointer");
    assert_eq!(vec_len_for_test(vec_ptr), 3, "length preserved");
    assert_eq!(vec_elem_for_test(vec_ptr, 1), 99, "element 1 updated");
    assert_eq!(vec_elem_for_test(vec_ptr, 0), 10, "element 0 retained");
}


// spec: design/backend/ownership-codegen.md §12.7 — `vec-push` as a VALUE:
// same owned-temporary polarity; COW rc==1 fast path appends. RED on HEAD:
// SIGSEGV.
#[test]
fn vec_push_as_value_wrapper_inline_emits_and_appends() {
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let prim_ty = Type::Fn(vec![vec_int.clone(), Type::Int], Box::new(vec_int.clone()));
    let consumer = vec_query_value_consumer(
        "vec-push",
        prim_ty,
        vec![
            vec_int_lit(&[10, 20], 30),
            Expr::IntLit {
                value: 30,
                span: Span::new(40, 42),
                inferred_type: Some(Box::new(Type::Int)),
            },
        ],
        vec_int,
    );
    let vec_ptr = run_vec_query_value_consumer(consumer);
    assert!(vec_ptr != 0, "vec-push-as-value must return a Vec pointer");
    assert_eq!(vec_len_for_test(vec_ptr), 3, "length incremented");
    assert_eq!(vec_elem_for_test(vec_ptr, 2), 30, "pushed element present");
}


// spec: design/backend/ownership-codegen.md §12.7 — the CURRY seam is distinct:
// a partial application `(vec-get v)` routes `compile_auto_curry` →
// `emit_curry_target_call` with `trait_resolution: BuiltinFn{vec-get}`; the
// vec family is NOT in `primitives_inline`, so on HEAD the wrapper declares a
// `Linkage::Import` for `vec-get` and JIT-finalize panics
// ("can't resolve symbol vec-get" — the e2e exit-101 signature). The curry
// wrapper must inline-emit instead, with the element type recovered from the
// applied Vec argument's concrete type.
#[test]
fn vec_get_curried_partial_wrapper_inline_emits_and_applies() {
    use cranelisp_types::ResolvedCall;
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let get_ty = Type::Fn(vec![vec_int.clone(), Type::Int], Box::new(Type::Int));
    let curried_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));

    // (defn use1 [] (let [g (vec-get [10 20 30])] (g 1)))
    let body = Expr::Let {
        bindings: vec![(
            Symbol::from("g"),
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(10, 17),
                    resolved_call: None,
                    inferred_type: Some(Box::new(get_ty)),
                }),
                args: vec![vec_int_lit(&[10, 20, 30], 30)],
                span: Span::new(9, 45),
                resolved_call: Some(Box::new(ResolvedCall::AutoCurry {
                    target_name: Symbol::from("vec-get"),
                    applied_count: 1,
                    total_count: 2,
                    trait_resolution: Some(Box::new(ResolvedCall::BuiltinFn {
                        name: Symbol::from("vec-get"),
                    })),
                })),
                inferred_type: Some(Box::new(curried_ty.clone())),
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("g"),
                span: Span::new(50, 51),
                resolved_call: None,
                inferred_type: Some(Box::new(curried_ty)),
            }),
            args: vec![Expr::IntLit {
                value: 1,
                span: Span::new(52, 53),
                inferred_type: Some(Box::new(Type::Int)),
            }],
            span: Span::new(49, 54),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        span: Span::new(5, 55),
        inferred_type: Some(Box::new(Type::Int)),
    };
    let consumer = Defn {
        name: Symbol::from("use-vec-query"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::new(0, 56),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 56),
    };
    assert_eq!(run_vec_query_value_consumer(consumer), 20);
}
