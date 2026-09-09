//! Monomorphisation signature reconstruction, instance publication and annotation guards.

use cranelisp_types::{
    Binding, Defn, DefnVariant, Expr, Life, ModuleFullPath, Span, Symbol, TemplateKind,
    TopLevel, Type, TypeName, Visibility,
};

use super::*;
use crate::checker::TypeCheckEnv;
use crate::program::test_support::{
    check_src, collect_resolved_targets, seed_specific_import, symbol_names_containing,
};
use crate::traits::test_helpers::*;
// -----------------------------------------------------------------------
// Mono-instance minting via the check_repl_input / monomorphise_call seams.
// -----------------------------------------------------------------------

// spec: design/typecheck/ast-annotation.md §9.4 — mono specialisation ast + distinct GOT slot
#[test]
fn wave0_mono_entry_registered_with_distinct_got_slot() {
    let mut tc = tc_with_prims();
    register_num_for_int(&mut tc);

    // Template: (defn add [x y] (+ x y))
    let add_defn = cranelisp_types::TopLevel::Defn(Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                args: vec![
                    Expr::var(Symbol::from("x"), Span::new(20, 21)),
                    Expr::var(Symbol::from("y"), Span::new(22, 23)),
                ],
                span: Span::new(17, 24),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 25),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 25),
    });
    tc.check_repl_input_self(&add_defn).unwrap();

    // Concrete call-site triggers monomorphisation: (defn main [] (add 1 2))
    let main_defn = cranelisp_types::TopLevel::Defn(Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), Span::new(200, 203))),
                args: vec![
                    Expr::IntLit {
                        value: 1,
                        span: Span::new(204, 205),
                        inferred_type: None,
                    },
                    Expr::IntLit {
                        value: 2,
                        span: Span::new(206, 207),
                        inferred_type: None,
                    },
                ],
                span: Span::new(199, 208),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(180, 209),
        }],
        visibility: Visibility::Public,
        span: Span::new(180, 209),
    });
    tc.check_repl_input_self(&main_defn).unwrap();

    // Template entry: kind UserFn { constrained_fn: Some(_) }.
    // NOTE: §9.2 of design/typecheck/ast-annotation.md says the template's `ast`
    // "stays None" to signal "skip at codegen". That is the future intent — the
    // filter in `defined_symbols()` (§9.5) gates on `kind`, not `ast`, so the
    // invariant that matters today is `kind`. The mono entry below carries the
    // compilable body.
    let template_got_slot = {
        let st = tc.symbol_table();
        match st.get("add") {
            Some(entry) => {
                assert!(
                    matches!(
                        entry.callable().map(|c| &c.arm.life),
                        Some(Life::Template {
                            kind: TemplateKind::Constrained(_),
                            ..
                        })
                    ),
                    "template 'add' should be constrained"
                );
                // S83 (Principle 20): a constrained template carries no slot
                // (read via the accessor) — `None` by construction.
                entry.callable_got_slot()
            }
            other => panic!("'add' template should be Def entry, got {:?}", other),
        }
    };

    // Mono entry: kind UserFn(Concrete), ast: Some(..), has a GOT slot distinct from template.
    let mono_got_slot = {
        let st = tc.symbol_table();
        // FIXME 0519: mono names are home-qualified `{home}/{bare}$sig`; the
        // fixture's current module is `test`.
        match st.get("test/add$Int") {
            Some(entry) => {
                let callable = entry.callable().expect("mono callable");
                assert!(
                    matches!(callable.arm.life, Life::Concrete { .. }),
                    "mono 'test/add$Int' should be concrete"
                );
                let Life::Concrete {
                    ast: Some(defn), ..
                } = &callable.arm.life
                else {
                    panic!("mono must carry ast")
                };
                // Per S69 Submission 35: ast: Option<DefnVariant>; the name lives on
                // the symbol-table key ("add$Int+Int" here), not on the variant.

                // All inferred types on the mono body are concrete.
                assert_types_concrete(&defn.body);

                // The resolved_call on the + call site must be set (SigDispatch or
                // TraitMethod — both are valid concrete resolutions post-mono).
                if let Expr::Apply { resolved_call, .. } = &defn.body {
                    assert!(
                        resolved_call.is_some(),
                        "mono body's + call site must have resolved_call set"
                    );
                } else {
                    panic!("mono body should be Apply, got {:?}", defn.body);
                }

                entry
                    .callable_got_slot()
                    .expect("mono must have a GOT slot assigned")
            }
            other => panic!("'test/add$Int' mono should be Def entry, got {:?}", other),
        }
    };

    // Distinctness: template slot (if any) must differ from the mono slot.
    // Constrained templates usually get no slot (`None`); in that case any
    // Some(slot) on the mono is trivially distinct.
    if let Some(t) = template_got_slot {
        assert_ne!(
            t, mono_got_slot,
            "template and mono must have distinct GOT slots"
        );
    }
}

// spec: design/typecheck/ast-annotation.md §9.4 — resolved-stage annotations
// live on the `MonoDefn.defn` AST, not on a side map (FIXME 0033).
//
// Pins the invariant that makes the S81 W-G `MonoDefn` side-map drop safe:
// `monomorphise_call` returns a `MonoDefn` whose `defn` AST already carries
// every `inferred_type` (concrete) and every call-site `resolved_call`. The
// dropped `MonoDefn.resolutions` / `MonoDefn.expr_types` Span-keyed maps held
// exactly this data; with them gone, the single source of truth is the AST.
// This test reads the returned `MonoDefn` directly (not the registered
// symbol-table entry) so it asserts the contract on `MonoDefn` itself.
#[test]
fn fixme0033_monodefn_annotations_live_on_defn_ast_not_side_maps() {
    let mut tc = tc_with_prims();
    register_num_for_int(&mut tc);

    // Template: (defn add [x y] (+ x y)) — constrained on Num via the `+`.
    let add_defn = cranelisp_types::TopLevel::Defn(Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                args: vec![
                    Expr::var(Symbol::from("x"), Span::new(20, 21)),
                    Expr::var(Symbol::from("y"), Span::new(22, 23)),
                ],
                span: Span::new(17, 24),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 25),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 25),
    });
    tc.check_repl_input_self(&add_defn).unwrap();

    // Drive `monomorphise_call` directly for `(add 1 2)` and capture the
    // returned `MonoDefn`. Construct the env borrowing individual fields so
    // `&mut tc.state` stays available (the test_support borrow-split idiom).
    let mono = {
        let env = TypeCheckEnv::new(
            &tc.modules,
            &tc.next_id,
            &tc.module_aliases,
            &tc.prelude_fallback,
        );
        env.monomorphise_call(
            &mut tc.state,
            &Symbol::from("add"),
            &MonoDemand::from_type_args(
                CallableTarget::Binding(FQSymbol {
                    module: ModuleFullPath::from("test"),
                    symbol: Symbol::from("add"),
                }),
                vec![ConcreteType::Int],
                Span::new(199, 208),
            ),
            None,
            None,
            None,
        )
        .unwrap()
        .expect("(add 1 2) must monomorphise")
    };

    // The mono body is the single variant's body. Every inferred_type on it
    // is concrete — that is the data the dropped `expr_types` side map held.
    let body = &mono.defn.variants.first().expect("mono has a variant").body;
    assert_types_concrete(body);

    // The `+` call site carries a concrete `resolved_call` directly on the
    // AST node — the data the dropped `resolutions` side map held.
    if let Expr::Apply { resolved_call, .. } = body {
        assert!(
            resolved_call.is_some(),
            "mono body's + call site must carry resolved_call on the AST node \
             (the dropped MethodResolutions side map is no longer the carrier)"
        );
    } else {
        panic!("mono body should be Apply, got {:?}", body);
    }
}

// spec: 07-traits §7.4 / design/typecheck/ast-annotation.md §9.4 — ≥2
// INSTANTIATIONS. A single generic (constrained) template called at TWO
// distinct concrete type sets mints TWO distinct mono instances, each a
// Concrete `Def` with the correct mangled key AND its own GOT slot. This is
// the crate-side mint-seam pin for the 0488 defect class (generic-fn missing
// monomorphisation at ≥2 instantiations) — it asserts the specific resolved
// facts (both keys minted, both Concrete, distinct slots), not "no panic".
#[test]
fn two_instantiations_mint_two_distinct_concrete_mono_entries() {
    let mut tc = tc_with_prims();
    register_num_for_int(&mut tc);
    register_num_impl_for_float(&mut tc);

    // Template: (defn add [x y] (+ x y)) — constrained on Num.
    let add_defn = TopLevel::Defn(Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                args: vec![
                    Expr::var(Symbol::from("x"), Span::new(20, 21)),
                    Expr::var(Symbol::from("y"), Span::new(22, 23)),
                ],
                span: Span::new(17, 24),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 25),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 25),
    });
    tc.check_repl_input_self(&add_defn).unwrap();

    // First instantiation: (defn use-int [] (add 1 2))
    let use_int = TopLevel::Defn(Defn {
        name: Symbol::from("use-int"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), Span::new(200, 203))),
                args: vec![
                    Expr::IntLit {
                        value: 1,
                        span: Span::new(204, 205),
                        inferred_type: None,
                    },
                    Expr::IntLit {
                        value: 2,
                        span: Span::new(206, 207),
                        inferred_type: None,
                    },
                ],
                span: Span::new(199, 208),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(180, 209),
        }],
        visibility: Visibility::Public,
        span: Span::new(180, 209),
    });
    tc.check_repl_input_self(&use_int).unwrap();

    // Second instantiation at a DISTINCT type set: (defn use-float [] (add 1.5 2.5))
    let use_float = TopLevel::Defn(Defn {
        name: Symbol::from("use-float"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), Span::new(300, 303))),
                args: vec![
                    Expr::FloatLit {
                        value: 1.5,
                        span: Span::new(304, 307),
                        inferred_type: None,
                    },
                    Expr::FloatLit {
                        value: 2.5,
                        span: Span::new(308, 311),
                        inferred_type: None,
                    },
                ],
                span: Span::new(299, 312),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(280, 313),
        }],
        visibility: Visibility::Public,
        span: Span::new(280, 313),
    });
    tc.check_repl_input_self(&use_float).unwrap();

    // BOTH mono instances must be minted, each Concrete, under its own key.
    let int_slot = assert_concrete_mono_slot(&tc, "test/add$Int");
    let float_slot = assert_concrete_mono_slot(&tc, "test/add$Float");

    // Distinct instantiations get distinct GOT slots.
    assert_ne!(
        int_slot, float_slot,
        "the two mono instances must occupy distinct GOT slots"
    );
}

/// Assert `key` names a registered Concrete mono `Def` with a GOT slot; return
/// the slot. Shared by the ≥2-instantiations cell above.
fn assert_concrete_mono_slot(tc: &crate::checker::TestFixture, key: &str) -> usize {
    let st = tc.symbol_table();
    match st.get(key) {
        Some(entry) => {
            let callable = entry.callable().expect("mono callable");
            assert!(
                matches!(callable.arm.life, Life::Concrete { .. }),
                "mono '{key}' should be concrete"
            );
            assert!(
                matches!(callable.arm.life, Life::Concrete { ast: Some(_), .. }),
                "mono '{key}' must carry a compilable ast: Some(..)"
            );
            entry
                .callable_got_slot()
                .unwrap_or_else(|| panic!("mono '{key}' must have a GOT slot assigned"))
        }
        other => panic!("mono '{key}' should be a Def entry, got {:?}", other),
    }
}

// -----------------------------------------------------------------------
// concrete_type_name — the bare-TypeName extractor used by the mangler.
// -----------------------------------------------------------------------

// spec: 07-traits §7.4.1 — concrete_type_name maps Int to TypeName
#[test]
fn test_concrete_type_name_int() {
    assert_eq!(concrete_type_name(&Type::Int), Some(TypeName::from("Int")));
}

// spec: 07-traits §7.4.1 — concrete_type_name maps Float to TypeName
#[test]
fn test_concrete_type_name_float() {
    assert_eq!(
        concrete_type_name(&Type::Float),
        Some(TypeName::from("Float"))
    );
}

// spec: 07-traits §7.4.1 — concrete_type_name maps Bool to TypeName
#[test]
fn test_concrete_type_name_bool() {
    assert_eq!(
        concrete_type_name(&Type::Bool),
        Some(TypeName::from("Bool"))
    );
}

// spec: 07-traits §7.4.1 — concrete_type_name maps String to TypeName
#[test]
fn test_concrete_type_name_string() {
    assert_eq!(
        concrete_type_name(&Type::String),
        Some(TypeName::from("String"))
    );
}

// spec: 07-traits §7.4.1 — concrete_type_name maps ADT to its TypeName
#[test]
fn test_concrete_type_name_adt() {
    assert_eq!(
        concrete_type_name(&Type::ADT(test_fqtn("Color"), vec![])),
        Some(TypeName::from("Color"))
    );
}

// spec: 07-traits §7.4.1 — type variable has no concrete type name
#[test]
fn test_concrete_type_name_var_is_none() {
    assert_eq!(concrete_type_name(&Type::Var(0)), None);
}

// spec: 07-traits §7.4.1 — concrete function types have no nominal impl target name.
#[test]
fn concrete_type_name_fn_is_none() {
    let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    assert!(
        fn_ty.is_concrete(),
        "a Fn over concrete arg/ret is itself concrete"
    );
    assert_eq!(concrete_type_name(&fn_ty), None);
}

// spec: design/typecheck/monomorphisation.md §11.8; sprints/s121-timeout-intake.md —
// a generic body that passes a bare constructor as a higher-order value must
// acquire the concrete constructor instance and its caller-local carrier when
// the enclosing body is rechecked.
#[test]
fn rechecked_bare_constructor_value_mints_and_carries_its_concrete_instance() {
    let control = fixture_for_rechecked_constructor_value("timeout-lambda", "(fn [x] (Some x))");
    assert_lambda_constructor_control(&control, "test");

    let subject = fixture_for_rechecked_constructor_value("timeout", "Some");
    assert_bare_constructor_instance_and_carrier(&subject, "test", "timeout");
}

// spec: design/typecheck/monomorphisation.md §11.8; sprints/s121-timeout-intake.md —
// rechecking an imported constructor template must retain its defining home for
// minting while the concrete value carrier names the distinct caller module.
#[test]
fn rechecked_imported_constructor_value_mints_and_carries_in_the_caller_module() {
    let control = fixture_for_rechecked_imported_constructor_value(
        "timeout-lambda",
        "(fn [x] (Some x))",
    );
    assert_lambda_constructor_control(&control, "caller");

    let subject = fixture_for_rechecked_imported_constructor_value("timeout", "Some");
    assert_bare_constructor_instance_and_carrier(&subject, "caller", "timeout");
}

fn fixture_for_rechecked_constructor_value(
    caller: &str,
    mapper: &str,
) -> crate::checker::TestFixture {
    let mut tc = tc_with_prims();
    let source = format!(
        "(deftype (Option a) (Some [:a value]))\n\
         (defn map-value [f value] (f value))\n\
         (defn {caller} [value] (map-value {mapper} value))\n\
         (defn use-timeout [] ({caller} 10))"
    );
    check_src(&mut tc, &source);
    tc
}

fn fixture_for_rechecked_imported_constructor_value(
    caller_name: &str,
    mapper: &str,
) -> crate::checker::TestFixture {
    let mut tc = tc_with_prims();
    let template_home = ModuleFullPath::from("template-home");
    let caller = ModuleFullPath::from("caller");
    tc.set_current_module(template_home.clone());
    check_src(&mut tc, "(deftype (Option a) (Some [:a value]))");

    tc.set_current_module(caller.clone());
    seed_specific_import(&mut tc, &template_home, &["Some"]);
    let source = format!(
        "(defn map-value [f value] (f value))\n\
         (defn {caller_name} [value] (map-value {mapper} value))\n\
         (defn use-timeout [] ({caller_name} 10))"
    );
    check_src(&mut tc, &source);
    tc
}

fn concrete_some_instance(tc: &crate::checker::TestFixture) -> String {
    symbol_names_containing(tc, "Some$Int")
        .into_iter()
        .next()
        .expect("the concrete constructor instance must be registered")
}

fn assert_lambda_constructor_control(tc: &crate::checker::TestFixture, caller_module: &str) {
    let some_instance = concrete_some_instance(tc);
    let caller_instance = symbol_names_containing(tc, "timeout-lambda$Int")
        .into_iter()
        .next()
        .expect("the concrete lambda caller instance must be registered");
    let view = tc
        .symbol_table()
        .get(&caller_instance)
        .and_then(Binding::codegen_view)
        .cloned()
        .expect("the concrete lambda caller instance must retain a codegen view");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        targets.iter().any(|(name, target)| {
            name == "@apply"
                && target.as_ref()
                    == Some(&FQSymbol {
                        module: ModuleFullPath::from(caller_module),
                        symbol: Symbol::from(some_instance.as_str()),
                    })
        }),
        "the lambda control must dispatch its concrete `Some` instance; targets: {targets:?}"
    );
}

fn assert_bare_constructor_instance_and_carrier(
    tc: &crate::checker::TestFixture,
    caller_module: &str,
    caller: &str,
) {
    let some_instance = concrete_some_instance(tc);
    let caller_instance = symbol_names_containing(tc, &format!("{caller}$Int"))
        .into_iter()
        .next()
        .expect("the concrete caller instance must be registered");
    let view = tc
        .symbol_table()
        .get(&caller_instance)
        .and_then(Binding::codegen_view)
        .cloned()
        .expect("the concrete caller instance must retain a codegen view");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        targets.iter().any(|(name, target)| {
            name == "Some"
                && target.as_ref()
                    == Some(&FQSymbol {
                        module: ModuleFullPath::from(caller_module),
                        symbol: Symbol::from(some_instance.as_str()),
                    })
        }),
        "{caller}$Int must carry the caller-local concrete `Some` instance; targets: {targets:?}"
    );
}

// spec: 03-types §3.6.3 — generic positions follow structural occurrence, including HKT heads.
#[test]
fn result_context_canonical_substitution_order_and_replay() {
    let mut tc = tc_with_prims();
    let env = TypeCheckEnv::new(
        &tc.modules,
        &tc.next_id,
        &tc.module_aliases,
        &tc.prelude_fallback,
    );
    let target = CallableTarget::Binding(FQSymbol {
        module: ModuleFullPath::from("test"),
        symbol: Symbol::from("ordered"),
    });
    for (first, second) in [(90, 7), (3, 88)] {
        let scheme = Scheme {
            type_vars: if first < second {
                vec![first, second]
            } else {
                vec![second, first]
            },
            constraints: Default::default(),
            ty: Type::Fn(
                vec![Type::Var(first), Type::Var(first)],
                Box::new(Type::Fn(
                    vec![Type::Var(second)],
                    Box::new(Type::Var(first)),
                )),
            ),
        };
        let use_type = Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Fn(vec![Type::String], Box::new(Type::Int))),
        );
        let demand = env
            .derive_mono_demand(
                &tc.state,
                target.clone(),
                &scheme,
                &use_type,
                Span::SYNTHETIC,
            )
            .unwrap();
        assert_eq!(
            demand.type_args,
            vec![ConcreteType::Int, ConcreteType::String]
        );
        let (reconstructed, _) = env
            .instantiate_and_resolve(&mut tc.state, &scheme, &demand.type_args, Span::SYNTHETIC)
            .unwrap();
        assert_eq!(reconstructed, use_type);
        assert!(
            env.derive_mono_demand(
                &tc.state,
                target.clone(),
                &scheme,
                &scheme.ty,
                Span::SYNTHETIC
            )
            .is_none()
        );
    }
    let scheme = Scheme {
        type_vars: vec![7, 90],
        constraints: Default::default(),
        ty: Type::Fn(
            vec![Type::TyConApp(90, vec![Type::Var(7)])],
            Box::new(Type::Var(7)),
        ),
    };
    let use_type = Type::Fn(
        vec![Type::ADT(test_fqtn("Vec"), vec![Type::String])],
        Box::new(Type::String),
    );
    let demand = env
        .derive_mono_demand(&tc.state, target, &scheme, &use_type, Span::SYNTHETIC)
        .unwrap();
    assert_eq!(
        demand.type_args,
        vec![
            ConcreteType::from_type(&Type::ADT(test_fqtn("Vec"), vec![])).unwrap(),
            ConcreteType::String
        ]
    );
    assert_eq!(
        env.instantiate_and_resolve(&mut tc.state, &scheme, &demand.type_args, Span::SYNTHETIC)
            .unwrap()
            .0,
        use_type
    );
}
