use super::*;

pub(super) fn assert_instance_references(tc: &TestFixture, caller: &str, expected: &[Symbol]) {
    let view = main_codegen_view_of(tc, caller);
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    for key in expected {
        let references = targets
            .iter()
            .filter(|(_, target)| {
                target.as_ref().is_some_and(|target| {
                    target.module == tc.state.current_module && target.symbol == *key
                })
            })
            .count();
        assert_eq!(
            references, 1,
            "{caller} must reference {key} exactly once: {targets:?}"
        );
    }
}

fn assert_instance(
    tc: &TestFixture,
    target: CallableTarget,
    type_args: Vec<Type>,
    signature: Type,
    expected_key: &str,
) -> Symbol {
    let (owner, template_scheme) = match &target {
        CallableTarget::Binding(owner) => {
            let table = tc.modules.get(&owner.module).expect("template home exists");
            let scheme = table
                .get(owner.symbol.as_ref())
                .and_then(Binding::callable)
                .map(|callable| callable.arm.scheme.clone())
                .expect("binding template has a scheme");
            (owner.clone(), scheme)
        }
        CallableTarget::OverloadArm { owner, arm } => {
            let table = tc.modules.get(&owner.module).expect("template home exists");
            let scheme = match &table
                .get(owner.symbol.as_ref())
                .expect("overload family exists")
                .declaration
            {
                Decl::Overloaded(declaration) => {
                    declaration.arms[arm.ordinal()].callable.scheme.clone()
                }
                other => panic!("expected overload family, got {other:?}"),
            };
            (owner.clone(), scheme)
        }
        other => panic!("unsupported result-context template {other:?}"),
    };
    let link = cranelisp_types::InstanceLink::from_type_args(
        target,
        type_args
            .iter()
            .map(|ty| ConcreteType::from_type(ty).unwrap())
            .collect(),
    );
    let key = link.instance_key(&template_scheme).unwrap();
    let signature_key = cranelisp_types::concrete_callable_key(
        &owner,
        &ConcreteType::from_type(&signature).unwrap(),
    )
    .unwrap();
    assert_eq!(key, signature_key);
    assert_eq!(key.as_ref(), expected_key);
    let table = tc.symbol_table();
    let entry = table
        .get(&key)
        .unwrap_or_else(|| panic!("missing instance {key}"));
    let callable = entry.callable().unwrap();
    assert_eq!(callable.arm.scheme.ty, signature);
    assert!(
        matches!(&callable.arm.life, Life::Concrete { minted_from: Some(actual), .. } if actual == &link)
    );
    assert!(entry.callable_got_slot().is_some());
    assert!(entry.codegen_view().is_some());
    key
}

fn fn_type(params: Vec<Type>, ret: Type) -> Type {
    Type::Fn(params, Box::new(ret))
}

// spec: 03-types §3.6.3 — value arguments and result-only choices jointly specialize a template.
#[test]
fn result_context_nonzero_argument_closure_and_container() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn constf [x] (fn [y] x)) (defn empty [x] []) (defn main [] (add-i64 ((constf 100) 5) ((constf 100) \"heap\"))) (defn ints [] :(Vec Int) (empty 0))",
    );
    let mut keys = Vec::new();
    for result_arg in [Type::Int, Type::String] {
        let rendered = if result_arg == Type::Int {
            "primitives/Int"
        } else {
            "primitives/String"
        };
        keys.push(assert_instance(
            &tc,
            CallableTarget::Binding(fq_sym("test", "constf")),
            vec![Type::Int, result_arg.clone()],
            fn_type(vec![Type::Int], fn_type(vec![result_arg], Type::Int)),
            &format!("(test/constf [primitives/Int] (Fn [{rendered}] primitives/Int))"),
        ));
    }
    assert_instance_references(&tc, "main", &keys);
    let empty_key = assert_instance(
        &tc,
        CallableTarget::Binding(fq_sym("test", "empty")),
        vec![Type::Int, Type::Int],
        fn_type(
            vec![Type::Int],
            Type::ADT(
                cranelisp_types::FQTypeName {
                    module: ModuleFullPath::from("primitives"),
                    name: TypeName::from("Vec"),
                },
                vec![Type::Int],
            ),
        ),
        "(test/empty [primitives/Int] (primitives/Vec primitives/Int))",
    );
    assert_instance_references(&tc, "ints", &[empty_key]);
}

// spec: 03-types §3.6.3 — a function value retains its entire function result.
#[test]
fn result_context_function_value_preserves_result() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn g [] (fn [y] 100)) (defn invoke [factory x] ((factory) x)) (defn main [] (add-i64 (invoke g 5) (invoke g \"heap\")))",
    );
    let mut keys = Vec::new();
    for ty in [Type::Int, Type::String] {
        let rendered = if ty == Type::Int {
            "primitives/Int"
        } else {
            "primitives/String"
        };
        keys.push(assert_instance(
            &tc,
            CallableTarget::Binding(fq_sym("test", "g")),
            vec![ty.clone()],
            fn_type(vec![], fn_type(vec![ty], Type::Int)),
            &format!("(test/g [] (Fn [{rendered}] primitives/Int))"),
        ));
    }
    assert_instance_references(&tc, "main", &keys);
}

// spec: 03-types §3.6.3 / 05-definitions §5.2 — partial application separates residual arity from a returned closure.
#[test]
fn result_context_auto_curry_preserves_final_return() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn build [x z] (fn [y] x)) (defn main [] (let [p (build 100)] ((p 0) \"heap\")))",
    );
    let key = assert_instance(
        &tc,
        CallableTarget::Binding(fq_sym("test", "build")),
        vec![Type::Int, Type::Int, Type::String],
        fn_type(
            vec![Type::Int, Type::Int],
            fn_type(vec![Type::String], Type::Int),
        ),
        "(test/build [primitives/Int primitives/Int] (Fn [primitives/String] primitives/Int))",
    );
    assert_instance_references(&tc, "main", &[key]);
}

// spec: 03-types §3.6.3 / 05-definitions §5.1.2 — a selected overload arm owns the complete substitution.
#[test]
fn result_context_selected_overload_arm() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn g ([] (fn [y] 100)) ([x] x)) (defn main [] (add-i64 ((g) 5) ((g) \"heap\")))",
    );
    let mut keys = Vec::new();
    for ty in [Type::Int, Type::String] {
        let rendered = if ty == Type::Int {
            "primitives/Int"
        } else {
            "primitives/String"
        };
        keys.push(assert_instance(
            &tc,
            CallableTarget::OverloadArm {
                owner: fq_sym("test", "g"),
                arm: cranelisp_types::CallableArmId::from_ordinal(0).unwrap(),
            },
            vec![ty.clone()],
            fn_type(vec![], fn_type(vec![ty], Type::Int)),
            &format!("(test/g [] (Fn [{rendered}] primitives/Int))"),
        ));
    }
    assert_instance_references(&tc, "main", &keys);
}

// spec: 03-types §3.6.3 / 08-modules §8.6 — nested imported rechecks use their own result map and defining scope.
#[test]
fn result_context_imported_nested_hops() {
    let mut tc = tc_with_prims();
    tc.set_current_module(ModuleFullPath::from("hop"));
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(&mut tc, "(defn g [] (fn [y] 100)) (defn h [] (g))");
    tc.set_current_module(ModuleFullPath::from("caller"));
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    seed_specific_import(&mut tc, &ModuleFullPath::from("hop"), &["h"]);
    check_src(&mut tc, "(defn main [] (add-i64 ((h) 5) ((h) \"heap\")))");
    let mut outer_keys = Vec::new();
    for ty in [Type::Int, Type::String] {
        let rendered = if ty == Type::Int {
            "primitives/Int"
        } else {
            "primitives/String"
        };
        let mut keys = Vec::new();
        for name in ["g", "h"] {
            keys.push(assert_instance(
                &tc,
                CallableTarget::Binding(fq_sym("hop", name)),
                vec![ty.clone()],
                fn_type(vec![], fn_type(vec![ty.clone()], Type::Int)),
                &format!("(hop/{name} [] (Fn [{rendered}] primitives/Int))"),
            ));
        }
        assert_instance_references(&tc, keys[1].as_ref(), &keys[..1]);
        outer_keys.push(keys[1].clone());
    }
    assert_instance_references(&tc, "main", &outer_keys);
}
