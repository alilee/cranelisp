use crate::test_support::*;
use cranelisp_types::{CallableOrigin, FQTypeName, ModeSummary, Realization, ResultMode, Scheme};

fn var(name: &str, ty: Type, start: u32) -> Expr {
    Expr::Var {
        name: name.into(),
        span: Span::new(start, start + 1),
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

fn defn(name: &str, body: Expr) -> Defn {
    Defn {
        name: name.into(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![("p".into(), None)],
            body,
            span: Span::new(0, 100),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 100),
    }
}

fn forwarded_result_clif(mode: ResultMode, raw_binding_arm: bool) -> String {
    forwarded_result_clif_declaring(mode, raw_binding_arm, None)
}

/// Compile `forward`, which calls `helper`, and return `forward`'s CLIF.
///
/// `mode` is the summary installed on the CALLEE (`helper`) and selects the
/// fixture's body/type shape. `wrapper_result` is the summary the COMPILED
/// function carries — `None` reproduces the Decision-24 absent-summary point.
/// The two are separate because they feed different seams: the caller reads the
/// callee's `param_modes` and realization, never its `result`, while
/// `return_is_fresh_by_summary` reads the compiled function's own `result` and
/// nothing else.
fn forwarded_result_clif_declaring(
    mode: ResultMode,
    raw_binding_arm: bool,
    wrapper_result: Option<ResultMode>,
) -> String {
    let module = ModuleFullPath::from("user");
    let (param_ty, result_ty, helper_body) = match mode {
        ResultMode::Fresh => {
            let option = FQTypeName::new("primitives".into(), "Option".into());
            let result = Type::ADT(option.clone(), vec![Type::String]);
            (
                Type::String,
                result.clone(),
                Expr::ConstrADT {
                    type_name: option,
                    tag: 1,
                    fields: vec![Expr::StringLit {
                        value: "fresh".into(),
                        span: Span::new(5, 12),
                        inferred_type: Some(Box::new(Type::String)),
                    }],
                    span: Span::new(4, 13),
                    inferred_type: Some(Box::new(result)),
                },
            )
        }
        ResultMode::ProjectionOf(_) => {
            let vec_string = Type::adt("primitives".into(), "Vec".into(), vec![Type::String]);
            let body = Expr::Apply {
                callee: Box::new(var(
                    "vec-get",
                    Type::Fn(vec![vec_string.clone(), Type::Int], Box::new(Type::String)),
                    4,
                )),
                args: vec![
                    var("p", vec_string.clone(), 5),
                    Expr::IntLit {
                        value: 0,
                        span: Span::new(6, 7),
                        inferred_type: Some(Box::new(Type::Int)),
                    },
                ],
                span: Span::new(3, 8),
                resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::BuiltinFn {
                    name: "vec-get".into(),
                })),
                inferred_type: Some(Box::new(Type::String)),
            };
            (vec_string, Type::String, body)
        }
        // `MayAliasAny` is the S121 result ⊤ and shares the forwarding shape:
        // a helper whose result reaches a parameter. It is stated as its own
        // pattern rather than folded into a wildcard because the caller seam
        // does not read a callee's `result` at all — the only consumer of that
        // field is `return_is_fresh_by_summary`, on the compiled function's OWN
        // summary, which is what `result_top_summary_keeps_the_return_protect`
        // drives.
        ResultMode::AliasOf(_) | ResultMode::MayAliasOf(_) | ResultMode::MayAliasAny => {
            (Type::String, Type::String, var("p", Type::String, 5))
        }
    };
    let helper = defn("helper", helper_body);
    let call = Expr::Apply {
        callee: Box::new(var(
            "helper",
            Type::Fn(vec![param_ty.clone()], Box::new(result_ty.clone())),
            21,
        )),
        args: vec![var("p", param_ty.clone(), 22)],
        span: Span::new(20, 25),
        resolved_call: None,
        inferred_type: Some(Box::new(result_ty.clone())),
    };
    let body = if raw_binding_arm {
        Expr::If {
            cond: Box::new(var("choose", Type::Bool, 15)),
            then_branch: Box::new(call),
            else_branch: Box::new(var("p", result_ty.clone(), 30)),
            span: Span::new(14, 32),
            inferred_type: Some(Box::new(result_ty.clone())),
        }
    } else {
        call
    };
    let mut wrapper = defn("forward", body);
    let mut wrapper_params = vec![param_ty.clone()];
    if raw_binding_arm {
        wrapper.variants[0].params.push(("choose".into(), None));
        wrapper_params.push(Type::Bool);
    }
    let tables = empty_tables();
    let mut table = SymbolTable::new(module.clone());
    let mut view = test_codegen_view(&helper.name, &helper.variants[0], &HashMap::new());
    view.mode_summary = Some(ModeSummary {
        result: mode,
        ..ModeSummary::default()
    });
    table
        .install_concrete(
            helper.name.clone(),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![param_ty.clone()], Box::new(result_ty.clone())),
            },
            vec!["p".into()],
            None,
            0,
            CallableOrigin::Plain,
            Realization::Body { view, code: None },
            Some(helper.variants[0].clone()),
            vec![],
            Visibility::Public,
        )
        .unwrap();
    insert_user_fn_stub_typed(&mut table, "forward", &wrapper_params, result_ty);
    tables.insert(module.clone(), table);
    let targets = call_carriers(wrapper.body(), &module, &["helper"]);
    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let summaries = [wrapper_result.map(|result| ModeSummary {
        result,
        ..ModeSummary::default()
    })];
    try_compile_defns_in_module(
        &[&wrapper],
        &summaries,
        &[],
        &targets,
        &tables,
        module,
        jit.jit_module(),
    )
    .expect("probe: forward compiles")
    .into_iter()
    .next()
    .expect("probe: one compiled defn")
}

/// Whether the function's tail keeps a return-protect retain after the call.
fn retains_after_helper_call(clif: &str) -> bool {
    after_helper_call(clif)
        .lines()
        .any(|line| line.contains("atomic_rmw") && line.contains("add"))
}

fn after_helper_call(clif: &str) -> &str {
    let call = clif
        .lines()
        .find(|line| line.contains("call_indirect"))
        .unwrap();
    let parameter = call.rsplit_once('(').unwrap().1.trim_end_matches(')');
    let (_, tail) = clif
        .split_once("call_indirect")
        .expect("actual callable result");
    assert!(
        tail.lines()
            .any(|line| line.contains("call fn") && line.contains(&format!("({parameter})"))),
        "parameter cleanup must remain after the call:\n{clif}"
    );
    tail
}

// spec: spec/12-runtime.md §12.3.1; tests/plan/s121-test-plan.md §14.1
#[test]
fn forwarded_callable_result_transfers_without_duplicate_retain() {
    for mode in [
        ResultMode::Fresh,
        ResultMode::AliasOf(0),
        ResultMode::ProjectionOf(0),
        ResultMode::MayAliasOf(0),
        ResultMode::MayAliasAny,
    ] {
        let clif = forwarded_result_clif(mode, false);
        let tail = after_helper_call(&clif);
        let result = clif
            .lines()
            .find(|line| line.contains("call_indirect"))
            .unwrap()
            .trim()
            .split_once(" = ")
            .unwrap()
            .0;
        assert!(
            tail.lines()
                .any(|line| line.trim() == format!("return {result}")),
            "forward the actual call result:\n{clif}"
        );
        assert!(
            !tail
                .lines()
                .any(|line| line.contains("atomic_rmw") && line.contains("add")),
            "{mode:?}: owned callable result must not be retained again:\n{clif}"
        );
    }
}

// spec: spec/12-runtime.md §12.3.1 — one borrowed arm cannot transfer an owned result.
#[test]
fn mixed_callable_and_scope_binding_return_keeps_protection() {
    let clif = forwarded_result_clif(ResultMode::AliasOf(0), true);
    assert!(
        retains_after_helper_call(&clif),
        "scope-binding arm still needs protection:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.3.1; design/typecheck/ownership-inference.md §19.2
// — `MayAliasAny` is the S121 result ⊤, and the ONE backend consumer of the
// `result` field is `return_is_fresh_by_summary`, a silent `== Fresh` binary
// read that a variant addition does NOT force to be revisited (the standing
// escape grep names it). So the ⊤ landing on the protect-KEPT side has to be
// measured, not inspected: the same fixture is compiled twice, differing only
// in the point its own summary declares.
//
// The `Fresh` leg is the discriminating control. It is what makes the ⊤ leg
// non-vacuous — without it a dead protect path would satisfy the assertion —
// and it pins the contract as written: the backend TRUSTS a present `Fresh` and
// elides on it for any body shape (`fn_compiler::return_protect_tests::
// fresh_summary_elides_all_body_shapes`). That a body returning its own
// parameter must never be *published* as `Fresh` is the producer's obligation
// (§19.1's F-2, the defect this wave corrects), not a second gate here.
#[test]
fn result_top_summary_keeps_the_return_protect() {
    let top = forwarded_result_clif_declaring(
        ResultMode::AliasOf(0),
        true,
        Some(ResultMode::MayAliasAny),
    );
    assert!(
        retains_after_helper_call(&top),
        "a declared MayAliasAny result is not Fresh and must keep the return protect:\n{top}"
    );
    let fresh =
        forwarded_result_clif_declaring(ResultMode::AliasOf(0), true, Some(ResultMode::Fresh));
    assert!(
        !retains_after_helper_call(&fresh),
        "control: the elision is keyed on the declared point, and only Fresh elides:\n{fresh}"
    );
}
