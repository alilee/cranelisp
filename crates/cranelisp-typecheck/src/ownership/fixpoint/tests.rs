//! CS-3 Principle-23 matrices for `fixpoint.rs`
//! (`design/typecheck/ownership-inference.md` §13.7 `fixpoint.rs` block):
//! SCC-shape, ordering/determinism, re-entry, and boundary-condition negatives.
//!
//! Driven through `compute_cluster` with hand-built `Callable`s whose bodies
//! reference each other via `SigDispatch` (⇒ in-cluster `working`-map lookups),
//! so the fixpoint logic is exercised without a full symbol-table fixture. A
//! `TestFixture` env supplies the (here unused) chain-follow fallback.

use cranelisp_types::{
    CallableTarget, ConcreteType, FQSymbol, FQTypeName, Mode, ModuleFullPath, MonoExpr, Span,
    Symbol, TypeName,
};

use crate::checker::test_support::TestFixture;
use crate::program::test_support::{check_src, tc_with_prims};

use super::*;

fn s() -> Span {
    Span::SYNTHETIC
}
fn var(n: &str) -> MonoExpr {
    MonoExpr::Var {
        name: Symbol::from(n),
        span: s(),
        resolved_call: None,
        ty: ConcreteType::String,
        resolution: cranelisp_types::VarRef::Local {
            binder: Symbol::from(n),
            binding_span: cranelisp_types::Span::SYNTHETIC,
        },
    }
}
fn call(name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(name)),
        args,
        span: s(),
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::SigDispatch {
            target: CallableTarget::Binding(FQSymbol {
                module: ModuleFullPath::from("user"),
                symbol: Symbol::from(name),
            }),
        })),
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}
/// `(Box field...)` returned — a fresh ADT embedding its fields.
fn boxed(fields: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
        tag: 0,
        fields,
        span: s(),
        ty: ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
            vec![],
        ),
        escapes: None,
        confined: None,
        unique_static: None,
    }
}
fn callable(key: &str, params: Vec<&str>, body: MonoExpr) -> Callable {
    Callable {
        key: Symbol::from(key),
        params: params
            .into_iter()
            .map(|n| (Symbol::from(n), ConcreteType::String))
            .collect(),
        body,
        residual_params: false,
    }
}
fn run(universe: Vec<Callable>) -> ClusterOwnership {
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    compute_cluster(&tf.env(), &module, &universe)
}
fn mode(c: &ClusterOwnership, key: &str, i: usize) -> Mode {
    c.summaries[&Symbol::from(key)].param_mode(i)
}

fn register_layout_type(env: &TypeCheckEnv, module: &str, name: &str, field: FQTypeName) {
    let mut state = CheckState::new(ModuleFullPath::from(module));
    env.register_type_def(
        &mut state,
        &TypeName::from(name),
        &None,
        &[],
        &[cranelisp_types::ConstructorDef {
            name: Symbol::from("Wrap"),
            docstring: None,
            fields: vec![cranelisp_types::FieldDef {
                name: Symbol::from("value"),
                type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                    Some(field.module),
                    field.name,
                )),
                span: s(),
            }],
            span: s(),
        }],
        cranelisp_types::Visibility::Public,
        s(),
    )
    .unwrap();
}

fn staged_layout_cases(mut observe: impl FnMut(&TypeCheckEnv, &ConcreteType, bool)) {
    let fq = |module: &str, name: &str| {
        FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name))
    };
    for (published, staged, copy) in [
        (None, Some("Int"), true),
        (Some("String"), Some("Int"), true),
        (Some("Int"), Some("String"), false),
        (Some("Int"), None, true),
    ] {
        let tf = TestFixture::with_content(
            crate::builtins::FixtureBuilder::new().with_builtin_type_names(),
        );
        if let Some(field) = published {
            register_layout_type(&tf.env(), "user", "Customer", fq("primitives", field));
        }
        let mut staging = cranelisp_types::SymbolTable::new(ModuleFullPath::from("user"));
        let cell = std::cell::RefCell::new(&mut staging);
        let lookup_dependencies = crate::checker::LookupDependencyCollector::default();
        let env = TypeCheckEnv::new_with_staging(
            &tf.modules,
            &tf.next_id,
            ModuleFullPath::from("user"),
            &cell,
            &lookup_dependencies,
            &tf.module_aliases,
            &tf.prelude_fallback,
        );
        if let Some(field) = staged {
            register_layout_type(&env, "user", "Customer", fq("primitives", field));
        }
        observe(
            &env,
            &ConcreteType::ADT(fq("user", "Customer"), vec![]),
            copy,
        );
    }

    let tf =
        TestFixture::with_content(crate::builtins::FixtureBuilder::new().with_builtin_type_names());
    tf.env()
        .ensure_module_exists(&ModuleFullPath::from("other"));
    register_layout_type(&tf.env(), "other", "Inner", fq("primitives", "Int"));
    let mut staging = cranelisp_types::SymbolTable::new(ModuleFullPath::from("user"));
    let cell = std::cell::RefCell::new(&mut staging);
    let lookup_dependencies = crate::checker::LookupDependencyCollector::default();
    let env = TypeCheckEnv::new_with_staging(
        &tf.modules,
        &tf.next_id,
        ModuleFullPath::from("user"),
        &cell,
        &lookup_dependencies,
        &tf.module_aliases,
        &tf.prelude_fallback,
    );
    register_layout_type(&env, "user", "Outer", fq("other", "Inner"));
    observe(&env, &ConcreteType::ADT(fq("user", "Outer"), vec![]), true);
}

// spec: design/typecheck/ownership-inference.md §14.5 — Copy uses the checked
// declaration view, including staged precedence and published-key fallback.
#[test]
fn copy_layout_uses_staged_declarations() {
    staged_layout_cases(|env, ty, copy| {
        let mut subject = callable("subject", vec![], var("unused"));
        subject.params = vec![(Symbol::from("p"), ty.clone())];
        subject.body = MonoExpr::IntLit {
            value: 0,
            span: s(),
            ty: ConcreteType::Int,
        };
        let result = compute_cluster(env, &ModuleFullPath::from("user"), &[subject]);
        assert_eq!(
            mode(&result, "subject", 0),
            if copy { Mode::Copy } else { Mode::Borrowed }
        );
    });
}

// spec: design/typecheck/ownership-inference.md §14.2, §14.5 — reuse requires a
// String/ADT heap slot; a staged value layout excludes reuse.
#[test]
fn uniqueness_layout_uses_staged_declarations() {
    use super::super::uniqueness::UniqEnv;

    staged_layout_cases(|env, ty, copy| {
        let uenv = UniqClusterEnv {
            env,
            current_module: ModuleFullPath::from("user"),
            summaries: &HashMap::new(),
            members: &HashSet::new(),
            working_unique: &HashMap::new(),
        };
        assert_eq!(uenv.layout_eligible(ty), !copy);
        assert!(uenv.layout_eligible(&ConcreteType::String));
        for excluded in [
            ConcreteType::Int,
            ConcreteType::Bool,
            ConcreteType::Float,
            ConcreteType::Fn(vec![], Box::new(ConcreteType::Int)),
        ] {
            assert!(!uenv.layout_eligible(&excluded));
        }
    });
}

// =================== SCC-shape matrix ===================

#[test]
fn straight_chain_propagates_owned_callee_to_caller() {
    // spec: §3.2 — a straight chain converges in reverse-topo; the Owned callee
    // widens the caller's forwarded param.
    // sink(y) = (Box y)  ⇒ y Owned; caller(x) = (sink x) ⇒ x Owned.
    let uni = vec![
        callable("sink", vec!["y"], boxed(vec![var("y")])),
        callable("caller", vec!["x"], call("sink", vec![var("x")])),
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "sink", 0), Mode::Owned);
    assert_eq!(mode(&c, "caller", 0), Mode::Owned);
}

#[test]
fn self_recursive_borrowed_converges() {
    // spec: §3.2 — a self-recursive fn whose only use is a borrowed self-handoff
    // stays Borrowed (≤2 visits).
    // f(p) = (f p)  — p forwarded to f (in-cluster, Borrowed handoff).
    let uni = vec![callable("f", vec!["p"], call("f", vec![var("p")]))];
    let c = run(uni);
    assert_eq!(mode(&c, "f", 0), Mode::Borrowed);
}

fn assert_cow_escape_convergence(tail: &str) {
    let mut tf = tc_with_prims();
    let source = format!(
        "(deftype (Option a) None (Some [:a value]))
        (deftype Grid [:(Vec Int) cells])
        (defn boxed [n xs]
          (if (eq-i64 n 0) (Some (Grid xs))
            {tail}))"
    );
    check_src(&mut tf, &source);
    let env = tf.env();
    let mut universe = collect_universe(&env, &tf.state);
    universe.sort_by(|a, b| a.key.as_ref().cmp(b.key.as_ref()));
    let first = compute_cluster(&env, &tf.state.current_module, &universe);
    universe.reverse();
    let second = compute_cluster(&env, &tf.state.current_module, &universe);
    let start = source.find("(vec-push xs 1)").unwrap() as u32;
    let cow_span = Span::new(start, start + "(vec-push xs 1)".len() as u32);
    let key = Symbol::from("boxed");
    let callable = universe.iter().find(|c| c.key == key).unwrap();
    let copy = CopyClassifier::new(|ty| checked_value_layout(&env, ty).is_some());
    assert_eq!(
        universe.len(),
        2,
        "boxed and its specialized Some constructor"
    );
    assert_eq!(first.summaries, second.summaries);
    for (order, result) in [("sorted", &first), ("reversed", &second)] {
        let final_env = ClusterEnv {
            env: &env,
            current_module: tf.state.current_module.clone(),
            working: &result.summaries,
            members: &universe.iter().map(|c| c.key.clone()).collect(),
        };
        let settled = transfer(&callable.params, &callable.body, &final_env, &copy);
        assert_eq!(settled.facts.escapes.get(&cow_span), Some(&true));
        assert_eq!(
            result.summaries[&key].param_modes,
            settled.summary.param_modes
        );
        assert_eq!(
            result.summaries[&key].param_flow,
            settled.summary.param_flow
        );
        assert_eq!(result.summaries[&key].result, settled.summary.result);
        assert_eq!(
            result.facts[&key].escapes.get(&cow_span),
            Some(&true),
            "{order}: COW escape must use final recursive summary"
        );
        assert_eq!(result.facts[&key].escapes, settled.facts.escapes, "{order}");
    }
    assert_eq!(first.facts[&key].escapes, second.facts[&key].escapes);
}

// spec: spec/12-runtime.md §12.3.1; design/typecheck/ownership-inference.md
// §3.2 — recursive site facts must agree with the converged callee summaries.
#[test]
fn recursive_cow_escape_facts_converge_independently_of_universe_order() {
    assert_cow_escape_convergence("(boxed (sub-i64 n 1) (vec-push xs 1))");
}

// spec: design/typecheck/ownership-inference.md §3.2 — ordinary callee re-entry
// converges the same owning result without a recursive dependency.
#[test]
fn nonrecursive_cow_escape_facts_converge_independently_of_universe_order() {
    assert_cow_escape_convergence("(Some (Grid (vec-push xs 1)))");
}

#[test]
fn mutual_two_cycle_converges() {
    // spec: §3.2 — a mutual 2-cycle of pass-through calls converges (both Borrowed).
    let uni = vec![
        callable("a", vec!["p"], call("b", vec![var("p")])),
        callable("b", vec!["q"], call("a", vec![var("q")])),
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "a", 0), Mode::Borrowed);
    assert_eq!(mode(&c, "b", 0), Mode::Borrowed);
}

#[test]
fn recursive_owned_cycle_widens_both() {
    // spec: §3.2 — a cycle where one member consumes its param widens through
    // the cycle (monotone).
    // a(p) = (b p); b(q) = (Box (a q))  — b consumes via a's forwarded Owned.
    let uni = vec![
        callable("a", vec!["p"], boxed(vec![var("p")])), // a consumes p (Owned)
        callable("b", vec!["q"], call("a", vec![var("q")])), // b forwards q to a (Owned)
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "a", 0), Mode::Owned);
    assert_eq!(mode(&c, "b", 0), Mode::Owned);
}

#[test]
fn tail_recursion_base_returns_param_is_alias_not_fresh() {
    // spec: §4.2 (FIXME 0520) — the `build` repro (04_vec_cow_loop), driver
    // grain. `(defn build [v i n] (if c v (build (grow v) i n)))`: the base case
    // returns param `v`, the recursive case returns a fresh-derived vec. Pre-cure
    // the partial-if join collapsed build's result to `Fresh` DESPITE the
    // base-case param return — an ABI-half soundness narrowing (a consumer
    // trusting Fresh frees the returned param → the observed SIGABRT). Truth:
    // may-alias param 0 ⇒ MayAliasOf(0) (S111 §3.7/§15.3 — a may-origin publishes
    // MayAliasOf, keeping protect; AliasOf is reserved for unconditional claims).
    // `grow` is a boundary leaf (⊤: Owned/Fresh), so the recursive arg is fresh —
    // exactly the vec-push COW shape.
    let cond = MonoExpr::BoolLit {
        value: true,
        span: s(),
        ty: ConcreteType::Bool,
    };
    let recursive = call(
        "build",
        vec![call("grow", vec![var("v")]), var("i"), var("n")],
    );
    let body = MonoExpr::If {
        cond: Box::new(cond),
        then_branch: Box::new(var("v")),
        else_branch: Box::new(recursive),
        span: s(),
        ty: ConcreteType::String,
    };
    let uni = vec![callable("build", vec!["v", "i", "n"], body)];
    let c = run(uni);
    let build = &c.summaries[&Symbol::from("build")];
    assert_eq!(
        build.result,
        cranelisp_types::ResultMode::MayAliasOf(0),
        "build returns param v in the base case ⇒ MayAliasOf(0), never Fresh"
    );
    // v is returned (IntoResult) ⇒ Owned; the ABI param half was already correct.
    assert_eq!(
        mode(&c, "build", 0),
        Mode::Owned,
        "the returned param v is Owned"
    );
}

// =================== Reachability (the a3 leg, S111 §15.2) ===================

// spec: design/typecheck/ownership-inference.md §15.2 (spine §3.7(a3)) — the
// ownership envs must reach a declared leaf's facts through the implicit prelude
// fallback. A `vec-set`-shaped `MayAliasOf(0)` primitive PUBLIC in the `prelude`
// module must be found by the scoped resolver from a prelude-fallback `user`
// module — else a2's truthful declaration is dead code and results default to
// the false `Fresh` (the vec-assoc UAF root). The raw fallback-less resolver
// missed exactly this hop.
#[test]
fn declared_facts_reachable_through_prelude_fallback() {
    let tf = TestFixture::new();
    let prelude = ModuleFullPath::from("prelude");
    let user = ModuleFullPath::from("user");
    let scheme = cranelisp_types::Scheme {
        type_vars: vec![],
        constraints: Default::default(),
        ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
    };
    let mut pt = cranelisp_types::SymbolTable::<()>::new(prelude.clone());
    let install = |table: &mut cranelisp_types::SymbolTable, name: &str, vis| {
        let view = cranelisp_types::MonoDefnVariant {
            name: Symbol::from(name),
            params: vec![Symbol::from("x")],
            body: var("x"),
            span: s(),
            mode_summary: None,
        };
        table
            .install_concrete(
                Symbol::from(name),
                scheme.clone(),
                vec![Symbol::from("x")],
                None,
                0,
                cranelisp_types::CallableOrigin::Plain,
                cranelisp_types::Realization::Body {
                    view: view.clone(),
                    code: None,
                },
                None,
                vec![],
                vis,
            )
            .unwrap();
        table
            .publish_body_ownership(
                &CallableTarget::Binding(FQSymbol {
                    module: ModuleFullPath::from("prelude"),
                    symbol: Symbol::from(name),
                }),
                ModeSummary {
                    result: cranelisp_types::ResultMode::MayAliasOf(0),
                    ..Default::default()
                },
                view,
            )
            .unwrap();
    };
    install(&mut pt, "cow-op", cranelisp_types::Visibility::Public);
    // A PRIVATE prelude entry — the I-1 filter must NOT leak it.
    install(
        &mut pt,
        "cow-op-private",
        cranelisp_types::Visibility::Private,
    );
    tf.modules.insert(prelude.clone(), pt);
    tf.prelude_fallback.insert(user.clone(), true);

    // Positive: the PUBLIC declared fact is reachable via the prelude hop.
    let found = tf
        .env()
        .resolve_terminal_entry_and_home_scoped(&user, "cow-op");
    let (entry, home) = found.expect("public prelude declared fact must be reachable via fallback");
    assert_eq!(home, prelude);
    assert_eq!(
        entry.mode_summary().map(|s| s.result),
        Some(cranelisp_types::ResultMode::MayAliasOf(0)),
        "the resolved entry carries the declared MayAliasOf(0) fact"
    );
    // Negative: a PRIVATE prelude binding is NOT resolved (I-1 filter honoured).
    assert!(
        tf.env()
            .resolve_terminal_entry_and_home_scoped(&user, "cow-op-private")
            .is_none(),
        "a private prelude entry must not leak through the fallback (I-1)"
    );
}

// =================== Ordering / determinism ===================

#[test]
fn scrambled_seed_order_converges_identically() {
    // spec: §13.3 — seed order is a hint only; scrambled order ⇒ identical result.
    let mk = || {
        vec![
            callable("sink", vec!["y"], boxed(vec![var("y")])),
            callable("caller", vec!["x"], call("sink", vec![var("x")])),
        ]
    };
    let c1 = run(mk());
    let mut rev = mk();
    rev.reverse();
    let c2 = run(rev);
    assert_eq!(c1.summaries, c2.summaries);
}

// =================== Re-entry / boundary ===================

#[test]
fn absent_boundary_callee_reads_top() {
    // spec: §13.3 gap 4 — a callee absent from the cluster and unresolvable is a
    // boundary condition read as ⊤ (Owned/Retained) — never enqueued.
    // caller(x) = (external x)  where `external` is not in the universe.
    let uni = vec![callable(
        "caller",
        vec!["x"],
        call("external", vec![var("x")]),
    )];
    let c = run(uni);
    assert_eq!(mode(&c, "caller", 0), Mode::Owned);
    // `external` is not a cluster member ⇒ no summary published for it.
    assert!(!c.summaries.contains_key(&Symbol::from("external")));
}

#[test]
fn value_use_harvested_across_cluster() {
    // spec: §8.3 — a callable referenced in value position is recorded.
    // caller(x) = (sink helper)  — `helper` passed as a value.
    let uni = vec![
        callable("sink", vec!["y"], boxed(vec![var("y")])),
        callable("caller", vec!["x"], call("sink", vec![var("helper")])),
    ];
    let c = run(uni);
    assert!(c.value_used.contains(&Symbol::from("helper")));
}

#[test]
fn every_callable_gets_a_summary() {
    // spec: §13.2 — every codegen-bound callable in the universe is summarised.
    let uni = vec![
        callable("a", vec!["p"], var("p")),
        callable("b", vec!["q"], var("q")),
    ];
    let c = run(uni);
    assert!(c.summaries.contains_key(&Symbol::from("a")));
    assert!(c.summaries.contains_key(&Symbol::from("b")));
}

#[test]
fn mangled_mono_instance_propagates_in_cluster() {
    // spec: §6 / §13.7 (suggestion 5) — a mono instance keyed by its mangled
    // name (`reduce$Int+Int`) referenced via SigDispatch under the SAME mangled
    // name propagates in-cluster (precise), NOT degrading to ⊤. Pins that the
    // SigDispatch target and the universe key are the one mangled `Symbol`.
    let uni = vec![
        callable("reduce$Int+Int", vec!["y"], boxed(vec![var("y")])), // consumes y ⇒ Owned
        callable("caller", vec!["x"], call("reduce$Int+Int", vec![var("x")])),
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "reduce$Int+Int", 0), Mode::Owned);
    // Precise in-cluster propagation: caller's x widens through the mangled edge.
    assert_eq!(mode(&c, "caller", 0), Mode::Owned);
}

// =================== Confinement fixpoint (blocker 2) ===================

/// A ParBind of one binding whose RHS is `(name args…)`, joined into `body`.
fn parbind(binding: &str, rhs: MonoExpr, body: MonoExpr) -> MonoExpr {
    MonoExpr::ParBind {
        bindings: vec![(Symbol::from(binding), rhs)],
        body: Box::new(body),
        span: s(),
        ty: ConcreteType::String,
    }
}

#[test]
fn transitive_spark_ops_propagate_caller_before_callee() {
    // spec: §5.3 / §13.7 — a callee whose spark_ops is set must propagate to a
    // caller LISTED FIRST (processed before the callee). Blocker 2: confinement
    // is a worklist fixpoint, not a single unordered pass. A single pass over
    // `universe` in vec order would process `caller` while `producer.spark_ops`
    // is still the init `false` and never re-run ⇒ caller under-reports Confined.
    // producer(y) sparks y off-strand (ParBind consuming call); caller(x)
    // forwards x to producer on the PARENT strand ⇒ inherits transitively.
    let uni = vec![
        callable("caller", vec!["x"], call("producer", vec![var("x")])),
        callable(
            "producer",
            vec!["y"],
            parbind("r", call("mystery", vec![var("y")]), var("r")),
        ),
    ];
    let c = run(uni);
    assert!(
        c.summaries[&Symbol::from("producer")].spark_op(0),
        "producer sparks y off-strand"
    );
    assert!(
        c.summaries[&Symbol::from("caller")].spark_op(0),
        "caller must inherit producer's spark_ops transitively regardless of order"
    );
}

#[test]
fn confinement_no_spurious_cross_for_parent_only_chain() {
    // spec: §5.3 (negative twin) — a caller→callee chain with NO off-strand op
    // anywhere stays Confined (spark_ops clear). Guards against the fixpoint
    // over-widening every position.
    let uni = vec![
        callable("caller", vec!["x"], call("sink", vec![var("x")])),
        callable("sink", vec!["y"], boxed(vec![var("y")])),
    ];
    let c = run(uni);
    assert!(
        !c.summaries[&Symbol::from("sink")].spark_op(0),
        "sink parent-strand only"
    );
    assert!(
        !c.summaries[&Symbol::from("caller")].spark_op(0),
        "caller parent-strand only"
    );
}

// ============== Cap exhaustion refuses the cluster (§19.5) ==============
//
// The three cells that lived here asserted the pre-S121 recovery: on cap
// exhaustion the driver minted a ⊤ `ModeSummary`, ⊤ site facts and `false`
// uniqueness bits, and PUBLISHED them. That literal was ⊤ on four axes and the
// axis's STRONGEST claim on the fifth (`result: Fresh`), which the backend's
// `return_is_fresh_by_summary` reads to elide the callee return protect on a
// body that does return its parameter. The role those cells guarded — a cap must
// never publish the too-precise partial — is retained here; what changed, by the
// user's approval, is the spelling of the conservative point: from a ⊤ literal to
// ABSENCE (§19.5), which lands the refused cluster on the
// `CRANELISP_NO_OWNERSHIP` shape the differential oracle already measures.

/// The refusal's POSITIVE detection leg: whichever stratum exhausted the shared
/// cap, the whole cluster publishes nothing.
fn assert_refuses_publishing_nothing(c: &ClusterOwnership, key: &str, stratum: Stratum) {
    let r = c.refusal.expect("cap exhaustion must refuse the cluster");
    assert_eq!(r.stratum, stratum, "the exhausted stratum is named");
    assert_eq!(r.visits, r.cap, "the refusal spent its whole budget");
    assert!(
        c.summaries.is_empty(),
        "a refused cluster publishes NO summary; got {:?}",
        c.summaries
    );
    assert!(
        !c.summaries.contains_key(&Symbol::from(key)),
        "including for the callable that was being analysed"
    );
    assert!(
        c.facts.is_empty(),
        "a refused cluster publishes NO site fact"
    );
    assert!(
        c.value_used.is_empty(),
        "a refused cluster publishes NO value-use mark"
    );
}

// spec: design/typecheck/ownership-inference.md §19.5 — a cluster whose analysis
// does not converge publishes no summary, no site fact and no value-use mark.
// spec: spec/12-runtime.md §12.3.1 — freed memory MUST NOT be accessed after
// deallocation (the consequence the retired ⊤ literal carried: a present
// `result: Fresh` for a body that returns its parameter elides the return
// protect).
#[test]
fn cap_exhaustion_refuses_the_cluster_and_publishes_nothing() {
    // The subject is the same self-recursive pass-through the retired cell used
    // (it normally converges to Borrowed — see `self_recursive_borrowed_converges`).
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let uni = vec![callable("f", vec!["p"], call("f", vec![var("p")]))];
    let c = compute_cluster_with_cap(&tf.env(), &module, &uni, 0);
    assert_refuses_publishing_nothing(&c, "f", Stratum::Modes);
}

// spec: design/typecheck/ownership-inference.md §19.5 — the site facts and the
// uniqueness bits go with the summary. A partially-walked callable has no / too-low
// escape entries and a greatest-fixpoint `result_unique` still sitting above its
// true value; neither is salvageable, and neither is published.
#[test]
fn cap_exhaustion_refuses_site_facts_and_uniqueness_too() {
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    // `f` folds a param into a fresh aggregate and returns it (escape + provenance
    // bearing); `a` returns a bare fresh allocation, which converges to
    // `result_unique = true` when it is analysed at all
    // (`result_unique_fresh_return_true`).
    let uni = vec![
        callable(
            "f",
            vec!["x"],
            MonoExpr::Let {
                bindings: vec![(Symbol::from("a"), boxed(vec![var("x")]))],
                body: Box::new(var("a")),
                span: s(),
                ty: ConcreteType::String,
            },
        ),
        callable("a", vec![], boxed(vec![])),
    ];
    let c = compute_cluster_with_cap(&tf.env(), &module, &uni, 0);
    assert_refuses_publishing_nothing(&c, "f", Stratum::Modes);
    assert!(
        !c.facts.contains_key(&Symbol::from("a")),
        "the unrelated sibling loses its facts too — refusal is universe-wide"
    );
}

// spec: design/typecheck/ownership-inference.md §19.5 — the refusal's NEGATIVE
// detection leg. Without it, a publication path that silently wrote nothing would
// satisfy every positive cell above while looking like a working refusal.
#[test]
fn a_converging_cluster_refuses_nothing_and_publishes_a_full_summary_map() {
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let uni = vec![
        callable("f", vec!["p"], call("f", vec![var("p")])),
        callable("a", vec![], boxed(vec![])),
    ];
    let c = compute_cluster(&tf.env(), &module, &uni);
    assert!(
        c.refusal.is_none(),
        "a converging cluster carries no refusal; got {:?}",
        c.refusal
    );
    assert_eq!(
        c.summaries.len(),
        2,
        "and publishes a summary for EVERY universe member; got {:?}",
        c.summaries.keys().collect::<Vec<_>>()
    );
    assert!(
        c.facts.contains_key(&Symbol::from("f")),
        "with its site facts"
    );
    assert_eq!(
        c.summaries[&Symbol::from("f")].param_mode(0),
        Mode::Borrowed,
        "the converged answer, not the retired ⊤ Owned"
    );
}

// ============ Modes-worklist convergence (S121 D1) ============
//
// The three cells below are a discriminating trio over ONE source shape: a
// self-recursive callable whose base case returns a parameter and whose
// self-call PERMUTES its two parameters. They are source-derived (parsed +
// typechecked through `check_src`, universe via `collect_universe`) rather than
// hand-built, because the defect lives in how the worklist iterates a REAL
// callable's summary, not in a `Callable` literal.
//
// Provenance: QA's S121 crash attribution reduced an f4 SIGSEGV to this shape;
// `test` committed its runtime faces in `tests/s99_fixtures.rs`
// (`parameter_permuting_self_call_{repl,run}_yields_the_builder_sum` and the
// crash witness). These cells are the producer-seam half of that evidence.

/// The oscillator: the base case returns param `b`, the self-call passes
/// `(f b i)` — argument order PERMUTED. This is QA's `v23` shape verbatim.
const PERMUTING_SELF_CALL: &str = "(defn f [i b] (if (eq-i64 i 0) b (f b i)))
     (defn quiet [n] (add-i64 n 1))";

/// The same shape with the parameters annotated `:Int`. Annotation is NOT the
/// cure — this still fails to converge (cell 2) — but it is what keeps the
/// control non-vacuous, so subject and control differ by one token.
const ANNOTATED_PERMUTING_SELF_CALL: &str = "(defn f [:Int i :Int b] (if (eq-i64 i 0) b (f b i)))
     (defn quiet [n] (add-i64 n 1))";

/// The control: identical but for the self-call's argument ORDER — `(f i b)`.
///
/// The `:Int` annotations are load-bearing. Without them `b` never pins to a
/// concrete type, `f` fails `is_strict_type_concrete` and drops out of
/// `collect_universe` entirely (measured: universe becomes `["quiet(1)"]`), so
/// an unannotated control would pass because nothing was analysed.
const ANNOTATED_NON_PERMUTING_SELF_CALL: &str =
    "(defn f [:Int i :Int b] (if (eq-i64 i 0) b (f i b)))
     (defn quiet [n] (add-i64 n 1))";

/// Parse, typecheck and collect the ownership universe for `source`, sorted by
/// key so a recorded visit sequence is comparable across runs.
fn source_universe(tf: &mut TestFixture, source: &str) -> Vec<Callable> {
    check_src(tf, source);
    let env = tf.env();
    let mut universe = collect_universe(&env, &tf.state);
    universe.sort_by(|a, b| a.key.as_ref().cmp(b.key.as_ref()));
    universe
}

/// The summary this callable published, or `None` when the cluster published
/// nothing for it. After §19.5 a non-converging analysis has exactly one
/// spelling — absence — so "did the analysis fail" is read here, not from a ⊤
/// fingerprint the way it had to be while `reset_to_top` existed.
fn published<'c>(c: &'c ClusterOwnership, callable: &Callable) -> Option<&'c ModeSummary> {
    c.summaries.get(&callable.key)
}

fn named<'u>(universe: &'u [Callable], key: &str) -> &'u Callable {
    universe
        .iter()
        .find(|c| c.key.as_ref() == key)
        .unwrap_or_else(|| panic!("{key} must be in the analysed universe"))
}

// spec: design/typecheck/ownership-inference.md §3.2 — the modes worklist
// converges, so a converged cluster publishes a real summary, never ⊤.
// spec: spec/12-runtime.md §12.3.1 — freed memory MUST NOT be accessed after
// deallocation (the consequence: the ⊤ below claims `result: Fresh`, which
// `backend::compiler::fn_compiler::return_is_fresh_by_summary` reads to ELIDE
// the callee return protect on a body that does return its parameter).
#[test]
fn parameter_permuting_self_call_publishes_a_converged_summary() {
    let mut tf = tc_with_prims();
    let universe = source_universe(&mut tf, PERMUTING_SELF_CALL);
    let env = tf.env();
    let c = compute_cluster(&env, &tf.state.current_module, &universe);

    let f = named(&universe, "f");
    let quiet = named(&universe, "quiet");
    assert!(c.refusal.is_none(), "f converges; got {:?}", c.refusal);
    let published_f = published(&c, f).expect("f must publish its inferred summary");
    // The base case returns param 1 and the permuting self-call carries param 0
    // into the same position, so BOTH parameters may reach the result and neither
    // may be named: the axis's ⊤ (§19.2). Not-`Fresh` is the safety-bearing half —
    // `return_is_fresh_by_summary` keeps the callee return protect on it.
    assert_eq!(
        published_f.result,
        cranelisp_types::ResultMode::MayAliasAny,
        "a body that may return either of two parameters publishes the result ⊤"
    );
    // The universe-wide leg. `quiet` is `(add-i64 n 1)` — an Int-only body with
    // no relation to `f`, which converges to Copy/Consumed on its own in one
    // visit. Losing ITS summary was the cluster-wide recovery's fingerprint: the
    // failure was not local to `f`, it condemned every callable compiled alongside.
    let published_quiet =
        published(&c, quiet).expect("an unrelated Int-only callable keeps its own summary");
    assert_eq!(published_quiet.result, cranelisp_types::ResultMode::Fresh);
}

// spec: design/typecheck/ownership-inference.md §13.6 (blocker 4) — the visit
// cap is a DEFENSIVE guard for a converging analysis, so a well-typed cluster
// must drain the worklist rather than exhaust the cap.
#[test]
fn parameter_permuting_self_call_worklist_drains_below_a_generous_cap() {
    let mut tf = tc_with_prims();
    let universe = source_universe(&mut tf, ANNOTATED_PERMUTING_SELF_CALL);
    let env = tf.env();
    // A cap two orders of magnitude above the production bound
    // (`universe.len() * (maxp + 4) + 32` = 44 here). Draining well below it is
    // what separates "the cap is too tight" from "the transfer function does
    // not converge"; QA named exactly this as the refuter for its
    // cap-exhaustion reading.
    const GENEROUS_CAP: usize = 10_000;
    let (c, visits) = visit_log::capture(|| {
        compute_cluster_with_cap(&env, &tf.state.current_module, &universe, GENEROUS_CAP)
    });

    assert!(
        visits.len() < GENEROUS_CAP,
        "the worklist must drain, not exhaust {GENEROUS_CAP} visits; \
         last summaries seen: {:?}",
        visits.iter().rev().take(4).collect::<Vec<_>>()
    );
    assert!(
        c.refusal.is_none(),
        "annotating the parameters is not the cure — f must still converge; got {:?}",
        c.refusal
    );
    assert!(published(&c, named(&universe, "f")).is_some());
}

// spec: design/typecheck/ownership-inference.md §3.2, §4.2 (FIXME 0520) — a
// self-recursive body whose base case returns param 1 and whose recursive arm
// forwards the same parameter converges to `MayAliasOf(1)` in a few visits.
#[test]
fn non_permuting_self_call_control_converges_to_may_alias_of_the_returned_param() {
    let mut tf = tc_with_prims();
    let universe = source_universe(&mut tf, ANNOTATED_NON_PERMUTING_SELF_CALL);
    let env = tf.env();
    let f = named(&universe, "f");
    assert_eq!(f.params.len(), 2, "control must analyse a two-param f");

    const GENEROUS_CAP: usize = 10_000;
    let (c, visits) = visit_log::capture(|| {
        compute_cluster_with_cap(&env, &tf.state.current_module, &universe, GENEROUS_CAP)
    });

    // The instrument's negative leg: a silent visit log would read zero here,
    // making the `< GENEROUS_CAP` assertion above vacuous. Every callable is
    // visited at least once, so the log is never empty for a drained worklist.
    assert!(
        (universe.len()..GENEROUS_CAP).contains(&visits.len()),
        "control drains in a handful of visits; got {}",
        visits.len()
    );
    assert!(c.refusal.is_none(), "control must not be refused");
    assert_eq!(
        published(&c, f).expect("control publishes").result,
        cranelisp_types::ResultMode::MayAliasOf(1),
        "the base case returns param 1 on one path ⇒ may-alias param 1"
    );
}

/// A THREE-parameter rotation: the self-call sends `b`→`a`, `c`→`b`, `a`→`c`.
/// Under the retired lowest-index representative this is a 3-cycle by the same
/// reading that made the two-parameter shape an involution; the general trigger
/// set for that oscillation was never established (`unit-report.md` §8), so it is
/// carried as its own condition rather than assumed to follow.
const ANNOTATED_ROTATING_SELF_CALL: &str =
    "(defn f [:Int a :Int b :Int c] (if (eq-i64 a 0) c (f b c a)))
     (defn quiet [n] (add-i64 n 1))";

// spec: design/typecheck/ownership-inference.md §19.3, §19.8 — the reach set
// collapses at "two or more", so the settle time does not depend on the
// permutation's cycle length. A three-parameter rotation converges like the
// two-parameter one.
#[test]
fn three_parameter_rotating_self_call_converges_to_the_result_top() {
    let mut tf = tc_with_prims();
    let universe = source_universe(&mut tf, ANNOTATED_ROTATING_SELF_CALL);
    let env = tf.env();
    let f = named(&universe, "f");
    assert_eq!(
        f.params.len(),
        3,
        "the subject must analyse a three-param f"
    );

    const GENEROUS_CAP: usize = 10_000;
    let (c, visits) = visit_log::capture(|| {
        compute_cluster_with_cap(&env, &tf.state.current_module, &universe, GENEROUS_CAP)
    });

    assert!(
        (universe.len()..GENEROUS_CAP).contains(&visits.len()),
        "the worklist must drain, not exhaust {GENEROUS_CAP} visits; \
         last summaries seen: {:?}",
        visits.iter().rev().take(4).collect::<Vec<_>>()
    );
    assert!(c.refusal.is_none(), "got {:?}", c.refusal);
    assert_eq!(
        published(&c, f).expect("f publishes").result,
        cranelisp_types::ResultMode::MayAliasAny,
        "the base case returns `c` and the rotation carries `a` and `b` into that \
         position ⇒ the result reaches some parameter, which one undetermined"
    );
}

/// QA's `find-min-helper` (attribution.md §10 v4), reduced to what the producer
/// seam needs: a four-parameter search over a `(Vec Int)` whose recursive arms
/// permute `i` into the `b` position on one branch and keep `b` on the other.
/// Non-convergence was measured here at PROGRAM level only, so this cell is the
/// seam-level condition for the same shape.
const FIND_MIN_HELPER: &str = "(defn fmh [:(Vec Int) g :Int i :Int b :Int c] \
       (if (eq-i64 i 9) b \
         (let [cnt (vec-get g i)] \
           (if (lt-i64 cnt c) (fmh g (add-i64 i 1) i cnt) (fmh g (add-i64 i 1) b c)))))
     (defn quiet [n] (add-i64 n 1))";

// spec: design/typecheck/ownership-inference.md §19.3, §19.8 — the shape QA
// measured as non-converging over a plain `(Vec Int)` drains its worklist and
// publishes a real summary.
#[test]
fn find_min_helper_over_a_vec_int_converges() {
    let mut tf = tc_with_prims();
    let universe = source_universe(&mut tf, FIND_MIN_HELPER);
    let env = tf.env();
    let f = named(&universe, "fmh");

    const GENEROUS_CAP: usize = 10_000;
    let (c, visits) = visit_log::capture(|| {
        compute_cluster_with_cap(&env, &tf.state.current_module, &universe, GENEROUS_CAP)
    });

    assert!(
        (universe.len()..GENEROUS_CAP).contains(&visits.len()),
        "the worklist must drain, not exhaust {GENEROUS_CAP} visits; \
         last summaries seen: {:?}",
        visits.iter().rev().take(4).collect::<Vec<_>>()
    );
    assert!(c.refusal.is_none(), "got {:?}", c.refusal);
    let result = published(&c, f).expect("fmh publishes").result;
    assert_ne!(
        result,
        cranelisp_types::ResultMode::Fresh,
        "fmh returns parameter `b` on its base path, so `Fresh` would elide the \
         callee return protect"
    );
}

// =================== Residual-parameter frames (§19.6) ===================

// spec: design/typecheck/ownership-inference.md §19.6 — a frame whose scheme
// still carries a residual parameter type refuses per-parameter seeding (§18.2
// O-1) and is never walked, so it publishes nothing: it is recorded in the keyed
// trace set and is absent from the summary map. Its callers read it as absent,
// which is the Decision-24 lowering it actually receives.
#[test]
fn a_residual_parameter_frame_publishes_nothing_and_stays_in_the_keyed_set() {
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let mut residual = callable("r", vec!["p"], var("p"));
    residual.residual_params = true;
    let uni = vec![residual, callable("ok", vec!["q"], boxed(vec![var("q")]))];
    let c = compute_cluster(&tf.env(), &module, &uni);

    assert!(
        c.refusal.is_none(),
        "one residual frame does not refuse the cluster"
    );
    assert!(
        c.residual_param_frames.contains(&Symbol::from("r")),
        "the keyed set records the frame for the trace"
    );
    assert!(
        !c.summaries.contains_key(&Symbol::from("r")),
        "a frame the fixpoint never walks publishes NO summary; got {:?}",
        c.summaries.get(&Symbol::from("r"))
    );
    assert!(
        !c.facts.contains_key(&Symbol::from("r")),
        "and no site facts"
    );
    // The negative leg: its non-residual sibling is unaffected, so "publishes
    // nothing" is the residual frame's property and not a dead publication path.
    assert!(c.summaries.contains_key(&Symbol::from("ok")));
    assert_eq!(mode(&c, "ok", 0), Mode::Owned);
}

// spec: design/typecheck/ownership-inference.md §19.6, §19.7 — an in-cluster
// caller of a residual frame reads it as ABSENT (Owned/Retained at the argument),
// never falling through to whatever summary a previous compile persisted on that
// entry.
#[test]
fn a_caller_of_a_residual_frame_reads_it_as_absent() {
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let mut residual = callable("r", vec!["p"], var("p"));
    residual.residual_params = true;
    let uni = vec![
        residual,
        callable("caller", vec!["x"], call("r", vec![var("x")])),
    ];
    let c = compute_cluster(&tf.env(), &module, &uni);
    assert_eq!(
        mode(&c, "caller", 0),
        Mode::Owned,
        "an absent callee summary reads ⊤ at the argument (Owned/Retained)"
    );
}

// ---- §19.6: the cluster-member fence over the chain-follow fallback ----
//
// `ClusterEnv`/`UniqClusterEnv` fall through to the symbol table for imports and
// declared leaves. A cluster MEMBER with no working entry was never walked THIS
// compile, so the fallback would hand back whatever a PREVIOUS compile persisted
// on its entry — live under REPL redefinition, which the schema version does not
// fence within a session. The two cells below are a pair: the same persisted
// summary is refused for a member and honoured for a non-member.

/// Install a concrete unary callable into the fixture's `user` table carrying a
/// summary a previous compile persisted on its entry.
fn install_persisted(tf: &TestFixture, key: &str, summary: cranelisp_types::ModeSummary) {
    let view = cranelisp_types::MonoDefnVariant {
        name: Symbol::from(key),
        params: vec![Symbol::from("p")],
        body: var("p"),
        span: s(),
        mode_summary: None,
    };
    let mut table = tf.modules.get_mut(&ModuleFullPath::from("user")).unwrap();
    table
        .install_concrete(
            Symbol::from(key),
            crate::scheme::mono(Type::Fn(vec![Type::String], Box::new(Type::String))),
            vec![Symbol::from("p")],
            None,
            0,
            cranelisp_types::CallableOrigin::Plain,
            cranelisp_types::Realization::Body {
                view: view.clone(),
                code: None,
            },
            None,
            vec![],
            cranelisp_types::Visibility::Public,
        )
        .unwrap();
    table
        .publish_body_ownership(
            &CallableTarget::Binding(FQSymbol {
                module: ModuleFullPath::from("user"),
                symbol: Symbol::from(key),
            }),
            summary,
            view,
        )
        .unwrap();
}

/// A summary strong enough that reading it is observable on both strata:
/// `Borrowed` keeps a caller's argument un-widened, and `result_unique` lets a
/// caller chain uniqueness through the call.
fn strong_persisted() -> cranelisp_types::ModeSummary {
    cranelisp_types::ModeSummary {
        param_modes: vec![Mode::Borrowed],
        result: cranelisp_types::ResultMode::Fresh,
        param_flow: vec![cranelisp_types::ParamFlow::Consumed],
        spark_ops: vec![false],
        result_unique: true,
    }
}

/// `(let [v (Box)] [_t (<callee> v)] v)` — `v` is returned, so it is unique only
/// if the call does NOT also consume it. The consuming-ness of that argument
/// comes from the callee's summary, which is the second private-env read the
/// member fence governs.
fn arg_pos_caller(key: &str, callee: &str) -> Callable {
    let body = MonoExpr::Let {
        bindings: vec![
            (Symbol::from("v"), boxed(vec![])),
            (Symbol::from("_t"), call(callee, vec![var("v")])),
        ],
        body: Box::new(var("v")),
        span: s(),
        ty: ConcreteType::String,
    };
    callable(key, vec![], body)
}

#[test]
fn a_cluster_members_persisted_summary_is_never_read() {
    // spec: §19.6 — the member fence. `r` is a residual-parameter frame, so this
    // compile never walks it; its entry still carries the summary a previous
    // compile persisted. Both private envs must read it as ABSENT.
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    install_persisted(&tf, "r", strong_persisted());
    let mut residual = callable("r", vec!["p"], var("p"));
    residual.residual_params = true;
    let uni = vec![
        residual,
        callable("caller", vec!["x"], call("r", vec![var("x")])),
        arg_pos_caller("uniq_caller", "r"),
    ];
    let c = compute_cluster(&tf.env(), &module, &uni);
    assert_eq!(
        mode(&c, "caller", 0),
        Mode::Owned,
        "ClusterEnv must not fall through to the persisted Borrowed summary"
    );
    assert!(
        !runique(&c, "caller"),
        "UniqClusterEnv must not chain the persisted result_unique bit"
    );
    assert!(
        !runique(&c, "uniq_caller"),
        "nor read the persisted ARG POSITIONS: an absent callee consumes its \
         argument, so the returned binding has two consuming uses"
    );
}

#[test]
fn a_non_members_persisted_summary_is_read() {
    // spec: §19.6 (the negative twin) — the fence is keyed on cluster membership
    // and nothing else. The same persisted summary on a callable OUTSIDE the
    // universe is the declared-leaf fact the chain-follow exists to deliver, and
    // both strata consume it.
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    install_persisted(&tf, "ext", strong_persisted());
    let uni = vec![
        callable("caller", vec!["x"], call("ext", vec![var("x")])),
        arg_pos_caller("uniq_caller", "ext"),
    ];
    let c = compute_cluster(&tf.env(), &module, &uni);
    assert_eq!(
        mode(&c, "caller", 0),
        Mode::Borrowed,
        "an import's persisted Borrowed summary keeps the argument un-widened"
    );
    assert!(
        runique(&c, "caller"),
        "an import's persisted result_unique bit chains through the call"
    );
    assert!(
        runique(&c, "uniq_caller"),
        "and its persisted arg positions: a Borrowed argument is not a consuming \
         use, so the returned binding stays unique"
    );
}

// =================== Uniqueness stratum (CS-II-1/2) ===================

fn runique(c: &ClusterOwnership, key: &str) -> bool {
    c.summaries[&Symbol::from(key)].result_unique
}

#[test]
fn result_unique_fresh_return_true() {
    // spec: §14.2 clause 3 (driver) — a body returning a fresh alloc is unique.
    let uni = vec![callable("a", vec![], boxed(vec![]))];
    let c = run(uni);
    assert!(runique(&c, "a"));
}

#[test]
fn result_unique_param_return_false() {
    // spec: §14.2 (negative, driver) — returning a param aliases it ⇒ not unique.
    let uni = vec![callable("c", vec!["x"], var("x"))];
    let c = run(uni);
    assert!(!runique(&c, "c"));
}

#[test]
fn result_unique_chains_across_two_call_cluster() {
    // spec: §14.2 clause 3 (driver) — `a() = (Box)` [unique]; `b() = (a)` chains
    // the proof through the call ⇒ b unique.
    let uni = vec![
        callable("a", vec![], boxed(vec![])),
        callable("b", vec![], call("a", vec![])),
    ];
    let c = run(uni);
    assert!(runique(&c, "a"));
    assert!(
        runique(&c, "b"),
        "b chains a.result_unique through the call"
    );
}

#[test]
fn result_unique_greatest_fixpoint_cycle_stays_true() {
    // spec: §14.2 (greatest fixpoint) — a mutual cycle both returning fresh-or-
    // each-other converges to `true` co-inductively (init-optimistic-true holds).
    // ping() = (if c (Box) (pong)); pong() = (ping).
    let cond = MonoExpr::BoolLit {
        value: true,
        span: s(),
        ty: ConcreteType::Bool,
    };
    let ping_body = MonoExpr::If {
        cond: Box::new(cond),
        then_branch: Box::new(boxed(vec![])),
        else_branch: Box::new(call("pong", vec![])),
        span: s(),
        ty: ConcreteType::String,
    };
    let uni = vec![
        callable("ping", vec![], ping_body),
        callable("pong", vec![], call("ping", vec![])),
    ];
    let c = run(uni);
    assert!(runique(&c, "ping"));
    assert!(runique(&c, "pong"));
}

#[test]
fn result_unique_narrows_through_chain() {
    // spec: §14.2 (greatest fixpoint narrowing) — a non-unique leaf narrows its
    // whole caller chain from the optimistic `true` init to `false`, in ANY
    // processing order (the DepSet re-entry). leaf(x)=x [not unique] ⇒ mid(x)=
    // (leaf x) ⇒ top(x)=(mid x): all false.
    let uni = vec![
        callable("top", vec!["x"], call("mid", vec![var("x")])),
        callable("mid", vec!["x"], call("leaf", vec![var("x")])),
        callable("leaf", vec!["x"], var("x")),
    ];
    let c = run(uni);
    assert!(!runique(&c, "leaf"));
    assert!(!runique(&c, "mid"), "mid narrows when leaf narrows");
    assert!(!runique(&c, "top"), "top narrows when mid narrows");
}

/// A call with no `resolved_call` (the Decision-24 classifier row).
fn bare_call(name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(name)),
        args,
        span: s(),
        resolved_call: None,
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

// spec: design/typecheck/ownership-inference.md §19.5 — ONE refusal serves all
// three strata. The retired cell asserted the uniqueness stratum's own recovery
// (`result_unique` forced `false` everywhere, `unique` site facts skipped) while
// the modes summaries it sat on stayed published; the cluster now publishes
// nothing at all, whichever stratum ran out.
//
// The subject drives the UNIQUENESS stratum specifically. Every body here is
// nullary and returns a value the modes walk already predicts, so the modes and
// confinement worklists drain in exactly `universe.len()` visits with no
// re-entry; the uniqueness greatest-fixpoint then needs two more, because
// `leaf`'s Decision-24 body narrows `result_unique` true→false and that narrowing
// walks back up the chain. A cap of 4 is therefore ample for the first two strata
// and one short for the third.
#[test]
fn uniqueness_cap_exhaustion_refuses_the_whole_cluster() {
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let chain = || {
        vec![
            callable("top", vec![], call("mid", vec![])),
            callable("mid", vec![], call("leaf", vec![])),
            callable("leaf", vec![], bare_call("mystery", vec![])),
        ]
    };
    let c = compute_cluster_with_cap(&tf.env(), &module, &chain(), 4);
    assert_refuses_publishing_nothing(&c, "top", Stratum::Uniqueness);

    // The negative leg, one visit further out: the SAME universe at cap 5 drains
    // every stratum, publishes all three summaries, and narrows the chain to
    // `result_unique = false` as `result_unique_narrows_through_chain` expects.
    // Without it, a uniqueness stratum that could never converge would satisfy
    // the refusal above for the wrong reason.
    let ok = compute_cluster_with_cap(&tf.env(), &module, &chain(), 5);
    assert!(ok.refusal.is_none(), "got {:?}", ok.refusal);
    assert_eq!(ok.summaries.len(), 3);
    assert!(
        !runique(&ok, "top"),
        "the narrowing reached the head of the chain"
    );
}

#[test]
fn unique_static_site_fact_emitted_by_driver() {
    // spec: §14.2 (CS-II-2 driver) — `f() = (let [v (Box@30)] (consume v))`: v is
    // a fresh single-use root ⇒ the alloc @30 carries unique_static Some(true).
    let boxsp = Span::new(30, 31);
    let alloc = MonoExpr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
        tag: 0,
        fields: vec![],
        span: boxsp,
        ty: ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
            vec![],
        ),
        escapes: None,
        confined: None,
        unique_static: None,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("v"), alloc)],
        body: Box::new(call("consume", vec![var("v")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let uni = vec![callable("f", vec![], body)];
    let c = run(uni);
    assert_eq!(
        c.facts[&Symbol::from("f")].unique.get(&boxsp),
        Some(&true),
        "the fresh single-use alloc carries unique_static Some(true)"
    );
}
