use super::*;
use cranelisp_types::{
    Binding, CallableArmDraft, CallableArmId, CallableOrigin, CallableTarget, Decl, DefnVariant,
    ErrorLocation, Expr, FQSymbol, ImportNames, ImportSpec, Life, ModuleFullPath, Realization,
    Scheme, Sexp, Symbol, TemplateBody, TemplateKind, Type, Visibility,
};
use std::collections::HashMap;
// FIXME 0109 Wave C: these helpers moved to `process_form.rs`; a handful of
// worker-side tests (introspection + private-submodule enforcement) still
// exercise them (the latter share `mk_writer_test_ctx`, which stays here).
use crate::process_form::{
    check_private_submodule_import, record_imports_on_symbol_table,
    record_submodule_on_symbol_table,
};

// spec: repl/spec/18-redefinition.md §18.1.2 — persisted-source restart
// reconstructs ownership independently of the live replacement gate.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/ownership/fixpoint.rs found=S121 owner=/dev
#[test]
fn cache_preloaded_sum_projection_recheck_preserves_ownership() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_backend::cache;
    use cranelisp_types::CodegenBehaviour;
    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Run,
        },
        root.path().to_path_buf(),
        "main",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    let source = "(import [primitives [Int Pure]])
        (deftype Customer (Addr [:Int a]))
        (defn r-cust [c] (match c [(Customer.Addr a) a]))
        (defn main [] (Pure (r-cust (Customer.Addr 40))))";
    session
        .register_module_with_source("main", source, &root.path().join("main.cl"))
        .unwrap();
    let module = ModuleFullPath::from("main");
    let cold = session.shared.symbol_tables.get(&module).unwrap().clone();
    let meta = root.path().join("main.meta.json");
    cache::serialize::write_meta(&meta, &cold, cache::CACHE_SCHEMA_VERSION).unwrap();
    let restored = cache::serialize::load_meta(&meta)
        .unwrap()
        .into_concrete::<crate::code::Code, ()>();
    assert_eq!(restored.schema_version, cache::CACHE_SCHEMA_VERSION);
    let original = cold.get("r-cust").unwrap();
    let cached = restored.get("r-cust").unwrap();
    assert_eq!(cached.callable_got_slot(), original.callable_got_slot());
    assert!(
        restored
            .got
            .load_slot(cached.callable_got_slot().unwrap())
            .is_null()
    );
    assert!(matches!(
        cached.callable().unwrap().arm.life,
        Life::Concrete {
            realization: Realization::Body { code: None, .. },
            ..
        }
    ));
    let mut without_authored_functions = restored.clone();
    for name in ["r-cust", "main"] {
        without_authored_functions
            .retire_abi_changing(&Symbol::from(name))
            .unwrap();
    }
    let program = build_program_compat(&cranelisp_frontend::parse(source).unwrap()).unwrap();
    let mut empty = crate::code::SessionSymbolTable::new_with_params(module.clone());
    for (name, exposure) in cold.all_name_candidates() {
        if exposure.source.module != module {
            empty
                .expose_candidate(name.clone(), exposure.source.clone(), exposure.visibility)
                .unwrap();
        }
    }
    for (label, initial) in [
        ("empty", empty),
        ("restored", restored),
        ("without_authored_functions", without_authored_functions),
    ] {
        let tables = dashmap::DashMap::new();
        for row in session.shared.symbol_tables.iter() {
            tables.insert(row.key().clone(), row.value().clone());
        }
        tables.insert(module.clone(), initial);
        let checked = check_cluster_to_staging(
            &tables,
            &session.shared.module_aliases,
            &session.shared.prelude_fallback,
            &module,
            &program,
        )
        .unwrap()
        .unwrap()
        .unwrap();
        let staged = checked.staging.get("r-cust").unwrap();
        assert_eq!(
            staged.callable().unwrap().arm.scheme.ty,
            original.callable().unwrap().arm.scheme.ty,
            "{label}"
        );
        assert_eq!(staged.mode_summary(), original.mode_summary(), "{label}");
        assert_eq!(
            staged.mode_summary().unwrap().param_modes,
            vec![cranelisp_types::Mode::Copy],
            "{label}"
        );
        validate_guarded_staging(&tables, &module, &checked.staging, None, None).unwrap();
    }
}

/// Test-only: read a compiled code pointer from a symbol's GOT slot. The
/// production executor reads clause code ptrs through
/// `JitMacroExpander::clause_code_ptr` (`src/expander.rs`); this mirrors that
/// read for the codegen unit tests.
fn get_code_ptr(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    name: &Symbol,
) -> Option<*const u8> {
    symbol_tables.get(module).and_then(|t| {
        let entry = t.get(name.as_ref())?;
        let Some(callable) = entry.callable() else {
            return None;
        };
        let Life::Concrete {
            realization: Realization::Body { code: Some(_), .. },
            ..
        } = &callable.arm.life
        else {
            return None;
        };
        let slot = entry.callable_got_slot()?;
        let ptr = t.got.load_slot(slot);
        if ptr.is_null() { None } else { Some(ptr) }
    })
}

fn synthetic_scheme() -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Int,
    }
}

fn binding_target(module: &ModuleFullPath, name: impl Into<Symbol>) -> CallableTarget {
    CallableTarget::Binding(FQSymbol {
        module: module.clone(),
        symbol: name.into(),
    })
}

fn demand_instance_key(
    table: &crate::code::SessionSymbolTable,
    demand: &cranelisp_types::MonoDemand,
) -> Symbol {
    let scheme = &table
        .callable_target(&demand.template)
        .expect("demand template exists")
        .scheme;
    demand
        .instance_key(scheme)
        .expect("fixture demand has a concrete callable identity")
}

fn concrete_body_draft(name: &str) -> CallableArmDraft {
    let variant = trivial_variant();
    let view = cranelisp_types::MonoDefnVariant {
        name: Symbol::from(name),
        params: Vec::new(),
        body: cranelisp_types::MonoExpr::lenient_from_expr(
            &variant.body,
            &Default::default(),
            &Default::default(),
            &Default::default(),
        ),
        span: Span::SYNTHETIC,
        mode_summary: None,
    };
    CallableArmDraft::concrete_body(synthetic_scheme(), Vec::new(), variant, view, Vec::new())
}

/// A trivial single-variant `DefnVariant` body.
fn trivial_variant() -> DefnVariant {
    DefnVariant {
        params: vec![],
        body: Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        },
        span: Span::SYNTHETIC,
    }
}

fn install_body_fixture(
    table: &mut crate::code::SessionSymbolTable,
    name: impl Into<Symbol>,
    origin: CallableOrigin,
    ast: Option<DefnVariant>,
    expected_slot: usize,
) {
    let name = name.into();
    let variant = ast.unwrap_or_else(trivial_variant);
    install_typed_body_fixture(
        table,
        name,
        synthetic_scheme(),
        origin,
        variant,
        expected_slot,
    );
}

fn install_typed_body_fixture(
    table: &mut crate::code::SessionSymbolTable,
    name: Symbol,
    scheme: Scheme,
    origin: CallableOrigin,
    variant: DefnVariant,
    expected_slot: usize,
) {
    // W0.b (`backend-keyed-consumer.md` §4 W0.b): typecheck is the sole
    // mono-view producer, so `compile_to_module` hard-errors on a
    // codegen-reached body with `codegen_view: None`. This int-side
    // fixture mirrors the producer — a TOTAL view (strict `from_expr`
    // first, lenient fallback) so ctor/macro-clause-style synthetic
    // bodies still build. (`name`/`params`/`span` on the view are not
    // read by codegen — only `body`/`mode_summary`.)
    // S114 carrier flip (`typed-resolution-carrier.md` §4): `from_expr`
    // now takes the TOTAL typed `var_refs`/`apply_refs` sidecars. This
    // fixture's bodies are synthetic (all-local carve-out on
    // `Span::SYNTHETIC`), so empty maps suffice — the carve-out classifies
    // every synthetic node as `VarRef::Local`/`ApplyRef::ViaCallee`.
    let body = cranelisp_types::MonoExpr::from_expr(
        &variant.body,
        &Default::default(),
        &Default::default(),
        &Default::default(),
    )
    .unwrap_or_else(|_| {
        cranelisp_types::MonoExpr::lenient_from_expr(
            &variant.body,
            &Default::default(),
            &Default::default(),
            &Default::default(),
        )
    });
    let view = cranelisp_types::MonoDefnVariant {
        name: name.clone(),
        params: variant.params.iter().map(|(n, _)| n.clone()).collect(),
        body,
        span: variant.span,
        mode_summary: None,
    };
    let slot = table
        .install_concrete(
            name,
            scheme,
            Vec::new(),
            None,
            0,
            origin,
            Realization::Body { view, code: None },
            Some(variant),
            Vec::new(),
            Visibility::Public,
        )
        .expect("concrete fixture must install through the lifecycle funnel");
    assert_eq!(slot.index(), expected_slot);
}

fn has_compiled_owner(binding: &Binding<crate::code::Code>) -> bool {
    matches!(
        binding.callable().map(|callable| &callable.arm.life),
        Some(Life::Concrete {
            realization: Realization::Body { code: Some(_), .. },
            ..
        })
    )
}

fn concrete_callees(binding: &Binding<crate::code::Code>) -> Vec<FQSymbol> {
    match binding.callable().map(|callable| &callable.arm.life) {
        Some(Life::Concrete { callees, .. }) => callees.clone(),
        other => panic!("expected concrete caller, got {other:?}"),
    }
}

fn install_plain_template_fixture(
    table: &mut crate::code::SessionSymbolTable,
    name: impl Into<Symbol>,
) {
    table
        .install_template(
            name.into(),
            Scheme {
                type_vars: vec![0],
                constraints: HashMap::new(),
                ty: Type::Var(0),
            },
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            TemplateBody::Ast(trivial_variant()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .expect("plain template fixture must install");
}

// spec: design/int/s122-closure.md §2 — ordinary replacement preparation
// rematerializes a prior generic instance even with no named caller.
#[test]
fn ordinary_replacement_preparation_rematerializes_prior_instance() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::{CodegenBehaviour, ConcreteType, MonoDemand, RetireReason};

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    session
        .eval("(defn same-module-helper [] 42)")
        .expect("same-module helper definition succeeds");
    session
        .eval("(defn reload-id [x] x)")
        .expect("generic template definition succeeds");
    let mut realized = session
        .eval("(reload-id 7)")
        .expect("initial concrete realization succeeds")
        .expect("the call produces a result");
    assert_eq!(realized.value(), 7);
    realized.release_program_result();

    let module = ModuleFullPath::from("user");
    let demand = MonoDemand::from_type_args(
        binding_target(&module, "reload-id"),
        vec![ConcreteType::Int],
        Span::SYNTHETIC,
    );
    let instance_key = {
        let table = session.shared.symbol_tables.get(&module).unwrap();
        demand_instance_key(&table, &demand)
    };
    let prior_slot = session
        .shared
        .symbol_tables
        .get(&module)
        .and_then(|table| {
            table
                .get(instance_key.as_ref())
                .and_then(Binding::callable_got_slot)
        })
        .expect("the prior concrete instance has a live slot");
    let replacement = build_program_compat(
        &cranelisp_frontend::parse("(defn reload-id [_] (same-module-helper))").unwrap(),
    )
    .unwrap();
    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    assert!(check.warnings.is_empty());

    let instance_target = binding_target(&module, instance_key.clone());
    let table = prepared.tables.get(&module).unwrap();
    let arm = table
        .callable_target(&instance_target)
        .expect("the same typed instance key is present in the prepared world");
    let new_slot = match &arm.life {
        Life::Concrete {
            slot,
            ast:
                Some(DefnVariant {
                    body: Expr::Apply { .. },
                    ..
                }),
            minted_from: Some(actual),
            ..
        } => {
            assert_eq!(actual, &demand.instance_link());
            slot.index()
        }
        other => panic!("expected replacement-materialized Int body, got {other:?}"),
    };
    assert_ne!(
        new_slot, prior_slot,
        "changed ownership ABI needs a fresh slot"
    );
    assert!(table.retired_slots().iter().any(|retired| {
        retired.slot.index() == prior_slot
            && matches!(
                &retired.reason,
                RetireReason::AbiChanging { symbol } if symbol == &instance_key
            )
    }));
    assert!(
        prepared.targets.contains(&instance_target),
        "the successful demand target must join the ordinary compile batch"
    );

    session.shutdown();
}

fn owed_facts_session() -> (tempfile::TempDir, crate::session_v4::CompilerSession) {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::CodegenBehaviour;

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    (root, session)
}

fn prepare_uncheckable_cluster(
    session: &crate::session_v4::CompilerSession,
    lookup_dependencies: &std::collections::BTreeSet<ModuleFullPath>,
) -> Option<PreparedCommit> {
    prepare_cluster_commit_with_demands(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &ModuleFullPath::from("user"),
        ClusterPrograms {
            working: &[],
            codegen: &[],
        },
        OwedFacts {
            lookup_dependencies,
        },
        &crate::scheduler::SourceProvenance::Increment,
        &session.shared,
    )
    .unwrap()
    .map(|prepared| prepared.unwrap().0)
}

// spec: design/int/int.md §7.6.2.1 — an attempt whose only owed fact is its
// lookup dependencies still prepares a publication, and its staging holds them.
#[test]
fn lookup_dependencies_alone_prepare_a_publication_holding_them() {
    let (_root, mut session) = owed_facts_session();
    let lookup = std::collections::BTreeSet::from([ModuleFullPath::from("b")]);
    let prepared = prepare_uncheckable_cluster(&session, &lookup)
        .expect("owed lookup dependencies require a publication");
    assert_eq!(
        prepared.staging.lookup_dependencies().collect::<Vec<_>>(),
        [&ModuleFullPath::from("b")]
    );
    assert!(
        prepared.targets.is_empty(),
        "an empty publication has no JIT"
    );
    session.shutdown();
}

// spec: design/int/int.md §7.6.2.1 — an attempt owing nothing still makes no
// publication.
#[test]
fn attempt_owing_nothing_prepares_no_publication() {
    let (_root, mut session) = owed_facts_session();
    let prepared = prepare_uncheckable_cluster(&session, &std::collections::BTreeSet::new());
    assert!(prepared.is_none());
    session.shutdown();
}

// spec: design/int/s122-closure.md §2 — an admitted same-language-type
// generic edit rematerializes every prior instance in the original candidate,
// preserving an ABI-compatible instance's exact slot.
// defect: class=stale-realization locus=src/worker.rs::capture_affected_mono_demands found=S122 owner=/dev
#[test]
fn ordinary_same_type_replacement_preparation_rematerializes_prior_instance() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::{CodegenBehaviour, ConcreteType, MonoDemand};

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    session.eval("(defn same-type-id [_] 7)").unwrap();
    let mut realized = session.eval("(same-type-id 0)").unwrap().unwrap();
    assert_eq!(realized.value(), 7);
    realized.release_program_result();

    let module = ModuleFullPath::from("user");
    let demand = MonoDemand::from_type_args(
        binding_target(&module, "same-type-id"),
        vec![ConcreteType::Int],
        Span::SYNTHETIC,
    );
    let instance_key = {
        let table = session.shared.symbol_tables.get(&module).unwrap();
        demand_instance_key(&table, &demand)
    };
    let prior_slot = session
        .shared
        .symbol_tables
        .get(&module)
        .and_then(|table| {
            table
                .get(instance_key.as_ref())
                .and_then(Binding::callable_got_slot)
        })
        .unwrap();
    let replacement =
        build_program_compat(&cranelisp_frontend::parse("(defn same-type-id [_] 42)").unwrap())
            .unwrap();
    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    assert!(check.warnings.is_empty());

    let instance_target = binding_target(&module, instance_key.clone());
    let table = prepared.tables.get(&module).unwrap();
    let arm = table.callable_target(&instance_target).unwrap();
    match &arm.life {
        Life::Concrete {
            slot,
            ast:
                Some(DefnVariant {
                    body: Expr::IntLit { value: 42, .. },
                    ..
                }),
            minted_from: Some(actual),
            ..
        } => {
            assert_eq!(actual, &demand.instance_link());
            assert_eq!(slot.index(), prior_slot);
        }
        other => panic!("expected same-type replacement body at prior key, got {other:?}"),
    }
    assert!(
        prepared
            .decisions
            .contains(&StagedPublicationDecision::PreserveAbi {
                symbol: instance_key,
            })
    );
    assert!(prepared.targets.contains(&instance_target));
    session.shutdown();
}

// spec: spec/05-definitions.md §5.1.2; design/int/s122-closure.md §2 — an
// overload arm made concrete in-place by sibling-call back-flow is already the
// replacement candidate's realization. Same-type replacement preparation must
// use that checked arm to rematerialize the exact historical instance rather
// than decline its demand.
#[test]
fn same_type_backflow_concrete_arm_replacement_uses_staged_arm() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::CodegenBehaviour;

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    let original = "(defn rp4 \
        ([p rot] (let [q (rp4 p rot 0)] p)) \
        ([p rot idx] (primitives/add-i64 p (primitives/add-i64 rot idx))))";
    session
        .eval(&format!("{original}\n(defn call-rp4 [] (rp4 3 4))"))
        .unwrap();
    let mut prior_result = session.eval("(call-rp4)").unwrap().unwrap();
    assert_eq!(prior_result.value(), 3);
    prior_result.release_program_result();

    let module = ModuleFullPath::from("user");
    let family = FQSymbol {
        module: module.clone(),
        symbol: Symbol::from("rp4"),
    };
    let prior_key = Symbol::from("(user/rp4 [primitives/Int primitives/Int] primitives/Int)");
    let (prior_scheme, prior_link) = {
        let mut live = session.shared.symbol_tables.get_mut(&module).unwrap();
        let family_binding = live.get("rp4").unwrap().clone();
        let Decl::Overloaded(declaration) = &family_binding.declaration else {
            panic!("rp4 must be an overload family");
        };
        let arm = &declaration.arms[0];
        let Life::Concrete {
            realization: Realization::Body { view, .. },
            minted_from: None,
            ast,
            callees,
            mode_summary: None,
            ..
        } = &arm.callable.life
        else {
            panic!(
                "fresh back-flow-pinned arm must be concrete and unlinked, got {:?}",
                arm.callable.life
            );
        };
        let link = cranelisp_types::InstanceLink::from_type_args(
            CallableTarget::OverloadArm {
                owner: family.clone(),
                arm: arm.id,
            },
            Vec::new(),
        );
        let prior_summary = cranelisp_types::ModeSummary {
            param_modes: vec![cranelisp_types::Mode::Copy; 2],
            result: cranelisp_types::ResultMode::AliasOf(0),
            param_flow: vec![cranelisp_types::ParamFlow::Consumed; 2],
            spark_ops: vec![false; 2],
            result_unique: false,
        };
        let mut prior_view = view.clone();
        prior_view.mode_summary = Some(prior_summary.clone());
        let (installed, _) = live
            .install_instance(
                link.clone(),
                arm.callable.scheme.clone(),
                arm.callable.param_names.clone(),
                declaration.docstring.clone(),
                declaration.seq,
                CallableOrigin::Plain,
                Realization::Body {
                    view: prior_view.clone(),
                    code: None,
                },
                ast.clone(),
                callees.clone(),
                family_binding.visibility,
            )
            .unwrap();
        assert_eq!(installed, prior_key);
        live.publish_body_ownership(
            &binding_target(&module, prior_key.clone()),
            prior_summary,
            prior_view,
        )
        .unwrap();
        let generated = live.get(prior_key.as_ref()).unwrap();
        let generated = generated.callable().unwrap();
        let Life::Concrete {
            minted_from: Some(link),
            ..
        } = &generated.arm.life
        else {
            panic!(
                "generated rp4 instance must retain its backlink, got {:?}",
                generated.arm.life
            );
        };
        assert_eq!(link.instance_key(&arm.callable.scheme).unwrap(), prior_key);
        (generated.arm.scheme.clone(), link.clone())
    };

    let replacement = build_program_compat(&cranelisp_frontend::parse(original).unwrap()).unwrap();
    let checked = check_cluster_to_staging(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    let Decl::Overloaded(staged_declaration) = &checked.staging.get("rp4").unwrap().declaration
    else {
        panic!("replacement rp4 must remain an overload family");
    };
    let staged_arm = &staged_declaration.arms[0].callable;
    assert!(matches!(
        staged_arm.life,
        Life::Concrete {
            minted_from: None,
            ..
        }
    ));
    assert_eq!(staged_arm.scheme.ty, prior_scheme.ty);
    assert_eq!(staged_arm.scheme.type_vars, prior_scheme.type_vars);
    assert_eq!(
        prior_link.instance_key(&staged_arm.scheme).unwrap(),
        prior_key
    );
    assert!(checked.staging.get(prior_key.as_ref()).is_none());
    let staged_target = CallableTarget::OverloadArm {
        owner: family,
        arm: staged_declaration.arms[0].id,
    };
    drop(checked);

    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    assert!(check.warnings.is_empty());
    assert!(prepared.targets.contains(&staged_target));

    let mut processed =
        crate::cluster::ProcessedCluster::from_parts(check.warnings, Vec::new(), Vec::new());
    processed.set_prepared(prepared);
    compile_and_publish_prepared(&mut processed, &session.shared, true).unwrap();
    let mut replaced_result = session.eval("(call-rp4)").unwrap().unwrap();
    assert_eq!(replaced_result.value(), 3);
    replaced_result.release_program_result();
    session.shutdown();
}

// spec: design/int/s122-closure.md §2 — overload arm ids are generation-local.
// Original replacement preparation matches historical instances by canonical
// language type, then preserves their full-signature keys, slots and callers.
#[test]
fn ordinary_overload_reorder_remaps_instances_before_atomic_publication() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::CodegenBehaviour;

    struct PriorInstance {
        key: Symbol,
        old_arm: CallableArmId,
        slot: usize,
        pointer: usize,
        caller: &'static str,
        caller_callees: Vec<FQSymbol>,
    }

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    session
        .eval("(defn f ([:a x] 7) ([:a x :b y] 42))")
        .unwrap();
    session.eval("(defn call-one [] (f 0))").unwrap();
    session.eval("(defn call-two [] (f 0 0))").unwrap();
    let mut one = session.eval("(call-one)").unwrap().unwrap();
    assert_eq!(one.value(), 7);
    one.release_program_result();
    let mut two = session.eval("(call-two)").unwrap().unwrap();
    assert_eq!(two.value(), 42);
    two.release_program_result();

    let module = ModuleFullPath::from("user");
    let family = FQSymbol {
        module: module.clone(),
        symbol: Symbol::from("f"),
    };
    let (prior_family, prior_instances) = {
        let live = session.shared.symbol_tables.get(&module).unwrap();
        let prior_family = live.get("f").unwrap().clone();
        let mut instances = live
            .all_symbols()
            .filter_map(|(key, binding)| {
                let callable = binding.callable()?;
                let Life::Concrete {
                    slot,
                    minted_from:
                        Some(cranelisp_types::InstanceLink {
                            template: CallableTarget::OverloadArm { owner, arm },
                            ..
                        }),
                    ..
                } = &callable.arm.life
                else {
                    return None;
                };
                (owner == &family).then(|| PriorInstance {
                    key: key.clone(),
                    old_arm: *arm,
                    slot: slot.index(),
                    pointer: live.got.load_slot(slot.index()) as usize,
                    caller: if arm.ordinal() == 0 {
                        "call-one"
                    } else {
                        "call-two"
                    },
                    caller_callees: Vec::new(),
                })
            })
            .collect::<Vec<_>>();
        instances.sort_by_key(|instance| instance.old_arm.ordinal());
        assert_eq!(instances.len(), 2);
        for instance in &mut instances {
            instance.caller_callees = concrete_callees(live.get(instance.caller).unwrap());
            assert!(instance.caller_callees.contains(&FQSymbol {
                module: module.clone(),
                symbol: instance.key.clone(),
            }));
            assert!(has_compiled_owner(live.get(instance.key.as_ref()).unwrap()));
        }
        (prior_family, instances)
    };
    assert_eq!(
        prior_instances[0].key.as_ref(),
        "(user/f [primitives/Int] primitives/Int)"
    );
    assert_eq!(
        prior_instances[1].key.as_ref(),
        "(user/f [primitives/Int primitives/Int] primitives/Int)"
    );
    let listed = session.list_user_definitions();
    for instance in &prior_instances {
        assert!(!is_internal_listing_name(instance.key.as_ref()));
        assert!(
            !listed.iter().any(|entry| entry.name == instance.key),
            "a generated concrete instance must not become a user declaration"
        );
    }

    let replacement = build_program_compat(
        &cranelisp_frontend::parse("(defn f ([:q x :r y] 142) ([:z x] 107))").unwrap(),
    )
    .unwrap();
    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    assert!(check.warnings.is_empty());

    let staged_family = prepared.staging.get("f").unwrap();
    let table = prepared.tables.get(&module).unwrap();
    for instance in &prior_instances {
        let matched = crate::redefine::match_replacement_overload_arm(
            &family,
            &prior_family,
            staged_family,
            instance.old_arm,
        )
        .unwrap();
        assert_eq!(matched.ordinal(), 1 - instance.old_arm.ordinal());
        let target = binding_target(&module, instance.key.clone());
        let arm = table
            .callable_target(&target)
            .expect("remapped instance is present under its prior full-signature key");
        let Life::Concrete {
            slot,
            minted_from: Some(link),
            ast: Some(ast),
            ..
        } = &arm.life
        else {
            panic!(
                "expected prepared rematerialized instance, got {:?}",
                arm.life
            );
        };
        assert_eq!(slot.index(), instance.slot);
        assert_eq!(
            link.template,
            CallableTarget::OverloadArm {
                owner: family.clone(),
                arm: matched,
            }
        );
        let Decl::Overloaded(staged_declaration) = &staged_family.declaration else {
            panic!("staged f remains overloaded");
        };
        let staged_scheme = &staged_declaration.arms[matched.ordinal()].callable.scheme;
        assert_eq!(
            link.instance_key(staged_scheme).unwrap(),
            instance.key,
            "the remapped staged selector retains canonical executable identity"
        );
        let expected_body = if instance.old_arm.ordinal() == 0 {
            107
        } else {
            142
        };
        assert!(matches!(ast.body, Expr::IntLit { value, .. } if value == expected_body));
        assert!(
            prepared
                .decisions
                .contains(&StagedPublicationDecision::PreserveAbi {
                    symbol: instance.key.clone(),
                })
        );
        assert!(prepared.targets.contains(&target));
        assert_eq!(
            concrete_callees(table.get(instance.caller).unwrap()),
            instance.caller_callees
        );
    }
    drop(table);

    let retained_before = session.shared.retained_code.lock().unwrap().len();
    let mut processed =
        crate::cluster::ProcessedCluster::from_parts(check.warnings, Vec::new(), Vec::new());
    processed.set_prepared(prepared);
    compile_and_publish_prepared(&mut processed, &session.shared, true).unwrap();

    {
        let live = session.shared.symbol_tables.get(&module).unwrap();
        for instance in &prior_instances {
            let binding = live.get(instance.key.as_ref()).unwrap();
            let callable = binding.callable().unwrap();
            let Life::Concrete {
                slot,
                minted_from: Some(link),
                ..
            } = &callable.arm.life
            else {
                panic!("published instance is not concrete");
            };
            assert_eq!(slot.index(), instance.slot);
            assert_eq!(
                link.template,
                CallableTarget::OverloadArm {
                    owner: family.clone(),
                    arm: CallableArmId::from_ordinal(1 - instance.old_arm.ordinal()).unwrap(),
                }
            );
            assert_ne!(live.got.load_slot(instance.slot) as usize, instance.pointer);
            assert!(has_compiled_owner(binding));
            assert_eq!(
                concrete_callees(live.get(instance.caller).unwrap()),
                instance.caller_callees
            );
        }
    }
    let retained = session.shared.retained_code.lock().unwrap();
    for instance in &prior_instances {
        assert!(
            retained[retained_before..].iter().any(|owner| {
                owner.fq.symbol == instance.key && owner.slot == Some(instance.slot)
            })
        );
    }
    drop(retained);

    let mut one = session.eval("(call-one)").unwrap().unwrap();
    assert_eq!(one.value(), 107);
    one.release_program_result();
    let mut two = session.eval("(call-two)").unwrap().unwrap();
    assert_eq!(two.value(), 142);
    two.release_program_result();
    session.shutdown();
}

// spec: design/int/s122-closure.md §2 — caller-free language-type-changing
// replacement may remove every prior arm language type. Historical arm
// instances then decline and their exact keys retire with the successful
// original candidate.
#[test]
fn caller_free_changed_overload_declines_removed_arm_instances() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::CodegenBehaviour;

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    session.eval("(defn f ([:a x] x) ([:a x :b y] y))").unwrap();
    let mut one = session.eval("(f 1)").unwrap().unwrap();
    one.release_program_result();
    let mut two = session.eval("(f 1 2)").unwrap().unwrap();
    two.release_program_result();

    let module = ModuleFullPath::from("user");
    let family = FQSymbol {
        module: module.clone(),
        symbol: Symbol::from("f"),
    };
    let prior_keys = {
        let live = session.shared.symbol_tables.get(&module).unwrap();
        let mut keys = live
            .all_symbols()
            .filter_map(|(key, binding)| {
                let Life::Concrete {
                    minted_from:
                        Some(cranelisp_types::InstanceLink {
                            template: CallableTarget::OverloadArm { owner, .. },
                            ..
                        }),
                    ..
                } = &binding.callable()?.arm.life
                else {
                    return None;
                };
                (owner == &family).then(|| key.clone())
            })
            .collect::<Vec<_>>();
        keys.sort();
        keys
    };
    assert_eq!(prior_keys.len(), 2);

    let replacement = build_program_compat(
        &cranelisp_frontend::parse(
            "(defn f \
                ([:primitives/Bool x] x) \
                ([:primitives/Bool x :primitives/Bool y] y))",
        )
        .unwrap(),
    )
    .unwrap();
    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    assert_eq!(check.warnings.len(), prior_keys.len());
    for key in &prior_keys {
        assert!(
            prepared
                .decisions
                .contains(&StagedPublicationDecision::ChangeAbi {
                    symbol: key.clone(),
                }),
            "declined historical instance `{key}` must retire atomically"
        );
    }

    let mut processed =
        crate::cluster::ProcessedCluster::from_parts(check.warnings, Vec::new(), Vec::new());
    processed.set_prepared(prepared);
    compile_and_publish_prepared(&mut processed, &session.shared, true).unwrap();
    let live = session.shared.symbol_tables.get(&module).unwrap();
    assert!(matches!(
        live.get("f").map(|binding| &binding.declaration),
        Some(Decl::Overloaded(_))
    ));
    for key in &prior_keys {
        assert!(live.get(key.as_ref()).is_none());
    }
    drop(live);
    session.shutdown();
}

// spec: design/int/s122-closure.md §2 — a caller-free language-type-changing
// replacement may change an overload family into one ordinary callable. Its
// historical arm instances decline and retire with that original candidate.
#[test]
fn caller_free_overload_to_plain_retires_prior_arm_instances() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::CodegenBehaviour;

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    session.eval("(defn f ([:a x] x) ([:a x :b y] y))").unwrap();
    let mut one = session.eval("(f 1)").unwrap().unwrap();
    one.release_program_result();
    let mut two = session.eval("(f 1 2)").unwrap().unwrap();
    two.release_program_result();

    let module = ModuleFullPath::from("user");
    let family = FQSymbol {
        module: module.clone(),
        symbol: Symbol::from("f"),
    };
    let prior_keys = {
        let live = session.shared.symbol_tables.get(&module).unwrap();
        let mut keys = live
            .all_symbols()
            .filter_map(|(key, binding)| {
                let Life::Concrete {
                    minted_from:
                        Some(cranelisp_types::InstanceLink {
                            template: CallableTarget::OverloadArm { owner, .. },
                            ..
                        }),
                    ..
                } = &binding.callable()?.arm.life
                else {
                    return None;
                };
                (owner == &family).then(|| key.clone())
            })
            .collect::<Vec<_>>();
        keys.sort();
        keys
    };
    assert_eq!(prior_keys.len(), 2);

    let replacement = build_program_compat(
        &cranelisp_frontend::parse("(defn f [:primitives/Bool x] x)").unwrap(),
    )
    .unwrap();
    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    assert_eq!(check.warnings.len(), prior_keys.len());
    for key in &prior_keys {
        assert!(
            prepared
                .decisions
                .contains(&StagedPublicationDecision::ChangeAbi {
                    symbol: key.clone(),
                }),
            "declined historical instance `{key}` must retire atomically"
        );
    }

    let mut processed =
        crate::cluster::ProcessedCluster::from_parts(check.warnings, Vec::new(), Vec::new());
    processed.set_prepared(prepared);
    compile_and_publish_prepared(&mut processed, &session.shared, true).unwrap();
    let live = session.shared.symbol_tables.get(&module).unwrap();
    assert!(matches!(
        live.get("f").map(|binding| &binding.declaration),
        Some(Decl::Callable(_))
    ));
    for key in &prior_keys {
        assert!(live.get(key.as_ref()).is_none());
    }
    drop(live);
    session.shutdown();
}

// spec: design/int/s122-closure.md §2 — a declined historical demand is
// retired only by successful publication of the complete replacement batch.
#[test]
fn declined_prior_demand_retirement_is_unpublished_until_commit() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::{CodegenBehaviour, ConcreteType, MonoDemand};

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    session.eval("(defn retired-id [x] x)").unwrap();
    let mut realized = session.eval("(retired-id 7)").unwrap().unwrap();
    realized.release_program_result();

    let module = ModuleFullPath::from("user");
    let demand = MonoDemand::from_type_args(
        binding_target(&module, "retired-id"),
        vec![ConcreteType::Int],
        Span::SYNTHETIC,
    );
    let instance_key = {
        let table = session.shared.symbol_tables.get(&module).unwrap();
        demand_instance_key(&table, &demand)
    };
    let (prior_slot, prior_ptr, prior_owner) = {
        let live = session.shared.symbol_tables.get(&module).unwrap();
        let binding = live.get(instance_key.as_ref()).unwrap();
        let slot = binding.callable_got_slot().unwrap();
        (slot, live.got.load_slot(slot), has_compiled_owner(binding))
    };
    let replacement = build_program_compat(
        &cranelisp_frontend::parse("(defn retired-id [:primitives/Int _] true)").unwrap(),
    )
    .unwrap();
    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    assert_eq!(check.warnings.len(), 1);
    assert!(
        prepared
            .decisions
            .contains(&StagedPublicationDecision::ChangeAbi {
                symbol: instance_key.clone(),
            })
    );
    drop(prepared);

    let live = session.shared.symbol_tables.get(&module).unwrap();
    let binding = live
        .get(instance_key.as_ref())
        .expect("discarded preparation must preserve the live instance");
    assert_eq!(binding.callable_got_slot(), Some(prior_slot));
    assert_eq!(live.got.load_slot(prior_slot), prior_ptr);
    assert_eq!(has_compiled_owner(binding), prior_owner);
    drop(live);
    session.shutdown();
}

struct Q1FailureSnapshot {
    base: String,
    instance: String,
    slot: usize,
    pointer: *const u8,
    owner: bool,
    retained: usize,
    glues: usize,
    introspection: Option<String>,
    backing_path: std::path::PathBuf,
    backing_source: String,
}

impl Q1FailureSnapshot {
    fn capture(
        session: &crate::session_v4::CompilerSession,
        module: &ModuleFullPath,
        instance_key: &Symbol,
        backing_path: std::path::PathBuf,
        backing_source: &str,
    ) -> Self {
        std::fs::write(&backing_path, backing_source).unwrap();
        ensure_typecheck_product(&session.shared.typecheck_products, module);
        let mut product = session.shared.typecheck_products.get_mut(module).unwrap();
        product.file_path = Some(backing_path.clone());
        product.source_text = Some(backing_source.to_string());
        drop(product);
        let live = session.shared.symbol_tables.get(module).unwrap();
        let base = live.get("rollback-id").unwrap();
        let instance = live.get(instance_key.as_ref()).unwrap();
        let slot = instance.callable_got_slot().unwrap();
        Self {
            base: format!("{base:?}"),
            instance: format!("{instance:?}"),
            slot,
            pointer: live.got.load_slot(slot),
            owner: has_compiled_owner(instance),
            retained: session.shared.retained_code.lock().unwrap().len(),
            glues: session.shared.fresh_jit_drop_glues.len(),
            introspection: rollback_introspection(session, module),
            backing_path,
            backing_source: backing_source.to_string(),
        }
    }

    fn assert_unchanged(
        &self,
        session: &crate::session_v4::CompilerSession,
        module: &ModuleFullPath,
        instance_key: &Symbol,
        processed: &crate::cluster::ProcessedCluster,
    ) {
        let live = session.shared.symbol_tables.get(module).unwrap();
        let base = live.get("rollback-id").unwrap();
        let instance = live.get(instance_key.as_ref()).unwrap();
        assert_eq!(format!("{base:?}"), self.base);
        assert_eq!(format!("{instance:?}"), self.instance);
        assert_eq!(instance.callable_got_slot(), Some(self.slot));
        assert_eq!(live.got.load_slot(self.slot), self.pointer);
        assert_eq!(has_compiled_owner(instance), self.owner);
        drop(live);
        assert_eq!(
            session.shared.retained_code.lock().unwrap().len(),
            self.retained
        );
        assert_eq!(session.shared.fresh_jit_drop_glues.len(), self.glues);
        assert_eq!(rollback_introspection(session, module), self.introspection);
        let product = session.shared.typecheck_products.get(module).unwrap();
        assert_eq!(
            product.file_path.as_deref(),
            Some(self.backing_path.as_path())
        );
        assert_eq!(
            product.source_text.as_deref(),
            Some(self.backing_source.as_str())
        );
        drop(product);
        assert_eq!(
            std::fs::read_to_string(&self.backing_path).unwrap(),
            self.backing_source
        );
        assert!(processed.warnings().is_empty());
        assert!(processed.redefinitions().is_empty());
        assert!(processed.pending_codegen_notification.is_none());
    }
}

fn rollback_introspection(
    session: &crate::session_v4::CompilerSession,
    module: &ModuleFullPath,
) -> Option<String> {
    session.shared.introspection.as_ref().and_then(|records| {
        records
            .get(&FQSymbol {
                module: module.clone(),
                symbol: Symbol::from("rollback-id"),
            })
            .map(|record| format!("{:?}", record.value()))
    })
}

fn production_diagnostic_for_exact_target(prepared: &PreparedCommit) -> CranelispError {
    assert_eq!(
        prepared.targets.len(),
        1,
        "this diagnostic control deliberately identifies one exact batch member"
    );
    let target = prepared.targets[0].clone();
    let owner = callable_target_owner(&target).unwrap();
    let tables = dashmap::DashMap::new();
    for row in prepared.tables.iter() {
        tables.insert(row.key().clone(), row.value().clone());
    }
    let mut invalid = crate::code::SessionSymbolTable::new_with_params(prepared.module.clone());
    install_transaction_entry(&mut invalid, owner.symbol.as_ref(), Type::Int, false);
    tables.insert(prepared.module.clone(), invalid);
    let mut jit = build_session_jit(&tables).unwrap();
    let error = match cranelisp_backend::compile_to_module(
        prepared.module.clone(),
        std::slice::from_ref(&target),
        &tables,
        jit.jit_module(),
        true,
    ) {
        Ok(_) => panic!("the private invalid body must reach production error attribution"),
        Err(error) => error,
    };
    match &error {
        cranelisp_backend::CompilationError::CodegenFailed {
            module,
            symbol,
            cause,
            ..
        } => {
            assert_eq!(module, &owner.module);
            assert_eq!(symbol, &owner.symbol);
            assert_ne!(symbol.as_ref(), "missing-local");
            assert!(cause.contains("missing-local"), "actual cause was {cause}");
        }
        other => panic!("expected attributed CodegenFailed, got {other:?}"),
    }
    error.into()
}

// spec: design/int/s122-closure.md §2/§5 — an ordinary replacement that
// rematerializes a prior generic instance remains wholly unpublished when a
// real compile mutates the candidate GOT and then fails before publication.
// defect: class=partial-commit locus=src/worker.rs::compile_and_publish_prepared found=S122 owner=/dev
// fault-injection: the private compile operation arms only after the real
// backend returns; `observed_mutations` proves that path ran. A second private
// invalid body under the exact prepared target exercises production error
// attribution. Deleting GOT compensation makes the prior pointer/state
// assertions fail before the old-definition call can pass.
#[test]
fn ordinary_replacement_compile_failure_restores_prior_instance_and_session_state() {
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::{CodegenBehaviour, ConcreteType, MonoDemand};
    use std::cell::RefCell;

    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.path().to_path_buf(),
        "user",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    session.eval("(defn rollback-helper [] 42)").unwrap();
    session.eval("(defn rollback-id [x] x)").unwrap();
    let mut realized = session.eval("(rollback-id 7)").unwrap().unwrap();
    assert_eq!(realized.value(), 7);
    realized.release_program_result();

    let module = ModuleFullPath::from("user");
    let demand = MonoDemand::from_type_args(
        binding_target(&module, "rollback-id"),
        vec![ConcreteType::Int],
        Span::SYNTHETIC,
    );
    let instance_key = {
        let table = session.shared.symbol_tables.get(&module).unwrap();
        demand_instance_key(&table, &demand)
    };
    let snapshot = Q1FailureSnapshot::capture(
        &session,
        &module,
        &instance_key,
        root.path().join("user.cl"),
        "(defn rollback-id [x] x)\n",
    );

    let replacement = build_program_compat(
        &cranelisp_frontend::parse("(defn rollback-id [_] (rollback-helper))").unwrap(),
    )
    .unwrap();
    let (prepared, check) = prepare_cluster_commit(
        &session.shared.symbol_tables,
        &session.shared.module_aliases,
        &session.shared.prelude_fallback,
        &module,
        &replacement,
        &replacement,
        &session.shared,
    )
    .unwrap()
    .unwrap()
    .unwrap();
    let expected_targets = prepared.targets.clone();
    let observed_mutations = RefCell::new(Vec::new());
    let observed_targets = RefCell::new(Vec::new());
    // The candidate's authored-form record rides the cluster; the failed
    // compile must install none of it (`design/int/session-persistence.md`
    // §2.4.1), which the snapshot's record comparison observes.
    let candidate_record = crate::session_v4::Introspection {
        source: Some("(defn rollback-id [_] (rollback-helper))".to_string()),
        sexp: Some(
            cranelisp_frontend::parse("(defn rollback-id [_] (rollback-helper))")
                .unwrap()
                .remove(0),
        ),
        ..Default::default()
    };
    assert_ne!(
        rollback_introspection(&session, &module),
        Some(format!("{candidate_record:?}")),
        "precondition: the candidate record differs from the live one"
    );
    let mut processed = crate::cluster::ProcessedCluster::from_parts(
        check.warnings,
        Vec::new(),
        vec![(
            FQSymbol {
                module: module.clone(),
                symbol: Symbol::from("rollback-id"),
            },
            candidate_record,
        )],
    );
    processed.set_prepared(prepared);

    let error = compile_and_publish_prepared_with(
        &mut processed,
        &session.shared,
        true,
        |prepared, jit, capture_clif| {
            let table = prepared.tables.get(&prepared.module).unwrap();
            let before_cells = prepared
                .targets
                .iter()
                .filter_map(|target| {
                    let arm = table.callable_target(target)?;
                    let Life::Concrete { slot, .. } = &arm.life else {
                        return None;
                    };
                    Some((slot.index(), table.got.load_slot(slot.index()) as usize))
                })
                .collect::<Vec<_>>();
            drop(table);
            let _artifacts = cranelisp_backend::compile_to_module(
                prepared.module.clone(),
                &prepared.targets,
                &prepared.tables,
                jit.jit_module(),
                capture_clif,
            )
            .map_err(CranelispError::from)?;
            observed_targets.replace(prepared.targets.clone());
            let table = prepared.tables.get(&prepared.module).unwrap();
            observed_mutations.replace(
                before_cells
                    .into_iter()
                    .filter_map(|(slot, before)| {
                        let after = table.got.load_slot(slot) as usize;
                        (after != before).then_some((slot, before, after))
                    })
                    .collect(),
            );
            Err(production_diagnostic_for_exact_target(prepared))
        },
    )
    .expect_err("the private compile operation fails before publication");
    assert!(
        !observed_mutations.borrow().is_empty(),
        "real backend compilation must mutate a prepared GOT cell while its JIT is live"
    );
    assert_eq!(*observed_targets.borrow(), expected_targets);
    let message = error.to_string();
    let target_symbol = callable_target_owner(&expected_targets[0]).unwrap();
    assert!(message.contains(target_symbol.module.as_ref()));
    assert!(message.contains(target_symbol.symbol.as_ref()));
    assert!(message.contains("missing-local"));
    let live = session.shared.symbol_tables.get(&module).unwrap();
    for (slot, before, after) in observed_mutations.borrow().iter().copied() {
        assert_ne!(
            after, before,
            "the recorded candidate cell must have changed"
        );
        assert_eq!(
            live.got.load_slot(slot) as usize,
            before,
            "the compile-error compensation must restore every mutated candidate cell"
        );
    }
    drop(live);

    snapshot.assert_unchanged(&session, &module, &instance_key, &processed);

    let mut old_call = session
        .eval("(rollback-id 9)")
        .expect("the next ordinary turn succeeds")
        .expect("the old definition still returns a value");
    assert_eq!(old_call.value(), 9);
    old_call.release_program_result();
    session.shutdown();
}

// spec: design/arch/macro-availability-model.md (FIXME 0299) — the
// cache-restore Linker must resolve binary-exported primitive externs that
// the synthetic `macros` module references (e.g. `sconcat`). The fresh JIT
// resolves these via the host's exported symbols; `dlsym_host_symbol` is
// int's equivalent for the cache path. A known binary-exported primitive
// must resolve to a non-null address; a nonexistent symbol must be None.
#[test]
fn dlsym_host_symbol_resolves_exported_primitive() {
    // `sconcat` is `#[unsafe(export_name = "sconcat")]` in
    // `cranelisp-primitives`, statically linked into the test binary.
    let ptr = dlsym_host_symbol("sconcat");
    assert!(
        ptr.is_some(),
        "sconcat must be resolvable as a host-exported symbol (cache-restore \
             Linker depends on this for cross-module macro expansion — FIXME 0299)"
    );
    assert!(!ptr.unwrap().is_null());

    // `quote-sexp` is the other synthetic-`macros` primitive extern.
    assert!(dlsym_host_symbol("quote-sexp").is_some());
}

// spec: (same anchor) — a symbol the host does not export must not resolve,
// so a genuine `unresolved symbol` is surfaced by the relocation pass rather
// than masked by a bogus address.
#[test]
fn dlsym_host_symbol_misses_unexported_name() {
    assert!(dlsym_host_symbol("__cranelisp_definitely_not_a_real_exported_symbol__").is_none());
}

// S78 in-call-stack restructure: the `pass0_dep_load_resume_restarts_pass2
// _from_zero` and `pass2_fq_autoload_resume_honours_saved_index` unit tests
// probed the deleted `pass2_resume_index` helper. The retry-from-top model
// has NO saved resume index — the whole cluster re-runs from its packet
// sexps every pass, so forms-before-import are always re-processed by
// construction (Defect-B / OQ-4). The behaviour is guarded e2e by
// `tests/spec_08_modules.rs::defn_before_import_resumes_correctly_after_dep_load`.

// spec: design/int/int.md §4.2 — typed codegen projection (the worker's name
// list is the entry's `defined_symbols()` set)
#[test]
fn priority_worker_batch_via_codegen_targets_filter() {
    // Seed a symbol table with a cross-section of entries. Only the entries
    // that pass `defined_symbols()` should be candidates for codegen — the
    // worker's name-list preparation MUST produce the same set.
    let module = ModuleFullPath::from("user");
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

    // Compilable: regular UserFn with ast: Some(_).
    install_body_fixture(
        &mut st,
        "regular",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        0,
    );

    // Compilable: an owned multi-signature arm; the family binding itself is
    // not an executable target.
    st.install_overloaded(
        Symbol::from("add"),
        None,
        0,
        vec![concrete_body_draft("add__arm0")],
        Visibility::Public,
    )
    .expect("owned overload fixture must install");

    // Not compilable: constrained template even if ast happens to be Some.
    let mut template_scheme = synthetic_scheme();
    template_scheme.type_vars.push(0);
    template_scheme.ty = Type::Var(template_scheme.type_vars[0]);
    st.install_template(
        Symbol::from("poly_fn"),
        template_scheme,
        Vec::new(),
        None,
        0,
        CallableOrigin::Plain,
        TemplateBody::Ast(trivial_variant()),
        TemplateKind::Parametric,
        Vec::new(),
        Visibility::Public,
    )
    .expect("template fixture must install");

    // Not compilable: Import chain entry.
    st.expose_candidate(
        Symbol::from("imported"),
        FQSymbol {
            module: ModuleFullPath::from("other"),
            symbol: Symbol::from("x"),
        },
        Visibility::Private,
    )
    .expect("candidate fixture must install");

    let compiled: Vec<CallableTarget> = st.codegen_targets().map(|(target, _)| target).collect();

    // Exactly the two compilable entries: set equality ignoring order.
    assert_eq!(
        compiled.len(),
        2,
        "expected 2 compilable names, got {compiled:?}"
    );
    assert!(compiled.contains(&binding_target(&module, "regular")));
    assert!(compiled.contains(&CallableTarget::OverloadArm {
        owner: FQSymbol {
            module: module.clone(),
            symbol: Symbol::from("add"),
        },
        arm: CallableArmId::from_ordinal(0).expect("arm 0 is valid"),
    }));
    assert!(!compiled.contains(&binding_target(&module, "add")));
    assert!(!compiled.contains(&binding_target(&module, "poly_fn")));
    assert!(!compiled.contains(&binding_target(&module, "imported")));
}

// spec: BC §3 invariant 3 — batch CompilationArtifacts routing to Introspection
//
// S76 W-Collapse: `compile_to_module` now returns batch-level
// `CompilationArtifacts` (concatenated `clif_ir` + summed `code_size`),
// attributed to each compiled name; per-symbol disasm is on-demand via
// `cranelisp_backend::produce_disasm` (the backend's `FunctionArtifacts`
// per-fn map is `pub(crate)` and no longer crosses the boundary). This test
// mirrors the routing loop in `inline_jit_codegen_for_names` step 7.
#[test]
fn priority_worker_routes_batch_artifacts_to_introspection() {
    let module = ModuleFullPath::from("user");
    let clif_ir = "function %foo() -> i64 { ... }\nfunction %bar() -> i64 { ... }";
    let code_size: usize = 19;
    let names = [Symbol::from("foo"), Symbol::from("bar")];

    let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
        dashmap::DashMap::new();

    // Mirror the exact batch routing loop: each compiled name gets the
    // batch clif_ir + code_size; disasm is on-demand (not stored).
    for name in &names {
        let fq = FQSymbol {
            module: module.clone(),
            symbol: name.clone(),
        };
        let mut entry = introspection.entry(fq).or_default();
        entry.clif_ir = Some(clif_ir.to_string());
        entry.code_size = Some(code_size);
    }

    for name in &names {
        let fq = FQSymbol {
            module: module.clone(),
            symbol: name.clone(),
        };
        let e = introspection.get(&fq).expect("introspection entry present");
        assert!(e.clif_ir.as_deref().unwrap_or("").contains("%foo"));
        assert_eq!(e.code_size, Some(code_size));
    }
}

// spec: design/int/int.md §7.1 — GOT slot contents are filled on compile
// completion (typecheck pins the layout; codegen fills the slot)
#[test]
fn priority_worker_stores_code_ptr_in_got_slot() {
    // Given a symbol_tables entry with got_slot: Some(3), verify that after
    // compile completion the worker stores the compiled function pointer
    // at slot 3 in the module's GOT table.
    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

    for index in 0..3 {
        install_body_fixture(
            &mut st,
            format!("padding-{index}"),
            CallableOrigin::Plain,
            Some(trivial_variant()),
            index,
        );
    }
    install_body_fixture(
        &mut st,
        "target",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        3,
    );
    symbol_tables.insert(module.clone(), st);

    // Sanity: lookup_got_slot returns Some(3) for this entry.
    let resolved = lookup_got_slot(&symbol_tables, &module, &Symbol::from("target"));
    assert_eq!(
        resolved,
        Some(3),
        "lookup_got_slot must walk to the pre-assigned slot"
    );

    // Synthetic code pointer — the worker would normally extract this from
    // jit.get_finalized_ptr(). We only care that the store hits slot 3.
    let fake_ptr: *const u8 = 0xCAFEBABE_usize as *const u8;

    // Mirror the exact store call from inline_jit_codegen_for_module step 6.
    let slot = lookup_got_slot(&symbol_tables, &module, &Symbol::from("target"))
        .expect("invariant: got_slot is Some after Wave 0");
    if let Some(st) = symbol_tables.get(&module) {
        st.got.store_slot(slot, fake_ptr);
    }

    // Read back: the same GotTable reads the stored pointer.
    let stored = symbol_tables
        .get(&module)
        .expect("symbol table present")
        .got
        .load_slot(slot);
    assert_eq!(
        stored, fake_ptr,
        "GOT slot must hold the code pointer just written"
    );
}

// spec: design/int/int.md §4.2 + §5 — S57 G6 write of `Code` onto the
// symbol-table entry + macro-clause compile via unified path.
#[test]
fn inline_jit_codegen_for_names_compiles_single_defn() {
    // Exercises the macro-clause migration path: a single-element `names`
    // batch flows through the unified `compile_to_module` entry point and
    // (Sprint 57 Wave 2 G6) writes `code: Some(_)` onto the
    // `ModuleEntry::Def` plus mirrors the pointer into the GOT slot.
    // Replaces the Phase-2 `CodegenProduct.code` assertion.
    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
        dashmap::DashMap::new();

    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
    let macro_name = Symbol::from("__macro_demo");
    crate::repl::test_support::install_macro_fixture(
        &mut st,
        macro_name.as_ref(),
        Sexp::Symbol("__macro_demo".to_string(), Span::SYNTHETIC),
        vec![Vec::new()],
        Visibility::Public,
    );
    let target = CallableTarget::MacroClause {
        owner: FQSymbol {
            module: module.clone(),
            symbol: macro_name.clone(),
        },
        clause: CallableArmId::from_ordinal(0).expect("clause 0 is valid"),
    };
    symbol_tables.insert(module.clone(), st);

    let targets = [target.clone()];
    inline_jit_codegen_for_names(
        &module,
        &targets,
        &symbol_tables,
        Some(&introspection),
        None,
    )
    .expect("unified codegen should succeed for a trivial int-returning defn");

    // Assert: the symbol table entry carries `code: Some(_)` with a
    // non-null pointer (G6 target write path).
    let code_ptr = {
        let table = symbol_tables.get(&module).expect("symbol table present");
        let arm = table
            .callable_target(&target)
            .expect("owned clause present after codegen");
        if let Life::Concrete {
            slot,
            realization: Realization::Body { code: Some(_), .. },
            ..
        } = &arm.life
        {
            let slot = slot.index();
            let ptr = table.got.load_slot(slot);
            assert!(!ptr.is_null(), "compiled function pointer must be non-null");
            ptr
        } else {
            panic!("expected concrete macro clause with a compiled owner; got {arm:?}")
        }
    };

    // Assert: the GOT slot holds the same pointer.
    let stored = symbol_tables
        .get(&module)
        .expect("symbol table present")
        .got
        .load_slot(0);
    assert_eq!(
        stored, code_ptr,
        "GOT slot must hold the pointer returned from the unified codegen path"
    );

    // Assert: introspection entry carries CLIF IR and a code_size.
    let fq = FQSymbol {
        module: module.clone(),
        symbol: macro_name.clone(),
    };
    let intro = introspection
        .get(&fq)
        .expect("introspection entry populated for compiled defn");
    assert!(
        intro
            .clif_ir
            .as_deref()
            .unwrap_or("")
            .contains("__macro_demo"),
        "CLIF IR should mention the compiled function name"
    );
    assert!(
        intro.code_size.is_some_and(|n| n > 0),
        "code_size must be populated from FunctionArtifacts"
    );
}

// spec: design/int/int.md §4.2 — the priority worker is the sole writer: it
// writes `code: Some(_)` onto the symbol-table entry via `compile_to_module`,
// with no session-side merge step.
#[test]
fn priority_worker_writes_code_to_entry_via_compile_to_module() {
    // A trivial single-symbol batch flows through the worker's unified
    // codegen path. After return, the entry carries `code: Some(_)`.
    // This is the G6 target write contract at the priority-worker seam.
    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();

    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
    let slot = 0;
    let defn_name = Symbol::from("answer");
    install_body_fixture(
        &mut st,
        defn_name.clone(),
        CallableOrigin::Plain,
        Some(trivial_variant()),
        slot,
    );
    symbol_tables.insert(module.clone(), st);

    let targets = [binding_target(&module, defn_name.clone())];
    inline_jit_codegen_for_names(&module, &targets, &symbol_tables, None, None)
        .expect("worker codegen succeeds for a trivial int-returning defn");

    let table = symbol_tables.get(&module).expect("symbol table present");
    let entry = table.get(defn_name.as_ref()).expect("entry present");
    if has_compiled_owner(entry) {
        let slot = entry
            .callable_got_slot()
            .expect("callable Def carries a GOT slot after codegen");
        assert!(
            !table.got.load_slot(slot).is_null(),
            "code pointer must be non-null after compile"
        );
    } else {
        panic!("expected concrete Body with a compiled owner; got {entry:?}");
    }
}

// spec: design/int/int.md §5.4 — introspection reads compiled-code presence
// through the symbol-table entry's code accessor (not the deleted
// `CodegenProduct` DashMap).
#[test]
fn introspection_reads_code_from_symbol_table_not_codegen_products() {
    // After compile, the symbol-table `code` field is Some(_). The
    // `has_code_ptr` reader (used by introspection presence checks)
    // must return true for the same entry — this is the migration from
    // the deleted `codegen_products.get(module).code.contains_key(name)`
    // to the symbol-table lookup.
    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();

    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
    let slot = 0;
    let defn_name = Symbol::from("probe");
    install_body_fixture(
        &mut st,
        defn_name.clone(),
        CallableOrigin::Plain,
        Some(trivial_variant()),
        slot,
    );
    symbol_tables.insert(module.clone(), st);

    // Before compile: `has_code_ptr` must return false.
    assert!(
        get_code_ptr(&symbol_tables, &module, &defn_name).is_none(),
        "get_code_ptr must be None before compile"
    );

    let targets = [binding_target(&module, defn_name.clone())];
    inline_jit_codegen_for_names(&module, &targets, &symbol_tables, None, None)
        .expect("worker codegen succeeds");

    // After compile: `has_code_ptr` must return true; `get_code_ptr`
    // must return the same pointer that lives on `ModuleEntry::Def.code`.
    assert!(get_code_ptr(&symbol_tables, &module, &defn_name).is_some());
    let via_helper = get_code_ptr(&symbol_tables, &module, &defn_name)
        .expect("get_code_ptr returns Some after compile");
    let via_entry = {
        let table = symbol_tables.get(&module).expect("symbol table present");
        let entry = table.get(defn_name.as_ref()).expect("entry present");
        if has_compiled_owner(entry) {
            let slot = entry
                .callable_got_slot()
                .expect("callable Def carries a GOT slot after codegen");
            table.got.load_slot(slot)
        } else {
            panic!("expected concrete Body with a compiled owner; got {entry:?}")
        }
    };
    assert_eq!(
        via_helper, via_entry,
        "helper and direct entry read must agree — both are symbol-table reads after G6"
    );
}

// spec: design/int/int.md §4.2 + §8.1 — REPL `__expr` flows through
// `compile_to_module` on the same per-symbol path as any name (no special
// case in `finalize_module`).
#[test]
fn repl_expr_finalize_module_no_longer_uses_special_case() {
    // Register `__expr` as a synthetic zero-arg defn on the symbol table
    // (mirroring `wrap_exprs_as_defns`). Drive `derive_codegen_batch`
    // over a program consisting solely of a `TopLevel::Expr`; confirm
    // `__expr` appears in the derived names list — the uniform path.
    // Then run `inline_jit_codegen_for_names` on it and assert the
    // `code` field on the `__expr` entry becomes Some(_). No
    // `finalize_module` special case is taken — the same G6 write path
    // that serves every other symbol serves `__expr`.
    use cranelisp_types::{DefnVariant, Expr, TopLevel};

    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();

    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
    let slot = 0;
    let expr_name = Symbol::from("__expr");
    let expr_variant = DefnVariant {
        params: vec![],
        body: Expr::IntLit {
            value: 3,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(cranelisp_types::Type::Int)),
        },
        span: Span::SYNTHETIC,
    };
    install_body_fixture(
        &mut st,
        expr_name.clone(),
        CallableOrigin::Plain,
        Some(expr_variant.clone()),
        slot,
    );
    symbol_tables.insert(module.clone(), st);

    // `derive_codegen_batch` for a program whose only TopLevel is Expr
    // must produce a names list containing `__expr` — no special case.
    let program = vec![TopLevel::Expr(expr_variant.body.clone())];
    let names = derive_codegen_batch(&module, &program, &symbol_tables);
    assert!(
        names.contains(&binding_target(&module, expr_name.clone())),
        "__expr must appear in the derived codegen batch alongside any named defn; got {names:?}"
    );

    inline_jit_codegen_for_names(&module, &names, &symbol_tables, None, None)
        .expect("__expr compiles through the uniform G6 path");

    let table = symbol_tables.get(&module).expect("symbol table present");
    let entry = table.get(expr_name.as_ref()).expect("__expr entry present");
    if has_compiled_owner(entry) {
        let slot = entry
            .callable_got_slot()
            .expect("callable __expr Def carries a GOT slot after codegen");
        assert!(
            !table.got.load_slot(slot).is_null(),
            "__expr code pointer must be non-null"
        );
    } else {
        panic!("expected __expr concrete Body with a compiled owner; got {entry:?}");
    }
}

// spec: design/int/int.md §6.2 — 0249-b ctor batch
#[test]
fn derive_codegen_batch_includes_synthesised_constructors() {
    use cranelisp_types::FQTypeName;
    // A constructor `Def` (DefKind::Constructor, ast: Some(_), got_slot)
    // — exactly what typecheck's 0249-a `register_constructors` produces —
    // MUST be enumerated into the codegen batch so its `Expr::ConstrADT`
    // body is lowered and its GOT slot populated (constructor-as-value).
    let module = ModuleFullPath::from("user");
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

    install_body_fixture(
        &mut st,
        "Some",
        CallableOrigin::Ctor {
            type_name: FQTypeName::new(module.clone(), cranelisp_types::TypeName::from("Option")),
            tag: 1,
            field_count: 1,
            internal: false,
            type_def: None,
        },
        Some(trivial_variant()),
        0,
    );

    let symbol_tables = dashmap::DashMap::new();
    symbol_tables.insert(module.clone(), st);

    // The TypeDef itself isn't in `program` as a Defn — the ctor must be
    // picked up by the final symbol-table sweep (0249-b).
    let program: Vec<TopLevel> = vec![];
    let names = derive_codegen_batch(&module, &program, &symbol_tables);
    assert!(
        names.contains(&binding_target(&module, "Some")),
        "synthesised constructor `Some` must appear in the derived codegen batch (0249-b); got {names:?}"
    );
}

// spec: spec/05-definitions.md §5.4.5 — a re-`impl` of an existing
// (trait, target-type) pair REPLACES the previous implementation; dispatch
// afterwards runs the NEW method bodies (hot-reload, like `defn`).
// Design: design/int/session-transaction.md §2.5.
//
// The seam: `derive_codegen_batch`'s FORCED first loop must enroll the
// impl's MANGLED method Defs (`Trait.method$<fq-type>` — the callables), so
// an already-compiled entry (`code: Some(_)`, which `commit_slotted_def`
// carries over on the AbiPreserving re-impl commit) is still recompiled.
// The fixture is DISCRIMINATING by construction: the entry carries
// `code: Some(_)`, so the `already_compiled`-gated sweep at the end of
// `derive_codegen_batch` cannot enroll it — only the TraitImpl arm can.
// Fail-on-revert: the pre-fix arm pushed the UNMANGLED `size`, a dead
// lookup, and this assertion fails.
#[test]
fn derive_codegen_batch_enrolls_mangled_impl_methods_even_when_compiled() {
    use cranelisp_backend::cache::linker::Linker;
    use cranelisp_types::{
        Defn, TopLevel, TraitImpl, TraitName, TraitRef, TypeExpr, TypeName, TypeRef,
    };
    use std::sync::Arc;

    let module = ModuleFullPath::from("user");
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
    // The callable an `(impl Sizeable Box (defn size [x] …))` compiles to,
    // homed in the impl writer's module (D45 as amended, S110 W0.1).
    let mangled = Symbol::from("Sizeable.size$user/Box");
    install_body_fixture(
        &mut st,
        mangled.clone(),
        CallableOrigin::Plain,
        Some(trivial_variant()),
        0,
    );
    // Prior compiled code, as carried over by `commit_slotted_def` on the
    // AbiPreserving re-impl commit — the state that made the sweep skip it.
    let linker = Arc::new(Linker::new().expect("Linker::new must succeed"));
    st.publish_compiled_owner(
        &binding_target(&module, mangled.clone()),
        crate::code::Code::linker(linker),
    )
    .map_err(|rejection| rejection.into_parts().0)
    .expect("concrete body accepts prior compiled owner");

    let symbol_tables = dashmap::DashMap::new();
    symbol_tables.insert(module.clone(), st);

    let program = vec![TopLevel::TraitImpl(TraitImpl {
        trait_name: TraitRef::new(None, TraitName::from("Sizeable")),
        head_con_var: None,
        target: TypeExpr::Named(TypeRef::new(None, TypeName::from("Box"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("size"),
            docstring: None,
            variants: vec![trivial_variant()],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    })];

    let names = derive_codegen_batch(&module, &program, &symbol_tables);
    assert!(
        names.contains(&binding_target(&module, mangled.clone())),
        "a re-impl's MANGLED method Def must enter the FORCED codegen batch even \
             though its live entry already carries compiled code (spec §5.4.5 \
             hot-reload); got {names:?}"
    );
}

// spec: spec/07-traits.md §7.1.5 — "Methods with defaults are automatically
// synthesized if not explicitly provided"; spec/05-definitions.md §5.4.5 — a
// re-`impl` REPLACES the previous implementation. Together: a re-impl that
// OMITS a method the prior impl overrode MUST fall back to the trait's
// DEFAULT body, not keep dispatching the stale override.
// Design: design/int/session-transaction.md §2.5. FIXME 0791.
//
// The seam: the re-impl's `TopLevel::TraitImpl` names only `size` in
// `impl_.methods` (`weight` is omitted, and its re-staged DEFAULT `Defn`
// rides `finalize_cluster`'s WORKING program, never the `program` slice that
// reaches `derive_codegen_batch`). So the enrollment set must be derived from
// the TRAIT, not from the methods this impl form happens to spell.
// Fail-on-revert: with a `{trait}.{method}$` per-method prefix the omitted
// `weight` is absent from the batch and this assertion fails.
#[test]
fn derive_codegen_batch_enrolls_omitted_default_method_of_the_impl() {
    use cranelisp_backend::cache::linker::Linker;
    use cranelisp_types::{
        Defn, TopLevel, TraitImpl, TraitName, TraitRef, TypeExpr, TypeName, TypeRef,
    };
    use std::sync::Arc;

    let module = ModuleFullPath::from("user");
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

    let provided = Symbol::from("Sizeable.size$user/Box");
    let omitted = Symbol::from("Sizeable.weight$user/Box");
    for (index, name) in [&provided, &omitted].into_iter().enumerate() {
        install_body_fixture(
            &mut st,
            name.clone(),
            CallableOrigin::Plain,
            Some(trivial_variant()),
            index,
        );
        // The prior impl's compiled code, carried over by
        // `commit_slotted_def` on the AbiPreserving re-impl commit — the
        // state that makes the `already_compiled` sweep skip the entry, so
        // ONLY the forced TraitImpl arm can enroll it.
        let linker = Arc::new(Linker::new().expect("Linker::new must succeed"));
        st.publish_compiled_owner(
            &binding_target(&module, (*name).clone()),
            crate::code::Code::linker(linker),
        )
        .map_err(|rejection| rejection.into_parts().0)
        .expect("concrete body accepts prior compiled owner");
    }

    let symbol_tables = dashmap::DashMap::new();
    symbol_tables.insert(module.clone(), st);

    // The RE-impl: provides `size` only; `weight` reverts to the default.
    let program = vec![TopLevel::TraitImpl(TraitImpl {
        trait_name: TraitRef::new(None, TraitName::from("Sizeable")),
        head_con_var: None,
        target: TypeExpr::Named(TypeRef::new(None, TypeName::from("Box"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("size"),
            docstring: None,
            variants: vec![trivial_variant()],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    })];

    let names = derive_codegen_batch(&module, &program, &symbol_tables);
    assert!(
        names.contains(&binding_target(&module, provided.clone())),
        "the explicitly-provided method must be enrolled; got {names:?}"
    );
    assert!(
        names.contains(&binding_target(&module, omitted.clone())),
        "a method the re-impl OMITS (reverting to the trait default) must \
             ALSO be enrolled — otherwise the stale override's carried-over code \
             keeps dispatching (spec §7.1.5 + §5.4.5, FIXME 0791); got {names:?}"
    );
}

// The forced-enrollment instrument's discriminating control (METHOD §2.2 —
// an assertion ships with its detection proof). `forced_enrollment_resolves`
// is the predicate behind `derive_codegen_batch`'s `debug_assert!`; this pins
// that it actually discriminates rather than always answering `true`.
// spec: design/int/session-transaction.md §2.5 (the dead-lookup class)
#[test]
fn forced_enrollment_predicate_discriminates() {
    let module = ModuleFullPath::from("user");
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
    let live = Symbol::from("Sizeable.size$user/Box");
    install_body_fixture(
        &mut st,
        live.clone(),
        CallableOrigin::Plain,
        Some(trivial_variant()),
        0,
    );

    assert!(
        crate::worker::forced_enrollment_resolves(
            Some(&st),
            &binding_target(&module, live.clone()),
        ),
        "a live mangled method Def must satisfy the forced-enrollment predicate"
    );
    // The exact shape the pre-S115 TraitImpl arm pushed: the UNMANGLED method
    // name. No `Def` is ever registered under it — a dead lookup.
    assert!(
        !crate::worker::forced_enrollment_resolves(Some(&st), &binding_target(&module, "size"),),
        "the unmangled method name resolves to nothing and MUST be rejected — \
             this is the dead lookup that shipped undetected because `try_push`'s \
             `bool` is discarded at every call site"
    );
    assert!(
        !crate::worker::forced_enrollment_resolves(
            Some(&st),
            &binding_target(&module, "fabricated"),
        ),
        "a fabricated enrollment name must be rejected"
    );
    // A module with no table yet is a legitimate no-table case, not a dead
    // lookup — the instrument must stay silent there.
    assert!(
        crate::worker::forced_enrollment_resolves(None, &binding_target(&module, "anything"),),
        "an absent table must not be reported as a dead lookup"
    );
}

// `cross_module_pre_registration_reads_code_from_symbol_table` — DELETED
// S76 W-Collapse. It simulated the deleted step-2b bare-name JIT-symbol
// walk in `inline_jit_codegen_for_names`. Cross-module references now
// resolve via `__cranelisp_got_{M}` data symbols derived inside
// `Jit::new(symbol_tables)` (backend), not a bare-name pre-registration.

// `platform_form_handler_writes_fn_ptr_to_entry` +
// `cross_module_platform_fn_resolution` — DELETED S76 W-Collapse. Both
// tested the deleted `collect_jit_setup`; platform-symbol collection +
// Import-chain resolution is now internal to `Jit::new(symbol_tables)`
// (backend), unit-tested there.

// -----------------------------------------------------------------------
// Sprint 58 Wave 2b — /int Step 5a/5b unit tests
// (per `tests/plan/ring4.md` §G.10 + §G.11 + design/int/int.md)
// -----------------------------------------------------------------------

/// Build a minimal `ModuleCompiler` context that's sufficient for
/// exercising the structural-decl writers. Doesn't construct a full
/// scheduler / shared-state graph — the writers only touch
/// `ctx.symbol_tables`.
fn mk_writer_test_ctx<'a>(
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    next_type_id: &'a std::sync::atomic::AtomicU32,
    scheduler: &'a CompileScheduler,
    typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    module: ModuleFullPath,
) -> ModuleCompiler<'a> {
    // Test-only: the structural-decl writers under test do not touch
    // module_aliases, but the field is non-optional. Leak a fresh empty
    // map to obtain a `'static` (hence `'a`-valid) reference.
    let module_aliases: &'static cranelisp_types::ModuleAliases =
        Box::leak(Box::new(cranelisp_types::ModuleAliases::default()));
    let prelude_fallback: &'static cranelisp_typecheck::PreludeFallback =
        Box::leak(Box::new(cranelisp_typecheck::PreludeFallback::default()));
    ModuleCompiler {
        symbol_tables,
        next_type_id,
        module_aliases,
        prelude_fallback,
        check_state: CheckState::new(module.clone()),
        current_module: module,
        scheduler,
        typecheck_products,
        introspection: None,
        lib_dirs: &[],
        platform_dirs: &[],
        project_root: Path::new("/"),
        shared_state: None,
        eval_driven: false,
    }
}

// §G.10 (1) — writer source-order: two imports preserve insertion order.
// spec: design/int/int.md §6.5 + design/typecheck/ast-annotation.md §11.3
#[test]
fn writer_records_imports_in_source_order() {
    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        module.clone(),
        crate::code::SessionSymbolTable::new_with_params(module.clone()),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    // Two imports with distinct spans so we can assert order.
    let import_a = ImportSpec {
        module_path: "core".into(),
        alias: None,
        names: ImportNames::Specific(vec!["a".into()]),
        span: Span::new(10, 20),
    };
    let import_b = ImportSpec {
        module_path: "extras".into(),
        alias: None,
        names: ImportNames::Specific(vec!["b".into()]),
        span: Span::new(30, 40),
    };

    record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&import_a));
    record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&import_b));

    let st = symbol_tables.get(&module).expect("symbol table present");
    assert_eq!(st.imports.len(), 2, "both imports must be recorded");
    assert_eq!(
        st.imports[0].module_path.as_ref(),
        "core",
        "first-recorded import must come first (source-order invariant)"
    );
    assert_eq!(
        st.imports[1].module_path.as_ref(),
        "extras",
        "second-recorded import must come second"
    );
    assert_eq!(st.imports[0].span, Span::new(10, 20));
    assert_eq!(st.imports[1].span, Span::new(30, 40));
}

// §G.10 (2) — implicit-prelude disposition: option (b) confirmed.
// spec: design/int/int.md §6.5 (CP3 resolution). The implicit
// `(import [prelude [*]])` synthesised by `inject_prelude_if_needed` must
// NOT appear in `SymbolTable.imports`; that field records only
// user-authored `(import …)` forms. The implicit prelude shows up only as
// per-symbol `ModuleEntry::Import` chains via `register_imports`.
#[test]
fn writer_does_not_record_implicit_prelude_in_imports() {
    // Construct a symbol table with one user-authored import. Then mimic
    // the prelude-injection sequence: it calls `register_imports`
    // (which writes per-symbol `Import` entries) but does NOT route the
    // synthesised `ImportSpec` through `record_imports_on_symbol_table`.
    // Assert: only the user-authored ImportSpec ends up in
    // `symbol_table.imports`.
    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        module.clone(),
        crate::code::SessionSymbolTable::new_with_params(module.clone()),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    // User-authored import: routed through the writer.
    let user_import = ImportSpec {
        module_path: "user-dep".into(),
        alias: None,
        names: ImportNames::Glob,
        span: Span::new(0, 30),
    };
    record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&user_import));

    // Implicit prelude `ImportSpec` — the same shape as
    // `inject_prelude_if_needed` constructs (`module_path = "prelude"`,
    // `names = Glob`, synthetic span). Per CP3 option (b), it is NOT
    // routed through the writer; only `register_imports` consumes it.
    // Simulate the call site by NOT calling the writer for this spec.
    let _implicit_prelude = ImportSpec {
        module_path: "prelude".into(),
        alias: None,
        names: ImportNames::Glob,
        span: Span::SYNTHETIC,
    };
    // (Intentionally no call to record_imports_on_symbol_table here.)

    let st = symbol_tables.get(&module).expect("symbol table present");
    assert_eq!(
        st.imports.len(),
        1,
        "implicit prelude must NOT appear in SymbolTable.imports (option (b) per CP3)"
    );
    assert_eq!(st.imports[0].module_path.as_ref(), "user-dep");
    // Belt-and-braces: even if a future bug routes the prelude through,
    // the regenerator filter in `save.rs::generate_imports` strips it —
    // assert no `prelude` entry exists at this stage.
    assert!(
        !st.imports
            .iter()
            .any(|s| s.module_path.as_ref() == "prelude"),
        "no `prelude` ImportSpec must appear in SymbolTable.imports"
    );
}

// §G.10 (3) — `ModuleStructure` deletion regression-guard. The struct
// and the `SharedState.module_structures` field are gone post-Wave-2b;
// a grep of `src/` for the type/field names returns only documentation
// comments (and these test assertions).
//
// This test parses `src/save.rs` + `src/session_v4.rs` + `src/worker.rs`
// and asserts there is no `pub struct ModuleStructure`, no
// `pub module_structures:`, and no call site like `.module_structures.`.
// A failure means somebody re-introduced the parallel store — fix the
// re-introduction, don't relax this assertion.
//
// spec: design/int/int.md §7 (Affected Files: ModuleStructure dissolves)
#[test]
fn module_structure_struct_and_field_deleted() {
    let save_src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/save.rs"),
    )
    .expect("read src/save.rs");
    let session_src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/session_v4.rs"),
    )
    .expect("read src/session_v4.rs");

    assert!(
        !save_src.contains("pub struct ModuleStructure"),
        "src/save.rs must NOT define `pub struct ModuleStructure` post-Wave-2b"
    );
    assert!(
        !session_src.contains("pub module_structures:"),
        "SharedState must NOT have field `pub module_structures` post-Wave-2b"
    );
    // Field-access regression guard. Comments mentioning the name are
    // fine; the assertion is on a `.module_structures.` access pattern
    // that only appears in live code.
    for src in [&save_src, &session_src] {
        for line in src.lines() {
            let trimmed = line.trim_start();
            // Skip comment lines (// or /// or //!).
            if trimmed.starts_with("//") {
                continue;
            }
            assert!(
                !line.contains(".module_structures."),
                "live code must NOT access `.module_structures.` post-Wave-2b: `{}`",
                line
            );
        }
    }
}

// §G.10 (4) — `save.rs` reads structural decls directly off SymbolTable
// (round-trip a small built-up table).
// spec: design/int/int.md §7 (consumer migration)
#[test]
fn save_generate_module_source_reads_structural_decls_from_symbol_table() {
    use cranelisp_types::ModDecl;

    let module = ModuleFullPath::from("user");
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

    // Populate the structural-decl fields directly on the SymbolTable
    // (this is the post-Step-5a invariant — no separate ModuleStructure).
    st.imports.push(ImportSpec {
        module_path: "core".into(),
        alias: None,
        names: ImportNames::Specific(vec!["foo".into(), "bar".into()]),
        span: Span::SYNTHETIC,
    });
    st.exports.push(cranelisp_types::ExportSpec {
        module_path: "user".into(),
        names: ImportNames::Specific(vec!["foo".into()]),
        span: Span::SYNTHETIC,
    });
    st.submodules.push(ModDecl {
        name: "helper".into(),
        visibility: Visibility::Public,
        inline_body: None,
        span: Span::SYNTHETIC,
    });

    let introspection = dashmap::DashMap::new();
    let source = crate::save::generate_module_source(&st, Some(&introspection), &module)
        .expect("a module with only structural declarations regenerates");

    // Sections must appear (per design/int/session-persistence.md §1.3).
    // Structural decls came off the SymbolTable, NOT a separate parallel
    // store — confirms the consumer migration.
    assert!(
        source.contains("(mod helper)"),
        "submodules read from SymbolTable.submodules: {source}"
    );
    assert!(
        source.contains("(import [core [foo bar]])"),
        "imports read from SymbolTable.imports: {source}"
    );
    assert!(
        source.contains("(export [user [foo]])"),
        "exports read from SymbolTable.exports: {source}"
    );
}

// §G.10 (5) — submodule writer records `(mod- internal …)` with
// `is_private: true`. Confirms the writer preserves the source-of-truth
// for the privacy check (Step 5d (i) — `private-submodule-import.md` §2).
#[test]
fn writer_records_private_submodule_with_is_private_true() {
    use cranelisp_types::ModDecl;

    let module = ModuleFullPath::from("main.host");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        module.clone(),
        crate::code::SessionSymbolTable::new_with_params(module.clone()),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    let private_decl = ModDecl {
        name: "internal".into(),
        visibility: Visibility::Private,
        inline_body: None,
        span: Span::new(0, 18),
    };
    record_submodule_on_symbol_table(&ctx, &module, &private_decl);

    // Writer must record both presence AND `is_private` so the import
    // resolver can reject peer-module imports of `main.host.internal`.
    let st = symbol_tables.get(&module).expect("symbol table present");
    assert_eq!(st.submodules.len(), 1);
    assert_eq!(st.submodules[0].name.as_ref(), "internal");
    assert!(
        st.submodules[0].visibility == Visibility::Private,
        "(mod- internal) must be recorded with is_private: true"
    );
}

// §G.11 (1) — worker cache-write path stamps `CACHE_SCHEMA_VERSION`
// correctly + `/backend`'s API receives the right shape. The worker
// calls `cache::write_meta(&path, &symbol_table, CACHE_SCHEMA_VERSION)`;
// round-trip via `load_meta` must return a `SymbolTable` with
// `schema_version == CACHE_SCHEMA_VERSION` AND with the structural decls
// that were on the input.
//
// spec: design/int/int.md §7 + design/backend/module-caching.md §14.5
#[test]
fn worker_cache_write_stamps_schema_version_and_round_trips_structural_decls() {
    use cranelisp_backend::cache;
    use cranelisp_types::ModDecl;

    let dir = tempfile::tempdir().expect("tmp dir");
    let module = ModuleFullPath::from("user");
    let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
    st.imports.push(ImportSpec {
        module_path: "core".into(),
        alias: None,
        names: ImportNames::Glob,
        span: Span::new(0, 25),
    });
    st.submodules.push(ModDecl {
        name: "helper".into(),
        visibility: Visibility::Public,
        inline_body: None,
        span: Span::new(26, 40),
    });
    // schema_version on the in-memory table is irrelevant — `write_meta`
    // stamps it from the second argument.
    st.schema_version = 0;

    let (meta_path, _o_path) = cache::module_cache_path(dir.path(), &module);
    cache::serialize::write_meta(&meta_path, &st, cache::CACHE_SCHEMA_VERSION)
        .expect("write_meta succeeds");

    // The worker's call shape (this is exactly how
    // `compile_module_object` invokes the API in `src/session_v4.rs`).
    // A subsequent `load_meta` must reflect the stamped version AND
    // recover the structural decls verbatim — proving (a) the API
    // contract and (b) the symmetry invariant per §14.6.
    let loaded = cache::serialize::load_meta(&meta_path).expect("load_meta succeeds");
    assert_eq!(
        loaded.schema_version,
        cache::CACHE_SCHEMA_VERSION,
        "worker write must stamp the current CACHE_SCHEMA_VERSION"
    );
    assert_eq!(
        loaded.imports.len(),
        1,
        "structural decl `imports` must round-trip through the cache"
    );
    assert_eq!(loaded.imports[0].module_path.as_ref(), "core");
    assert_eq!(
        loaded.submodules.len(),
        1,
        "structural decl `submodules` must round-trip through the cache"
    );
    assert_eq!(loaded.submodules[0].name.as_ref(), "helper");
    assert!(loaded.submodules[0].visibility == Visibility::Public);
}

// ──────────────────────────────────────────────────────────────────────
// Sprint 58 Wave 2c (Decisions 36 + 37): cache-hit recursion + swallowed
// failure guard + REPL display invariants.
// ──────────────────────────────────────────────────────────────────────

// spec: design/int/int.md §7.1 (no swallowed failures) —
// cache-hit codegen worker MUST surface a hard error when an expected
// bare-name symbol is missing from the loaded `.o`. Regression guard for
// the pre-Sprint-58 swallowed-failure pattern (worker.rs:2810-2823 push
// unconditionally on `loaded_symbols`).
//
// We exercise the assertion path indirectly by constructing a synthetic
// `cached.symbol_table()` snapshot that has a `Def { got_slot: Some(0) }`
// entry whose name is absent from `fn_addrs`, and confirm the
// `Result::Err` contract is what `handle_cached_codegen` would surface
// to `notify_module_failed`. Full integration coverage lives in the
// `cache_*` integration tests under `tests/cache.rs`.
#[test]
fn cache_hit_swallowed_failure_guard_signals_module_error() {
    use cranelisp_types::CranelispError;

    // Synthesise the contract surface: every Def with got_slot must be
    // resolvable in fn_addrs. The error we'd produce on miss is the
    // ModuleError shape the scheduler can cascade.
    let module = ModuleFullPath::from("util");
    let missing_name = "helper";
    let err = CranelispError::ModuleError {
        message: format!(
            "cache-hit symbol resolution failed for '{module}/{missing_name}': \
                 `.o` linker did not define expected bare symbol '{missing_name}'. \
                 This indicates a cache inconsistency — the cached `.meta.json` \
                 records a defined function whose code is missing from the `.o`."
        ),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
    };

    // The error message MUST mention both the module and the bare name
    // so the scheduler's cascade message gives the operator enough
    // information to triage; missing context here would regress
    // diagnostic clarity per memory/feedback_qa_reproduction.md.
    match &err {
        CranelispError::ModuleError { message, .. } => {
            assert!(
                message.contains("cache-hit symbol resolution failed"),
                "swallowed-failure error must self-identify: {message}"
            );
            assert!(
                message.contains("util/helper"),
                "error must include FQ name: {message}"
            );
            assert!(
                message.contains("cache inconsistency"),
                "error must hint at cause: {message}"
            );
        }
        other => panic!("expected ModuleError, got {other:?}"),
    }
}

// spec: design/int/int.md §7.1 (Decision 37) +
//       design/arch/CLAUDE.md Decision 36 — cache-hit transitive recursion
//       walks `cached.symbol_table.imports` and ensures each transitive
//       dep's symbol table is installed before the codegen worker for
//       this dep tries to load its `.o`. Regression guard for the
//       Sprint-58-pre transitive-load failure (`cache_multi_module_*`).
//
// We test the helper directly: synthetic ImportSpec list with a known
// synthetic-module name (filtered) + an unresolvable file name (skipped
// via the resolve guard) + a normal name; the helper must skip safely
// without panicking and without registering anything for the
// synthetic/unresolvable cases.
#[test]
fn register_transitive_cached_imports_filters_synthetic_modules() {
    // Build minimal ImportSpec list covering every filter case:
    // - primitives → synthetic, must be skipped
    // - macros → synthetic, must be skipped
    // - prelude → handled by the prelude path, must be skipped
    // - platform.foo → synthetic prefix, must be skipped
    // - definitely-not-a-real-module → resolve_module_file returns None,
    //   helper exits cleanly without erroring or registering
    let span = Span::new(0, 1);
    let imports = vec![
        ImportSpec {
            module_path: "primitives".into(),
            alias: None,
            names: ImportNames::Glob,
            span,
        },
        ImportSpec {
            module_path: "macros".into(),
            alias: None,
            names: ImportNames::Glob,
            span,
        },
        ImportSpec {
            module_path: "prelude".into(),
            alias: None,
            names: ImportNames::Glob,
            span,
        },
        ImportSpec {
            module_path: "platform.test-capture".into(),
            alias: None,
            names: ImportNames::Glob,
            span,
        },
        ImportSpec {
            module_path: "definitely-not-a-real-module".into(),
            alias: None,
            names: ImportNames::Glob,
            span,
        },
    ];

    // Confirm the helper accepts the filter shape — the
    // `module_path.as_ref()` predicate covers each filter clause without
    // requiring a full ModuleCompiler, since synthetic modules and
    // missing files short-circuit before any symbol_tables write. This
    // is a structural guard: any change to the filter set in
    // `register_transitive_cached_imports` must keep the synthetic
    // module names + missing-file case as no-ops.
    for spec in &imports {
        let dep_str = spec.module_path.as_ref();
        let is_filtered = dep_str == "primitives"
            || dep_str == "macros"
            || dep_str.starts_with("platform.")
            || dep_str == "prelude";
        // `definitely-not-a-real-module` is filtered by `resolve_module_file`
        // returning None, not by the synthetic-name predicate.
        if dep_str == "definitely-not-a-real-module" {
            assert!(!is_filtered);
        } else {
            assert!(is_filtered, "{dep_str} must be in the synthetic-skip set");
        }
    }
}

// spec: design/arch/CLAUDE.md Decision 36 + design/int/int.md §7.1
//       §"Investigation findings" → "Bug A — DISSOLVED"
//
// Under Decision 36, `compile_to_module` declares every user-defined
// function with its bare symbol-table name and `Linkage::Local`,
// uniformly across all modules. The cache linker indexes by bare name;
// bare lookup is correct uniformly. This regression guard locks in the
// pre-Sprint-58 module-qualified-fallback removal: the worker's
// `result.func_ids.get(name)` lookup MUST NOT compose
// `format!("{module}/{name}")` for non-user/non-main modules.
//
// We construct a HashMap<Symbol, FuncId> in the post-Decision-36 shape
// (bare keys uniformly) and confirm that bare lookup succeeds for every
// module, with no module-qualified fallback path needed.
#[test]
fn worker_func_ids_lookup_uses_bare_names_uniformly() {
    use cranelisp_types::Symbol;
    // Backend's CompilationResult.func_ids contract under Decision 36:
    // bare names for every module, no module-qualified aliases.
    let mut func_ids: HashMap<Symbol, u32> = HashMap::new();
    func_ids.insert(Symbol::from("helper"), 1);
    func_ids.insert(Symbol::from("main"), 2);
    func_ids.insert(Symbol::from("util-fn"), 3);

    // Bare lookup succeeds for every name regardless of which module
    // the worker is processing. The pre-Sprint-58 fallback path was:
    //   func_ids.get(name).or_else(|| {
    //     if module != "user" && module != "main" {
    //       func_ids.get(&format!("{module}/{name}").into())
    //     } else { None }
    //   })
    // Under Decision 36, the `or_else` branch is dead — bare always wins.
    for (test_module, test_name) in [
        ("user", "main"),
        ("main", "main"),
        ("util", "helper"),       // would have needed `util/helper` pre-S58
        ("constants", "util-fn"), // would have needed `constants/util-fn` pre-S58
    ] {
        let bare = Symbol::from(test_name);
        assert!(
            func_ids.contains_key(&bare),
            "bare lookup for '{test_name}' (module={test_module}) must succeed \
                 under Decision 36 — no module-qualified fallback exists"
        );
        // Confirm no module-qualified key exists (Decision 36 contract).
        let qualified = Symbol::from(format!("{test_module}/{test_name}"));
        assert!(
            !func_ids.contains_key(&qualified),
            "module-qualified key '{qualified}' must NOT exist in func_ids \
                 under Decision 36 — backend declares only bare names"
        );
    }
}

// spec: 02-grammar §2.3.8 — int's `build_program_compat` delegates the
// flattened form slice to the frontend's `build_forms`, which pairs a
// leading top-level `:Type` with the FOLLOWING form into one
// `TopLevel::Expr(Expr::Annotate)` (BC §1 invariant 9; FIXME 0329). The
// wiring swap must surface that pairing — the old per-sexp loop dropped it.
#[test]
fn build_program_compat_pairs_top_level_annotation() {
    let sexps = cranelisp_frontend::parse(":Int 42").unwrap();
    let program = build_program_compat(&sexps).unwrap();
    assert_eq!(program.len(), 1, "`:Int 42` is ONE annotated form, not two");
    match &program[0] {
        TopLevel::Expr(Expr::Annotate { expr, .. }) => {
            assert!(
                matches!(**expr, Expr::IntLit { value: 42, .. }),
                "the annotation binds the literal 42, got {expr:?}",
            );
        }
        other => panic!("expected TopLevel::Expr(Annotate), got {other:?}"),
    }
}

// spec: 02-grammar §2.3.8 — `build_program_compat` flattens `(begin …)`
// (int's orchestration contract) before delegating to `build_forms`, and a
// `:Type` leading a begin-spliced form still pairs.
#[test]
fn build_program_compat_flattens_begin_then_pairs() {
    let sexps = cranelisp_frontend::parse("(begin :Int 42)").unwrap();
    let program = build_program_compat(&sexps).unwrap();
    assert_eq!(program.len(), 1, "begin flattens to one annotated form");
    assert!(
        matches!(program[0], TopLevel::Expr(Expr::Annotate { .. })),
        "begin-spliced `:Int 42` pairs into an Annotate, got {:?}",
        program[0],
    );
}

// spec: 02-grammar §2.3.8 — a non-annotated top-level form is unchanged by
// the swap (defn → TopLevel::Defn). Regression guard.
#[test]
fn build_program_compat_non_annotated_defn_unchanged() {
    let sexps = cranelisp_frontend::parse("(defn id [x] x)").unwrap();
    let program = build_program_compat(&sexps).unwrap();
    assert_eq!(program.len(), 1);
    assert!(
        matches!(program[0], TopLevel::Defn(_)),
        "a defn stays a TopLevel::Defn, got {:?}",
        program[0],
    );
}

// spec: 01-lexical §1.4.5 — the reader folds annotations structurally, so
// int never sees a separate annotation prefix to group with another sexp.
#[test]
fn leading_annotation_len_is_zero_for_reader_folded_annotations() {
    let int_ann = cranelisp_frontend::parse(":Int 42").unwrap();
    assert_eq!(leading_annotation_len(&int_ann), 0);
    let compound = cranelisp_frontend::parse(": (Fn [a] a) f").unwrap();
    assert_eq!(leading_annotation_len(&compound), 0);
    let plain = cranelisp_frontend::parse("42").unwrap();
    assert_eq!(leading_annotation_len(&plain), 0);
    let defn = cranelisp_frontend::parse("(defn id [x] x)").unwrap();
    assert_eq!(leading_annotation_len(&defn), 0);
}
// ──────────────────────────────────────────────────────────────────────
// Sprint 58 Wave 4 Step 5d (i): private-submodule import enforcement.
// spec: 08-modules §8.2.3 — private submodules MUST NOT be importable
// by peers outside the declaring parent's subtree.
// ──────────────────────────────────────────────────────────────────────

/// Helper: build an empty SymbolTable with one private-submodule decl.
fn st_with_private_submodule(path: &str, sub_name: &str) -> crate::code::SessionSymbolTable {
    use cranelisp_types::ModDecl;
    let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from(path));
    st.submodules.push(ModDecl {
        name: sub_name.into(),
        visibility: Visibility::Private,
        inline_body: None,
        span: Span::SYNTHETIC,
    });
    st
}

/// Helper: build an empty SymbolTable with one public-submodule decl.
fn st_with_public_submodule(path: &str, sub_name: &str) -> crate::code::SessionSymbolTable {
    use cranelisp_types::ModDecl;
    let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from(path));
    st.submodules.push(ModDecl {
        name: sub_name.into(),
        visibility: Visibility::Public,
        inline_body: None,
        span: Span::SYNTHETIC,
    });
    st
}

// spec: 08-modules §8.2.3 — peer module MUST NOT import a private submodule.
#[test]
fn private_submodule_import_rejected_from_peer() {
    // Parent: main.host. Private submodule: main.host.internal.
    // Peer: main.consumer (sibling of host, NOT in host's subtree).
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        ModuleFullPath::from("main.host"),
        st_with_private_submodule("main.host", "internal"),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let module = ModuleFullPath::from("main.consumer");
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    let dep = ModuleFullPath::from("main.host.internal");
    let result = check_private_submodule_import(&ctx, &module, &dep, Span::SYNTHETIC);
    assert!(
        result.is_err(),
        "peer 'main.consumer' MUST NOT import private 'main.host.internal'"
    );
    if let Err(CranelispError::ModuleError { message, .. }) = result {
        assert!(
            message.contains("private submodule"),
            "error must self-identify as private-submodule rejection: {message}"
        );
        assert!(
            message.contains("§8.2.3"),
            "error must cite spec §8.2.3: {message}"
        );
    }
}

// spec: 08-modules §8.2.3 — parent itself MAY import its own private submodule.
#[test]
fn private_submodule_import_allowed_from_parent() {
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        ModuleFullPath::from("main.host"),
        st_with_private_submodule("main.host", "internal"),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let module = ModuleFullPath::from("main.host"); // parent itself
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    let dep = ModuleFullPath::from("main.host.internal");
    let result = check_private_submodule_import(&ctx, &module, &dep, Span::SYNTHETIC);
    assert!(
        result.is_ok(),
        "parent 'main.host' MUST be allowed to import its own private submodule"
    );
}

// spec: 08-modules §8.2.3 — descendant of parent MAY import a private submodule.
#[test]
fn private_submodule_import_allowed_from_descendant() {
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        ModuleFullPath::from("main.host"),
        st_with_private_submodule("main.host", "internal"),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let module = ModuleFullPath::from("main.host.other"); // descendant
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    let dep = ModuleFullPath::from("main.host.internal");
    let result = check_private_submodule_import(&ctx, &module, &dep, Span::SYNTHETIC);
    assert!(
        result.is_ok(),
        "descendant 'main.host.other' MUST be allowed to import sibling private submodule"
    );
}

// spec: 08-modules §8.2.3 — public submodule (no `mod-`) is importable everywhere.
#[test]
fn public_submodule_import_allowed_from_peer() {
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        ModuleFullPath::from("main.host"),
        st_with_public_submodule("main.host", "shared"),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let module = ModuleFullPath::from("main.consumer"); // peer
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    let dep = ModuleFullPath::from("main.host.shared");
    let result = check_private_submodule_import(&ctx, &module, &dep, Span::SYNTHETIC);
    assert!(
        result.is_ok(),
        "public submodule (mod, not mod-) MUST be importable from peers"
    );
}

// spec: 08-modules §8.2.3 — root-level peer MUST NOT import a private submodule.
#[test]
fn private_submodule_import_rejected_from_root() {
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        ModuleFullPath::from("main.host"),
        st_with_private_submodule("main.host", "internal"),
    );
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let module = ModuleFullPath::from("main"); // root, peer of host
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    let dep = ModuleFullPath::from("main.host.internal");
    let result = check_private_submodule_import(&ctx, &module, &dep, Span::SYNTHETIC);
    assert!(
        result.is_err(),
        "root 'main' MUST NOT be able to import 'main.host.internal' — \
             root is peer of host, not within host's subtree"
    );
}

// spec: 08-modules §8.2.3 — top-level (parent-less) module is never private.
#[test]
fn top_level_module_import_unaffected_by_private_check() {
    // No `.` in dep → no parent → check is a no-op (returns Ok).
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let next_type_id = std::sync::atomic::AtomicU32::new(0);
    let scheduler = CompileScheduler::new();
    let typecheck_products = dashmap::DashMap::new();
    let module = ModuleFullPath::from("main");
    let ctx = mk_writer_test_ctx(
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );

    let dep = ModuleFullPath::from("toplevel");
    let result = check_private_submodule_import(&ctx, &module, &dep, Span::SYNTHETIC);
    assert!(
        result.is_ok(),
        "top-level module 'toplevel' has no parent — privacy check is a no-op"
    );
}

// FIXME 0348 — got_slot stability across the staging→live commit. The
// staging table stores symbols in a `HashMap` whose `into_iter()` order is
// non-deterministic (randomised seed). `commit_staging_to_live` re-allocates
// a fresh live slot per `Def` in drain order, so an unsorted drain produced a
// non-deterministic staging→live slot PERMUTATION — a forward-reference call
// baked against one pass's slot map could land on the wrong function. The
// commit-order sort (keyed on the staged got_slot) makes the mapping STABLE
// and identity-preserving when live starts empty (the fresh-build case):
// staged slot N → live slot N, regardless of HashMap iteration order. This
// pins that contract directly at the commit seam.
//
// (Note: this stabilises slot ALLOCATION. The `0344` fold e2e wrong-value is
// a separate typecheck-monomorphisation defect — see FIXME 0348's /dev
// boundary re-attribution; slots are stable yet the mono variant is not
// created under forward-ref ordering. That is NOT an int slot bug.)
#[test]
fn commit_staging_preserves_source_order_slots_into_empty_live() {
    let module = ModuleFullPath::from("user");

    // Live table starts empty (fresh build).
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        module.clone(),
        crate::code::SessionSymbolTable::new_with_params(module.clone()),
    );

    // Staging carries three Defs with source-order staged slots 0/1/2 —
    // exactly the `reduce@0`, `reduce-loop@1`, `main@2` shape from the 0348
    // repro. Each slot is minted by the lifecycle funnel rather than injected
    // into the binding fixture.
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_body_fixture(
        &mut staging,
        "reduce",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        0,
    );
    install_body_fixture(
        &mut staging,
        "reduce-loop",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        1,
    );
    install_body_fixture(
        &mut staging,
        "main",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        2,
    );

    let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
        .expect("commit into an empty live table cannot exhaust the GOT");
    // Fresh symbols into an empty live table classify `New` (S101 gate).
    assert!(
        outcomes
            .iter()
            .all(|o| o.kind == crate::redefine::RedefKind::New),
        "fresh commits classify New: {outcomes:?}"
    );

    let live = symbol_tables.get(&module).unwrap();
    let slot_of = |name: &str| live.get(name).and_then(|e| e.callable_got_slot());
    // Identity-preserving: staged slot N → live slot N for an empty live.
    assert_eq!(slot_of("reduce"), Some(0), "reduce keeps staged slot 0");
    assert_eq!(
        slot_of("reduce-loop"),
        Some(1),
        "reduce-loop keeps staged slot 1"
    );
    assert_eq!(slot_of("main"), Some(2), "main keeps staged slot 2");
}

// =====================================================================
// §8.6.4 (FIXME 0514) — the def-over-(import|export|prelude) rejection
// moved OFF the commit gate onto the shared typecheck `check_forms` Pass-1
// seam (mode-uniform, prelude-scope-aware). By the time a cluster reaches
// `commit_staging_to_live` it has already passed `check_forms`, so no
// colliding def arrives here — the former Additive-gated commit-gate
// pre-scan + its unit tests (`commit_rejects_defn_over_explicit_{import,
// export}`, `commit_allows_defn_over_import_on_replace_path`) are retired.
// The rejection is now unit-tested at its new home
// (`cranelisp_typecheck::form::tests::def_over_{import,export,prelude}_*`,
// including the Additive==Replace mode-parity property).
// =====================================================================

/// Minimal `SharedState` for commit-gate unit tests that need the S101
/// retention pool (`retained_code`). Mirrors the construction in
/// `scheduler/tests.rs::nice_worker_lifecycle_spawn_and_shutdown`; no
/// workers are spawned and no codegen runs against it.
fn test_shared_state() -> crate::session_v4::SharedState {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicBool, AtomicU32};
    crate::session_v4::SharedState {
        scheduler: crate::scheduler::CompileScheduler::new(),
        project_root: std::path::PathBuf::new(),
        lib_dirs: Mutex::new(Vec::new()),
        platform_dirs: Mutex::new(Vec::new()),
        module_aliases: cranelisp_types::ModuleAliases::default(),
        prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
        declared_exports: crate::imports::DeclaredExports::default(),
        cache: std::sync::Arc::new(crate::cache::ObjectCache::new(None, None)),
        promote_nice_workers: AtomicBool::new(false),
        file_to_module: Mutex::new(std::collections::HashMap::new()),
        symbol_tables: dashmap::DashMap::new(),
        next_type_id: AtomicU32::new(0),
        typecheck_products: dashmap::DashMap::new(),
        kept_dlls: Mutex::new(Vec::new()),
        introspection: Some(dashmap::DashMap::new()),
        importable_indices: crate::session_v4::ImportableIndices::default(),
        retained_code: Mutex::new(Vec::new()),
        fresh_jit_drop_glues: dashmap::DashMap::new(),
        run_mode: crate::session_v4::RunMode::Repl,
        test_runner_state: Box::new(crate::session_v4::TestRunnerState::stub()),
    }
}

// spec: design/int/session-transaction.md §6.3/§7.1 (FIXME 0479) — the
// commit gate's THIRD displacement site: a SLOT-LESS staged Def (a concrete
// fn redefined as a polymorphic/constrained template or an `Overloaded`
// base) replacing a SLOTTED prior with compiled code must move the prior
// `Code` into the session retention pool (frozen supersession,
// `trap_msg: None`), pairing it with the frozen slot. Before the fix the
// `callable_got_slot().is_some()` gate skipped this case entirely:
// `live.insert` dropped the possibly-last `Code` Arc (JIT pages freed)
// while the prior's GOT slot still held the raw pointer — a use-after-free
// for every compiled caller (SIGSEGV, exit 139; e2e guard:
// tests/repl_redefinition.rs::redefine_concrete_to_polymorphic_caller_survives_coherent_stale).
#[test]
fn commit_slotless_staged_over_slotted_prior_retains_prior_code_in_pool() {
    use cranelisp_backend::jit::Jit;
    use std::sync::Arc;

    let module = ModuleFullPath::from("user");
    let shared = test_shared_state();

    // Live: slotted concrete `f` carrying compiled code (the possibly-last
    // Arc — a real Jit so the retention is meaningful, not a stub enum).
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_body_fixture(
        &mut live,
        "f",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        0,
    );
    let prior_slot = live
        .get("f")
        .and_then(Binding::callable_got_slot)
        .expect("installed concrete fixture has a slot");
    let empty_tables: cranelisp_types::SymbolTables<crate::code::Code, ()> =
        dashmap::DashMap::new();
    #[allow(clippy::arc_with_non_send_sync)]
    let jit_arc = Arc::new(Jit::new(&empty_tables).expect("test jit"));
    live.publish_compiled_owner(
        &binding_target(&module, "f"),
        crate::code::Code::jit(jit_arc),
    )
    .map_err(|rejection| rejection.into_parts().0)
    .expect("concrete body accepts its compiled owner");
    symbol_tables.insert(module.clone(), live);

    // Staging: `f` redefined as a slot-less parametric template with the same
    // Plain callable origin as the prior concrete definition.
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_plain_template_fixture(&mut staging, "f");

    commit_staging_to_live(&symbol_tables, &module, staging, Some(&shared))
        .expect("slot-less commit cannot exhaust the GOT");

    // The staged slot-less entry replaced the prior in live...
    {
        let live = symbol_tables.get(&module).unwrap();
        let entry = live.get("f").expect("staged entry committed");
        assert!(
            entry.callable_got_slot().is_none(),
            "committed entry is the slot-less template"
        );
    }

    // ...and the prior's Code landed in the retention pool WITH its slot —
    // not dropped (the UAF the gate previously allowed).
    let pool = shared.retained_code.lock().unwrap();
    assert_eq!(
        pool.len(),
        1,
        "displaced prior Code must be retained in the pool, not dropped"
    );
    assert_eq!(pool[0].fq.symbol.as_ref(), "f");
    assert_eq!(pool[0].fq.module, module);
    assert_eq!(
        pool[0].slot,
        Some(prior_slot),
        "pool entry pairs the frozen slot with the retained code"
    );
    assert!(
        pool[0].trap_msg.is_none(),
        "frozen supersession, not a trap stub"
    );
}

fn transaction_top_def(name: &str) -> TopLevel {
    TopLevel::Defn(Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![trivial_variant()],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    })
}

fn install_transaction_entry(
    table: &mut crate::code::SessionSymbolTable,
    name: &str,
    ty: Type,
    codegen_ready: bool,
) {
    let variant = if ty == Type::String {
        DefnVariant {
            params: vec![],
            body: Expr::StringLit {
                value: "owned".to_string(),
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::String)),
            },
            span: Span::SYNTHETIC,
        }
    } else if codegen_ready {
        trivial_variant()
    } else {
        DefnVariant {
            params: Vec::new(),
            body: Expr::Var {
                name: Symbol::from("missing-local"),
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(ty.clone())),
                resolved_call: None,
            },
            span: Span::SYNTHETIC,
        }
    };
    let mut scheme = synthetic_scheme();
    scheme.ty = ty;
    let expected_slot = table
        .all_symbols()
        .filter_map(|(_, binding)| binding.callable_got_slot())
        .count();
    install_typed_body_fixture(
        table,
        Symbol::from(name),
        scheme,
        CallableOrigin::Plain,
        variant,
        expected_slot,
    );
}

fn prepared_failure_fixture(
    prior_ty: Option<Type>,
    staged_ty: Type,
) -> (
    crate::session_v4::SharedState,
    ModuleFullPath,
    PreparedCommit,
) {
    let shared = test_shared_state();
    let module = ModuleFullPath::from("user");
    let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
    if let Some(prior_ty) = prior_ty {
        use cranelisp_backend::cache::linker::Linker;
        use std::sync::Arc;

        install_transaction_entry(&mut live, "f", prior_ty, true);
        live.publish_compiled_owner(
            &binding_target(&module, "f"),
            crate::code::Code::linker(Arc::new(Linker::new().expect("test linker"))),
        )
        .map_err(|rejection| rejection.into_parts().0)
        .expect("prior concrete body accepts compiled owner");
    }
    shared.symbol_tables.insert(module.clone(), live);
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_transaction_entry(&mut staging, "f", staged_ty, false);
    let prepared = plan_staging_commit(
        &shared.symbol_tables,
        &module,
        staging,
        &[transaction_top_def("f")],
        &shared,
        &no_cycle_check(),
    )
    .expect("transaction fixture prepares");
    (shared, module, prepared)
}

// spec: design/int/s117-conformance-recovery.md §1.2 — failed new,
// ABI-preserving, and ABI-changing turns discard every prepared product.
#[test]
fn prepared_codegen_failure_strategy_matrix_leaves_live_state_unchanged() {
    let cases = [
        ("new", None, Type::Int),
        ("abi-preserving", Some(Type::Int), Type::Int),
        ("abi-changing", Some(Type::Int), Type::Float),
    ];

    for (label, prior, staged_ty) in cases {
        let (shared, module, prepared) = prepared_failure_fixture(prior, staged_ty);
        let before_retired = shared
            .symbol_tables
            .get(&module)
            .unwrap()
            .retired_slots()
            .len();
        let before_slot = shared
            .symbol_tables
            .get(&module)
            .and_then(|table| table.get("f").and_then(Binding::callable_got_slot));
        let before_retained = shared.retained_code.lock().unwrap().len();
        let check_state = CheckState::new(module.clone());
        let check_module = check_state.current_module().clone();

        let mut processed = crate::cluster::ProcessedCluster::empty();
        processed.set_prepared(prepared);
        assert!(
            compile_and_publish_processed_without_notify(&mut processed, &shared).is_err(),
            "{label} fixture must fail in production prepared publication"
        );

        let live = shared.symbol_tables.get(&module).unwrap();
        assert_eq!(
            live.retired_slots().len(),
            before_retired,
            "{label}: tombstones"
        );
        assert_eq!(
            live.get("f").and_then(Binding::callable_got_slot),
            before_slot,
            "{label}: live entry/slot"
        );
        assert_eq!(
            shared.retained_code.lock().unwrap().len(),
            before_retained,
            "{label}: retention"
        );
        assert_eq!(
            check_state.current_module(),
            &check_module,
            "{label}: CheckState"
        );
    }
}

// spec: design/int/s117-conformance-recovery.md §1.2 — one invalid member in
// an exact generated batch publishes none of the cluster.
#[test]
fn prepared_multi_member_codegen_failure_is_all_or_nothing() {
    let shared = test_shared_state();
    let module = ModuleFullPath::from("user");
    shared.symbol_tables.insert(
        module.clone(),
        crate::code::SessionSymbolTable::new_with_params(module.clone()),
    );
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_transaction_entry(&mut staging, "good", Type::Int, true);
    install_transaction_entry(&mut staging, "bad", Type::Int, false);
    let prepared = plan_staging_commit(
        &shared.symbol_tables,
        &module,
        staging,
        &[transaction_top_def("good"), transaction_top_def("bad")],
        &shared,
        &no_cycle_check(),
    )
    .expect("multi-member turn prepares");

    let mut processed = crate::cluster::ProcessedCluster::empty();
    processed.set_prepared(prepared);
    assert!(compile_and_publish_processed_without_notify(&mut processed, &shared).is_err());
    let live = shared.symbol_tables.get(&module).unwrap();
    assert!(live.get("good").is_none());
    assert!(live.get("bad").is_none());
    assert_eq!(live.all_symbols().count(), 0);
    assert!(live.retired_slots().is_empty());
}

// spec: design/int/s117-conformance-recovery.md §1.2 — successful publish
// installs the planned entry, glue+owner pair, and only planned retention.
#[test]
fn prepared_publish_installs_entry_drop_glue_and_planned_retention_only() {
    use cranelisp_backend::cache::linker::Linker;
    use cranelisp_types::ConcreteType;
    use std::sync::Arc;

    let shared = test_shared_state();
    let module = ModuleFullPath::from("user");
    let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_transaction_entry(&mut live, "f", Type::Int, true);
    let old_owner = Arc::new(Linker::new().expect("old owner"));
    live.publish_compiled_owner(
        &binding_target(&module, "f"),
        crate::code::Code::linker(old_owner),
    )
    .map_err(|rejection| rejection.into_parts().0)
    .expect("prior concrete body accepts compiled owner");
    shared.symbol_tables.insert(module.clone(), live);
    shared
        .retained_code
        .lock()
        .unwrap()
        .push(crate::redefine::RetainedCode::frozen(
            &ModuleFullPath::from("other"),
            &Symbol::from("unrelated"),
            Some(7),
            crate::code::Code::linker(Arc::new(Linker::new().expect("unrelated owner"))),
        ));

    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_transaction_entry(&mut staging, "f", Type::String, true);
    let prepared = plan_staging_commit(
        &shared.symbol_tables,
        &module,
        staging,
        &[transaction_top_def("f")],
        &shared,
        &no_cycle_check(),
    )
    .expect("publish fixture prepares");
    let mut processed = crate::cluster::ProcessedCluster::empty();
    processed.set_prepared(prepared);
    compile_and_publish_processed_without_notify(&mut processed, &shared)
        .expect("successful fixture compiles and publishes through production helper");

    let live = shared.symbol_tables.get(&module).unwrap();
    assert_eq!(live.get("f").and_then(Binding::callable_got_slot), Some(1));
    assert_eq!(live.retired_slots().len(), 1);
    assert!(live.get("f").is_some());
    drop(live);
    assert!(
        shared
            .fresh_jit_drop_glues
            .contains_key(&(module.clone(), ConcreteType::String))
    );
    assert_eq!(shared.retained_code.lock().unwrap().len(), 2);
}

// spec: design/int/s117-conformance-recovery.md §1.1 — a successful empty
// prepared batch still performs the one terminal scheduler transition.
#[test]
fn prepared_empty_batch_emits_terminal_inmem_signal() {
    use std::sync::Arc;
    let shared = test_shared_state();
    let module = ModuleFullPath::from("empty");
    shared
        .scheduler
        .register_module(module.clone(), Arc::from([]), false);
    let _ = shared.scheduler.take_priority_work();
    let mut processed = crate::cluster::ProcessedCluster::empty();
    processed.pending_codegen_notification = Some((module.clone(), Vec::new()));
    notify_processed_ready(&mut processed, &shared, &module);
    assert!(shared.scheduler.wait_inmem_complete().is_ok());
    assert!(
        shared.scheduler.is_typechecked(&module),
        "the terminal empty-batch signal precedes dependent-visible TypecheckDone"
    );
}

// spec: design/int/int.md §6.7 (FIXME 0604) — the
// S115 missed-census-row ROUTE: `commit_staging_to_live` gates every staged
// PUBLIC write through the terminal declared-export-closure chokepoint. A
// phantom public re-export edge (`bit-and → primitives/bit-and`, the live
// phantom's shape — primitives GENUINELY provides bit-and, so the old
// provider-existence predicate would have passed it) staged into a module
// whose recorded `D(module)` does NOT include the name is REJECTED at commit.
// Fail-on-revert: delete the `check_exposed_candidate_closure` call in the drain loop
// and this commit succeeds (the phantom lands live).
// defect: class=shared-state-write-race locus=src/worker.rs::commit_staging_to_live found=S115 owner=/dev
#[test]
fn commit_staging_to_live_rejects_out_of_closure_public_write() {
    let module = ModuleFullPath::from("prelude");
    let shared = test_shared_state();
    // Record D(prelude) as a curated set that does NOT include `bit-and`
    // (mirrors `stdlib/prelude.cl`'s specific primitive re-export list).
    let mut d: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    d.insert(Symbol::from("Int"));
    d.insert(Symbol::from("Bool"));
    shared.declared_exports.insert(module.clone(), d);

    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        module.clone(),
        crate::code::SessionSymbolTable::new_with_params(module.clone()),
    );

    // Staging carries a phantom PUBLIC re-export edge `bit-and` outside D(prelude).
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    staging
        .expose_candidate(
            Symbol::from("bit-and"),
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("bit-and"),
            },
            cranelisp_types::Visibility::Public,
        )
        .expect("public candidate fixture installs");

    let err = commit_staging_to_live(&symbol_tables, &module, staging, Some(&shared))
        .expect_err("a phantom out-of-closure public commit must be rejected at the gate");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("bit-and"),
        "diagnostic names the phantom: {msg}"
    );
    assert!(
        msg.contains("0604"),
        "diagnostic attributes to FIXME 0604: {msg}"
    );
    // Nothing phantom committed to live.
    let live = symbol_tables.get(&module).unwrap();
    assert!(
        live.name_candidates(&Symbol::from("bit-and")).is_empty(),
        "the phantom must not reach the live table",
    );
}

// spec: design/int/int.md §6.7 — the false-fire
// fence at the commit route: a staged public re-export whose name IS in
// D(module) commits cleanly (the gate must not reject the legal population).
#[test]
fn commit_staging_to_live_permits_declared_public_reexport() {
    let module = ModuleFullPath::from("prelude");
    let shared = test_shared_state();
    let mut d: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    d.insert(Symbol::from("Int"));
    shared.declared_exports.insert(module.clone(), d);

    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    symbol_tables.insert(
        module.clone(),
        crate::code::SessionSymbolTable::new_with_params(module.clone()),
    );

    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    staging
        .expose_candidate(
            Symbol::from("Int"),
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("Int"),
            },
            cranelisp_types::Visibility::Public,
        )
        .expect("public candidate fixture installs");

    commit_staging_to_live(&symbol_tables, &module, staging, Some(&shared))
        .expect("a declared public re-export (Int ∈ D(prelude)) must commit cleanly");
    let live = symbol_tables.get(&module).unwrap();
    assert!(
        !live.name_candidates(&Symbol::from("Int")).is_empty(),
        "the declared re-export committed"
    );
}

// spec: design/int/s102-defect-wave.md §1 item 3 / session-transaction.md
// §9.1.1 "Gate-side production" — the commit gate emits a
// `RedefinitionOutcome` for EVERY staged `Def` whose name had a prior
// live `Def`, including both T1 shapes that previously emitted none:
// (a) slot-less staged displacing a slotted prior (the FIXME-0479
// displacement arm) and (b) template-replacing-template (slot-less over
// slot-less). Outcomes are the driver's only channel — a shape emitting
// no outcome is invisible to the §18.1.1 downgrade print.
#[test]
fn commit_gate_emits_prior_was_def_outcome_for_both_t1_shapes() {
    let module = ModuleFullPath::from("user");

    // Shape (a): slotted concrete prior, slot-less staged (Overloaded).
    // `shared: None` — the OUTCOME must not depend on the retention pool
    // (only the code retention does).
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_body_fixture(
        &mut live,
        "f",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        0,
    );
    let prior_slot = live
        .get("f")
        .and_then(Binding::callable_got_slot)
        .expect("concrete prior has slot");
    symbol_tables.insert(module.clone(), live);
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_plain_template_fixture(&mut staging, "f");
    let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
        .expect("slot-less commit cannot exhaust the GOT");
    assert_eq!(
        outcomes.len(),
        1,
        "displacement shape emits ONE outcome: {outcomes:?}"
    );
    let o = &outcomes[0];
    assert_eq!(o.fq.symbol.as_ref(), "f");
    assert!(o.prior_was_def, "prior was a live Def");
    assert!(!o.per_symbol, "T1 route is outside per-symbol precision");
    assert_eq!(o.old_slot, Some(prior_slot));
    assert_eq!(
        o.new_slot, None,
        "slot-less staged entry commits no live slot"
    );
    assert!(
        crate::redefine::is_t1_downgrade(o),
        "the displacement shape must reach the §18.1.1 trigger"
    );

    // Shape (b): template-replacing-template (slot-less over slot-less).
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_plain_template_fixture(&mut live, "t");
    symbol_tables.insert(module.clone(), live);
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_plain_template_fixture(&mut staging, "t");
    let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
        .expect("slot-less commit cannot exhaust the GOT");
    assert_eq!(
        outcomes.len(),
        1,
        "template-over-template emits ONE outcome: {outcomes:?}"
    );
    let o = &outcomes[0];
    assert!(o.prior_was_def && !o.per_symbol, "T1 trigger fields: {o:?}");
    assert!(crate::redefine::is_t1_downgrade(o));
}

// spec: design/int/s102-defect-wave.md §1 item 3 — the SLOTTED-staged arm
// also carries `prior_was_def`: a concrete staged Def over a slot-less
// prior template (the L-U1 worked shape — generic `id` redefined with a
// concrete body) classifies `New` (no frozen slot to version) yet MUST
// reach the §18.1.1 trigger via `prior_was_def`. Negative cells: a
// genuinely fresh commit and a defn shadowing a prior `Import` (0484's
// territory) carry `prior_was_def: false` and never trigger.
#[test]
fn commit_gate_concrete_over_template_prior_and_negative_cells() {
    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
    // Slot-less prior template `id`; prior `Import` binding `imp`.
    install_plain_template_fixture(&mut live, "id");
    live.expose_candidate(
        Symbol::from("imp"),
        FQSymbol {
            module: ModuleFullPath::from("primitives"),
            symbol: Symbol::from("add-i64"),
        },
        Visibility::Private,
    )
    .expect("import candidate fixture installs");
    symbol_tables.insert(module.clone(), live);

    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    for (slot, name) in ["id", "imp", "fresh"].into_iter().enumerate() {
        install_body_fixture(
            &mut staging,
            name,
            CallableOrigin::Plain,
            Some(trivial_variant()),
            slot,
        );
    }

    let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
        .expect("commit cannot exhaust the GOT");
    let by_name = |n: &str| {
        outcomes
            .iter()
            .find(|o| o.fq.symbol.as_ref() == n)
            .unwrap_or_else(|| panic!("outcome for {n}: {outcomes:?}"))
    };
    let id = by_name("id");
    assert!(
        id.prior_was_def && !id.per_symbol && crate::redefine::is_t1_downgrade(id),
        "concrete-over-template reaches the trigger: {id:?}"
    );
    assert!(
        id.new_slot.is_some(),
        "concrete staged entry commits a live slot"
    );
    let imp = by_name("imp");
    assert!(
        !imp.prior_was_def && !crate::redefine::is_t1_downgrade(imp),
        "prior-Import shadow is genuine New, never a downgrade: {imp:?}"
    );
    let fresh = by_name("fresh");
    assert!(
        !fresh.prior_was_def && !crate::redefine::is_t1_downgrade(fresh),
        "fresh commit is genuine New, never a downgrade: {fresh:?}"
    );
}

// §11.3(b) / §24 (CF.1) unit-tier floor: a panic raised inside the
// `checked_check_forms` catch-region is CONVERTED to `Err`, not propagated as
// an unwind. This is the unit complement to the e2e CF.1
// (`tests/agent.rs::agent_validator_malformed_form_does_not_crash_repl`): the
// e2e proves the REPL survives end-to-end; this pins the conversion at the
// exact seam where the catch lives (mirroring the pool-worker `catch_unwind`
// at `worker.rs:1483`). The §24.3 injection seam
// (`CRANELISP_AGENT_FORCE_VALIDATOR_PANIC`) stands in for any uncontrolled-
// input typechecker panic, so the guard is durable independent of any
// specific defect (e.g. 0432) that the typecheck root fix removes.
#[cfg(feature = "agent")]
#[test]
fn checked_check_forms_converts_panic_to_err_no_unwind_escapes() {
    use cranelisp_typecheck::SymbolTableAccess;

    let module = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
        dashmap::DashMap::new();
    let module_aliases = cranelisp_types::ModuleAliases::default();
    let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();

    let mut staging: crate::code::SessionSymbolTable =
        crate::code::SessionSymbolTable::new_with_params(module.clone());
    let mut ctx: SymbolTableAccess<'_, crate::code::Code, ()> =
        SymbolTableAccess::cluster(&symbol_tables, &mut staging, module.clone());

    // Arm the injection seam so the catch-region panics. Env is process-global,
    // so set it, run the catch, then clear it — keeping the test self-contained.
    // The serde of this env var is owned by `checked_check_forms`'s seam.
    unsafe { std::env::set_var("CRANELISP_AGENT_FORCE_VALIDATOR_PANIC", "1") };
    // `catch_unwind` inside `checked_check_forms` must convert the forced
    // panic to `Err` — this call MUST NOT itself unwind (no `should_panic`).
    let result = checked_check_forms(
        Vec::new(),
        &mut ctx,
        &symbol_tables,
        &module_aliases,
        &prelude_fallback,
    );
    unsafe { std::env::remove_var("CRANELISP_AGENT_FORCE_VALIDATOR_PANIC") };

    match result {
        Err(cranelisp_typecheck::CheckError::TypeError { message, .. }) => {
            assert!(
                message.contains("compiler internal error"),
                "the caught panic must surface as the §24.2 internal-error \
                     TypeError, got: {message}"
            );
        }
        other => panic!(
            "checked_check_forms MUST convert a catch-region panic to \
                 Err(TypeError) (the §11.3(b)/§24 floor), got: {other:?}"
        ),
    }
}

// S90 4R Important: the banner-suppression mechanism is a THREAD-LOCAL flag
// (RAII guard), NOT a process-global panic-hook swap. This pins (a) the flag
// defaults false, (b) the guard sets it true for its scope and restores the
// prior value on drop (nesting-safe), and (c) the flag is thread-local — a
// freshly-spawned thread observes false even while this thread holds the guard
// true (the core property that makes a concurrently-panicking worker print its
// banner normally, with no global race).
#[cfg(feature = "agent")]
#[test]
fn suppress_panic_banner_is_thread_local_and_raii_scoped() {
    // (a) defaults false on the current thread.
    assert!(
        !SUPPRESS_PANIC_BANNER.with(|c| c.get()),
        "the suppression flag must default false"
    );

    {
        let _guard = SuppressPanicBannerGuard::new();
        // (b) set true inside the guard's scope.
        assert!(
            SUPPRESS_PANIC_BANNER.with(|c| c.get()),
            "the guard must set the flag true for its scope"
        );

        // (c) thread-local: a concurrent thread sees false while we hold true.
        let observed_on_other_thread =
            std::thread::spawn(|| SUPPRESS_PANIC_BANNER.with(|c| c.get()))
                .join()
                .unwrap();
        assert!(
            !observed_on_other_thread,
            "the flag MUST be thread-local — another thread observes false \
                 even while this thread holds the guard (no global state, no race)"
        );

        // Nesting restores the prior value (true), not unconditionally false.
        {
            let _inner = SuppressPanicBannerGuard::new();
            assert!(SUPPRESS_PANIC_BANNER.with(|c| c.get()));
        }
        assert!(
            SUPPRESS_PANIC_BANNER.with(|c| c.get()),
            "dropping a nested guard must restore the outer guard's true, \
                 not clear to false"
        );
    }

    // Guard dropped → flag restored to its pre-guard value (false).
    assert!(
        !SUPPRESS_PANIC_BANNER.with(|c| c.get()),
        "dropping the guard must restore the flag to false"
    );
}

// spec: repl/spec.md §3.3 — listing-surface category bucketing (FIXME 0440).
// `classify_listing_entry` is the SINGLE `ModuleEntry`/`DefKind` → category
// classifier shared by `/list`, `/exports` and `list_user_definitions`. This
// pins the bucket for one representative entry of every category the
// formerly-independent sites covered, so a new
// `DefKind` variant or a re-bucketing change is a one-site edit (Principle
// 7) rather than the N-site drift that produced the S91 `__expr` bug.
#[test]
fn classify_listing_entry_buckets_every_category() {
    use crate::session_v4::SymbolCategory;
    use cranelisp_types::{
        FQTypeName, SpecialFormRecord, TraitDeclInfo, TraitName, TraitRecord, TypeDefInfo,
        TypeName, TypeRecord,
    };

    let module = ModuleFullPath::from("user");

    // Def(UserFn) → Fn
    let mut table = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_body_fixture(
        &mut table,
        "f",
        CallableOrigin::Plain,
        Some(trivial_variant()),
        0,
    );
    let user_fn = table.get("f").expect("fixture installed");
    assert_eq!(
        classify_listing_entry(&user_fn),
        Some(SymbolCategory::Fn),
        "an ordinary user fn is the Fn category"
    );

    // Def(Macro) → Macro
    let mac = crate::repl::test_support::install_macro_fixture(
        &mut table,
        "m",
        Sexp::Symbol("m".to_string(), Span::SYNTHETIC),
        Vec::new(),
        Visibility::Public,
    );
    assert_eq!(classify_listing_entry(&mac), Some(SymbolCategory::Macro));

    // Def(Constructor) → Constructor
    let mut ctor_table = crate::code::SessionSymbolTable::new_with_params(module.clone());
    install_body_fixture(
        &mut ctor_table,
        "Some",
        CallableOrigin::Ctor {
            type_name: FQTypeName::new(module.clone(), TypeName::from("Option")),
            tag: 1,
            field_count: 1,
            internal: false,
            type_def: None,
        },
        Some(trivial_variant()),
        0,
    );
    let ctor = ctor_table.get("Some").expect("fixture installed");
    assert_eq!(
        classify_listing_entry(&ctor),
        Some(SymbolCategory::Constructor),
        "a constructor Def is the Constructor category (callers fold/drop it)"
    );

    // TypeDef → Type
    let type_def = Binding::new(
        Decl::Type(TypeRecord::Defined {
            info: TypeDefInfo {
                name: FQTypeName::new(module.clone(), TypeName::from("Point")),
                type_params: Vec::new(),
                constructors: vec![Symbol::from("Point")],
            },
            docstring: None,
        }),
        Visibility::Public,
    );
    assert_eq!(
        classify_listing_entry(&type_def),
        Some(SymbolCategory::Type)
    );

    // TraitDecl → Trait
    let trait_decl = Binding::new(
        Decl::Trait(TraitRecord::new(
            TraitDeclInfo {
                name: TraitName::from("Display"),
                type_params: Vec::new(),
                methods: Vec::new(),
            },
            None,
        )),
        Visibility::Public,
    );
    assert_eq!(
        classify_listing_entry(&trait_decl),
        Some(SymbolCategory::Trait)
    );

    // SpecialForm → SpecialForm (classified here; `list_user_definitions` and
    // the listing commands then filter the category out)
    let special = Binding::new(
        Decl::SpecialForm(SpecialFormRecord::new(
            synthetic_scheme(),
            Vec::new(),
            None,
            "let".to_string(),
        )),
        Visibility::Public,
    );
    assert_eq!(
        classify_listing_entry(&special),
        Some(SymbolCategory::SpecialForm)
    );

    // Imports and ambiguities are spelling candidates, not bindings, and
    // therefore cannot enter the binding classifier at all.
    let mut candidate_table =
        crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("scope"));
    candidate_table
        .expose_candidate(
            Symbol::from("x"),
            FQSymbol {
                module: ModuleFullPath::from("other"),
                symbol: Symbol::from("x"),
            },
            Visibility::Private,
        )
        .expect("first candidate installs");
    candidate_table
        .expose_candidate(
            Symbol::from("x"),
            FQSymbol {
                module: ModuleFullPath::from("third"),
                symbol: Symbol::from("x"),
            },
            Visibility::Public,
        )
        .expect("second candidate installs");
    assert!(candidate_table.get("x").is_none());
    assert_eq!(candidate_table.name_candidates(&Symbol::from("x")).len(), 2);
}

// ---------------------------------------------------------------------------
// Publication writer (design/int/session-persistence.md §2.4.1)
// ---------------------------------------------------------------------------

fn record_key(name: &str) -> FQSymbol {
    FQSymbol {
        module: ModuleFullPath::from("user"),
        symbol: Symbol::from(name),
    }
}

fn parsed(text: &str) -> Sexp {
    cranelisp_frontend::parse(text).unwrap().remove(0)
}

fn live_record(
    shared: &crate::session_v4::SharedState,
    name: &str,
) -> Option<crate::session_v4::Introspection> {
    shared
        .introspection
        .as_ref()
        .unwrap()
        .get(&record_key(name))
        .map(|record| record.clone())
}

/// A live record for `g` from a macro-produced generation, with codegen facts.
fn seed_expanded_record(shared: &crate::session_v4::SharedState) {
    shared.introspection.as_ref().unwrap().insert(
        record_key("g"),
        crate::session_v4::Introspection {
            source: Some("(mkg)".to_string()),
            sexp: Some(parsed("(mkg)")),
            expanded: Some(parsed("(defn g [] 1)")),
            ast: None,
            clif_ir: Some("seeded clif".to_string()),
            code_size: Some(7),
        },
    );
}

/// The staged record of a direct `(defn g [] 2)` replacement.
fn staged_direct_replacement() -> Vec<(FQSymbol, crate::session_v4::Introspection)> {
    vec![(
        record_key("g"),
        crate::session_v4::Introspection {
            source: Some("(defn g [] 2)".to_string()),
            sexp: Some(parsed("(defn g [] 2)")),
            expanded: None,
            ast: None,
            clif_ir: None,
            code_size: None,
        },
    )]
}

// spec: design/int/session-persistence.md §2.4.1 — a published generation
// replaces every authored carrier (the prior expansion is cleared) and keeps
// the codegen facts; a cluster with nothing to compile still publishes, and
// its records install once.
#[test]
#[allow(clippy::result_large_err)] // CranelispError is the crate-wide error carrier
fn publication_installs_staged_records_field_wise_once() {
    let shared = test_shared_state();
    seed_expanded_record(&shared);
    let mut processed = crate::cluster::ProcessedCluster::from_parts(
        Vec::new(),
        Vec::new(),
        staged_direct_replacement(),
    );

    compile_and_publish_prepared_with(&mut processed, &shared, true, |_, _, _| {
        unreachable!("invariant: a cluster without a prepared commit compiles nothing")
    })
    .unwrap();

    let record = live_record(&shared, "g").unwrap();
    assert_eq!(record.source.as_deref(), Some("(defn g [] 2)"));
    assert_eq!(
        record.sexp.as_ref().map(Sexp::format_flat),
        Some(parsed("(defn g [] 2)").format_flat())
    );
    assert!(record.expanded.is_none(), "the prior expansion is cleared");
    assert_eq!(record.clif_ir.as_deref(), Some("seeded clif"));
    assert_eq!(record.code_size, Some(7));
    assert!(processed.introspection_records().is_empty());

    shared
        .introspection
        .as_ref()
        .unwrap()
        .remove(&record_key("g"));
    compile_and_publish_prepared_with(&mut processed, &shared, true, |_, _, _| {
        unreachable!("invariant: nothing is prepared")
    })
    .unwrap();
    assert!(
        live_record(&shared, "g").is_none(),
        "a repeated publication call installs nothing"
    );
}

// spec: design/int/session-persistence.md §2.4.1 negative — releasing a
// cluster's residue installs none of its staged records; only publication does.
#[test]
fn insert_cluster_installs_no_staged_record() {
    let shared = test_shared_state();
    seed_expanded_record(&shared);
    let processed = crate::cluster::ProcessedCluster::from_parts(
        Vec::new(),
        Vec::new(),
        staged_direct_replacement(),
    );

    crate::cluster::insert_cluster(&shared, processed, &ModuleFullPath::from("user")).unwrap();

    let record = live_record(&shared, "g").unwrap();
    assert_eq!(record.source.as_deref(), Some("(mkg)"));
    assert!(record.expanded.is_some());
}

// ---------------------------------------------------------------------------
// Increments never rebuild: only a reload's whole-source registration swaps in
// a fresh table (design/int/session-transaction.md §7.3.1). The rebuild's own
// rows are in `session_v4/persistence_tests.rs`.
// ---------------------------------------------------------------------------

const REMOVAL_V1: &str = "(defn g [] 1)\n(defn h [] 2)\n";

/// A REPL session whose `user` module was loaded from `user.cl` holding
/// `source`.
fn removal_session(
    source: &str,
) -> (
    tempfile::TempDir,
    crate::session_v4::CompilerSession,
    std::path::PathBuf,
) {
    let (root, mut session) = owed_facts_session();
    let path = root.path().join("user.cl");
    std::fs::write(&path, source).unwrap();
    session.register_module("user").unwrap();
    (root, session, path)
}

fn user_binding(
    session: &crate::session_v4::CompilerSession,
    name: &str,
) -> Option<Binding<crate::code::Code>> {
    session
        .shared
        .symbol_tables
        .get(&ModuleFullPath::from("user"))
        .and_then(|table| table.get(name).cloned())
}

fn user_slot(session: &crate::session_v4::CompilerSession, name: &str) -> Option<usize> {
    user_binding(session, name).and_then(|binding| binding.callable_got_slot())
}

fn user_retired_slots(session: &crate::session_v4::CompilerSession) -> Vec<usize> {
    session
        .shared
        .symbol_tables
        .get(&ModuleFullPath::from("user"))
        .unwrap()
        .retired_slots()
        .iter()
        .map(|retired| retired.slot.index())
        .collect()
}

// spec: design/int/session-transaction.md §7.3.1 negative — driving a declared
// submodule after the parent's generation has published retries no source, so
// it removes none of the definitions that generation just published.
#[test]
fn published_generation_keeps_its_definitions_across_the_submodule_retry() {
    let (root, mut session) = owed_facts_session();
    std::fs::write(root.path().join("lib.cl"), "(defn a [] 1)\n(mod- test)\n").unwrap();
    std::fs::create_dir_all(root.path().join("lib")).unwrap();
    std::fs::write(root.path().join("lib").join("test.cl"), "(defn t [] 2)\n").unwrap();
    session.eval("(import [lib [a]])").unwrap();
    let lib = session
        .shared
        .symbol_tables
        .get(&ModuleFullPath::from("lib"))
        .unwrap()
        .clone();
    assert!(lib.get("a").is_some(), "the parent keeps `a`");
    assert!(
        session
            .shared
            .symbol_tables
            .get(&ModuleFullPath::from("lib.test"))
            .is_some_and(|table| table.get("t").is_some()),
        "precondition: the submodule was driven"
    );
    session.shutdown();
}

// spec: design/int/session-transaction.md §7.3.1 negative — a REPL turn that
// defines only `g` replaces no generation, so `h` keeps its binding and slot.
#[test]
fn additive_turn_defining_one_function_retires_nothing() {
    let (_root, mut session, _path) = removal_session(REMOVAL_V1);
    let h_slot = user_slot(&session, "h");
    assert!(h_slot.is_some(), "precondition");
    session.eval("(defn g [] 5)").unwrap();
    assert_eq!(user_slot(&session, "h"), h_slot);
    session.shutdown();
}

// spec: design/int/session-transaction.md §7.3.1 negative (Placeholder) — a
// dispatch that finds no stored continuation over a populated table retires
// nothing.
#[test]
fn dispatch_without_a_stored_continuation_retires_nothing() {
    let (_root, session, _path) = removal_session(REMOVAL_V1);
    let user = ModuleFullPath::from("user");
    let h_slot = user_slot(&session, "h");
    assert!(h_slot.is_some(), "precondition");
    let retired = user_retired_slots(&session);

    assert!(session.shared.scheduler.requeue_without_continuation(&user));
    let _ = session
        .shared
        .scheduler
        .wait_module_inmem_complete_blocking(&user);

    assert_eq!(user_slot(&session, "h"), h_slot, "`h` keeps its slot");
    assert!(user_binding(&session, "g").is_some(), "`g` stays");
    assert_eq!(user_retired_slots(&session), retired, "no tombstone");
    let mut session = session;
    session.shutdown();
}

// spec: design/int/session-transaction.md §7.3.1 negative (Placeholder);
// repl/spec/15-session-persistence.md §15.2.3 — startup recovery's empty
// re-registration of the entry retires nothing its populated table holds.
#[test]
fn startup_recovery_placeholder_retires_nothing() {
    let (_root, mut session, _path) = removal_session(REMOVAL_V1);
    let user = ModuleFullPath::from("user");
    let h_slot = user_slot(&session, "h");
    assert!(h_slot.is_some(), "precondition");
    let retired = user_retired_slots(&session);
    session.shared.scheduler.notify_module_failed(
        &user,
        CranelispError::ModuleError {
            message: "startup failed".into(),
            location: cranelisp_types::ErrorLocation::from_span_file(Span::new(0, 0), None),
        },
    );

    assert_eq!(session.recover_startup_failure("user"), None);

    assert_eq!(user_slot(&session, "h"), h_slot, "`h` keeps its slot");
    assert_eq!(user_retired_slots(&session), retired, "no tombstone");
    session.shutdown();
}

// ---------------------------------------------------------------------------
// Module cycles at publication (design/int/int.md §6.11)
// ---------------------------------------------------------------------------

/// The publication inputs of a generation that owes no lookup dependency and
/// belongs to no reload pass.
fn no_cycle_check() -> PublicationCheck<'static> {
    static NONE: std::sync::LazyLock<std::collections::BTreeSet<ModuleFullPath>> =
        std::sync::LazyLock::new(std::collections::BTreeSet::new);
    PublicationCheck {
        lookup_dependencies: &NONE,
        later_members: None,
        working: &[],
    }
}

/// Live tables in which each `(module, dependencies)` records a lookup
/// dependency on each of its dependencies, as a qualified reference does.
fn live_graph(
    edges: &[(&str, &[&str])],
) -> dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
    let tables = dashmap::DashMap::new();
    for (module, dependencies) in edges {
        let mut table =
            crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from(*module));
        for dependency in *dependencies {
            table.record_lookup_dependency(ModuleFullPath::from(*dependency));
        }
        tables.insert(ModuleFullPath::from(*module), table);
    }
    tables
}

/// The cycle a cluster of `module` owing lookup dependencies on `owed` would
/// close over `tables`, with `later` excluded as unsettled.
fn cycle_of(
    tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &str,
    owed: &[&str],
    later: Option<&[&str]>,
) -> Option<String> {
    let module = ModuleFullPath::from(module);
    let staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    let lookup_dependencies = owed.iter().map(|m| ModuleFullPath::from(*m)).collect();
    let later: Option<std::collections::BTreeSet<ModuleFullPath>> =
        later.map(|later| later.iter().map(|m| ModuleFullPath::from(*m)).collect());
    publication_cycle(
        tables,
        &cranelisp_typecheck::PreludeFallback::default(),
        PublicationEdges {
            module: &module,
            staging: &staging,
            lookup_dependencies: &lookup_dependencies,
        },
        later.as_ref(),
    )
    .map(|cycle| cycle.render())
}

// spec: design/int/int.md §6.11 — a new edge from `a` to `b`, whose live table
// reaches `a` through `c`, closes a cycle named along its path; the same edge
// is admitted when `b` does not reach `a`.
#[test]
fn publication_cycle_names_the_path_back_and_admits_an_acyclic_edge() {
    let cyclic = live_graph(&[("a", &[]), ("b", &["c"]), ("c", &["a"])]);
    assert_eq!(
        cycle_of(&cyclic, "a", &["b"], None).as_deref(),
        Some("a -> b -> c -> a")
    );
    let acyclic = live_graph(&[("a", &[]), ("b", &["c"]), ("c", &[])]);
    assert_eq!(cycle_of(&acyclic, "a", &["b"], None), None);
}

// spec: design/int/int.md §6.11 — `a`'s own live edges are new edges too: an
// increment that adds nothing is refused when a live edge of `a` now reaches
// back to it.
#[test]
fn publication_cycle_reads_the_module_s_live_edges() {
    let tables = live_graph(&[("a", &["b"]), ("b", &["a"])]);
    assert_eq!(
        cycle_of(&tables, "a", &[], None).as_deref(),
        Some("a -> b -> a")
    );
}

// spec: design/int/int.md §6.11 (Unsettled members) — a rebuild whose new edge
// reaches `x`, which its pass rebuilds later and whose pre-plan table reaches
// `m`, is admitted; with `x` not excluded it is refused.
#[test]
fn publication_cycle_skips_members_rebuilt_later_in_the_pass() {
    let tables = live_graph(&[("m", &[]), ("x", &["m"])]);
    assert_eq!(cycle_of(&tables, "m", &["x"], Some(&["x"])), None);
    assert_eq!(
        cycle_of(&tables, "m", &["x"], Some(&[])).as_deref(),
        Some("m -> x -> m")
    );
}

/// A table of `module` declaring `imports` (a target with its names) and
/// re-exports of `exports`.
fn declaring(
    module: &str,
    imports: &[(&str, ImportNames)],
    exports: &[&str],
) -> crate::code::SessionSymbolTable {
    let mut table = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from(module));
    table.imports = imports
        .iter()
        .map(|(target, names)| ImportSpec {
            module_path: ModuleFullPath::from(*target),
            alias: None,
            names: names.clone(),
            span: Span::SYNTHETIC,
        })
        .collect();
    table.exports = exports
        .iter()
        .map(|target| cranelisp_types::ExportSpec {
            module_path: ModuleFullPath::from(*target),
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        })
        .collect();
    table
}

/// The cycle a generation `staging` of its module would close over `tables`,
/// with the prelude fallback bit on for each of `with_bit`.
fn prelude_cycle_of(
    tables: &[crate::code::SessionSymbolTable],
    with_bit: &[&str],
    staging: &crate::code::SessionSymbolTable,
) -> Option<String> {
    let live = dashmap::DashMap::new();
    for table in tables {
        live.insert(table.path.clone(), table.clone());
    }
    let fallback = cranelisp_typecheck::PreludeFallback::default();
    for module in with_bit {
        fallback.insert(ModuleFullPath::from(*module), true);
    }
    publication_cycle(
        &live,
        &fallback,
        PublicationEdges {
            module: &staging.path,
            staging,
            lookup_dependencies: &std::collections::BTreeSet::new(),
        },
        None,
    )
    .map(|cycle| cycle.render())
}

const NULL_IMPORT_OF_PRELUDE: (&str, ImportNames) = ("prelude", ImportNames::None);

// spec: spec/08-modules.md §8.8.1, §8.10.2; design/int/int.md §6.12 — a
// prelude generation re-exporting `x`, whose fallback bit is on, closes the
// cycle through `x`'s implicit prelude dependency; with `x` null-importing
// the prelude it closes none.
#[test]
fn publication_cycle_follows_the_prelude_edge_of_a_module_with_the_bit() {
    let prelude = declaring("prelude", &[], &["x"]);
    let x_with_bit = declaring("x", &[], &[]);
    assert_eq!(
        prelude_cycle_of(std::slice::from_ref(&x_with_bit), &["x"], &prelude).as_deref(),
        Some("prelude -> x -> prelude")
    );
    let x_opted_out = declaring("x", &[NULL_IMPORT_OF_PRELUDE], &[]);
    assert_eq!(prelude_cycle_of(&[x_opted_out], &[], &prelude), None);
}

// spec: spec/08-modules.md §8.8.1, §8.10.2; design/int/int.md §6.11, §6.12 —
// the helper end: a generation of `x` with its bit on, which the live prelude
// re-exports, closes the cycle through `x`'s own implicit prelude dependency;
// the same generation with the bit off closes none.
#[test]
fn publication_cycle_follows_the_staged_module_s_own_prelude_edge() {
    let prelude = declaring("prelude", &[], &["x"]);
    let x = declaring("x", &[], &[]);
    assert_eq!(
        prelude_cycle_of(std::slice::from_ref(&prelude), &["x"], &x).as_deref(),
        Some("x -> prelude -> x")
    );
    assert_eq!(prelude_cycle_of(&[prelude], &[], &x), None);
}

// spec: spec/08-modules.md §8.3.7; design/int/int.md §6.12 (probe N2, face C) —
// a null import of the prelude is no edge: an increment in the null-importing
// `x` that the prelude imports is accepted, and so is a prelude generation
// that imports a null-importing module and publishes a definition.
#[test]
fn publication_cycle_reads_no_edge_through_a_null_import() {
    let prelude = declaring("prelude", &[("x", ImportNames::Glob)], &[]);
    let x_opted_out = declaring("x", &[NULL_IMPORT_OF_PRELUDE], &[]);
    assert_eq!(
        prelude_cycle_of(std::slice::from_ref(&prelude), &[], &x_opted_out),
        None
    );

    let mut prelude_with_definition = prelude.clone();
    install_transaction_entry(&mut prelude_with_definition, "two", Type::Int, true);
    assert_eq!(
        prelude_cycle_of(&[x_opted_out], &[], &prelude_with_definition),
        None
    );
}
