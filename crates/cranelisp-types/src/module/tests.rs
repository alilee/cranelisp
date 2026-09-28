use super::*;
use crate::{
    BrokenProvenance, Expr, MonoDefnVariant, MonoDemand, MonoExpr, SynthSpec, TraitRecord, Type,
    TypeRecord,
};
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

fn scheme(ty: Type) -> Scheme {
    Scheme {
        type_vars: Vec::new(),
        constraints: HashMap::new(),
        ty,
    }
}

fn concrete_scheme() -> Scheme {
    scheme(Type::Int)
}

fn template_scheme() -> Scheme {
    Scheme {
        type_vars: vec![0],
        constraints: HashMap::new(),
        ty: Type::Var(0),
    }
}

fn ast() -> DefnVariant {
    DefnVariant {
        params: Vec::new(),
        body: Expr::IntLit {
            value: 1,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        },
        span: Span::SYNTHETIC,
    }
}

fn view() -> MonoDefnVariant {
    MonoDefnVariant {
        name: Symbol::from("f"),
        params: Vec::new(),
        body: MonoExpr::IntLit {
            value: 1,
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        },
        span: Span::SYNTHETIC,
        mode_summary: None,
    }
}

fn ownership_annotated_view() -> MonoDefnVariant {
    MonoDefnVariant {
        name: Symbol::from("f"),
        params: Vec::new(),
        body: MonoExpr::StringLit {
            value: "owned".into(),
            span: Span::SYNTHETIC,
            ty: ConcreteType::String,
            escapes: Some(false),
            confined: Some(true),
            unique_static: Some(true),
        },
        span: Span::SYNTHETIC,
        mode_summary: None,
    }
}

fn body() -> Realization<()> {
    Realization::Body {
        view: view(),
        code: None,
    }
}

fn non_callable_binding() -> Binding<()> {
    Binding::new(
        Decl::Type(TypeRecord::Intrinsic {
            ty: Type::Int,
            docstring: None,
        }),
        Visibility::Private,
    )
}

fn declare(table: &mut SymbolTable, name: &str, scheme: Scheme, origin: CallableOrigin) {
    table
        .declare(
            Symbol::from(name),
            scheme,
            Vec::new(),
            None,
            0,
            origin,
            Visibility::Public,
        )
        .unwrap();
}

fn binding_target(module: &str, name: &str) -> CallableTarget {
    CallableTarget::Binding(FQSymbol {
        module: ModuleFullPath::from(module),
        symbol: Symbol::from(name),
    })
}

fn overload_target(module: &str, name: &str, ordinal: usize) -> CallableTarget {
    CallableTarget::OverloadArm {
        owner: FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(name),
        },
        arm: CallableArmId::from_ordinal(ordinal).unwrap(),
    }
}

fn macro_target(module: &str, name: &str, ordinal: usize) -> CallableTarget {
    CallableTarget::MacroClause {
        owner: FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(name),
        },
        clause: CallableArmId::from_ordinal(ordinal).unwrap(),
    }
}

fn concrete_arm_draft(ty: Type, body_name: &str) -> CallableArmDraft {
    let mut body_view = view();
    body_view.name = Symbol::from(body_name);
    CallableArmDraft::concrete_body(scheme(ty), Vec::new(), ast(), body_view, Vec::new())
}

fn publish_string_owner(table: &mut SymbolTable<String, ()>, target: &CallableTarget, owner: &str) {
    match table.publish_compiled_owner(target, owner.to_owned()) {
        Ok(None) => {}
        Ok(Some(_)) => panic!("fresh family owner publication displaced an owner"),
        Err(rejection) => panic!("family owner publication refused: {}", rejection.reason()),
    }
}

#[test]
fn concrete_settlement_is_atomic_and_codegen_visible() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let slot = table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();

    assert_eq!(slot.index(), 0);
    assert_eq!(table.get("f").unwrap().callable_got_slot(), Some(0));
    assert_eq!(
        table
            .codegen_targets()
            .map(|(target, _)| target)
            .collect::<Vec<_>>(),
        vec![binding_target("m", "f")]
    );
    table.validate_lifecycle().unwrap();
}

#[test]
fn concrete_metadata_updates_use_table_funnels() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();

    let summary = ModeSummary::default();
    table
        .publish_body_ownership(&binding_target("m", "f"), summary.clone(), view())
        .unwrap();
    table.set_value_use(&Symbol::from("f"), true).unwrap();
    let binding = table.get("f").unwrap();
    assert_eq!(binding.mode_summary(), Some(&summary));
    assert!(binding.value_use());

    assert!(matches!(
        table.set_value_use(&Symbol::from("missing"), true),
        Err(LifecycleError::NotCallable { .. })
    ));
}

#[test]
fn family_install_mints_distinct_slots_and_one_authored_binding() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table
        .install_overloaded(
            Symbol::from("f"),
            Some("overloaded".into()),
            7,
            vec![
                CallableArmDraft::concrete_body(
                    concrete_scheme(),
                    Vec::new(),
                    ast(),
                    view(),
                    Vec::new(),
                ),
                CallableArmDraft::concrete_body(
                    concrete_scheme(),
                    Vec::new(),
                    ast(),
                    {
                        let mut second = view();
                        second.name = Symbol::from("f$second");
                        second
                    },
                    Vec::new(),
                ),
            ],
            Visibility::Public,
        )
        .unwrap();

    assert_eq!(table.all_symbols().count(), 1);
    let binding = table.get("f").unwrap();
    let Decl::Overloaded(declaration) = &binding.declaration else {
        panic!("family installer must publish one overloaded declaration")
    };
    let slots = declaration
        .arms
        .iter()
        .map(|arm| arm.callable.life.claimed_slot().unwrap().index())
        .collect::<Vec<_>>();
    assert_eq!(slots, vec![0, 1]);
    assert_eq!(
        table
            .codegen_targets()
            .map(|(target, _)| target)
            .collect::<Vec<_>>(),
        vec![
            CallableTarget::OverloadArm {
                owner: FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("f"),
                },
                arm: CallableArmId::from_ordinal(0).unwrap(),
            },
            CallableTarget::OverloadArm {
                owner: FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("f"),
                },
                arm: CallableArmId::from_ordinal(1).unwrap(),
            },
        ]
    );
    table.validate_lifecycle().unwrap();
}

#[test]
fn failed_family_install_leaves_binding_revision_and_slot_claims_unchanged() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table
        .install_concrete(
            Symbol::from("prior"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();

    let family = Symbol::from("f");
    assert!(matches!(
        table.install_overloaded(
            family.clone(),
            None,
            1,
            vec![
                CallableArmDraft::concrete_body(
                    concrete_scheme(),
                    Vec::new(),
                    ast(),
                    view(),
                    Vec::new(),
                ),
                CallableArmDraft::concrete_body(
                    template_scheme(),
                    Vec::new(),
                    ast(),
                    view(),
                    Vec::new(),
                ),
            ],
            Visibility::Private,
        ),
        Err(LifecycleError::SlotMint(SlotMintError::NotConcrete(_)))
    ));
    assert!(table.get("f").is_none());
    assert_eq!(table.symbol_revision(&family), 0);

    let next = table
        .install_concrete(
            Symbol::from("next"),
            concrete_scheme(),
            Vec::new(),
            None,
            2,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert_eq!(next.index(), 1);
}

#[test]
fn ownership_publication_targets_exact_family_arm() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let mut second = view();
    second.name = Symbol::from("f$second");
    table
        .install_overloaded(
            Symbol::from("f"),
            None,
            0,
            vec![
                CallableArmDraft::concrete_body(
                    concrete_scheme(),
                    Vec::new(),
                    ast(),
                    view(),
                    Vec::new(),
                ),
                CallableArmDraft::concrete_body(
                    concrete_scheme(),
                    Vec::new(),
                    ast(),
                    second.clone(),
                    Vec::new(),
                ),
            ],
            Visibility::Private,
        )
        .unwrap();
    let target = CallableTarget::OverloadArm {
        owner: FQSymbol {
            module: ModuleFullPath::from("m"),
            symbol: Symbol::from("f"),
        },
        arm: CallableArmId::from_ordinal(1).unwrap(),
    };
    let summary = ModeSummary::default();
    table
        .publish_body_ownership(&target, summary.clone(), second)
        .unwrap();

    let Decl::Overloaded(declaration) = &table.get("f").unwrap().declaration else {
        panic!("expected overloaded declaration")
    };
    assert!(declaration.arms[0].callable.life.claimed_slot().is_some());
    assert!(matches!(
        &declaration.arms[0].callable.life,
        Life::Concrete {
            mode_summary: None,
            ..
        }
    ));
    assert!(matches!(
        &declaration.arms[1].callable.life,
        Life::Concrete {
            mode_summary: Some(found),
            ..
        } if found == &summary
    ));
}

#[test]
fn overload_preserve_pairs_reordered_arms_by_complete_scheme() {
    let mut live = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    live.install_overloaded(
        Symbol::from("f"),
        None,
        0,
        vec![
            concrete_arm_draft(Type::Int, "f$int"),
            concrete_arm_draft(Type::Bool, "f$bool"),
        ],
        Visibility::Public,
    )
    .unwrap();
    for (ordinal, owner) in [(0, "old-int"), (1, "old-bool")] {
        publish_string_owner(&mut live, &overload_target("m", "f", ordinal), owner);
    }
    let old_slots = [0, 1].map(|ordinal| {
        live.callable_target(&overload_target("m", "f", ordinal))
            .unwrap()
            .life
            .claimed_slot()
            .unwrap()
    });

    let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    staging
        .install_overloaded(
            Symbol::from("f"),
            None,
            0,
            vec![
                concrete_arm_draft(Type::Bool, "f$bool"),
                concrete_arm_draft(Type::Int, "f$int"),
            ],
            Visibility::Public,
        )
        .unwrap();
    let records = live
        .publish_staged(
            staging,
            &[StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("f"),
            }],
        )
        .unwrap();

    assert_eq!(records[0].bodies.len(), 2);
    assert_eq!(
        records[0].bodies[0].prior_target,
        Some(overload_target("m", "f", 0))
    );
    assert_eq!(
        records[0].bodies[0].published_target,
        Some(overload_target("m", "f", 1))
    );
    assert_eq!(records[0].bodies[0].published_slot, Some(old_slots[0]));
    assert_eq!(
        records[0].bodies[0].displaced_owner.as_deref(),
        Some("old-int")
    );
    assert_eq!(
        records[0].bodies[1].prior_target,
        Some(overload_target("m", "f", 1))
    );
    assert_eq!(
        records[0].bodies[1].published_target,
        Some(overload_target("m", "f", 0))
    );
    assert_eq!(records[0].bodies[1].published_slot, Some(old_slots[1]));
    assert_eq!(
        records[0].bodies[1].displaced_owner.as_deref(),
        Some("old-bool")
    );
    assert_eq!(
        live.callable_target(&overload_target("m", "f", 0))
            .unwrap()
            .life
            .claimed_slot(),
        Some(old_slots[1])
    );
}

#[test]
fn overload_change_abi_shrink_retires_whole_prior_family() {
    let mut live = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    live.install_overloaded(
        Symbol::from("f"),
        None,
        0,
        vec![
            concrete_arm_draft(Type::Int, "f$int"),
            concrete_arm_draft(Type::Bool, "f$bool"),
            concrete_arm_draft(Type::String, "f$string"),
        ],
        Visibility::Public,
    )
    .unwrap();
    let old_slots = [0, 1, 2].map(|ordinal| {
        publish_string_owner(
            &mut live,
            &overload_target("m", "f", ordinal),
            &format!("old-{ordinal}"),
        );
        live.callable_target(&overload_target("m", "f", ordinal))
            .unwrap()
            .life
            .claimed_slot()
            .unwrap()
    });
    let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    staging
        .install_overloaded(
            Symbol::from("f"),
            None,
            0,
            vec![
                concrete_arm_draft(Type::Int, "f$int"),
                concrete_arm_draft(Type::Bool, "f$bool"),
            ],
            Visibility::Public,
        )
        .unwrap();

    let records = live
        .publish_staged(
            staging,
            &[StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("f"),
            }],
        )
        .unwrap();
    assert_eq!(records[0].bodies.len(), 5);
    assert_eq!(
        records[0]
            .bodies
            .iter()
            .filter_map(|body| body.displaced_owner.as_deref())
            .collect::<Vec<_>>(),
        vec!["old-0", "old-1", "old-2"]
    );
    assert!(old_slots.into_iter().all(|slot| {
        live.retired_slots()
            .iter()
            .any(|retired| retired.slot == slot)
    }));
    let new_slots = [0, 1].map(|ordinal| {
        live.callable_target(&overload_target("m", "f", ordinal))
            .unwrap()
            .life
            .claimed_slot()
            .unwrap()
    });
    assert!(new_slots.into_iter().all(|slot| !old_slots.contains(&slot)));
}

#[test]
fn macro_preserve_pairs_only_equal_patterns_at_the_same_ordinal() {
    let macro_draft = |param: &str, body_name: &str| {
        MacroClauseDraft::new(
            vec![crate::MacroParam::Name(Symbol::from(param))],
            None,
            concrete_arm_draft(Type::Int, body_name),
        )
    };
    let mut live = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    live.install_macro(
        Symbol::from("mac"),
        None,
        0,
        Sexp::Symbol("mac".into(), Span::SYNTHETIC),
        vec![macro_draft("x", "mac$0"), macro_draft("y", "mac$1")],
        Visibility::Public,
    )
    .unwrap();
    for (ordinal, owner) in [(0, "old-x"), (1, "old-y")] {
        publish_string_owner(&mut live, &macro_target("m", "mac", ordinal), owner);
    }
    let old_slots = [0, 1].map(|ordinal| {
        live.callable_target(&macro_target("m", "mac", ordinal))
            .unwrap()
            .life
            .claimed_slot()
            .unwrap()
    });
    let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    staging
        .install_macro(
            Symbol::from("mac"),
            None,
            0,
            Sexp::Symbol("mac".into(), Span::SYNTHETIC),
            vec![macro_draft("x", "mac$0"), macro_draft("z", "mac$1")],
            Visibility::Public,
        )
        .unwrap();

    let records = live
        .publish_staged(
            staging,
            &[StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("mac"),
            }],
        )
        .unwrap();
    assert_eq!(records[0].bodies.len(), 3);
    assert_eq!(records[0].bodies[0].published_slot, Some(old_slots[0]));
    assert_eq!(records[0].bodies[1].prior_slot, Some(old_slots[1]));
    assert!(records[0].bodies[1].published_target.is_none());
    assert!(records[0].bodies[2].prior_target.is_none());
    assert_ne!(records[0].bodies[2].published_slot, Some(old_slots[1]));
    assert_eq!(
        records[0].bodies[0].displaced_owner.as_deref(),
        Some("old-x")
    );
    assert_eq!(
        records[0].bodies[1].displaced_owner.as_deref(),
        Some("old-y")
    );
}

#[test]
fn complete_scheme_alpha_equivalence_includes_constraints_and_tycon_heads() {
    let trait_name = FQTraitName::new(ModuleFullPath::from("traits"), TraitName::from("Show"));
    let left = Scheme {
        type_vars: vec![7, 8],
        constraints: HashMap::from([(7, vec![trait_name.clone()])]),
        ty: Type::Fn(
            vec![Type::TyConApp(8, vec![Type::Var(7)])],
            Box::new(Type::Var(7)),
        ),
    };
    let right = Scheme {
        type_vars: vec![40, 41],
        constraints: HashMap::from([(40, vec![trait_name])]),
        ty: Type::Fn(
            vec![Type::TyConApp(41, vec![Type::Var(40)])],
            Box::new(Type::Var(40)),
        ),
    };
    assert!(schemes_alpha_equivalent(&left, &right));
}

fn assert_plain_docstring_update(
    table: &mut SymbolTable<String, ()>,
    name: &Symbol,
    docstring: &str,
) {
    let mut expected = table.get(name.as_ref()).unwrap().clone();
    expected.callable_mut().unwrap().docstring = Some(docstring.to_owned());
    let revision = table.symbol_revision(name);

    table
        .set_plain_callable_docstring(name, docstring.to_owned())
        .unwrap();

    assert_eq!(
        format!("{:?}", table.get(name.as_ref()).unwrap()),
        format!("{expected:?}")
    );
    assert_eq!(table.symbol_revision(name), revision.wrapping_add(1));
}

#[test]
fn plain_callable_docstring_accepts_every_legal_plain_lifecycle() {
    let name = Symbol::from("f");

    let mut declared = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("declared"));
    declared
        .declare(
            name.clone(),
            concrete_scheme(),
            vec![Symbol::from("arg")],
            Some("old".into()),
            3,
            CallableOrigin::Plain,
            Visibility::Private,
        )
        .unwrap();
    assert_plain_docstring_update(&mut declared, &name, "declared doc");

    let mut template = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("template"));
    template
        .install_template(
            name.clone(),
            template_scheme(),
            vec![Symbol::from("arg")],
            Some("old".into()),
            4,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            vec![FQSymbol {
                module: ModuleFullPath::from("dep"),
                symbol: Symbol::from("callee"),
            }],
            Visibility::Private,
        )
        .unwrap();
    assert_plain_docstring_update(&mut template, &name, "template doc");

    let mut concrete = owner_table("concrete", Some("compiled"));
    assert_plain_docstring_update(&mut concrete, &name, "concrete doc");

    let mut broken = owner_table("broken", Some("compiled"));
    let old_slot = broken.get("f").unwrap().callable_got_slot().unwrap();
    let transition = broken
        .mark_broken(
            &name,
            BrokenProvenance::new(
                FQSymbol {
                    module: ModuleFullPath::from("broken"),
                    symbol: Symbol::from("cause"),
                },
                "failed recompilation".into(),
            ),
        )
        .unwrap();
    assert_eq!(transition.slot.index(), old_slot);
    assert_eq!(transition.displaced_owner.as_deref(), Some("compiled"));
    assert_plain_docstring_update(&mut broken, &name, "broken doc");
}

#[test]
fn plain_callable_docstring_preserves_concrete_payload_candidates_got_and_tombstones() {
    let name = Symbol::from("f");
    let mut table = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    let slot = table
        .install_concrete(
            name.clone(),
            concrete_scheme(),
            vec![Symbol::from("arg")],
            Some("old".into()),
            17,
            CallableOrigin::Plain,
            owner_body(None),
            Some(ast()),
            vec![FQSymbol {
                module: ModuleFullPath::from("dep"),
                symbol: Symbol::from("callee"),
            }],
            Visibility::Private,
        )
        .unwrap();
    let summary = ModeSummary::default();
    table
        .publish_body_ownership(
            &binding_target("m", "f"),
            summary,
            ownership_annotated_view(),
        )
        .unwrap();
    table.set_value_use(&name, true).unwrap();
    match table.publish_compiled_owner(&binding_target("m", "f"), "compiled-owner".into()) {
        Ok(None) => {}
        Ok(Some(_)) | Err(_) => panic!("first compiled owner publication must succeed"),
    }
    let published = std::ptr::dangling::<u8>();
    table.got.store_slot(slot.index(), published);
    table
        .expose_candidate(
            name.clone(),
            FQSymbol {
                module: ModuleFullPath::from("dep"),
                symbol: Symbol::from("other-f"),
            },
            Visibility::Public,
        )
        .unwrap();

    table
        .install_concrete(
            Symbol::from("retired"),
            concrete_scheme(),
            Vec::new(),
            None,
            18,
            CallableOrigin::Plain,
            owner_body(None),
            None,
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    table.retire_abi_changing(&Symbol::from("retired")).unwrap();

    let candidates = table.name_candidates(&name);
    let tombstones = table.retired_slots().to_vec();
    assert_plain_docstring_update(&mut table, &name, "replacement");

    assert_eq!(table.name_candidates(&name), candidates);
    assert_eq!(table.retired_slots(), tombstones);
    assert_eq!(table.got.load_slot(slot.index()), published);
}

#[test]
fn plain_callable_docstring_refusals_are_exact_and_atomic() {
    let mut table = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));

    let missing = Symbol::from("missing");
    assert_eq!(
        table.set_plain_callable_docstring(&missing, "new".into()),
        Err(LifecycleError::MissingBinding {
            symbol: missing.clone(),
        })
    );
    assert_eq!(table.symbol_revision(&missing), 0);
    assert!(table.name_candidates(&missing).is_empty());

    let candidate_only = Symbol::from("imported");
    table
        .expose_candidate(
            candidate_only.clone(),
            FQSymbol {
                module: ModuleFullPath::from("dep"),
                symbol: Symbol::from("target"),
            },
            Visibility::Public,
        )
        .unwrap();
    let candidates = table.name_candidates(&candidate_only);
    let revision = table.symbol_revision(&candidate_only);
    assert_eq!(
        table.set_plain_callable_docstring(&candidate_only, "new".into()),
        Err(LifecycleError::MissingBinding {
            symbol: candidate_only.clone(),
        })
    );
    assert!(table.get(candidate_only.as_ref()).is_none());
    assert_eq!(table.name_candidates(&candidate_only), candidates);
    assert_eq!(table.symbol_revision(&candidate_only), revision);

    let non_callable = Symbol::from("a-type");
    table
        .install_binding(
            non_callable.clone(),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::Int,
                    docstring: Some("type doc".into()),
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
    let binding = format!("{:?}", table.get(non_callable.as_ref()).unwrap());
    let revision = table.symbol_revision(&non_callable);
    assert_eq!(
        table.set_plain_callable_docstring(&non_callable, "new".into()),
        Err(LifecycleError::NotCallable {
            symbol: non_callable.clone(),
        })
    );
    assert_eq!(
        format!("{:?}", table.get(non_callable.as_ref()).unwrap()),
        binding
    );
    assert_eq!(table.symbol_revision(&non_callable), revision);

    let non_plain = Symbol::from("primitive");
    table
        .install_extern(
            non_plain.clone(),
            concrete_scheme(),
            vec![Symbol::from("arg")],
            Some("primitive doc".into()),
            9,
            None,
            Some(ModeSummary::default()),
            Visibility::Public,
        )
        .unwrap();
    let binding = format!("{:?}", table.get(non_plain.as_ref()).unwrap());
    let revision = table.symbol_revision(&non_plain);
    assert_eq!(
        table.set_plain_callable_docstring(&non_plain, "new".into()),
        Err(LifecycleError::WrongState {
            symbol: non_plain.clone(),
            expected: "plain callable",
        })
    );
    assert_eq!(
        format!("{:?}", table.get(non_plain.as_ref()).unwrap()),
        binding
    );
    assert_eq!(table.symbol_revision(&non_plain), revision);
}

#[test]
fn residual_scheme_cannot_settle_concrete() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", template_scheme(), CallableOrigin::Plain);
    assert!(matches!(
        table.settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new(),),
        Err(LifecycleError::SlotMint(SlotMintError::NotConcrete(_)))
    ));
    assert!(matches!(
        table.get("f").unwrap().callable().unwrap().arm.life,
        Life::Declared { prior: None }
    ));
}

#[test]
fn concrete_scheme_cannot_settle_as_template() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    assert!(matches!(
        table.settle_template(
            &Symbol::from("f"),
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
        ),
        Err(LifecycleError::ConcreteTemplate { .. })
    ));
}

#[test]
fn redeclaration_rebinds_the_same_slot() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let first = table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let declared = table.get("f").unwrap();
    assert_eq!(
        declared.callable().unwrap().arm.life.claimed_slot(),
        Some(first)
    );
    assert_eq!(
        declared.callable_got_slot(),
        None,
        "Declared.prior is an allocation claim, not a dispatch capability"
    );
    let rebound = table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    assert_eq!(rebound, first);
    assert!(table.retired_slots().is_empty());
}

#[test]
fn redeclaration_cannot_change_callable_origin() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    let old_slot = table.get("f").unwrap().callable_got_slot();

    assert!(matches!(
        table.declare(
            Symbol::from("f"),
            concrete_scheme(),
            Vec::new(),
            None,
            1,
            CallableOrigin::RustPrimitive,
            Visibility::Public,
        ),
        Err(LifecycleError::IllegalOriginState { .. })
    ));
    assert_eq!(table.get("f").unwrap().callable_got_slot(), old_slot);
}

#[test]
fn concrete_to_template_conserves_and_never_reissues_prior_slot() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let old = table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();

    declare(&mut table, "f", template_scheme(), CallableOrigin::Plain);
    table
        .settle_template(
            &Symbol::from("f"),
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
        )
        .unwrap();
    assert_eq!(table.retired_slots()[0].slot, old);
    assert!(matches!(
        table.retired_slots()[0].reason,
        RetireReason::TemplateFlip { .. }
    ));

    declare(&mut table, "g", concrete_scheme(), CallableOrigin::Plain);
    let next = table
        .settle_concrete(&Symbol::from("g"), body(), Some(ast()), Vec::new())
        .unwrap();
    assert_ne!(next, old);
}

#[test]
fn abi_retirement_tombstones_the_slot_and_is_atomic_on_refusal() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table
        .install_binding(Symbol::from("x"), non_callable_binding())
        .unwrap();
    assert!(table.retire_abi_changing(&Symbol::from("x")).is_err());
    assert!(table.get("x").is_some());

    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let old = table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    table.retire_abi_changing(&Symbol::from("f")).unwrap();
    assert!(table.get("f").is_none());
    assert_eq!(table.retired_slots()[0].slot, old);

    declare(&mut table, "g", concrete_scheme(), CallableOrigin::Plain);
    let next = table
        .settle_concrete(&Symbol::from("g"), body(), Some(ast()), Vec::new())
        .unwrap();
    assert_ne!(next, old);
}

fn owner_body(owner: Option<&str>) -> Realization<String> {
    Realization::Body {
        view: view(),
        code: owner.map(str::to_owned),
    }
}

fn owner_table(path: &str, owner: Option<&str>) -> SymbolTable<String, ()> {
    let mut table = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from(path));
    table
        .install_concrete(
            Symbol::from("f"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            owner_body(owner),
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    table
}

fn compiled_owner<'a>(table: &'a SymbolTable<String, ()>, name: &str) -> Option<&'a str> {
    let callable = table.get(name)?.callable()?;
    let Life::Concrete {
        realization: Realization::Body { code, .. },
        ..
    } = &callable.arm.life
    else {
        return None;
    };
    code.as_deref()
}

#[derive(Clone)]
struct DropSpy {
    label: &'static str,
    drops: Arc<AtomicUsize>,
}

impl Drop for DropSpy {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}

fn drop_spy(label: &'static str) -> (DropSpy, Arc<AtomicUsize>) {
    let drops = Arc::new(AtomicUsize::new(0));
    (
        DropSpy {
            label,
            drops: Arc::clone(&drops),
        },
        drops,
    )
}

fn slotted_rust_primitive_table() -> SymbolTable<String, ()> {
    let mut table = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    table
        .install_extern(
            Symbol::from("primitive"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            None,
            None,
            Visibility::Public,
        )
        .unwrap();
    table
}

#[test]
fn compiled_owner_publication_conserves_submitted_and_displaced_owners() {
    let mut table = owner_table("m", None);
    match table.publish_compiled_owner(&binding_target("m", "f"), "first".to_owned()) {
        Ok(None) => {}
        Ok(Some(_)) | Err(_) => panic!("first owner publication should displace nothing"),
    }
    match table.publish_compiled_owner(&binding_target("m", "f"), "second".to_owned()) {
        Ok(Some(displaced)) => assert_eq!(displaced, "first"),
        Ok(None) | Err(_) => panic!("replacement should return the first owner"),
    }

    let rejection =
        match table.publish_compiled_owner(&binding_target("m", "missing"), "kept".into()) {
            Err(rejection) => rejection,
            Ok(_) => panic!("missing binding must refuse the owner"),
        };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::MissingBinding { symbol } if symbol.as_ref() == "missing"
    ));
    let (reason, owner) = rejection.into_parts();
    assert!(matches!(reason, LifecycleError::MissingBinding { .. }));
    assert_eq!(owner, "kept");

    table
        .install_binding(
            Symbol::from("non_callable"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::Int,
                    docstring: None,
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
    let rejection = match table.publish_compiled_owner(
        &binding_target("m", "non_callable"),
        "non-callable-owner".into(),
    ) {
        Err(rejection) => rejection,
        Ok(_) => panic!("non-callable binding must refuse the owner"),
    };
    let (reason, owner) = rejection.into_parts();
    assert!(matches!(reason, LifecycleError::NotCallable { .. }));
    assert_eq!(owner, "non-callable-owner");

    table
        .install_template(
            Symbol::from("template"),
            template_scheme(),
            Vec::new(),
            None,
            1,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    let rejection = match table
        .publish_compiled_owner(&binding_target("m", "template"), "template-owner".into())
    {
        Err(rejection) => rejection,
        Ok(_) => panic!("slotless template must refuse the owner"),
    };
    let (reason, owner) = rejection.into_parts();
    assert!(matches!(reason, LifecycleError::WrongState { .. }));
    assert_eq!(owner, "template-owner");

    table
        .install_extern(
            Symbol::from("extern"),
            concrete_scheme(),
            Vec::new(),
            None,
            2,
            None,
            None,
            Visibility::Private,
        )
        .unwrap();
    let rejection =
        match table.publish_compiled_owner(&binding_target("m", "extern"), "extern-owner".into()) {
            Err(rejection) => rejection,
            Ok(_) => panic!("non-Body concrete callable must refuse the owner"),
        };
    let (reason, owner) = rejection.into_parts();
    assert!(matches!(reason, LifecycleError::WrongState { .. }));
    assert_eq!(owner, "extern-owner");
}

#[test]
fn broken_transition_retains_slot_and_returns_body_owner() {
    let mut table = owner_table("m", Some("compiled"));
    let old_slot = table.get("f").unwrap().callable_got_slot().unwrap();
    let transition = table
        .mark_broken(
            &Symbol::from("f"),
            BrokenProvenance::new(
                FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("cause"),
                },
                "failed".into(),
            ),
        )
        .unwrap();
    assert_eq!(transition.slot.index(), old_slot);
    assert_eq!(transition.displaced_owner.as_deref(), Some("compiled"));
    assert!(matches!(
        &table.get("f").unwrap().callable().unwrap().arm.life,
        Life::Broken { slot, .. } if slot.index() == old_slot
    ));
}

#[test]
fn staged_publication_preserves_or_changes_abi_and_returns_old_owner() {
    let mut live = owner_table("m", Some("generation-1"));
    let old_slot = live.get("f").unwrap().callable_got_slot().unwrap();
    let records = live
        .publish_staged(
            owner_table("m", None),
            &[StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("f"),
            }],
        )
        .unwrap();
    assert_eq!(records.len(), 1);
    assert!(records[0].prior_was_callable);
    assert_eq!(
        records[0].bodies[0].prior_slot.map(|slot| slot.index()),
        Some(old_slot)
    );
    assert_eq!(
        records[0].bodies[0].published_slot.map(|slot| slot.index()),
        Some(old_slot)
    );
    assert_eq!(
        records[0].bodies[0].displaced_owner.as_deref(),
        Some("generation-1")
    );
    assert!(live.retired_slots().is_empty());

    match live.publish_compiled_owner(&binding_target("m", "f"), "generation-2".into()) {
        Ok(None) => {}
        Ok(Some(_)) | Err(_) => panic!("preserved publication should be ownerless before codegen"),
    }
    let records = live
        .publish_staged(
            owner_table("m", None),
            &[StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("f"),
            }],
        )
        .unwrap();
    assert_eq!(records[0].bodies.len(), 2);
    let new_slot = records[0].bodies[1].published_slot.unwrap();
    assert_ne!(new_slot.index(), old_slot);
    assert_eq!(
        records[0].bodies[0].displaced_owner.as_deref(),
        Some("generation-2")
    );
    assert_eq!(live.retired_slots()[0].slot.index(), old_slot);
    assert!(matches!(
        live.retired_slots()[0].reason,
        RetireReason::AbiChanging { .. }
    ));
}

#[test]
fn staged_publication_change_abi_can_explicitly_retire_absent_bindings() {
    let mut live = owner_table("m", Some("old-f"));
    for (name, seq, owner) in [("g", 1, "old-g"), ("h", 2, "old-h")] {
        live.install_concrete(
            Symbol::from(name),
            concrete_scheme(),
            Vec::new(),
            None,
            seq,
            CallableOrigin::Plain,
            owner_body(Some(owner)),
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    }
    live.expose_candidate(
        Symbol::from("g"),
        FQSymbol {
            module: ModuleFullPath::from("dep"),
            symbol: Symbol::from("g"),
        },
        Visibility::Private,
    )
    .unwrap();

    let old_slots = ["f", "g", "h"].map(|name| {
        live.get(name)
            .unwrap()
            .callable()
            .unwrap()
            .arm
            .life
            .claimed_slot()
            .unwrap()
    });
    let old_revisions = ["f", "g", "h"].map(|name| {
        let name = Symbol::from(name);
        (name.clone(), live.symbol_revision(&name))
    });
    let frozen = std::ptr::dangling::<u8>();
    live.got.store_slot(old_slots[1].index(), frozen);
    live.got.store_slot(old_slots[2].index(), frozen);

    let records = match live.publish_compiled_staged(
        owner_table("m", None),
        &[
            StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("h"),
            },
            StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("f"),
            },
            StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("g"),
            },
        ],
        HashMap::from([(binding_target("m", "f"), "new-f".to_owned())]),
    ) {
        Ok(records) => records,
        Err(rejection) => panic!("explicit retirement refused: {}", rejection.reason()),
    };

    assert_eq!(
        records
            .iter()
            .map(|record| record.symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["f", "g", "h"]
    );
    for (name, owner, old_slot) in [("g", "old-g", old_slots[1]), ("h", "old-h", old_slots[2])] {
        let record = records
            .iter()
            .find(|record| record.symbol.as_ref() == name)
            .unwrap();
        assert!(record.prior_was_callable);
        assert_eq!(record.bodies[0].prior_slot, Some(old_slot));
        assert!(record.bodies[0].published_slot.is_none());
        assert_eq!(record.bodies[0].displaced_owner.as_deref(), Some(owner));
        assert!(live.get(name).is_none());
        assert_eq!(live.got.load_slot(old_slot.index()), frozen);
        assert!(live.retired_slots().iter().any(|retired| {
            retired.slot == old_slot
                && matches!(
                    &retired.reason,
                    RetireReason::AbiChanging { symbol } if symbol.as_ref() == name
                )
        }));
    }
    assert_eq!(live.retired_slots().len(), 2);
    assert_eq!(
        live.name_candidates(&Symbol::from("g")),
        vec![NameCandidate::new(
            FQSymbol {
                module: ModuleFullPath::from("dep"),
                symbol: Symbol::from("g"),
            },
            Visibility::Private,
        )]
    );
    assert!(live.symbols.contains_key(&Symbol::from("g")));
    assert!(!live.symbols.contains_key(&Symbol::from("h")));
    for (name, revision) in old_revisions {
        assert_eq!(live.symbol_revision(&name), revision.wrapping_add(1));
    }

    let mut growth = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    for (name, seq) in [("g", 1), ("h", 2)] {
        growth
            .install_concrete(
                Symbol::from(name),
                concrete_scheme(),
                Vec::new(),
                None,
                seq,
                CallableOrigin::Plain,
                owner_body(None),
                Some(ast()),
                Vec::new(),
                Visibility::Public,
            )
            .unwrap();
    }
    match live.publish_compiled_staged(
        growth,
        &[],
        HashMap::from([
            (binding_target("m", "g"), "new-g".to_owned()),
            (binding_target("m", "h"), "new-h".to_owned()),
        ]),
    ) {
        Ok(_) => {}
        Err(rejection) => panic!("later growth refused: {}", rejection.reason()),
    }
    for name in ["g", "h"] {
        let new_slot = live.get(name).unwrap().callable_got_slot().unwrap();
        assert!(!old_slots.iter().any(|old| old.index() == new_slot));
    }
}

#[test]
fn absent_retirement_returns_the_displaced_owner_in_its_record() {
    let retained = Arc::new(());
    let mut live = SymbolTable::<Arc<()>, ()>::new_with_params(ModuleFullPath::from("m"));
    live.install_concrete(
        Symbol::from("f"),
        concrete_scheme(),
        Vec::new(),
        None,
        0,
        CallableOrigin::Plain,
        Realization::Body {
            view: view(),
            code: Some(Arc::clone(&retained)),
        },
        Some(ast()),
        Vec::new(),
        Visibility::Public,
    )
    .unwrap();
    assert_eq!(Arc::strong_count(&retained), 2);

    let staging = SymbolTable::<Arc<()>, ()>::new_with_params(ModuleFullPath::from("m"));
    let mut records = live
        .publish_staged(
            staging,
            &[StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("f"),
            }],
        )
        .unwrap();

    assert!(live.get("f").is_none());
    assert_eq!(Arc::strong_count(&retained), 2);
    assert!(Arc::ptr_eq(
        records[0].bodies[0].displaced_owner.as_ref().unwrap(),
        &retained
    ));
    records[0].bodies[0].displaced_owner.take();
    assert_eq!(Arc::strong_count(&retained), 1);
}

#[test]
fn staged_publication_omission_never_removes_live_bindings() {
    let mut live = owner_table("m", Some("old-f"));
    live.install_concrete(
        Symbol::from("g"),
        concrete_scheme(),
        Vec::new(),
        None,
        1,
        CallableOrigin::Plain,
        owner_body(Some("old-g")),
        Some(ast()),
        Vec::new(),
        Visibility::Public,
    )
    .unwrap();
    let old_g_slot = live.get("g").unwrap().callable_got_slot();
    let old_g_revision = live.symbol_revision(&Symbol::from("g"));

    match live.publish_compiled_staged(
        owner_table("m", None),
        &[StagedPublicationDecision::PreserveAbi {
            symbol: Symbol::from("f"),
        }],
        HashMap::from([(binding_target("m", "f"), "new-f".to_owned())]),
    ) {
        Ok(_) => {}
        Err(rejection) => panic!("ordinary replacement refused: {}", rejection.reason()),
    }

    assert_eq!(live.get("g").unwrap().callable_got_slot(), old_g_slot);
    assert_eq!(compiled_owner(&live, "g"), Some("old-g"));
    assert_eq!(live.symbol_revision(&Symbol::from("g")), old_g_revision);
}

#[test]
fn staged_publication_absent_decision_refusal_matrix_is_atomic() {
    #[derive(Clone, Copy)]
    enum ExpectedRefusal {
        Missing,
        NotCallable,
        WrongState,
    }

    fn retirement_live() -> SymbolTable<String, ()> {
        let mut live = owner_table("m", Some("old-f"));
        live.install_binding(
            Symbol::from("type"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::Int,
                    docstring: None,
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
        live.install_template(
            Symbol::from("template"),
            template_scheme(),
            Vec::new(),
            None,
            1,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
        live.expose_candidate(
            Symbol::from("candidate"),
            FQSymbol {
                module: ModuleFullPath::from("dep"),
                symbol: Symbol::from("candidate"),
            },
            Visibility::Private,
        )
        .unwrap();
        live
    }

    fn retirement_staging() -> SymbolTable<String, ()> {
        let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
        staging
            .install_concrete(
                Symbol::from("new"),
                concrete_scheme(),
                Vec::new(),
                None,
                2,
                CallableOrigin::Plain,
                owner_body(None),
                Some(ast()),
                Vec::new(),
                Visibility::Public,
            )
            .unwrap();
        staging
    }

    let cases = vec![
        (
            vec![StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("f"),
            }],
            ExpectedRefusal::WrongState,
        ),
        (
            vec![StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("missing"),
            }],
            ExpectedRefusal::Missing,
        ),
        (
            vec![StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("type"),
            }],
            ExpectedRefusal::NotCallable,
        ),
        (
            vec![StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("template"),
            }],
            ExpectedRefusal::WrongState,
        ),
        (
            vec![StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("candidate"),
            }],
            ExpectedRefusal::WrongState,
        ),
        (
            vec![
                StagedPublicationDecision::ChangeAbi {
                    symbol: Symbol::from("f"),
                },
                StagedPublicationDecision::ChangeAbi {
                    symbol: Symbol::from("f"),
                },
            ],
            ExpectedRefusal::WrongState,
        ),
    ];

    for (decisions, expected) in cases {
        let mut live = retirement_live();
        let live_slot = live.get("f").unwrap().callable_got_slot().unwrap();
        let frozen = std::ptr::dangling::<u8>();
        live.got.store_slot(live_slot, frozen);
        let before = serde_json::to_string(&live).unwrap();
        let revisions = ["f", "type", "template", "candidate"].map(|name| {
            let name = Symbol::from(name);
            (name.clone(), live.symbol_revision(&name))
        });
        let rejection = match live.publish_compiled_staged(
            retirement_staging(),
            &decisions,
            HashMap::from([(binding_target("m", "new"), "submitted".to_owned())]),
        ) {
            Err(rejection) => rejection,
            Ok(_) => panic!("invalid absent-key decision must refuse publication"),
        };
        assert!(matches!(
            (expected, rejection.reason()),
            (
                ExpectedRefusal::Missing,
                LifecycleError::MissingBinding { .. }
            ) | (
                ExpectedRefusal::NotCallable,
                LifecycleError::NotCallable { .. }
            ) | (
                ExpectedRefusal::WrongState,
                LifecycleError::WrongState { .. }
            )
        ));
        let (_, recovered) = rejection.into_parts();
        assert_eq!(recovered[&binding_target("m", "new")], "submitted");
        assert_eq!(serde_json::to_string(&live).unwrap(), before);
        assert_eq!(compiled_owner(&live, "f"), Some("old-f"));
        assert_eq!(live.got.load_slot(live_slot), frozen);
        for (name, revision) in revisions {
            assert_eq!(live.symbol_revision(&name), revision);
        }
    }
}

#[test]
fn absent_retirement_dangling_candidate_refusal_returns_all_submitted_owners() {
    let (old_f, _old_f_drops) = drop_spy("old-f");
    let mut live = SymbolTable::<DropSpy, ()>::new_with_params(ModuleFullPath::from("m"));
    live.install_concrete(
        Symbol::from("f"),
        concrete_scheme(),
        Vec::new(),
        None,
        0,
        CallableOrigin::Plain,
        Realization::Body {
            view: view(),
            code: Some(old_f),
        },
        Some(ast()),
        Vec::new(),
        Visibility::Public,
    )
    .unwrap();
    live.expose_candidate(
        Symbol::from("alias"),
        FQSymbol {
            module: ModuleFullPath::from("m"),
            symbol: Symbol::from("f"),
        },
        Visibility::Private,
    )
    .unwrap();
    let before = serde_json::to_string(&live).unwrap();
    let f_revision = live.symbol_revision(&Symbol::from("f"));
    let g_revision = live.symbol_revision(&Symbol::from("g"));
    let h_revision = live.symbol_revision(&Symbol::from("h"));

    let mut staging = SymbolTable::<DropSpy, ()>::new_with_params(ModuleFullPath::from("m"));
    for (name, seq) in [("g", 1), ("h", 2)] {
        staging
            .install_concrete(
                Symbol::from(name),
                concrete_scheme(),
                Vec::new(),
                None,
                seq,
                CallableOrigin::Plain,
                Realization::Body {
                    view: view(),
                    code: None,
                },
                Some(ast()),
                Vec::new(),
                Visibility::Public,
            )
            .unwrap();
    }
    let (new_g, new_g_drops) = drop_spy("new-g");
    let (new_h, new_h_drops) = drop_spy("new-h");
    let rejection = match live.publish_compiled_staged(
        staging,
        &[StagedPublicationDecision::ChangeAbi {
            symbol: Symbol::from("f"),
        }],
        HashMap::from([
            (binding_target("m", "g"), new_g),
            (binding_target("m", "h"), new_h),
        ]),
    ) {
        Err(rejection) => rejection,
        Ok(_) => panic!("dangling local candidate must refuse the complete publication"),
    };

    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongState { .. }
    ));
    assert_eq!(serde_json::to_string(&live).unwrap(), before);
    assert_eq!(live.symbol_revision(&Symbol::from("f")), f_revision);
    assert_eq!(live.symbol_revision(&Symbol::from("g")), g_revision);
    assert_eq!(live.symbol_revision(&Symbol::from("h")), h_revision);
    assert_eq!(new_g_drops.load(Ordering::SeqCst), 0);
    assert_eq!(new_h_drops.load(Ordering::SeqCst), 0);
    let (_, recovered) = rejection.into_parts();
    assert_eq!(recovered.len(), 2);
    assert_eq!(recovered[&binding_target("m", "g")].label, "new-g");
    assert_eq!(recovered[&binding_target("m", "h")].label, "new-h");
    assert_eq!(new_g_drops.load(Ordering::SeqCst), 0);
    assert_eq!(new_h_drops.load(Ordering::SeqCst), 0);
    drop(recovered);
    assert_eq!(new_g_drops.load(Ordering::SeqCst), 1);
    assert_eq!(new_h_drops.load(Ordering::SeqCst), 1);
}

#[test]
fn staged_publication_refusals_are_atomic_and_owner_safe() {
    let mut live = owner_table("m", Some("live-owner"));
    let old_slot = live.get("f").unwrap().callable_got_slot().unwrap();

    assert!(matches!(
        live.publish_staged(owner_table("other", None), &[]),
        Err(LifecycleError::WrongModule { .. })
    ));
    assert!(matches!(
        live.publish_staged(owner_table("m", None), &[]),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        live.publish_staged(
            owner_table("m", None),
            &[
                StagedPublicationDecision::PreserveAbi {
                    symbol: Symbol::from("f"),
                },
                StagedPublicationDecision::ChangeAbi {
                    symbol: Symbol::from("f"),
                },
            ],
        ),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        live.publish_staged(
            owner_table("m", Some("staging-owner")),
            &[StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("f"),
            }],
        ),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        live.publish_staged(
            owner_table("m", None),
            &[StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("not_staged"),
            }],
        ),
        Err(LifecycleError::WrongState { .. })
    ));

    assert_eq!(live.get("f").unwrap().callable_got_slot(), Some(old_slot));
    let owner = match &live.get("f").unwrap().callable().unwrap().arm.life {
        Life::Concrete {
            realization: Realization::Body { code, .. },
            ..
        } => code.as_deref(),
        _ => None,
    };
    assert_eq!(owner, Some("live-owner"));
    assert!(live.retired_slots().is_empty());
}

#[test]
fn staged_publication_collision_and_late_validation_refusals_are_atomic() {
    let mut collision = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    collision
        .install_binding(
            Symbol::from("f"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::Int,
                    docstring: None,
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
    assert!(matches!(
        collision.publish_staged(owner_table("m", None), &[]),
        Err(LifecycleError::NotCallable { .. })
    ));
    assert!(matches!(
        collision.get("f").unwrap().declaration,
        Decl::Type(_)
    ));

    let mut invalid_live = owner_table("m", Some("retained"));
    let claimed = invalid_live
        .get("f")
        .unwrap()
        .callable()
        .unwrap()
        .arm
        .life
        .claimed_slot()
        .unwrap();
    invalid_live.retired_slots.push(RetiredSlot {
        slot: claimed,
        reason: RetireReason::AbiChanging {
            symbol: Symbol::from("prior"),
        },
    });
    let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    staging
        .install_binding(
            Symbol::from("metadata"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::String,
                    docstring: None,
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
    assert!(matches!(
        invalid_live.publish_staged(staging, &[]),
        Err(LifecycleError::DuplicateSlot { .. })
    ));
    assert!(invalid_live.get("metadata").is_none());
    let retained = match &invalid_live.get("f").unwrap().callable().unwrap().arm.life {
        Life::Concrete {
            realization: Realization::Body { code, .. },
            ..
        } => code.as_deref(),
        _ => None,
    };
    assert_eq!(retained, Some("retained"));
}

#[test]
fn staged_publication_commits_a_deterministic_mixed_cluster() {
    let mut live = owner_table("m", Some("old-f"));
    live.install_concrete(
        Symbol::from("g"),
        concrete_scheme(),
        Vec::new(),
        None,
        1,
        CallableOrigin::Plain,
        Realization::Body {
            view: view(),
            code: Some("old-g".into()),
        },
        Some(ast()),
        Vec::new(),
        Visibility::Public,
    )
    .unwrap();

    let mut staging = owner_table("m", None);
    staging
        .install_template(
            Symbol::from("g"),
            template_scheme(),
            Vec::new(),
            None,
            1,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_concrete(
            Symbol::from("h"),
            concrete_scheme(),
            Vec::new(),
            None,
            2,
            CallableOrigin::Plain,
            owner_body(None),
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_binding(
            Symbol::from("metadata"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::String,
                    docstring: None,
                }),
                Visibility::Private,
            ),
        )
        .unwrap();

    let records = live
        .publish_staged(
            staging,
            &[StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("f"),
            }],
        )
        .unwrap();
    assert_eq!(
        records
            .iter()
            .map(|record| record.symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["f", "h", "g", "metadata"]
    );
    let displaced = records
        .iter()
        .flat_map(|record| &record.bodies)
        .filter_map(|body| body.displaced_owner.as_deref())
        .collect::<Vec<_>>();
    assert_eq!(displaced, vec!["old-f", "old-g"]);
    assert_eq!(live.get("f").unwrap().callable_got_slot(), Some(0));
    assert!(live.get("g").unwrap().callable_got_slot().is_none());
    assert_eq!(live.get("h").unwrap().callable_got_slot(), Some(2));
    assert!(matches!(
        live.get("metadata").unwrap().declaration,
        Decl::Type(_)
    ));
}

#[test]
fn compiled_staged_publication_commits_preserve_change_template_and_new_as_one_cluster() {
    let mut live = owner_table("m", Some("old-f"));
    live.install_concrete(
        Symbol::from("g"),
        concrete_scheme(),
        Vec::new(),
        None,
        1,
        CallableOrigin::Plain,
        owner_body(Some("old-g")),
        Some(ast()),
        Vec::new(),
        Visibility::Public,
    )
    .unwrap();
    live.install_concrete(
        Symbol::from("template"),
        concrete_scheme(),
        Vec::new(),
        None,
        2,
        CallableOrigin::Plain,
        owner_body(Some("old-template")),
        Some(ast()),
        Vec::new(),
        Visibility::Public,
    )
    .unwrap();
    live.expose_candidate(
        Symbol::from("f"),
        FQSymbol {
            module: ModuleFullPath::from("dep.one"),
            symbol: Symbol::from("f"),
        },
        Visibility::Private,
    )
    .unwrap();
    live.module_preamble = Some("live preamble".into());
    live.schema_version = 17;
    live.imports.push(ImportSpec {
        module_path: ModuleFullPath::from("dep.import"),
        alias: None,
        names: ImportNames::Glob,
        span: Span::SYNTHETIC,
    });
    live.exports.push(ExportSpec {
        module_path: ModuleFullPath::from("dep.export"),
        names: ImportNames::Specific(vec![Symbol::from("x")]),
        span: Span::SYNTHETIC,
    });
    live.platforms.push(PlatformSpec {
        name: "io".into(),
        span: Span::SYNTHETIC,
    });
    live.submodules.push(ModDecl {
        name: ModuleName::from("child"),
        visibility: Visibility::Private,
        inline_body: None,
        span: Span::SYNTHETIC,
    });
    let live_written_impl = written_impl("m", "display");
    live.written_trait_impls.push(live_written_impl.clone());

    let old_f_slot = live.get("f").unwrap().callable_got_slot().unwrap();
    let old_g_slot = live.get("g").unwrap().callable_got_slot().unwrap();
    let old_template_slot = live.get("template").unwrap().callable_got_slot().unwrap();
    let revisions = ["f", "g", "template", "h", "metadata"].map(|name| {
        let name = Symbol::from(name);
        (name.clone(), live.symbol_revision(&name))
    });

    let mut staging = owner_table("m", None);
    staging
        .install_concrete(
            Symbol::from("g"),
            concrete_scheme(),
            Vec::new(),
            None,
            1,
            CallableOrigin::Plain,
            owner_body(None),
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_template(
            Symbol::from("template"),
            template_scheme(),
            Vec::new(),
            None,
            2,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_concrete(
            Symbol::from("h"),
            concrete_scheme(),
            Vec::new(),
            None,
            3,
            CallableOrigin::Plain,
            owner_body(None),
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_binding(
            Symbol::from("metadata"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::String,
                    docstring: Some("metadata".into()),
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
    staging
        .expose_candidate(
            Symbol::from("f"),
            FQSymbol {
                module: ModuleFullPath::from("dep.two"),
                symbol: Symbol::from("f"),
            },
            Visibility::Public,
        )
        .unwrap();
    let staged_written_impl = WrittenTraitImpl::new(
        FQTraitName::new(ModuleFullPath::from("traits"), TraitName::from("Eq")),
        FQTypeName::new(ModuleFullPath::from("types"), TypeName::from("Other")),
        ModuleFullPath::from("m"),
        vec![Symbol::from("eq")],
        Visibility::Public,
    );
    staging
        .written_trait_impls
        .push(staged_written_impl.clone());

    let owners = HashMap::from([
        (binding_target("m", "f"), "new-f".to_owned()),
        (binding_target("m", "g"), "new-g".to_owned()),
        (binding_target("m", "h"), "new-h".to_owned()),
    ]);
    let records = match live.publish_compiled_staged(
        staging,
        &[
            StagedPublicationDecision::PreserveAbi {
                symbol: Symbol::from("f"),
            },
            StagedPublicationDecision::ChangeAbi {
                symbol: Symbol::from("g"),
            },
        ],
        owners,
    ) {
        Ok(records) => records,
        Err(rejection) => panic!("compiled publication refused: {}", rejection.reason()),
    };

    assert_eq!(compiled_owner(&live, "f"), Some("new-f"));
    assert_eq!(compiled_owner(&live, "g"), Some("new-g"));
    assert_eq!(compiled_owner(&live, "h"), Some("new-h"));
    assert_eq!(live.get("f").unwrap().callable_got_slot(), Some(old_f_slot));
    assert_ne!(live.get("g").unwrap().callable_got_slot(), Some(old_g_slot));
    assert!(live.get("template").unwrap().callable_got_slot().is_none());
    assert_eq!(
        records
            .iter()
            .flat_map(|record| &record.bodies)
            .filter_map(|body| body.displaced_owner.as_deref())
            .collect::<Vec<_>>(),
        vec!["old-f", "old-g", "old-template"]
    );
    assert!(live.retired_slots().iter().any(|retired| {
        retired.slot.index() == old_g_slot
            && matches!(retired.reason, RetireReason::AbiChanging { .. })
    }));
    assert!(live.retired_slots().iter().any(|retired| {
        retired.slot.index() == old_template_slot
            && matches!(retired.reason, RetireReason::TemplateFlip { .. })
    }));
    let candidates = live.name_candidates(&Symbol::from("f"));
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate.source.module.as_ref() == "dep.one")
    );
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate.source.module.as_ref() == "dep.two")
    );
    assert_eq!(live.module_preamble.as_deref(), Some("live preamble"));
    assert_eq!(live.schema_version, 17);
    assert_eq!(live.imports.len(), 1);
    assert_eq!(live.imports[0].module_path.as_ref(), "dep.import");
    assert_eq!(live.exports.len(), 1);
    assert_eq!(live.exports[0].module_path.as_ref(), "dep.export");
    assert_eq!(live.platforms.len(), 1);
    assert_eq!(live.platforms[0].name, "io");
    assert_eq!(live.submodules.len(), 1);
    assert_eq!(live.submodules[0].name.as_ref(), "child");
    assert_eq!(
        live.written_trait_impls,
        vec![live_written_impl, staged_written_impl]
    );
    for (name, revision) in revisions {
        assert_eq!(live.symbol_revision(&name), revision.wrapping_add(1));
    }
    live.validate_lifecycle().unwrap();
}

fn owner_coverage_staging() -> SymbolTable<String, ()> {
    let mut staging = owner_table("m", None);
    staging
        .install_template(
            Symbol::from("template"),
            template_scheme(),
            Vec::new(),
            None,
            1,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_inline(
            Symbol::from("inline"),
            concrete_scheme(),
            Vec::new(),
            None,
            2,
            None,
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_host_promised(
            Symbol::from("host"),
            concrete_scheme(),
            Vec::new(),
            None,
            3,
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_extern(
            Symbol::from("extern"),
            concrete_scheme(),
            Vec::new(),
            None,
            4,
            None,
            None,
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_overloaded(
            Symbol::from("group"),
            None,
            5,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    staging
        .install_binding(
            Symbol::from("type"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::Int,
                    docstring: None,
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
    staging
        .install_trait_method(
            Symbol::from("method"),
            TraitMethodRecord::new(
                concrete_scheme(),
                Vec::new(),
                None,
                FQTraitName::new(ModuleFullPath::from("m"), TraitName::from("Trait")),
            ),
            Visibility::Public,
        )
        .unwrap();
    staging
        .expose_candidate(
            Symbol::from("candidate"),
            FQSymbol {
                module: ModuleFullPath::from("dep"),
                symbol: Symbol::from("candidate"),
            },
            Visibility::Private,
        )
        .unwrap();
    staging
}

#[test]
fn compiled_staged_publication_requires_exact_concrete_body_owner_keys() {
    let staging = owner_coverage_staging();
    let mut live = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    let rejection = match live.publish_compiled_staged(staging.clone(), &[], HashMap::new()) {
        Err(rejection) => rejection,
        Ok(_) => panic!("missing concrete-body owner must refuse publication"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongState { symbol, .. } if symbol.as_ref() == "f"
    ));
    assert!(rejection.into_parts().1.is_empty());
    assert!(live.all_symbols().next().is_none());

    for extra in [
        "template",
        "inline",
        "host",
        "extern",
        "group",
        "type",
        "Trait.method",
        "candidate",
        "absent",
    ] {
        let owners = HashMap::from([
            (binding_target("m", "f"), "body-owner".to_owned()),
            (binding_target("m", extra), "extra-owner".to_owned()),
        ]);
        let rejection = match live.publish_compiled_staged(staging.clone(), &[], owners) {
            Err(rejection) => rejection,
            Ok(_) => panic!("owner for '{extra}' must refuse publication"),
        };
        assert!(matches!(
            rejection.reason(),
            LifecycleError::WrongState { symbol, .. } if symbol.as_ref() == extra
        ));
        let (_, recovered) = rejection.into_parts();
        assert_eq!(recovered.len(), 2);
        assert_eq!(
            recovered.get(&binding_target("m", "f")).map(String::as_str),
            Some("body-owner")
        );
        assert_eq!(
            recovered
                .get(&binding_target("m", extra))
                .map(String::as_str),
            Some("extra-owner")
        );
        assert!(live.all_symbols().next().is_none());
    }
}

#[test]
fn compiled_staged_publication_returns_all_owners_after_late_multi_row_refusal() {
    let (old_owner, _old_drops) = drop_spy("old-f");
    let mut live = SymbolTable::<DropSpy, ()>::new_with_params(ModuleFullPath::from("m"));
    live.install_concrete(
        Symbol::from("f"),
        concrete_scheme(),
        Vec::new(),
        None,
        0,
        CallableOrigin::Plain,
        Realization::Body {
            view: view(),
            code: Some(old_owner),
        },
        Some(ast()),
        Vec::new(),
        Visibility::Public,
    )
    .unwrap();
    live.expose_candidate(
        Symbol::from("f"),
        FQSymbol {
            module: ModuleFullPath::from("dep"),
            symbol: Symbol::from("f"),
        },
        Visibility::Private,
    )
    .unwrap();
    let claimed = live
        .get("f")
        .unwrap()
        .callable()
        .unwrap()
        .arm
        .life
        .claimed_slot()
        .unwrap();
    live.retired_slots.push(RetiredSlot {
        slot: claimed,
        reason: RetireReason::AbiChanging {
            symbol: Symbol::from("prior"),
        },
    });
    let f_revision = live.symbol_revision(&Symbol::from("f"));
    let g_revision = live.symbol_revision(&Symbol::from("g"));
    let candidates = live.name_candidates(&Symbol::from("f")).to_vec();
    let tombstones = live.retired_slots.clone();
    let live_written_impl = written_impl("m", "display");
    live.written_trait_impls.push(live_written_impl.clone());

    let mut staging = SymbolTable::<DropSpy, ()>::new_with_params(ModuleFullPath::from("m"));
    for (name, seq) in [("f", 0), ("g", 1)] {
        staging
            .install_concrete(
                Symbol::from(name),
                concrete_scheme(),
                Vec::new(),
                None,
                seq,
                CallableOrigin::Plain,
                Realization::Body {
                    view: view(),
                    code: None,
                },
                Some(ast()),
                Vec::new(),
                Visibility::Public,
            )
            .unwrap();
    }
    let (new_f, new_f_drops) = drop_spy("new-f");
    let (new_g, new_g_drops) = drop_spy("new-g");
    let owners = HashMap::from([
        (binding_target("m", "f"), new_f),
        (binding_target("m", "g"), new_g),
    ]);

    let rejection = match live.publish_compiled_staged(
        staging,
        &[StagedPublicationDecision::PreserveAbi {
            symbol: Symbol::from("f"),
        }],
        owners,
    ) {
        Err(rejection) => rejection,
        Ok(_) => panic!("duplicate live claim must refuse the complete cluster"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::DuplicateSlot { .. }
    ));
    assert_eq!(new_f_drops.load(Ordering::SeqCst), 0);
    assert_eq!(new_g_drops.load(Ordering::SeqCst), 0);
    assert!(live.get("g").is_none());
    assert_eq!(live.symbol_revision(&Symbol::from("f")), f_revision);
    assert_eq!(live.symbol_revision(&Symbol::from("g")), g_revision);
    assert_eq!(live.name_candidates(&Symbol::from("f")), candidates);
    assert_eq!(live.retired_slots, tombstones);
    assert_eq!(live.written_trait_impls, vec![live_written_impl]);

    let (_, recovered) = rejection.into_parts();
    assert_eq!(recovered.len(), 2);
    assert_eq!(recovered[&binding_target("m", "f")].label, "new-f");
    assert_eq!(recovered[&binding_target("m", "g")].label, "new-g");
    assert_eq!(new_f_drops.load(Ordering::SeqCst), 0);
    assert_eq!(new_g_drops.load(Ordering::SeqCst), 0);
    drop(recovered);
    assert_eq!(new_f_drops.load(Ordering::SeqCst), 1);
    assert_eq!(new_g_drops.load(Ordering::SeqCst), 1);
}

#[test]
fn compiled_owner_attachment_recovers_earlier_rows_on_late_candidate_inconsistency() {
    let live = SymbolTable::<DropSpy, ()>::new_with_params(ModuleFullPath::from("m"));
    let mut staging = SymbolTable::<DropSpy, ()>::new_with_params(ModuleFullPath::from("m"));
    for (name, seq) in [("f", 0), ("g", 1)] {
        staging
            .install_concrete(
                Symbol::from(name),
                concrete_scheme(),
                Vec::new(),
                None,
                seq,
                CallableOrigin::Plain,
                Realization::Body {
                    view: view(),
                    code: None,
                },
                Some(ast()),
                Vec::new(),
                Visibility::Public,
            )
            .unwrap();
    }
    let mut plan = live.plan_staged_publication(staging, &[]).unwrap();
    plan.candidate.symbols.remove(&Symbol::from("g"));
    let (f_owner, f_drops) = drop_spy("f");
    let (g_owner, g_drops) = drop_spy("g");

    let (reason, recovered) = attach_compiled_publication_owners(
        &mut plan,
        HashMap::from([
            (binding_target("m", "f"), f_owner),
            (binding_target("m", "g"), g_owner),
        ]),
    )
    .unwrap_err();
    assert!(matches!(
        reason,
        LifecycleError::MissingBinding { symbol } if symbol.as_ref() == "g"
    ));
    assert_eq!(recovered.len(), 2);
    assert_eq!(recovered[&binding_target("m", "f")].label, "f");
    assert_eq!(recovered[&binding_target("m", "g")].label, "g");
    assert_eq!(f_drops.load(Ordering::SeqCst), 0);
    assert_eq!(g_drops.load(Ordering::SeqCst), 0);
}

#[test]
fn compiled_staged_publication_refusal_matrix_is_atomic_and_returns_submitted_owners() {
    let owners = || HashMap::from([(binding_target("m", "f"), "new-f".to_owned())]);

    let mut wrong_module = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    let rejection =
        match wrong_module.publish_compiled_staged(owner_table("other", None), &[], owners()) {
            Err(rejection) => rejection,
            Ok(_) => panic!("wrong-module staging must be refused"),
        };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongModule { .. }
    ));
    assert_eq!(rejection.into_parts().1[&binding_target("m", "f")], "new-f");
    assert!(wrong_module.all_symbols().next().is_none());

    let mut owner_bearing_staging = owner_table("m", Some("illegal-staging-owner"));
    let mut live = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    let rejection = match live.publish_compiled_staged(
        std::mem::replace(
            &mut owner_bearing_staging,
            SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("unused")),
        ),
        &[],
        owners(),
    ) {
        Err(rejection) => rejection,
        Ok(_) => panic!("owner-bearing staging must be refused"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongState { .. }
    ));
    assert_eq!(rejection.into_parts().1[&binding_target("m", "f")], "new-f");
    assert!(live.all_symbols().next().is_none());

    let mut broken_staging = owner_table("m", None);
    let broken_transition = broken_staging
        .mark_broken(
            &Symbol::from("f"),
            BrokenProvenance::new(
                FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("cause"),
                },
                "failed".into(),
            ),
        )
        .unwrap();
    assert!(broken_transition.displaced_owner.is_none());
    let rejection = match live.publish_compiled_staged(broken_staging, &[], owners()) {
        Err(rejection) => rejection,
        Ok(_) => panic!("broken staging must be refused"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongState { .. }
    ));
    assert_eq!(rejection.into_parts().1[&binding_target("m", "f")], "new-f");
    assert!(live.all_symbols().next().is_none());

    let mut collision = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    collision
        .install_binding(
            Symbol::from("f"),
            Binding::new(
                Decl::Type(TypeRecord::Intrinsic {
                    ty: Type::Int,
                    docstring: None,
                }),
                Visibility::Private,
            ),
        )
        .unwrap();
    let collision_revision = collision.symbol_revision(&Symbol::from("f"));
    let rejection = match collision.publish_compiled_staged(owner_table("m", None), &[], owners()) {
        Err(rejection) => rejection,
        Ok(_) => panic!("non-callable collision must be refused"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::NotCallable { .. }
    ));
    assert_eq!(rejection.into_parts().1[&binding_target("m", "f")], "new-f");
    assert!(matches!(
        collision.get("f").unwrap().declaration,
        Decl::Type(_)
    ));
    assert_eq!(
        collision.symbol_revision(&Symbol::from("f")),
        collision_revision
    );

    let mut missing_decision = owner_table("m", Some("old-f"));
    let old_slot = missing_decision
        .get("f")
        .unwrap()
        .callable_got_slot()
        .unwrap();
    let decision_revision = missing_decision.symbol_revision(&Symbol::from("f"));
    let rejection =
        match missing_decision.publish_compiled_staged(owner_table("m", None), &[], owners()) {
            Err(rejection) => rejection,
            Ok(_) => panic!("missing ABI decision must be refused"),
        };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongState { .. }
    ));
    assert_eq!(rejection.into_parts().1[&binding_target("m", "f")], "new-f");
    assert_eq!(
        missing_decision.get("f").unwrap().callable_got_slot(),
        Some(old_slot)
    );
    assert_eq!(compiled_owner(&missing_decision, "f"), Some("old-f"));
    assert_eq!(
        missing_decision.symbol_revision(&Symbol::from("f")),
        decision_revision
    );
    assert!(missing_decision.retired_slots().is_empty());

    let mut exhausted = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    for index in 0..GOT_TABLE_SIZE {
        exhausted.retired_slots.push(RetiredSlot {
            slot: CallableSlot(index),
            reason: RetireReason::AbiChanging {
                symbol: Symbol::from("retired"),
            },
        });
    }
    let tombstones = exhausted.retired_slots.clone();
    let revision = exhausted.symbol_revision(&Symbol::from("f"));
    let rejection = match exhausted.publish_compiled_staged(owner_table("m", None), &[], owners()) {
        Err(rejection) => rejection,
        Ok(_) => panic!("full live GOT must refuse a fresh published slot"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::SlotMint(SlotMintError::Exhausted(_))
    ));
    assert_eq!(rejection.into_parts().1[&binding_target("m", "f")], "new-f");
    assert!(exhausted.get("f").is_none());
    assert_eq!(exhausted.retired_slots, tombstones);
    assert_eq!(exhausted.symbol_revision(&Symbol::from("f")), revision);
}

fn live_table_with_publication_state() -> SymbolTable<String, ()> {
    let mut live = owner_table("m", Some("old-f"));
    live.expose_candidate(
        Symbol::from("f"),
        FQSymbol {
            module: ModuleFullPath::from("dep"),
            symbol: Symbol::from("f"),
        },
        Visibility::Private,
    )
    .unwrap();
    live.retired_slots.push(RetiredSlot {
        slot: CallableSlot(7),
        reason: RetireReason::AbiChanging {
            symbol: Symbol::from("retired"),
        },
    });
    live
}

#[test]
fn compiled_staged_publication_rejects_staging_tombstone_without_live_mutation() {
    let mut live = live_table_with_publication_state();
    let live_slot = live.get("f").unwrap().callable_got_slot();
    let live_revision = live.symbol_revision(&Symbol::from("f"));
    let live_tombstones = live.retired_slots.clone();
    let live_candidates = live.name_candidates(&Symbol::from("f")).to_vec();
    let live_symbols = live
        .all_symbols()
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();

    let mut staging = owner_table("m", None);
    staging.retired_slots.push(RetiredSlot {
        slot: CallableSlot(8),
        reason: RetireReason::AbiChanging {
            symbol: Symbol::from("staged-retired"),
        },
    });
    let rejection = match live.publish_compiled_staged(
        staging,
        &[StagedPublicationDecision::PreserveAbi {
            symbol: Symbol::from("f"),
        }],
        HashMap::from([(binding_target("m", "f"), "new-f".to_owned())]),
    ) {
        Err(rejection) => rejection,
        Ok(_) => panic!("staging tombstone must refuse compiled publication"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongState { expected, .. }
            if *expected == "unpublished staging without retired slots"
    ));
    let (_, recovered) = rejection.into_parts();
    assert_eq!(recovered.len(), 1);
    assert_eq!(recovered[&binding_target("m", "f")], "new-f");
    assert_eq!(live.get("f").unwrap().callable_got_slot(), live_slot);
    assert_eq!(compiled_owner(&live, "f"), Some("old-f"));
    assert_eq!(live.symbol_revision(&Symbol::from("f")), live_revision);
    assert_eq!(live.retired_slots, live_tombstones);
    assert_eq!(live.name_candidates(&Symbol::from("f")), live_candidates);
    assert_eq!(
        live.all_symbols()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>(),
        live_symbols
    );
}

#[test]
fn compiled_staged_publication_rejects_declared_life_without_live_mutation() {
    let mut live = live_table_with_publication_state();
    let live_slot = live.get("f").unwrap().callable_got_slot();
    let live_revision = live.symbol_revision(&Symbol::from("f"));
    let live_tombstones = live.retired_slots.clone();
    let live_candidates = live.name_candidates(&Symbol::from("f")).to_vec();
    let live_symbols = live
        .all_symbols()
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();

    let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    staging
        .declare(
            Symbol::from("f"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            Visibility::Public,
        )
        .unwrap();
    assert!(matches!(
        &staging.get("f").unwrap().callable().unwrap().arm.life,
        Life::Declared { .. }
    ));
    let rejection = match live.publish_compiled_staged(
        staging,
        &[],
        HashMap::from([(binding_target("m", "f"), "new-f".to_owned())]),
    ) {
        Err(rejection) => rejection,
        Ok(_) => panic!("Declared staging must refuse compiled publication"),
    };
    assert!(matches!(
        rejection.reason(),
        LifecycleError::WrongState { expected, .. }
            if *expected == "a settled, non-broken staged callable"
    ));
    let (_, recovered) = rejection.into_parts();
    assert_eq!(recovered.len(), 1);
    assert_eq!(recovered[&binding_target("m", "f")], "new-f");
    assert_eq!(live.get("f").unwrap().callable_got_slot(), live_slot);
    assert_eq!(compiled_owner(&live, "f"), Some("old-f"));
    assert_eq!(live.symbol_revision(&Symbol::from("f")), live_revision);
    assert_eq!(live.retired_slots, live_tombstones);
    assert_eq!(live.name_candidates(&Symbol::from("f")), live_candidates);
    assert_eq!(
        live.all_symbols()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>(),
        live_symbols
    );
}

#[test]
fn staged_slotless_replacement_retires_slot_and_keeps_unrelated_live_candidates() {
    let mut live = owner_table("m", Some("compiled"));
    let old_slot = live.get("f").unwrap().callable_got_slot().unwrap();
    live.expose_candidate(
        Symbol::from("f"),
        FQSymbol {
            module: ModuleFullPath::from("dependency"),
            symbol: Symbol::from("f"),
        },
        Visibility::Public,
    )
    .unwrap();

    let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    staging
        .install_template(
            Symbol::from("f"),
            template_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    let records = live.publish_staged(staging, &[]).unwrap();
    assert_eq!(
        records[0].bodies[0].prior_slot.map(|slot| slot.index()),
        Some(old_slot)
    );
    assert!(records[0].bodies[0].published_slot.is_none());
    assert_eq!(
        records[0].bodies[0].displaced_owner.as_deref(),
        Some("compiled")
    );
    assert_eq!(live.retired_slots()[0].slot.index(), old_slot);
    assert_eq!(live.name_candidates(&Symbol::from("f")).len(), 2);
}

#[test]
fn staged_slotted_primitive_cannot_be_relabelled_inline_or_host_promised() {
    let mut live = slotted_rust_primitive_table();
    let slot = live.get("primitive").unwrap().callable_got_slot().unwrap();
    let mut inline = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    inline
        .install_inline(
            Symbol::from("primitive"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            None,
            Visibility::Public,
        )
        .unwrap();
    assert!(matches!(
        live.publish_staged(inline, &[]),
        Err(LifecycleError::WrongState { .. })
    ));
    assert_eq!(
        live.get("primitive").unwrap().callable_got_slot(),
        Some(slot)
    );
    assert!(live.retired_slots().is_empty());

    let mut host = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    host.install_host_promised(
        Symbol::from("primitive"),
        concrete_scheme(),
        Vec::new(),
        None,
        0,
        Visibility::Public,
    )
    .unwrap();
    assert!(matches!(
        live.publish_staged(host, &[]),
        Err(LifecycleError::WrongState { .. })
    ));
    assert_eq!(
        live.get("primitive").unwrap().callable_got_slot(),
        Some(slot)
    );
    assert!(live.retired_slots().is_empty());
}

fn raw_callable(scheme: Scheme, origin: CallableOrigin, life: Life<()>) -> Binding<()> {
    Binding::new(
        Decl::Callable(Callable {
            docstring: None,
            seq: 0,
            origin,
            arm: CallableArm::new(scheme, Vec::new(), life),
        }),
        Visibility::Public,
    )
}

#[test]
fn load_validation_rejects_duplicate_claims_and_claim_tombstone_collision() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let slot = CallableSlot(2);
    table.replace_binding(
        Symbol::from("a"),
        raw_callable(
            concrete_scheme(),
            CallableOrigin::Plain,
            Life::Concrete {
                slot,
                realization: body(),
                minted_from: None,
                ast: Some(ast()),
                callees: Vec::new(),
                value_use: false,
                mode_summary: None,
            },
        ),
    );
    table.replace_binding(
        Symbol::from("b"),
        raw_callable(
            concrete_scheme(),
            CallableOrigin::Plain,
            Life::Broken {
                slot,
                error: BrokenProvenance {
                    broken_by: FQSymbol {
                        module: ModuleFullPath::from("m"),
                        symbol: Symbol::from("b"),
                    },
                    message: "plant".into(),
                },
            },
        ),
    );
    assert_eq!(
        table.validate_lifecycle(),
        Err(LifecycleError::DuplicateSlot { slot: 2 })
    );

    table.symbols.remove("b");
    table.retired_slots.push(RetiredSlot {
        slot,
        reason: RetireReason::AbiChanging {
            symbol: Symbol::from("old"),
        },
    });
    assert_eq!(
        table.validate_lifecycle(),
        Err(LifecycleError::DuplicateSlot { slot: 2 })
    );
}

#[test]
fn load_validation_counts_declared_prior_and_duplicate_tombstones_as_claims() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let slot = CallableSlot(3);
    table.replace_binding(
        Symbol::from("live"),
        raw_callable(
            concrete_scheme(),
            CallableOrigin::Plain,
            Life::Concrete {
                slot,
                realization: body(),
                minted_from: None,
                ast: Some(ast()),
                callees: Vec::new(),
                value_use: false,
                mode_summary: None,
            },
        ),
    );
    table.replace_binding(
        Symbol::from("pending"),
        raw_callable(
            concrete_scheme(),
            CallableOrigin::Plain,
            Life::Declared { prior: Some(slot) },
        ),
    );
    assert_eq!(
        table.validate_lifecycle(),
        Err(LifecycleError::DuplicateSlot { slot: 3 })
    );

    table.symbols.clear();
    table.replace_binding(
        Symbol::from("pending"),
        raw_callable(
            concrete_scheme(),
            CallableOrigin::Plain,
            Life::Declared {
                prior: Some(CallableSlot(GOT_TABLE_SIZE)),
            },
        ),
    );
    assert_eq!(
        table.validate_lifecycle(),
        Err(LifecycleError::SlotOutOfRange {
            slot: GOT_TABLE_SIZE
        })
    );

    table.symbols.clear();
    for symbol in ["old-a", "old-b"] {
        table.retired_slots.push(RetiredSlot {
            slot,
            reason: RetireReason::AbiChanging {
                symbol: Symbol::from(symbol),
            },
        });
    }
    assert_eq!(
        table.validate_lifecycle(),
        Err(LifecycleError::DuplicateSlot { slot: 3 })
    );
}

#[test]
fn load_validation_rejects_nonconcrete_and_out_of_range_claims() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table.replace_binding(
        Symbol::from("bad"),
        raw_callable(
            template_scheme(),
            CallableOrigin::Plain,
            Life::Concrete {
                slot: CallableSlot(0),
                realization: body(),
                minted_from: None,
                ast: Some(ast()),
                callees: Vec::new(),
                value_use: false,
                mode_summary: None,
            },
        ),
    );
    assert!(matches!(
        table.validate_lifecycle(),
        Err(LifecycleError::NonConcreteSlot { .. })
    ));

    table.symbols.clear();
    table.retired_slots.push(RetiredSlot {
        slot: CallableSlot(GOT_TABLE_SIZE),
        reason: RetireReason::AbiChanging {
            symbol: Symbol::from("old"),
        },
    });
    assert_eq!(
        table.validate_lifecycle(),
        Err(LifecycleError::SlotOutOfRange {
            slot: GOT_TABLE_SIZE
        })
    );
}

fn fq_type() -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("T"))
}

fn origins() -> Vec<CallableOrigin> {
    vec![
        CallableOrigin::Plain,
        CallableOrigin::TraitMethod {
            shell: FQSymbol {
                module: ModuleFullPath::from("m"),
                symbol: Symbol::from("impl"),
            },
            trait_name: FQTraitName::new(ModuleFullPath::from("m"), TraitName::from("Show")),
            impl_type: fq_type(),
        },
        CallableOrigin::Ctor {
            type_name: fq_type(),
            tag: 0,
            field_count: 0,
            internal: false,
            type_def: None,
        },
        CallableOrigin::Accessor {
            type_name: fq_type(),
            field: Symbol::from("v"),
        },
        CallableOrigin::RustPrimitive,
        CallableOrigin::PlatformEffect {
            scheduling_class: SchedulingClass::Sequential,
            poll_shape: false,
        },
    ]
}

#[derive(Debug, Clone, Copy)]
enum State {
    Declared,
    Template,
    Concrete,
    Inline,
    HostPromised,
    Broken,
}

fn life_for(origin: &CallableOrigin, state: State) -> Life<()> {
    match state {
        State::Declared => Life::Declared { prior: None },
        State::Template => {
            let body = match origin {
                CallableOrigin::RustPrimitive => TemplateBody::UniformRust {
                    abi_name: LinkerSymbol::from("shim"),
                },
                CallableOrigin::Ctor { .. } | CallableOrigin::Accessor { .. } => {
                    TemplateBody::Synth(SynthSpec { variant: ast() })
                }
                _ => TemplateBody::Ast(ast()),
            };
            Life::Template {
                body,
                kind: TemplateKind::Parametric,
                callees: Vec::new(),
            }
        }
        State::Concrete => {
            let realization = match origin {
                CallableOrigin::PlatformEffect { .. } => Realization::Dll,
                CallableOrigin::RustPrimitive => Realization::ExternShim {
                    borrowed_sibling: None,
                },
                _ => body(),
            };
            Life::Concrete {
                slot: CallableSlot(0),
                realization,
                minted_from: None,
                ast: None,
                callees: Vec::new(),
                value_use: false,
                mode_summary: None,
            }
        }
        State::Inline => Life::Inline { mode_summary: None },
        State::HostPromised => Life::HostPromised,
        State::Broken => Life::Broken {
            slot: CallableSlot(0),
            error: BrokenProvenance {
                broken_by: FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("f"),
                },
                message: "plant".into(),
            },
        },
    }
}

fn expected_legal(origin: &CallableOrigin, state: State) -> bool {
    match origin {
        CallableOrigin::PlatformEffect { .. } => matches!(state, State::Concrete),
        CallableOrigin::RustPrimitive => matches!(
            state,
            State::Template | State::Concrete | State::Inline | State::HostPromised
        ),
        CallableOrigin::Ctor { .. } | CallableOrigin::Accessor { .. } => {
            matches!(state, State::Template | State::Concrete | State::Broken)
        }
        _ => matches!(
            state,
            State::Declared | State::Template | State::Concrete | State::Broken
        ),
    }
}

#[test]
fn load_validation_exercises_exhaustive_origin_life_matrix() {
    let states = [
        State::Declared,
        State::Template,
        State::Concrete,
        State::Inline,
        State::HostPromised,
        State::Broken,
    ];
    for origin in origins() {
        for state in states {
            let scheme = if matches!(state, State::Template) {
                template_scheme()
            } else {
                concrete_scheme()
            };
            let mut table = SymbolTable::new(ModuleFullPath::from("m"));
            table.replace_binding(
                Symbol::from("f"),
                raw_callable(scheme, origin.clone(), life_for(&origin, state)),
            );
            assert_eq!(
                table.validate_lifecycle().is_ok(),
                expected_legal(&origin, state),
                "origin={origin:?}, state={state:?}"
            );
        }
    }
}

#[test]
fn funnels_reject_incompatible_template_and_realization_payloads_atomically() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(
        &mut table,
        "template",
        template_scheme(),
        CallableOrigin::Plain,
    );
    assert!(matches!(
        table.settle_template(
            &Symbol::from("template"),
            TemplateBody::Synth(SynthSpec { variant: ast() }),
            TemplateKind::Parametric,
            Vec::new(),
        ),
        Err(LifecycleError::IllegalRealization { .. })
    ));
    assert!(matches!(
        table.get("template").unwrap().callable().unwrap().arm.life,
        Life::Declared { prior: None }
    ));

    assert!(matches!(
        table.install_concrete(
            Symbol::from("concrete"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            Realization::Dll,
            None,
            Vec::new(),
            Visibility::Public,
        ),
        Err(LifecycleError::IllegalRealization { .. })
    ));
    assert!(table.get("concrete").is_none());
}

#[test]
fn serde_and_clone_bypass_are_rejected_by_validation() {
    let mut valid = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut valid, "f", concrete_scheme(), CallableOrigin::Plain);
    let slot = valid
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();

    let mut cloned = valid.clone();
    cloned.replace_binding(
        Symbol::from("g"),
        raw_callable(
            concrete_scheme(),
            CallableOrigin::Plain,
            Life::Broken {
                slot,
                error: BrokenProvenance {
                    broken_by: FQSymbol {
                        module: ModuleFullPath::from("m"),
                        symbol: Symbol::from("g"),
                    },
                    message: "clone plant".into(),
                },
            },
        ),
    );
    assert!(matches!(
        cloned.validate_lifecycle(),
        Err(LifecycleError::DuplicateSlot { .. })
    ));

    let json = serde_json::to_string(&cloned).unwrap();
    let restored: SymbolTable = serde_json::from_str(&json).unwrap();
    assert!(matches!(
        restored.validate_lifecycle(),
        Err(LifecycleError::DuplicateSlot { .. })
    ));
}

#[test]
fn platform_manifest_slot_and_fresh_mint_share_one_claim_space() {
    let mut table = SymbolTable::new(ModuleFullPath::from("platform"));
    let platform = table
        .install_platform(
            Symbol::from("effect"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            SchedulingClass::Sequential,
            false,
            0,
            Visibility::Public,
        )
        .unwrap();
    assert_eq!(platform.index(), 0);

    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let fresh = table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    assert_eq!(fresh.index(), 1);
}

#[test]
fn illegal_funnels_refuse_without_mutating_the_table() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    assert!(matches!(
        table.declare(
            Symbol::from("effect"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::PlatformEffect {
                scheduling_class: SchedulingClass::Sequential,
                poll_shape: false,
            },
            Visibility::Public,
        ),
        Err(LifecycleError::IllegalOriginState { .. })
    ));
    assert!(table.get("effect").is_none());

    table
        .install_platform(
            Symbol::from("effect"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            SchedulingClass::Sequential,
            false,
            0,
            Visibility::Public,
        )
        .unwrap();
    assert!(matches!(
        table.mark_broken(
            &Symbol::from("effect"),
            BrokenProvenance {
                broken_by: FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("effect"),
                },
                message: "plant".into(),
            },
        ),
        Err(LifecycleError::IllegalOriginState { .. })
    ));
    assert!(matches!(
        table.get("effect").unwrap().callable().unwrap().arm.life,
        Life::Concrete {
            realization: Realization::Dll,
            ..
        }
    ));
}

#[test]
fn install_instance_derives_key_preserves_backlink_and_mints_slot() {
    let mut table = SymbolTable::new(ModuleFullPath::from("consumer"));
    table
        .install_template(
            Symbol::from("generic"),
            template_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();

    let link = InstanceLink::from_type_args(
        CallableTarget::Binding(FQSymbol {
            module: ModuleFullPath::from("producer"),
            symbol: Symbol::from("generic"),
        }),
        vec![ConcreteType::Int],
    );
    let expected_key = crate::concrete_callable_key(
        &FQSymbol {
            module: "producer".into(),
            symbol: "generic".into(),
        },
        &ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int)),
    )
    .unwrap();
    let (key, slot) = table
        .install_instance(
            link.clone(),
            scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
            Vec::new(),
            None,
            1,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert_eq!(key, expected_key);
    assert_eq!(slot.index(), 0);
    assert_eq!(
        table.get(key.as_ref()).unwrap().callable_got_slot(),
        Some(0)
    );
    let callable = table.get(key.as_ref()).unwrap().callable().unwrap();
    assert!(matches!(
        &callable.arm.life,
        Life::Concrete {
            minted_from: Some(found),
            ..
        } if found == &link
    ));
}

#[test]
fn mismatched_instance_candidate_is_rejected_before_mutation() {
    let mut table = SymbolTable::new(ModuleFullPath::from("consumer"));
    let link = InstanceLink::from_type_args(
        CallableTarget::Binding(FQSymbol {
            module: ModuleFullPath::from("producer"),
            symbol: Symbol::from("generic"),
        }),
        vec![ConcreteType::Int],
    );
    let expected = crate::concrete_callable_key(
        &FQSymbol {
            module: "producer".into(),
            symbol: "generic".into(),
        },
        &ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int)),
    )
    .unwrap();
    let actual = Symbol::from("wrong-key");
    let slot = table
        .mint_callable_slot(&scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int))))
        .unwrap();
    let candidate = Callable {
        docstring: None,
        seq: 0,
        origin: CallableOrigin::Plain,
        arm: CallableArm::new(
            scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
            Vec::new(),
            Life::Concrete {
                slot,
                realization: body(),
                minted_from: Some(link),
                ast: Some(ast()),
                callees: Vec::new(),
                value_use: false,
                mode_summary: None,
            },
        ),
    };

    assert_eq!(
        table.install_settled_callable(actual.clone(), candidate, Visibility::Private),
        Err(LifecycleError::InstanceKeyMismatch {
            symbol: actual.clone(),
            expected,
        })
    );
    assert!(table.get(actual.as_ref()).is_none());
    assert_eq!(table.all_symbols().count(), 0);
}

#[test]
fn restored_instance_with_tampered_storage_key_is_rejected_exactly() {
    let mut table = SymbolTable::new(ModuleFullPath::from("consumer"));
    let link = InstanceLink::from_type_args(
        CallableTarget::Binding(FQSymbol {
            module: ModuleFullPath::from("producer"),
            symbol: Symbol::from("generic"),
        }),
        vec![ConcreteType::Int],
    );
    let expected = crate::concrete_callable_key(
        &FQSymbol {
            module: "producer".into(),
            symbol: "generic".into(),
        },
        &ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int)),
    )
    .unwrap();
    table
        .install_instance(
            link,
            scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();

    let actual = Symbol::from("tampered-key");
    let mut serialized = serde_json::to_value(&table).unwrap();
    let symbols = serialized
        .get_mut("symbols")
        .and_then(serde_json::Value::as_object_mut)
        .expect("symbol table serializes its private binding map");
    let binding = symbols
        .remove(expected.as_ref())
        .expect("installed instance key is serialized");
    symbols.insert(actual.to_string(), binding);
    let restored: SymbolTable = serde_json::from_value(serialized).unwrap();

    assert_eq!(
        restored.validate_lifecycle(),
        Err(LifecycleError::InstanceKeyMismatch {
            symbol: actual,
            expected,
        })
    );
}

#[test]
fn typed_demand_and_link_share_one_lossless_instance_key() {
    let selected_scheme = key_template(vec![Type::Var(0), Type::Var(1)], Type::Int, vec![0, 1]);
    let template = FQSymbol {
        module: ModuleFullPath::from("producer"),
        symbol: Symbol::from("apply"),
    };
    let vec_name = FQTypeName::new(ModuleFullPath::from("collections"), TypeName::from("Vec"));
    let args = vec![
        ConcreteType::ADT(vec_name.clone(), vec![ConcreteType::Int]),
        ConcreteType::Fn(vec![ConcreteType::String], Box::new(ConcreteType::Bool)),
    ];
    let target = CallableTarget::Binding(template.clone());
    let demand = MonoDemand::from_type_args(target.clone(), args.clone(), Span::SYNTHETIC);
    let link = demand.instance_link();
    assert_eq!(link.template, target);
    assert_eq!(link.type_args, args);
    assert_eq!(
        demand.instance_key(&selected_scheme).unwrap(),
        link.instance_key(&selected_scheme).unwrap()
    );

    let other_home = InstanceLink::from_type_args(
        CallableTarget::Binding(FQSymbol {
            module: ModuleFullPath::from("other"),
            symbol: Symbol::from("apply"),
        }),
        link.type_args.clone(),
    );
    assert_ne!(
        link.instance_key(&selected_scheme).unwrap(),
        other_home.instance_key(&selected_scheme).unwrap()
    );
    let other_adt_arg = InstanceLink::from_type_args(
        link.template.clone(),
        vec![
            ConcreteType::ADT(vec_name, vec![ConcreteType::String]),
            ConcreteType::Fn(vec![ConcreteType::String], Box::new(ConcreteType::Bool)),
        ],
    );
    assert_ne!(
        link.instance_key(&selected_scheme).unwrap(),
        other_adt_arg.instance_key(&selected_scheme).unwrap()
    );
}

fn trait_name() -> FQTraitName {
    FQTraitName::new(ModuleFullPath::from("traits"), TraitName::from("Display"))
}

fn impl_type() -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("types"), TypeName::from("Thing"))
}

fn written_impl(writer: &str, method: &str) -> WrittenTraitImpl {
    WrittenTraitImpl::new(
        trait_name(),
        impl_type(),
        ModuleFullPath::from(writer),
        vec![Symbol::from(method)],
        Visibility::Public,
    )
}

#[test]
fn trait_method_install_is_idempotent_and_conflict_checked() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let method = TraitMethodRecord::new(
        concrete_scheme(),
        vec![Symbol::from("self")],
        Some("display".into()),
        trait_name(),
    );
    table
        .install_trait_method(Symbol::from("display"), method.clone(), Visibility::Public)
        .unwrap();
    table
        .install_trait_method(Symbol::from("display"), method, Visibility::Public)
        .unwrap();
    assert_eq!(table.name_candidates(&Symbol::from("display")).len(), 1);
    let divergent = TraitMethodRecord::new(
        template_scheme(),
        vec![Symbol::from("self")],
        None,
        trait_name(),
    );
    assert!(matches!(
        table.install_trait_method(Symbol::from("display"), divergent, Visibility::Public),
        Err(LifecycleError::WrongState { .. })
    ));
    assert_eq!(table.name_candidates(&Symbol::from("display")).len(), 1);
    assert_eq!(table.all_symbols().count(), 1);
    table
        .install_binding(
            crate::member_key("Display", "occupied"),
            non_callable_binding(),
        )
        .unwrap();
    assert!(matches!(
        table.install_trait_method(
            Symbol::from("occupied"),
            TraitMethodRecord::new(concrete_scheme(), Vec::new(), None, trait_name()),
            Visibility::Private,
        ),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn trait_method_dedicated_funnel_cannot_be_bypassed_or_removed() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let name = Symbol::from("display");
    let canonical = crate::member_key("Display", "display");
    let method = TraitMethodRecord::new(
        concrete_scheme(),
        vec![Symbol::from("self")],
        Some("original".into()),
        trait_name(),
    );
    let direct = Binding::new(Decl::TraitMethod(method.clone()), Visibility::Public);
    assert!(matches!(
        table.install_binding(name.clone(), direct),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(table.get(name.as_ref()).is_none());

    table
        .install_trait_method(name.clone(), method, Visibility::Public)
        .unwrap();
    let divergent = Binding::new(
        Decl::TraitMethod(TraitMethodRecord::new(
            template_scheme(),
            Vec::new(),
            Some("divergent".into()),
            trait_name(),
        )),
        Visibility::Private,
    );
    assert!(matches!(
        table.install_binding(canonical.clone(), divergent),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        table.remove_non_callable(&canonical),
        Err(LifecycleError::WrongState { .. })
    ));
    assert_eq!(
        table
            .get(canonical.as_ref())
            .unwrap()
            .trait_method()
            .unwrap()
            .docstring
            .as_deref(),
        Some("original")
    );
}

#[test]
fn trait_method_is_dispatchable_but_never_defined() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    table
        .install_trait_method(
            Symbol::from("display"),
            TraitMethodRecord::new(
                concrete_scheme(),
                vec![Symbol::from("self")],
                None,
                trait_name(),
            ),
            Visibility::Public,
        )
        .unwrap();

    let binding = table.get("Display.display").unwrap();
    assert!(binding.trait_method().is_some());
    assert!(binding.is_callable_target());
    assert!(table.get("display").is_none());
    assert_eq!(table.name_candidates(&Symbol::from("display")).len(), 1);
    assert_eq!(table.codegen_targets().count(), 0);
}

#[test]
fn trait_method_uses_qualified_storage_and_bare_projection() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let method = Symbol::from("display");
    table
        .install_trait_method(
            method.clone(),
            TraitMethodRecord::new(
                concrete_scheme(),
                vec![Symbol::from("self")],
                None,
                trait_name(),
            ),
            Visibility::Public,
        )
        .unwrap();

    let canonical = crate::member_key("Display", "display");
    assert!(table.get(method.as_ref()).is_none());
    assert!(
        table
            .get(canonical.as_ref())
            .unwrap()
            .trait_method()
            .is_some()
    );
    assert_eq!(
        table.name_candidates(&method),
        vec![NameCandidate::new(
            FQSymbol {
                module: ModuleFullPath::from("traits"),
                symbol: canonical,
            },
            Visibility::Public,
        )]
    );
    table.validate_lifecycle().unwrap();
}

#[test]
fn trait_method_funnels_refuse_wrong_home_and_source_atomically() {
    let mut table = SymbolTable::new(ModuleFullPath::from("consumer"));
    assert!(matches!(
        table.install_trait_method(
            Symbol::from("display"),
            TraitMethodRecord::new(concrete_scheme(), Vec::new(), None, trait_name()),
            Visibility::Public,
        ),
        Err(LifecycleError::WrongState { .. })
    ));
    assert_eq!(table.all_symbols().count(), 0);
    assert!(table.name_candidates(&Symbol::from("display")).is_empty());

    assert!(matches!(
        table.expose_candidate(
            Symbol::from("display"),
            FQSymbol {
                module: ModuleFullPath::from("consumer"),
                symbol: Symbol::from("display"),
            },
            Visibility::Public,
        ),
        Err(LifecycleError::MissingBinding { .. })
    ));
    assert!(table.name_candidates(&Symbol::from("display")).is_empty());
}

#[test]
fn accessor_and_trait_method_candidates_coexist() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let method = Symbol::from("display");
    let accessor = FQSymbol {
        module: ModuleFullPath::from("types"),
        symbol: Symbol::from("Box.display"),
    };
    table
        .expose_candidate(method.clone(), accessor.clone(), Visibility::Public)
        .unwrap();
    table
        .install_trait_method(
            method.clone(),
            TraitMethodRecord::new(concrete_scheme(), Vec::new(), None, trait_name()),
            Visibility::Public,
        )
        .unwrap();

    assert!(table.get(method.as_ref()).is_none());
    let candidates = table.name_candidates(&method);
    assert_eq!(candidates.len(), 2);
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate.source == accessor)
    );
}

#[test]
fn name_candidate_same_source_dedups_and_public_wins() {
    let mut table = SymbolTable::new(ModuleFullPath::from("consumer"));
    let local = Symbol::from("display");
    let source = FQSymbol {
        module: ModuleFullPath::from("traits"),
        symbol: crate::member_key("Display", "display"),
    };
    table
        .expose_candidate(local.clone(), source.clone(), Visibility::Private)
        .unwrap();
    table
        .expose_candidate(local.clone(), source.clone(), Visibility::Public)
        .unwrap();
    table
        .expose_candidate(local.clone(), source.clone(), Visibility::Private)
        .unwrap();

    assert_eq!(
        table.name_candidates(&local),
        vec![NameCandidate::new(source, Visibility::Public)]
    );
}

#[test]
fn all_name_candidates_includes_private_while_public_projection_filters() {
    let mut table = SymbolTable::new(ModuleFullPath::from("consumer"));
    table
        .expose_candidate(
            Symbol::from("value"),
            FQSymbol {
                module: ModuleFullPath::from("private-source"),
                symbol: Symbol::from("hidden"),
            },
            Visibility::Private,
        )
        .unwrap();
    table
        .expose_candidate(
            Symbol::from("value"),
            FQSymbol {
                module: ModuleFullPath::from("public-source"),
                symbol: Symbol::from("visible"),
            },
            Visibility::Public,
        )
        .unwrap();

    let all = table.all_name_candidates().collect::<Vec<_>>();
    assert_eq!(all.len(), 2);
    assert!(
        all.iter()
            .any(|(_, candidate)| candidate.visibility == Visibility::Private)
    );
    let public = table.public_name_candidates().collect::<Vec<_>>();
    assert_eq!(public.len(), 1);
    assert_eq!(
        public[0].1.source.module,
        ModuleFullPath::from("public-source")
    );
}

#[test]
fn inline_and_extern_installers_preserve_declared_mode_summary() {
    let summary = ModeSummary {
        result_unique: true,
        ..ModeSummary::default()
    };
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table
        .install_inline(
            Symbol::from("inline"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            Some(summary.clone()),
            Visibility::Public,
        )
        .unwrap();
    table
        .install_extern(
            Symbol::from("extern"),
            concrete_scheme(),
            Vec::new(),
            None,
            1,
            None,
            Some(summary.clone()),
            Visibility::Public,
        )
        .unwrap();

    assert_eq!(table.get("inline").unwrap().mode_summary(), Some(&summary));
    assert_eq!(table.get("extern").unwrap().mode_summary(), Some(&summary));
}

#[test]
fn distinct_name_candidate_sources_remain_candidates() {
    let mut table = SymbolTable::new(ModuleFullPath::from("consumer"));
    let local = Symbol::from("show");
    for (module, parent) in [("alpha", "Display"), ("beta", "Render")] {
        table
            .expose_candidate(
                local.clone(),
                FQSymbol {
                    module: ModuleFullPath::from(module),
                    symbol: crate::member_key(parent, "show"),
                },
                Visibility::Public,
            )
            .unwrap();
    }
    let candidates = table.name_candidates(&local);
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].source.module, ModuleFullPath::from("alpha"));
    assert_eq!(candidates[1].source.module, ModuleFullPath::from("beta"));
}

#[test]
fn name_candidate_load_validation_rejects_dangling_sources() {
    let method = Symbol::from("display");
    let mut dangling = SymbolTable::new(ModuleFullPath::from("consumer"));
    dangling
        .expose_candidate(
            method,
            FQSymbol {
                module: ModuleFullPath::from("missing"),
                symbol: crate::member_key("Display", "display"),
            },
            Visibility::Public,
        )
        .unwrap();
    let tables = SymbolTables::new();
    assert!(matches!(
        dangling.validate_name_candidates(&tables),
        Err(LifecycleError::MissingBinding { .. })
    ));

    let mut wrong_home = SymbolTable::new(ModuleFullPath::from("traits"));
    let canonical = crate::member_key("Display", "display");
    wrong_home.replace_binding(
        canonical.clone(),
        Binding::new(
            Decl::TraitMethod(TraitMethodRecord::new(
                concrete_scheme(),
                Vec::new(),
                None,
                FQTraitName::new(ModuleFullPath::from("other"), TraitName::from("Display")),
            )),
            Visibility::Public,
        ),
    );
    assert!(matches!(
        wrong_home.validate_lifecycle(),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn cross_table_candidate_validation_direct_probes_terminal() {
    let mut home = SymbolTable::new(ModuleFullPath::from("traits"));
    home.install_trait_method(
        Symbol::from("display"),
        TraitMethodRecord::new(concrete_scheme(), Vec::new(), None, trait_name()),
        Visibility::Public,
    )
    .unwrap();
    let source = FQSymbol {
        module: home.path.clone(),
        symbol: crate::member_key("Display", "display"),
    };
    let mut consumer = SymbolTable::new(ModuleFullPath::from("consumer"));
    consumer
        .expose_candidate(Symbol::from("show"), source.clone(), Visibility::Public)
        .unwrap();
    let tables = SymbolTables::new();
    tables.insert(home.path.clone(), home);
    consumer.validate_name_candidates(&tables).unwrap();

    tables
        .get_mut(&source.module)
        .unwrap()
        .remove_binding(&source.symbol);
    assert!(matches!(
        consumer.validate_name_candidates(&tables),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn module_replacement_drops_name_candidates_with_the_table() {
    let path = ModuleFullPath::from("traits");
    let mut old = SymbolTable::new(path.clone());
    old.install_trait_method(
        Symbol::from("display"),
        TraitMethodRecord::new(concrete_scheme(), Vec::new(), None, trait_name()),
        Visibility::Public,
    )
    .unwrap();
    let tables = SymbolTables::new();
    tables.insert(path.clone(), old);
    let replacement = SymbolTable::new(path.clone());
    let displaced = tables.insert(path.clone(), replacement).unwrap();

    assert_eq!(displaced.name_candidates(&Symbol::from("display")).len(), 1);
    let current = tables.get(&path).unwrap();
    assert!(current.name_candidates(&Symbol::from("display")).is_empty());
    assert!(current.get("Display.display").is_none());
}

#[test]
fn remove_non_callable_refuses_trait_and_trait_method_terminals() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let trait_key = Symbol::from("Display");
    table
        .install_binding(
            trait_key.clone(),
            Binding::new(
                Decl::Trait(TraitRecord::new(
                    TraitDeclInfo {
                        name: TraitName::from("Display"),
                        type_params: Vec::new(),
                        methods: Vec::new(),
                    },
                    None,
                )),
                Visibility::Public,
            ),
        )
        .unwrap();
    table
        .install_trait_method(
            Symbol::from("display"),
            TraitMethodRecord::new(concrete_scheme(), Vec::new(), None, trait_name()),
            Visibility::Public,
        )
        .unwrap();
    let canonical = crate::member_key("Display", "display");

    assert!(matches!(
        table.remove_non_callable(&trait_key),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        table.remove_non_callable(&canonical),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        table.install_binding(trait_key.clone(), non_callable_binding()),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn checked_resettlement_is_atomic_and_moves_slots_once() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", template_scheme(), CallableOrigin::Plain);
    table
        .settle_checked_template(
            &Symbol::from("f"),
            template_scheme(),
            ast(),
            TemplateKind::Parametric,
            Vec::new(),
        )
        .unwrap();
    let first = table
        .settle_checked_concrete(
            &Symbol::from("f"),
            concrete_scheme(),
            ast(),
            view(),
            Vec::new(),
        )
        .unwrap();
    table
        .settle_checked_template(
            &Symbol::from("f"),
            template_scheme(),
            ast(),
            TemplateKind::Parametric,
            Vec::new(),
        )
        .unwrap();
    assert_eq!(table.retired_slots().len(), 1);
    assert_eq!(table.retired_slots()[0].slot, first);
    let second = table
        .settle_checked_concrete(
            &Symbol::from("f"),
            concrete_scheme(),
            ast(),
            view(),
            Vec::new(),
        )
        .unwrap();
    assert_ne!(first, second);

    let tombstones = table.retired_slots().to_vec();
    assert!(matches!(
        table.settle_checked_template(
            &Symbol::from("f"),
            concrete_scheme(),
            ast(),
            TemplateKind::Parametric,
            Vec::new(),
        ),
        Err(LifecycleError::ConcreteTemplate { .. })
    ));
    assert_eq!(
        table.get("f").unwrap().callable_got_slot(),
        Some(second.index())
    );
    assert_eq!(table.retired_slots(), tombstones);
    table.validate_lifecycle().unwrap();
}

#[test]
fn checked_view_identity_refuses_without_mutation() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("f");
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let mut wrong = view();
    wrong.name = Symbol::from("other");
    assert!(matches!(
        table.settle_checked_concrete(&name, concrete_scheme(), ast(), wrong.clone(), Vec::new(),),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        table.get("f").unwrap().callable().unwrap().arm.life,
        Life::Declared { prior: None }
    ));
    assert!(table.retired_slots().is_empty());

    table
        .settle_checked_concrete(&name, concrete_scheme(), ast(), view(), Vec::new())
        .unwrap();
    assert!(matches!(
        table.publish_body_ownership(&binding_target("m", "f"), ModeSummary::default(), wrong),
        Err(LifecycleError::WrongState { .. })
    ));
    let binding = table.get("f").unwrap();
    assert!(binding.mode_summary().is_none());
    assert_eq!(binding.codegen_view().unwrap().name, name);
    assert!(matches!(
        binding.codegen_view().unwrap().body,
        MonoExpr::IntLit { .. }
    ));
}

#[test]
fn checked_body_rejects_synth_uniform_instance_and_foreign_realizations() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table
        .install_template(
            Symbol::from("synth"),
            template_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Ctor {
                type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Synth")),
                tag: 0,
                field_count: 0,
                internal: false,
                type_def: None,
            },
            TemplateBody::Synth(SynthSpec::new(ast())),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert!(matches!(
        table.settle_checked_concrete(
            &Symbol::from("synth"),
            concrete_scheme(),
            ast(),
            view(),
            Vec::new(),
        ),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        table.get("synth").unwrap().callable().unwrap().arm.life,
        Life::Template {
            body: TemplateBody::Synth(_),
            ..
        }
    ));

    table
        .install_template(
            Symbol::from("uniform"),
            template_scheme(),
            Vec::new(),
            None,
            1,
            CallableOrigin::RustPrimitive,
            TemplateBody::UniformRust {
                abi_name: LinkerSymbol::from("uniform_shim"),
            },
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert!(matches!(
        table.settle_checked_concrete(
            &Symbol::from("uniform"),
            concrete_scheme(),
            ast(),
            view(),
            Vec::new(),
        ),
        Err(LifecycleError::WrongState { .. })
    ));

    let link = InstanceLink::from_type_args(
        CallableTarget::Binding(FQSymbol {
            module: ModuleFullPath::from("producer"),
            symbol: Symbol::from("generic"),
        }),
        vec![ConcreteType::Int],
    );
    let (instance, _) = table
        .install_instance(
            link,
            scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
            Vec::new(),
            None,
            1,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert!(matches!(
        table.settle_checked_concrete(&instance, concrete_scheme(), ast(), view(), Vec::new(),),
        Err(LifecycleError::WrongState { .. })
    ));

    table
        .install_concrete(
            Symbol::from("foreign"),
            concrete_scheme(),
            Vec::new(),
            None,
            2,
            CallableOrigin::PlatformEffect {
                scheduling_class: SchedulingClass::Sequential,
                poll_shape: false,
            },
            Realization::Dll,
            None,
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert!(matches!(
        table.settle_checked_concrete(
            &Symbol::from("foreign"),
            concrete_scheme(),
            ast(),
            view(),
            Vec::new(),
        ),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn declared_scheme_update_preserves_prior() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    let slot = table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    declare(&mut table, "f", template_scheme(), CallableOrigin::Plain);

    table
        .update_declared_scheme(&Symbol::from("f"), concrete_scheme())
        .unwrap();
    let callable = table.get("f").unwrap().callable().unwrap();
    assert_eq!(callable.arm.scheme.ty, Type::Int);
    assert!(matches!(callable.arm.life, Life::Declared { prior: Some(found) } if found == slot));
}

#[test]
fn checked_settlement_uses_final_scheme() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", template_scheme(), CallableOrigin::Plain);
    table
        .update_declared_scheme(&Symbol::from("f"), concrete_scheme())
        .unwrap();
    table
        .settle_checked_concrete(
            &Symbol::from("f"),
            concrete_scheme(),
            ast(),
            view(),
            Vec::new(),
        )
        .unwrap();
    table.set_value_use(&Symbol::from("f"), true).unwrap();
    table
        .publish_body_ownership(&binding_target("m", "f"), ModeSummary::default(), view())
        .unwrap();
    table
        .settle_checked_concrete(
            &Symbol::from("f"),
            concrete_scheme(),
            ast(),
            view(),
            Vec::new(),
        )
        .unwrap();
    let binding = table.get("f").unwrap();
    assert_eq!(binding.callable().unwrap().arm.scheme.ty, Type::Int);
    assert!(!binding.value_use());
    assert!(binding.mode_summary().is_none());
    assert!(binding.codegen_view().unwrap().mode_summary.is_none());
    assert!(matches!(
        table.update_declared_scheme(&Symbol::from("f"), concrete_scheme()),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn replace_callees_canonicalizes_both_settled_states() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    let b = FQSymbol {
        module: ModuleFullPath::from("z"),
        symbol: Symbol::from("b"),
    };
    let a = FQSymbol {
        module: ModuleFullPath::from("a"),
        symbol: Symbol::from("a"),
    };
    table
        .replace_callees(&Symbol::from("f"), vec![b.clone(), a.clone(), b])
        .unwrap();
    assert_eq!(
        table.get("f").unwrap().callees(),
        &[
            a,
            FQSymbol {
                module: ModuleFullPath::from("z"),
                symbol: Symbol::from("b"),
            }
        ]
    );

    declare(
        &mut table,
        "template",
        template_scheme(),
        CallableOrigin::Plain,
    );
    table
        .settle_template(
            &Symbol::from("template"),
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
        )
        .unwrap();
    table
        .replace_callees(
            &Symbol::from("template"),
            vec![
                FQSymbol {
                    module: ModuleFullPath::from("z"),
                    symbol: Symbol::from("b"),
                },
                FQSymbol {
                    module: ModuleFullPath::from("a"),
                    symbol: Symbol::from("a"),
                },
                FQSymbol {
                    module: ModuleFullPath::from("z"),
                    symbol: Symbol::from("b"),
                },
            ],
        )
        .unwrap();
    assert_eq!(table.get("template").unwrap().callees().len(), 2);
}

#[test]
fn ownership_publication_keeps_summary_twins_equal() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    let summary = ModeSummary::default();
    let mut replacement = ownership_annotated_view();
    replacement.mode_summary = None;
    table
        .publish_body_ownership(&binding_target("m", "f"), summary.clone(), replacement)
        .unwrap();
    let binding = table.get("f").unwrap();
    assert_eq!(binding.mode_summary(), Some(&summary));
    assert_eq!(
        binding.codegen_view().unwrap().mode_summary.as_ref(),
        Some(&summary)
    );
    assert!(matches!(
        &binding.codegen_view().unwrap().body,
        MonoExpr::StringLit {
            escapes: Some(false),
            confined: Some(true),
            unique_static: Some(true),
            ..
        }
    ));
}

#[test]
fn ownership_and_value_use_refuse_wrong_or_published_states() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(
        &mut table,
        "declared",
        concrete_scheme(),
        CallableOrigin::Plain,
    );
    assert!(matches!(
        table.set_value_use(&Symbol::from("declared"), true),
        Err(LifecycleError::WrongState { .. })
    ));

    table
        .install_concrete(
            Symbol::from("published"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            Realization::Body {
                view: view(),
                code: Some(()),
            },
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert!(matches!(
        table.publish_body_ownership(
            &binding_target("m", "published"),
            ModeSummary::default(),
            view(),
        ),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn non_callable_remove_and_prior_free_declared_discard_are_narrow() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table
        .install_binding(Symbol::from("alias"), non_callable_binding())
        .unwrap();
    assert!(
        table
            .remove_non_callable(&Symbol::from("alias"))
            .unwrap()
            .is_some()
    );

    declare(
        &mut table,
        "fresh",
        concrete_scheme(),
        CallableOrigin::Plain,
    );
    table.discard_declared(&Symbol::from("fresh")).unwrap();
    assert!(table.get("fresh").is_none());

    declare(&mut table, "live", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("live"), body(), Some(ast()), Vec::new())
        .unwrap();
    assert!(matches!(
        table.remove_non_callable(&Symbol::from("live")),
        Err(LifecycleError::WrongState { .. })
    ));
    declare(&mut table, "live", concrete_scheme(), CallableOrigin::Plain);
    assert!(matches!(
        table.discard_declared(&Symbol::from("live")),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        table.get("live").unwrap().callable().unwrap().arm.life,
        Life::Declared {
            prior: Some(slot)
        } if slot.index() == 0
    ));
    assert!(table.retired_slots().is_empty());
}

#[test]
fn retained_callables_roll_back_first_write_and_reimpl() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    let retained = table
        .retain_callables(&[Symbol::from("f"), Symbol::from("g")])
        .unwrap();
    declare(&mut table, "f", template_scheme(), CallableOrigin::Plain);
    table
        .settle_template(
            &Symbol::from("f"),
            TemplateBody::Ast(ast()),
            TemplateKind::Parametric,
            Vec::new(),
        )
        .unwrap();
    declare(&mut table, "g", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("g"), body(), Some(ast()), Vec::new())
        .unwrap();
    assert_eq!(table.retired_slots().len(), 1);

    table.rollback_callables(retained).unwrap();
    assert_eq!(table.get("f").unwrap().callable_got_slot(), Some(0));
    assert!(table.get("g").is_none());
    assert!(table.retired_slots().is_empty());
    table.validate_lifecycle().unwrap();
}

#[test]
fn retained_callable_batch_commit_and_overlap_are_explicit() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let retained = table.retain_callables(&[Symbol::from("f")]).unwrap();
    assert!(matches!(
        table.retain_callables(&[Symbol::from("f")]),
        Err(LifecycleError::WrongState { .. })
    ));
    declare(&mut table, "f", concrete_scheme(), CallableOrigin::Plain);
    table
        .settle_concrete(&Symbol::from("f"), body(), Some(ast()), Vec::new())
        .unwrap();
    retained.commit();
    assert_eq!(table.get("f").unwrap().callable_got_slot(), Some(0));
    table
        .retain_callables(&[Symbol::from("f")])
        .unwrap()
        .commit();
}

#[test]
fn retained_callables_refuse_published_fresh_slot() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let retained = table.retain_callables(&[Symbol::from("f")]).unwrap();
    let slot = table
        .install_concrete(
            Symbol::from("f"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    table
        .got
        .store_slot(slot.index(), std::ptr::dangling::<u8>());
    assert!(matches!(
        table.rollback_callables(retained),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(table.get("f").is_some());

    let mut code_table = SymbolTable::new(ModuleFullPath::from("code"));
    let retained = code_table
        .retain_callables(&[Symbol::from("compiled")])
        .unwrap();
    code_table
        .install_concrete(
            Symbol::from("compiled"),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            Realization::Body {
                view: view(),
                code: Some(()),
            },
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert!(matches!(
        code_table.rollback_callables(retained),
        Err(LifecycleError::WrongState { .. })
    ));
}

#[test]
fn rollback_callables_refuses_published_template_hidden_slot() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("f");
    let retained = table.retain_callables(std::slice::from_ref(&name)).unwrap();
    let slot = table
        .install_concrete(
            name.clone(),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    table
        .settle_checked_template(
            &name,
            template_scheme(),
            ast(),
            TemplateKind::Parametric,
            Vec::new(),
        )
        .unwrap();
    table
        .got
        .store_slot(slot.index(), std::ptr::dangling::<u8>());

    assert!(matches!(
        table.rollback_callables(retained),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(matches!(
        table.get("f").unwrap().callable().unwrap().arm.life,
        Life::Template { .. }
    ));
    assert_eq!(table.retired_slots()[0].slot, slot);
}

#[test]
fn rollback_callables_refuses_published_removed_binding_slot() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("f");
    let retained = table.retain_callables(std::slice::from_ref(&name)).unwrap();
    let slot = table
        .install_concrete(
            name.clone(),
            concrete_scheme(),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            body(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    table.retire_abi_changing(&name).unwrap();
    table
        .got
        .store_slot(slot.index(), std::ptr::dangling::<u8>());

    assert!(matches!(
        table.rollback_callables(retained),
        Err(LifecycleError::WrongState { .. })
    ));
    assert!(table.get("f").is_none());
    assert_eq!(table.retired_slots()[0].slot, slot);
}

#[test]
fn staged_impl_shell_rolls_back_absent_and_prior() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let first = written_impl("writer", "first");
    let staged = table.stage_trait_impl_shell(&first).unwrap();
    let key = crate::trait_impl_key(&first.impl_type, &first.trait_name);
    assert!(table.get(key.as_ref()).is_some());
    table.rollback_trait_impl_shell(staged).unwrap();
    assert!(table.get(key.as_ref()).is_none());

    table.stage_trait_impl_shell(&first).unwrap().commit();
    let replacement = written_impl("writer", "replacement");
    let staged = table.stage_trait_impl_shell(&replacement).unwrap();
    table.rollback_trait_impl_shell(staged).unwrap();
    assert!(binding_matches_written_trait_impl(
        table.get(key.as_ref()).unwrap(),
        &first
    ));

    let staged = table.stage_trait_impl_shell(&replacement).unwrap();
    staged.commit();
    assert!(binding_matches_written_trait_impl(
        table.get(key.as_ref()).unwrap(),
        &replacement
    ));

    table.replace_binding(Symbol::from("occupied"), non_callable_binding());
    let mut colliding = replacement.clone();
    colliding.impl_type =
        FQTypeName::new(ModuleFullPath::from("types"), TypeName::from("Occupied"));
    let occupied_key = crate::trait_impl_key(&colliding.impl_type, &colliding.trait_name);
    table.replace_binding(occupied_key, non_callable_binding());
    assert!(table.stage_trait_impl_shell(&colliding).is_err());
}

#[test]
fn staged_impl_shell_refuses_payload_identical_intervening_write() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let record = written_impl("writer", "staged");
    let staged = table.stage_trait_impl_shell(&record).unwrap();
    let key = crate::trait_impl_key(&record.impl_type, &record.trait_name);
    let identical = table.get(key.as_ref()).unwrap().clone();
    table.install_binding(key.clone(), identical).unwrap();

    assert!(table.rollback_trait_impl_shell(staged).is_err());
    assert!(binding_matches_written_trait_impl(
        table.get(key.as_ref()).unwrap(),
        &record
    ));
}

#[test]
fn stage_impl_shell_refuses_wrong_trait_home_without_mutation() {
    let mut table = SymbolTable::new(ModuleFullPath::from("wrong-home"));
    let record = written_impl("writer", "staged");

    assert!(table.stage_trait_impl_shell(&record).is_err());
    assert_eq!(table.all_symbols().count(), 0);
    assert!(
        table
            .transactions
            .0
            .lock()
            .unwrap()
            .staged_shells
            .is_empty()
    );
}

#[test]
fn staged_impl_shell_refuses_intervening_occupant() {
    let mut table = SymbolTable::new(ModuleFullPath::from("traits"));
    let staged_record = written_impl("writer", "staged");
    let staged = table.stage_trait_impl_shell(&staged_record).unwrap();
    let key = crate::trait_impl_key(&staged_record.impl_type, &staged_record.trait_name);
    let intervening = written_impl("other-writer", "other");
    table.replace_binding(key.clone(), written_trait_impl_binding(&intervening));
    assert!(table.rollback_trait_impl_shell(staged).is_err());
    assert!(binding_matches_written_trait_impl(
        table.get(key.as_ref()).unwrap(),
        &intervening
    ));
}

#[test]
fn transaction_tokens_refuse_wrong_table_identity() {
    let source = SymbolTable::new(ModuleFullPath::from("source"));
    let mut other = SymbolTable::new(ModuleFullPath::from("other"));
    let retained = source.retain_callables(&[Symbol::from("method")]).unwrap();
    assert!(matches!(
        other.rollback_callables(retained),
        Err(LifecycleError::WrongState { .. })
    ));
    source
        .retain_callables(&[Symbol::from("method")])
        .unwrap()
        .commit();

    let mut trait_home = SymbolTable::new(ModuleFullPath::from("traits"));
    let mut other_trait_home = SymbolTable::new(ModuleFullPath::from("traits"));
    let record = written_impl("writer", "staged");
    let staged = trait_home.stage_trait_impl_shell(&record).unwrap();
    assert!(other_trait_home.rollback_trait_impl_shell(staged).is_err());
    assert_eq!(trait_home.all_symbols().count(), 1);
    trait_home.stage_trait_impl_shell(&record).unwrap().commit();
}

#[test]
fn written_impl_upsert_is_one_per_key_and_writer_checked() {
    let mut table = SymbolTable::new(ModuleFullPath::from("writer"));
    let first = written_impl("writer", "first");
    table.upsert_written_trait_impl(first.clone()).unwrap();
    let replacement = written_impl("writer", "replacement");
    table
        .upsert_written_trait_impl(replacement.clone())
        .unwrap();
    assert_eq!(table.written_trait_impls, vec![replacement.clone()]);

    let mut other = written_impl("writer", "other");
    other.impl_type = FQTypeName::new(ModuleFullPath::from("types"), TypeName::from("Other"));
    table.upsert_written_trait_impl(other.clone()).unwrap();
    assert_eq!(table.written_trait_impls, vec![replacement, other]);

    let before = table.written_trait_impls.clone();
    assert!(
        table
            .upsert_written_trait_impl(written_impl("wrong-writer", "bad"))
            .is_err()
    );
    assert_eq!(table.written_trait_impls, before);

    let empty = WrittenTraitImpl::new(
        trait_name(),
        impl_type(),
        ModuleFullPath::from("writer"),
        Vec::new(),
        Visibility::Public,
    );
    assert!(table.upsert_written_trait_impl(empty).is_err());
    assert_eq!(table.written_trait_impls, before);

    table.written_trait_impls.push(first.clone());
    table.written_trait_impls.push(first);
    let duplicate_before = table.written_trait_impls.clone();
    assert!(
        table
            .upsert_written_trait_impl(written_impl("writer", "new"))
            .is_err()
    );
    assert_eq!(table.written_trait_impls, duplicate_before);
}

// spec: spec/03-types.md §3.6.3 — complete substitutions identify concrete instances
#[test]
fn result_only_substitutions_distinguish_instances_and_reuse_equal_vectors() {
    let selected_scheme = key_template(
        vec![],
        Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
        vec![0],
    );
    let target = CallableTarget::Binding(FQSymbol {
        module: ModuleFullPath::from("producer"),
        symbol: Symbol::from("returned_closure"),
    });
    let int = MonoDemand::from_type_args(target.clone(), vec![ConcreteType::Int], Span::new(1, 4));
    let string = MonoDemand::from_type_args(
        target.clone(),
        vec![ConcreteType::String],
        Span::new(10, 14),
    );
    let int_again = MonoDemand::from_type_args(target, vec![ConcreteType::Int], Span::new(20, 24));

    assert_eq!(int.instance_link().type_args, vec![ConcreteType::Int]);
    assert_eq!(string.instance_link().type_args, vec![ConcreteType::String]);
    assert_ne!(
        int.instance_key(&selected_scheme).unwrap(),
        string.instance_key(&selected_scheme).unwrap()
    );
    assert_eq!(
        int.instance_key(&selected_scheme).unwrap(),
        int_again.instance_key(&selected_scheme).unwrap()
    );
    let mut instances = std::collections::HashSet::new();
    assert!(instances.insert(int.instance_link()));
    assert!(instances.insert(string.instance_link()));
    assert!(!instances.insert(int_again.instance_link()));
    assert_eq!(instances.len(), 2);
}

#[test]
fn demand_key_uses_storage_symbol_but_excludes_diagnostic_site() {
    let selected_scheme = key_template(vec![Type::Var(0)], Type::Var(0), vec![0]);
    let template = FQSymbol {
        module: ModuleFullPath::from("producer"),
        symbol: Symbol::from("written-alias"),
    };
    let args = vec![ConcreteType::Int];
    let target = CallableTarget::Binding(template.clone());
    let first = MonoDemand::from_type_args(target.clone(), args.clone(), Span::new(1, 4));
    let later_site = MonoDemand::from_type_args(target.clone(), args.clone(), Span::new(40, 80));
    assert_eq!(first.instance_link().template, target);
    assert_eq!(
        first.instance_key(&selected_scheme).unwrap(),
        later_site.instance_key(&selected_scheme).unwrap()
    );
    assert_eq!(
        first.instance_key(&selected_scheme).unwrap(),
        first
            .instance_link()
            .instance_key(&selected_scheme)
            .unwrap()
    );

    let other_storage_symbol = MonoDemand::from_type_args(
        CallableTarget::Binding(FQSymbol {
            module: ModuleFullPath::from("producer"),
            symbol: Symbol::from("terminal-storage-key"),
        }),
        args,
        first.site,
    );
    assert_ne!(
        first.instance_key(&selected_scheme).unwrap(),
        other_storage_symbol.instance_key(&selected_scheme).unwrap()
    );
}

fn packet_a_accessor_origin(field: &str) -> CallableOrigin {
    CallableOrigin::Accessor {
        type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Box")),
        field: Symbol::from(field),
    }
}

fn packet_a_view(name: &str) -> MonoDefnVariant {
    MonoDefnVariant {
        name: Symbol::from(name),
        params: Vec::new(),
        body: MonoExpr::IntLit {
            value: 1,
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        },
        span: Span::SYNTHETIC,
        mode_summary: None,
    }
}

fn install_packet_a_accessor<C: CodeStore>(
    table: &mut SymbolTable<C>,
    name: &str,
    code: Option<C>,
) -> CallableSlot {
    table
        .install_concrete(
            Symbol::from(name),
            concrete_scheme(),
            Vec::new(),
            Some("old".into()),
            7,
            packet_a_accessor_origin("v"),
            Realization::Body {
                view: packet_a_view(name),
                code,
            },
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap()
}

#[test]
fn unpublished_synthesized_template_replacement_preserves_complete_candidates() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("Box.v");
    let old_slot = install_packet_a_accessor(&mut table, name.as_ref(), None);
    table
        .install_binding(Symbol::from("Trait.v"), non_callable_binding())
        .unwrap();
    for (source, visibility) in [
        (name.clone(), Visibility::Public),
        (Symbol::from("Trait.v"), Visibility::Private),
    ] {
        table
            .expose_candidate(
                Symbol::from("v"),
                FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: source,
                },
                visibility,
            )
            .unwrap();
    }
    let candidates_before = table.name_candidates(&Symbol::from("v"));

    table
        .replace_unpublished_synthesized_template(
            name.clone(),
            template_scheme(),
            vec![Symbol::from("self")],
            Some("new".into()),
            packet_a_accessor_origin("v"),
            SynthSpec::new(ast()),
            Visibility::Private,
        )
        .unwrap();

    assert_eq!(table.name_candidates(&Symbol::from("v")), candidates_before);
    assert!(table.retired_slots().is_empty());
    let callable = table.get(name.as_ref()).unwrap().callable().unwrap();
    assert_eq!(callable.seq, 7);
    assert_eq!(callable.docstring.as_deref(), Some("new"));
    assert_eq!(
        table.get(name.as_ref()).unwrap().visibility,
        Visibility::Private
    );
    assert!(matches!(
        &callable.arm.life,
        Life::Template {
            body: TemplateBody::Synth(_),
            kind: TemplateKind::Parametric,
            callees,
        } if callees.is_empty()
    ));
    assert!(table.got.load_slot(old_slot.index()).is_null());
    table.validate_lifecycle().unwrap();
}

#[test]
fn unpublished_synthesized_concrete_replaces_broken_and_returns_its_slot() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("Box.v");
    let old_slot = install_packet_a_accessor(&mut table, name.as_ref(), None);
    let broken = table
        .mark_broken(
            &name,
            BrokenProvenance::new(
                FQSymbol {
                    module: ModuleFullPath::from("m"),
                    symbol: Symbol::from("cause"),
                },
                "failed".into(),
            ),
        )
        .unwrap();
    assert_eq!(broken.slot, old_slot);
    assert!(broken.displaced_owner.is_none());

    let returned = table
        .replace_unpublished_synthesized_concrete(
            name.clone(),
            concrete_scheme(),
            vec![Symbol::from("self")],
            Some("replacement".into()),
            packet_a_accessor_origin("v"),
            SynthSpec::new(ast()),
            packet_a_view(name.as_ref()),
            Visibility::Public,
        )
        .unwrap();

    assert_eq!(returned, old_slot);
    assert!(table.retired_slots().is_empty());
    assert!(matches!(
        &table.get(name.as_ref()).unwrap().callable().unwrap().arm.life,
        Life::Concrete {
            slot,
            realization: Realization::Body { code: None, view },
            minted_from: None,
            ast: Some(_),
            callees,
            value_use: false,
            mode_summary: None,
        } if *slot == old_slot && view.name == name && callees.is_empty()
    ));
    table.validate_lifecycle().unwrap();
}

#[test]
fn unpublished_synthesized_constructor_replacement_accepts_the_same_origin() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("Box");
    let type_name = FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Box"));
    let old_slot = table
        .install_concrete(
            name.clone(),
            concrete_scheme(),
            vec![Symbol::from("v")],
            None,
            0,
            CallableOrigin::Ctor {
                type_name: type_name.clone(),
                tag: 0,
                field_count: 1,
                internal: false,
                type_def: None,
            },
            Realization::Body {
                view: packet_a_view(name.as_ref()),
                code: None,
            },
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();

    let returned = table
        .replace_unpublished_synthesized_concrete(
            name.clone(),
            concrete_scheme(),
            vec![Symbol::from("v")],
            None,
            CallableOrigin::Ctor {
                type_name,
                tag: 0,
                field_count: 1,
                internal: false,
                type_def: None,
            },
            SynthSpec::new(ast()),
            packet_a_view(name.as_ref()),
            Visibility::Public,
        )
        .unwrap();

    assert_eq!(returned, old_slot);
    assert!(matches!(
        &table.get(name.as_ref()).unwrap().callable().unwrap().origin,
        CallableOrigin::Ctor { field_count: 1, .. }
    ));
    assert!(table.retired_slots().is_empty());
}

#[test]
fn unpublished_synthesized_replacement_refuses_wrong_origin_and_shape_atomically() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("Box.v");
    install_packet_a_accessor(&mut table, name.as_ref(), None);
    let before = serde_json::to_string(&table).unwrap();

    assert!(matches!(
        table.replace_unpublished_synthesized_template(
            name.clone(),
            concrete_scheme(),
            Vec::new(),
            None,
            packet_a_accessor_origin("v"),
            SynthSpec::new(ast()),
            Visibility::Public,
        ),
        Err(LifecycleError::ConcreteTemplate { .. })
    ));
    assert_eq!(serde_json::to_string(&table).unwrap(), before);

    assert!(matches!(
        table.replace_unpublished_synthesized_concrete(
            name.clone(),
            template_scheme(),
            Vec::new(),
            None,
            packet_a_accessor_origin("v"),
            SynthSpec::new(ast()),
            packet_a_view(name.as_ref()),
            Visibility::Public,
        ),
        Err(LifecycleError::SlotMint(SlotMintError::NotConcrete(_)))
    ));
    assert_eq!(serde_json::to_string(&table).unwrap(), before);

    assert!(matches!(
        table.replace_unpublished_synthesized_template(
            name.clone(),
            template_scheme(),
            Vec::new(),
            None,
            packet_a_accessor_origin("other"),
            SynthSpec::new(ast()),
            Visibility::Public,
        ),
        Err(LifecycleError::IllegalOriginState { .. })
    ));
    assert_eq!(serde_json::to_string(&table).unwrap(), before);

    assert!(matches!(
        table.replace_unpublished_synthesized_concrete(
            name.clone(),
            concrete_scheme(),
            Vec::new(),
            None,
            packet_a_accessor_origin("v"),
            SynthSpec::new(ast()),
            packet_a_view("wrong-name"),
            Visibility::Public,
        ),
        Err(LifecycleError::WrongState { .. })
    ));
    assert_eq!(serde_json::to_string(&table).unwrap(), before);
    assert!(table.retired_slots().is_empty());
}

#[test]
fn unpublished_synthesized_replacement_refuses_published_owner_without_mutation() {
    let mut table = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    let name = Symbol::from("Box.v");
    install_packet_a_accessor(&mut table, name.as_ref(), Some("compiled".into()));
    let before = serde_json::to_string(&table).unwrap();

    assert!(matches!(
        table.replace_unpublished_synthesized_template(
            name.clone(),
            template_scheme(),
            Vec::new(),
            None,
            packet_a_accessor_origin("v"),
            SynthSpec::new(ast()),
            Visibility::Public,
        ),
        Err(LifecycleError::WrongState { .. })
    ));

    assert_eq!(serde_json::to_string(&table).unwrap(), before);
    assert!(matches!(
        &table.get(name.as_ref()).unwrap().callable().unwrap().arm.life,
        Life::Concrete {
            realization: Realization::Body {
                code: Some(owner), ..
            },
            ..
        } if owner == "compiled"
    ));
    assert!(table.retired_slots().is_empty());
}

#[test]
fn unpublished_synthesized_replacement_refuses_non_null_got_without_mutation() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    let name = Symbol::from("Box.v");
    let slot = install_packet_a_accessor(&mut table, name.as_ref(), None);
    let published = std::ptr::dangling::<u8>();
    table.got.store_slot(slot.index(), published);
    let before = serde_json::to_string(&table).unwrap();

    assert!(matches!(
        table.replace_unpublished_synthesized_concrete(
            name.clone(),
            concrete_scheme(),
            Vec::new(),
            None,
            packet_a_accessor_origin("v"),
            SynthSpec::new(ast()),
            packet_a_view(name.as_ref()),
            Visibility::Public,
        ),
        Err(LifecycleError::WrongState { .. })
    ));

    assert_eq!(serde_json::to_string(&table).unwrap(), before);
    assert_eq!(table.got.load_slot(slot.index()), published);
    assert_eq!(
        table.get(name.as_ref()).unwrap().callable_got_slot(),
        Some(slot.index())
    );
    assert!(table.retired_slots().is_empty());
}

fn key_template(params: Vec<Type>, result: Type, variables: Vec<u32>) -> Scheme {
    Scheme {
        type_vars: variables,
        constraints: HashMap::new(),
        ty: Type::Fn(params, Box::new(result)),
    }
}

// spec: spec/03-types.md §3.6.3 — complete callable types distinguish realizations
#[test]
fn executable_keys_share_rendering_without_ordinals_or_substitution_collisions() {
    use crate::concrete_callable_key;
    let owner = FQSymbol {
        module: "user".into(),
        symbol: "f".into(),
    };
    let single = key_template(vec![Type::Var(8)], Type::Int, vec![99, 8]);
    let repeated = key_template(vec![Type::Var(2), Type::Var(2)], Type::Int, vec![2]);
    let target = CallableTarget::Binding(owner.clone());
    let demand = MonoDemand::from_type_args(target, vec![ConcreteType::Int], Span::SYNTHETIC);
    let single_key = demand.instance_key(&single).unwrap();
    assert_eq!(
        single_key.as_ref(),
        "(user/f [primitives/Int] primitives/Int)"
    );
    assert_eq!(
        demand.instance_key(&repeated).unwrap().as_ref(),
        "(user/f [primitives/Int primitives/Int] primitives/Int)"
    );
    assert_ne!(single_key, demand.instance_key(&repeated).unwrap());
    for ordinal in [0, 7] {
        let link = InstanceLink::from_type_args(
            CallableTarget::OverloadArm {
                owner: owner.clone(),
                arm: CallableArmId::from_ordinal(ordinal).unwrap(),
            },
            vec![ConcreteType::Int],
        );
        assert_eq!(link.instance_key(&single).unwrap(), single_key);
    }
    let concrete = ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int));
    assert_eq!(
        concrete_callable_key(&owner, &concrete).unwrap(),
        single_key
    );
    let renamed = key_template(vec![Type::Var(51)], Type::Int, vec![51]);
    assert_eq!(demand.instance_key(&renamed).unwrap(), single_key);
    let params = vec![ConcreteType::Int, ConcreteType::String];
    assert_ne!(
        concrete_callable_key(
            &owner,
            &ConcreteType::Fn(params.clone(), Box::new(ConcreteType::Bool))
        )
        .unwrap(),
        concrete_callable_key(
            &owner,
            &ConcreteType::Fn(
                params.into_iter().rev().collect(),
                Box::new(ConcreteType::Bool)
            )
        )
        .unwrap()
    );
}

// spec: spec/03-types.md §3.6.3 — result context participates recursively in identity
#[test]
fn executable_key_result_context_and_nominal_structure_are_lossless() {
    use crate::concrete_callable_key;
    let owner = FQSymbol {
        module: "user".into(),
        symbol: "maker".into(),
    };
    let signature = |ty| {
        ConcreteType::Fn(
            vec![],
            Box::new(ConcreteType::Fn(vec![ty], Box::new(ConcreteType::Bool))),
        )
    };
    let int = concrete_callable_key(&owner, &signature(ConcreteType::Int)).unwrap();
    let string = concrete_callable_key(&owner, &signature(ConcreteType::String)).unwrap();
    assert_ne!(int, string);
    assert_eq!(
        int.as_ref(),
        "(user/maker [] (Fn [primitives/Int] primitives/Bool))"
    );
    let vec_name = FQTypeName::new("collections".into(), "Vec".into());
    let nominal = ConcreteType::ADT(vec_name.clone(), vec![ConcreteType::Float]);
    let key = concrete_callable_key(&owner, &signature(nominal)).unwrap();
    assert_eq!(
        key.as_ref(),
        "(user/maker [] (Fn [(collections/Vec primitives/Float)] primitives/Bool))"
    );
    let other = ConcreteType::ADT(
        FQTypeName::new("other".into(), "Vec".into()),
        vec![ConcreteType::Float],
    );
    assert_ne!(
        key,
        concrete_callable_key(&owner, &signature(other)).unwrap()
    );
    let higher = key_template(
        vec![Type::TyConApp(9, vec![Type::Var(3)])],
        Type::Bool,
        vec![3, 9],
    );
    let link = InstanceLink::from_type_args(
        CallableTarget::Binding(owner),
        vec![ConcreteType::ADT(vec_name, vec![]), ConcreteType::Float],
    );
    assert_eq!(
        link.instance_key(&higher).unwrap().as_ref(),
        "(user/maker [(collections/Vec primitives/Float)] primitives/Bool)"
    );
}

#[test]
fn executable_key_errors_refuse_incomplete_or_unsupported_inputs() {
    use crate::{InstanceKeyError as E, NotConcrete, concrete_callable_key};
    let owner = FQSymbol {
        module: "user".into(),
        symbol: "f".into(),
    };
    let link = InstanceLink::from_type_args(CallableTarget::Binding(owner.clone()), vec![]);
    assert_eq!(
        link.instance_key(&key_template(vec![Type::Var(0)], Type::Int, vec![0])),
        Err(E::ArgumentCount {
            expected: 1,
            actual: 0
        })
    );
    assert_eq!(
        link.instance_key(&key_template(vec![Type::Var(0)], Type::Int, vec![])),
        Err(E::NotConcrete(NotConcrete::Var(0)))
    );
    assert_eq!(
        link.instance_key(&key_template(
            vec![Type::TyConApp(0, vec![])],
            Type::Int,
            vec![]
        )),
        Err(E::NotConcrete(NotConcrete::HktHead(0)))
    );
    assert_eq!(link.instance_key(&scheme(Type::Int)), Err(E::NotFunction));
    assert_eq!(
        concrete_callable_key(&owner, &ConcreteType::Int),
        Err(E::NotFunction)
    );
    let macro_link = InstanceLink::from_type_args(
        CallableTarget::MacroClause {
            owner,
            clause: CallableArmId::from_ordinal(0).unwrap(),
        },
        vec![],
    );
    assert_eq!(
        macro_link.instance_key(&scheme(Type::Int)),
        Err(E::UnsupportedTemplate)
    );
}

// spec: repl/spec/18-redefinition.md §18.3 — signature removal/addition replaces the whole family
#[test]
fn cross_class_plain_overload_publication_conserves_slots_and_owners() {
    let overloaded = || {
        let mut table = SymbolTable::<String, ()>::new_with_params("m".into());
        table
            .install_overloaded(
                "f".into(),
                None,
                0,
                vec![
                    concrete_arm_draft(Type::Int, "int-arm"),
                    concrete_arm_draft(Type::Bool, "bool-arm"),
                ],
                Visibility::Public,
            )
            .unwrap();
        table
    };
    for overload_to_plain in [true, false] {
        let (mut live, staging, old_targets) = if overload_to_plain {
            (
                overloaded(),
                owner_table("m", None),
                vec![overload_target("m", "f", 0), overload_target("m", "f", 1)],
            )
        } else {
            (
                owner_table("m", None),
                overloaded(),
                vec![binding_target("m", "f")],
            )
        };
        let old_slots: Vec<_> = old_targets
            .iter()
            .enumerate()
            .map(|(i, target)| {
                publish_string_owner(&mut live, target, &format!("old-{i}"));
                live.callable_target(target)
                    .unwrap()
                    .life
                    .claimed_slot()
                    .unwrap()
            })
            .collect();
        let before = serde_json::to_value(&live).unwrap();
        let preservation = live.publish_staged(
            staging.clone(),
            &[StagedPublicationDecision::PreserveAbi { symbol: "f".into() }],
        );
        assert!(preservation.is_err());
        assert_eq!(serde_json::to_value(&live).unwrap(), before);
        let records = live
            .publish_staged(
                staging,
                &[StagedPublicationDecision::ChangeAbi { symbol: "f".into() }],
            )
            .unwrap();
        assert!(matches!(
            preservation,
            Err(LifecycleError::WrongState { .. })
        ));
        let bodies = &records[0].bodies;
        assert_eq!(
            bodies
                .iter()
                .filter_map(|body| body.displaced_owner.clone())
                .collect::<Vec<_>>(),
            (0..old_targets.len())
                .map(|i| format!("old-{i}"))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            bodies
                .iter()
                .filter_map(|body| body.prior_target.clone())
                .collect::<Vec<_>>(),
            old_targets
        );
        let new_slots: Vec<_> = bodies
            .iter()
            .filter_map(|body| body.published_slot)
            .collect();
        assert_eq!(new_slots.len(), if overload_to_plain { 1 } else { 2 });
        assert!(new_slots.iter().all(|slot| !old_slots.contains(slot)));
        assert_eq!(live.retired_slots().len(), old_slots.len());
        for old_slot in old_slots {
            assert!(
                live.retired_slots()
                    .iter()
                    .any(|retired| retired.slot == old_slot
                        && matches!(retired.reason, RetireReason::AbiChanging { .. }))
            );
        }
        assert!(
            matches!(live.get("f").unwrap().declaration, Decl::Callable(_)) == overload_to_plain
        );
        live.validate_lifecycle().unwrap();
    }
}

#[test]
fn cross_class_publication_does_not_admit_non_plain_origins() {
    for overload_to_primitive in [true, false] {
        let mut overloaded = SymbolTable::<String, ()>::new_with_params("m".into());
        overloaded
            .install_overloaded(
                "f".into(),
                None,
                0,
                vec![
                    concrete_arm_draft(Type::Int, "int-arm"),
                    concrete_arm_draft(Type::Bool, "bool-arm"),
                ],
                Visibility::Public,
            )
            .unwrap();
        let mut primitive = owner_table("m", None);
        primitive
            .symbols
            .get_mut(&Symbol::from("f"))
            .unwrap()
            .binding
            .as_mut()
            .unwrap()
            .callable_mut()
            .unwrap()
            .origin = CallableOrigin::RustPrimitive;
        let (live, staging) = if overload_to_primitive {
            (overloaded, primitive)
        } else {
            (primitive, overloaded)
        };
        let before = serde_json::to_value(&live).unwrap();
        assert!(matches!(
            validate_publication_collision(
                &live,
                &Symbol::from("f"),
                live.get("f"),
                staging.get("f").unwrap()
            ),
            Err(LifecycleError::NotCallable { .. })
        ));
        assert_eq!(serde_json::to_value(&live).unwrap(), before);
    }
}

// --- Qualified lookup dependencies (tests/plan/s122-evidence-delta.md LD-T) ---

fn lookup_set<C: CodeStore, L: LinkerStore>(table: &SymbolTable<C, L>) -> Vec<&str> {
    table
        .lookup_dependencies()
        .map(|module| module.as_ref())
        .collect()
}

// spec: design/arch/interfaces.md §Qualified lookup dependencies — T1 recorder
#[test]
fn lookup_recorder_ignores_own_path_and_collapses_duplicates() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table.record_lookup_dependency(ModuleFullPath::from("r"));
    table.record_lookup_dependency(ModuleFullPath::from("m"));
    table.record_lookup_dependency(ModuleFullPath::from("r"));
    table.record_lookup_dependency(ModuleFullPath::from("m.child"));

    assert_eq!(lookup_set(&table), vec!["m.child", "r"]);
}

// spec: design/arch/interfaces.md §Qualified lookup dependencies — T2 publish union
#[test]
fn both_publish_funnels_union_staged_lookup_dependencies_into_live() {
    let live_with = |members: &[&str]| {
        let mut live = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
        for member in members {
            live.record_lookup_dependency(ModuleFullPath::from(*member));
        }
        live
    };
    let staging = || {
        let mut staging = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
        staging.record_lookup_dependency(ModuleFullPath::from("new"));
        staging.record_lookup_dependency(ModuleFullPath::from("both"));
        staging
    };

    let mut plain = live_with(&["kept", "both"]);
    plain.publish_staged(staging(), &[]).unwrap();
    assert_eq!(lookup_set(&plain), vec!["both", "kept", "new"]);

    let mut compiled = live_with(&["kept", "both"]);
    if let Err(rejection) = compiled.publish_compiled_staged(staging(), &[], HashMap::new()) {
        panic!("empty compiled publication refused: {}", rejection.reason());
    }
    assert_eq!(lookup_set(&compiled), vec!["both", "kept", "new"]);
}

// spec: design/arch/interfaces.md §Qualified lookup dependencies — T3 conversions
#[test]
fn lookup_dependencies_survive_clone_and_concrete_conversion_and_start_empty() {
    let fresh = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    assert!(lookup_set(&fresh).is_empty());
    assert!(lookup_set(&SymbolTable::new(ModuleFullPath::from("m"))).is_empty());

    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table.record_lookup_dependency(ModuleFullPath::from("r"));
    assert_eq!(lookup_set(&table.clone()), vec!["r"]);
    let concrete: SymbolTable<String, ()> = table.into_concrete();
    assert_eq!(lookup_set(&concrete), vec!["r"]);
}

fn box_type() -> Type {
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Box")),
        Vec::new(),
    )
}

fn box_ctor_origin() -> CallableOrigin {
    CallableOrigin::Ctor {
        type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Box")),
        tag: 0,
        field_count: 1,
        internal: false,
        type_def: None,
    }
}

/// A concrete one-field product `Box` whose field `v` has type `field`,
/// restricted to the synthesized members named in `members`.
fn concrete_box_members(field: Type, members: &[&str]) -> SymbolTable<String, ()> {
    let mut table = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    for &member in members {
        let (ty, origin) = match member {
            "Box" => (
                Type::Fn(vec![field.clone()], Box::new(box_type())),
                box_ctor_origin(),
            ),
            "Box.v" => (
                Type::Fn(vec![box_type()], Box::new(field.clone())),
                packet_a_accessor_origin("v"),
            ),
            other => panic!("no synthesized Box member {other}"),
        };
        table
            .install_concrete(
                Symbol::from(member),
                scheme(ty),
                vec![Symbol::from("v")],
                None,
                0,
                origin,
                Realization::Body {
                    view: packet_a_view(member),
                    code: None,
                },
                Some(ast()),
                Vec::new(),
                Visibility::Public,
            )
            .unwrap();
    }
    table
}

/// A generic `Box` constructor quantified over `var`, whose field has type
/// `field`.
fn generic_box_ctor(var: TypeId, field: Type) -> SymbolTable<String, ()> {
    let mut table = SymbolTable::<String, ()>::new_with_params(ModuleFullPath::from("m"));
    let result = Type::ADT(
        FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Box")),
        vec![Type::Var(var)],
    );
    table
        .install_template(
            Symbol::from("Box"),
            Scheme {
                type_vars: vec![var],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![field], Box::new(result)),
            },
            vec![Symbol::from("v")],
            None,
            0,
            box_ctor_origin(),
            TemplateBody::Synth(SynthSpec::new(ast())),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    table
}

// spec: repl/spec/18-redefinition.md §18.5 — an existing value is never
// reinterpreted under a changed layout; the types publication funnel refuses to
// republish a synthesized constructor or accessor under a different scheme.
#[test]
fn staged_publication_refuses_synthesized_member_with_changed_scheme_atomically() {
    for member in ["Box", "Box.v"] {
        let mut live = concrete_box_members(Type::Int, &["Box", "Box.v"]);
        let before = serde_json::to_string(&live).unwrap();
        let refused = live
            .publish_staged(
                concrete_box_members(Type::String, &[member]),
                &[StagedPublicationDecision::ChangeAbi {
                    symbol: Symbol::from(member),
                }],
            )
            .err();
        assert!(
            matches!(
                &refused,
                Some(LifecycleError::WrongState { symbol, .. }) if symbol.as_ref() == member
            ),
            "{member} field-type change must be refused, got {refused:?}"
        );
        assert_eq!(serde_json::to_string(&live).unwrap(), before, "{member}");
    }

    let mut live = generic_box_ctor(0, Type::Var(0));
    let before = serde_json::to_string(&live).unwrap();
    let refused = live
        .publish_staged(generic_box_ctor(0, Type::Int), &[])
        .err();
    assert!(
        matches!(
            &refused,
            Some(LifecycleError::WrongState { symbol, .. }) if symbol.as_ref() == "Box"
        ),
        "generic field-type change must be refused, got {refused:?}"
    );
    assert_eq!(serde_json::to_string(&live).unwrap(), before);
}

// spec: repl/spec/18-redefinition.md §18.5 — a structurally identical
// redeclaration republishes its synthesized members.
#[test]
fn staged_publication_admits_synthesized_members_with_alpha_equivalent_schemes() {
    let mut live = concrete_box_members(Type::Int, &["Box", "Box.v"]);
    let slot = live.get("Box").unwrap().callable_got_slot();
    let _ = live
        .publish_staged(
            concrete_box_members(Type::Int, &["Box", "Box.v"]),
            &[
                StagedPublicationDecision::PreserveAbi {
                    symbol: Symbol::from("Box"),
                },
                StagedPublicationDecision::PreserveAbi {
                    symbol: Symbol::from("Box.v"),
                },
            ],
        )
        .expect("an identical scheme republishes");
    assert_eq!(live.get("Box").unwrap().callable_got_slot(), slot);

    let mut live = generic_box_ctor(0, Type::Var(0));
    let _ = live
        .publish_staged(generic_box_ctor(7, Type::Var(7)), &[])
        .expect("an alpha-renamed scheme republishes");
    assert_eq!(
        live.get("Box")
            .unwrap()
            .callable()
            .unwrap()
            .arm
            .scheme
            .type_vars,
        vec![7]
    );
}

// spec: design/arch/interfaces.md §Qualified lookup dependencies — T4 schema fence
#[test]
fn lookup_dependencies_round_trip_and_absence_fails_to_decode() {
    let mut table = SymbolTable::new(ModuleFullPath::from("m"));
    table.record_lookup_dependency(ModuleFullPath::from("r"));
    table.record_lookup_dependency(ModuleFullPath::from("q"));

    let serialized = serde_json::to_value(&table).unwrap();
    let restored: SymbolTable = serde_json::from_value(serialized.clone()).unwrap();
    assert_eq!(lookup_set(&restored), vec!["q", "r"]);

    let mut without = serialized;
    without
        .as_object_mut()
        .unwrap()
        .remove("lookup_dependencies")
        .expect("lookup dependencies serialize under their field name");
    assert!(
        serde_json::from_value::<SymbolTable>(without).is_err(),
        "a sidecar without lookup dependencies must not decode as an empty set"
    );
}
