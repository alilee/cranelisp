use std::collections::HashMap;

use cranelisp_types::{
    Binding, BrokenProvenance, CallableArmDraft, CallableOrigin, CallableTarget, ConcreteType,
    ConstrainedMeta, Decl, DefnVariant, Expr, FQSymbol, FQTypeName, InstanceLink, Life,
    MacroClauseDraft, ModeSummary, MonoDefnVariant, MonoExpr, Realization, Scheme, Sexp, Span,
    SpecialFormRecord, StagedPublicationDecision, Symbol, SymbolTable, SymbolTables, SynthSpec,
    TemplateBody, TemplateKind, TraitDeclInfo, TraitMethodRecord, TraitName, TraitRecord, Type,
    TypeName, Visibility, WrittenTraitImpl, member_key,
};

fn scheme(ty: Type) -> Scheme {
    Scheme {
        type_vars: Vec::new(),
        constraints: HashMap::new(),
        ty,
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

fn realization() -> Realization<()> {
    Realization::Body {
        view: MonoDefnVariant {
            name: Symbol::from("body"),
            params: Vec::new(),
            body: MonoExpr::IntLit {
                value: 1,
                span: Span::SYNTHETIC,
                ty: ConcreteType::Int,
            },
            span: Span::SYNTHETIC,
            mode_summary: None,
        },
        code: None,
    }
}

fn view_for(name: &str) -> MonoDefnVariant {
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

fn binding_target(module: &str, name: &str) -> CallableTarget {
    CallableTarget::Binding(FQSymbol {
        module: module.into(),
        symbol: Symbol::from(name),
    })
}

#[test]
fn external_consumer_can_author_lifecycle_records_and_instance_funnel() {
    let concrete = scheme(Type::Int);
    let trait_record = TraitRecord::new(
        TraitDeclInfo {
            name: TraitName::from("Display"),
            type_params: Vec::new(),
            methods: Vec::new(),
        },
        Some("trait".into()),
    );
    let trait_name =
        cranelisp_types::FQTraitName::new("consumer".into(), TraitName::from("Display"));
    let trait_method = TraitMethodRecord::new(
        concrete.clone(),
        vec![Symbol::from("self")],
        Some("method".into()),
        trait_name.clone(),
    );
    let special_form = SpecialFormRecord::new(
        concrete.clone(),
        Vec::new(),
        Some("special".into()),
        "usage".into(),
    );
    let synth = SynthSpec::new(ast());
    let constrained = ConstrainedMeta::new(HashMap::new());
    let broken = BrokenProvenance::new(
        FQSymbol {
            module: "consumer".into(),
            symbol: Symbol::from("ordinary"),
        },
        "compile failed".into(),
    );

    let mut table = SymbolTable::new("consumer".into());
    for (name, decl) in [
        ("trait", Decl::Trait(trait_record)),
        ("special", Decl::SpecialForm(special_form)),
    ] {
        table
            .install_binding(Symbol::from(name), Binding::new(decl, Visibility::Public))
            .unwrap();
    }
    table
        .install_overloaded(
            Symbol::from("overload"),
            Some("overload".into()),
            0,
            vec![CallableArmDraft::concrete_body(
                concrete.clone(),
                Vec::new(),
                ast(),
                view_for("overload$0"),
                Vec::new(),
            )],
            Visibility::Public,
        )
        .unwrap();
    table
        .install_macro(
            Symbol::from("macro"),
            Some("macro".into()),
            1,
            Sexp::Symbol("macro-source".into(), Span::SYNTHETIC),
            vec![MacroClauseDraft::new(
                Vec::new(),
                None,
                CallableArmDraft::concrete_body(
                    concrete.clone(),
                    Vec::new(),
                    ast(),
                    view_for("macro$0"),
                    Vec::new(),
                ),
            )],
            Visibility::Public,
        )
        .unwrap();
    table
        .install_trait_method(Symbol::from("display"), trait_method, Visibility::Public)
        .unwrap();
    assert_eq!(
        table
            .get("Display.display")
            .unwrap()
            .trait_method()
            .unwrap()
            .trait_name,
        trait_name
    );
    let projected = table.name_candidates(&Symbol::from("display"));
    assert_eq!(projected.len(), 1);
    assert_eq!(projected[0].source.symbol, member_key("Display", "display"));

    let checked = Symbol::from("checked");
    table
        .declare(
            checked.clone(),
            Scheme {
                type_vars: vec![0],
                constraints: HashMap::new(),
                ty: Type::Var(0),
            },
            Vec::new(),
            None,
            2,
            CallableOrigin::Plain,
            Visibility::Private,
        )
        .unwrap();
    table
        .settle_checked_template(
            &checked,
            Scheme {
                type_vars: vec![0],
                constraints: HashMap::new(),
                ty: Type::Var(0),
            },
            ast(),
            TemplateKind::Parametric,
            Vec::new(),
        )
        .unwrap();
    table
        .replace_callees(
            &checked,
            vec![FQSymbol {
                module: "dependency".into(),
                symbol: Symbol::from("callee"),
            }],
        )
        .unwrap();
    table
        .settle_checked_concrete(
            &checked,
            concrete.clone(),
            ast(),
            view_for("checked"),
            Vec::new(),
        )
        .unwrap();
    table
        .publish_body_ownership(
            &binding_target("consumer", "checked"),
            ModeSummary::default(),
            view_for("checked"),
        )
        .unwrap();
    assert!(table.get("checked").unwrap().mode_summary().is_some());

    table
        .install_template(
            Symbol::from("Box.make"),
            scheme(Type::Var(0)),
            Vec::new(),
            None,
            3,
            CallableOrigin::Ctor {
                type_name: FQTypeName::new("consumer".into(), TypeName::from("Box")),
                tag: 0,
                field_count: 0,
                internal: false,
                type_def: None,
            },
            TemplateBody::Synth(synth),
            TemplateKind::Constrained(Box::new(constrained)),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();

    let slot = table
        .install_concrete(
            Symbol::from("ordinary"),
            concrete.clone(),
            Vec::new(),
            None,
            4,
            CallableOrigin::Plain,
            realization(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    let broken_transition = table
        .mark_broken(&Symbol::from("ordinary"), broken.clone())
        .unwrap();
    assert_eq!(broken_transition.slot, slot);
    assert!(broken_transition.displaced_owner.is_none());
    assert!(matches!(
        &table.get("ordinary").unwrap().callable().unwrap().arm.life,
        Life::Broken { error, .. } if error == &broken
    ));

    let link = InstanceLink::from_type_args(
        CallableTarget::Binding(FQSymbol {
            module: "producer".into(),
            symbol: Symbol::from("generic"),
        }),
        vec![ConcreteType::Int],
    );
    let instance_scheme = scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    let expected = cranelisp_types::concrete_callable_key(
        &FQSymbol {
            module: "producer".into(),
            symbol: "generic".into(),
        },
        &ConcreteType::from_type(&instance_scheme.ty).unwrap(),
    )
    .unwrap();
    let (key, slot) = table
        .install_instance(
            link.clone(),
            instance_scheme,
            Vec::new(),
            None,
            5,
            CallableOrigin::Plain,
            realization(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    assert_eq!(key, expected);
    assert_eq!(
        table.get(key.as_ref()).unwrap().callable_got_slot(),
        Some(slot.index())
    );
    assert!(matches!(
        &table.get(key.as_ref()).unwrap().callable().unwrap().arm.life,
        Life::Concrete {
            minted_from: Some(stored),
            ..
        } if stored == &link
    ));

    let retained = table
        .retain_callables(&[Symbol::from("transactional")])
        .unwrap();
    table
        .install_concrete(
            Symbol::from("transactional"),
            scheme(Type::Int),
            Vec::new(),
            None,
            6,
            CallableOrigin::Plain,
            realization(),
            Some(ast()),
            Vec::new(),
            Visibility::Private,
        )
        .unwrap();
    table.rollback_callables(retained).unwrap();
    assert!(table.get("transactional").is_none());

    let written = WrittenTraitImpl::new(
        cranelisp_types::FQTraitName::new("traits".into(), TraitName::from("Display")),
        FQTypeName::new("consumer".into(), TypeName::from("Thing")),
        "consumer".into(),
        vec![Symbol::from("display")],
        Visibility::Public,
    );
    let mut trait_home = SymbolTable::new("traits".into());
    let staged = trait_home.stage_trait_impl_shell(&written).unwrap();
    staged.commit();
    table.upsert_written_trait_impl(written).unwrap();
    assert_eq!(table.written_trait_impls.len(), 1);

    let mut importer = SymbolTable::new("importer".into());
    importer
        .expose_candidate(
            Symbol::from("show"),
            FQSymbol {
                module: "consumer".into(),
                symbol: member_key("Display", "display"),
            },
            Visibility::Public,
        )
        .unwrap();
    assert_eq!(importer.public_name_candidates().count(), 1);
    assert_eq!(importer.name_candidates(&Symbol::from("show")).len(), 1);
    let tables: SymbolTables<(), ()> = SymbolTables::new();
    tables.insert("consumer".into(), table);
    importer.validate_name_candidates(&tables).unwrap();
}

#[test]
fn external_consumer_can_publish_and_retain_owner_transitions() {
    let mut live = SymbolTable::new("consumer".into());
    let first_slot = live
        .install_concrete(
            Symbol::from("f"),
            scheme(Type::Int),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            realization(),
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    let mut staging = SymbolTable::new("consumer".into());
    staging
        .install_concrete(
            Symbol::from("f"),
            scheme(Type::Int),
            Vec::new(),
            None,
            0,
            CallableOrigin::Plain,
            realization(),
            Some(ast()),
            Vec::new(),
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
    assert_eq!(records[0].symbol, Symbol::from("f"));
    assert_eq!(records[0].bodies[0].prior_slot, Some(first_slot));
    assert_eq!(records[0].bodies[0].published_slot, Some(first_slot));
    assert!(records[0].bodies[0].displaced_owner.is_none());

    match live.publish_compiled_owner(
        &CallableTarget::Binding(FQSymbol {
            module: "consumer".into(),
            symbol: Symbol::from("f"),
        }),
        (),
    ) {
        Ok(None) => {}
        Ok(Some(())) | Err(_) => panic!("fresh owner publication must displace nothing"),
    }
    let transition = live
        .mark_broken(
            &Symbol::from("f"),
            BrokenProvenance::new(
                FQSymbol {
                    module: "consumer".into(),
                    symbol: Symbol::from("cause"),
                },
                "failed".into(),
            ),
        )
        .unwrap();
    assert_eq!(transition.slot, first_slot);
    assert_eq!(transition.displaced_owner, Some(()));
}

#[test]
fn external_consumer_can_replace_unpublished_synthesized_callables() {
    let mut table = SymbolTable::new("consumer".into());
    let type_name = FQTypeName::new("consumer".into(), TypeName::from("Box"));
    let origin = || CallableOrigin::Accessor {
        type_name: type_name.clone(),
        field: Symbol::from("v"),
    };
    let concrete_name = Symbol::from("Box.v");
    let template_name = Symbol::from("Box.w");

    let provisional = table
        .install_concrete(
            concrete_name.clone(),
            scheme(Type::Int),
            Vec::new(),
            None,
            0,
            origin(),
            Realization::Body {
                view: view_for(concrete_name.as_ref()),
                code: None,
            },
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    let returned = table
        .replace_unpublished_synthesized_concrete(
            concrete_name.clone(),
            scheme(Type::Int),
            Vec::new(),
            None,
            origin(),
            SynthSpec::new(ast()),
            view_for(concrete_name.as_ref()),
            Visibility::Public,
        )
        .unwrap();
    assert_eq!(returned, provisional);

    table
        .install_concrete(
            template_name.clone(),
            scheme(Type::Int),
            Vec::new(),
            None,
            1,
            CallableOrigin::Accessor {
                type_name: type_name.clone(),
                field: Symbol::from("w"),
            },
            Realization::Body {
                view: view_for(template_name.as_ref()),
                code: None,
            },
            Some(ast()),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    table
        .replace_unpublished_synthesized_template(
            template_name.clone(),
            Scheme {
                type_vars: vec![0],
                constraints: HashMap::new(),
                ty: Type::Var(0),
            },
            Vec::new(),
            None,
            CallableOrigin::Accessor {
                type_name,
                field: Symbol::from("w"),
            },
            SynthSpec::new(ast()),
            Visibility::Public,
        )
        .unwrap();
    assert!(matches!(
        &table
            .get(template_name.as_ref())
            .unwrap()
            .callable()
            .unwrap()
            .arm
            .life,
        Life::Template {
            body: TemplateBody::Synth(_),
            kind: TemplateKind::Parametric,
            ..
        }
    ));
}
