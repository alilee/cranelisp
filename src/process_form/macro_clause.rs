//! Source-ordered macro checkpoint preparation and publication.

use cranelisp_types::{
    CallableArmDraft, CallableOrigin, CranelispError, Decl, ErrorLocation, FQTypeName, Life,
    MacroClauseDraft, ModuleFullPath, Realization, Scheme, Span, Symbol, Type, TypeName,
    Visibility,
};

use crate::worker::build_program_compat;

pub(super) struct MacroClauseEnv<'a> {
    pub symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    pub module_aliases: &'a cranelisp_types::ModuleAliases,
    pub prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
    pub shared_state: Option<&'a crate::session_v4::SharedState>,
}

pub(super) enum MacroCheckpoint {
    Published,
    Gap(cranelisp_types::ResolutionGap),
}

/// Compile and immediately publish one complete parent-plus-clause generation.
///
/// The publication records the attempt's macro-head modules and the clause
/// bodies' own lookup dependencies (`design/int/int.md` §7.6.2).
pub(super) fn compile_macro_checkpoint(
    env: &MacroClauseEnv<'_>,
    module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    macro_sexp: &cranelisp_types::Sexp,
    macro_lookup_dependencies: &std::collections::BTreeSet<ModuleFullPath>,
) -> Result<MacroCheckpoint, CranelispError> {
    let span = macro_sexp.span();
    let shared = env.shared_state.ok_or_else(|| CranelispError::MacroError {
        message: format!(
            "macro checkpoint for '{}/{}' has no live publication owner",
            module, info.name
        ),
        location: ErrorLocation::from_span(span),
    })?;
    let expanded = info
        .clauses
        .iter()
        .enumerate()
        .map(|(index, clause)| {
            let synthesized = cranelisp_frontend::synthesize_macro_clause_defn(
                info.name.as_ref(),
                index,
                clause,
                span,
            );
            cranelisp_frontend::expand_quasiquotes(&synthesized)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let program = build_program_compat(&expanded)?;
    // Generated clause keys are a typecheck-local ledger only. They make the
    // ordinary body checker reusable, then disappear before any publication,
    // cache write, search pass, or backend call.
    let mut clause_staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    let seq = env
        .symbol_tables
        .get(module)
        .map_or(0, |table| table.next_seq);
    let visibility = if info.is_private {
        Visibility::Private
    } else {
        Visibility::Public
    };
    let abi = macro_clause_scheme();
    let clause_names: Vec<_> = (0..info.clauses.len())
        .map(|index| macro_clause_key(&info.name, index))
        .collect();
    for name in &clause_names {
        clause_staging
            .declare(
                name.clone(),
                abi.clone(),
                vec![Symbol::from("__args__")],
                None,
                seq,
                CallableOrigin::Plain,
                Visibility::Private,
            )
            .map_err(|error| lifecycle_error(name, span, error))?;
    }

    let mut access = cranelisp_typecheck::SymbolTableAccess::cluster(
        env.symbol_tables,
        &mut clause_staging,
        module.clone(),
    );
    let checked = cranelisp_typecheck::check_forms(
        crate::worker::top_level_to_parsed_entries(&program),
        &mut access,
        env.symbol_tables,
        env.module_aliases,
        env.prelude_fallback,
    );
    drop(access);
    let checked = match checked {
        Ok(result) => result,
        Err(cranelisp_typecheck::CheckError::Gap(gap)) => return Ok(MacroCheckpoint::Gap(gap)),
        Err(error) => return Err(crate::worker::check_error_to_cranelisp_error(error)),
    };
    let clause_drafts = checked_clause_drafts(&clause_staging, info, &clause_names, &abi, span)?;
    let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
    retain_checked_instances(&clause_staging, &mut staging, span)?;
    staging
        .install_macro(
            info.name.clone(),
            info.docstring.clone(),
            seq,
            macro_sexp.clone(),
            clause_drafts,
            visibility,
        )
        .map_err(|error| lifecycle_error(&info.name, span, error))?;
    staging.next_seq = seq.saturating_add(1);
    let mut prepared = crate::worker::plan_staging_commit(
        env.symbol_tables,
        module,
        staging,
        &program,
        shared,
        &[],
    )?;
    prepared.unresolved_dispatch = checked.unresolved_dispatch;
    // The clause bodies were checked in the scratch table, which is not
    // published, so their lookup dependencies move to the macro's table here.
    prepared.record_lookup_dependencies(
        clause_staging
            .lookup_dependencies()
            .chain(macro_lookup_dependencies),
    );
    let mut processed =
        crate::cluster::ProcessedCluster::from_parts(Vec::new(), Vec::new(), Vec::new());
    processed.set_prepared(prepared);
    crate::worker::compile_and_publish_processed_without_notify(&mut processed, shared)?;
    if let Some((published_module, names)) = processed.pending_codegen_notification.take() {
        for name in names {
            shared
                .scheduler
                .notify_inmem_codegen_complete(&published_module, &name, false);
        }
    }
    Ok(MacroCheckpoint::Published)
}

/// Preserve concrete instances synthesized while checking the private clause
/// bodies. The generated clause bindings themselves are deliberately replaced
/// by the owned macro family, but their monomorphised constructor/helper
/// dependencies remain ordinary executable bindings needed by those bodies.
fn retain_checked_instances(
    checked: &crate::code::SessionSymbolTable,
    target: &mut crate::code::SessionSymbolTable,
    span: Span,
) -> Result<(), CranelispError> {
    for (name, binding) in checked.all_symbols() {
        let Decl::Callable(callable) = &binding.declaration else {
            continue;
        };
        let Life::Concrete {
            realization: Realization::Body { view, code: None },
            minted_from: Some(link),
            ast,
            callees,
            value_use,
            mode_summary,
            ..
        } = &callable.arm.life
        else {
            continue;
        };
        let (installed, _) = target
            .install_instance(
                link.clone(),
                callable.arm.scheme.clone(),
                callable.arm.param_names.clone(),
                callable.docstring.clone(),
                callable.seq,
                callable.origin.clone(),
                Realization::Body {
                    view: view.clone(),
                    code: None,
                },
                ast.clone(),
                callees.clone(),
                binding.visibility,
            )
            .map_err(|error| lifecycle_error(name, span, error))?;
        let installed_target =
            cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
                module: target.path.clone(),
                symbol: installed.clone(),
            });
        if let Some(summary) = mode_summary {
            target
                .publish_body_ownership(&installed_target, summary.clone(), view.clone())
                .map_err(|error| lifecycle_error(&installed, span, error))?;
        }
        if *value_use {
            target
                .set_value_use(&installed, true)
                .map_err(|error| lifecycle_error(&installed, span, error))?;
        }
    }
    Ok(())
}

pub(super) fn macro_clause_key(parent: &Symbol, index: usize) -> Symbol {
    Symbol::from(format!("__macro_{}_clause_{}", parent, index))
}

pub(super) fn macro_clause_scheme() -> Scheme {
    let macros = ModuleFullPath::from("macros");
    let sexp = Type::ADT(
        FQTypeName::new(macros.clone(), TypeName::from("Sexp")),
        Vec::new(),
    );
    let args = Type::ADT(
        FQTypeName::new(macros, TypeName::from("SList")),
        vec![sexp.clone()],
    );
    Scheme {
        type_vars: Vec::new(),
        constraints: std::collections::HashMap::new(),
        ty: Type::Fn(vec![args], Box::new(sexp)),
    }
}

fn checked_clause_drafts(
    staging: &crate::code::SessionSymbolTable,
    info: &cranelisp_frontend::DefmacroInfo,
    names: &[Symbol],
    abi: &Scheme,
    span: Span,
) -> Result<Vec<MacroClauseDraft>, CranelispError> {
    let mut drafts = Vec::with_capacity(names.len());
    for (name, parsed) in names.iter().zip(&info.clauses) {
        let binding = staging
            .get(name.as_ref())
            .ok_or_else(|| invalid_clause(name, span, "missing after typecheck"))?;
        if binding.visibility != Visibility::Private {
            return Err(invalid_clause(name, span, "clause is not private"));
        }
        let callable = binding
            .callable()
            .ok_or_else(|| invalid_clause(name, span, "clause is not callable"))?;
        if !same_macro_abi(&callable.arm.scheme, abi) {
            return Err(invalid_clause(name, span, "clause ABI is not canonical"));
        }
        let Life::Concrete {
            realization: Realization::Body { view, code: None },
            ast: Some(ast),
            callees,
            ..
        } = &callable.arm.life
        else {
            return Err(invalid_clause(
                name,
                span,
                "clause is not an uncompiled concrete body",
            ));
        };
        let view = pin_macro_clause_ownership(view.clone());
        drafts.push(MacroClauseDraft::new(
            parsed.fixed_params.clone(),
            parsed.rest_param.clone(),
            CallableArmDraft::concrete_body(
                callable.arm.scheme.clone(),
                callable.arm.param_names.clone(),
                ast.clone(),
                view,
                callees.clone(),
            ),
        ));
    }
    Ok(drafts)
}

/// Pin a synthesized macro clause to its declared consuming ABI.
fn pin_macro_clause_ownership(
    mut view: cranelisp_types::MonoDefnVariant,
) -> cranelisp_types::MonoDefnVariant {
    // Macro clauses cross the fixed consuming `SexpListToSexpI64V1`
    // boundary. Clearing the generated body's inferred summary pins the
    // backend to its all-Owned convention for every clause shape.
    view.mode_summary = None;
    view
}

pub(super) fn same_macro_abi(actual: &Scheme, expected: &Scheme) -> bool {
    let (Type::Fn(actual_params, actual_ret), Type::Fn(expected_params, _)) =
        (&actual.ty, &expected.ty)
    else {
        return false;
    };
    actual.type_vars.is_empty()
        && actual.constraints.is_empty()
        && actual_params == expected_params
        && actual_ret.is_concrete()
}

fn lifecycle_error(
    name: &Symbol,
    span: Span,
    error: cranelisp_types::LifecycleError,
) -> CranelispError {
    invalid_clause(name, span, &error.to_string())
}

fn invalid_clause(name: &Symbol, span: Span, reason: &str) -> CranelispError {
    CranelispError::MacroError {
        message: format!("invalid macro clause '{name}': {reason}"),
        location: ErrorLocation::from_span(span),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        CallableTarget, ConcreteType, FQSymbol, InstanceLink, Mode, ModeSummary, MonoDefnVariant,
        MonoExpr, ParamFlow, ResultMode,
    };

    // spec: design/int/macro-turn-ownership.md Rule 0 / D4 — every synthesized
    // clause is compiled under the all-Owned fallback, independent of the
    // ownership result inferred for its body.
    #[test]
    fn macro_clause_preparation_clears_inferred_ownership_summary() {
        let mut view = MonoDefnVariant {
            name: Symbol::from("__macro_m_clause_0"),
            params: vec![Symbol::from("__args__")],
            body: MonoExpr::IntLit {
                value: 1,
                span: Span::SYNTHETIC,
                ty: ConcreteType::Int,
            },
            span: Span::SYNTHETIC,
            mode_summary: None,
        };
        view.mode_summary = Some(ModeSummary {
            param_modes: vec![Mode::Borrowed],
            result: ResultMode::Fresh,
            param_flow: vec![ParamFlow::Consumed],
            spark_ops: vec![false],
            result_unique: false,
        });

        let pinned = pin_macro_clause_ownership(view);
        assert!(pinned.mode_summary.is_none());
    }

    // spec: spec/03-types.md §3.3.4 — complete substitutions distinguish
    // independent result-context specializations across publication.
    #[test]
    fn retained_instances_preserve_result_substitutions_and_distinct_slots() {
        let module = ModuleFullPath::from("user");
        let mut checked = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let mut target = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let template = CallableTarget::Binding(FQSymbol {
            module,
            symbol: Symbol::from("g"),
        });
        let template_scheme = Scheme {
            type_vars: vec![0],
            constraints: Default::default(),
            ty: Type::Fn(
                Vec::new(),
                Box::new(Type::Fn(vec![Type::Var(0)], Box::new(Type::Int))),
            ),
        };
        let links = [ConcreteType::Int, ConcreteType::String]
            .map(|arg| InstanceLink::from_type_args(template.clone(), vec![arg]));
        for link in &links {
            let result = ConcreteType::Fn(link.type_args.clone(), Box::new(ConcreteType::Int));
            let view = MonoDefnVariant {
                name: link.instance_key(&template_scheme).unwrap(),
                params: Vec::new(),
                body: MonoExpr::Lambda {
                    params: vec![Symbol::from("y")],
                    body: Box::new(MonoExpr::IntLit {
                        value: 100,
                        span: Span::SYNTHETIC,
                        ty: ConcreteType::Int,
                    }),
                    span: Span::SYNTHETIC,
                    ty: result.clone(),
                    escapes: None,
                    confined: None,
                    unique_static: None,
                },
                span: Span::SYNTHETIC,
                mode_summary: None,
            };
            checked
                .install_instance(
                    link.clone(),
                    Scheme {
                        type_vars: Vec::new(),
                        constraints: Default::default(),
                        ty: Type::Fn(Vec::new(), Box::new(result.to_type())),
                    },
                    Vec::new(),
                    None,
                    0,
                    CallableOrigin::Plain,
                    Realization::Body { view, code: None },
                    None,
                    Vec::new(),
                    Visibility::Public,
                )
                .unwrap();
        }

        retain_checked_instances(&checked, &mut target, Span::SYNTHETIC).unwrap();
        assert_ne!(
            links[0].instance_key(&template_scheme).unwrap(),
            links[1].instance_key(&template_scheme).unwrap()
        );
        let slots = links.map(|link| {
            let key = link.instance_key(&template_scheme).unwrap();
            let original = checked.get(key.as_ref()).unwrap().callable().unwrap();
            let retained = target.get(key.as_ref()).unwrap().callable().unwrap();
            assert_eq!(retained.arm.scheme.ty, original.arm.scheme.ty);
            assert!(retained.arm.scheme.type_vars.is_empty());
            assert!(retained.arm.scheme.constraints.is_empty());
            let Life::Concrete {
                minted_from, slot, ..
            } = &retained.arm.life
            else {
                unreachable!("retained instance is concrete");
            };
            assert_eq!(minted_from.as_ref(), Some(&link));
            slot.index()
        });
        assert_ne!(slots[0], slots[1]);
    }
}
