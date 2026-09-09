//! Body-scoped selection of contested module names.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    ApplyRef, Binding, CallableOrigin, CranelispError, Decl, ErrorLocation, Expr, FQSymbol, Scheme,
    Span, Subst, Symbol, Type, TypeId, VarRef, apply, free_vars,
};

use crate::checker::{CheckState, TypeCheckEnv};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BodySettlementScope {
    /// A source body may leave selected overload applications for the sole
    /// module-wide drain, while auto-curry remains deferrable.
    TopLevel,
    /// An isolated impl/default/HKT or mono body must settle all of its own
    /// deterministic overload and auto-curry work before publication.
    Isolated,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PendingApplication {
    pub(crate) call_span: Span,
    pub(crate) argument_types: Vec<Type>,
    pub(crate) result_type: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PendingNameUse {
    pub(crate) written_name: Symbol,
    pub(crate) source_span: Span,
    pub(crate) anchor: Type,
    pub(crate) survivors: Vec<FQSymbol>,
    pub(crate) considered: Vec<FQSymbol>,
    pub(crate) applications: Vec<PendingApplication>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PendingPatternUse {
    pub(crate) written_name: Symbol,
    pub(crate) source_span: Span,
    pub(crate) scrutinee: Type,
    pub(crate) binder_anchors: Vec<Type>,
    pub(crate) survivors: Vec<FQSymbol>,
    pub(crate) considered: Vec<FQSymbol>,
}

/// Project a terminal declaration into the language's value namespace.
/// Expansion-only macro parents and their synthesized clauses remain visible
/// to the compiler's structural readers, but can never enter HM inference.
pub(crate) fn language_value_scheme<C: cranelisp_types::CodeStore>(
    binding: &Binding<C>,
) -> Option<&Scheme> {
    match &binding.declaration {
        Decl::Callable(callable) => Some(&callable.arm.scheme),
        Decl::TraitMethod(method) => Some(&method.scheme),
        Decl::Overloaded(declaration) => declaration.arms.first().map(|arm| &arm.callable.scheme),
        _ => None,
    }
}

pub(crate) fn is_value_candidate<C: cranelisp_types::CodeStore>(binding: &Binding<C>) -> bool {
    language_value_scheme(binding).is_some()
}

fn instantiate_for_trial(scheme: &Scheme, base: &Subst) -> (Type, HashMap<TypeId, TypeId>) {
    if scheme.type_vars.is_empty() {
        return (scheme.ty.clone(), HashMap::new());
    }

    let mut forbidden: HashSet<TypeId> = base.keys().copied().collect();
    for ty in base.values() {
        forbidden.extend(free_vars(ty));
    }
    forbidden.extend(free_vars(&scheme.ty));
    forbidden.extend(scheme.type_vars.iter().copied());

    let mut next = TypeId::MAX;
    let mut instantiation = Subst::new();
    let mut ids = HashMap::new();
    for original in &scheme.type_vars {
        while forbidden.contains(&next) {
            next = next
                .checked_sub(1)
                .expect("finite inference state leaves a trial TypeId");
        }
        forbidden.insert(next);
        instantiation.insert(*original, Type::Var(next));
        ids.insert(*original, next);
        next = next
            .checked_sub(1)
            .expect("finite inference state leaves a trial TypeId");
    }
    (apply(&instantiation, &scheme.ty), ids)
}

fn apply_application_constraints(
    subst: &mut Subst,
    rigid: &HashSet<TypeId>,
    candidate_type: &Type,
    application: &PendingApplication,
) -> Result<(), CranelispError> {
    let Type::Fn(parameters, result) = apply(subst, candidate_type) else {
        return Err(CranelispError::TypeError {
            message: "candidate is not callable".to_string(),
            location: ErrorLocation::from_span(application.call_span),
        });
    };
    if application.argument_types.len() > parameters.len() {
        return Err(CranelispError::TypeError {
            message: "candidate has insufficient arity".to_string(),
            location: ErrorLocation::from_span(application.call_span),
        });
    }
    for (parameter, argument) in parameters.iter().zip(application.argument_types.iter()) {
        crate::unify::unify_with_rigid(subst, rigid, parameter, argument)?;
    }
    let supplied = application.argument_types.len();
    let resulting_type = if supplied == parameters.len() {
        (*result).clone()
    } else {
        Type::Fn(parameters[supplied..].to_vec(), result)
    };
    crate::unify::unify_with_rigid(subst, rigid, &resulting_type, &application.result_type)
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Drive one inferred body to the fixed point available at its settlement
    /// seam. Candidate trials remain independent; only a unique survivor is
    /// replayed into real inference state. The deterministic stages may then
    /// strengthen the substitution and make another candidate pass productive.
    pub(crate) fn settle_body_work(
        &self,
        state: &mut CheckState,
        body: &Expr,
        scope: BodySettlementScope,
    ) -> Result<(), CranelispError> {
        loop {
            let subst_before = state.subst.clone();
            let measure_before = (
                state.body_frame.pending_name_uses.len(),
                state
                    .body_frame
                    .pending_name_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
                state.body_frame.pending_pattern_uses.len(),
                state
                    .body_frame
                    .pending_pattern_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
                state.method_resolutions.resolved_calls.len(),
                state.pending_overload_resolutions.len(),
                state.pending_auto_curry.len(),
                state.deferred_auto_curry.len(),
            );

            self.settle_pending_candidates(state, false, false)?;
            self.resolve_deferred_trait_calls(state, body)?;
            self.resolve_value_position_trait_methods(state, body, false)?;
            match scope {
                BodySettlementScope::TopLevel => {
                    self.resolve_auto_curry(state, crate::program::AutoCurryDrain::Deferrable);
                }
                BodySettlementScope::Isolated => {
                    self.resolve_pending_overloads(state, None)?;
                    self.resolve_auto_curry(state, crate::program::AutoCurryDrain::Final);
                }
            }

            let measure_after = (
                state.body_frame.pending_name_uses.len(),
                state
                    .body_frame
                    .pending_name_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
                state.body_frame.pending_pattern_uses.len(),
                state
                    .body_frame
                    .pending_pattern_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
                state.method_resolutions.resolved_calls.len(),
                state.pending_overload_resolutions.len(),
                state.pending_auto_curry.len(),
                state.deferred_auto_curry.len(),
            );
            if state.subst == subst_before && measure_after == measure_before {
                break;
            }
        }

        self.settle_pending_candidates(state, true, true)
    }

    pub(crate) fn collect_pending_pattern_use(
        &self,
        state: &mut CheckState,
        written_name: Symbol,
        source_span: Span,
        scrutinee: Type,
        binders: &[Symbol],
        mut survivors: Vec<FQSymbol>,
    ) {
        survivors.sort_by_key(ToString::to_string);
        survivors.dedup();
        let binder_anchors = binders.iter().map(|_| self.fresh_var()).collect::<Vec<_>>();
        for (name, anchor) in binders.iter().zip(&binder_anchors) {
            self.bind_local(state, name.clone(), crate::scheme::mono(anchor.clone()));
        }
        state
            .body_frame
            .pending_pattern_uses
            .push(PendingPatternUse {
                written_name,
                source_span,
                scrutinee,
                binder_anchors,
                considered: survivors.clone(),
                survivors,
            });
    }

    pub(crate) fn collect_pending_name_use(
        &self,
        state: &mut CheckState,
        written_name: Symbol,
        source_span: Span,
        mut survivors: Vec<FQSymbol>,
    ) -> Type {
        survivors.sort_by_key(ToString::to_string);
        survivors.dedup();
        let anchor = self.fresh_var();
        state.body_frame.pending_name_uses.push(PendingNameUse {
            written_name,
            source_span,
            anchor: anchor.clone(),
            considered: survivors.clone(),
            survivors,
            applications: Vec::new(),
        });
        self.record_expr_type(state, source_span, anchor.clone());
        anchor
    }

    /// Attach an application to the candidate source whose monotype flows into
    /// `callee_type`, including through a monomorphic local alias.
    pub(crate) fn attach_pending_application(
        &self,
        state: &mut CheckState,
        callee_type: &Type,
        call_span: Span,
        argument_types: Vec<Type>,
        result_type: Type,
    ) -> bool {
        let callee = self.apply_subst(state, callee_type);
        let Some(site) = state.body_frame.pending_name_uses.iter_mut().find(|site| {
            let anchor = apply(&state.subst, &site.anchor);
            anchor == callee || site.anchor == *callee_type
        }) else {
            return false;
        };
        site.applications.push(PendingApplication {
            call_span,
            argument_types,
            result_type,
        });
        true
    }

    fn candidate_is_compatible(
        &self,
        state: &CheckState,
        site: &PendingNameUse,
        fq: &FQSymbol,
    ) -> bool {
        let Some(binding) = self.probe_module_entry_owned(&fq.module, fq.symbol.as_ref()) else {
            return false;
        };
        let Some(scheme) = language_value_scheme(&binding) else {
            return false;
        };
        let mut trial_subst = state.subst.clone();
        let (candidate_type, trial_ids) = instantiate_for_trial(scheme, &trial_subst);
        if crate::unify::unify_with_rigid(
            &mut trial_subst,
            &state.body_frame.rigid_vars,
            &site.anchor,
            &candidate_type,
        )
        .is_err()
        {
            return false;
        }
        let applications_match = site.applications.iter().all(|application| {
            apply_application_constraints(
                &mut trial_subst,
                &state.body_frame.rigid_vars,
                &candidate_type,
                application,
            )
            .is_ok()
        });
        applications_match
            && self.trial_constraints_are_satisfied(state, scheme, &trial_ids, &trial_subst)
    }

    fn trial_constraints_are_satisfied(
        &self,
        state: &CheckState,
        scheme: &Scheme,
        trial_ids: &HashMap<TypeId, TypeId>,
        subst: &Subst,
    ) -> bool {
        let scheme_constraints = scheme.constraints.iter().filter_map(|(original, traits)| {
            trial_ids
                .get(original)
                .map(|trial| (*trial, traits.as_slice()))
        });
        let active_constraints = state
            .active_constraints
            .all()
            .map(|(id, traits)| (*id, traits.as_slice()));
        scheme_constraints
            .chain(active_constraints)
            .all(|(id, traits)| {
                let resolved = apply(subst, &Type::Var(id));
                let Some(type_name) = crate::traits::concrete_type_name(&resolved) else {
                    return true;
                };
                traits.iter().all(|required| {
                    self.has_impl_in_home(&required.module, &required.name, &type_name)
                })
            })
    }

    fn replay_selected_candidate(
        &self,
        state: &mut CheckState,
        site: &PendingNameUse,
        selected: &FQSymbol,
    ) -> Result<(), CranelispError> {
        let binding = self
            .probe_module_entry_owned(&selected.module, selected.symbol.as_ref())
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("selected declaration `{selected}` disappeared"),
                location: ErrorLocation::from_span(site.source_span),
            })?;
        let scheme = language_value_scheme(&binding).ok_or_else(|| CranelispError::TypeError {
            message: format!("selected declaration `{selected}` is not a value"),
            location: ErrorLocation::from_span(site.source_span),
        })?;
        let candidate_type = self.instantiate(state, scheme);
        self.unify(state, &site.anchor, &candidate_type, site.source_span)?;
        for application in &site.applications {
            apply_application_constraints(
                &mut state.subst,
                &state.body_frame.rigid_vars,
                &candidate_type,
                application,
            )
            .map_err(|error| CranelispError::TypeError {
                message: error.message().to_string(),
                location: ErrorLocation::from_span(application.call_span),
            })?;
            match &binding.declaration {
                Decl::TraitMethod(_) => {
                    let arguments = application
                        .argument_types
                        .iter()
                        .map(|argument| self.apply_subst(state, argument))
                        .collect::<Vec<_>>();
                    if let Some(dispatch) = self.try_resolve_selected_trait_method(
                        state,
                        selected,
                        &arguments,
                        application.call_span,
                    )? {
                        let resolution =
                            self.settle_dispatch(state, application.call_span, dispatch);
                        state
                            .method_resolutions
                            .resolved_calls
                            .insert(application.call_span, resolution);
                    }
                }
                Decl::Overloaded(_) => {
                    self.enqueue_selected_overload_application(
                        state,
                        selected,
                        &binding,
                        application,
                        site.source_span,
                    );
                }
                _ => {
                    state
                        .method_resolutions
                        .apply_refs
                        .insert(application.call_span, ApplyRef::ViaCallee);
                }
            }
            self.record_expr_type(
                state,
                application.call_span,
                self.apply_subst(state, &application.result_type),
            );
        }
        self.record_expr_type(
            state,
            site.source_span,
            self.apply_subst(state, &candidate_type),
        );
        state
            .method_resolutions
            .var_refs
            .insert(site.source_span, VarRef::Global(selected.clone()));
        if binding.callable().is_some_and(|callable| {
            matches!(
                callable.origin,
                CallableOrigin::Plain | CallableOrigin::TraitMethod { .. }
            )
        }) {
            state
                .body_frame
                .user_fn_refs
                .insert(site.source_span, selected.clone());
        }
        Ok(())
    }

    /// Shrink every candidate set against committed HM information and replay
    /// sites that have become unique. `final_pass` turns a stable survivor set
    /// into the source-facing no-match/ambiguity verdict.
    pub(crate) fn settle_pending_name_uses(
        &self,
        state: &mut CheckState,
        final_pass: bool,
    ) -> Result<(), CranelispError> {
        loop {
            let pending = std::mem::take(&mut state.body_frame.pending_name_uses);
            let mut remaining = Vec::new();
            let mut changed = false;
            for mut site in pending {
                let before = site.survivors.len();
                site.survivors = site
                    .survivors
                    .iter()
                    .filter(|candidate| self.candidate_is_compatible(state, &site, candidate))
                    .cloned()
                    .collect();
                site.survivors.sort_by_key(ToString::to_string);
                site.survivors.dedup();
                changed |= site.survivors.len() != before;
                if site.survivors.len() == 1 {
                    self.replay_selected_candidate(state, &site, &site.survivors[0])?;
                    changed = true;
                } else {
                    remaining.push(site);
                }
            }
            state.body_frame.pending_name_uses = remaining;
            if !changed {
                break;
            }
        }

        state
            .body_frame
            .pending_name_uses
            .sort_by_key(|site| (site.source_span.start, site.source_span.end));
        if let Some(site) = state
            .body_frame
            .pending_name_uses
            .iter()
            .find(|site| site.survivors.is_empty())
        {
            let considered = site
                .considered
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(CranelispError::TypeError {
                message: format!(
                    "no matching declaration for '{}'; considered: {considered}",
                    site.written_name
                ),
                location: ErrorLocation::from_span(site.source_span),
            });
        }
        if !final_pass || state.body_frame.pending_name_uses.is_empty() {
            return Ok(());
        }
        let site = &state.body_frame.pending_name_uses[0];
        let considered = site
            .survivors
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        let message = format!(
            "ambiguous bare name '{}'; surviving declarations: {considered}; qualify the name or add an annotation",
            site.written_name
        );
        Err(CranelispError::TypeError {
            message,
            location: ErrorLocation::from_span(site.source_span),
        })
    }

    fn pattern_candidate_is_compatible(
        &self,
        state: &CheckState,
        site: &PendingPatternUse,
        fq: &FQSymbol,
    ) -> bool {
        let Some(binding) = self.probe_module_entry_owned(&fq.module, fq.symbol.as_ref()) else {
            return false;
        };
        let Some(scheme) = language_value_scheme(&binding) else {
            return false;
        };
        let mut subst = state.subst.clone();
        let (candidate, _) = instantiate_for_trial(scheme, &subst);
        let (fields, result) = match candidate {
            Type::ADT(..) if site.binder_anchors.is_empty() => (Vec::new(), candidate),
            Type::Fn(fields, result) if fields.len() == site.binder_anchors.len() => {
                (fields, *result)
            }
            _ => return false,
        };
        if crate::unify::unify_with_rigid(
            &mut subst,
            &state.body_frame.rigid_vars,
            &site.scrutinee,
            &result,
        )
        .is_err()
        {
            return false;
        }
        fields
            .iter()
            .zip(&site.binder_anchors)
            .all(|(field, anchor)| {
                crate::unify::unify_with_rigid(
                    &mut subst,
                    &state.body_frame.rigid_vars,
                    field,
                    anchor,
                )
                .is_ok()
            })
    }

    fn replay_selected_pattern(
        &self,
        state: &mut CheckState,
        site: &PendingPatternUse,
        selected: &FQSymbol,
    ) -> Result<(), CranelispError> {
        let binding = self
            .probe_module_entry_owned(&selected.module, selected.symbol.as_ref())
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("selected constructor `{selected}` disappeared"),
                location: ErrorLocation::from_span(site.source_span),
            })?;
        let scheme = language_value_scheme(&binding).ok_or_else(|| CranelispError::TypeError {
            message: format!("selected declaration `{selected}` is not a constructor"),
            location: ErrorLocation::from_span(site.source_span),
        })?;
        let candidate = self.instantiate(state, scheme);
        let (fields, result) = match candidate {
            Type::ADT(..) if site.binder_anchors.is_empty() => (Vec::new(), candidate),
            Type::Fn(fields, result) if fields.len() == site.binder_anchors.len() => {
                (fields, *result)
            }
            _ => {
                return Err(CranelispError::TypeError {
                    message: format!("constructor '{}' has the wrong arity", site.written_name),
                    location: ErrorLocation::from_span(site.source_span),
                });
            }
        };
        self.unify(state, &site.scrutinee, &result, site.source_span)?;
        for (field, anchor) in fields.iter().zip(&site.binder_anchors) {
            self.unify(state, field, anchor, site.source_span)?;
        }
        state
            .method_resolutions
            .pattern_ctors
            .insert(site.source_span, selected.clone());
        Ok(())
    }

    pub(crate) fn settle_pending_pattern_uses(
        &self,
        state: &mut CheckState,
        final_pass: bool,
    ) -> Result<(), CranelispError> {
        loop {
            let pending = std::mem::take(&mut state.body_frame.pending_pattern_uses);
            let mut remaining = Vec::new();
            let mut changed = false;
            for mut site in pending {
                let before = site.survivors.len();
                site.survivors = site
                    .survivors
                    .iter()
                    .filter(|candidate| {
                        self.pattern_candidate_is_compatible(state, &site, candidate)
                    })
                    .cloned()
                    .collect();
                site.survivors.sort_by_key(ToString::to_string);
                site.survivors.dedup();
                changed |= site.survivors.len() != before;
                if site.survivors.len() == 1 {
                    self.replay_selected_pattern(state, &site, &site.survivors[0])?;
                    changed = true;
                } else {
                    remaining.push(site);
                }
            }
            state.body_frame.pending_pattern_uses = remaining;
            if !changed {
                break;
            }
        }
        if let Some(site) = state
            .body_frame
            .pending_pattern_uses
            .iter()
            .find(|site| site.survivors.is_empty())
        {
            let considered = site
                .considered
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(CranelispError::TypeError {
                message: format!(
                    "no matching constructor for '{}'; considered: {considered}",
                    site.written_name
                ),
                location: ErrorLocation::from_span(site.source_span),
            });
        }
        if final_pass && let Some(site) = state.body_frame.pending_pattern_uses.first() {
            let survivors = site
                .survivors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(CranelispError::TypeError {
                message: format!(
                    "ambiguous constructor '{}'; surviving declarations: {survivors}; qualify the constructor or add an annotation",
                    site.written_name
                ),
                location: ErrorLocation::from_span(site.source_span),
            });
        }
        Ok(())
    }

    /// Interleave value and pattern settlement until neither survivor measure
    /// shrinks. Selection remains per-site: this loop never enumerates or
    /// commits cross-site candidate combinations.
    pub(crate) fn settle_pending_candidates(
        &self,
        state: &mut CheckState,
        final_names: bool,
        final_patterns: bool,
    ) -> Result<(), CranelispError> {
        loop {
            let before = (
                state.body_frame.pending_name_uses.len(),
                state
                    .body_frame
                    .pending_name_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
                state.body_frame.pending_pattern_uses.len(),
                state
                    .body_frame
                    .pending_pattern_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
            );
            self.settle_pending_name_uses(state, false)?;
            self.settle_pending_pattern_uses(state, false)?;
            let after = (
                state.body_frame.pending_name_uses.len(),
                state
                    .body_frame
                    .pending_name_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
                state.body_frame.pending_pattern_uses.len(),
                state
                    .body_frame
                    .pending_pattern_uses
                    .iter()
                    .map(|site| site.survivors.len())
                    .sum::<usize>(),
            );
            if after == before {
                break;
            }
        }
        if final_names {
            self.settle_pending_name_uses(state, true)?;
        }
        if final_patterns {
            self.settle_pending_pattern_uses(state, true)?;
        }
        Ok(())
    }
}
