//! The MULTI-SIGNATURE overload family — registration and dispatch resolution
//! for a `defn` with several arity/type clauses (`spec/05-definitions.md`
//! §5.1.2; `design/typecheck/monomorphisation.md` §11.3/§11.4).
//!
//! One concern end-to-end: turn the clause set into mangled declarations plus
//! an overloaded-base index (`resolve_multi_sig_overloads`,
//! `register_mangled_variants`, `register_overloaded_base`), refine each checked
//! clause at Phase A (`finalize_multi_sig_variant_types`,
//! `resolve_variant_types`), and drain each deferred call site to its selected
//! clause (`resolve_pending_overloads` → `resolve_one_overload_call`, the
//! §5.1.2 back-flow).
//!
//! Cut out of `program/register.rs` at the S115 W4 re-budget (FIXME 0722).

use super::*;

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Rehydrate an overload-arm template from its committed declaration
    /// family. This is the restart path: private clause labels used while the
    /// source cluster was checked have already been discarded.
    pub(crate) fn owned_overload_template(
        &self,
        target: &CallableTarget,
    ) -> Option<crate::traits::TemplateFn> {
        let CallableTarget::OverloadArm { owner, arm } = target else {
            return None;
        };
        let binding = self.probe_module_entry_owned(&owner.module, owner.symbol.as_ref())?;
        let Decl::Overloaded(declaration) = binding.declaration else {
            return None;
        };
        let owned_arm = declaration
            .arms
            .get(arm.ordinal())
            .filter(|candidate| candidate.id == *arm)?;
        let Life::Template { body, .. } = &owned_arm.callable.life else {
            return None;
        };
        Some(crate::traits::TemplateFn {
            core: crate::traits::TemplateCore {
                body: body.clone(),
                scheme: owned_arm.callable.scheme.clone(),
                origin: CallableOrigin::Plain,
            },
            local_templates: HashMap::new(),
            template_target: Some(target.clone()),
        })
    }

    /// Resolve multi-sig overloads after pass 2: build mangled names from
    /// concrete types, check for duplicates, register mangled names in symbol
    /// table, and populate `resolved_overloads`.
    ///
    /// Returns a list of mangled Defn objects that the backend should compile.
    /// `mangled_by_base` is an OUT-parameter: for each multi-sig base name it
    /// receives the MANGLED variant names that `register_mangled_variants`
    /// inserted (S91 Wave-7, FIXME 0432 Face A). The finalize re-annotation block
    /// and the return-type refresh need these keys: the internal `{name}__v{i}`
    /// entries no longer exist (they were removed-and-reinserted under the
    /// mangled names here), so a stale internal-key lookup misses and an in-body
    /// self-call's `SigDispatch` resolution never reaches the variant body —
    /// leaving the backend to fall back to the undefined bare name. (Out-param,
    /// not a return-tuple, to keep this fn's `Result` Ok-type unchanged.)
    pub(crate) fn resolve_multi_sig_overloads(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
        accumulator: &mut ModuleCheckAccumulator,
        mangled_by_base: &mut MangledNamesByBase,
    ) -> Result<Vec<Defn>, CranelispError> {
        let mut result_defns = Vec::new();

        for top in program {
            if let TopLevel::Defn(defn) = top {
                if !defn.is_multi_sig() {
                    continue;
                }

                let resolved = self.resolve_variant_types(state, defn, &accumulator.bodies)?;
                let (mangled_defns, resolved_info) = self.register_mangled_variants(
                    state,
                    defn,
                    &resolved,
                    &mut accumulator.bodies,
                )?;
                mangled_by_base
                    .entry(defn.name.clone())
                    .or_default()
                    .extend(resolved_info.iter().map(|(_, _, mangled)| mangled.clone()));
                result_defns.extend(mangled_defns);
                self.register_overloaded_base(state, defn, resolved_info)?;
            }
        }

        Ok(result_defns)
    }

    /// Post-drain finalisation of multi-sig variant types (S112 leg a §11.3(B),
    /// extends the S91 Wave-7 / FIXME 0432 Face A return-type refresh).
    ///
    /// Runs AFTER the module-wide `resolve_pending_overloads` drain, once the §5.1.2
    /// back-flow has settled every clause's params. Two phases:
    ///
    /// **Phase A — promote back-flow-pinned clause targets.** A clause
    /// pinned concrete by a sibling self-call (`rp4`'s 2-arg clause) was
    /// provisionally targeted at a `$Var` declaration pre-drain (its params were
    /// still `Var`). Now that its params are concrete its checked ledger record
    /// is re-keyed to the CONCRETE mangle —
    /// the exact name the drain's concrete branch already recorded in each
    /// caller's `SigDispatch` (Principle 7, one `mangle_sig` source ⇒ no rewrite).
    /// The base `OverloadVariant`, `resolved_overloads`, and the re-annotation
    /// name map are re-pointed at the concrete sibling, and the stale `$Var`
    /// template entry is removed (§11.3(B): no `$Var` Concrete entry survives, and
    /// no dead `$Var` template lingers for a back-flow clause). A genuinely
    /// constrained/polymorphic clause (`g$Var`) keeps its `Var` params here → is
    /// left untouched as a template (its mono instances carry codegen).
    ///
    /// **Phase B — refresh persisted RETURN types.** A variant whose body
    /// self-calls another has a return pinned only by the drain, captured stale in
    /// Pass 2.5; walk the final subst over the stored return types so a later REPL
    /// cluster rehydrating `resolved_overloads`/the base entry sees the concrete
    /// return.
    pub(crate) fn finalize_multi_sig_variant_types(
        &self,
        state: &mut CheckState,
        working_program: &[TopLevel],
        accumulator: &mut ModuleCheckAccumulator,
        multi_sig_mangled_names: &mut MangledNamesByBase,
    ) -> Result<(), CranelispError> {
        // B1 fix (§11.3.2): drain the deferred self-call worklist and group by the
        // selected clause. Taken unconditionally so no stale entry survives into a
        // later REPL cluster. Each self-call's `SigDispatch` is derived below from
        // the SAME `mangle_sig` (over the finalised post-drain params) that keys the
        // clause's `Concrete` entry — carriers 5–6 join carriers 1–4 at ONE source.
        let mut deferred_by_variant: HashMap<(Symbol, usize), Vec<Span>> = HashMap::new();
        for (span, base, idx) in std::mem::take(&mut state.deferred_self_call_dispatch) {
            deferred_by_variant
                .entry((base, idx))
                .or_default()
                .push(span);
        }

        if multi_sig_mangled_names.is_empty() {
            return Ok(());
        }

        // ---- Phase A — promote back-flow-pinned clauses to Concrete ----
        for top in working_program {
            let TopLevel::Defn(defn) = top else { continue };
            if !defn.is_multi_sig() {
                continue;
            }
            let Some(names) = multi_sig_mangled_names.get(&defn.name).cloned() else {
                continue;
            };
            for (i, dispatch_name) in names.iter().enumerate() {
                let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                let Some(registration) = accumulator
                    .bodies
                    .registration_for_publication(dispatch_name)
                    .or_else(|| {
                        accumulator
                            .bodies
                            .registration_for_publication(&internal_name)
                    })
                else {
                    continue;
                };
                let concrete_params: Vec<Type> = registration
                    .param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect();
                let concrete_ret = self.apply_subst(state, &registration.ret_ty);

                // The clause's finalised mangle — over the post-drain subst-applied
                // params. Concrete (`f3$Int`) for a back-flow-pinned / own-annotated
                // clause; the normalized `$Var` name for a clause left a
                // genuinely-polymorphic / constrained template. This is the ONE
                // `mangle_sig` source (Principle 7) feeding BOTH the clause's entry
                // key (carriers 1–4, below) AND every deferred self-call
                // `SigDispatch` that selected clause `i` (carriers 5–6) — so all six
                // agree by construction, order-independent (Principle 24).
                let concrete_mangled = mangle_sig(defn.name.as_ref(), &concrete_params);

                // B1 fix (§11.3.2 carriers 5–6): every self-call that selected this
                // clause now gets its `SigDispatch` from `concrete_mangled`, derived
                // ONCE here (post-drain, every clause settled) — never mid-drain
                // where a ≥2-hop chain leaves a later clause `$Var`. Recorded for a
                // template clause too (its `$Var` name is a real slot-less entry;
                // the mono recheck of an external instantiation re-resolves the
                // in-instance self-call — I1).
                if let Some(spans) = deferred_by_variant.get(&(defn.name.clone(), i)) {
                    for &self_span in spans {
                        let resolution = ResolvedCall::SigDispatch {
                            target: CallableTarget::OverloadArm {
                                owner: FQSymbol {
                                    module: state.current_module.clone(),
                                    symbol: defn.name.clone(),
                                },
                                arm: CallableArmId::from_ordinal(i)
                                    .map_err(crate::result::lifecycle_error)?,
                            },
                        };
                        self.record_dispatch_target(state, self_span, &resolution);
                        state
                            .method_resolutions
                            .resolved_calls
                            .insert(self_span, resolution);
                    }
                }

                // A genuinely constrained/polymorphic clause keeps `Var` params →
                // stays a template, unchanged (only its self-call dispatch, recorded
                // above against its `$Var` name, was updated).
                if !concrete_params.iter().all(Type::is_concrete) {
                    continue;
                }
                // Already concrete pre-drain (own-annotated clause) — nothing to
                // promote; Phase B refreshes its return.
                if *dispatch_name == concrete_mangled {
                    continue;
                }
                // Back-flow clause: promote its `$Var` `Polymorphic` template to a
                // `Concrete{slot}` sibling under the concrete mangle.
                let fn_ty = Type::Fn(concrete_params.clone(), Box::new(concrete_ret.clone()));
                let scheme = self.generalize(state, &fn_ty);
                let variant = &defn.variants[i];
                let doc = self
                    .current_symbol_table(state)
                    .view()
                    .lookup(dispatch_name)
                    .and_then(Binding::callable)
                    .and_then(|callable| callable.docstring.clone());
                self.current_symbol_table_mut(state)
                    .declare(
                        concrete_mangled.clone(),
                        scheme,
                        variant.params.iter().map(|(n, _)| n.clone()).collect(),
                        doc,
                        0,
                        CallableOrigin::Plain,
                        defn.visibility,
                    )
                    .map_err(crate::result::lifecycle_error)?;
                self.current_symbol_table_mut(state)
                    .discard_declared(dispatch_name)
                    .map_err(crate::result::lifecycle_error)?;
                accumulator
                    .bodies
                    .rekey_publication(dispatch_name, concrete_mangled.clone())?;
                // Refresh the type facts and the private work label.
                if let Some(vs) = state.resolved_overloads.get_mut(&defn.name)
                    && let Some(v) = vs.get_mut(i)
                {
                    *v = (
                        concrete_params.clone(),
                        concrete_ret.clone(),
                        concrete_mangled.clone(),
                    );
                }
                // Re-point the re-annotation name map so
                // `finalize_annotations_and_publish` re-annotates the concrete
                // sibling (not the removed `$Var` template).
                if let Some(names_mut) = multi_sig_mangled_names.get_mut(&defn.name)
                    && let Some(n) = names_mut.get_mut(i)
                {
                    *n = concrete_mangled.clone();
                }
            }
        }

        // ---- Phase B — refresh persisted return types through the final subst ----
        let subst = state.subst.clone();
        for variants in state.resolved_overloads.values_mut() {
            for (_params, ret, _private_label) in variants.iter_mut() {
                *ret = apply(&subst, ret);
            }
        }
        for (_base, mangled_names) in multi_sig_mangled_names.iter() {
            for mangled in mangled_names {
                let Some(registration) = accumulator.bodies.registration_for_publication(mangled)
                else {
                    continue;
                };
                let fn_ty = Type::Fn(
                    registration
                        .param_types
                        .iter()
                        .map(|ty| apply(&subst, ty))
                        .collect(),
                    Box::new(apply(&subst, &registration.ret_ty)),
                );
                let scheme = self.generalize(state, &fn_ty);
                self.current_symbol_table_mut(state)
                    .update_declared_scheme(mangled, scheme)
                    .map_err(crate::result::lifecycle_error)?;
            }
        }
        Ok(())
    }

    /// For a single multi-sig defn, resolve each variant's concrete param/return
    /// types by applying substitution, and check for duplicate signatures.
    ///
    /// Returns a vec of `(concrete_params, concrete_ret, internal_name, variant_index)`
    /// for each variant.
    pub(crate) fn resolve_variant_types(
        &self,
        state: &CheckState,
        defn: &Defn,
        bodies: &BodyLedger,
    ) -> Result<Vec<ResolvedVariant>, CranelispError> {
        let mut resolved = Vec::new();
        let mut sig_set: Vec<Vec<Type>> = Vec::new();

        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));

            let registration = bodies
                .registration_for_publication(&internal_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!(
                        "internal: missing type vars for multi-sig variant {}",
                        internal_name
                    ),
                    location: ErrorLocation::from_span(variant.span),
                })?;

            let concrete_params: Vec<Type> = registration
                .param_types
                .iter()
                .map(|t| self.apply_subst(state, t))
                .collect();
            let concrete_ret = self.apply_subst(state, &registration.ret_ty);

            // §5.1.1 dispatch coherence — the DEFINITION-SITE overlap check
            // (S112 leg a, MS-6/CP-2; spec §5.1.2 MUST "reported at the
            // definition, both colliding clauses named").
            //
            // Strict-equal signatures are the exact-duplicate subcase.
            if let Some(prev) = sig_set.iter().position(|s| s == &concrete_params) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "duplicate signature for '{}': arity clauses #{} and #{} \
                         both have parameter types ({})",
                        defn.name,
                        prev + 1,
                        i + 1,
                        concrete_params
                            .iter()
                            .map(|t| format!("{t}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    location: ErrorLocation::from_span(variant.span),
                });
            }
            // The general case: two SAME-ARITY clauses whose signatures can
            // UNIFY are a dispatch-ambiguity — a call matching one matches both,
            // regardless of which clause is concrete vs written-var/constrained
            // (`[:Int x]` + `[:a x]`, the CP-2 constrained×concrete overlap).
            // Reported HERE at the definition (both clauses named by arity index),
            // NOT deferred to a call-site `Ambiguous` — the spec MUST that the old
            // strict-equal-only check under-implemented.
            if let Some(prev) = sig_set.iter().position(|s| {
                s.len() == concrete_params.len()
                    && s.iter()
                        .zip(concrete_params.iter())
                        .all(|(a, b)| types_compatible(a, b))
            }) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "ambiguous dispatch for '{}': the {}-arg arity clauses \
                         #{} and #{} have unifiable (overlapping) parameter types \
                         — a call matching one matches both signatures (spec \
                         §5.1.1 dispatch coherence); make their parameter types \
                         disjoint",
                        defn.name,
                        concrete_params.len(),
                        prev + 1,
                        i + 1
                    ),
                    location: ErrorLocation::from_span(variant.span),
                });
            }
            sig_set.push(concrete_params.clone());

            resolved.push((concrete_params, concrete_ret, internal_name, i));
        }

        Ok(resolved)
    }

    /// For each resolved variant, compute the mangled name, update the symbol
    /// table (remove internal name, register mangled name), and build the
    /// mangled `Defn` for the backend.
    ///
    /// Returns `(mangled_defns, resolved_info)` where `resolved_info` is
    /// `(concrete_params, concrete_ret, mangled_name)` per variant.
    pub(crate) fn register_mangled_variants(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        resolved: &[ResolvedVariant],
        bodies: &mut BodyLedger,
    ) -> Result<(Vec<Defn>, Vec<MangledVariantInfo>), CranelispError> {
        let mut mangled_defns = Vec::new();
        let mut resolved_info = Vec::new();

        for (concrete_params, concrete_ret, internal_name, idx) in resolved {
            let variant = &defn.variants[*idx];
            let mangled = mangle_sig(defn.name.as_ref(), concrete_params);

            // §11.4 bifurcation — a clause whose PARAMS are non-concrete
            // (constrained `:a`, or a genuinely-polymorphic `:a`) is NOT a single
            // concrete callable: KEEP its slot-less `Constrained`/`Polymorphic`
            // template entry, re-keyed to the clause's normalized-var mangle
            // (`g$Var`), and record THAT name in the base's
            // `OverloadVariant.mangled_name`. Per-call-site dispatch at the drain
            // reads the referenced entry's kind and routes a template clause
            // through `monomorphise_call` exactly as a standalone
            // constrained/parametric fn (no `OverloadVariant` field — the kind
            // lives on the entry, Principle 7). This makes the §11.3(B) invariant
            // hold: no `$Var` Concrete entry survives — a `$Var` mangle always
            // references a template. A clause that a sibling self-call PINS
            // concrete (`rp4`'s 2-arg clause) still has `Var` PARAMS HERE
            // (pre-drain, before the self-call drains); it rides the template
            // branch now and gains its `Concrete` sibling post-drain in
            // `finalize_multi_sig_variant_types`, once the back-flow settles.
            //
            // The bifurcation keys on PARAM concreteness, NOT the `__vN` fn_state:
            // a clause with CONCRETE params but a `Var` RETURN (`([:Int n] (h n
            // n))` — the return is pinned only by the self-call at the drain) is a
            // `Polymorphic` `__vN`, yet it is a single concrete callable (its
            // params fix its identity) and MUST take the concrete path, else its
            // `$Int` mangle would reference a slot-less template and the backend
            // would hit `undefined function` on the external call.
            let fn_ty = Type::Fn(concrete_params.clone(), Box::new(concrete_ret.clone()));
            let scheme = self.generalize(state, &fn_ty);
            self.current_symbol_table_mut(state)
                .declare(
                    mangled.clone(),
                    scheme,
                    variant.params.iter().map(|(n, _)| n.clone()).collect(),
                    defn.docstring.clone(),
                    0,
                    CallableOrigin::Plain,
                    defn.visibility,
                )
                .map_err(crate::result::lifecycle_error)?;
            self.current_symbol_table_mut(state)
                .discard_declared(internal_name)
                .map_err(crate::result::lifecycle_error)?;
            bodies.rekey_publication(internal_name, mangled.clone())?;

            // Build the mangled defn for the backend
            mangled_defns.push(Defn {
                name: mangled.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            });

            resolved_info.push((concrete_params.clone(), concrete_ret.clone(), mangled));
        }

        Ok((mangled_defns, resolved_info))
    }

    /// Build `OverloadVariant` entries, register the base name as `Overloaded`
    /// in the symbol table, and record resolved overloads in state.
    pub(crate) fn register_overloaded_base(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        resolved: Vec<(Vec<Type>, Type, Symbol)>,
    ) -> Result<(), CranelispError> {
        state.resolved_overloads.insert(defn.name.clone(), resolved);
        Ok(())
    }

    /// Resolve pending overload dispatch resolutions through the shared drain.
    ///
    /// Top-level finalization owns the sole module-wide invocation (§5.1.2).
    /// Mono rechecks and locally-settled impl/default/HKT bodies first isolate
    /// their own pending queue, then invoke this worker without consuming the
    /// module queue.
    ///
    /// Two passes over the pending list (S112 leg a §11.3(B)/§11.4):
    ///
    /// 1. **Self-calls (monomorphic recursion).** A cross-clause sibling self-call
    ///    inside the SAME multi-sig `defn` is monomorphic recursion within the
    ///    mutually-recursive group: UNIFY the selected clause's params with the
    ///    args, pinning whichever side is unbound — the §5.1.2 back-flow. This runs
    ///    FIRST so every clause's params are settled before external calls are
    ///    resolved.
    /// 2. **External calls.** A call to a CONCRETE clause (own-annotated, or pinned
    ///    concrete by a self-call in pass 1 — `rp4`/`rp15`) unifies + dispatches to
    ///    the concrete mangle. A call to a genuinely-polymorphic / trait-constrained
    ///    TEMPLATE clause monomorphises at this call's args (fresh instantiation) so
    ///    distinct external calls at distinct types never conflict, and dispatches
    ///    to the minted instance.
    pub(crate) fn resolve_pending_overloads(
        &self,
        state: &mut CheckState,
        bodies: Option<&BodyLedger>,
    ) -> Result<(), CranelispError> {
        let pending = std::mem::take(&mut state.pending_overload_resolutions);

        // Pass 1 — self-calls (monomorphic recursion).
        for (span, base_name, arg_types, ret_type_var, is_self, callee_span) in &pending {
            if !is_self {
                continue;
            }
            self.resolve_one_overload_call(
                state,
                *span,
                base_name,
                arg_types,
                ret_type_var,
                true,
                *callee_span,
                bodies,
            )?;
        }
        // Pass 2 — external calls.
        for (span, base_name, arg_types, ret_type_var, is_self, callee_span) in &pending {
            if *is_self {
                continue;
            }
            self.resolve_one_overload_call(
                state,
                *span,
                base_name,
                arg_types,
                ret_type_var,
                false,
                *callee_span,
                bodies,
            )?;
        }

        Ok(())
    }

    /// Resolve one pending overload call (`resolve_pending_overloads` worker).
    /// `is_self_call` selects monomorphic-recursion UNIFY (self-call) vs the
    /// concrete-or-monomorphise external dispatch bifurcation.
    #[allow(clippy::too_many_arguments)]
    fn resolve_one_overload_call(
        &self,
        state: &mut CheckState,
        span: Span,
        base_name: &Symbol,
        arg_types: &[Type],
        ret_type_var: &Type,
        is_self_call: bool,
        callee_span: Span,
        bodies: Option<&BodyLedger>,
    ) -> Result<(), CranelispError> {
        let concrete_args: Vec<Type> = arg_types.iter().map(|t| apply(&state.subst, t)).collect();

        let variants = state
            .resolved_overloads
            .get(base_name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("no overloaded function: {}", base_name),
                location: ErrorLocation::from_span(span),
            })?
            .clone();

        // The ONE shared overload-selection predicate (Principle 7, I-B).
        let (param_types, ret_ty, mangled_name) =
            match select_unique_overload_variant(&variants, &concrete_args) {
                OverloadSelection::Unique(v) => v.clone(),
                OverloadSelection::Ambiguous(count) => {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "ambiguous call to '{}' — {} matching signatures",
                            base_name, count
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
                OverloadSelection::NoMatch => {
                    // If exactly one variant matches by ARITY, the wrong-type call
                    // is a TYPE mismatch, not a no-signature (wrong-arity) miss —
                    // unify that variant's params against the args to surface the
                    // precise "expected X, got Y" (the standalone-equivalent
                    // diagnostic the §5.1.2 equivalence implies: a back-flow-pinned
                    // 2-arg clause `(Fn [Int Int] Int)` called `(rp15 "x" "y")` is a
                    // String≠Int mismatch, cleanly rejected — never a memory-unsafe
                    // read). A genuine arity miss keeps the no-signature error.
                    let arity_only: Vec<&(Vec<Type>, Type, Symbol)> = variants
                        .iter()
                        .filter(|(p, _, _)| p.len() == concrete_args.len())
                        .collect();
                    if let [only] = arity_only.as_slice() {
                        for (p, a) in only.0.iter().zip(concrete_args.iter()) {
                            self.unify(state, p, a, span)?;
                        }
                    }
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "no matching signature for '{}' with arg types ({})",
                            base_name,
                            concrete_args
                                .iter()
                                .map(|t| format!("{t}"))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
            };
        let variant_index = variants
            .iter()
            .position(|(_, _, private_label)| private_label == &mangled_name)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("internal: selected overload arm missing from `{base_name}`"),
                location: ErrorLocation::from_span(span),
            })?;
        let owner_module = state
            .overload_homes
            .get(base_name)
            .cloned()
            .unwrap_or_else(|| state.current_module.clone());
        let owner_symbol = Symbol::from(
            base_name
                .as_ref()
                .rsplit('/')
                .next()
                .unwrap_or(base_name.as_ref()),
        );
        let selected_target = CallableTarget::OverloadArm {
            owner: FQSymbol {
                module: owner_module,
                symbol: owner_symbol,
            },
            arm: CallableArmId::from_ordinal(variant_index)
                .map_err(crate::result::lifecycle_error)?,
        };

        let resolved_variant_params: Vec<Type> =
            param_types.iter().map(|t| apply(&state.subst, t)).collect();

        if is_self_call {
            // Monomorphic recursion: UNIFY the clause's params + return with the
            // call, pinning whichever side is unbound (the §5.1.2 back-flow —
            // `rp15`'s 3-arg clause pins the poly 2-arg clause to `Int`; `rp4`'s
            // 2-arg clause is itself pinned by its call to the concrete 3-arg
            // sibling). This unify IS the back-flow and MUST run during the drain.
            for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                self.unify(state, p, a, span)?;
            }
            self.unify(state, ret_type_var, &ret_ty, span)?;
            // B1 fix (§11.3.2, Option (1) DEFERRAL): record NO `SigDispatch` here.
            // Deriving the dispatch name mid-drain is order-dependent — in a ≥2-hop
            // delegation chain the selected clause's params may still be `Var` at
            // THIS point (that clause is pinned only when ITS OWN self-call drains
            // later in this same pass-1 loop), so a mid-drain mangle records the
            // `$Var` template name, which `finalize_multi_sig_variant_types` Phase A
            // then removes → a dangling `$Var` dispatch reaches codegen. Instead,
            // defer the site (span + selected clause index); its `SigDispatch` is
            // derived ONCE post-drain in `finalize_multi_sig_variant_types` from the
            // SAME `mangle_sig` over the finalised (subst-applied) clause params that
            // keys the clause's `Concrete` entry — so all six carriers agree by
            // construction and order-independence is unrepresentable (Principle 24),
            // not repaired.
            // N1 (S112 W2.1 review minor): the selected clause's mangled name is
            // always one of `variants` (it was chosen from that very set), so the
            // position lookup is a hard invariant, not a silent-`0` fallback — a
            // miss would silently defer the WRONG variant's dispatch (P18/P25).
            state
                .deferred_self_call_dispatch
                .push((span, base_name.clone(), variant_index));
            // FIXME 0719 (§11.8.11) — RETYPE THE CALLEE NODE from settled state.
            // Mirror of the inline dispatch arm in `infer.rs::infer_apply`
            // ("Retype the callee (the overloaded base `Var`) to the sibling
            // clause's concrete signature — `from_expr` requires every node
            // concrete, and the base otherwise carries the polymorphic union").
            // The deferred arm skipped it, so the callee `Var` kept the
            // PRE-DISPATCH instantiation of the overloaded base. That is
            // invisible while the same vars happen to be pinned globally by a
            // top-level concrete call — and fatal one indirection out
            // (`(defn run-elim [idx] (vec-len (peers idx)))`), where the
            // wrapper's monomorphisation instantiates FRESH vars for the base:
            // the minted `peers$Var$Int` shipped `Fn([Var(31)], Var(32))` on its
            // callee node and `from_expr` rejected the instance as ambiguous.
            //
            // The dispatch DECISION is settled here (the clause is selected and
            // its params are back-flow-unified above), so the node's type is
            // recorded from that decision, not re-derived later (Principle 26).
            // The NAME is still deferred (the paragraph above) — that is a
            // separate carrier with a separate hazard; the TYPE has no ordering
            // hazard, because any var still unbound at this point is grounded by
            // the final `resolve_expr_types` subst application
            // (`mono_collect.rs` — it maps `apply(&state.subst, ty)` over EVERY
            // recorded node type), the same monotone subst §11.8.10 obligation 2
            // relies on. So this can only move toward ground.
            //
            // Read the params/return back out of the subst AFTER the back-flow
            // unifies above — `resolved_variant_params` was computed before them
            // and is therefore pre-settlement (0774).
            let settled_params: Vec<Type> =
                param_types.iter().map(|t| apply(&state.subst, t)).collect();
            let settled_ret = apply(&state.subst, &ret_ty);
            self.record_expr_type(
                state,
                callee_span,
                Type::Fn(settled_params, Box::new(settled_ret)),
            );

            return Ok(());
        }

        // External call — bifurcate on the selected arm's lifecycle. Its
        // instantiated parameters can be concrete even when the declaration
        // arm is a template, so substituted type shape is not a valid proxy.
        let mut selected_template = state.mono_recheck_self.as_ref().and_then(|context| {
            context
                .local_templates
                .get(&mangled_name)
                .cloned()
                .map(|core| crate::traits::TemplateFn {
                    core,
                    local_templates: context.local_templates.clone(),
                    template_target: Some(selected_target.clone()),
                })
        });
        if selected_template.is_none() {
            selected_template =
                bodies.and_then(|ledger| self.checked_body_template(state, ledger, &mangled_name));
            if let Some(template) = selected_template.as_mut() {
                template.template_target = Some(selected_target.clone());
            }
        }
        if selected_template.is_none() {
            selected_template = self.owned_overload_template(&selected_target);
        }
        if selected_template.is_none() {
            // CONCRETE clause: unify the variant's params with the call args
            // (type-check them) and dispatch to the CONCRETE mangle — the exact
            // name `finalize_multi_sig_concrete_variants` registers the entry
            // under (one `mangle_sig` source, Principle 7 ⇒ no SigDispatch rewrite).
            for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                self.unify(state, p, a, span)?;
            }
            self.unify(state, ret_type_var, &ret_ty, span)?;
            // Fix A (MC-X2 qualified face) — mangle the concrete dispatch identity
            // from the BARE base name (strip any module qualifier), NEVER the
            // WRITTEN reference. This matches `finalize_multi_sig_variant_types`
            // Phase A, which registers a back-flow-pinned clause under
            // `mangle_sig(defn.name, concrete_params)` (bare), so the drain's
            // re-derivation must also be bare (`rp4$Int+Int`, not the still-`$Var`
            // stored `mangled_name` Phase A hasn't promoted yet). For an imported
            // base the qualified reference `mlib/h` must NOT leak into the mangle
            // (`mangle_sig("mlib/h",…) = "mlib/h$Int"` → the bad `mlib/mlib/h$Int`)
            // — the stored entry is `h$Int` in `mlib`. Bare-name mangle serves both.
            let bare_base = base_name
                .as_ref()
                .rsplit('/')
                .next()
                .unwrap_or(base_name.as_ref());
            let concrete_mangled = mangle_sig(bare_base, &resolved_variant_params);
            let resolution = ResolvedCall::SigDispatch {
                target: selected_target,
            };
            self.record_dispatch_target(state, span, &resolution);
            state
                .method_resolutions
                .resolved_calls
                .insert(span, resolution);
            // MC-X2 (W2-close) — an IMPORTED base's concrete clause `Def` lives in
            // its HOME module, not the caller's. `record_dispatch_target` keyed the
            // carrier at `current_module` (the `SigDispatch` arm's "always local"
            // assumption — correct only for a LOCAL base); override with the base's
            // recorded home so the backend keyed-read finds `mlib/h$Int` (P24 —
            // key by storage identity). Local bases have no `overload_homes` entry
            // → no override. Also cures the W2a scoped-drain carrier's same
            // current-module face (this is the ONE drain both use).
            if let Some(home) = state.overload_homes.get(base_name).cloned() {
                state.method_resolutions.apply_refs.insert(
                    span,
                    cranelisp_types::ApplyRef::Dispatch(FQSymbol {
                        module: home,
                        symbol: Symbol::from(concrete_mangled.as_ref()),
                    }),
                );
            }
            // FIXME 0719 (§11.8.11) — THE LOAD-BEARING ARM (bisect-confirmed).
            // Retype the callee node to the SELECTED clause's concrete signature
            // (see the self-call arm above for the full rationale). This is the
            // arm a wrapper-indirected mono recheck takes: inside the minted
            // instance of a `$Var` template clause the base is no longer the
            // enclosing defn, so its sibling call drains as an EXTERNAL call to
            // the concrete clause — and the callee node kept the base's
            // pre-dispatch instantiation, whose element var never settled.
            self.record_expr_type(
                state,
                callee_span,
                Type::Fn(resolved_variant_params.clone(), Box::new(ret_ty.clone())),
            );
        } else {
            // TEMPLATE clause (constrained / genuinely-polymorphic, §11.4 step 4).
            // Its params must NOT be globally pinned (a second external call at a
            // different concrete type must not conflict), so monomorphise at THIS
            // call's concrete args — the standalone constrained/parametric
            // machinery — and dispatch to the minted INSTANCE. `home` is `None`:
            // the clause template lives in the current module (a local multi-sig
            // defn).
            // `origin_base = Some(base_name)`: this external call monomorphises a
            // multi-sig `$Var` TEMPLATE clause. Threading the base lets the recheck
            // resolve an inner self-call to that base at these args as monomorphic
            // recursion to THIS instance (§11.3.1 caveat (b) / I1), instead of
            // orphaning a pending entry the drain has taken.
            // A generic caller can select an overload arm before its own
            // arguments are grounded. That caller is itself retained as a
            // template and this call is rechecked when a concrete caller mints
            // it; do not mint a lossy partial overload instance now.
            let Some(template) = selected_template else {
                return Ok(());
            };
            let expected_template = selected_target.clone();
            let use_type = Type::Fn(
                concrete_args.clone(),
                Box::new(self.apply_subst(state, ret_type_var)),
            );
            let Some(demand) = self.derive_mono_demand(
                state,
                selected_target.clone(),
                &template.core.scheme,
                &use_type,
                span,
            ) else {
                return Ok(());
            };
            let expected_instance = Self::demand_instance_key(&demand, &template.core.scheme)?;
            // The module-wide drain may already have minted this exact template
            // instance before a later isolated mono-body recheck reaches the
            // same call.  Consume that keyed lifecycle fact instead of trying
            // to install the identical instance twice.  This is the same exact
            // instance-key witness used by the pass-4 driver; no name scan or
            // alternate dispatch authority is introduced.
            let already_minted = self
                .current_symbol_table(state)
                .view()
                .lookup(&expected_instance)
                .and_then(Binding::callable)
                .is_some_and(|callable| {
                    matches!(
                        &callable.arm.life,
                        Life::Concrete {
                            minted_from: Some(link),
                            ..
                        } if link.template == expected_template
                    )
                });
            let instance = if already_minted {
                expected_instance
            } else {
                let template_home = match &selected_target {
                    CallableTarget::OverloadArm { owner, .. } => owner.module.clone(),
                    _ => state.current_module.clone(),
                };
                let imported_home =
                    (template_home != state.current_module).then_some(template_home);
                match self.monomorphise_call(
                    state,
                    &mangled_name,
                    &demand,
                    imported_home.as_ref(),
                    Some(base_name),
                    Some(template),
                )? {
                    Some(md) => md.defn.name.clone(),
                    None => mangled_name.clone(),
                }
            };
            // Pin the caller's deferred return var to the instance's concrete
            // return so the caller generalises over the settled type.
            let cm = state.current_module.clone();
            if let Some(callable) = self
                .probe_module_entry_owned(&cm, instance.as_ref())
                .and_then(|entry| entry.callable().cloned())
                && let Type::Fn(_, ret) = &callable.arm.scheme.ty
            {
                let ret = *ret.clone();
                self.unify(state, ret_type_var, &ret, span)?;
            }
            let resolution = ResolvedCall::SigDispatch {
                target: CallableTarget::Binding(FQSymbol {
                    module: state.current_module.clone(),
                    symbol: instance,
                }),
            };
            self.record_dispatch_target(state, span, &resolution);
            state
                .method_resolutions
                .resolved_calls
                .insert(span, resolution);
            // FIXME 0719 — retype the callee node to the MINTED INSTANCE's
            // signature (see the self-call arm above for the rationale). The
            // instance's params ARE this call's concrete args by construction.
            let inst_ret = self.apply_subst(state, ret_type_var);
            self.record_expr_type(
                state,
                callee_span,
                Type::Fn(concrete_args.clone(), Box::new(inst_ret)),
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
