use super::*;
#[cfg(test)]
use cranelisp_types::ConcreteType;
use cranelisp_types::{ApplyRef, MonoDemand, Scheme};

/// A polymorphic fn-value passed as an argument into a HOF, recorded per
/// enclosing defn for post-mint `Var` rewrite (FIXME 0374 / 0488 sig b):
/// (enclosing_defn, bare_fn_value_symbol, arg_span, concrete_param_types,
/// home_of_imported_callee).
pub(super) struct FnValueArgSite {
    enclosing: Symbol,
    arg_span: Span,
    demand: MonoDemand,
}

/// A monomorphisation call site collected by `pass4_monomorphise`:
/// (callee_name, arg_spans, call_span, home_of_imported_callee).
type MonoCallSite = MonoDemand;

/// The body expressions a mono-collect scan must walk for one `Defn`.
///
/// A single-sig defn contributes its one body; a MULTI-sig defn contributes each
/// clause variant's body (§11.8.3 leg D3 — NEVER `defn.body()`, which asserts
/// single-variant and panics on a multi-sig defn, `cranelisp-types/src/ast.rs`).
/// The `MultiSig` harvest runs post-`finalize_multi_sig_variant_types` so every
/// clause is settled concrete before its body is scanned. The base defn name is
/// the self-exclusion key in either case (a clause's own `(build …)` self-call is
/// overloaded-base dispatch handled by the drain, not a mono leaf).
fn mono_scan_bodies(defn: &Defn) -> Vec<&Expr> {
    if defn.is_multi_sig() {
        defn.variants.iter().map(|v| &v.body).collect()
    } else {
        vec![defn.body()]
    }
}

/// The settlement discipline a `resolve_auto_curry` drain runs under (S115 W4).
///
/// The auto-curry drain runs at SIX seams, and they are not equivalent: the
/// per-form body drains fire while later forms may still pin the operand type,
/// whereas the finalize drain runs post-drain/post-Phase-A on settled state.
/// Only a settled drain may conclude "this trait operator has no impl to
/// dispatch to"; a pre-settlement one must hold the entry back rather than
/// transport the trait-method DECLARATION FQ as a dispatch carrier
/// (`design/backend/s115-carrier-and-rc-sweep.md` §1.3 — the `'='` face).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AutoCurryDrain {
    /// A pre-settlement seam (per-form / per-variant body post-pass). An
    /// operator whose only available carrier is a trait-method-decl FQ is
    /// pushed to `CheckState::deferred_auto_curry` for the settled retry.
    Deferrable,
    /// A settled or recheck-scoped seam (finalize; impl-method and mono-body
    /// rechecks, whose resolution maps and module scope are swapped so nothing
    /// may be deferred out of them). No entry is held back.
    Final,
}

// --- Name mangling for multi-sig overload dispatch ---

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    pub(crate) fn checked_body_template(
        &self,
        state: &CheckState,
        bodies: &BodyLedger,
        name: &Symbol,
    ) -> Option<crate::traits::TemplateFn> {
        // Select the requested source occurrence through the ledger's exact
        // publication index. The companion snapshot below exists only so a
        // scoped mono recheck can follow a later same-cluster template hop;
        // it is not used to discover or choose the requested body.
        let selected = bodies.checked_for_publication(name)?;
        let selected_callable = self
            .current_symbol_table(state)
            .view()
            .lookup(name)
            .and_then(Binding::callable)
            .cloned()?;
        let selected_scheme = self.checked_body_scheme(state, selected.registration);
        if selected_callable.arm.scheme.ty.is_concrete()
            && selected_callable.arm.scheme.constraints.is_empty()
        {
            return None;
        }
        let core = crate::traits::TemplateCore {
            body: TemplateBody::Ast(selected.ast.clone()),
            scheme: selected_scheme,
            origin: selected_callable.origin,
        };

        let mut local_templates = HashMap::new();
        for body in bodies.checked_bodies() {
            let publication = &body.registration.publication_name;
            let Some(callable) = self
                .current_symbol_table(state)
                .view()
                .lookup(publication)
                .and_then(Binding::callable)
                .cloned()
            else {
                continue;
            };
            let scheme = self.checked_body_scheme(state, body.registration);
            if callable.arm.scheme.ty.is_concrete() && callable.arm.scheme.constraints.is_empty() {
                continue;
            }
            local_templates.insert(
                publication.clone(),
                crate::traits::TemplateCore {
                    body: TemplateBody::Ast(body.ast.clone()),
                    scheme,
                    origin: callable.origin,
                },
            );
        }
        Some(crate::traits::TemplateFn {
            core,
            local_templates,
            template_target: Some(CallableTarget::Binding(FQSymbol {
                module: state.current_module.clone(),
                symbol: name.clone(),
            })),
        })
    }

    /// Rebuild a checked body's scheme from the ledger-owned monotypes and the
    /// current settlement substitution. A symbol-table declaration may still
    /// carry its pre-drain generalized scheme; instantiating that snapshot would
    /// sever return/parameter refinements made by overload back-flow.
    fn checked_body_scheme(&self, state: &CheckState, body: &RegisteredBody) -> Scheme {
        let fn_type = Type::Fn(
            body.param_types
                .iter()
                .map(|ty| apply(&state.subst, ty))
                .collect(),
            Box::new(apply(&state.subst, &body.ret_ty)),
        );
        self.generalize(state, &fn_type)
    }

    fn mono_demand(
        &self,
        state: &CheckState,
        template: FQSymbol,
        use_type: Type,
        site: Span,
        bodies: &BodyLedger,
    ) -> Option<MonoDemand> {
        let local = (template.module == state.current_module)
            .then(|| self.checked_body_template(state, bodies, &template.symbol))
            .flatten();
        let scheme = if let Some(local) = local {
            local.core.scheme
        } else {
            self.probe_module_entry_owned(&template.module, template.symbol.as_ref())?
                .callable()?
                .arm
                .scheme
                .clone()
        };
        self.derive_mono_demand(
            state,
            CallableTarget::Binding(template),
            &scheme,
            &use_type,
            site,
        )
    }

    fn mono_demand_from_spans(
        &self,
        state: &CheckState,
        template: FQSymbol,
        arg_spans: &[Span],
        site: Span,
        bodies: &BodyLedger,
    ) -> Option<MonoDemand> {
        let use_type = Self::mono_call_type(
            state,
            &state.expr_types,
            &state.method_resolutions,
            arg_spans,
            site,
        )?;
        self.mono_demand(state, template, use_type, site, bodies)
    }

    pub(crate) fn mono_call_type(
        state: &CheckState,
        types: &HashMap<Span, Type>,
        resolutions: &cranelisp_types::MethodResolutions,
        arg_spans: &[Span],
        site: Span,
    ) -> Option<Type> {
        let mut params = arg_spans
            .iter()
            .map(|span| types.get(span).map(|ty| apply(&state.subst, ty)))
            .collect::<Option<Vec<_>>>()?;
        let mut result = apply(&state.subst, types.get(&site)?);
        if matches!(
            resolutions.resolved_calls.get(&site),
            Some(ResolvedCall::AutoCurry { .. })
        ) {
            let Type::Fn(remaining, ret) = result else {
                return None;
            };
            params.extend(remaining);
            result = *ret;
        }
        Some(Type::Fn(params, Box::new(result)))
    }

    fn record_mono_dispatch(&self, state: &mut CheckState, span: Span, mangled: JitSymbol) {
        if span == Span::SYNTHETIC {
            return;
        }
        let resolution = match state.method_resolutions.resolved_calls.get(&span).cloned() {
            Some(ResolvedCall::AutoCurry {
                applied_count,
                total_count,
                trait_resolution,
                ..
            }) => {
                state.method_resolutions.apply_refs.insert(
                    span,
                    ApplyRef::Dispatch(FQSymbol {
                        module: state.current_module.clone(),
                        symbol: Symbol::from(mangled.as_ref()),
                    }),
                );
                ResolvedCall::AutoCurry {
                    target_name: Symbol::from(mangled.as_ref()),
                    applied_count,
                    total_count,
                    trait_resolution,
                }
            }
            _ => {
                let resolution = ResolvedCall::SigDispatch {
                    target: CallableTarget::Binding(FQSymbol {
                        module: state.current_module.clone(),
                        symbol: Symbol::from(mangled.as_ref()),
                    }),
                };
                self.record_dispatch_target(state, span, &resolution);
                resolution
            }
        };
        state
            .method_resolutions
            .resolved_calls
            .insert(span, resolution);
    }

    /// Seed the existing pass-4 driver from reload-captured typed demands.
    /// This is deliberately a caller of `drive_call_site_monomorphisation`,
    /// never a second caller of the mint core.
    pub(crate) fn instantiate_demand_roots(
        &self,
        state: &mut CheckState,
        demands: Vec<MonoDemand>,
    ) -> Result<CheckResult, CranelispError> {
        let mut warnings = Vec::new();
        let mut seen = HashMap::new();
        let mut mono_defns = Vec::new();
        let no_local_bodies = BodyLedger::default();

        for demand in demands {
            let Some(owner) = callable_target_owner(&demand.template) else {
                continue;
            };
            let template_present = self
                .probe_module_entry_owned(&owner.module, owner.symbol.as_ref())
                .is_some_and(|binding| match &demand.template {
                    CallableTarget::Binding(_) => binding.callable().is_some_and(|callable| {
                        matches!(callable.arm.life, Life::Template { .. })
                    }),
                    CallableTarget::OverloadArm { arm, .. } => {
                        matches!(&binding.declaration, Decl::Overloaded(declaration)
                            if declaration.arms.get(arm.ordinal()).is_some_and(|candidate|
                                candidate.id == *arm && matches!(candidate.callable.life, Life::Template { .. })))
                    }
                    CallableTarget::MacroClause { .. } => false,
                    _ => false,
                });
            if !template_present {
                warnings.push(cranelisp_types::Warning {
                    kind: cranelisp_types::WarningKind::Other,
                    message: format!(
                        "declined stale monomorphisation demand for {:?} at ({})",
                        demand.template,
                        demand
                            .type_args
                            .iter()
                            .map(|arg| arg.to_type().to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    span: Span::SYNTHETIC,
                });
                continue;
            }

            let drive = self.drive_call_site_monomorphisation(
                state,
                std::slice::from_ref(&demand),
                &mut seen,
                &mut mono_defns,
                &no_local_bodies,
            );
            match drive {
                Ok(()) => {}
                Err(CranelispError::TypeError { message, location })
                    if location.span == Span::SYNTHETIC =>
                {
                    warnings.push(cranelisp_types::Warning {
                        kind: cranelisp_types::WarningKind::Other,
                        message: format!(
                            "declined stale monomorphisation demand for {:?} at ({}): {message}",
                            demand.template,
                            demand
                                .type_args
                                .iter()
                                .map(|arg| arg.to_type().to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                        span: Span::SYNTHETIC,
                    });
                }
                Err(error) => return Err(error),
            }
        }

        Ok(CheckResult {
            warnings,
            display: None,
            unresolved_dispatch: Vec::new(),
        })
    }

    /// Monomorphise every reachable polymorphic / constrained call site into
    /// concrete instances.
    ///
    /// Returns the `Vec<MonoDefn>` (each carrying a `Defn` body the backend
    /// still reads pre-Phase-3). S84 Phase-3 (FIXME 0392): the concrete-boundary
    /// `MonoExpr` view of every instance is now set ON the instance's
    /// `ModuleEntry::Def.codegen_view` at `register_mono_entry` (the single
    /// source of truth, Principle 7) — the transitional parallel
    /// `CheckState.mono_variants` `Vec` that carried it is retired. The
    /// `MonoExpr::from_expr` validation (a residual `Var` in any instance
    /// surfaces as a §3.11.1 could-not-monomorphise error) runs at the
    /// `monomorphise_call` seam, unchanged.
    pub(super) fn pass4_monomorphise(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
        constrained_fn_names: &HashSet<Symbol>,
        bodies: &mut BodyLedger,
    ) -> Result<Vec<MonoDefn>, CranelispError> {
        let (call_sites, fn_value_arg_sites) =
            self.collect_mono_call_sites(state, defns, constrained_fn_names, bodies);

        // Nothing to monomorphise (neither local constrained fns nor imported
        // constrained call sites nor polymorphic fn-value arguments) — bail
        // before resolving expr_types.
        if call_sites.is_empty() && fn_value_arg_sites.is_empty() {
            return Ok(Vec::new());
        }

        // Monomorphise each call site and record dispatch mappings
        let mut mono_defns = Vec::new();
        let mut seen: HashMap<Symbol, JitSymbol> = HashMap::new();
        // The caller's module — the fallback home for a LOCAL generic's mono
        // name. `monomorphise_call` restores `state.current_module` per call, so
        // capturing once here is stable across the loop (FIXME 0519).
        let current_module = state.current_module.clone();

        self.drive_call_site_monomorphisation(
            state,
            &call_sites,
            &mut seen,
            &mut mono_defns,
            bodies,
        )?;

        let fn_value_rewrites = self.drive_fn_value_monomorphisation(
            state,
            &fn_value_arg_sites,
            &mut seen,
            &mut mono_defns,
            bodies,
        )?;

        // Apply the fn-value `Var` renames to the stored ASTs. A later
        // re-annotation pass (in `finalize_check_result_inner`) only writes
        // `inferred_type` / `resolved_call` by span — it does not touch the
        // `Var` name — so this rename survives.
        if !fn_value_rewrites.is_empty() {
            for (enclosing, arg_span, mangled_sym) in &fn_value_rewrites {
                if let Some(body) = bodies.checked_mut_for_publication(enclosing) {
                    rename_var_at_span(&mut body.ast.body, *arg_span, mangled_sym);
                    body.callees.push(FQSymbol {
                        module: current_module.clone(),
                        symbol: mangled_sym.clone(),
                    });
                    body.callees.sort_by(|a, b| {
                        a.module
                            .as_ref()
                            .cmp(b.module.as_ref())
                            .then(a.symbol.as_ref().cmp(b.symbol.as_ref()))
                    });
                    body.callees.dedup();
                }
            }
            // S110 W0.1b (§1.1.1, fn-value mono-rewrite carrier): the rename
            // repoints the arg-position `Var` at the caller-local mangled mono,
            // but the span-keyed carrier still names the slot-less template (or
            // is absent). Update the sidecar to the minted instance's STORAGE
            // identity — the caller's module (`register_mono_entry` registers
            // the mono in `current_module`, even for an imported generic whose
            // mangle embeds its home). Without this, the W2 0585 keyed read
            // would hard-fail this VALID program on the stale template carrier.
            for (_enclosing, arg_span, mangled_sym) in &fn_value_rewrites {
                // Arg-position fn-value `Var` → the minted instance's storage FQ
                // (a table reference: `VarRef::Global`). S114 carrier flip.
                state.method_resolutions.var_refs.insert(
                    *arg_span,
                    cranelisp_types::VarRef::Global(FQSymbol {
                        module: current_module.clone(),
                        symbol: mangled_sym.clone(),
                    }),
                );
            }
        }

        // S84 Phase-3 (FIXME 0392): the concrete-boundary `MonoExpr` view of
        // each minted instance is now set ON its `ModuleEntry::Def.codegen_view`
        // at `register_mono_entry` — no parallel `Vec` to drain.
        Ok(mono_defns)
    }

    /// Collect the Pass-4 monomorphisation work list from every defn body
    /// (`program-decomposition.md` §2.2): local constrained calls, imported
    /// constrained/parametric calls, local pure-parametric hops, and
    /// polymorphic fn-value arguments. Returns `(call_sites, fn_value_arg_sites)`.
    pub(super) fn collect_mono_call_sites(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
        constrained_fn_names: &HashSet<Symbol>,
        bodies: &BodyLedger,
    ) -> (Vec<MonoCallSite>, Vec<FnValueArgSite>) {
        // Same-cluster checked bodies intentionally remain `Life::Declared`
        // until final publication. Derive the local template trigger set from
        // the exact ledger records; committed/imported templates continue to be
        // recognized from their settled table lifecycle.
        let local_template_names: HashSet<Symbol> = bodies
            .checked_bodies()
            .filter_map(|body| {
                let name = &body.registration.publication_name;
                let is_template = self
                    .current_symbol_table(state)
                    .view()
                    .lookup(name)
                    .and_then(Binding::callable)
                    .is_some_and(|callable| {
                        !callable.arm.scheme.ty.is_concrete()
                            || !callable.arm.scheme.constraints.is_empty()
                    });
                (name.as_ref() != "__expr" && is_template).then(|| name.clone())
            })
            .collect();
        // Collect call sites: (fn_name, arg_spans, call_span, home_module).
        //
        // `home_module` is `None` for a call to a LOCALLY-defined constrained fn
        // (`monomorphise_call` re-checks its body in the current module's scope,
        // the as-built path). It is `Some(home)` for a call to an IMPORTED
        // constrained fn that chain-resolves to a constrained `Def` in another
        // module — the mono body must be re-checked in that DEFINING module's
        // import context, where its trait-method + helper references resolve
        // (FIXME 0355; the feature half of the resolved 0354 SIGSEGV).
        //
        // FIXME 0349 — scan EVERY defn body, including those that are themselves
        // in `constrained_fn_names`. A constrained/polymorphic defn can still
        // host a *concrete* call to another constrained fn that needs a mono
        // variant. Under forward-reference ordering a caller (`main`) can stay
        // spuriously polymorphic (its result var never pinned because the callee
        // it forward-references was generalized before the helper that ties its
        // accumulator) and thus land in `constrained_fn_names`; skipping its body
        // wholesale meant the `(reduce add-i64 0 [1 2 3])` call site was never
        // collected and `reduce$Int+Vec` was never created — so `main` called the
        // polymorphic template and returned the initial accumulator (0344/0349).
        // We must NOT skip such bodies; we only skip a call from a fn to ITSELF
        // (the generic self-recursion of a constrained defn is not a concrete
        // call site — its arg types are the defn's own generic vars).
        let mut local_calls = Vec::new();
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                Self::collect_constrained_calls_excluding_self(
                    body,
                    &defn.name,
                    constrained_fn_names,
                    &state.method_resolutions.var_refs,
                    &mut local_calls,
                );
            }
        }
        let mut call_sites: Vec<MonoCallSite> = local_calls
            .into_iter()
            .filter_map(|(name, spans, span)| {
                let resolved = self.resolve_terminal_fq_scoped(state, name.as_ref())?;
                self.mono_demand_from_spans(state, resolved.canonical, &spans, span, bodies)
            })
            .collect();

        // FIXME 0355 — collect call sites for IMPORTED callees that
        // chain-resolve to a constrained (or pure-parametric) `Def` in another
        // module. These are NOT in `constrained_fn_names` (their local name is a
        // `ModuleEntry::Import`), so the local collection above never sees them.
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                self.collect_imported_constrained_calls(
                    state,
                    body,
                    constrained_fn_names,
                    &mut call_sites,
                    bodies,
                );
            }
        }

        // FIXME 0373 (Tier 1, /arch ruling (A) — monomorphise polymorphic-result
        // hops) — collect call sites for LOCAL (same-module) pure-parametric
        // polymorphic callees. These are NOT in `constrained_fn_names` (that set
        // holds only trait-constrained fns — `detect_constrained_fns` keys on
        // `Life::Template { kind: TemplateKind::Constrained(..) }`), and they
        // live in the current module so the
        // imported-call pass above (which requires `home != current_module`)
        // skips them too. Yet a hop like `(defn h1 [f] (h2 f))` whose RESULT type
        // generalizes to an unbound `Type::Var` is compiled ONCE generically
        // (program.rs §919 "generalize-and-keep-a-single-generic Concrete slot"),
        // leaving its result `Type::Var` at codegen. The backend's RC classifier
        // (`HeapCategory::classify(Type::Var) -> Mixed`) then emits a guarded
        // RC-inc whose `< 1024` immediate-vs-pointer heuristic mis-reads a
        // negative / large Int result as a heap pointer and dereferences it →
        // SIGSEGV (FIXME 0373 root-cause). Monomorphising the hop at the concrete
        // instantiation reached from its call site gives the mono instance a
        // CONCRETE result type (`Int`) → `classify` sees `NeverHeap` → no guard →
        // no crash. This reuses the same 0355 collection + `monomorphise_call` +
        // caller-GOT-slot mechanism, widening the trigger from "constrained /
        // imported callee" to "polymorphic-result hop reached at a concrete type".
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                self.collect_local_parametric_calls(
                    state,
                    body,
                    &defn.name,
                    constrained_fn_names,
                    &local_template_names,
                    &mut call_sites,
                    bodies,
                );
            }
        }

        // F2: a trait-dispatched apply can resolve directly to a generic impl
        // method template.  It is not an Apply-of-bare-Var, so widen successor
        // discovery explicitly while feeding the same typed worklist.
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                self.collect_dispatch_template_calls(state, body, &mut call_sites, bodies);
            }
        }

        // FIXME 0374 (Tier 2 — the `(Box a)`-field-through-HOF gap). Collect
        // bare-`Var` ARGUMENTS that pass a monomorphisable polymorphic fn as a
        // VALUE into a higher-order call. These are not callees (so the
        // call-site collectors above miss them) but they still need a concrete
        // mono instance — see `collect_parametric_fn_value_args`. Recorded
        // per enclosing defn so the fn-value `Var` can be rewritten to the
        // mangled name in that defn's stored AST after minting.
        let mut fn_value_arg_sites: Vec<FnValueArgSite> = Vec::new();
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                let mut sites = Vec::new();
                self.collect_parametric_fn_value_args(
                    state,
                    body,
                    &local_template_names,
                    &mut sites,
                );
                for (template, arg_span, param_types) in sites {
                    if let Some(demand) =
                        self.mono_demand(state, template, param_types, arg_span, bodies)
                    {
                        fn_value_arg_sites.push(FnValueArgSite {
                            enclosing: defn.name.clone(),
                            arg_span,
                            demand,
                        });
                    }
                }
            }
        }

        (call_sites, fn_value_arg_sites)
    }

    /// Drive monomorphisation over the collected call sites
    /// (`program-decomposition.md` §2.2): re-derive each site's concrete arg
    /// types from the final `resolved_expr_types`, dedup by the canonical
    /// mangled name, mint the mono instance via `monomorphise_call`, and record
    /// the `SigDispatch`. Threads `seen` / `mono_defns` shared with the fn-value
    /// pass.
    pub(super) fn drive_call_site_monomorphisation(
        &self,
        state: &mut CheckState,
        call_sites: &[MonoCallSite],
        seen: &mut HashMap<Symbol, JitSymbol>,
        mono_defns: &mut Vec<MonoDefn>,
        bodies: &BodyLedger,
    ) -> Result<(), CranelispError> {
        for demand in call_sites {
            let Some(owner) = callable_target_owner(&demand.template) else {
                continue;
            };
            let fn_name = &owner.symbol;
            let call_span = demand.site;
            let home_module = &owner.module;

            let selected_template = match &demand.template {
                CallableTarget::OverloadArm { .. } => {
                    self.owned_overload_template(&demand.template)
                }
                _ => (home_module == &state.current_module)
                    .then(|| self.checked_body_template(state, bodies, fn_name))
                    .flatten()
                    .or_else(|| self.get_constrained_fn(state, fn_name, Some(home_module))),
            };
            let Some(selected_template) = selected_template else {
                continue;
            };

            // Deduplicate by the selected template's complete concrete function
            // signature. Route the key through the canonical identity helper so
            // the dedup grain equals the minted-name grain (FIXME 0519): a
            // home-blind key collapsed same-named imported generics, while an
            // argument-only key collapses result-context and legal arity choices.
            let instance_key = Self::demand_instance_key(demand, &selected_template.core.scheme)?;
            let key = instance_key.clone();

            // The finalize pipeline has three intentional pass-4 windows. An
            // earlier window may already have settled this typed instance; the
            // lifecycle funnel correctly refuses a second install, so treat the
            // existing concrete instance as the cross-window dedup witness.
            if self
                .current_symbol_table(state)
                .view()
                .lookup(&instance_key)
                .and_then(Binding::callable)
                .is_some_and(|callable| matches!(callable.arm.life, Life::Concrete { .. }))
            {
                let mangled = JitSymbol::from(key.as_ref());
                self.record_mono_dispatch(state, call_span, mangled.clone());
                seen.insert(key, mangled);
                continue;
            }

            if let Some(mangled) = seen.get(&key) {
                // Already generated this specialization — just record dispatch
                self.record_mono_dispatch(state, call_span, mangled.clone());
                continue;
            }

            if let Some(mono) = self.monomorphise_call(
                state,
                fn_name,
                demand,
                Some(home_module),
                None,
                Some(selected_template),
            )? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                // Record dispatch for this call site
                self.record_mono_dispatch(state, call_span, mangled.clone());
                seen.insert(key, mangled);
                mono_defns.push(mono);
            }
        }

        Ok(())
    }

    /// Drive monomorphisation of polymorphic fn-value arguments
    /// (`program-decomposition.md` §2.2, FIXME 0374 Tier 2): mint each site's
    /// concrete mono instance and collect the `(enclosing, arg_span, mangled)`
    /// rewrites the driver applies to the stored ASTs. Shares `seen` /
    /// `mono_defns` with the call-site pass.
    pub(super) fn drive_fn_value_monomorphisation(
        &self,
        state: &mut CheckState,
        fn_value_arg_sites: &[FnValueArgSite],
        seen: &mut HashMap<Symbol, JitSymbol>,
        mono_defns: &mut Vec<MonoDefn>,
        bodies: &BodyLedger,
    ) -> Result<Vec<(Symbol, Span, Symbol)>, CranelispError> {
        // FIXME 0374 (Tier 2 — fn-value-argument monomorphisation). For each
        // polymorphic fn passed as a value into a HOF, mint its concrete mono
        // instance (`mk$Int`) and rewrite the fn-value `Var` in the enclosing
        // defn's stored AST to the mangled name, so the backend's
        // `compile_fn_as_value` takes the concrete (slotted) instance's GOT slot
        // rather than the slot-less `Polymorphic` template. The mono instance's
        // body re-checks at the concrete param types, so its `(Box a)` field
        // becomes `(Box Int)` — concrete, classifying cleanly, no RC guard.
        let mut fn_value_rewrites: Vec<(Symbol, Span, Symbol)> = Vec::new();
        for site in fn_value_arg_sites {
            let enclosing = &site.enclosing;
            let arg_span = site.arg_span;
            let Some(owner) = callable_target_owner(&site.demand.template) else {
                continue;
            };
            let arg_name = &owner.symbol;
            let selected_template = match &site.demand.template {
                CallableTarget::OverloadArm { .. } => {
                    self.owned_overload_template(&site.demand.template)
                }
                _ => (owner.module == state.current_module)
                    .then(|| self.checked_body_template(state, bodies, arg_name))
                    .flatten()
                    .or_else(|| self.get_constrained_fn(state, arg_name, Some(&owner.module))),
            };
            let Some(selected_template) = selected_template else {
                continue;
            };
            // The selected template's complete concrete signature supplies the
            // dedup key and minted name (FIXME 0519), including the imported
            // home for an imported generic fn-value (FIXME 0488 sig b).
            let instance_key =
                Self::demand_instance_key(&site.demand, &selected_template.core.scheme)?;
            let key = instance_key.clone();
            let mangled_sym = if self
                .current_symbol_table(state)
                .view()
                .lookup(&instance_key)
                .and_then(Binding::callable)
                .is_some_and(|callable| matches!(callable.arm.life, Life::Concrete { .. }))
            {
                let existing = JitSymbol::from(key.as_ref());
                seen.insert(key.clone(), existing.clone());
                Symbol::from(existing.as_ref())
            } else if let Some(existing) = seen.get(&key) {
                Symbol::from(existing.as_ref())
            } else if let Some(mono) = self.monomorphise_call(
                state,
                arg_name,
                &site.demand,
                Some(&owner.module),
                None,
                Some(selected_template),
            )? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                seen.insert(key, mangled.clone());
                let sym = Symbol::from(mangled.as_ref());
                mono_defns.push(mono);
                sym
            } else {
                continue;
            };
            fn_value_rewrites.push((enclosing.clone(), arg_span, mangled_sym));
        }

        Ok(fn_value_rewrites)
    }

    /// Walk a defn body collecting calls to IMPORTED callees that chain-resolve
    /// to a constrained (trait-bound) or pure-parametric polymorphic `Def` in
    /// another module (FIXME 0355).
    ///
    /// A locally-defined constrained fn is named in `constrained_fn_names` and is
    /// already collected by [`Self::collect_constrained_calls_excluding_self`];
    /// here we skip those and look only at bare `Var` callees whose local name
    /// chain-resolves (via [`Self::resolve_terminal_entry_and_home`]) to a
    /// terminal in a DIFFERENT module. When that terminal is a constrained or
    /// still-polymorphic `UserFn` `Def`, the call needs a cross-module mono
    /// variant re-checked in the terminal's HOME scope, so we record the call
    /// site with `Some(home)`.
    pub(super) fn collect_imported_constrained_calls(
        &self,
        state: &CheckState,
        expr: &Expr,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<MonoDemand>,
        bodies: &BodyLedger,
    ) {
        // DEF-1 (S86): resolve the bare callee through the **prelude-fallback**
        // scope resolve (`resolve_terminal_fq_scoped`), NOT the
        // current-module-only `resolve_terminal_entry_and_home`. A polymorphic fn
        // provided ONLY via the implicit prelude (an implicit `(import [prelude
        // [*]])`, no explicit import) is invisible to a current-module-rooted
        // lookup, so its concrete mono was never minted in the consuming module →
        // codegen `undefined function`. The fallback-aware resolver applies the
        // same I-1 public-only filter the value/type/ctor/trait chokepoints use,
        // and reports the terminal `home` (the prelude — `!= current_module`), so
        // the cross-module mono path fires exactly as it does for the
        // explicit-import control (S78 prelude-fallback discipline; the
        // mono-collection chokepoint had been missed).
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            // FIXME 0653 — skip a §4.6 LOCAL shadow (see collect_local_parametric_calls).
            && callee_has_keyed_carrier(&state.method_resolutions.var_refs, callee.span())
            && !constrained_fn_names.contains(name)
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && resolved.canonical.module != state.current_module
            && Self::entry_is_monomorphisable_polymorphic(&resolved.entry)
        {
            // FIXME 0488 sig a (cross-module FQ): record the canonical terminal
            // (`resolved.canonical`), not the raw reference `name` — a qualified
            // callee (`gen/iden2`) would otherwise reach `get_constrained_fn`'s
            // home-probe as a `/`-bearing key in the home module → no mint. The
            // resolver already split `mod/sym` and resolved the module alias.
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            if let Some(demand) =
                self.mono_demand_from_spans(state, resolved.canonical, &arg_spans, *span, bodies)
            {
                out.push(demand);
            }
        }
        for_each_child_expr(expr, |child| {
            self.collect_imported_constrained_calls(state, child, constrained_fn_names, out, bodies)
        });
    }

    /// Whether a call site to a LOCAL polymorphic callee should be collected for
    /// monomorphisation. ONE predicate: **every argument is fully concrete**
    /// (Phase-4 part A, Option 1, concrete-boundary-type.md §4-A — collapsing the
    /// former two triggers).
    ///
    /// A mono instance is minted **iff every argument type is concrete**; its
    /// result is then concrete by the per-instance re-check (the body re-check +
    /// `unify(body_ty, ret_ty)` pins the result). This subsumes BOTH the old
    /// 0373 result-hop trigger (`result_is_bare_var`) and the 0374
    /// direct-concrete-call trigger:
    ///
    /// - **Genuine result hops (0373) are still minted** — a result-bare-var hop
    ///   whose ARGS are concrete (`(g 1)`, `(h2 x)` with `x: Int`) passes this
    ///   predicate; the body re-check pins the result. The genuine concrete
    ///   result-hop arrives here through the parent's concrete re-check chain
    ///   with every arg already pinned.
    /// - **Direct concrete calls (0374)** — `(g 1)` with `g : ∀a. a→a` passes:
    ///   all args concrete, so the `g$Int` instance is minted (`g` is slot-less
    ///   under the structural slot gate; an un-monomorphised call would lower
    ///   through a missing slot).
    /// - **The SPURIOUS partial result-hop is EXCLUDED** — a result-bare-var hop
    ///   whose args are still the parent's free scheme vars (the `reduce →
    ///   reduce-loop` 0344 fold inner call, where `f`/`acc`/element are
    ///   `reduce`'s OWN `Var34`/`Var31`) fails the all-args-concrete predicate,
    ///   so no partial `reduce-loop$Vec+Int+Int` is minted. The genuine concrete
    ///   `reduce-loop$Int+Vec+Int+Int` is minted via the concrete `reduce$Int+Vec`
    ///   chain (where the args ARE pinned), unaffected.
    ///
    /// **The 0344 fold is preserved by the all-args-concrete guard.** The fold
    /// call `(reduce vec-push [] vv)` has args `vec-push` (a polymorphic
    /// fn-VALUE), `[]` (`(Vec a)`), `vv` — NOT all concrete — so it is excluded.
    /// Monomorphising it would pin `reduce`'s accumulator var through the
    /// post-mono regeneralisation, re-collapsing the polymorphic scheme 0344
    /// deliberately keeps; the all-concrete guard keeps it out.
    ///
    /// An empty-arg call does NOT trigger (a nullary polymorphic call cannot be
    /// pinned by its args — if its result is concrete it needs no mono; if its
    /// result is a free var it is the ambiguity case, §2.6, not a mono site).
    pub(super) fn local_parametric_call_triggers(
        state: &CheckState,
        _call_span: &Span,
        args: &[Expr],
    ) -> bool {
        args.iter().all(|a| {
            state
                .expr_types
                .get(&a.span())
                .map(|ty| apply(&state.subst, ty).is_concrete())
                .unwrap_or(false)
        })
    }

    /// Collect F2 calls whose typed dispatch carrier points at a checked AST
    /// template. Trait dispatch is not syntactically an Apply-of-bare-Var, so
    /// it joins the same demand worklist through this carrier-driven widening.
    fn collect_dispatch_template_calls(
        &self,
        state: &CheckState,
        expr: &Expr,
        out: &mut Vec<MonoDemand>,
        bodies: &BodyLedger,
    ) {
        if let Expr::Apply { args, span, .. } = expr
            && Self::local_parametric_call_triggers(state, span, args)
            && let Some(ApplyRef::Dispatch(template)) =
                state.method_resolutions.apply_refs.get(span)
            && let Some(binding) =
                self.probe_module_entry_owned(&template.module, template.symbol.as_ref())
            && binding.callable().is_some_and(|callable| {
                matches!(
                    callable.arm.life,
                    Life::Template {
                        body: TemplateBody::Ast(_),
                        ..
                    }
                )
            })
        {
            let arg_spans: Vec<Span> = args.iter().map(Expr::span).collect();
            if let Some(demand) =
                self.mono_demand_from_spans(state, template.clone(), &arg_spans, *span, bodies)
            {
                out.push(demand);
            }
        }
        for_each_child_expr(expr, |child| {
            self.collect_dispatch_template_calls(state, child, out, bodies)
        });
    }

    /// Walk a defn body collecting calls to LOCAL (same-module) pure-parametric
    /// polymorphic callees that need a concrete monomorphisation (FIXME 0373,
    /// Tier 1 — the polymorphic-result-hop fix; /arch ruling (A)).
    ///
    /// Mirrors [`Self::collect_imported_constrained_calls`] for the *local* case:
    /// a trait-constrained local fn is already in `constrained_fn_names` and is
    /// collected by [`Self::collect_constrained_calls_excluding_self`]; here we
    /// pick up bare `Var` callees whose local name resolves (chain-follow) to a
    /// terminal in the SAME module that is a pure-parametric polymorphic `UserFn`
    /// `Def` (the `entry_is_monomorphisable_polymorphic` shape, excluding the
    /// already-collected constrained set). The call site is recorded with
    /// `home: None` (the same-module `monomorphise_call` path — recheck the body
    /// in the current module's scope). A call from a fn to ITSELF is skipped:
    /// generic self-recursion is the defn's own generic vars, not a concrete site.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn collect_local_parametric_calls(
        &self,
        state: &CheckState,
        expr: &Expr,
        self_name: &Symbol,
        constrained_fn_names: &HashSet<Symbol>,
        local_template_names: &HashSet<Symbol>,
        out: &mut Vec<MonoDemand>,
        bodies: &BodyLedger,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && name != self_name
            // FIXME 0653 — skip a §4.6 LOCAL shadow: a callee whose `var_refs`
            // verdict is `VarRef::Local` (S114 carrier flip — was "no keyed
            // `resolved_targets` carrier") resolved to a let/fn/param binding
            // (the shadow gate declined a table target), NOT the top-level
            // parametric fn the name-scan would mint. The name is a trigger, not
            // the identity; `callee_has_keyed_carrier` returns TRUE only for a
            // `VarRef::Global` verdict.
            && callee_has_keyed_carrier(&state.method_resolutions.var_refs, callee.span())
            && !constrained_fn_names.contains(name)
            && Self::local_parametric_call_triggers(state, span, args)
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && resolved.canonical.module == state.current_module
            && (local_template_names.contains(&resolved.canonical.symbol)
                || Self::entry_is_monomorphisable_polymorphic(&resolved.entry))
        {
            // FIXME 0488 sig a (same-module FQ): resolve via the `/`-splitting
            // fallback resolver (the raw `resolve_terminal_entry_and_home` probe
            // keyed the qualified `test/iden` string and missed) and record the
            // BARE terminal symbol so `(test/iden 5)` mints/dispatches under the
            // same `iden$Int` name as the bare call. A cross-module qualifier
            // resolves with `home != current` and is left to the imported
            // collector; a prelude fn likewise (home == prelude != current).
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            if let Some(demand) =
                self.mono_demand_from_spans(state, resolved.canonical, &arg_spans, *span, bodies)
            {
                out.push(demand);
            }
        }
        for_each_child_expr(expr, |child| {
            self.collect_local_parametric_calls(
                state,
                child,
                self_name,
                constrained_fn_names,
                local_template_names,
                out,
                bodies,
            )
        });
    }

    /// Walk a defn body collecting bare-`Var` ARGUMENTS that pass a
    /// monomorphisable polymorphic fn as a *value* into a higher-order call
    /// (FIXME 0374 — the `(Box a)`-field-carrying-`Type::Var`-through-HOF gap).
    ///
    /// The result-hop collectors ([`Self::collect_local_parametric_calls`] +
    /// [`Self::monomorphise_inner_parametric_hops`]) trigger on a bare-`Var`
    /// *call result* or an `Apply`-of-bare-`Var`. They do NOT cover a polymorphic
    /// fn passed as an argument value (`(thru mk x)` — `mk` is a fn-value
    /// argument, never a callee here, and the HOF call's result `(Box Int)` is
    /// concrete so the result-var gate skips it). That fn-value still needs a
    /// concrete mono instance: `mk`'s body constructs `(Box a)` with a `Type::Var`
    /// field that reaches the RC boundary as a non-concrete `Box` field →
    /// `classify(Type::Var)` → the unsound `<1024` guard → SIGSEGV.
    ///
    /// For each `Apply` whose bare-`Var` argument resolves (chain-follow) to a
    /// LOCAL monomorphisable polymorphic def AND whose resolved expr-type at the
    /// argument span is a FULLY CONCRETE `(Fn [..] ..)`, record
    /// `(arg_var_name, arg_span, concrete_param_types)`. The caller mints
    /// `arg_var$T..` and rewrites the fn-value `Var` in the enclosing defn's
    /// stored AST to the mangled name so the backend takes the concrete mono
    /// instance's GOT slot.
    pub(super) fn collect_parametric_fn_value_args(
        &self,
        state: &CheckState,
        expr: &Expr,
        local_template_names: &HashSet<Symbol>,
        out: &mut Vec<(FQSymbol, Span, Type)>,
    ) {
        // A generic fn referenced in VALUE position at a concrete `Fn` type
        // (FIXME 0374 fn-value monomorphisation; 0571 D1 extension; 0585 —
        // position-completeness cure). A value-position generic fn-value ref
        // reaches the backend slot-less unless monomorphised here ⇒ the
        // `undefined variable` codegen leak (0571 D1).
        //
        // **POSITION-COMPLETE (0585, mirroring `find_ambiguous_value_position`).**
        // The verdict must fire on EVERY codegen-reaching value position, not a
        // hand-picked whitelist. The old shape only visited `Apply { args }` and
        // `Let`/`ParBind` binding values, so a generic fn-value in an `if`
        // branch, a `match` arm body, a `VecLit` element, a ctor field, or a
        // `let` tail body slipped past collection and reached codegen slot-less.
        // `for_each_child_expr` is the single child-enumeration source of truth;
        // its children ARE the value positions. Only the `Apply` CALLEE is a
        // DISPATCH position (not a runtime value) — it mints through the ordinary
        // call-site path, so we recurse INTO it but never collect it as a
        // fn-value. `try_collect_parametric_fn_value` self-guards on
        // `Expr::Var`, so applying it to a non-`Var` child is a no-op.
        let callee_span = match expr {
            Expr::Apply { callee, .. } => Some(callee.span()),
            _ => None,
        };
        for_each_child_expr(expr, |child| {
            if Some(child.span()) != callee_span {
                self.try_collect_parametric_fn_value(state, child, local_template_names, out);
            }
            self.collect_parametric_fn_value_args(state, child, local_template_names, out);
        });
    }

    /// The per-`Var` fn-value monomorphisation collect (FIXME 0374 / 0488 sig b /
    /// 0571 D1) — records `(bare_symbol, ref_span, param_types, home)` for a
    /// value-position `Var` that resolves to a monomorphisable polymorphic fn
    /// whose full `Fn` signature is concrete at this reference. Shared by the HOF
    /// argument and let-binding value sites.
    pub(super) fn try_collect_parametric_fn_value(
        &self,
        state: &CheckState,
        var_expr: &Expr,
        local_template_names: &HashSet<Symbol>,
        out: &mut Vec<(FQSymbol, Span, Type)>,
    ) {
        if let Expr::Var { name, span, .. } = var_expr
            && let Some(ty) = state.expr_types.get(span)
            && let Type::Fn(param_types, ret_ty) = apply(&state.subst, ty)
            // The fn-value's full signature must be concrete — the instantiation
            // the use demands, and the shape that pins any residual ADT-field
            // `Type::Var`.
            && param_types.iter().all(|p| p.is_concrete())
            && ret_ty.is_concrete()
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && (local_template_names.contains(&resolved.canonical.symbol)
                || Self::entry_is_monomorphisable_polymorphic(&resolved.entry))
        {
            out.push((resolved.canonical, *span, Type::Fn(param_types, ret_ty)));
        }
    }

    /// Does this terminal entry need a monomorphised specialisation when called
    /// with concrete arg types? (FIXME 0355 — mirrors `get_constrained_fn`'s two
    /// accepted shapes: a trait-constrained `UserFn`, or a pure-parametric
    /// polymorphic `UserFn` carrying a stored annotated `ast`.)
    pub(crate) fn entry_is_monomorphisable_polymorphic(entry: &Binding<C>) -> bool {
        entry.callable().is_some_and(|callable| {
            matches!(
                callable.arm.life,
                Life::Template {
                    body: TemplateBody::Ast(_) | TemplateBody::Synth(_),
                    ..
                }
            )
        })
    }

    /// Recursively walk an expression tree collecting calls to constrained fns.
    ///
    /// Each call site is recorded as (fn_name, arg_spans, call_span).
    /// The arg_spans are the spans of each argument expression, used to look up
    /// their types from `expr_types`.
    #[cfg(test)]
    pub(crate) fn collect_constrained_calls(
        expr: &Expr,
        constrained_fn_names: &HashSet<Symbol>,
        var_refs: &HashMap<Span, cranelisp_types::VarRef>,
        out: &mut Vec<(Symbol, Vec<Span>, Span)>,
    ) {
        // Per-node action: record a call site when this node is an Apply whose
        // callee is a bare reference to a constrained fn.
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && constrained_fn_names.contains(name)
            // FIXME 0653 — skip a §4.6 LOCAL shadow of a top-level constrained fn.
            && callee_has_keyed_carrier(var_refs, callee.span())
        {
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((name.clone(), arg_spans, *span));
        }
        // Recurse into children via the shared enumeration helper.
        for_each_child_expr(expr, |child| {
            Self::collect_constrained_calls(child, constrained_fn_names, var_refs, out)
        });
    }

    /// Like the `#[cfg(test)]` `collect_constrained_calls` walk, but excludes
    /// calls a constrained fn makes to ITSELF (FIXME 0349).
    ///
    /// A constrained/polymorphic defn's self-recursion is the generic definition,
    /// not a concrete monomorphisation site — its argument types are the defn's
    /// own generic vars, so there is no concrete instantiation to specialise.
    /// Every OTHER constrained call inside the body (including calls to *other*
    /// constrained fns from within a constrained fn) IS a real call site and must
    /// be collected, so a forward-referenced helper gets its mono variant created
    /// regardless of source definition order.
    pub(super) fn collect_constrained_calls_excluding_self(
        expr: &Expr,
        self_name: &Symbol,
        constrained_fn_names: &HashSet<Symbol>,
        var_refs: &HashMap<Span, cranelisp_types::VarRef>,
        out: &mut Vec<(Symbol, Vec<Span>, Span)>,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && constrained_fn_names.contains(name)
            && name != self_name
            // FIXME 0653 — skip a §4.6 LOCAL shadow of a top-level constrained fn.
            && callee_has_keyed_carrier(var_refs, callee.span())
        {
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((name.clone(), arg_spans, *span));
        }
        for_each_child_expr(expr, |child| {
            Self::collect_constrained_calls_excluding_self(
                child,
                self_name,
                constrained_fn_names,
                var_refs,
                out,
            )
        });
    }

    // --- Result building ---

    /// Drain pending auto-curry resolutions into method_resolutions.
    ///
    /// Each entry in `pending_auto_curry` records a call site where the
    /// typechecker detected partial application (fewer args than params).
    /// This converts them to `ResolvedCall::AutoCurry` entries that the
    /// backend can use for codegen.
    ///
    /// `drain` is a REQUIRED parameter, deliberately (Principle 18 — enforce
    /// invariants structurally; FIXME 0775). The drain runs at six
    /// non-equivalent seams and the safe answer differs between them, so there
    /// is **no default and no short convenience name**: every call site names
    /// its discipline, and a seam added later cannot inherit "never defer"
    /// silently by calling the obvious function. `Final` is the dangerous
    /// polarity — it asserts "this seam is settled", and asserting that at a
    /// pre-settlement seam strands an unresolved trait-operator curry on the
    /// `ViaCallee` fallback, diagnosed one crate away as the backend's located
    /// producer contradiction.
    ///
    /// The seam census is the mapping this parameter forces each caller to
    /// answer. `mono_collect::tests::auto_curry_drain_*` pins the two polarity
    /// behaviours directly; the per-seam reasons remain design-recorded:
    ///
    /// | Seam | Discipline | Why |
    /// |---|---|---|
    /// The complete six-seam census and the reason each seam selects
    /// `Deferrable` or `Final` live in `design/typecheck/auto-curry.md` §1.2.
    /// Keeping the durable set there avoids stale source-line coordinates.
    pub(crate) fn resolve_auto_curry(&self, state: &mut CheckState, drain: AutoCurryDrain) {
        let pending = std::mem::take(&mut state.pending_auto_curry);
        for (
            span,
            name,
            applied_count,
            total_count,
            callee_ty,
            mut pending_dispatch,
            callee_var_span,
        ) in pending
        {
            // If the trait resolution wasn't determined earlier (types were
            // still unresolved vars during try_auto_curry), attempt it now.
            // Later unifications (e.g., from a call site like `(make-adder 10)`)
            // may have pinned the type vars to concrete types.
            //
            // §11.8.8 (W3-review Important-1) — "the carrier is the IDENTITY". Gate
            // this raw-name re-resolution on the callee's recorded CARRIER VERDICT:
            // a callee resolved to a §4.6 LOCAL shadow (`(let [+ (fn [a b] 0)]
            // ((+ 1) 2))`) has `VarRef::Local`, so it must curry the LOCAL closure,
            // NOT re-derive the trait/primitive dispatch by raw name (mis-dispatch
            // → 3). `callee_has_keyed_carrier` is the shared P7 carrier guard (TRUE
            // only for `VarRef::Global`); a `None` inner resolution then transports
            // the local carrier downstream (below), currying the closure.
            if pending_dispatch.is_none()
                && callee_var_span.is_none_or(|sp| {
                    callee_has_keyed_carrier(&state.method_resolutions.var_refs, sp)
                })
            {
                let resolved_callee = self.apply_subst(state, &callee_ty);
                if let Type::Fn(full_params, _) = &resolved_callee {
                    let resolved_params: Vec<Type> = full_params
                        .iter()
                        .map(|t| self.apply_subst(state, t))
                        .collect();
                    match self.try_resolve_trait_method(state, &name, &resolved_params, span) {
                        Ok(Some(dispatch)) => pending_dispatch = Some(dispatch),
                        _ => {
                            if let Some(builtin) = self.resolve_builtin(state, &name, span) {
                                pending_dispatch =
                                    Some(crate::checker::PendingDispatch::Builtin(builtin));
                            }
                        }
                    }
                }
            }

            // S115 W4 — the fn-as-value `'='` producer boundary
            // (`design/backend/s115-carrier-and-rc-sweep.md` §1.3). A trait
            // OPERATOR whose operand type is still a free `Var` at this seam
            // resolves to NO impl, so the transport branch below would carry the
            // callee `Var`'s `VarRef::Global(prelude/=)` — the trait-method
            // DECLARATION FQ, a dispatch-table key with no GOT slot — into
            // `ApplyRef::Dispatch`. The wrapper emitter then dies at the
            // GOT terminal ("reached codegen with no GOT-slot carrier").
            //
            // BOUNDARY (structural, both drains): a trait-method-decl FQ is
            // NEVER transported as a dispatch carrier. At a DEFERRABLE
            // (pre-settlement) seam the whole entry is held back for the
            // settled finalize drain, where the call site has pinned the
            // operand concrete and `try_resolve_trait_method` above yields the
            // real impl (`primitives/eq-i64`) — P26, record from settled state.
            if pending_dispatch.is_none()
                && let Some(cvs) = callee_var_span
                && let Some(cranelisp_types::VarRef::Global(fq)) =
                    state.method_resolutions.var_refs.get(&cvs)
                && self.fq_is_trait_method_decl(fq)
            {
                if matches!(drain, AutoCurryDrain::Deferrable) {
                    state.deferred_auto_curry.push((
                        span,
                        name,
                        applied_count,
                        total_count,
                        callee_ty,
                        pending_dispatch,
                        callee_var_span,
                    ));
                    continue;
                }
                // FINAL drain and still unresolved: record the `AutoCurry`
                // without a dispatch carrier (the Apply epilogue's
                // `ApplyRef::ViaCallee` stands). The backend's 0705 totality
                // table then reports a LOCATED producer contradiction rather
                // than the raw GOT-terminal miss — a decl FQ still never rides.
                state.method_resolutions.resolved_calls.insert(
                    span,
                    ResolvedCall::AutoCurry {
                        target_name: name,
                        applied_count,
                        total_count,
                        trait_resolution: None,
                    },
                );
                continue;
            }

            let builtin_storage = match &pending_dispatch {
                Some(crate::checker::PendingDispatch::Builtin(builtin)) => {
                    Some(builtin.storage_fq.clone())
                }
                _ => None,
            };
            let trait_resolution = pending_dispatch.map(|dispatch| match dispatch {
                crate::checker::PendingDispatch::Resolved(resolution) => resolution,
                crate::checker::PendingDispatch::Builtin(builtin) => ResolvedCall::BuiltinFn {
                    name: builtin.jit_name,
                },
            });
            let has_inner = trait_resolution.is_some();
            let resolution = ResolvedCall::AutoCurry {
                target_name: name,
                applied_count,
                total_count,
                trait_resolution: trait_resolution.map(Box::new),
            };
            // S110 0583 leg 1 + W0.1b (§1.1.1): auto-curry carrier at the Apply
            // span. A trait/primitive curry derives from the inner resolution
            // (TraitMethod now reads `impl_module`). A PLAIN-fn curry instead
            // TRANSPORTS the callee `Var`'s already-recorded storage carrier
            // (resolve-once, shadow-correct) — the old `{current_module,
            // target}` derivation was wrong for an imported target. Matches
            // nothing for a local-binding target (`infer_var` records
            // `VarRef::Local`, not a `Global` — S114 carrier flip; was "recorded
            // nothing").
            if let Some(storage_fq) = builtin_storage {
                state
                    .method_resolutions
                    .apply_refs
                    .insert(span, cranelisp_types::ApplyRef::Dispatch(storage_fq));
            } else if has_inner {
                self.record_dispatch_target(state, span, &resolution);
            } else if let Some(cvs) = callee_var_span
                && let Some(cranelisp_types::VarRef::Global(fq)) =
                    state.method_resolutions.var_refs.get(&cvs).cloned()
            {
                // A PLAIN-fn auto-curry over a TABLE-resolved callee (`Global`)
                // transports the callee's storage FQ as the Apply-span dispatch
                // carrier (S114 carrier flip). A curry over a LOCAL callee
                // (`VarRef::Local`) matches nothing here → the Apply epilogue's
                // `ApplyRef::ViaCallee` stands (the identity rides the callee).
                state
                    .method_resolutions
                    .apply_refs
                    .insert(span, cranelisp_types::ApplyRef::Dispatch(fq));
            }
            state
                .method_resolutions
                .resolved_calls
                .insert(span, resolution);
        }
    }

    /// Is `fq` the storage identity of a trait-method **DECLARATION** (the
    /// `deftrait` method entry carrying `trait_origin`), as opposed to a
    /// callable — a plain user fn, a builtin, or a resolved impl method?
    ///
    /// Carrier-keyed (Principle 24): the question is asked of the FQ that would
    /// be transported, not of the raw source name. A declaration entry is a
    /// dispatch-table key — it never has a GOT slot — so it must never appear in
    /// an `ApplyRef::Dispatch`.
    pub(crate) fn fq_is_trait_method_decl(&self, fq: &cranelisp_types::FQSymbol) -> bool {
        self.method_to_trait_in_module(&fq.module, &fq.symbol)
            .is_some()
    }
}

#[cfg(test)]
mod tests;
