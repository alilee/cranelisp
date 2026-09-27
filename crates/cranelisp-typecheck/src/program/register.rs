use super::*;

mod multi_sig;

/// Resolved variant info: (concrete_params, concrete_ret, internal_name, variant_index).
type ResolvedVariant = (Vec<Type>, Type, Symbol, usize);

/// Mangled variant info: (concrete_params, concrete_ret, mangled_name).
type MangledVariantInfo = (Vec<Type>, Type, Symbol);

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Pass 1 (Register) dispatch: register type defs, trait decls/impls, signatures.
    pub(super) fn check_form_register(
        &self,
        state: &mut CheckState,
        form: &TopLevel,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        match form {
            TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } => {
                self.register_type_def(
                    state,
                    name,
                    docstring,
                    type_params,
                    constructors,
                    *visibility,
                    *span,
                )?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitDecl(decl) => {
                self.register_trait_decl(state, decl)?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitImpl(impl_) => {
                let defaults = self.register_trait_impl(state, impl_)?;
                let mut result = FormCheckResult::empty();
                result.default_method_defns = defaults;
                Ok(result)
            }
            TopLevel::Defn(defn) => {
                if defn.is_multi_sig() {
                    self.check_form_register_multi_sig(state, defn, accumulator)
                } else {
                    self.check_form_register_single_defn(state, defn, accumulator)
                }
            }
            TopLevel::Expr(_) => {
                // Expr forms should be wrapped as synthetic Defn before reaching here.
                // If they somehow arrive unwrapped, treat as no-op.
                Ok(FormCheckResult::empty())
            }
        }
    }

    /// Register a single-sig defn's signature (Pass 1).
    pub(super) fn check_form_register_single_defn(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let target = BodyTarget::Direct(defn.name.clone());
        accumulator
            .bodies
            .reject_duplicate(&target, &defn.name, defn.span)?;
        let signature = self.register_defn_signature(state, defn)?;
        let already_checked_trait_method = self
            .current_symbol_table(state)
            .view()
            .lookup(&defn.name)
            .and_then(Binding::callable)
            .is_some_and(|callable| {
                matches!(callable.origin, CallableOrigin::TraitMethod { .. })
                    && matches!(
                        callable.arm.life,
                        Life::Concrete { ast: Some(_), .. }
                            | Life::Template {
                                body: TemplateBody::Ast(_),
                                ..
                            }
                    )
            });
        if !already_checked_trait_method {
            accumulator.bodies.register(signature.into_registration(
                target,
                defn.name.clone(),
                defn.span,
            ))?;
        }
        Ok(FormCheckResult::empty())
    }

    /// Register a multi-sig defn: expand variants, register each, register base as Overloaded.
    pub(super) fn check_form_register_multi_sig(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let mut overload_entries = Vec::new();
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            let target = BodyTarget::MultiSignatureClause {
                group: defn.name.clone(),
                clause: i,
            };
            accumulator
                .bodies
                .reject_duplicate(&target, &internal_name, variant.span)?;
            overload_entries.push((internal_name.clone(), variant.params.len()));

            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };
            // Register each variant's signature
            let signature = self.register_defn_signature(state, &internal_defn)?;
            accumulator.bodies.register(signature.into_registration(
                target,
                internal_name,
                variant.span,
            ))?;
        }
        state.overloads.insert(defn.name.clone(), overload_entries);

        Ok(FormCheckResult::empty())
    }

    /// Detect constrained polymorphic functions after generalization.
    ///
    /// A function is constrained if its generalized scheme has non-empty constraints.
    /// These functions settle as constrained templates.
    pub(super) fn detect_constrained_fns(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
    ) -> HashSet<Symbol> {
        // Body checking records the constrained names; this reconstruction
        // reads the settled lifecycle rather than a parallel state marker.
        let mut names = HashSet::new();

        for defn in defns {
            let r = self.current_symbol_table(state);
            if let Some(callable) = r.view().lookup(&defn.name).and_then(Binding::callable)
                && matches!(
                    callable.arm.life,
                    Life::Template {
                        kind: TemplateKind::Constrained(_),
                        ..
                    }
                )
            {
                names.insert(defn.name.clone());
            }
        }

        names
    }

    /// Resolve a stacked trait-bound parameter annotation (`:Eq :Display a`,
    /// spec §3.9.2) to a fresh constrained type variable (spec §3.9.3
    /// try-type-then-trait; FIXME 0346 / 0341 typecheck half).
    ///
    /// Allocates a fresh `Type::Var`, resolves each `TraitRef` as written
    /// through the step the type-or-trait annotation shares
    /// (`design/typecheck/typecheck.md` §3.5), and records the (var, trait)
    /// pairs on `state.active_constraints`. `generalize` then lifts these onto
    /// the defn's `Scheme.constraints` when the var is quantified. A member that
    /// does not resolve is the form's failure, so an absent module records its
    /// `Type` gap. Returns the var and the resolved traits in written order,
    /// which the ledger keeps as the parameter's declared bounds (§9.2.1).
    ///
    /// The binder is deliberately NOT unified with any concrete type here — it
    /// is a fresh constrained var, and any concrete shape is contributed by the
    /// body's use of the parameter (the bounds restrict which instantiations are
    /// legal, exactly as a body-driven constrained-fn does).
    pub(super) fn resolve_bound_param(
        &self,
        state: &mut CheckState,
        bounds: &[cranelisp_types::TraitRef],
        span: Span,
    ) -> Result<(Type, Vec<cranelisp_types::FQTraitName>), CranelispError> {
        let (var_ty, var_id) = self.fresh_var_id();
        let mut traits = Vec::with_capacity(bounds.len());
        for tref in bounds {
            let fqtn = self
                .resolve_trait_as_written(state, tref.module.as_ref(), tref.name.as_ref(), span)
                .map_err(|failure| failure.into_form_error(state))?;
            state.active_constraints.add(var_id, fqtn.clone());
            traits.push(fqtn);
        }
        Ok((var_ty, traits))
    }

    /// Create fresh type variables for a function's parameters and return type,
    /// respecting any annotations, and register the signature in the symbol table.
    ///
    /// Returns the signature facts body checking and settlement read.
    /// Shared by the per-form registration path (`check_form_register_single_defn`)
    /// and the multi-sig variant registration to prevent the two paths from
    /// diverging as rings add complexity.
    pub(super) fn register_defn_signature(
        &self,
        state: &mut CheckState,
        defn: &Defn,
    ) -> Result<DefnSignature, CranelispError> {
        // Fast path for trait impl (mangled) methods: if this symbol already
        // has a checked callable entry, AND its name matches the trait-impl mangled
        // form `Trait.method$Type`, it was already type-checked by
        // `check_impl_method`. Reuse its param/ret types rather than
        // allocating fresh type vars — the fresh vars would never be unified
        // (CheckBody short-circuits on `ast: Some`) and would leave the symbol
        // with a spuriously polymorphic scheme after
        // `finalize_check_result_inner`'s generalization pass, breaking trait
        // dispatch (e.g., `(double true)` silently accepting any type).
        //
        // The name-pattern gate avoids false positives on `__expr` (REPL
        // synthetic) or regular user defns whose ast was annotated by a prior
        // REPL evaluation.
        if is_trait_impl_mangled_name(defn.name.as_ref()) {
            let r = self.current_symbol_table(state);
            if let Some(callable) = r.view().lookup(&defn.name).and_then(Binding::callable)
                && matches!(callable.origin, CallableOrigin::TraitMethod { .. })
                && matches!(
                    callable.arm.life,
                    Life::Concrete { ast: Some(_), .. }
                        | Life::Template {
                            body: TemplateBody::Ast(_),
                            ..
                        }
                )
                && let Type::Fn(param_types, ret_ty) = &callable.arm.scheme.ty
            {
                return Ok(DefnSignature {
                    param_types: param_types.clone(),
                    ret_ty: (*ret_ty.clone()),
                    written_var_scope: HashMap::new(),
                    declared_bounds: Vec::new(),
                });
            }
        }

        // ONE var scope for the whole signature (spec §3.3.1 [S109 W6.3]): a
        // free lowercase type var the author writes in a param annotation mints a
        // fresh FLEXIBLE var carrying that display name, and a repeated name
        // (`[:a x :a y]`) resolves to the SAME var so x and y unify. This map is
        // built fresh PER CALL — multi-arity clauses each go through a separate
        // `register_defn_signature` (via their own `{name}__vN` internal defn,
        // see `check_form_register_multi_sig`), so `:a` in one clause is
        // independent of `:a` in another (fresh scope per clause). It is returned
        // with the signature facts in that occurrence's registered ledger record,
        // then installed by Pass 2 so a body/nested-`fn` `:a` CO-REFERS to the
        // param's var (§3.3.1 co-reference; 0588). A bare written var carries ONLY a name
        // — it is NOT rigid; rigidity lives on the constraint path, and
        // `check_defn_body` seeds `rigid_vars` from asserted-constraint param
        // vars, NOT from this map's values.
        let mut var_map: HashMap<Symbol, TypeId> = HashMap::new();
        let mut param_types = Vec::new();
        let mut declared_bounds = Vec::new();
        for (param_index, (param, ann)) in defn.params().iter().enumerate() {
            let (param_ty, bounds) = match ann {
                // Stacked trait-bound annotation (`:Eq :Display a`, spec §3.9.2):
                // the binder is "an unspecified type satisfying these traits"
                // (spec §3.9.3 try-type-then-trait). It resolves to a FRESH
                // constrained type variable, NOT a concrete type — so it is
                // intercepted here, before delegating to the pure
                // `TypeExpr -> Type` resolver (which has no fresh-var allocator
                // or constraint sink). The traits accumulate onto the var via
                // `active_constraints`, which `generalize` later lifts onto the
                // defn's `Scheme.constraints` (FIXME 0346 / 0341 typecheck half).
                Some(cranelisp_types::TypeExpr::Bounds(bounds)) => {
                    self.resolve_bound_param(state, bounds, defn.span)?
                }
                Some(ann) => {
                    match self.resolve_annotation_type_expr_in_module(
                        ann,
                        &mut var_map,
                        &state.current_module,
                        defn.span,
                    ) {
                        // A bare param-annotation var is FLEXIBLE and carries only
                        // its display name (§3.3.1 [S109 W6.3]); the shared scope
                        // (`var_map`) threads it to Pass-2 for CO-REFERENCE, not
                        // rigidity — `check_defn_body` seeds `rigid_vars` from
                        // asserted-constraint param vars, not from `var_map`.
                        Ok(ty) => (ty, Vec::new()),
                        // Try-type-then-trait (spec §3.9.3). A SINGLE annotation
                        // `:Eq a` is ambiguous between a concrete-type annotation
                        // and a single trait bound; the frontend leaves it as a
                        // `TypeExpr::Named`. When no TYPE exists, a name that
                        // resolves as a trait (read by the step the value route
                        // shares, typecheck.md §7.3.2) constrains a fresh var with
                        // the trait's resolved home. Otherwise the type failure
                        // (the genuine "neither type nor trait" case) propagates.
                        Err(type_err) => {
                            match self.resolve_annotation_trait(state, ann, defn.span) {
                                Some(fq_trait) => {
                                    let (var_ty, var_id) = self.fresh_var_id();
                                    state.active_constraints.add(var_id, fq_trait.clone());
                                    (var_ty, vec![fq_trait])
                                }
                                None => return Err(type_err.into_form_error(state)),
                            }
                        }
                    }
                }
                None => (self.fresh_var(), Vec::new()),
            };
            param_types.push(param_ty);
            declared_bounds.extend(bounds.into_iter().map(|trait_ref| DeclaredBound {
                param_index,
                param: param.clone(),
                trait_ref,
            }));
        }
        let ret_ty = self.fresh_var();

        let fn_type = Type::Fn(param_types.clone(), Box::new(ret_ty.clone()));
        let scheme = mono(fn_type);

        // Pass 1 declares only the signature. `Life::Declared { prior }` is the
        // sole redefinition carrier: it preserves any displaced concrete slot
        // and code owner until checked settlement either reuses them or the
        // enclosing transaction fails. The private body ledger independently
        // retains the source body until that final settlement window.
        let mut table = self.current_symbol_table_mut(state);
        let origin = CallableOrigin::Plain;
        table
            .declare(
                defn.name.clone(),
                scheme,
                defn.params().iter().map(|(n, _)| n.clone()).collect(),
                defn.docstring.clone(),
                0,
                origin,
                defn.visibility,
            )
            .map_err(crate::result::lifecycle_error)?;

        Ok(DefnSignature {
            param_types,
            ret_ty,
            written_var_scope: var_map,
            declared_bounds,
        })
    }

    /// Pass 4 (batch): scan all defn bodies for calls to constrained functions
    /// and generate monomorphised specializations.
    /// S84 Wave 1b (FIXME 0374/0378 issue 3, Principle 20): register discovered
    /// `test-*` entry points as monomorphisation ROOTS, like `main`.
    ///
    /// The TOTAL slot gate (`slot ⟺ is_concrete()`) makes a result-only-var test
    /// fn (`(defn test-x [] None)` → `(Fn [] (Option a))`) slot-less `Polymorphic`.
    /// But a test fn is an ENTRY POINT — the discovery readers
    /// (`discover_test_names` / `discover_eligible_tests`) need a concrete
    /// `(Fn [] (Option String))` instance to invoke. So we register each such test
    /// fn as a root: recheck its body at the expected entry type
    /// `(Fn [] (Option String))` and re-register a `Concrete{slot}` entry UNDER THE
    /// BARE NAME (no `name$T` mangling — one fixed entry type per test fn). This
    /// mirrors `main`'s `(IO t)→(IO Int)` finalisation, and keeps int's names-only
    /// discovery reader byte-identical (the slot now rides the concrete instance
    /// under the same name).
    ///
    /// Only the **degenerate** shape needs this: a well-formed test fn
    /// (`(defn test-x [] (if c None (Some "msg")))`) already pins `(Option String)`
    /// and is already `Concrete{slot}` — its scheme is concrete, so it is not
    /// `Polymorphic` and is skipped here. A param-polymorphic def is excluded
    /// by the nullary requirement.
    ///
    /// The root set is enumerated by the SAME syntactic+shape filter the discovery
    /// readers use (no int→typecheck call): bare name `test-*`, nullary, current
    /// scheme `(Fn [] (Option a))` with the result var free (the only carve-out
    /// customer). A test fn whose body forces a NON-`String` `(Option …)` (or any
    /// other concrete result) is already `Concrete` and not seen here.
    pub(super) fn register_test_fn_mono_roots(
        &self,
        state: &mut CheckState,
        bodies: &mut BodyLedger,
    ) -> Result<(), CranelispError> {
        // Enumerate eligible checked test-fn bodies plus the Option FQTypeName
        // from their declared result type. Collect first (no mutable overlap),
        // then recheck and refine the same ledger records.
        let candidates: Vec<(Symbol, DefnVariant, cranelisp_types::FQTypeName)> = bodies
            .checked_bodies()
            .filter_map(|body| {
                let name = &body.registration.publication_name;
                if !name.as_ref().starts_with("test-") {
                    return None;
                }
                let callable = self
                    .current_symbol_table(state)
                    .view()
                    .lookup(name)
                    .and_then(Binding::callable)
                    .cloned()?;
                // Must be nullary with a result-only free var — shape
                // `(Fn [] (Option a))` (a is unbound). A concrete-result test
                // fn has no free result variable and therefore does not
                // reach this shape; a parameter-polymorphic def has params.
                let Type::Fn(params, ret) = &callable.arm.scheme.ty else {
                    return None;
                };
                if !params.is_empty() {
                    return None;
                }
                // The result must be `(Option <var>)` — the degenerate
                // `(defn test-x [] None)` shape. Anything else (a bare result
                // var, a non-Option ADT) is not a test-discovery entry. Keep
                // the actual FQTypeName so the concrete instance uses Option's
                // real home module (not a hardcoded one).
                let Type::ADT(fqtn, args) = ret.as_ref() else {
                    return None;
                };
                if fqtn.name.as_ref() != "Option" || args.len() != 1 {
                    return None;
                }
                if !matches!(args[0], Type::Var(_)) {
                    return None;
                }
                Some((name.clone(), body.ast.clone(), fqtn.clone()))
            })
            .collect();

        for (name, variant, option_fqtn) in candidates {
            // Recheck the body at the expected entry type `(Fn [] (Option String))`
            // — the discovery contract's fixed entry type (`test_scheme_is_eligible`).
            // The degenerate body `None` unifies trivially (`a -> String`).
            let option_string = Type::ADT(option_fqtn, vec![Type::String]);
            let mut wrap_defn = Defn {
                name: name.clone(),
                docstring: None,
                variants: vec![variant.clone()],
                visibility: Visibility::Public,
                span: variant.span,
            };
            let recheck =
                self.recheck_body_for_mono(state, &mut wrap_defn, &[], &option_string, None);
            // If the body cannot be concretised at `(Option String)` (e.g. it
            // forces a different concrete `Option` instance), leave the
            // checked declaration untouched — discovery's eligibility filter will
            // correctly skip a non-`(Option String)` test fn.
            let Ok((resolutions, mono_expr_types)) = recheck else {
                continue;
            };

            // Annotate the body and apply the final substitution so the backend
            // codegens the concrete instance (mirrors `register_mono_entry`).
            let mut concrete_defn = Defn {
                name: name.clone(),
                docstring: None,
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: Visibility::Public,
                span: variant.span,
            };
            annotate_defn_from_maps(
                &mut concrete_defn,
                &mono_expr_types,
                &resolutions.resolved_calls,
            );
            apply_subst_to_defn(&state.subst, &mut concrete_defn);

            let concrete_scheme = mono(Type::Fn(vec![], Box::new(option_string.clone())));
            state
                .method_resolutions
                .resolved_calls
                .extend(resolutions.resolved_calls);
            state
                .method_resolutions
                .pattern_ctors
                .extend(resolutions.pattern_ctors);
            state
                .method_resolutions
                .var_refs
                .extend(resolutions.var_refs);
            state
                .method_resolutions
                .apply_refs
                .extend(resolutions.apply_refs);
            state.expr_types.extend(mono_expr_types);
            if let Some(ast) = concrete_defn.variants.into_iter().next() {
                if let Some(body) = bodies.checked_mut_for_publication(&name) {
                    *body.ast = ast;
                }
                self.current_symbol_table_mut(state)
                    .update_declared_scheme(&name, concrete_scheme)
                    .map_err(crate::result::lifecycle_error)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
