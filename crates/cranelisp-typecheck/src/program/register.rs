use super::*;

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
                // §8.6.4 (FIXME 0514): reject a type def whose name is already in
                // scope via an explicit import/export or the implicit prelude —
                // the same mode-uniform seam as the value-def case below.
                self.reject_def_over_binding(state, &Symbol::from(name.as_ref()), *span)?;
                self.register_type_def(
                    state, name, docstring, type_params, constructors, *visibility, *span,
                )?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitDecl(decl) => {
                // §8.6.4 (S108 Wave-G convergence): route the trait NAME and
                // each METHOD name through the ONE definition seam BEFORE
                // registration — a `deftrait`/`deftrait-` whose trait name or
                // any method name is already in scope via an explicit
                // import/export or the implicit prelude is a compile-time
                // conflict, never a shadow (§8.8.1: the prelude is just an
                // implicit `(import [prelude [*]])`). Placed at the arm (not
                // inside `register_trait_decl`) so it covers the plain AND HKT
                // registration branches with one call site, keeping
                // `check_form_register` the ONE visible place all typecheck-side
                // definition forms hit the seam. A trait method is a fresh
                // module-scope binding with a fresh terminal — it can never
                // dedup — so each method name is checked identically to the
                // trait name.
                self.reject_def_over_binding(
                    state, &Symbol::from(decl.name.as_ref()), decl.span,
                )?;
                for method in &decl.methods {
                    self.reject_def_over_binding(state, &method.name, decl.span)?;
                }
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
                // §8.6.4 (FIXME 0514): reject a definition whose bare name is
                // already bound in scope by an explicit import/export or the
                // implicit prelude (the no-exception ruling). Fires identically
                // in every mode — the single shared seam both REPL/Additive and
                // batch/Replace traverse. Own-redefinition (home == current) is
                // NOT a collision and is left to the redefinition machinery.
                self.reject_def_over_binding(state, &defn.name, defn.span)?;
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
        // Capture the prior concrete slot BEFORE register_defn_signature
        // overwrites the entry with a slot-less NotDetermined (S83 deferred
        // allocation, Principle 20). The Pass-2 determination point reuses it.
        // Read through the same `current_symbol_table_mut().get()` path the
        // overwrite uses, so staging-vs-live matches the write target.
        if let Some(slot) = self
            .current_symbol_table_mut(state)
            .get(defn.name.as_ref())
            .and_then(|e| e.callable_got_slot())
        {
            accumulator.redef_slots.insert(defn.name.clone(), slot);
        }
        let (param_types, ret_ty, var_scope) = self.register_defn_signature(state, defn)?;
        accumulator.defn_type_vars.insert(defn.name.clone(), (param_types, ret_ty));
        accumulator.defn_var_scopes.insert(defn.name.clone(), var_scope);
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
            // Capture the prior concrete slot for this `__vN` variant before
            // register_defn_signature overwrites it (S83 deferred allocation):
            // the Pass-2 determination point reuses it on REPL redefinition of
            // the same multi-sig defn.
            if let Some(slot) = self
                .current_symbol_table_mut(state)
                .get(internal_name.as_ref())
                .and_then(|e| e.callable_got_slot())
            {
                accumulator.redef_slots.insert(internal_name.clone(), slot);
            }
            // Register each variant's signature
            let (param_types, ret_ty, var_scope) =
                self.register_defn_signature(state, &internal_defn)?;
            accumulator.defn_var_scopes.insert(internal_name.clone(), var_scope);
            accumulator.defn_type_vars.insert(internal_name, (param_types, ret_ty));
        }
        state.overloads.insert(defn.name.clone(), overload_entries);

        // Register a placeholder for the base name
        let placeholder_ty = self.fresh_var();
        let placeholder_scheme = mono(placeholder_ty);
        let mut builder = ModuleEntry::def(
            placeholder_scheme,
            DefKind::Overloaded { variants: vec![] },
        )
        .visibility(defn.visibility);
        if let Some(doc) = defn.docstring.clone() {
            builder = builder.docstring(doc);
        }
        self.current_symbol_table_mut(state).insert(defn.name.clone(), builder.build());

        Ok(FormCheckResult::empty())
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
    pub(super) fn resolve_multi_sig_overloads(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
        mangled_by_base: &mut MangledNamesByBase,
    ) -> Result<Vec<Defn>, CranelispError> {
        let mut result_defns = Vec::new();

        for top in program {
            if let TopLevel::Defn(defn) = top {
                if !defn.is_multi_sig() {
                    continue;
                }

                let resolved = self.resolve_variant_types(state, defn, type_vars)?;
                let (mangled_defns, resolved_info) =
                    self.register_mangled_variants(state, defn, &resolved)?;
                mangled_by_base
                    .entry(defn.name.clone())
                    .or_default()
                    .extend(resolved_info.iter().map(|(_, _, mangled)| mangled.clone()));
                result_defns.extend(mangled_defns);
                self.register_overloaded_base(state, defn, resolved_info);
            }
        }

        Ok(result_defns)
    }


    /// Post-drain finalisation of multi-sig variant types (S112 leg a §11.3(B),
    /// extends the S91 Wave-7 / FIXME 0432 Face A return-type refresh).
    ///
    /// Runs AFTER `resolve_pending_overloads` (the sole drain), once the §5.1.2
    /// back-flow has settled every clause's params. Two phases:
    ///
    /// **Phase A — promote back-flow-pinned clauses to `Concrete`.** A clause
    /// pinned concrete by a sibling self-call (`rp4`'s 2-arg clause) was
    /// registered as a `$Var` `Polymorphic` TEMPLATE pre-drain (its params were
    /// still `Var`). Now that its params are concrete it is a single concrete
    /// callable and gets its `Concrete{slot}` sibling under the CONCRETE mangle —
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
    pub(super) fn finalize_multi_sig_variant_types(
        &self,
        state: &mut CheckState,
        working_program: &[TopLevel],
        accumulator: &ModuleCheckAccumulator,
        multi_sig_mangled_names: &mut MangledNamesByBase,
    ) -> Result<(), CranelispError> {
        // B1 fix (§11.3.2): drain the deferred self-call worklist and group by the
        // selected clause. Taken unconditionally so no stale entry survives into a
        // later REPL cluster. Each self-call's `SigDispatch` is derived below from
        // the SAME `mangle_sig` (over the finalised post-drain params) that keys the
        // clause's `Concrete` entry — carriers 5–6 join carriers 1–4 at ONE source.
        let mut deferred_by_variant: HashMap<(Symbol, usize), Vec<Span>> = HashMap::new();
        for (span, base, idx) in std::mem::take(&mut state.deferred_self_call_dispatch) {
            deferred_by_variant.entry((base, idx)).or_default().push(span);
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
                let Some((param_tys, ret_ty)) =
                    accumulator.defn_type_vars.get(&internal_name)
                else {
                    continue;
                };
                let concrete_params: Vec<Type> =
                    param_tys.iter().map(|t| self.apply_subst(state, t)).collect();
                let concrete_ret = self.apply_subst(state, ret_ty);

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
                            mangled_name: JitSymbol::from(concrete_mangled.as_ref()),
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
                let (annotated_ast, doc): (Option<DefnVariant>, Option<String>) =
                    match self.current_symbol_table(state).view().lookup(dispatch_name) {
                        Some(ModuleEntry::Def { ast, docstring, .. }) => {
                            (ast.clone(), docstring.clone())
                        }
                        _ => (None, None),
                    };
                let fn_ty = Type::Fn(concrete_params.clone(), Box::new(concrete_ret.clone()));
                let scheme = self.generalize(state, &fn_ty);
                let variant = &defn.variants[i];
                {
                    let mut st = self.current_symbol_table_mut(state);
                    let slot = st
                        .allocate_got_slot()
                        .map_err(crate::result::got_exhausted_error)?;
                    let mut builder = ModuleEntry::def(
                        scheme.clone(),
                        DefKind::UserFn {
                            fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
                        },
                    )
                    .visibility(defn.visibility)
                    .param_names(variant.params.iter().map(|(n, _)| n.clone()).collect());
                    if let Some(doc) = doc {
                        builder = builder.docstring(doc);
                    }
                    if let Some(ast) = annotated_ast {
                        // The concrete-boundary view is rebuilt by
                        // `finalize_annotations_and_publish` (it re-annotates every
                        // mangled entry named in `multi_sig_mangled_names`, now
                        // pointing at the concrete sibling); set the ast here.
                        builder = builder.ast(ast);
                    }
                    st.insert(concrete_mangled.clone(), builder.build());
                    // Remove the stale `$Var` template — a back-flow clause is a
                    // single concrete callable, not a mono source.
                    st.symbols.remove(dispatch_name.as_ref());
                }
                // Re-point the base OverloadVariant.
                {
                    let mut st = self.current_symbol_table_mut(state);
                    if let Some(ModuleEntry::Def { kind, .. }) =
                        st.symbols.get_mut(defn.name.as_ref())
                        && let DefKind::Overloaded { variants } = kind.as_mut()
                        && let Some(v) = variants.get_mut(i)
                    {
                        v.param_types = concrete_params.clone();
                        v.ret_type = concrete_ret.clone();
                        v.mangled_name = concrete_mangled.clone();
                    }
                }
                // Re-point resolved_overloads (rehydrated by a later cluster).
                if let Some(vs) = state.resolved_overloads.get_mut(&defn.name)
                    && let Some(v) = vs.get_mut(i)
                {
                    *v = (concrete_params.clone(), concrete_ret.clone(), concrete_mangled.clone());
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
            for (_params, ret, _mangled) in variants.iter_mut() {
                *ret = apply(&subst, ret);
            }
        }
        let mut st = self.current_symbol_table_mut(state);
        for (base, mangled_names) in multi_sig_mangled_names.iter() {
            if let Some(ModuleEntry::Def { kind, .. }) = st.symbols.get_mut(base.as_ref())
                && let DefKind::Overloaded { variants } = kind.as_mut()
            {
                for v in variants.iter_mut() {
                    v.ret_type = apply(&subst, &v.ret_type);
                }
            }
            for mangled in mangled_names {
                if let Some(ModuleEntry::Def { scheme, .. }) = st.symbols.get_mut(mangled) {
                    scheme.ty = apply(&subst, &scheme.ty);
                }
            }
        }
        Ok(())
    }


    /// For a single multi-sig defn, resolve each variant's concrete param/return
    /// types by applying substitution, and check for duplicate signatures.
    ///
    /// Returns a vec of `(concrete_params, concrete_ret, internal_name, variant_index)`
    /// for each variant.
    pub(super) fn resolve_variant_types(
        &self,
        state: &CheckState,
        defn: &Defn,
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Result<Vec<ResolvedVariant>, CranelispError> {
        let mut resolved = Vec::new();
        let mut sig_set: Vec<Vec<Type>> = Vec::new();

        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));

            let (param_tys, ret_ty) = type_vars
                .get(&internal_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!(
                        "internal: missing type vars for multi-sig variant {}",
                        internal_name
                    ),
                    location: ErrorLocation::from_span(variant.span),
                })?;

            let concrete_params: Vec<Type> = param_tys
                .iter()
                .map(|t| self.apply_subst(state, t))
                .collect();
            let concrete_ret = self.apply_subst(state, ret_ty);

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
    pub(super) fn register_mangled_variants(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        resolved: &[ResolvedVariant],
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
            let is_template = !concrete_params.iter().all(Type::is_concrete);
            if is_template {
                let mut st = self.current_symbol_table_mut(state);
                if let Some(entry) = st.symbols.remove(internal_name.as_ref()) {
                    // Re-key intact: keep the `Constrained`/`Polymorphic` kind,
                    // its scheme, and its annotated `ast`. Templates are mono
                    // SOURCES (`defined_symbols()` excludes them), so no mangled
                    // `Defn` is produced for the backend — the mono instances
                    // minted at the drain carry the codegen bodies.
                    st.insert(mangled.clone(), entry);
                }
                drop(st);
                resolved_info.push((concrete_params.clone(), concrete_ret.clone(), mangled));
                continue;
            }

            let fn_ty = Type::Fn(
                concrete_params.clone(),
                Box::new(concrete_ret.clone()),
            );
            let scheme = self.generalize(state, &fn_ty);

            // Remove internal name, register mangled name.
            // Wave 0 (§9.3): capture the already-annotated `ast` from the
            // internal-name entry (`foo__v0`) and transfer it onto the mangled
            // entry, renaming `defn.name` to the mangled form. The internal
            // variant was fully annotated by `check_form_body_multi_sig` —
            // no re-annotation needed here.
            let mut st = self.current_symbol_table_mut(state);
            let internal_entry = st.symbols.remove(internal_name.as_ref());
            // Post S69 Submission 35: `ast: Option<DefnVariant>`. No `name`
            // field on DefnVariant — the symbol-table key carries the name;
            // mangling lives at the entry insertion below.
            let annotated_ast: Option<DefnVariant> = match internal_entry {
                Some(ModuleEntry::Def { ast, .. }) => ast,
                _ => None,
            };
            // A resolved multi-sig mangled variant is a concrete callable born
            // with its slot (S83 deferred allocation, Principle 20): the slot
            // rides inside the `Concrete` `fn_state`, not a flat `Def` field.
            let slot = st
                .allocate_got_slot()
                .map_err(crate::result::got_exhausted_error)?;
            let mut builder = ModuleEntry::def(
                scheme.clone(),
                DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None } },
            )
            .visibility(defn.visibility)
            .param_names(variant.params.iter().map(|(n, _)| n.clone()).collect());
            if let Some(doc) = defn.docstring.clone() {
                builder = builder.docstring(doc);
            }
            if let Some(ast) = annotated_ast {
                // S84 Phase-3 (FIXME 0392): a resolved multi-sig mangled variant
                // is a codegen-bound `Concrete` entry — build its
                // concrete-boundary `MonoExpr` view from the same annotated,
                // subst-resolved variant body the `ast` carries (best-effort; a
                // `$Var`-param variant body legitimately stays non-concrete — see
                // `build_concrete_codegen_view`).
                if let Some(view) = build_concrete_codegen_view(&mangled, &ast, &state.method_resolutions.pattern_ctors, &state.method_resolutions.resolved_targets) {
                    builder = builder.codegen_view(view);
                }
                builder = builder.ast(ast);
            }
            st.insert(mangled.clone(), builder.build());

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
    pub(super) fn register_overloaded_base(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        resolved: Vec<(Vec<Type>, Type, Symbol)>,
    ) {
        let overload_variants = resolved
            .iter()
            .map(|(params, ret, mangled)| {
                cranelisp_types::OverloadVariant {
                    param_types: params.clone(),
                    ret_type: ret.clone(),
                    mangled_name: mangled.clone(),
                }
            })
            .collect();

        // Build a union scheme for the base name — use first variant's
        // scheme for now. The base name is registered as Overloaded so
        // `infer_apply` detects it and records a pending overload.
        let first_fn_ty = Type::Fn(
            resolved[0].0.clone(),
            Box::new(resolved[0].1.clone()),
        );
        let base_scheme = self.generalize(state, &first_fn_ty);

        let mut builder = ModuleEntry::def(
            base_scheme,
            DefKind::Overloaded { variants: overload_variants },
        )
        .visibility(defn.visibility);
        if let Some(doc) = defn.docstring.clone() {
            builder = builder.docstring(doc);
        }
        self.current_symbol_table_mut(state).insert(defn.name.clone(), builder.build());

        state.resolved_overloads.insert(
            defn.name.clone(),
            resolved,
        );
    }


    /// Resolve pending overload dispatch resolutions (the sole drain, §5.1.2).
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
    pub(super) fn resolve_pending_overloads(&self, state: &mut CheckState) -> Result<(), CranelispError> {
        let pending = std::mem::take(&mut state.pending_overload_resolutions);

        // Pass 1 — self-calls (monomorphic recursion).
        for (span, base_name, arg_types, ret_type_var, is_self) in &pending {
            if !is_self {
                continue;
            }
            self.resolve_one_overload_call(state, *span, base_name, arg_types, ret_type_var, true)?;
        }
        // Pass 2 — external calls.
        for (span, base_name, arg_types, ret_type_var, is_self) in &pending {
            if *is_self {
                continue;
            }
            self.resolve_one_overload_call(state, *span, base_name, arg_types, ret_type_var, false)?;
        }

        Ok(())
    }


    /// Resolve one pending overload call (`resolve_pending_overloads` worker).
    /// `is_self_call` selects monomorphic-recursion UNIFY (self-call) vs the
    /// concrete-or-monomorphise external dispatch bifurcation.
    fn resolve_one_overload_call(
        &self,
        state: &mut CheckState,
        span: Span,
        base_name: &Symbol,
        arg_types: &[Type],
        ret_type_var: &Type,
        is_self_call: bool,
    ) -> Result<(), CranelispError> {
        let concrete_args: Vec<Type> =
            arg_types.iter().map(|t| apply(&state.subst, t)).collect();

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
            let variant_index = variants
                .iter()
                .position(|(_, _, m)| *m == mangled_name)
                .unwrap_or(0);
            state
                .deferred_self_call_dispatch
                .push((span, base_name.clone(), variant_index));
            return Ok(());
        }

        // External call — bifurcate on the clause's concreteness.
        if resolved_variant_params.iter().all(Type::is_concrete) {
            // CONCRETE clause: unify the variant's params with the call args
            // (type-check them) and dispatch to the CONCRETE mangle — the exact
            // name `finalize_multi_sig_concrete_variants` registers the entry
            // under (one `mangle_sig` source, Principle 7 ⇒ no SigDispatch rewrite).
            for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                self.unify(state, p, a, span)?;
            }
            self.unify(state, ret_type_var, &ret_ty, span)?;
            let concrete_mangled = mangle_sig(base_name.as_ref(), &resolved_variant_params);
            let resolution = ResolvedCall::SigDispatch {
                mangled_name: JitSymbol::from(concrete_mangled.as_ref()),
            };
            self.record_dispatch_target(state, span, &resolution);
            state.method_resolutions.resolved_calls.insert(span, resolution);
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
            let mono = self.monomorphise_call(
                state, &mangled_name, &concrete_args, span, None, Some(base_name),
            )?;
            let instance = match mono {
                Some(md) => md.defn.name.clone(),
                None => mangled_name.clone(),
            };
            // Pin the caller's deferred return var to the instance's concrete
            // return so the caller generalises over the settled type.
            let cm = state.current_module.clone();
            if let Some(ModuleEntry::Def { scheme, .. }) =
                self.probe_module_entry_owned(&cm, instance.as_ref())
                && let Type::Fn(_, ret) = &scheme.ty
            {
                let ret = (**ret).clone();
                self.unify(state, ret_type_var, &ret, span)?;
            }
            let resolution = ResolvedCall::SigDispatch {
                mangled_name: JitSymbol::from(instance.as_ref()),
            };
            self.record_dispatch_target(state, span, &resolution);
            state.method_resolutions.resolved_calls.insert(span, resolution);
        }
        Ok(())
    }


    /// Detect constrained polymorphic functions after generalization.
    ///
    /// A function is constrained if its generalized scheme has non-empty constraints.
    /// These functions are stored with `ConstrainedFn` in their DefKind.
    pub(super) fn detect_constrained_fns(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
    ) -> HashSet<Symbol> {
        // Constrained functions are eagerly marked in pass2_check_bodies
        // by checking DefKind::UserFn { fn_state: UserFnState::Constrained(..) }.
        let mut names = HashSet::new();

        for defn in defns {
            let r = self.current_symbol_table(state);
            if let Some(ModuleEntry::Def { kind, .. }) = r.view().lookup(&defn.name)
                && let DefKind::UserFn { fn_state: UserFnState::Constrained(_) } = kind.as_ref()
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
    /// Allocates a fresh `Type::Var`, resolves each `TraitRef` to its
    /// `FQTraitName` (a qualified ref names its module directly; a bare ref is
    /// resolved via the current-module-or-prelude chain), and records the
    /// (var, trait) pairs on `state.active_constraints`. `generalize` then lifts
    /// these onto the defn's `Scheme.constraints` when the var is quantified.
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
    ) -> Result<Type, CranelispError> {
        let (var_ty, var_id) = self.fresh_var_id();
        for tref in bounds {
            let home = match &tref.module {
                // Qualified ref (`:fmt/Display`) names its module directly.
                Some(m) => m.clone(),
                // Bare ref (`:Display`) resolves via current-module-or-prelude.
                None => self
                    .resolve_trait(state, tref.name.as_ref(), span)
                    .map_err(CranelispError::from)?,
            };
            let fqtn = cranelisp_types::FQTraitName::new(home, tref.name.clone());
            state.active_constraints.add(var_id, fqtn);
        }
        Ok(var_ty)
    }


    /// Create fresh type variables for a function's parameters and return type,
    /// respecting any annotations, and register the signature in the symbol table.
    ///
    /// Returns `(param_types, return_type)` for use in body checking.
    /// Shared by the per-form registration path (`check_form_register_single_defn`)
    /// and the multi-sig variant registration to prevent the two paths from
    /// diverging as rings add complexity.
    pub(super) fn register_defn_signature(
        &self,
        state: &mut CheckState,
        defn: &Defn,
    ) -> Result<(Vec<Type>, Type, HashMap<Symbol, TypeId>), CranelispError> {
        // Fast path for trait impl (mangled) methods: if this symbol already
        // has a Def entry with `ast: Some(_)` and a concrete scheme (no free
        // vars / constraints), AND its name matches the trait-impl mangled
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
            if let Some(ModuleEntry::Def { scheme, ast: Some(_), .. }) =
                r.view().lookup(&defn.name)
                && scheme.type_vars.is_empty()
                && scheme.constraints.is_empty()
                && let Type::Fn(param_types, ret_ty) = &scheme.ty
            {
                return Ok((param_types.clone(), (**ret_ty).clone(), HashMap::new()));
            }
        }

        // ONE var scope for the whole signature (spec §3.3.1 [S109 W6.3]): a
        // free lowercase type var the author writes in a param annotation mints a
        // fresh FLEXIBLE var carrying that display name, and a repeated name
        // (`[:a x :a y]`) resolves to the SAME var so x and y unify. This map is
        // built fresh PER CALL — multi-arity clauses each go through a separate
        // `register_defn_signature` (via their own `{name}__vN` internal defn,
        // see `check_form_register_multi_sig`), so `:a` in one clause is
        // independent of `:a` in another (fresh scope per clause). It is RETURNED
        // to the caller and threaded (via `accumulator.defn_var_scopes`) into
        // Pass-2 body checking so a body/nested-`fn` `:a` CO-REFERS to the param's
        // var (§3.3.1 co-reference; 0588). A bare written var carries ONLY a name
        // — it is NOT rigid; rigidity lives on the constraint path, and
        // `check_defn_body` seeds `rigid_vars` from asserted-constraint param
        // vars, NOT from this map's values.
        let mut var_map: HashMap<Symbol, TypeId> = HashMap::new();
        let mut param_types = Vec::new();
        for (_name, ann) in defn.params().iter() {
            let param_ty = match ann {
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
                        ann, &mut var_map, &state.current_module, defn.span,
                    ) {
                        // A bare param-annotation var is FLEXIBLE and carries only
                        // its display name (§3.3.1 [S109 W6.3]); the shared scope
                        // (`var_map`) threads it to Pass-2 for CO-REFERENCE, not
                        // rigidity — `check_defn_body` seeds `rigid_vars` from
                        // asserted-constraint param vars, not from `var_map`.
                        Ok(ty) => ty,
                        // Try-type-then-trait (spec §3.9.3, S86 D4). A SINGLE
                        // annotation `:Eq a` is ambiguous between a concrete-type
                        // annotation and a single trait bound. The frontend leaves
                        // a run-of-length-1 as the resolved `TypeExpr::Named`
                        // (`annotation_run_carrier`), delegating disambiguation to
                        // here: when no TYPE with that name exists, resolve it as a
                        // trait constraint. We funnel it through `resolve_bound_param`
                        // (the same single-trait → fresh constrained var path as a
                        // `Bounds([..])` of length 1) iff the annotation's head
                        // resolves as a trait; otherwise the original type error
                        // (the genuine "neither type nor trait" case) propagates.
                        Err(type_err) => {
                            match single_trait_bound_from_annotation(ann) {
                                Some(tref)
                                    if self
                                        .resolve_trait(state, tref.name.as_ref(), defn.span)
                                        .is_ok() =>
                                {
                                    self.resolve_bound_param(
                                        state,
                                        std::slice::from_ref(&tref),
                                        defn.span,
                                    )?
                                }
                                _ => return Err(type_err.into()),
                            }
                        }
                    }
                }
                None => self.fresh_var(),
            };
            param_types.push(param_ty);
        }
        let ret_ty = self.fresh_var();

        let fn_type = Type::Fn(param_types.clone(), Box::new(ret_ty.clone()));
        let scheme = mono(fn_type);

        // Upsert: preserve existing ast AND code if the symbol is being
        // redefined (REPL Additive mode, module reload, or trait impl method
        // re-registration). Preserving ast prevents double-checking of trait
        // impl methods that were already type-checked by check_impl_method.
        //
        // **Deferred GOT-slot allocation (S83, FIXME 0356/0357, Principle 20;
        // amends Decision 0035).** Pass-1 NO LONGER allocates a slot here. With
        // callability now a `DefKind::UserFn` property (`UserFnState`), Pass-1
        // cannot yet know whether this fn is `Concrete` (slotted) or
        // `Constrained` (slot-less) — Pass-2 constraint detection runs later.
        // So Pass-1 registers `UserFnState::NotDetermined` (slot-less by
        // construction; nothing may call an as-yet-undetermined fn). The slot is
        // allocated at the determination point in the unconstrained Pass-2 arm
        // (`check_form_body` / `check_form_body_multi_sig`), where the
        // redefinition slot-reuse carry-forward (below) now lives. See the
        // `UserFnState` rustdoc "Timing-wall resolution".
        //
        // Sprint 58 Wave 3b (Decision 35 / 31): preserving `code` is load-bearing
        // for failed-redefinition recovery. Pre-Wave-3b, `Arc<Jit>` lived in
        // `SharedState.kept_jits` (session-level); replacing the entry was a
        // pointer-swap and the JIT pages stayed alive at session level. Wave 3b
        // moves `Arc<Jit>` retention onto `Code::Jit` per-entry — replacing the
        // entry with `code: None` drops the Arc, and if no other entry referenced
        // it, the Jit's `Drop` calls `free_memory()` and the GOT slot's old
        // pointer (still in place during typecheck) becomes invalid. If the
        // redefinition then fails (type error), snapshot/restore reverts the
        // entry's keys but the GOT slot is already pointing at freed pages —
        // a subsequent call to the original defn segfaults.
        //
        // Carrying the existing `code` forward through registration preserves
        // the Arc; on success, codegen overwrites it with the new `Code::Jit`;
        // on failure, restore keeps the carried-forward (original) `code`,
        // and the GOT slot remains valid because the Arc never dropped.
        let mut st = self.current_symbol_table_mut(state);
        let (existing_ast, existing_code) = st.get(defn.name.as_ref())
            .map(|e| match e {
                ModuleEntry::Def { ast, code, .. } => (ast.clone(), code.clone()),
                _ => (None, None),
            })
            .unwrap_or((None, None));

        // NOT converted to `ModuleEntry::def(...)` (FIXME 0241): this site
        // carries `code: existing_code` forward to preserve the existing
        // `Code::Jit` Arc across REPL redefinition (use-after-free guard, see
        // the block comment above). `DefBuilder` deliberately has no `code`
        // setter (`code` is runtime state, written downstream), so the builder
        // cannot express this entry — the struct literal is retained here.
        st.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: defn.params().iter().map(|(n, _)| n.clone()).collect(),
                kind: Box::new(DefKind::UserFn {
                    fn_state: UserFnState::NotDetermined,
                }),
                callees: Vec::new(),
                trait_origin: None,
                seq: 0,
                ast: existing_ast,
                // Pass-1 `NotDetermined` entry (pre-body-check) — never a codegen
                // target, so no concrete-boundary view yet. The mono/body-check
                // seam populates `codegen_view` once the body is concrete (S84
                // concrete-boundary arc, Phase 2b/3 — /dev(typecheck)).
                codegen_view: None,
                code: existing_code,
                value_use: false,
            },
        );

        Ok((param_types, ret_ty, var_map))
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
    ) -> Result<(), CranelispError> {
        // Enumerate eligible Polymorphic test-fn names + their stored variant +
        // the Option FQTypeName from their result type. Read-only scan first (no
        // &mut overlap), then recheck + re-register.
        let candidates: Vec<(Symbol, DefnVariant, cranelisp_types::FQTypeName)> = {
            let st = self.current_symbol_table(state);
            st.view()
                .iter()
                .filter_map(|(name, entry)| {
                    if !name.as_ref().starts_with("test-") {
                        return None;
                    }
                    let ModuleEntry::Def { kind, ast, .. } = entry else {
                        return None;
                    };
                    let DefKind::UserFn {
                        fn_state: UserFnState::Polymorphic(pf),
                    } = kind.as_ref()
                    else {
                        return None;
                    };
                    // Must be nullary with a result-only free var — shape
                    // `(Fn [] (Option a))` (a is unbound). A concrete-result test
                    // fn is already `Concrete{slot}` (not `Polymorphic`), so it
                    // never reaches here; a param-polymorphic def has params.
                    let Type::Fn(params, ret) = &pf.scheme.ty else {
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
                    ast.clone().map(|variant| (name.clone(), variant, fqtn.clone()))
                })
                .collect()
        };

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
            // `Polymorphic` entry untouched — discovery's eligibility filter will
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

            // S84 Phase-3 (FIXME 0392): this minted test-fn root is a
            // codegen-bound `Concrete` entry — build its concrete-boundary
            // `MonoExpr` view from the fully-annotated, subst-resolved body. The
            // discovery contract pins it to `(Fn [] (Option String))`, so the
            // body (`None`) is concrete and `from_expr` succeeds (best-effort
            // per `build_concrete_codegen_view`).
            //
            // The check-run pairing rule (S110 W3.1, FIXME 0622,
            // `backend-keyed-consumer.md` §1.1.3): build the view from the SAME
            // `MethodResolutions` instance the per-root `recheck_body_for_mono`
            // above populated (`resolutions`), NOT the enclosing
            // `state.method_resolutions`. Correct-by-reach when the root's mint
            // is same-run as its form check; the cross-run retry edge (a root
            // left `Polymorphic` by a failed recheck, re-attempted in a later
            // run) reads a map WITHOUT the body's spans off the enclosing map —
            // the sibling cell of the mono-instance 0622 gap.
            let codegen_view = concrete_defn
                .variants
                .first()
                .and_then(|v| build_concrete_codegen_view(&name, v, &resolutions.pattern_ctors, &resolutions.resolved_targets));

            // Re-register the entry under the BARE name as `Concrete{slot}`,
            // carrying the concrete scheme + annotated body. Allocate a fresh
            // slot (the `Polymorphic` original had none).
            let concrete_scheme = mono(Type::Fn(vec![], Box::new(option_string.clone())));
            let mut st = self.current_symbol_table_mut(state);
            let got_slot = st
                .allocate_got_slot()
                .map_err(crate::result::got_exhausted_error)?;
            if let Some(ModuleEntry::Def { scheme, kind, ast, codegen_view: cv, .. }) =
                st.symbols.get_mut(&name)
            {
                *scheme = concrete_scheme;
                **kind = DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
                };
                *ast = concrete_defn.variants.into_iter().next();
                *cv = codegen_view;
            }
        }
        Ok(())
    }

}
