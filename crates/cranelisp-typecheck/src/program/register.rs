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
            let codegen_view = match concrete_defn.variants.first() {
                Some(v) => build_concrete_codegen_view(
                    &name,
                    v,
                    &resolutions.pattern_ctors,
                    &resolutions.var_refs,
                    &resolutions.apply_refs,
                )?,
                None => None,
            };

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

#[cfg(test)]
mod tests;
