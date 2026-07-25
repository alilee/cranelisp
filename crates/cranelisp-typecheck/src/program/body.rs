use super::*;

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Pass 2 (CheckBody) dispatch: check function bodies, generalize, detect constraints.
    pub(super) fn check_form_body(
        &self,
        state: &mut CheckState,
        form: &TopLevel,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        // FIXME 0488 sig c: settle forward-reference chains in already-determined
        // polymorphic templates so this form's body is checked against tied
        // schemes, not the stale under-tied ones a 0344 writeback froze before a
        // forward-referenced helper's own body ran.
        self.resettle_polymorphic_schemes(state, accumulator);
        match form {
            TopLevel::Defn(defn) => {
                if defn.is_multi_sig() {
                    self.check_form_body_multi_sig(state, defn, accumulator)
                } else {
                    self.check_form_body_single_defn(state, defn, accumulator)
                }
            }
            // Non-Defn forms are no-ops in CheckBody pass.
            _ => Ok(FormCheckResult::empty()),
        }
    }

    /// Check a single-sig defn body (Pass 2).
    ///
    /// Checks the body, does eager constrained-fn detection, and scans
    /// for monomorphisation call sites.
    pub(super) fn check_form_body_single_defn(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        // Skip body re-check for trait impl (mangled) defns already type-checked
        // by `check_impl_method` during Pass 1. Re-checking with fresh type vars
        // causes spurious constrained-fn detection → null GOT → SIGSEGV.
        //
        // Gated on the `Trait.method$Type` name pattern to avoid false positives
        // on REPL-transient `__expr` or regular user defns whose ast was
        // annotated by a prior evaluation.
        if is_trait_impl_mangled_name(defn.name.as_ref()) {
            let r = self.current_symbol_table(state);
            let v = r.view();
            if let Some(ModuleEntry::Def { ast: Some(_), .. }) = v.lookup(&defn.name) {
                return Ok(FormCheckResult::empty());
            }
        }

        let (param_types, ret_ty) =
            accumulator.defn_type_vars.get(&defn.name).ok_or_else(|| {
                CranelispError::TypeError {
                    message: format!("internal: missing type vars for {}", defn.name),
                    location: ErrorLocation::from_span(defn.span),
                }
            })?;
        // The Pass-1 written-var scope threaded through to the body check
        // (spec §3.3 [S109]; empty when no written type vars — 0588).
        let var_scope = accumulator
            .defn_var_scopes
            .get(&defn.name)
            .cloned()
            .unwrap_or_default();

        // Snapshot method_resolutions and expr_types sizes so we can extract
        // just the new entries added during this form's checking.
        let mr_before: HashSet<Span> = state
            .method_resolutions
            .resolved_calls
            .keys()
            .copied()
            .collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();
        let ufr_before: HashSet<Span> = state.user_fn_refs.keys().copied().collect();

        self.check_defn_body(state, defn, param_types, ret_ty, var_scope)
            .map_err(|e| enrich_macro_clause_resolution_error(defn.name.as_ref(), e))?;
        self.resolve_deferred_trait_calls(state, defn.body())?;
        self.resolve_value_position_trait_methods(state, defn.body(), false)?;

        // Per-defn post-passes: resolve auto-curry accumulated during this
        // defn's body check. Overload resolution is deferred to finalize
        // because resolved_overloads is populated by resolve_multi_sig_overloads.
        // DEFERRABLE (S115 W4): this seam is PRE-settlement — a later form's call
        // site may still pin this body's operand types — so a trait operator with
        // no resolvable impl yet is held for the settled finalize drain instead of
        // transporting its declaration FQ as a dispatch carrier.
        self.resolve_auto_curry(state, AutoCurryDrain::Deferrable);

        // Eager constrained-fn detection + the S83 determination point: finalise
        // this defn's `fn_state` (Concrete{slot} / Constrained / Polymorphic)
        // from its trial scheme (`program-decomposition.md` §2.2).
        let constrained_fn =
            self.determine_fn_state(state, defn, param_types, ret_ty, accumulator)?;

        // Extract new method resolutions and expr types added during this form
        let mut form_mr = HashMap::new();
        for (span, res) in &state.method_resolutions.resolved_calls {
            if !mr_before.contains(span) {
                form_mr.insert(*span, res.clone());
            }
        }
        let mut form_et = HashMap::new();
        for (span, ty) in &state.expr_types {
            if !et_before.contains(span) {
                form_et.insert(*span, ty.clone());
            }
        }

        // Per-defn AST annotation + concrete-boundary `codegen_view` writeback.
        self.annotate_and_writeback_single_defn(state, defn, &form_et, &form_mr)?;

        // Harvest call graph edges (Decision 21 + FIXME 0470/0472): the
        // ResolvedCall channel + the user-fn references recorded during this
        // form's body inference — call- and value-position alike, uniform
        // carrier. ONE shared helper across all body-check seams.
        let call_graph_edges = self.harvest_callee_edges(state, &defn.name, &form_mr, &ufr_before);

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            pattern_ctors: state.method_resolutions.pattern_ctors.clone(),
            var_refs: state.method_resolutions.var_refs.clone(),
            apply_refs: state.method_resolutions.apply_refs.clone(),
            expr_types: form_et,
            constrained_fn,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
            call_graph_edges,
        })
    }

    /// The S83 determination point (FIXME 0356/0357, Principle 20; deferred
    /// GOT-slot allocation) extracted from `check_form_body_single_defn`
    /// (`program-decomposition.md` §2.2). Eagerly detects constrained-ness from
    /// this defn's trial scheme and finalises its `fn_state`: unconstrained-
    /// concrete → `Concrete{got_slot}` (slot reused on REPL redef); constrained
    /// → slot-less `Constrained`; unconstrained-but-non-concrete → slot-less
    /// `Polymorphic`. Returns the defn name iff it was marked constrained.
    pub(super) fn determine_fn_state(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<Option<Symbol>, CranelispError> {
        // Eager constrained-fn detection
        let fn_type = Type::Fn(
            param_types
                .iter()
                .map(|t| self.apply_subst(state, t))
                .collect(),
            Box::new(self.apply_subst(state, ret_ty)),
        );
        let trial_scheme = self.generalize(state, &fn_type);

        // FIXME 0344 — generalize-before-cross-defn-use (PURE-parametric only).
        // Write the generalized scheme back to this defn's symbol-table entry
        // NOW, immediately after its body is checked, so a later-source sibling
        // in the same cluster that calls it instantiates a FRESH (polymorphic)
        // copy rather than monomorphising the defn's own still-`mono` Pass-1
        // vars. Without this, a fold helper threading a polymorphic accumulator
        // distinct from the element type (`vec-reduce`) collapses `b`, `a`, and
        // `Vec` onto one var when a sibling Vec-accumulator use is checked.
        //
        // Gated on `trial_scheme.constraints.is_empty()`: this writeback is for
        // PURE parametric polymorphism (the 0344 fold shape). A *constrained*
        // fn (one whose scheme carries trait constraints) MUST keep its `mono`
        // Pass-1 entry so a same-program caller monomorphises it through the
        // shared substitution (the established constrained-fn-vs-same-program
        // behaviour the monomorphisation pipeline depends on); generalizing a
        // constrained fn here would suppress that call-site pinning. The
        // recursion-name binding itself stays `mono(fn_type)` (set in
        // `check_defn_body`) in both cases — we do NOT make the self-reference
        // polymorphic (polymorphic recursion is undecidable in HM). This
        // writeback is idempotent with `finalize`'s Phase-2 writeback
        // (`finalize_check_result_inner` ~line 1109): both recompute from the
        // same `accumulator.defn_type_vars` source vars + the same global
        // `subst`, so the later pass writes the identical scheme.
        if trial_scheme.constraints.is_empty()
            && let Some(ModuleEntry::Def { scheme, .. }) = self
                .current_symbol_table_mut(state)
                .symbols
                .get_mut(&defn.name)
        {
            *scheme = trial_scheme.clone();
        }

        // Eager constrained-fn detection reads from the trial scheme (regression
        // guard (a): constraint detection still keys off `trial_scheme`, not the
        // entry's scheme field).
        //
        // **The determination point (S83, FIXME 0356/0357, Principle 20;
        // deferred GOT-slot allocation).** Pass-1 registered this fn as
        // `UserFnState::NotDetermined` (slot-less). Now that body-check has run
        // and constraints are known, we finalise the `fn_state`:
        //
        // - **Unconstrained → `Concrete { got_slot }`.** Allocate the slot HERE,
        //   reusing a prior concrete entry's slot on REPL redefinition (the
        //   `existing_callable_slot` carry-forward — orphaning the live GOT
        //   pointer would be a use-after-free; see the helper rustdoc). A
        //   constrained→concrete redef reads `None` (the prior constrained
        //   template carried no slot) and allocates fresh.
        // - **Constrained → `Constrained(cf)`.** Construct the slot-less template
        //   directly (replaces the retired `mark_constrained_template` flip +
        //   `assert_well_formed` phantom-slot guard — there is no sibling slot
        //   field to clear or assert about now). A concrete→constrained redef
        //   drops the old slot; the constrained template is never call-resolved
        //   so there is no live GOT pointer to orphan (no UAF).
        if !trial_scheme.constraints.is_empty() {
            if let Some(entry) = self
                .current_symbol_table_mut(state)
                .symbols
                .get_mut(&defn.name)
                && let ModuleEntry::Def { kind, .. } = entry
            {
                let cf = ConstrainedFn {
                    variant: defn.variants[0].clone(),
                    scheme: trial_scheme,
                };
                *kind = Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Constrained(Box::new(cf)),
                });
            }
            Ok(Some(defn.name.clone()))
        } else if !trial_scheme.ty.is_concrete() && defn.name.as_ref() != "__expr" {
            // S84 Wave 1b (FIXME 0374/0378, Principle 20): the slot gate is now
            // TOTAL — `slot ⟺ is_concrete()`, with NO `monomorphisable-from-
            // params` carve-out. ANY unconstrained non-concrete def (including a
            // RESULT-ONLY-var def: `(defn test-x [] None)` → `(Fn [] (Option a))`,
            // `(defn empty [] [])` → `(Fn [] (Vec a))`) is slot-less `Polymorphic`.
            // The former carve-out kept result-only-var defs `Concrete`-with-a-slot
            // so `discover_test_names` could find them; test fns are now explicit
            // monomorphisation ROOTS (`register_test_fn_mono_roots` in
            // `pass4_monomorphise`), which mint a concrete `(Fn [] (Option String))`
            // instance under the bare name — so a degenerate test fn is found via
            // that concrete instance's slot, not the polymorphic original.
            //
            // **`__expr` is still excluded.** A synthetic top-level-expression
            // defn is a VALUE to evaluate, never a reusable polymorphic template,
            // and the REPL/`--run` driver requires its GOT slot to invoke it. A
            // residual `Type::Var` in an `__expr` result is either a transient
            // unresolved-multi-sig-dispatch shape (concrete at runtime) or a bare
            // polymorphic value (displayed via introspection per §3.11.2, never
            // compiled to a runtime value). Either way it stays `Concrete` here.
            //
            // A def carrying a residual `Type::Var` is NOT directly callable as a
            // value (only its concrete mono instances are), so it is slot-less by
            // construction — the `Polymorphic` arm, a sibling to `Constrained`.
            // This forecloses the leak where a generic-unconstrained def took a
            // `Concrete` slot while carrying a `Type::Var`, reaching
            // `classify(Type::Var)` → the unsound `<1024` RC guard → the
            // `(Box a)`-through-HOF SIGSEGV. Only `pass4_monomorphise` instances
            // (concrete) are slotted. Drops any prior concrete slot (the redef
            // carry-forward is moot — a `Polymorphic` template is never
            // call-resolved, so no live GOT pointer is orphaned).
            if let Some(entry) = self
                .current_symbol_table_mut(state)
                .symbols
                .get_mut(&defn.name)
                && let ModuleEntry::Def { kind, .. } = entry
            {
                let pf = ParametricFn {
                    variant: defn.variants[0].clone(),
                    scheme: trial_scheme,
                };
                *kind = Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Polymorphic(Box::new(pf)),
                });
            }
            Ok(None)
        } else {
            // Unconstrained AND concrete: allocate (or reuse) the slot and pin
            // `Concrete`.
            // Prefer the Pass-1-captured redefinition slot (the prior concrete
            // entry's slot, stashed before Pass-1 overwrote it with
            // NotDetermined). Fall back to a same-call concrete slot if one
            // somehow already exists, else allocate fresh.
            let mut st = self.current_symbol_table_mut(state);
            let reuse = accumulator
                .redef_slots
                .get(&defn.name)
                .copied()
                .or_else(|| existing_callable_slot(&st, defn.name.as_ref()));
            let got_slot = match reuse {
                Some(s) => s,
                None => st
                    .allocate_got_slot()
                    .map_err(crate::result::got_exhausted_error)?,
            };
            // Slot-reuse invariant (replaces the retired `assert_well_formed`):
            // a reused slot is below the high-water mark; a freshly allocated one
            // equals it minus one. Either way it is a valid allocated index.
            debug_assert!(
                got_slot < st.next_got_slot,
                "determination-point got_slot {got_slot} must be within the \
                 allocated range (next_got_slot = {})",
                st.next_got_slot,
            );
            if let Some(ModuleEntry::Def { kind, .. }) = st.symbols.get_mut(&defn.name) {
                *kind = Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Concrete {
                        got_slot,
                        mode_summary: None,
                    },
                });
            }
            Ok(None)
        }
    }

    /// Per-defn AST annotation + concrete-boundary `codegen_view` writeback for
    /// a single-sig defn, extracted from `check_form_body_single_defn`
    /// (`program-decomposition.md` §2.2). Clones the defn, annotates it from the
    /// per-form side maps + subst, and writes `ast` (+ `codegen_view` for a
    /// `Concrete{slot}` codegen target) to its symbol-table entry.
    pub(super) fn annotate_and_writeback_single_defn(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        form_et: &HashMap<Span, Type>,
        form_mr: &HashMap<Span, ResolvedCall>,
    ) -> Result<(), CranelispError> {
        let resolved_et: HashMap<Span, Type> = form_et
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();
        let mut annotated = defn.clone();
        annotate_defn_from_maps(&mut annotated, &resolved_et, form_mr);
        apply_subst_to_defn(&state.subst, &mut annotated);

        // S84 Phase-3 (FIXME 0392): populate the concrete-boundary
        // `codegen_view` for an ordinary CONCRETE single-sig defn (e.g.
        // `main`, `(defn f [x] (+ x 1))` at a concrete instantiation). Only
        // a `Concrete` entry is a `compile_to_module` codegen target —
        // `Polymorphic`/`Constrained` templates (and any non-`Def`) get no
        // view (they are mono SOURCES, excluded by `defined_symbols()`). The
        // view is built from the SAME fully-annotated, subst-resolved body
        // the `ast` carries, via `MonoExpr::from_expr`.
        //
        // **The validation payoff (FIXME 0392 §VALIDATION):** a
        // `Concrete{slot}` defn that passed body-check (§3.11.1) has a fully
        // concrete body ⇒ `from_expr` MUST succeed. A failure on a
        // legitimate concrete defn is a real §3.11.1-position gap — surfaced
        // HERE as the unified ambiguity / could-not-monomorphise error
        // (NOT silently set to `None`, which would later trip the Phase-3
        // backend backstop).
        let is_concrete_codegen_target = matches!(
            self.current_symbol_table(state).view().lookup(&defn.name),
            Some(ModuleEntry::Def {
                kind,
                ..
            }) if matches!(
                kind.as_ref(),
                DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
            )
        );
        let codegen_view = if is_concrete_codegen_target {
            match annotated.variants.first() {
                Some(variant) => build_concrete_codegen_view(
                    &defn.name,
                    variant,
                    &state.method_resolutions.pattern_ctors,
                    &state.method_resolutions.var_refs,
                    &state.method_resolutions.apply_refs,
                )?,
                None => None,
            }
        } else {
            None
        };

        if let Some(ModuleEntry::Def {
            ast,
            codegen_view: cv,
            ..
        }) = self
            .current_symbol_table_mut(state)
            .symbols
            .get_mut(&defn.name)
        {
            // S69 Submission 35: `ast: Option<DefnVariant>` (the single
            // meaningful payload; multi-sig decomposition already split
            // into per-mangled-name Defs upstream of this point).
            *ast = annotated.variants.into_iter().next();
            *cv = codegen_view;
        }
        Ok(())
    }

    /// Check a multi-sig defn's variant bodies (Pass 2).
    pub(super) fn check_form_body_multi_sig(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let mr_before: HashSet<Span> = state
            .method_resolutions
            .resolved_calls
            .keys()
            .copied()
            .collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();
        let ufr_before: HashSet<Span> = state.user_fn_refs.keys().copied().collect();

        // Check each variant body
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            let (param_types, ret_ty) =
                accumulator
                    .defn_type_vars
                    .get(&internal_name)
                    .ok_or_else(|| CranelispError::TypeError {
                        message: format!(
                            "internal: missing type vars for multi-sig variant {}",
                            internal_name
                        ),
                        location: ErrorLocation::from_span(variant.span),
                    })?;
            // Each arity clause is a DISJOINT written-var scope (§5.1.2 clause
            // independence; spec §3.3 [S109], u3) — clause i's rigid `:a` is a
            // distinct skolem from clause j's.
            let var_scope = accumulator
                .defn_var_scopes
                .get(&internal_name)
                .cloned()
                .unwrap_or_default();

            // Snapshot for per-variant delta extraction
            let variant_mr_before: HashSet<Span> = state
                .method_resolutions
                .resolved_calls
                .keys()
                .copied()
                .collect();
            let variant_et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

            // Build a temporary single-variant defn for body checking
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

            self.check_defn_body(state, &internal_defn, param_types, ret_ty, var_scope)?;
            self.resolve_deferred_trait_calls(state, internal_defn.body())?;
            self.resolve_value_position_trait_methods(state, internal_defn.body(), false)?;

            // Per-variant post-passes (auto-curry only; overloads deferred to
            // finalize). DEFERRABLE for the same pre-settlement reason as the
            // single-sig seam above.
            self.resolve_auto_curry(state, AutoCurryDrain::Deferrable);

            // Per-variant AST annotation
            {
                let variant_mr: HashMap<Span, ResolvedCall> = state
                    .method_resolutions
                    .resolved_calls
                    .iter()
                    .filter(|(span, _)| !variant_mr_before.contains(span))
                    .map(|(span, res)| (*span, res.clone()))
                    .collect();
                let variant_et: HashMap<Span, Type> = state
                    .expr_types
                    .iter()
                    .filter(|(span, _)| !variant_et_before.contains(span))
                    .map(|(span, ty)| (*span, apply(&state.subst, ty)))
                    .collect();
                let mut annotated = internal_defn.clone();
                annotate_defn_from_maps(&mut annotated, &variant_et, &variant_mr);
                apply_subst_to_defn(&state.subst, &mut annotated);
                if let Some(ModuleEntry::Def { ast, .. }) = self
                    .current_symbol_table_mut(state)
                    .symbols
                    .get_mut(&internal_name)
                {
                    // S69 Submission 35 narrowing.
                    *ast = annotated.variants.into_iter().next();
                }
            }

            // Eager constrained-fn detection for variant
            let fn_type = Type::Fn(
                param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let trial_scheme = self.generalize(state, &fn_type);

            // FIXME 0344 — generalize-before-cross-defn-use, mirrored at the
            // multi-sig variant site (PURE-parametric only): write the
            // generalized scheme back to the variant's `__vN` entry now so a
            // sibling that references it sees a polymorphic, instantiable view.
            // A constrained variant keeps its `mono` entry for same-program
            // call-site monomorphisation. Idempotent with `finalize` Phase 2.
            if trial_scheme.constraints.is_empty()
                && let Some(ModuleEntry::Def { scheme, .. }) = self
                    .current_symbol_table_mut(state)
                    .symbols
                    .get_mut(&internal_name)
            {
                *scheme = trial_scheme.clone();
            }

            // Determination point for this multi-sig variant's `__vN` entry
            // (S83, FIXME 0356/0357, Principle 20; deferred GOT-slot
            // allocation). Mirrors the single-sig site: constrained → slot-less
            // `Constrained(cf)`; unconstrained → allocate (or reuse) the slot
            // and pin `Concrete`. The `__vN` internal names are synthesised
            // fresh per multi-sig form, so `existing_callable_slot` reuse only
            // fires on REPL redefinition of the same multi-sig defn.
            if !trial_scheme.constraints.is_empty() {
                if let Some(entry) = self
                    .current_symbol_table_mut(state)
                    .symbols
                    .get_mut(&internal_name)
                    && let ModuleEntry::Def { kind, .. } = entry
                {
                    let cf = ConstrainedFn {
                        variant: internal_defn
                            .variants
                            .into_iter()
                            .next()
                            .expect("internal_defn constructed with exactly one variant above"),
                        scheme: trial_scheme,
                    };
                    *kind = Box::new(DefKind::UserFn {
                        fn_state: UserFnState::Constrained(Box::new(cf)),
                    });
                }
            } else if !trial_scheme.ty.is_concrete() {
                // S84 Wave 1b (FIXME 0374/0378, Principle 20): a multi-sig
                // *variant* whose finalised type still carries ANY `Type::Var`
                // (parameter OR result position) is non-concrete and
                // trait-unconstrained → slot-less `Polymorphic`, NOT
                // `Concrete{slot}`. The slot gate is TOTAL — slot ⟺ concrete,
                // with no `monomorphisable-from-params` carve-out.
                if let Some(entry) = self
                    .current_symbol_table_mut(state)
                    .symbols
                    .get_mut(&internal_name)
                    && let ModuleEntry::Def { kind, .. } = entry
                {
                    let pf = ParametricFn {
                        variant: internal_defn
                            .variants
                            .into_iter()
                            .next()
                            .expect("internal_defn constructed with exactly one variant above"),
                        scheme: trial_scheme,
                    };
                    *kind = Box::new(DefKind::UserFn {
                        fn_state: UserFnState::Polymorphic(Box::new(pf)),
                    });
                }
            } else {
                let mut st = self.current_symbol_table_mut(state);
                let reuse = accumulator
                    .redef_slots
                    .get(&internal_name)
                    .copied()
                    .or_else(|| existing_callable_slot(&st, internal_name.as_ref()));
                let got_slot = match reuse {
                    Some(s) => s,
                    None => st
                        .allocate_got_slot()
                        .map_err(crate::result::got_exhausted_error)?,
                };
                debug_assert!(
                    got_slot < st.next_got_slot,
                    "multi-sig determination-point got_slot {got_slot} must be \
                     within the allocated range (next_got_slot = {})",
                    st.next_got_slot,
                );
                if let Some(ModuleEntry::Def { kind, .. }) = st.symbols.get_mut(&internal_name) {
                    *kind = Box::new(DefKind::UserFn {
                        fn_state: UserFnState::Concrete {
                            got_slot,
                            mode_summary: None,
                        },
                    });
                }
            }
        }

        // Extract new method resolutions and expr types
        let mut form_mr = HashMap::new();
        for (span, res) in &state.method_resolutions.resolved_calls {
            if !mr_before.contains(span) {
                form_mr.insert(*span, res.clone());
            }
        }
        let mut form_et = HashMap::new();
        for (span, ty) in &state.expr_types {
            if !et_before.contains(span) {
                form_et.insert(*span, ty.clone());
            }
        }

        // Harvest call graph edges for the variants (Decision 21 + FIXME
        // 0470/0472) — ONE shared helper across all body-check seams.
        // Multi-sig variant edges are attributed to the base defn name since
        // the mangled names aren't known until overload resolution in finalize.
        let call_graph_edges = self.harvest_callee_edges(state, &defn.name, &form_mr, &ufr_before);

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            pattern_ctors: state.method_resolutions.pattern_ctors.clone(),
            var_refs: state.method_resolutions.var_refs.clone(),
            apply_refs: state.method_resolutions.apply_refs.clone(),
            expr_types: form_et,
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
            call_graph_edges,
        })
    }

    /// Check a single function definition body.
    ///
    /// `written_var_scope` is the definition's Pass-1 written-type-var scope
    /// (name → flexible `TypeId`, spec §3.3.1 [S109]); it is installed as the
    /// active `state.written_var_scope` for the duration of this body so a
    /// body/nested-`fn` `:a` CO-REFERS to the param's var (§3.3.1 co-reference,
    /// the 0588 seam). A bare written var is otherwise an ORDINARY FLEXIBLE
    /// inference var: the body MAY pin it to a concrete type (never an error —
    /// §3.3.1 MUST (a), rows 2/4/11). Rigidity lives ONLY on the CONSTRAINT
    /// path: `state.rigid_vars` is seeded (per body) from the param vars that
    /// ALREADY carry an asserted constraint at Pass-2 entry (`:C x`, recorded by
    /// `resolve_bound_param` in Pass-1), so the body narrowing such a var to a
    /// concrete type is a skolem escape (§3.3.2 MUST (b), row 6). All per-body
    /// inference state (scope, rigid set, lambda-written-var accumulator, scope
    /// frame) is torn down on EVERY exit — success or error — so a
    /// forward-referencing sibling instantiates the (now quantified) var freshly
    /// and no state bleeds across a failed body-check (the error-safe
    /// save/restore discipline, mirroring `recheck_body_for_mono`; FIXME 0599).
    pub(super) fn check_defn_body(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
        written_var_scope: HashMap<Symbol, TypeId>,
    ) -> Result<(), CranelispError> {
        // Binder provenance: the defn form span every param + the recursion-self
        // binding share (S114 `VarRef::Local`).
        self.push_scope(state, defn.span);

        // Activate the definition's written-var scope + the constraint-abstract
        // rigid set (spec §3.3.1–§3.3.2 [S109]). Two independent pieces:
        //
        // - `written_var_scope` (name → `TypeId`) threads LEXICAL CO-REFERENCE:
        //   every occurrence of one bare written name within the definition —
        //   including inside nested `fn` closures (`infer_lambda` shares it) —
        //   resolves to the SAME var (`[:a x :a y]` ties x/y; a body `:a`
        //   co-refers to a param `:a`). This is ALL a bare written var does; it
        //   is an ordinary FLEXIBLE inference var otherwise, and the body MAY pin
        //   it to a concrete type (never an error — §3.3.1 MUST (a), rows 2/4/11).
        //
        // - `rigid_vars` holds ONLY the ASSERTED-constraint param vars (`:C x`):
        //   a constraint at a parameter position is held abstract over `C` for
        //   the body-check, so the body narrowing it to a concrete type — by
        //   ascription or by use — is a skolem escape (§3.3.2 MUST (b), row 6).
        //   These are exactly the param `Type::Var`s that ALREADY carry a
        //   constraint at Pass-2 entry: `resolve_bound_param` recorded the
        //   assertion during Pass-1 signature registration. A BARE `:a` param
        //   that merely ACCRUES a constraint from body use (row 7) is NOT here —
        //   its var carries no constraint until body inference runs, after this
        //   seeding, so it stays flexible (inferred-not-asserted).
        //
        // Every piece is SAVED here and restored on every exit below.
        let prev_rigid = std::mem::take(&mut state.rigid_vars);
        let prev_scope = state.written_var_scope.take();
        let mut rigid: HashSet<TypeId> = HashSet::new();
        for pt in param_types {
            if let Type::Var(id) = self.apply_subst(state, pt)
                && state.active_constraints.get(id).is_some()
            {
                rigid.insert(id);
            }
        }
        state.rigid_vars = rigid;
        state.written_var_scope = Some(written_var_scope);
        // Install the enclosing defn's name + its recursion-binding frame so
        // `record_reference_target`'s self-recursion carve-out (S110 0583 leg 2)
        // can record the fn's own storage FQ for a GENUINE self-call — the
        // recursion name is env-shadowed here (bound below for recursion
        // typing), so the ordinary carrier path skips it.
        //
        // A param named identically to the fn (`(defn f [f] …)`) is a genuine
        // LOCAL (a backend param), NOT the self-recursion slot: suppress
        // `current_defn` entirely in that case so the carve-out never fires for
        // it (FIXME 0619 item 2 — the recursion binding is still installed
        // below for type inference; this gates only the carrier). The frame
        // index is captured now (the topmost frame after the `push_scope`
        // above) so the carve-out records only when the name resolves at THIS
        // frame — a same-named nested `let`/`fn` binding resolves deeper and is
        // a local, not self-recursion. Torn down on every exit below.
        let installed_defn =
            (!defn.params().iter().any(|(p, _)| *p == defn.name)).then(|| defn.name.clone());
        let prev_defn = std::mem::replace(&mut state.current_defn, installed_defn);
        let prev_defn_frame = state
            .current_defn_frame
            .replace(state.env.top_frame_index());
        // torn down at ONE restore point regardless of how it exits (FIXME
        // 0599 — the pre-existing `?` exits previously leaked
        // `rigid_vars`/`written_var_scope`/the scope frame, so a failed
        // body-check left a stale `written_var_scope` installed for the next
        // top-level annotation).
        let result = (|| {
            // Bind parameters.
            for ((param_name, _), param_ty) in defn.params().iter().zip(param_types.iter()) {
                self.bind_local(state, param_name.clone(), mono(param_ty.clone()));
            }

            // Bind the function name for recursion.
            let fn_type = Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone()));
            self.bind_local(state, defn.name.clone(), mono(fn_type));

            // Infer body type.
            let body_ty = self.infer_expr(state, defn.body())?;

            // Unify body type with return type variable.
            self.unify(state, &body_ty, ret_ty, defn.span)?;

            // A `defn` body that DEFINES a rank-1 polymorphic function value —
            // returned (`(defn mk [] (fn [:b y] y))`), let-stored-and-returned,
            // or applied in place — is a legitimate syntactic value (spec
            // §3.3.4 / §3.10, W6.3 ruling): the written `:b` is irrelevant, so
            // `mk`/`weird` are the same as `mkid`/`constf` and all are ACCEPTED.
            // There is NO eager poly-as-value escape check here. The genuine
            // restrictions are enforced ELSEWHERE:
            //  - MULTI-TYPE use of ONE poly instance (`(let [f (mkid)] (f "x")
            //    (f 5))`) → the value restriction / unification (a type conflict).
            //  - RANK-2 (a poly value passed as an argument and used at two
            //    types, `(defn apply2 [f] … (f "x") … (f 5))`) → unification.
            //  - A RESULT-ONLY var held unresolved (`(defn g [] (constf 5))`) →
            //    the §3.11 ambiguity gate (pin-the-type; the R16 result-var
            //    monomorphisation family), a separate carried limitation.

            // Record the defn's Fn type in expr_types so the backend can look up
            // authoritative parameter types. Without this, unused params (e.g.,
            // `_s` in `(defn f [:String _s] 42)`) have no type recorded and
            // scope cleanup skips their RC dec, causing leaks.
            let resolved_fn_type = Type::Fn(
                param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            self.record_expr_type(state, defn.span, resolved_fn_type);
            Ok(())
        })();

        // Tear down ALL per-body inference state on every exit (§3.3.1 MUST (a):
        // outside its own body a written var is an ordinary quantified var).
        state.rigid_vars = prev_rigid;
        state.written_var_scope = prev_scope;
        state.current_defn = prev_defn;
        state.current_defn_frame = prev_defn_frame;
        self.pop_scope(state);

        result
    }

    // --- Monomorphisation passes ---
}

#[cfg(test)]
mod tests;
