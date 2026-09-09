use super::*;
use crate::checker::{BodyFrame, RecursionBinding};

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
        self.resettle_polymorphic_schemes(state, accumulator)?;
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
        accumulator: &mut ModuleCheckAccumulator,
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
            if v.lookup(&defn.name)
                .and_then(Binding::callable)
                .is_some_and(|c| {
                    matches!(c.origin, CallableOrigin::TraitMethod { .. })
                        && matches!(
                            &c.arm.life,
                            Life::Concrete { ast: Some(_), .. }
                                | Life::Template {
                                    body: TemplateBody::Ast(_),
                                    ..
                                }
                        )
                })
            {
                return Ok(FormCheckResult::empty());
            }
        }

        let body_handle = accumulator
            .bodies
            .registered_for_check(&defn.name)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("internal: missing registered body for {}", defn.name),
                location: ErrorLocation::from_span(defn.span),
            })?;
        let registration = body_handle.registration().clone();

        // Snapshot method_resolutions and expr_types sizes so we can extract
        // just the new entries added during this form's checking.
        let mr_before: HashSet<Span> = state
            .method_resolutions
            .resolved_calls
            .keys()
            .copied()
            .collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();
        let user_fn_refs = self
            .check_defn_body(
                state,
                defn,
                &registration.param_types,
                &registration.ret_ty,
                registration.written_var_scope.clone(),
            )
            .map_err(|e| enrich_macro_clause_resolution_error(defn.name.as_ref(), e))?;

        // Detect whether this checked declaration is constrained and refresh
        // the declared scheme needed by later siblings. Lifecycle publication
        // remains deferred to the final ledger-consumption window.
        let constrained_fn =
            self.determine_fn_state(state, defn, &registration.param_types, &registration.ret_ty)?;

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

        let ast = self.annotate_single_defn(state, defn, &form_et, &form_mr);

        // Harvest call graph edges (Decision 21 + FIXME 0470/0472): the
        // ResolvedCall channel + the user-fn references recorded during this
        // form's body inference — call- and value-position alike, uniform
        // carrier. ONE shared helper across all body-check seams.
        let callees = self.harvest_callees(state, &form_mr, &user_fn_refs);
        body_handle.finish(ast, callees);

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            constrained_fn,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
        })
    }

    /// Detect constrained-ness from this body's trial scheme and refresh the
    /// declaration scheme used by later same-cluster siblings. Returns the
    /// definition name iff it is constrained; final `Life` selection and slot
    /// allocation occur only when the checked ledger record is published.
    pub(super) fn determine_fn_state(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
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
        // same registered body monotypes + the same global `subst`, so the
        // later pass writes the identical scheme.
        if trial_scheme.constraints.is_empty() {
            self.current_symbol_table_mut(state)
                .update_declared_scheme(&defn.name, trial_scheme.clone())
                .map_err(crate::result::lifecycle_error)?;
        }

        if !trial_scheme.constraints.is_empty() {
            Ok(Some(defn.name.clone()))
        } else {
            Ok(None)
        }
    }

    /// Build the initially annotated checked variant retained by the body
    /// ledger. Final substitution, late resolutions, strict view construction,
    /// and symbol-table publication occur in finalization.
    pub(super) fn annotate_single_defn(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        form_et: &HashMap<Span, Type>,
        form_mr: &HashMap<Span, ResolvedCall>,
    ) -> DefnVariant {
        let resolved_et: HashMap<Span, Type> = form_et
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();
        let mut annotated = defn.clone();
        annotate_defn_from_maps(&mut annotated, &resolved_et, form_mr);
        apply_subst_to_defn(&state.subst, &mut annotated);

        annotated
            .variants
            .into_iter()
            .next()
            .expect("single variant")
    }

    /// Check a multi-sig defn's variant bodies (Pass 2).
    pub(super) fn check_form_body_multi_sig(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        // Check each variant body
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            let body_handle = accumulator
                .bodies
                .registered_for_check(&internal_name)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!(
                        "internal: missing registered body for multi-signature clause {}",
                        internal_name
                    ),
                    location: ErrorLocation::from_span(variant.span),
                })?;
            let registration = body_handle.registration().clone();

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

            let user_fn_refs = self.check_defn_body(
                state,
                &internal_defn,
                &registration.param_types,
                &registration.ret_ty,
                registration.written_var_scope.clone(),
            )?;

            // Per-variant AST annotation
            let variant_mr: HashMap<Span, ResolvedCall> = state
                .method_resolutions
                .resolved_calls
                .iter()
                .filter(|(span, _)| !variant_mr_before.contains(span))
                .map(|(span, res)| (*span, res.clone()))
                .collect();
            let annotated_variant = {
                let variant_et: HashMap<Span, Type> = state
                    .expr_types
                    .iter()
                    .filter(|(span, _)| !variant_et_before.contains(span))
                    .map(|(span, ty)| (*span, apply(&state.subst, ty)))
                    .collect();
                let mut annotated = internal_defn.clone();
                annotate_defn_from_maps(&mut annotated, &variant_et, &variant_mr);
                apply_subst_to_defn(&state.subst, &mut annotated);
                annotated
                    .variants
                    .into_iter()
                    .next()
                    .expect("single variant")
            };

            // Eager constrained-fn detection for variant
            let fn_type = Type::Fn(
                registration
                    .param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect(),
                Box::new(self.apply_subst(state, &registration.ret_ty)),
            );
            let trial_scheme = self.generalize(state, &fn_type);

            // FIXME 0344 — generalize-before-cross-defn-use, mirrored at the
            // multi-sig variant site (PURE-parametric only): write the
            // generalized scheme back to the variant's `__vN` entry now so a
            // sibling that references it sees a polymorphic, instantiable view.
            // A constrained variant keeps its `mono` entry for same-program
            // call-site monomorphisation. Idempotent with `finalize` Phase 2.
            if trial_scheme.constraints.is_empty() {
                self.current_symbol_table_mut(state)
                    .update_declared_scheme(&internal_name, trial_scheme.clone())
                    .map_err(crate::result::lifecycle_error)?;
            }

            let callees = self.harvest_callees(state, &variant_mr, &user_fn_refs);
            body_handle.finish(annotated_variant, callees);
        }

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
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
    ) -> Result<HashMap<Span, FQSymbol>, CranelispError> {
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
        let mut rigid: HashSet<TypeId> = HashSet::new();
        for pt in param_types {
            if let Type::Var(id) = self.apply_subst(state, pt)
                && state.active_constraints.get(id).is_some()
            {
                rigid.insert(id);
            }
        }
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
        let recursion =
            (!defn.params().iter().any(|(p, _)| *p == defn.name)).then(|| RecursionBinding {
                name: defn.name.clone(),
                frame: state.env.top_frame_index(),
            });
        let previous_frame = std::mem::replace(
            &mut state.body_frame,
            BodyFrame {
                rigid_vars: rigid,
                written_var_scope: Some(written_var_scope),
                recursion,
                ..BodyFrame::default()
            },
        );
        // torn down at ONE restore point regardless of how it exits (FIXME
        // 0599 — the pre-existing `?` exits previously leaked
        // `rigid_vars`/`written_var_scope`/the scope frame, so a failed
        // body-check left a stale `written_var_scope` installed for the next
        // top-level annotation).
        let result = (|| {
            // Install recursion first, then parameters. A same-named parameter
            // occupies the same lexical frame and must be the lookup winner for
            // both HM inference and carrier classification; an unshadowed name
            // continues to resolve to this recursive monotype.
            let fn_type = Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone()));
            self.bind_local(state, defn.name.clone(), mono(fn_type));

            for ((param_name, _), param_ty) in defn.params().iter().zip(param_types.iter()) {
                self.bind_local(state, param_name.clone(), mono(param_ty.clone()));
            }

            // Infer body type.
            let body_ty = self.infer_expr(state, defn.body())?;

            // Unify body type with return type variable.
            self.unify(state, &body_ty, ret_ty, defn.span)?;
            self.settle_body_work(
                state,
                defn.body(),
                crate::candidate_selection::BodySettlementScope::TopLevel,
            )?;

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

        let completed_frame = std::mem::replace(&mut state.body_frame, previous_frame);
        self.pop_scope(state);
        result.map(|()| completed_frame.user_fn_refs)
    }

    // --- Monomorphisation passes ---
}

#[cfg(test)]
mod tests;
