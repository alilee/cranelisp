use std::collections::{HashMap, HashSet};

use cranelisp_types::{ErrorLocation,
    ConstrainedFn, CranelispError, DefKind, Defn, DefnVariant, Expr, FQSymbol,
    JitSymbol, MethodResolutions, ModuleEntry, ModuleFullPath, MonoDefn, MonoDefnVariant, MonoExpr,
    NotConcrete, ResolvedCall, Scheme,
    Span, Symbol, Type,
    TypeName, UserFnState, Visibility, apply,
};

use crate::checker::{CheckState, TypeCheckEnv};

// ---------------------------------------------------------------------------
// Constrained Instantiation
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Instantiate a constrained scheme, tracking the constraints on fresh vars.
    ///
    /// Returns the instantiated type. Side effect: adds constraints to
    /// `self.state.active_constraints`.
    pub(crate) fn instantiate_constrained(
        &self,
        state: &mut CheckState,
        scheme: &Scheme,
    ) -> Type {
        if scheme.type_vars.is_empty() {
            return scheme.ty.clone();
        }

        // Build mapping from old vars to fresh vars.
        //
        // Each fresh var must NOT collide with any of the scheme's own
        // quantified vars — re-roll on collision. A collision (e.g. a
        // cross-module scheme whose quantified TypeIds the per-session
        // `next_id` counter has not been advanced past) would otherwise build
        // an identity self-map and make `apply` recurse forever
        // (FIXME 0279/0295). See `instantiate_scheme`'s `fresh_instantiation_subst`.
        let bound: std::collections::HashSet<cranelisp_types::TypeId> =
            scheme.type_vars.iter().copied().collect();
        let mut inst_subst = cranelisp_types::Subst::new();
        let mut var_mapping = HashMap::new();
        for &var_id in &scheme.type_vars {
            let (fresh_ty, fresh_id) = loop {
                let (fresh_ty, fresh_id) = self.fresh_var_id();
                if !bound.contains(&fresh_id) {
                    break (fresh_ty, fresh_id);
                }
            };
            inst_subst.insert(var_id, fresh_ty);
            var_mapping.insert(var_id, fresh_id);
        }

        // Carry constraints to fresh vars
        for (old_var, traits) in &scheme.constraints {
            if let Some(&new_var) = var_mapping.get(old_var) {
                for t in traits {
                    state.active_constraints.add(new_var, t.clone());
                }
            }
        }

        apply(&inst_subst, &scheme.ty)
    }
}

// ---------------------------------------------------------------------------
// Monomorphisation
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Generate a monomorphised specialization of a constrained function.
    ///
    /// Called when a constrained function is applied with concrete argument types.
    #[allow(dead_code)]
    ///
    /// `home` is `Some(defining_module)` when `fn_name` is an IMPORTED
    /// constrained fn whose body must be re-checked in its DEFINING module's
    /// import context (FIXME 0355) — `show`/`str-concat`/trait-method references
    /// inside the body resolve there, not in the caller's scope. It is `None` for
    /// a locally-defined constrained fn (the as-built same-module path), in which
    /// case the lookup + re-check use `state.current_module` unchanged.
    pub(crate) fn monomorphise_call(
        &self,
        state: &mut CheckState,
        fn_name: &Symbol,
        arg_types: &[Type],
        call_span: Span,
        home: Option<&ModuleFullPath>,
    ) -> Result<Option<MonoDefn>, CranelispError> {
        // === P0 — lookup ===
        // Look up the constrained fn (in its defining module when imported).
        // `home` selects the lookup module; early `None` is the "not a mono
        // target" signal callers depend on (`Ok(None)` vs `Ok(Some)`).
        let constrained_fn = match self.get_constrained_fn(state, fn_name, home) {
            Some(cf) => cf,
            None => return Ok(None),
        };

        let scheme = constrained_fn.scheme.clone();
        let defn = constrained_fn.variant.clone();

        // === P1 — instantiate + concrete params ===
        // Instantiate, unify with arg types, and resolve concrete types. Keep
        // the original→fresh var-id mapping so constraint verification resolves
        // through the instantiated vars (FIXME 0355). Losing the mapping
        // reintroduces the cross-module `IO`-collision bug.
        let (resolved, var_mapping) =
            self.instantiate_and_resolve(state, &scheme, arg_types, call_span)?;

        let concrete_param_types = if let Type::Fn(pts, _) = &resolved {
            pts.clone()
        } else {
            return Ok(None);
        };

        // === §9 concreteness gate (FIXME 0432, monomorphisation.md §9.3) ===
        // Defence-in-depth, Principle 18 belt-and-braces. A residual `Type::Var`
        // in a minted mono-instance param vector (the FIXME's `[Int, Var(N)]`
        // shape from an unannotated multi-clause `defn` whose cross-variant
        // self-call cannot pin a param) must NEVER reach `build_mangled_name` as
        // a debug panic (`:1016` tripwire) — `s84-concrete-types-ambiguity-ruling`:
        // a residual `Var` at a codegen position is a CLEAN type error, never a
        // panic. The release path's §3.11.1 backstop
        // (`find_ambiguous_top_level_form`) already catches this form cleanly AND
        // the multi-clause variant mangler (`program.rs:627`) tolerates a `Var`
        // param without reaching this seam — so the `:1016` assert is provably
        // unreachable-for-0432 today (this gate makes that guarantee structural
        // rather than incidental). Lift the same `Type::is_concrete()` predicate
        // the `:1016` `debug_assert!` tests from a release-erased assertion to a
        // live `Result`-returning check, fired one step earlier — at the
        // param-vector, before mangling. The error reuses the §3.11.1 /
        // `finalize_mono_codegen_view` wording so REPL and `--run` produce one
        // identical diagnostic and the suite's ambiguous-type assertions hold.
        if !concrete_param_types.iter().all(Type::is_concrete) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "ambiguous type; add an annotation to pin the type of \
                     the polymorphic value monomorphised in `{fn_name}` (a \
                     residual unbound type variable reached a codegen position)"
                ),
                location: ErrorLocation::from_span(call_span),
            });
        }

        // The DEFINING module qualifies the mangled name (FIXME 0519): `home`
        // for an imported generic (FIXME 0355), else the local `current_module`.
        let home_path = home
            .cloned()
            .unwrap_or_else(|| state.current_module.clone());
        let mangled_name = build_mangled_name(&home_path, fn_name, &concrete_param_types);

        // === P2 — verify constraints (module-switched) ===
        self.verify_mono_constraints(state, &scheme, &var_mapping, home, call_span)?;

        let concrete_ret_ty = if let Type::Fn(_, ret) = &resolved {
            *ret.clone()
        } else {
            return Ok(None);
        };

        // === P3 — call-site return pinning (0349) ===
        self.pin_call_site_return(state, &concrete_ret_ty, call_span)?;

        // === P4 — recheck body + harvest ===
        // `defn: DefnVariant` (S70 ConstrainedFn narrowing). Wrap in a
        // temporary single-variant `Defn` for the recheck helpers which
        // still take `&mut Defn`. The post-passes annotate THIS clone.
        let mut wrap_defn = Defn {
            name: fn_name.clone(),
            docstring: None,
            variants: vec![defn.clone()],
            visibility: Visibility::Public,
            span: defn.span,
        };
        let (mut resolutions, mono_expr_types) = self.recheck_and_resolve_inner(
            state,
            &mut wrap_defn,
            &concrete_param_types,
            &concrete_ret_ty,
            home,
        )?;

        // === P5 — self-recursion dispatch (0374) ===
        self.record_self_recursion_dispatch(
            &wrap_defn,
            &home_path,
            fn_name,
            &mangled_name,
            &mono_expr_types,
            &mut resolutions,
            &state.current_module,
        );

        // === P6 — build annotated mono defn ===
        let mono_defn_ast = self.build_annotated_mono_defn(
            state,
            fn_name,
            &mangled_name,
            &defn,
            &mono_expr_types,
            &resolutions,
            home,
        );

        // === P7 — concrete-boundary view + register ===
        let mono_defn = self.finalize_mono_codegen_view(
            state,
            mono_defn_ast,
            &mangled_name,
            &concrete_param_types,
            &concrete_ret_ty,
            defn.span,
            &resolutions.resolved_targets,
        )?;

        Ok(Some(mono_defn))
    }

    /// P2 — verify trait constraints, with `current_module` switched to `home`
    /// for the impl lookup of an IMPORTED callee (FIXME 0355).
    ///
    /// For an IMPORTED callee, the trait + impl referenced by the constraint
    /// live in the DEFINING module's scope, so switch `current_module` to
    /// `home` for the impl lookup (mirrors `recheck_body_for_mono`'s module
    /// switch). The switch is **restored unconditionally** BEFORE the result is
    /// `?`-propagated. Without this, `has_impl_with_state` roots the trait
    /// resolution in the caller's scope and a home-local (non-prelude) impl is
    /// invisible — a spurious "no impl of trait T for type Int".
    fn verify_mono_constraints(
        &self,
        state: &mut CheckState,
        scheme: &Scheme,
        var_mapping: &HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>,
        home: Option<&ModuleFullPath>,
        call_span: Span,
    ) -> Result<(), CranelispError> {
        let saved_module = home.map(|h| {
            std::mem::replace(&mut state.current_module, h.clone())
        });
        let verify_result = self.verify_constraints(state, scheme, var_mapping, call_span);
        if let Some(prev) = saved_module {
            state.current_module = prev;
        }
        verify_result
    }

    /// P3 — propagate the concrete return type back to the CALL SITE (FIXME 0349).
    ///
    /// `instantiate_and_resolve` instantiated a FRESH copy of the callee
    /// scheme and unified only its parameters with the concrete arg types;
    /// the freshly-instantiated return var (now resolved to `concrete_ret_ty`)
    /// is otherwise disconnected from the caller's recorded result type. Under
    /// forward-reference ordering a polymorphic callee (`reduce`) is generalized
    /// before the helper that ties its accumulator-to-result var, so the
    /// caller (`main`) bound its own result var to the callee's *loose*
    /// generalized return var during body-check; that left `main`'s result
    /// un-pinned (`(IO t)`), marking `main` itself spuriously polymorphic.
    /// Unifying the call-site's recorded expr type with the concrete return
    /// pins the caller's result (`t -> Int`), so the subsequent caller
    /// re-generalization yields the correct monomorphic scheme — the caller
    /// then calls the mono variant instead of the polymorphic template (0344).
    ///
    /// This unify writes into the parent's LIVE `state.subst` (NOT an isolated
    /// clone) — this is the one place the parent subst is intentionally mutated.
    fn pin_call_site_return(
        &self,
        state: &mut CheckState,
        concrete_ret_ty: &Type,
        call_span: Span,
    ) -> Result<(), CranelispError> {
        if let Some(call_result_ty) = state.expr_types.get(&call_span).cloned() {
            self.unify(state, &call_result_ty, concrete_ret_ty, call_span)?;
        }
        Ok(())
    }

    /// P4 — re-check the mono body with concrete types and harvest resolutions,
    /// then propagate the concrete instantiation through inner hops.
    ///
    /// `recheck_body_for_mono` saves/restores `method_resolutions`/`expr_types`/
    /// `pending_auto_curry`/`current_module` itself, and the post-passes
    /// annotate the SAME `wrap_defn` clone (passed by `&mut`).
    ///
    /// `resolve_inner_constrained_calls` records SigDispatch for inner
    /// constrained calls (e.g. self-recursion), scoped in `home` (FIXME 0355).
    ///
    /// FIXME 0373 (Tier 1, /arch ruling (A)) — propagate the concrete
    /// instantiation through the CHAIN OF HOPS. The repro `(h1 neg)` reaches
    /// its invocation through two hops: `h1` calls `h2` calls `f`. The
    /// top-level pass4 scan collected `(h1 neg)` and monomorphised `h1`,
    /// re-checking its body `(h2 f)` with `f: (Fn [Int] Int)` concrete — but
    /// the inner `(h2 f)` call only became concrete DURING this recheck, so
    /// pass4's outer scan (where `f` was still `h1`'s generic param var) never
    /// saw it with concrete types. Without monomorphising `h2` HERE, `h2`'s
    /// result stays `Type::Var` → the same RC-guard SIGSEGV one hop deeper.
    ///
    /// So after re-checking this hop's body we recursively monomorphise the
    /// inner polymorphic-result hops it reached, using the concrete types now
    /// pinned in `mono_expr_types`. `monomorphise_inner_parametric_hops`
    /// isolates `state.subst` around EACH inner recursion (0344) — that
    /// isolation stays inside that fn; do NOT lift it to this driver.
    fn recheck_and_resolve_inner(
        &self,
        state: &mut CheckState,
        wrap_defn: &mut Defn,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        home: Option<&ModuleFullPath>,
    ) -> Result<(MethodResolutions, HashMap<Span, Type>), CranelispError> {
        let (mut resolutions, mono_expr_types) =
            self.recheck_body_for_mono(state, wrap_defn, concrete_param_types, concrete_ret_ty, home)?;

        // Add SigDispatch entries for inner constrained fn calls. For an
        // imported callee, inner constrained calls (e.g. self-recursion) are
        // named in the DEFINING module's scope, so scope this in `home` too
        // (FIXME 0355).
        self.resolve_inner_constrained_calls(
            state,
            wrap_defn,
            &mono_expr_types,
            &mut resolutions,
            home,
        );

        // FIXME 0373: recursively monomorphise inner polymorphic-result hops.
        // `resolve_inner_constrained_calls` above already records the
        // SigDispatch for inner CONSTRAINED self-recursion; this step
        // additionally CREATES the mono entries for distinct inner hops
        // (constrained or pure-parametric) and records their dispatch. The
        // `seen`-style de-dup that guards the outer pass lives in
        // `register_mono_entry` (it preserves an existing entry's slot) and in
        // the `resolved_calls` contains-key guard inside the recursion, so a
        // diamond of hops converging on one specialisation is created once.
        self.monomorphise_inner_parametric_hops(
            state,
            wrap_defn,
            &mono_expr_types,
            &mut resolutions,
            home,
        )?;

        Ok((resolutions, mono_expr_types))
    }

    /// P5 — record SigDispatch for monomorphic self-recursion (FIXME 0374).
    ///
    /// A polymorphic fn that recurses on itself at its OWN generic vars
    /// (`(repeat-fn f (sub-i64 n 1) (f x))`) is monomorphic recursion (rank-1
    /// HM): the self-call instantiates the SAME `(Def, type-args)` as this
    /// mono, so it dispatches to THIS mono (`mangled_name`). With the
    /// structural slot gate the original `fn_name` def is slot-less
    /// `Polymorphic`, so the self-call MUST be redirected to the slotted mono
    /// instance or it lowers through a missing slot ("undefined function").
    /// `collect_apply_var_calls` deliberately skips self-calls (they are not a
    /// DISTINCT instance to mint), so record their dispatch here. Only the
    /// same-arg-type self-recursion is the same mono; a self-call at different
    /// concrete types would have been a distinct hop already minted in P4.
    ///
    /// This is a pure `resolutions` mutation — no `state.subst` touch.
    #[allow(clippy::too_many_arguments)]
    fn record_self_recursion_dispatch(
        &self,
        wrap_defn: &Defn,
        home: &ModuleFullPath,
        fn_name: &Symbol,
        mangled_name: &str,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &mut MethodResolutions,
        current_module: &ModuleFullPath,
    ) {
        let mut self_calls = Vec::new();
        collect_self_apply_calls(wrap_defn.body(), fn_name, &mut self_calls);
        for (arg_spans, self_span) in &self_calls {
            if resolutions.resolved_calls.contains_key(self_span) {
                continue;
            }
            let self_arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| mono_expr_types.get(span).cloned())
                .collect();
            if self_arg_types.len() != arg_spans.len() {
                continue;
            }
            // Same concrete param types ⇒ same mono instance (`mangled_name`).
            // Same instance ⇒ same defining home, so key with the same `home`.
            if build_mangled_name(home, fn_name, &self_arg_types) == mangled_name {
                resolutions.resolved_calls.insert(
                    *self_span,
                    ResolvedCall::SigDispatch {
                        mangled_name: JitSymbol::from(mangled_name),
                    },
                );
                // S110 0583 leg 1 (mono self-recursion carrier, FIXME 0616):
                // the mono variant is registered in the caller's current module
                // (`register_mono_entry`), so the storage FQ is
                // `{current_module, mangled_name}` — the SigDispatch home
                // `resolved_call_to_fqsymbol` derives.
                resolutions.resolved_targets.insert(
                    *self_span,
                    FQSymbol {
                        module: current_module.clone(),
                        symbol: Symbol::from(mangled_name),
                    },
                );
            }
        }
    }

    /// P6 — build the annotated mono `Defn`: recover parent metadata, annotate
    /// from side maps, apply subst.
    ///
    /// `defn: DefnVariant` (S70 ConstrainedFn narrowing) — name/docstring/
    /// visibility no longer ride on the payload; recover them from the parent
    /// Def's ModuleEntry which is keyed by `fn_name`. For an imported callee the
    /// parent `Def` lives in `home`, not the caller's current module, so probe
    /// there (FIXME 0355). `apply_subst_to_defn` reads the parent's live
    /// `state.subst` (which P3+P4 populated) — it runs after P4, on the parent
    /// subst.
    #[allow(clippy::too_many_arguments)]
    fn build_annotated_mono_defn(
        &self,
        state: &CheckState,
        fn_name: &Symbol,
        mangled_name: &str,
        defn: &DefnVariant,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &MethodResolutions,
        home: Option<&ModuleFullPath>,
    ) -> Defn {
        let parent_metadata: Option<(Option<String>, Visibility)> = {
            let lookup_module = home.unwrap_or(&state.current_module);
            self.resolve_terminal_entry_and_home(lookup_module, fn_name.as_ref())
                .and_then(|(e, _)| match e {
                    ModuleEntry::Def { docstring, visibility, .. } => {
                        Some((docstring.clone(), visibility))
                    }
                    _ => None,
                })
        };
        let (docstring, visibility) = parent_metadata.unwrap_or((None, Visibility::Public));
        let mut mono_defn_ast = Defn {
            name: Symbol::from(mangled_name),
            docstring,
            variants: vec![DefnVariant {
                params: defn.params.clone(),
                body: defn.body.clone(),
                span: defn.span,
            }],
            visibility,
            span: defn.span,
        };
        crate::program::annotate_defn_from_maps(
            &mut mono_defn_ast,
            mono_expr_types,
            &resolutions.resolved_calls,
        );
        crate::program::apply_subst_to_defn(&state.subst, &mut mono_defn_ast);
        mono_defn_ast
    }

    /// P7 — build the concrete-boundary `MonoExpr` view, register the mono
    /// entry, and return the `MonoDefn`.
    ///
    /// S84 Phase 2b (concrete-boundary-type.md §2.4 "mono-population seam"):
    /// build the concrete-boundary AST view (`MonoExpr`) of this instance at
    /// the seam, IMMEDIATELY after `apply_subst_to_defn` (P6) resolved every
    /// node's `inferred_type` through the substitution. `MonoExpr::from_expr`
    /// walks the fully-annotated, subst-resolved body and converts each node's
    /// `inferred_type` to a `ConcreteType` — failing at the first node whose
    /// type is absent or a residual `Type::Var` / unresolved HKT head.
    ///
    /// The validation payoff: `from_expr` runs on EVERY monomorphised instance.
    /// A correctly-monomorphised instance MUST succeed (every node concrete). A
    /// failure means this mono instance retains a residual `Var` (a genuine
    /// incompleteness) — surfaced HERE as the unified §3.11.1 ambiguity /
    /// could-not-monomorphise error (reusing the same diagnostic wording the
    /// position-complete scan in `find_ambiguous_top_level_form` produces, so no
    /// regression in rejection coverage), NOT silently swallowed.
    ///
    /// **Phase-4 part A — the carve-out is DELETED; every minted instance is
    /// concrete.** Before Phase 4, the mono pass minted a SPURIOUS partial
    /// instance (`reduce-loop$Vec+Int+Int`, the 0344 fold) whose body retained
    /// scheme-quantified vars, and an `allowed_vars` carve-out admitted it with
    /// no `MonoExpr`. Part A suppresses that mint at the collection gate
    /// (`local_parametric_call_triggers` + `monomorphise_inner_parametric_hops`
    /// now require ALL ARGS CONCRETE). With no partial instance minted, every
    /// instance reaching this seam is fully concrete ⇒ `from_expr` succeeds on
    /// EVERY one ⇒ the carve-out is dead code, deleted. The deletion IS the
    /// completeness proof: an `Err` here now means a GENUINELY-free residual
    /// (the real ambiguity case, §1.3 / §2.6) — for a valid program it must not
    /// happen, and if it does the suite goes red at that instance (Principle 20:
    /// completeness forced by representation, not chased by hand).
    ///
    /// S84 Phase-3 (FIXME 0392): the `MonoDefnVariant` built here is the
    /// entry's `codegen_view` — set ON the mono instance's `ModuleEntry::Def`
    /// at `register_mono_entry` (single source of truth, Principle 7).
    #[allow(clippy::too_many_arguments)]
    fn finalize_mono_codegen_view(
        &self,
        state: &mut CheckState,
        mono_defn_ast: Defn,
        mangled_name: &str,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        defn_span: Span,
        resolved_targets: &HashMap<Span, FQSymbol>,
    ) -> Result<MonoDefn, CranelispError> {
        // `resolved_targets` (S110 0583 leg 1, FIXME 0616) is the PER-INSTANCE
        // mono `resolutions.resolved_targets`, NOT `state.method_resolutions`:
        // `recheck_body_for_mono` restored the enclosing map before this seam,
        // and the enclosing map carries no mono-time dispatch SELECTIONS (a
        // self-call / sig-dispatch is minted per instance — `f$Int` vs `f$Float`
        // at the SAME template span, so a shared map would collide). The local
        // map carries the mono body's Var-ref carriers (recheck infer_var) AND
        // the dispatch carriers (P4/P5 seams). `pattern_ctors` stays on the
        // enclosing map: template ctors are instance-INVARIANT (same span → same
        // ctor), so the original template check's entries serve every instance.
        let codegen_view = match MonoExpr::from_expr(mono_defn_ast.body(), &state.method_resolutions.pattern_ctors, resolved_targets) {
            Ok(mono_body) => {
                // Genuinely concrete instance — carry the concrete-boundary view.
                MonoDefnVariant {
                    name: Symbol::from(mangled_name),
                    params: mono_defn_ast.params().iter().map(|(n, _)| n.clone()).collect(),
                    body: mono_body,
                    span: defn_span,
                    mode_summary: None,
                }
            }
            // A genuinely-free residual (an unbound type variable, or an
            // un-annotated node — `Var(0)` sentinel — reaching a codegen
            // position) is the unified ambiguity / could-not-monomorphise error
            // (§1.3 / §2.6), reusing the §3.11.1 diagnostic wording (no
            // rejection-coverage regression). Post-part-A this arm fires ONLY for
            // genuinely-ambiguous code, never for a valid program.
            Err(nc) => {
                let detail = match nc {
                    NotConcrete::Var(_) => "a residual unbound type variable",
                    NotConcrete::HktHead(_) => "an unresolved higher-kinded type head",
                };
                return Err(CranelispError::TypeError {
                    message: format!(
                        "ambiguous type; add an annotation to pin the type of \
                         the polymorphic value monomorphised in `{}` ({detail} \
                         reached a codegen position)",
                        mangled_name
                    ),
                    location: ErrorLocation::from_span(defn_span),
                });
            }
        };

        let mono_defn = MonoDefn {
            defn: mono_defn_ast,
        };

        // Wave 0 (§9.4): register the mono specialisation as a symbol-table
        // entry with `ast: Some(annotated)`. The body has been fully annotated
        // by `annotate_defn_from_maps` + `apply_subst_to_defn` (P6) — no further
        // enrichment needed. Backend codegen reads the body via
        // `ModuleEntry::Def.ast`.
        self.register_mono_entry(
            state,
            &mono_defn,
            concrete_param_types,
            concrete_ret_ty,
            codegen_view,
        );

        Ok(mono_defn)
    }

    /// Register a mono specialisation on the current module's symbol table
    /// as a `ModuleEntry::Def` with `ast: Some(annotated)`. Wave 0 §9.4.
    fn register_mono_entry(
        &self,
        state: &mut CheckState,
        mono: &MonoDefn,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        codegen_view: MonoDefnVariant,
    ) {
        let fn_ty = Type::Fn(
            concrete_param_types.to_vec(),
            Box::new(concrete_ret_ty.clone()),
        );
        let scheme = crate::scheme::mono(fn_ty);

        let mut st = self.current_symbol_table_mut(state);
        // De-duplication note: `pass4_monomorphise` / `monomorphise_expr_calls`
        // short-circuit via `seen` before calling `monomorphise_call` a second
        // time for the same mangled name, so this insertion runs exactly once
        // per specialisation. If an entry already exists (e.g., REPL redefinition),
        // we preserve its `got_slot` to keep call-site GOT indices stable.
        // A mono specialisation is a concrete callable born with its slot
        // (S83 deferred allocation, Principle 20). On REPL redefinition reuse
        // the prior concrete entry's slot (read via `callable_got_slot`) to
        // keep call-site GOT indices stable; the slot rides inside the
        // `Concrete` fn_state, not a flat `Def` field.
        let existing_got_slot = st.get(mono.defn.name.as_ref())
            .and_then(|e| e.callable_got_slot());
        let got_slot = existing_got_slot.unwrap_or_else(|| st.allocate_got_slot());

        let mut builder = ModuleEntry::def(
            scheme,
            DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot, mode_summary: None } },
        )
        .visibility(mono.defn.visibility)
        .param_names(mono.defn.params().iter().map(|(n, _)| n.clone()).collect());
        if let Some(doc) = mono.defn.docstring.clone() {
            builder = builder.docstring(doc);
        }
        // S69 Submission 35: ast holds the single meaningful DefnVariant
        // (not the parent Defn wrapper).
        if let Some(ast) = mono.defn.variants.first().cloned() {
            builder = builder.ast(ast);
        }
        // S84 Phase-3 (FIXME 0392): a mono instance is a codegen-bound
        // `Concrete` entry — carry its concrete-boundary `MonoExpr` view, built
        // + validated at the `monomorphise_call` seam. Produces-but-unread until
        // the backend read-flip (FIXME 0391); the backend still reads `ast`.
        builder = builder.codegen_view(codegen_view);
        st.insert(mono.defn.name.clone(), builder.build());
    }

    /// Instantiate a scheme with fresh type variables, unify with the given
    /// argument types, and return the fully-resolved function type.
    fn instantiate_and_resolve(
        &self,
        state: &mut CheckState,
        scheme: &Scheme,
        arg_types: &[Type],
        call_span: Span,
    ) -> Result<(Type, HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>), CranelispError>
    {
        // Instantiate the scheme with fresh vars, KEEPING the original→fresh
        // var-id mapping. The mapping is needed by `verify_constraints`:
        // `scheme.constraints` are keyed by the scheme's ORIGINAL var_ids, but
        // only the FRESH vars are unified into `state.subst` here. Cross-module
        // (FIXME 0355) the scheme comes from another module's check, so its
        // original var_ids are stale in the caller's `state.subst` — and may
        // COLLIDE with a caller var (observed: `cmp`'s constraint var_id
        // resolving to the caller's `IO` from `main`'s `Pure`, producing a
        // spurious "no impl of Eq/Display for IO"). Resolving constraints
        // through the instantiation map fixes this. Re-rolls fresh ids on
        // collision with the scheme's own bound vars (FIXME 0279/0295), like
        // the sibling instantiator above.
        let bound: std::collections::HashSet<cranelisp_types::TypeId> =
            scheme.type_vars.iter().copied().collect();
        let mut inst_subst = cranelisp_types::Subst::new();
        let mut var_mapping: HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId> =
            HashMap::new();
        for &var_id in &scheme.type_vars {
            let (fresh_ty, fresh_id) = loop {
                let (fresh_ty, fresh_id) = self.fresh_var_id();
                if !bound.contains(&fresh_id) {
                    break (fresh_ty, fresh_id);
                }
            };
            inst_subst.insert(var_id, fresh_ty);
            var_mapping.insert(var_id, fresh_id);
        }
        let inst_type = apply(&inst_subst, &scheme.ty);

        if let Type::Fn(param_types, _) = &inst_type {
            for (pt, at) in param_types.iter().zip(arg_types.iter()) {
                self.unify(state, pt, at, call_span)?;
            }
        }

        Ok((self.apply_subst(state, &inst_type), var_mapping))
    }

    /// Verify that all trait constraints in the scheme are satisfied by
    /// the concrete types determined during unification.
    fn verify_constraints(
        &self,
        state: &CheckState,
        scheme: &Scheme,
        var_mapping: &HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>,
        call_span: Span,
    ) -> Result<(), CranelispError> {
        for (var_id, traits) in &scheme.constraints {
            // `scheme.constraints` are keyed by the scheme's ORIGINAL quantified
            // var_ids. Only the FRESH vars from instantiation were unified into
            // `state.subst`, so resolve each constraint var through the
            // instantiation map first (FIXME 0355 — cross-module the original
            // var_id is stale/colliding in the caller's subst). A var absent
            // from the map (defensive) falls back to its original id.
            let effective_id = var_mapping.get(var_id).copied().unwrap_or(*var_id);
            let resolved_var = apply(&state.subst, &Type::Var(effective_id));
            let impl_type = match concrete_type_name(&resolved_var) {
                Some(tn) => tn,
                None => continue,
            };
            for fq_trait in traits {
                if !self.has_impl_with_state(state, &fq_trait.name, &impl_type) {
                    // `fq_trait` is already FQ; render `impl_type` FQ too so the
                    // message disambiguates two same-named ADTs (S87-1).
                    let fq_impl_type =
                        self.fq_type_name_for_diagnostics(state, &impl_type, call_span);
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "no impl of trait {} for type {}",
                            fq_trait, fq_impl_type
                        ),
                        location: ErrorLocation::from_span(call_span),
                    });
                }
            }
        }
        Ok(())
    }

    /// Re-check a function body with concrete types, saving and restoring
    /// the typechecker's resolution/expr_types state around the check.
    ///
    /// Returns the per-specialization method resolutions and expression types.
    ///
    /// `home` is `Some(defining_module)` for an IMPORTED constrained fn
    /// (FIXME 0355): `state.current_module` is saved and switched to `home`
    /// around the body re-check, so the body's bare references
    /// (`show`/`str-concat`/trait methods) resolve in the DEFINING module's
    /// import context — re-checking them in the caller's scope mis-resolves them
    /// (`no impl of trait Display for type IO`). The home is a COMMITTED import
    /// → the live view suffices (no staging shadow). It is restored unconditionally
    /// alongside the resolution/expr-type/auto-curry side state. `None` leaves the
    /// current module unchanged (the as-built same-module path).
    pub(crate) fn recheck_body_for_mono(
        &self,
        state: &mut CheckState,
        defn: &mut Defn,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        home: Option<&ModuleFullPath>,
    ) -> Result<(MethodResolutions, HashMap<Span, Type>), CranelispError> {
        let saved_resolutions = std::mem::take(&mut state.method_resolutions);
        let saved_expr_types = std::mem::take(&mut state.expr_types);
        let saved_pending_auto_curry = std::mem::take(&mut state.pending_auto_curry);
        // Switch into the defining module for an imported callee so the body's
        // bare-name references resolve in its import context (FIXME 0355).
        let saved_current_module = home.map(|h| {
            std::mem::replace(&mut state.current_module, h.clone())
        });

        let result = self.check_defn_body_with_types(state, defn, concrete_param_types, concrete_ret_ty);

        // Drain pending auto-curry entries into method_resolutions before
        // capturing. During re-check, auto-curry sites push to
        // pending_auto_curry but aren't yet in method_resolutions.
        if result.is_ok() {
            self.resolve_auto_curry(state);
        }

        let resolutions = std::mem::take(&mut state.method_resolutions);
        let mono_expr_types: HashMap<Span, Type> = state.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();

        state.method_resolutions = saved_resolutions;
        state.expr_types = saved_expr_types;
        state.pending_auto_curry = saved_pending_auto_curry;
        // Restore the caller's module unconditionally (mirrors the side-state
        // save/restore discipline above).
        if let Some(prev) = saved_current_module {
            state.current_module = prev;
        }

        result?;
        Ok((resolutions, mono_expr_types))
    }

    /// Scan the monomorphised body for constrained fn calls (e.g. self-recursive
    /// calls) and add SigDispatch entries so the backend can find them.
    fn resolve_inner_constrained_calls(
        &self,
        state: &CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &mut MethodResolutions,
        home: Option<&ModuleFullPath>,
    ) {
        // For an imported callee, inner constrained-fn names live in the
        // DEFINING module's scope (FIXME 0355). Read constrained fns from there
        // rather than the caller's current module.
        let constrained_fn_names: HashSet<Symbol> = match home {
            Some(h) => {
                let mut names = HashSet::new();
                self.for_each_in_module(h, |name, entry| {
                    if let ModuleEntry::Def { kind, .. } = entry
                        && let DefKind::UserFn { fn_state: UserFnState::Constrained(_) } = kind.as_ref()
                    {
                        names.insert(name.clone());
                    }
                });
                names
            }
            None => {
                let r = self.current_symbol_table(state);
                r.view()
                    .iter()
                    .filter_map(|(name, entry)| {
                        if let ModuleEntry::Def { kind, .. } = entry
                            && let DefKind::UserFn { fn_state: UserFnState::Constrained(_) } = kind.as_ref()
                        {
                            return Some(name.clone());
                        }
                        None
                    })
                    .collect()
            }
        };
        let mut inner_calls = Vec::new();
        Self::collect_constrained_calls(defn.body(), &constrained_fn_names, &mut inner_calls);
        for (inner_fn_name, arg_spans, inner_call_span) in &inner_calls {
            if resolutions.resolved_calls.contains_key(inner_call_span) {
                continue; // already resolved (e.g. as a trait method)
            }
            let inner_arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| mono_expr_types.get(span).cloned())
                .collect();
            if inner_arg_types.len() != arg_spans.len() {
                continue;
            }
            // Inner constrained fns live in the SAME defining module as the
            // outer (collected from `home` when imported, else current), so the
            // inner mono instance's name is qualified by that same home.
            let inner_home = home
                .cloned()
                .unwrap_or_else(|| state.current_module.clone());
            let inner_mangled = build_mangled_name(&inner_home, inner_fn_name, &inner_arg_types);
            resolutions.resolved_calls.insert(
                *inner_call_span,
                ResolvedCall::SigDispatch {
                    mangled_name: JitSymbol::from(inner_mangled.as_str()),
                },
            );
            // S110 0583 leg 1 (inner constrained-call carrier, FIXME 0616): the
            // inner mono variant registers in the caller's current module, so
            // its storage FQ is `{current_module, inner_mangled}`.
            resolutions.resolved_targets.insert(
                *inner_call_span,
                FQSymbol {
                    module: state.current_module.clone(),
                    symbol: Symbol::from(inner_mangled.as_str()),
                },
            );
        }
    }

    /// Recursively monomorphise the polymorphic-result hops a just-rechecked
    /// mono body reached (FIXME 0373, Tier 1 — multi-hop concrete-type
    /// propagation; /arch ruling (A)).
    ///
    /// `resolve_inner_constrained_calls` (called just before this) records the
    /// SigDispatch for inner CONSTRAINED self-recursion, but does not CREATE a
    /// mono entry for a *distinct* inner hop. A chain `h1 → h2 → f` needs `h2`
    /// monomorphised at the concrete `(Fn [Int] Int)` instantiation that only
    /// became visible during `h1`'s recheck — otherwise `h2`'s result stays
    /// `Type::Var` and the RC-guard SIGSEGV fires one hop deeper.
    ///
    /// For each inner `Apply`-of-bare-`Var` call whose callee chain-resolves to a
    /// monomorphisable polymorphic `Def` (constrained OR pure-parametric), with
    /// all argument types now concrete in `mono_expr_types`, this recursively
    /// invokes [`Self::monomorphise_call`] (which itself recurses into deeper
    /// hops and registers the inner mono entry + slot via `register_mono_entry`),
    /// then records the inner call site's SigDispatch. The recheck module is the
    /// callee's HOME: an inner hop reached from an imported hop lives in `home`;
    /// a local hop lives in `current_module`. A callee that resolves to a
    /// different module than the recheck scope is handed `Some(its_home)` so its
    /// own body re-checks in the right import context (the 0355 module switch).
    fn monomorphise_inner_parametric_hops(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &mut MethodResolutions,
        home: Option<&ModuleFullPath>,
    ) -> Result<(), CranelispError> {
        // The scope the body was re-checked in: `home` for an imported hop, else
        // the caller's current module.
        let recheck_module = home.cloned().unwrap_or_else(|| state.current_module.clone());

        // Collect inner Apply-of-bare-Var call sites first (immutable walk), then
        // monomorphise (mutable) — avoids borrowing `self`/`state` across the walk.
        let mut inner_sites: Vec<(Symbol, Vec<Span>, Span)> = Vec::new();
        collect_apply_var_calls(defn.body(), &defn.name, &mut inner_sites);

        for (inner_name, arg_spans, inner_span) in &inner_sites {
            if resolutions.resolved_calls.contains_key(inner_span) {
                continue; // already resolved (trait method / inner constrained self-rec)
            }
            // Resolve the inner callee's terminal entry + its home, rooted in the
            // module the body was re-checked in.
            let resolved = self.resolve_terminal_entry_and_home(&recheck_module, inner_name.as_ref());
            let (entry, callee_home) = match resolved {
                Some(r) => r,
                None => continue,
            };
            if !Self::entry_is_monomorphisable_polymorphic(&entry) {
                continue;
            }
            // All arg types must be concrete (pinned during the parent recheck).
            let inner_arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| mono_expr_types.get(span).cloned())
                .collect();
            if inner_arg_types.len() != arg_spans.len() {
                continue;
            }
            // ALL-ARGS-CONCRETE GUARD (Phase-4 part A, concrete-boundary-type.md
            // §4-A). A hop reached from a GENERIC caller's body is collected with
            // the parent's OWN free scheme vars in its arg positions (the
            // `reduce → reduce-loop` 0344 fold: `f`/`acc`/element are still
            // `reduce`'s `Var34`/`Var31`). Minting on that is a SPURIOUS partial
            // instance — a re-spelling of the generic template under a lossy
            // name, not a concrete specialisation. The GENUINE concrete instance
            // is minted by the parent's CONCRETE re-check chain (e.g.
            // `reduce$Int+Vec → reduce-loop$Int+Vec+Int+Int`), which arrives here
            // with every arg pinned. Skip the hop unless every arg is concrete
            // after substitution — suppressing the spurious mint so the
            // `allowed_vars` carve-out at the mono-population seam is dead and
            // `from_expr` succeeds on every minted instance (the completeness
            // proof).
            if !inner_arg_types
                .iter()
                .all(|t| apply(&state.subst, t).is_concrete())
            {
                continue;
            }
            // FIXME 0373 (Tier 1.5 — CROSS-MODULE hops). `monomorphise_call`
            // roots its callee lookup + body re-check at `home`, falling back to
            // `state.current_module` when `home` is `None`. Crucially,
            // `recheck_body_for_mono` has ALREADY RESTORED `state.current_module`
            // to the caller's module by the time this runs — so the gate must be
            // "is the inner callee in a different module than `state.current_module`
            // NOW", not "than `recheck_module`". For a CROSS-MODULE parent hop
            // (`h1` imported from `hop`, re-checked with `recheck_module = hop` but
            // `state.current_module = user`), the inner hop `h2` lives in `hop`,
            // which differs from the current `user`; passing `None` here would make
            // `get_constrained_fn` look `h2` up in `user` (where it does not exist)
            // → `None` → `h2` never re-monomorphised at the concrete
            // `(Fn [Int] Int)` instantiation → its result stays `Type::Var` → the
            // RC-guard SIGSEGV one hop deeper (the 0373 residual). Rooting at
            // `Some(callee_home)` whenever the callee is not in the current module
            // re-checks `h2`'s body in its defining (`hop`) scope (the 0355 module
            // switch), yielding a concrete-`Int`-result `h2$` mono. A genuinely
            // same-(current-)module inner hop still passes `None` (the as-built
            // local path).
            let inner_home = if callee_home == state.current_module {
                None
            } else {
                Some(callee_home.clone())
            };
            // Isolate `state.subst` around the inner-mono recursion (FIXME 0373,
            // preserves 0344). The sole obligation of this recursion is to CREATE
            // the inner hop's concrete mono entry (`register_mono_entry`, with its
            // own GOT slot) so its result type is concrete at codegen. We must NOT
            // let the recursion's call-result unification (the FIXME 0349
            // propagation in `monomorphise_call` ~line 1339) leak back into the
            // PARENT's substitution: when the inner callee is a recursive helper
            // sharing the parent's accumulator var (the 0344 `reduce`/`reduce-loop`
            // fold), that leak pins the accumulator and re-collapses the
            // polymorphic scheme 0344 deliberately keeps. The inner entry is built
            // from `inner_arg_types` (already concrete, captured before this) +
            // the isolated subst, so isolation does not affect what gets created.
            let saved_subst = state.subst.clone();
            let inner_mono = self.monomorphise_call(
                state,
                inner_name,
                &inner_arg_types,
                *inner_span,
                inner_home.as_ref(),
            );
            state.subst = saved_subst;
            if let Some(mono) = inner_mono? {
                resolutions.resolved_calls.insert(
                    *inner_span,
                    ResolvedCall::SigDispatch {
                        mangled_name: JitSymbol::from(mono.defn.name.as_ref()),
                    },
                );
                // S110 0583 leg 1 (inner parametric-hop carrier, FIXME 0616):
                // `register_mono_entry` stored this instance in the caller's
                // current module — key its carrier there.
                resolutions.resolved_targets.insert(
                    *inner_span,
                    FQSymbol {
                        module: state.current_module.clone(),
                        symbol: Symbol::from(mono.defn.name.as_ref()),
                    },
                );
            }
        }
        Ok(())
    }

    /// Look up a constrained function by name.
    #[allow(dead_code)]
    fn get_constrained_fn(
        &self,
        state: &CheckState,
        name: &Symbol,
        home: Option<&ModuleFullPath>,
    ) -> Option<ConstrainedFn> {
        // For an IMPORTED callee (FIXME 0355), the constrained `Def` lives in its
        // DEFINING module — chain-follow to the terminal entry there. The home is
        // a committed import → live view suffices. For a local callee, read the
        // current module directly. Staging-aware (FIXME 0179): the local probe
        // reads through staging so in-cluster constrained-fn registrations are
        // visible.
        let entry = match home {
            Some(h) => self.resolve_terminal_entry_and_home(h, name.as_ref()).map(|(e, _)| e)?,
            None => self.probe_module_entry_owned(&state.current_module, name.as_ref())?,
        };
        match &entry {
            ModuleEntry::Def { kind, scheme, ast, .. } => match kind.as_ref() {
                DefKind::UserFn {
                    fn_state: UserFnState::Constrained(cf),
                } => Some(cf.as_ref().clone()),
                // Pure parametric polymorphism: the scheme is still polymorphic
                // (non-empty `vars`), no trait constraints, but the call site
                // demands a concrete specialisation. Synthesise a
                // `ConstrainedFn` view from the stored AST so the existing
                // `monomorphise_call` machinery applies. The previously-stored
                // defn AST is the source of truth for the body — it was
                // annotated and substitution-applied during the originating
                // Pass 2 / finalize pass for this defn.
                DefKind::UserFn { fn_state }
                    if !matches!(fn_state, UserFnState::Constrained(_))
                        && !scheme.type_vars.is_empty()
                        && ast.is_some() =>
                {
                    Some(ConstrainedFn {
                        variant: ast.as_ref().unwrap().clone(),
                        scheme: scheme.clone(),
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a mangled name from a function name and its concrete parameter types.
///
/// Format: `name$Type1+Type2`
/// Collect every `Apply`-of-bare-`Var` call site in an expression tree, except
/// calls a fn makes to ITSELF (generic self-recursion is not a concrete mono
/// site — its arg types are the defn's own generic vars). Records
/// `(callee_name, arg_spans, call_span)`. Used by
/// `monomorphise_inner_parametric_hops` (FIXME 0373) to find inner hops to
/// recursively monomorphise after a parent hop's body re-check.
pub(super) fn collect_apply_var_calls(
    expr: &Expr,
    self_name: &Symbol,
    out: &mut Vec<(Symbol, Vec<Span>, Span)>,
) {
    if let Expr::Apply { callee, args, span, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
        && name != self_name
    {
        let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
        out.push((name.clone(), arg_spans, *span));
    }
    crate::program::for_each_child_expr(expr, |child| {
        collect_apply_var_calls(child, self_name, out)
    });
}

/// Collect every `Apply`-of-bare-`Var` call to `self_name` (the OPPOSITE of
/// [`collect_apply_var_calls`], which excludes self-calls). Used by
/// `monomorphise_call` (FIXME 0374) to redirect a polymorphic fn's monomorphic
/// self-recursion to its own mono instance — the original `Polymorphic` def is
/// slot-less, so a by-name self-call would lower through a missing slot.
pub(super) fn collect_self_apply_calls(
    expr: &Expr,
    self_name: &Symbol,
    out: &mut Vec<(Vec<Span>, Span)>,
) {
    if let Expr::Apply { callee, args, span, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
        && name == self_name
    {
        let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
        out.push((arg_spans, *span));
    }
    crate::program::for_each_child_expr(expr, |child| {
        collect_self_apply_calls(child, self_name, out)
    });
}

pub(crate) fn build_mangled_name(
    home: &ModuleFullPath,
    fn_name: &Symbol,
    param_types: &[Type],
) -> String {
    // THE ONE canonical mono-instance name-composer (FIXME 0519, Principle 7).
    // Grammar: `{home}/{bare}${recursive-concrete-sig}` where
    //   - `home` = the DEFINING module's `ModuleFullPath` (distinguishes two
    //     same-named imported generics `a/twist` vs `b/twist` registered into
    //     one consumer table → cures the 0508 home-erasure silent miscompile);
    //   - the sig recurses EVERY concrete param type through the ONE canonical
    //     total type-mangler `program::mangle_type` — ADT args are recursed
    //     (`Vec$Int` ≠ `Vec$String`, curing 0483) and `Fn` params are recursed
    //     rather than dropped (curing the latent Fn-param-drop collision axis).
    //
    // Collision-free BY CONSTRUCTION (Principle 20): the name is a pure function
    // of (defining home, bare name, recursively-mangled concrete sig); two
    // instantiations differing in any one fact mint different names, and the
    // "two distinct instantiations → one name" state is unrepresentable. All
    // three facts are persisted (module path, symbol, concrete param types), so
    // the name is cache-safe / compile-order-independent.
    //
    // TRIPWIRE (Phase-4 part A, concrete-boundary-type.md §4-A "secondary
    // hardening", Principle 18). After the all-args-concrete collection gate,
    // every minted instance has all-CONCRETE params. A residual `Type::Var`
    // reaching here is a lossy-name hazard (`mangle_type` would emit the shared
    // token `Var`, collapsing two distinct partial instantiations). The §9.3
    // concreteness gate in `monomorphise_call` returns a clean type error one
    // step earlier; this `debug_assert!` is the belt-and-braces backstop for a
    // future spurious-mint site.
    debug_assert!(
        param_types.iter().all(|t| t.is_concrete()),
        "build_mangled_name({home}/{fn_name}) saw a non-concrete param type \
         (lossy-name hazard — a spurious partial mono instance reached the \
         mangler): {param_types:?}"
    );
    let sig = param_types
        .iter()
        .map(crate::program::mangle_type)
        .collect::<Vec<_>>()
        .join("+");
    format!("{home}/{fn_name}${sig}")
}

/// Extract the bare TypeName from a concrete (non-Var) type.
/// For ADTs, returns the bare name without module qualification.
/// This is used for mangled name construction and impl registry lookup.
pub(crate) fn concrete_type_name(ty: &Type) -> Option<TypeName> {
    match ty {
        Type::Int => Some(TypeName::from("Int")),
        Type::Float => Some(TypeName::from("Float")),
        Type::Bool => Some(TypeName::from("Bool")),
        Type::String => Some(TypeName::from("String")),
        Type::ADT(fqtn, _) => Some(fqtn.name.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
