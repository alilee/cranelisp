use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    ApplyRef, CallableOrigin, CallableTarget, ConcreteType, CranelispError, Defn, DefnVariant,
    ErrorLocation, Expr, FQSymbol, FQTypeName, InstanceLink, JitSymbol, Life, MethodResolutions,
    ModuleFullPath, MonoDefn, MonoDefnVariant, MonoDemand, MonoExpr, NotConcrete, Realization,
    ResolvedCall, Scheme, Span, Symbol, TemplateBody, Type, TypeName, VarRef, ViewBuildError,
    Visibility, apply, concrete_callable_key, free_vars,
};

use crate::checker::{CheckState, TypeCheckEnv};

#[derive(Clone)]
pub(crate) struct TemplateCore {
    pub(crate) body: TemplateBody,
    pub(crate) scheme: Scheme,
    pub(crate) origin: CallableOrigin,
}

#[derive(Clone)]
pub(crate) struct TemplateFn {
    pub(crate) core: TemplateCore,
    /// Semantic declaration body which owns this template. Ordinary templates
    /// derive a binding target from `fn_name`; owned overload arms provide it.
    pub(crate) template_target: Option<CallableTarget>,
}

/// The same-cluster template set of one settlement window
/// (`design/typecheck/monomorphisation.md` §3.10.2): the cluster's checked
/// bodies that are still templates, keyed by canonical identity.
#[derive(Clone)]
pub(crate) struct MonoWindow {
    module: ModuleFullPath,
    templates: HashMap<Symbol, TemplateCore>,
}

impl MonoWindow {
    pub(crate) fn new(module: ModuleFullPath, templates: HashMap<Symbol, TemplateCore>) -> Self {
        MonoWindow { module, templates }
    }

    /// A window with no same-cluster templates, as replay has: its templates
    /// are published.
    pub(crate) fn empty(module: ModuleFullPath) -> Self {
        Self::new(module, HashMap::new())
    }

    /// The template for a resolved callee, only when the callee belongs to
    /// the cluster this window settles.
    pub(crate) fn template(&self, callee: &FQSymbol) -> Option<&TemplateCore> {
        (callee.module == self.module)
            .then(|| self.templates.get(&callee.symbol))
            .flatten()
    }
}

/// Spec §3.10's instantiation depth limit: a chain of implementation
/// instantiations deeper than this is a type error. Spec admits any limit of
/// at least 64.
pub(crate) const INSTANTIATION_DEPTH_LIMIT: usize = 64;

/// One implementation at one concrete implementing type: the counting unit
/// of the depth limit (`monomorphisation.md` §3.10.3).
#[derive(Clone, PartialEq)]
struct ImplementationInstantiation {
    shell: FQSymbol,
    /// The concrete type the dispatch selected the implementation by; `None`
    /// for a higher-kinded implementation, whose constructor is the shell's.
    receiver: Option<Type>,
}

/// A successor demand found inside a rechecked instance (§3.10).
struct Successor {
    fn_name: Symbol,
    demand: MonoDemand,
    home: Option<ModuleFullPath>,
    template: TemplateFn,
    site: SuccessorSite,
}

/// A successor after its out-of-line preparation. Moved once, never stored.
#[allow(clippy::large_enum_variant)]
enum SuccessorStep {
    /// The site is redirected to this key: installed, on the chain, or
    /// settled without a recheck.
    Redirect(Symbol),
    /// No mono target: the site keeps its verdict.
    Unsettled,
    Mint(Box<MintInProgress>, ChainLink, Option<ModuleFullPath>),
}

/// Successor demands, boxed so the settling loop, live across the recursion,
/// holds a pointer each.
#[allow(clippy::vec_box)]
type Successors = Vec<Box<Successor>>;

/// A rechecked instance body's harvest: its own resolutions and expression
/// types, and the successor demands still to settle.
struct RecheckHarvest {
    resolutions: MethodResolutions,
    mono_expr_types: HashMap<Span, Type>,
    successors: Successors,
}

/// Where a successor's instance is recorded: a call's dispatch, or a value
/// reference.
#[derive(Clone, Copy)]
enum SuccessorSite {
    Call(Span),
    Value(Span),
}

/// What preparing a mint yields: an instance settled without a recheck (or
/// no mono target), or an authored body to recheck with its chain element.
enum PreparedMint {
    Settled(Option<MonoDefn>),
    Recheck(Box<MintInProgress>, ChainLink),
}

/// A mint between its preparation and completion.
struct MintInProgress {
    fn_name: Symbol,
    scheme: Scheme,
    origin: CallableOrigin,
    link: InstanceLink,
    instance_key: Symbol,
    mangled_name: String,
    concrete_param_types: Vec<Type>,
    concrete_ret_ty: Type,
    defn: DefnVariant,
    wrap_defn: Defn,
}

/// A demand being minted: one element of the in-progress chain
/// (`monomorphisation.md` §3.9 channel 5).
pub(crate) struct ChainLink {
    key: Symbol,
    template: FQSymbol,
    signature: Type,
    implementation: Option<ImplementationInstantiation>,
    /// Whether this element adds one to the chain's depth.
    counts: bool,
}

// ---------------------------------------------------------------------------
// Constrained Instantiation
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    pub(crate) fn demand_instance_key(
        demand: &MonoDemand,
        scheme: &Scheme,
    ) -> Result<Symbol, CranelispError> {
        demand
            .instance_key(scheme)
            .map_err(|error| CranelispError::TypeError {
                message: format!(
                    "could not derive the concrete instance key for {:?}: {error}",
                    demand.template
                ),
                location: ErrorLocation::from_span(demand.site),
            })
    }

    pub(crate) fn derive_mono_demand(
        &self,
        state: &CheckState,
        template: CallableTarget,
        scheme: &Scheme,
        use_type: &Type,
        site: Span,
    ) -> Option<MonoDemand> {
        let (inst_type, mapping) = self.fresh_mono_signature(scheme);
        let mut subst = cranelisp_types::Subst::new();
        crate::unify::unify_with_rigid(
            &mut subst,
            &HashSet::new(),
            &inst_type,
            &apply(&state.subst, use_type),
        )
        .ok()?;
        let type_args = ordered_generic_vars(scheme)
            .into_iter()
            .map(|id| ConcreteType::from_type(&apply(&subst, &Type::Var(mapping[&id]))))
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        Some(MonoDemand::from_type_args(template, type_args, site))
    }

    fn fresh_mono_signature(
        &self,
        scheme: &Scheme,
    ) -> (
        Type,
        HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>,
    ) {
        let bound: HashSet<_> = scheme.type_vars.iter().copied().collect();
        let mut subst = cranelisp_types::Subst::new();
        let mut mapping = HashMap::new();
        for &id in &scheme.type_vars {
            let (ty, fresh) = loop {
                let pair = self.fresh_var_id();
                if !bound.contains(&pair.1) {
                    break pair;
                }
            };
            subst.insert(id, ty);
            mapping.insert(id, fresh);
        }
        (apply(&subst, &scheme.ty), mapping)
    }

    /// Instantiate a constrained scheme, tracking the constraints on fresh vars.
    ///
    /// Returns the instantiated type. Side effect: adds constraints to
    /// `self.state.active_constraints`.
    pub(crate) fn instantiate_constrained(&self, state: &mut CheckState, scheme: &Scheme) -> Type {
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
    /// The demand supplies every concrete generic substitution, including result context.
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
        demand: &MonoDemand,
        home: Option<&ModuleFullPath>,
        origin_base: Option<&Symbol>,
        local_template: Option<TemplateFn>,
    ) -> Result<Option<MonoDefn>, CranelispError> {
        match self.prepare_mint(state, fn_name, demand, home, local_template)? {
            PreparedMint::Settled(instance) => Ok(instance),
            PreparedMint::Recheck(mint, link) => {
                self.recheck_mint(state, mint, link, home, origin_base)
            }
        }
    }

    /// P0–P2: look up the template, reconstruct the signature from the demand
    /// and check its key, verify constraints, and settle a synthesised
    /// template directly. An authored body comes back boxed for its recheck,
    /// with its chain element; a demand past the depth limit is refused here.
    ///
    /// Kept out of line so its locals are not live across the successor
    /// recursion (`monomorphisation.md` §3.10.3, the chain is host recursion).
    #[inline(never)]
    fn prepare_mint(
        &self,
        state: &mut CheckState,
        fn_name: &Symbol,
        demand: &MonoDemand,
        home: Option<&ModuleFullPath>,
        local_template: Option<TemplateFn>,
    ) -> Result<PreparedMint, CranelispError> {
        let call_span = demand.site;
        // `home` selects the lookup module; `None` is the "not a mono target"
        // signal callers depend on (`Ok(None)` vs `Ok(Some)`).
        let Some(constrained_fn) =
            local_template.or_else(|| self.get_constrained_fn(state, fn_name, home))
        else {
            return Ok(PreparedMint::Settled(None));
        };
        let TemplateCore {
            body: template_body,
            scheme,
            origin,
        } = constrained_fn.core;

        // Reconstruct the complete signature from the demand before allocating an identity.
        // The fresh-variable mapping also owns constraint verification across modules.
        let (resolved, var_mapping) =
            self.instantiate_and_resolve(state, &scheme, &demand.type_args, call_span)?;
        let Type::Fn(concrete_param_types, concrete_ret_ty) = &resolved else {
            return Ok(PreparedMint::Settled(None));
        };
        let concrete_param_types = concrete_param_types.clone();
        let concrete_ret_ty = (**concrete_ret_ty).clone();

        // Reject malformed template signatures before publication.
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

        // Preserve the demand's identity through naming and publication.
        let link = demand.instance_link();
        let instance_key = Self::demand_instance_key(demand, &scheme)?;
        let resolved_key = Self::realized_instance_key(&link, &resolved, call_span)?;
        if instance_key != resolved_key {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "demand key `{instance_key}` does not match realized signature key \
                     `{resolved_key}` for `{fn_name}`"
                ),
                location: ErrorLocation::from_span(call_span),
            });
        }
        let mangled_name = String::from(instance_key.as_ref());

        self.verify_mono_constraints(state, &scheme, &var_mapping, home, call_span)?;

        // Synthesized templates have no authored body or span-keyed check-run
        // sidecars.  Re-run their derivation at the concrete signature and
        // settle the ordinary instance directly (A-MINT); never send them
        // through the source-body recheck path below.
        let defn = match template_body {
            TemplateBody::Synth(synth) => {
                return self
                    .monomorphise_synth(
                        state,
                        fn_name,
                        synth,
                        link,
                        &instance_key,
                        origin,
                        &mangled_name,
                        &concrete_param_types,
                        &concrete_ret_ty,
                    )
                    .map(PreparedMint::Settled);
            }
            TemplateBody::Ast(defn) => defn,
            // Uniform Rust templates are served through facades and do not
            // acquire a source/body instance in this engine.
            _ => return Ok(PreparedMint::Settled(None)),
        };

        // The in-progress chain (§3.10.3): refuse a demand that would take the
        // chain past the depth limit.
        let chain_link = self.chain_link(
            state,
            &link,
            instance_key.clone(),
            &origin,
            &resolved,
            call_span,
        )?;
        if chain_link.counts && chain_depth(&state.mono_chain) >= INSTANTIATION_DEPTH_LIMIT {
            return Err(depth_refusal(
                &state.mono_chain,
                &chain_link,
                &origin,
                call_span,
            ));
        }

        // `defn: DefnVariant` (S70 ConstrainedFn narrowing). Wrap in a
        // temporary single-variant `Defn` for the recheck helpers which
        // still take `&mut Defn`. The post-passes annotate THIS clone.
        let wrap_defn = Defn {
            name: fn_name.clone(),
            docstring: None,
            variants: vec![defn.clone()],
            visibility: Visibility::Public,
            span: defn.span,
        };
        Ok(PreparedMint::Recheck(
            Box::new(MintInProgress {
                fn_name: fn_name.clone(),
                scheme,
                origin,
                link,
                instance_key,
                mangled_name,
                concrete_param_types,
                concrete_ret_ty,
                defn,
                wrap_defn,
            }),
            chain_link,
        ))
    }

    /// P4: recheck the body with the demand held on the chain, then settle
    /// its successors. This frame and the settling frames are the ones live
    /// across the successor recursion (§3.10.3: the chain is host recursion),
    /// so they hold only boxes; the work is done out of line.
    fn recheck_mint(
        &self,
        state: &mut CheckState,
        mut mint: Box<MintInProgress>,
        chain_link: ChainLink,
        home: Option<&ModuleFullPath>,
        origin_base: Option<&Symbol>,
    ) -> Result<Option<MonoDefn>, CranelispError> {
        let saved_recursion = self.enter_mint(state, &mint, chain_link, origin_base);
        let harvest = self.recheck_and_resolve_inner(
            state,
            &mut mint.wrap_defn,
            &mint.concrete_param_types,
            &mint.concrete_ret_ty,
            home,
        );
        let settled = match harvest {
            Ok(mut harvest) => self
                .settle_successors(state, &mut harvest)
                .map(|()| harvest),
            Err(error) => Err(error),
        };
        state.mono_chain.pop();
        state.mono_recheck_self = saved_recursion;
        self.complete_mint(state, mint, settled?, home).map(Some)
    }

    /// Hold the demand on the chain and, for a multi-signature clause, carry
    /// its concrete self-recursion identity into this recheck only. Returns
    /// the context to restore, unconditionally, when the recheck ends.
    #[inline(never)]
    fn enter_mint(
        &self,
        state: &mut CheckState,
        mint: &MintInProgress,
        chain_link: ChainLink,
        origin_base: Option<&Symbol>,
    ) -> Option<crate::checker::MonoRecursionContext> {
        state.mono_chain.push(chain_link);
        std::mem::replace(
            &mut state.mono_recheck_self,
            origin_base.map(|base| crate::checker::MonoRecursionContext {
                base: base.clone(),
                instance: JitSymbol::from(mint.mangled_name.as_str()),
                params: mint.concrete_param_types.clone(),
                ret: mint.concrete_ret_ty.clone(),
            }),
        )
    }

    /// P5–P7: self-recursion dispatch, the annotated instance, its codegen
    /// view and its installation.
    #[inline(never)]
    fn complete_mint(
        &self,
        state: &mut CheckState,
        mint: Box<MintInProgress>,
        harvest: Box<RecheckHarvest>,
        home: Option<&ModuleFullPath>,
    ) -> Result<MonoDefn, CranelispError> {
        let RecheckHarvest {
            mut resolutions,
            mono_expr_types,
            ..
        } = *harvest;
        let MintInProgress {
            fn_name,
            scheme,
            origin,
            link,
            instance_key,
            mangled_name,
            concrete_param_types,
            concrete_ret_ty,
            defn,
            wrap_defn,
        } = *mint;

        // === P5 — self-recursion dispatch (0374) ===
        self.record_self_recursion_dispatch(
            &wrap_defn,
            state,
            &scheme,
            &link,
            &fn_name,
            &mangled_name,
            &mono_expr_types,
            &mut resolutions,
            &state.current_module,
        );

        // === P6 — build annotated mono defn ===
        let mono_defn_ast = self.build_annotated_mono_defn(
            state,
            &fn_name,
            &mangled_name,
            &defn,
            &mono_expr_types,
            &resolutions,
            home,
        );

        // === P7 — concrete-boundary view + register ===
        self.finalize_mono_codegen_view(
            state,
            mono_defn_ast,
            link,
            &instance_key,
            origin,
            &mangled_name,
            &concrete_param_types,
            &concrete_ret_ty,
            defn.span,
            &resolutions,
        )
    }

    /// Re-synthesise a constructor/accessor template at concrete arguments.
    #[allow(clippy::too_many_arguments)]
    fn monomorphise_synth(
        &self,
        state: &mut CheckState,
        fn_name: &Symbol,
        synth: cranelisp_types::SynthSpec,
        link: InstanceLink,
        instance_key: &Symbol,
        origin: CallableOrigin,
        mangled_name: &str,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
    ) -> Result<Option<MonoDefn>, CranelispError> {
        let parameter_vars: HashSet<_> = concrete_param_types.iter().flat_map(free_vars).collect();
        if free_vars(concrete_ret_ty)
            .iter()
            .any(|var| !parameter_vars.contains(var))
        {
            return Ok(None);
        }
        let mut variant = synth.variant;
        let variant_span = variant.span;
        match (&origin, &mut variant.body) {
            (
                CallableOrigin::Ctor { .. },
                Expr::ConstrADT {
                    fields,
                    inferred_type,
                    ..
                },
            ) => {
                *inferred_type = Some(Box::new(concrete_ret_ty.clone()));
                for (field, ty) in fields.iter_mut().zip(concrete_param_types) {
                    field.set_inferred_type(Some(Box::new(ty.clone())));
                }
            }
            (
                CallableOrigin::Accessor { type_name, .. },
                Expr::Match {
                    scrutinee,
                    arms,
                    inferred_type,
                    ..
                },
            ) => {
                let Some(receiver_ty) = concrete_param_types.first() else {
                    return Ok(None);
                };
                scrutinee.set_inferred_type(Some(Box::new(receiver_ty.clone())));
                for arm in arms.iter_mut() {
                    arm.body
                        .set_inferred_type(Some(Box::new(concrete_ret_ty.clone())));
                }
                let _ = type_name;
                *inferred_type = Some(Box::new(concrete_ret_ty.clone()));
            }
            _ => {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "synthesis recipe for `{fn_name}` does not match its callable origin"
                    ),
                    location: ErrorLocation::from_span(variant.span),
                });
            }
        }

        let mut pattern_ctors = HashMap::new();
        if let CallableOrigin::Accessor { type_name, .. } = &origin
            && let Expr::Match { arms, .. } = &variant.body
        {
            for arm in arms {
                if let cranelisp_types::Pattern::Constructor { name, span, .. } = &arm.pattern {
                    let symbol = if name.name.as_ref() == type_name.name.as_ref() {
                        name.name.clone()
                    } else {
                        cranelisp_types::member_key(&type_name.name, name.name.as_ref())
                    };
                    pattern_ctors.insert(
                        *span,
                        FQSymbol {
                            module: type_name.module.clone(),
                            symbol,
                        },
                    );
                }
            }
        }
        let view = MonoDefnVariant {
            name: Symbol::from(mangled_name),
            params: variant
                .params
                .iter()
                .map(|(name, _)| name.clone())
                .collect(),
            body: MonoExpr::synthetic_local_from_expr(&variant.body, &pattern_ctors),
            span: variant.span,
            mode_summary: None,
        };
        let defn = Defn {
            name: Symbol::from(mangled_name),
            docstring: None,
            variants: vec![variant],
            visibility: Visibility::Public,
            span: variant_span,
        };
        let mono = MonoDefn { defn };
        self.register_mono_entry(
            state,
            &mono,
            link,
            instance_key,
            origin,
            concrete_param_types,
            concrete_ret_ty,
            view,
        )?;
        Ok(Some(mono))
    }

    /// P2 — verify trait constraints, with `current_module` switched to `home`
    /// for the impl lookup of an IMPORTED callee (FIXME 0355).
    ///
    /// For an IMPORTED callee, the trait + impl referenced by the constraint
    /// live in the DEFINING module's scope, so switch `current_module` to
    /// `home` for the impl lookup (mirrors `recheck_body_for_mono`'s module
    /// switch). The switch is **restored unconditionally** BEFORE the result is
    /// `?`-propagated. The impl probe itself is keyed at the constraint's trait
    /// home and reads no `current_module`; the switch now affects only how the
    /// no-impl diagnostic renders the type.
    fn verify_mono_constraints(
        &self,
        state: &mut CheckState,
        scheme: &Scheme,
        var_mapping: &HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>,
        home: Option<&ModuleFullPath>,
        call_span: Span,
    ) -> Result<(), CranelispError> {
        let saved_module = home.map(|h| std::mem::replace(&mut state.current_module, h.clone()));
        let verify_result = self.verify_constraints(state, scheme, var_mapping, call_span);
        if let Some(prev) = saved_module {
            state.current_module = prev;
        }
        verify_result
    }

    /// P4 — re-check the mono body with concrete types and harvest its
    /// resolutions and its successor demands, which the caller settles.
    ///
    /// `recheck_body_for_mono` saves/restores `method_resolutions`/`expr_types`/
    /// `pending_auto_curry`/`current_module` itself, and the post-passes
    /// annotate the SAME `wrap_defn` clone (passed by `&mut`).
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
    /// So after re-checking this hop's body we collect the inner
    /// polymorphic-result hops it reached, using the concrete types now pinned
    /// in `mono_expr_types`. `settle_successor` isolates `state.subst` around
    /// EACH inner recursion (0344) — that isolation stays there; do NOT lift
    /// it to this driver.
    #[inline(never)]
    fn recheck_and_resolve_inner(
        &self,
        state: &mut CheckState,
        wrap_defn: &mut Defn,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        home: Option<&ModuleFullPath>,
    ) -> Result<Box<RecheckHarvest>, CranelispError> {
        let (resolutions, mono_expr_types) = self.recheck_body_for_mono(
            state,
            wrap_defn,
            concrete_param_types,
            concrete_ret_ty,
            home,
        )?;
        let successors =
            self.instance_successors(state, wrap_defn, &mono_expr_types, &resolutions, home);
        Ok(Box::new(RecheckHarvest {
            resolutions,
            mono_expr_types,
            successors,
        }))
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
        state: &CheckState,
        scheme: &Scheme,
        link: &InstanceLink,
        fn_name: &Symbol,
        mangled_name: &str,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &mut MethodResolutions,
        current_module: &ModuleFullPath,
    ) {
        let mut self_calls = Vec::new();
        collect_self_apply_calls(wrap_defn.body(), fn_name, &mut self_calls);
        for (callee_span, arg_spans, self_span) in &self_calls {
            if resolutions.resolved_calls.contains_key(self_span) {
                continue;
            }
            // Fix 1 (/arch-directed) — the frame-guarded self-call discriminator.
            // A `(s1 x)` whose callee `s1` is a `let`/`fn`/param binding shadowing
            // the base (`(defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))`) is NOT
            // monomorphic self-recursion — it is a LOCAL indirect call. The ONE
            // shared discriminator `is_recursion_self_ref` (via
            // `record_reference_target`, run at `infer_var` during THIS recheck)
            // already made the verdict: a genuine self-call — the base resolving at
            // the recursion frame — records a `var_refs` `VarRef::Global` callee
            // carrier (S114 carrier flip — was a `resolved_targets` carrier); a
            // deeper-frame shadow records `VarRef::Local` (not `Global`). So
            // a self-apply whose callee span carries no `Global` target is a shadow:
            // record
            // NO SigDispatch, NO carrier → the Apply reaches the backend fully bare
            // → `compile_var_apply` → `variables` → indirect local call (fixes the
            // TCO-self-loop hang + the non-tail wrong-value sibling).
            if !crate::program::callee_has_keyed_carrier(&resolutions.var_refs, *callee_span) {
                continue;
            }
            let Some(use_type) =
                Self::mono_call_type(state, mono_expr_types, resolutions, arg_spans, *self_span)
            else {
                continue;
            };
            let Some(demand) = self.derive_mono_demand(
                state,
                link.template.clone(),
                scheme,
                &use_type,
                *self_span,
            ) else {
                continue;
            };
            if demand.instance_link() == *link {
                record_instance_dispatch(
                    resolutions,
                    current_module,
                    *self_span,
                    &Symbol::from(mangled_name),
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
    /// `state.subst` after the scoped body recheck.
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
                .and_then(|(entry, _)| {
                    entry
                        .callable()
                        .map(|c| (c.docstring.clone(), entry.visibility))
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
    /// (`local_parametric_call_triggers` + `parametric_hop_successors`
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
        link: InstanceLink,
        instance_key: &Symbol,
        origin: CallableOrigin,
        mangled_name: &str,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        defn_span: Span,
        resolutions: &MethodResolutions,
    ) -> Result<MonoDefn, CranelispError> {
        // The check-run pairing rule (S110 W3.1, FIXME 0622,
        // `backend-keyed-consumer.md` §1.1.3): a codegen view is built from the
        // SAME `MethodResolutions` instance that the body-check run which
        // annotated this body populated — never from a map restored from,
        // accumulated for, or belonging to a different check run.
        //
        // Here that instance is the PER-INSTANCE `resolutions` returned by
        // `recheck_body_for_mono` (which switched `current_module` to `home` and
        // re-recorded every carrier for this instance: `infer_var` Var-refs, the
        // P4/P5 dispatch selections, the in-swap auto-curry drain, AND — via
        // `check_constructor_pattern` → `instantiate_ctor` — every ctor-pattern
        // span, defining-module-correct). It is NOT `state.method_resolutions`:
        // `recheck_body_for_mono` restored the ENCLOSING map before this seam,
        // and that map carries neither the mono-time dispatch SELECTIONS (a
        // self-call / sig-dispatch minted per instance — `f$Int` vs `f$Float` at
        // the SAME template span, so a shared map would collide) NOR — the 0622
        // fix — the template's `pattern_ctors` when the template was checked in a
        // DIFFERENT run (cross-module, or cross-check-run same-module REPL-
        // incremental). Read BOTH sidecars off the one per-instance map.
        let codegen_view = match MonoExpr::from_expr(
            mono_defn_ast.body(),
            &resolutions.pattern_ctors,
            &resolutions.var_refs,
            &resolutions.apply_refs,
        ) {
            Ok(mono_body) => {
                // Genuinely concrete instance — carry the concrete-boundary view.
                MonoDefnVariant {
                    name: Symbol::from(mangled_name),
                    params: mono_defn_ast
                        .params()
                        .iter()
                        .map(|(n, _)| n.clone())
                        .collect(),
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
            Err(ViewBuildError::NotConcrete(nc)) => {
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
            // S114 carrier flip (design §4.3): an unresolved reference in a
            // minted instance body is a distinct producer bug — a located
            // typecheck error at the reference span (should never fire on a
            // valid program; the tier-3 seam altitude surfaced as an error since
            // a `Result` is in hand here).
            Err(ViewBuildError::Unresolved {
                span,
                name: ref_name,
            }) => {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "unresolved reference `{ref_name}` in monomorphised body \
                         of `{mangled_name}` — typecheck recorded no local/global \
                         verdict (in-process producer bug; \
                         design/arch/typed-resolution-carrier.md §4.3)"
                    ),
                    location: ErrorLocation::from_span(span),
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
            link,
            instance_key,
            origin,
            concrete_param_types,
            concrete_ret_ty,
            codegen_view,
        )?;

        Ok(mono_defn)
    }

    /// Register a mono specialisation on the current module's symbol table
    /// as a `ModuleEntry::Def` with `ast: Some(annotated)`. Wave 0 §9.4.
    fn register_mono_entry(
        &self,
        state: &mut CheckState,
        mono: &MonoDefn,
        link: InstanceLink,
        expected_instance_key: &Symbol,
        origin: CallableOrigin,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        codegen_view: MonoDefnVariant,
    ) -> Result<(), CranelispError> {
        let fn_ty = Type::Fn(
            concrete_param_types.to_vec(),
            Box::new(concrete_ret_ty.clone()),
        );
        let instance_key = Self::realized_instance_key(&link, &fn_ty, mono.defn.span)?;
        if &instance_key != expected_instance_key {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "prepared instance key `{expected_instance_key}` does not match realized \
                     signature key `{instance_key}`"
                ),
                location: ErrorLocation::from_span(mono.defn.span),
            });
        }
        let scheme = crate::scheme::mono(fn_ty);

        let already_installed = {
            let table = self.current_symbol_table(state);
            let view = table.view();
            view.lookup(&instance_key)
                .and_then(|binding| binding.callable())
                .is_some_and(|callable| {
                    callable.arm.scheme.type_vars == scheme.type_vars
                        && callable.arm.scheme.constraints == scheme.constraints
                        && callable.arm.scheme.ty == scheme.ty
                        && matches!(
                            &callable.arm.life,
                            Life::Concrete {
                                minted_from: Some(existing),
                                ..
                            } if existing == &link
                        )
                })
        };
        if already_installed {
            return Ok(());
        }
        let ast = mono.defn.variants.first().cloned();
        self.current_symbol_table_mut(state)
            .install_instance(
                link,
                scheme,
                mono.defn.params().iter().map(|(n, _)| n.clone()).collect(),
                mono.defn.docstring.clone(),
                0,
                origin,
                Realization::Body {
                    view: codegen_view,
                    code: None,
                },
                ast,
                Vec::new(),
                mono.defn.visibility,
            )
            .map_err(crate::result::lifecycle_error)?;
        Ok(())
    }

    fn realized_instance_key(
        link: &InstanceLink,
        signature: &Type,
        span: Span,
    ) -> Result<Symbol, CranelispError> {
        let owner = match &link.template {
            CallableTarget::Binding(owner) | CallableTarget::OverloadArm { owner, .. } => owner,
            CallableTarget::MacroClause { .. } => {
                return Err(CranelispError::CodegenError {
                    message: "macro clauses do not have language-callable instance keys"
                        .to_string(),
                    location: ErrorLocation::from_span(span),
                });
            }
            _ => {
                return Err(CranelispError::CodegenError {
                    message: "unsupported callable target for a concrete instance".to_string(),
                    location: ErrorLocation::from_span(span),
                });
            }
        };
        let concrete =
            ConcreteType::from_type(signature).map_err(|error| CranelispError::TypeError {
                message: format!("instance signature is not concrete: {error:?}"),
                location: ErrorLocation::from_span(span),
            })?;
        concrete_callable_key(owner, &concrete).map_err(|error| CranelispError::CodegenError {
            message: format!("could not derive the realized instance key: {error}"),
            location: ErrorLocation::from_span(span),
        })
    }

    /// Instantiate a scheme with fresh type variables, unify with the given
    /// argument types, and return the fully-resolved function type.
    fn instantiate_and_resolve(
        &self,
        state: &mut CheckState,
        scheme: &Scheme,
        type_args: &[ConcreteType],
        call_span: Span,
    ) -> Result<
        (
            Type,
            HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>,
        ),
        CranelispError,
    > {
        let ordered = ordered_generic_vars(scheme);
        if type_args.len() != ordered.len() {
            return Err(CranelispError::TypeError {
                message: format!(
                    "generic argument count mismatch: expected {}, got {}",
                    ordered.len(),
                    type_args.len()
                ),
                location: ErrorLocation::from_span(call_span),
            });
        }
        let (inst_type, var_mapping) = self.fresh_mono_signature(scheme);
        for (id, ty) in ordered.iter().zip(type_args) {
            self.unify(state, &Type::Var(var_mapping[id]), &ty.to_type(), call_span)?;
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
            for fq_trait in traits {
                // D2/§7.0.1 P24 — `fq_trait` already holds the trait's HOME, so
                // the shared step roots the impl lookup there rather than
                // re-resolving the bare name in the caller's scope, which
                // wrong-rejects a method-only import ("no impl of trait
                // blib/Bump for type Int").
                if self.trait_satisfaction(fq_trait, &resolved_var)
                    != super::TraitSatisfaction::Unsatisfied
                {
                    continue;
                }
                // `fq_trait` is already FQ; render the impl type FQ too so the
                // message disambiguates two same-named ADTs (S87-1).
                let fq_impl_type = match concrete_type_name(&resolved_var) {
                    Some(impl_type) => {
                        self.fq_type_name_for_diagnostics(state, &impl_type, call_span)
                    }
                    None => cranelisp_types::render_type(
                        &resolved_var,
                        cranelisp_types::PrimitiveNaming::Qualified,
                        cranelisp_types::VarNaming::Numbered,
                    ),
                };
                return Err(CranelispError::TypeError {
                    message: format!("no impl of trait {} for type {}", fq_trait, fq_impl_type),
                    location: ErrorLocation::from_span(call_span),
                });
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
        // §11.8.3 leg R2 (W2a /review Important 1) — isolate the OUTER pending
        // overloads so the scoped drain below resolves ONLY the dispatch calls
        // THIS mono body defers (`(h 1)` inside `ga$Int`). Without isolation those
        // deferrals would either leak to the single top-level drain (landing in
        // the wrong, outer resolutions map — the original R2 carrier-loss) or —
        // for a D3-harvest recheck that runs AFTER that drain — be dropped
        // entirely (the residual-unbound-var wrong-reject, Important 1b).
        let saved_pending_overloads = std::mem::take(&mut state.pending_overload_resolutions);
        // Switch into the defining module for an imported callee so the body's
        // bare-name references resolve in its import context (FIXME 0355).
        let saved_current_module =
            home.map(|h| std::mem::replace(&mut state.current_module, h.clone()));

        let result =
            self.check_defn_body_with_types(state, defn, concrete_param_types, concrete_ret_ty);

        let resolutions = std::mem::take(&mut state.method_resolutions);
        let mono_expr_types: HashMap<Span, Type> = state
            .expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();

        state.method_resolutions = saved_resolutions;
        state.expr_types = saved_expr_types;
        state.pending_auto_curry = saved_pending_auto_curry;
        state.pending_overload_resolutions = saved_pending_overloads;
        // Restore the caller's module unconditionally (mirrors the side-state
        // save/restore discipline above).
        if let Some(prev) = saved_current_module {
            state.current_module = prev;
        }

        result?;
        Ok((resolutions, mono_expr_types))
    }

    /// The free-function hops a just-rechecked mono body reached (FIXME 0373,
    /// Tier 1 — multi-hop concrete-type propagation; /arch ruling (A)).
    ///
    /// A nested hop can settle only during its parent's recheck, so its
    /// complete demand is derived from that recheck's captured maps.
    ///
    /// For each inner `Apply`-of-bare-`Var` call read through its callee whose
    /// callee resolves to a monomorphisable polymorphic `Def` (constrained OR
    /// pure-parametric) or to a template of the window, with its full use type
    /// settled in `mono_expr_types`, the demand is collected. The callee's
    /// HOME is the recheck module for an inner hop reached from an imported
    /// hop; a callee in a different module than the recheck scope gets
    /// `Some(its_home)` so its own body re-checks in the right import context
    /// (the 0355 module switch).
    fn parametric_hop_successors(
        &self,
        state: &CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &MethodResolutions,
        home: Option<&ModuleFullPath>,
        successors: &mut Successors,
    ) {
        // The scope the body was re-checked in: `home` for an imported hop, else
        // the caller's current module.
        let recheck_module = home
            .cloned()
            .unwrap_or_else(|| state.current_module.clone());

        let mut inner_sites: Vec<(Symbol, Vec<Span>, Span)> = Vec::new();
        // FIXME 0653 — gate the name-scan on the recheck's carriers: a §4.6 local
        // shadow of a parametric hop carries `VarRef::Local`, not the
        // `VarRef::Global` `callee_has_keyed_carrier` admits (S114 carrier flip —
        // was "no `resolved_targets` carrier").
        collect_apply_var_calls(
            defn.body(),
            &defn.name,
            &resolutions.var_refs,
            &mut inner_sites,
        );

        for (inner_name, arg_spans, inner_span) in &inner_sites {
            // A `Dispatch` verdict classifies the site by itself: a template
            // target is the dispatch hop's, a concrete one is settled. Only a
            // site read through its callee is a free-function hop.
            if matches!(
                resolutions.apply_refs.get(inner_span),
                Some(ApplyRef::Dispatch(_))
            ) || resolutions.resolved_calls.contains_key(inner_span)
            {
                continue;
            }
            // Resolve the inner callee's terminal entry + its home, rooted in the
            // module the body was re-checked in.
            let resolved = self
                .scope_resolve_in(&recheck_module, inner_name.as_ref(), Span::SYNTHETIC)
                .ok();
            let (entry, callee) = match resolved {
                Some(resolved) => (resolved.entry, resolved.canonical),
                None => continue,
            };
            // Same-cluster checked templates stay `Declared` until final
            // settlement; the window's set answers for them, by identity.
            let local_core = state
                .mono_window
                .as_ref()
                .and_then(|window| window.template(&callee).cloned());
            if local_core.is_none() && !Self::entry_is_monomorphisable_polymorphic(&entry) {
                continue;
            }
            let inner_home = if callee.module == state.current_module {
                None
            } else {
                Some(callee.module.clone())
            };
            let template = local_core
                .map(|core| TemplateFn {
                    core,
                    template_target: Some(CallableTarget::Binding(callee.clone())),
                })
                .or_else(|| self.get_constrained_fn(state, &callee.symbol, Some(&callee.module)));
            let Some(template) = template else {
                continue;
            };
            let Some(use_type) =
                Self::mono_call_type(state, mono_expr_types, resolutions, arg_spans, *inner_span)
            else {
                continue;
            };
            let Some(demand) = self.derive_mono_demand(
                state,
                CallableTarget::Binding(callee.clone()),
                &template.core.scheme,
                &use_type,
                *inner_span,
            ) else {
                continue;
            };
            successors.push(Box::new(Successor {
                fn_name: callee.symbol.clone(),
                demand,
                home: inner_home,
                template,
                site: SuccessorSite::Call(*inner_span),
            }));
        }
    }

    /// The dispatch hops (`monomorphisation.md` §3.10.1): each site whose
    /// `Dispatch` verdict names an AST-bodied template, every argument
    /// concrete in this instance's own expression types, is demanded at its
    /// use type. A call spelled as the enclosing method's own name is such a
    /// site like any other.
    fn dispatch_hop_successors(
        &self,
        state: &CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &MethodResolutions,
        successors: &mut Successors,
    ) {
        let mut sites = Vec::new();
        collect_apply_sites(defn.body(), &mut sites);
        for (arg_spans, site) in sites {
            let Some(ApplyRef::Dispatch(target)) = resolutions.apply_refs.get(&site).cloned()
            else {
                continue;
            };
            let admitted = arg_spans.iter().all(|span| {
                mono_expr_types
                    .get(span)
                    .is_some_and(|ty| apply(&state.subst, ty).is_concrete())
            });
            if !admitted {
                continue;
            }
            let Some(template) = self.dispatch_template(state, &target) else {
                continue;
            };
            let Some(use_type) =
                Self::mono_call_type(state, mono_expr_types, resolutions, &arg_spans, site)
            else {
                continue;
            };
            let Some(demand) = self.derive_mono_demand(
                state,
                CallableTarget::Binding(target.clone()),
                &template.core.scheme,
                &use_type,
                site,
            ) else {
                continue;
            };
            let home = (target.module != state.current_module).then(|| target.module.clone());
            successors.push(Box::new(Successor {
                fn_name: target.symbol.clone(),
                demand,
                home,
                template,
                site: SuccessorSite::Call(site),
            }));
        }
    }

    /// The template a `Dispatch` verdict names, when it is an AST-bodied
    /// template (an implementation-method template). The one predicate the
    /// cluster scan and the instance step share.
    pub(crate) fn dispatch_template(
        &self,
        state: &CheckState,
        target: &FQSymbol,
    ) -> Option<TemplateFn> {
        let template = self.get_constrained_fn(state, &target.symbol, Some(&target.module))?;
        matches!(template.core.body, TemplateBody::Ast(_)).then_some(template)
    }

    /// Every successor demand of a rechecked instance body, in step order:
    /// free-function hops, function values, dispatch hops
    /// (`monomorphisation.md` §3.10). Derived before any is minted; each mint
    /// restores the substitution, so the order of derivation is immaterial.
    /// Out of line so its locals are not live across the recursion.
    #[inline(never)]
    fn instance_successors(
        &self,
        state: &CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &MethodResolutions,
        home: Option<&ModuleFullPath>,
    ) -> Successors {
        let mut successors = Vec::new();
        self.parametric_hop_successors(
            state,
            defn,
            mono_expr_types,
            resolutions,
            home,
            &mut successors,
        );
        self.function_value_successors(state, defn, mono_expr_types, resolutions, &mut successors);
        self.dispatch_hop_successors(state, defn, mono_expr_types, resolutions, &mut successors);
        successors
    }

    /// Settle each successor and redirect its site to the instance.
    fn settle_successors(
        &self,
        state: &mut CheckState,
        harvest: &mut RecheckHarvest,
    ) -> Result<(), CranelispError> {
        for successor in std::mem::take(&mut harvest.successors) {
            let site = successor.site;
            if let Some(instance) = self.settle_successor(state, successor)? {
                record_successor(state, &mut harvest.resolutions, site, instance);
            }
        }
        Ok(())
    }

    /// Settle one successor demand (`monomorphisation.md` §3.10.1, §3.10.3):
    /// reuse an installed instance, redirect to one still being minted on the
    /// chain, or mint. Returns the instance key the site is redirected to.
    ///
    /// `state.subst` is isolated around the mint (FIXME 0373, preserves
    /// 0344): the inner recursion's call-result unification must not leak
    /// into the parent's substitution and re-collapse a fold accumulator.
    fn settle_successor(
        &self,
        state: &mut CheckState,
        successor: Box<Successor>,
    ) -> Result<Option<Symbol>, CranelispError> {
        let saved_subst = state.subst.clone();
        let settled = match self.prepare_successor(state, successor) {
            Ok(SuccessorStep::Redirect(key)) => Ok(Some(key)),
            Ok(SuccessorStep::Unsettled) => Ok(None),
            Ok(SuccessorStep::Mint(mint, link, home)) => self
                .recheck_mint(state, mint, link, home.as_ref(), None)
                .map(|mono| mono.map(|mono| mono.defn.name)),
            Err(error) => Err(error),
        };
        state.subst = saved_subst;
        settled
    }

    /// Everything a successor's settlement does before its recheck, out of
    /// line: the redirect checks, then the mint's preparation.
    #[inline(never)]
    fn prepare_successor(
        &self,
        state: &mut CheckState,
        successor: Box<Successor>,
    ) -> Result<SuccessorStep, CranelispError> {
        let Successor {
            fn_name,
            demand,
            home,
            template,
            ..
        } = *successor;
        let key = Self::demand_instance_key(&demand, &template.core.scheme)?;
        if self.instance_installed(state, &key) || state.mono_chain.iter().any(|l| l.key == key) {
            return Ok(SuccessorStep::Redirect(key));
        }
        Ok(
            match self.prepare_mint(state, &fn_name, &demand, home.as_ref(), Some(template))? {
                PreparedMint::Settled(instance) => SuccessorStep::Redirect(match instance {
                    Some(mono) => mono.defn.name,
                    None => return Ok(SuccessorStep::Unsettled),
                }),
                PreparedMint::Recheck(mint, link) => SuccessorStep::Mint(mint, link, home),
            },
        )
    }

    #[inline(never)]
    fn instance_installed(&self, state: &CheckState, key: &Symbol) -> bool {
        self.current_symbol_table(state)
            .view()
            .lookup(key)
            .and_then(cranelisp_types::Binding::callable)
            .is_some_and(|callable| matches!(callable.arm.life, Life::Concrete { .. }))
    }

    /// The chain element for a demand about to be minted.
    fn chain_link(
        &self,
        state: &CheckState,
        link: &InstanceLink,
        key: Symbol,
        origin: &CallableOrigin,
        signature: &Type,
        site: Span,
    ) -> Result<ChainLink, CranelispError> {
        let template = match &link.template {
            CallableTarget::Binding(owner) | CallableTarget::OverloadArm { owner, .. } => {
                owner.clone()
            }
            _ => FQSymbol {
                module: state.current_module.clone(),
                symbol: key.clone(),
            },
        };
        let implementation =
            match origin {
                CallableOrigin::TraitMethod {
                    shell,
                    trait_name,
                    impl_type,
                } => Some(ImplementationInstantiation {
                    shell: shell.clone(),
                    receiver: if self.is_higher_kinded_trait(trait_name) {
                        None
                    } else {
                        Some(self.implementing_type_at(
                            trait_name, impl_type, &template, signature, site,
                        )?)
                    },
                }),
                _ => None,
            };
        let counts = implementation.as_ref().is_some_and(|instantiation| {
            let mut at_instantiation = state
                .mono_chain
                .iter()
                .filter(|element| element.implementation.as_ref() == Some(instantiation))
                .peekable();
            at_instantiation.peek().is_none()
                || at_instantiation.any(|element| element.template == template)
        });
        Ok(ChainLink {
            key,
            template,
            signature: signature.clone(),
            implementation,
            counts,
        })
    }

    /// The type `self` takes in an instance of the conventional
    /// implementation method `template`, read by matching the trait member's
    /// declared scheme against the instance's concrete `signature` (§3.10.3).
    /// The member is the one whose mangled implementation entry is `template`.
    ///
    /// A template whose receiver cannot be read is an internal inconsistency
    /// between the implementation entry and its trait's declaration, refused at
    /// the demand's `site`; it is never recorded as a higher-kinded receiver.
    fn implementing_type_at(
        &self,
        trait_name: &cranelisp_types::FQTraitName,
        impl_type: &FQTypeName,
        template: &FQSymbol,
        signature: &Type,
        site: Span,
    ) -> Result<Type, CranelispError> {
        let unreadable = |cause: &str| CranelispError::CodegenError {
            message: format!(
                "internal inconsistency: the implementation instantiation of `{template}` \
                 (impl of {trait_name} for {impl_type}) cannot be read: {cause}; \
                 signature `{signature}`"
            ),
            location: ErrorLocation::from_span(site),
        };
        let Some(cranelisp_types::Decl::Trait(trait_record)) = self
            .probe_module_entry_owned(&trait_name.module, trait_name.name.as_ref())
            .map(|binding| binding.declaration)
        else {
            return Err(unreadable("the trait declaration is not in its home table"));
        };
        let member = trait_record
            .info
            .methods
            .iter()
            .find(|method| {
                crate::traits::mangle_trait_method(
                    trait_name.name.as_ref(),
                    method.name.as_ref(),
                    impl_type,
                ) == template.symbol.as_ref()
            })
            .ok_or_else(|| unreadable("no trait member names this implementation entry"))?;
        let key = cranelisp_types::member_key(trait_name.name.as_ref(), member.name.as_ref());
        let Some(cranelisp_types::Decl::TraitMethod(record)) = self
            .probe_module_entry_owned(&trait_name.module, key.as_ref())
            .map(|binding| binding.declaration)
        else {
            return Err(unreadable(&format!(
                "the member declaration `{key}` is not in the trait's home table"
            )));
        };
        let self_var = record
            .scheme
            .constraints
            .iter()
            .find_map(|(var, traits)| traits.contains(trait_name).then_some(*var))
            .ok_or_else(|| unreadable(&format!("`{key}` constrains no variable by the trait")))?;
        binding_of(self_var, &record.scheme.ty, signature).ok_or_else(|| {
            unreadable(&format!(
                "`{key}`'s self variable is not bound by the signature against `{}`",
                record.scheme.ty
            ))
        })
    }

    fn is_higher_kinded_trait(&self, trait_name: &cranelisp_types::FQTraitName) -> bool {
        self.probe_module_entry_owned(&trait_name.module, trait_name.name.as_ref())
            .is_some_and(|binding| {
                matches!(&binding.declaration, cranelisp_types::Decl::Trait(record)
                    if !record.info.type_params.is_empty())
            })
    }

    /// Bare function references used as values in a rechecked mono body. Apply callees keep their existing dispatch path.
    fn function_value_successors(
        &self,
        state: &CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &MethodResolutions,
        successors: &mut Successors,
    ) {
        let mut sites = Vec::new();
        collect_non_callee_var_values(defn.body(), &mut sites);

        for span in sites {
            let Some(VarRef::Global(callee)) = resolutions.var_refs.get(&span) else {
                continue;
            };
            let Some(Type::Fn(params, ret)) = mono_expr_types.get(&span) else {
                continue;
            };
            if !params.iter().all(Type::is_concrete) || !ret.is_concrete() {
                continue;
            }
            let callee = callee.clone();
            let window_core = state
                .mono_window
                .as_ref()
                .and_then(|window| window.template(&callee).cloned());
            let template = match window_core {
                Some(core) => Some(TemplateFn {
                    core,
                    template_target: Some(CallableTarget::Binding(callee.clone())),
                }),
                None => self
                    .probe_module_entry_owned(&callee.module, callee.symbol.as_ref())
                    .filter(Self::entry_is_monomorphisable_polymorphic)
                    .and_then(|_| {
                        self.get_constrained_fn(state, &callee.symbol, Some(&callee.module))
                    }),
            };
            let Some(template) = template else {
                continue;
            };
            let use_type = Type::Fn(params.clone(), ret.clone());
            let Some(demand) = self.derive_mono_demand(
                state,
                CallableTarget::Binding(callee.clone()),
                &template.core.scheme,
                &use_type,
                span,
            ) else {
                continue;
            };
            let home = (callee.module != state.current_module).then(|| callee.module.clone());
            successors.push(Box::new(Successor {
                fn_name: callee.symbol.clone(),
                demand,
                home,
                template,
                site: SuccessorSite::Value(span),
            }));
        }
    }

    /// Look up a constrained function by name.
    pub(crate) fn get_constrained_fn(
        &self,
        state: &CheckState,
        name: &Symbol,
        home: Option<&ModuleFullPath>,
    ) -> Option<TemplateFn> {
        // For an IMPORTED callee (FIXME 0355), the constrained `Def` lives in its
        // DEFINING module — chain-follow to the terminal entry there. The home is
        // a committed import → live view suffices. For a local callee, read the
        // current module directly. Staging-aware (FIXME 0179): the local probe
        // reads through staging so in-cluster constrained-fn registrations are
        // visible.
        let lookup_module = home.unwrap_or(&state.current_module);
        // `name` is already a terminal storage key. It can legitimately
        // contain `/` inside a generated trait-method mangle
        // (`Functor.fmap$primitives/Option`), so do not feed it back through
        // source-name qualification parsing here.
        let entry = self.probe_module_entry_owned(lookup_module, name.as_ref())?;
        let callable = entry.callable()?;
        let Life::Template { body, .. } = &callable.arm.life else {
            return None;
        };
        Some(TemplateFn {
            core: TemplateCore {
                body: body.clone(),
                scheme: callable.arm.scheme.clone(),
                origin: callable.origin.clone(),
            },
            template_target: Some(CallableTarget::Binding(FQSymbol {
                module: lookup_module.clone(),
                symbol: name.clone(),
            })),
        })
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Collect every `Apply`-of-bare-`Var` call site in an expression tree, except
/// calls a fn makes to ITSELF (generic self-recursion is not a concrete mono
/// site — its arg types are the defn's own generic vars). Records
/// `(callee_name, arg_spans, call_span)`. Used by
/// `parametric_hop_successors` (FIXME 0373) to find inner hops to
/// recursively monomorphise after a parent hop's body re-check.
pub(super) fn collect_apply_var_calls(
    expr: &Expr,
    self_name: &Symbol,
    var_refs: &HashMap<Span, VarRef>,
    out: &mut Vec<(Symbol, Vec<Span>, Span)>,
) {
    if let Expr::Apply { callee, args, span, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
        && name != self_name
        // FIXME 0653 — skip a §4.6 LOCAL shadow of a top-level parametric fn: a
        // callee whose verdict is `VarRef::Local` resolved to a local.
        && crate::program::callee_has_keyed_carrier(var_refs, callee.span())
    {
        let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
        out.push((name.clone(), arg_spans, *span));
    }
    crate::program::for_each_child_expr(expr, |child| {
        collect_apply_var_calls(child, self_name, var_refs, out)
    });
}

/// Record that the call at `span` dispatches to the concrete `instance`
/// installed in `module`: the one redirect writer of the cluster scan and of
/// every successor step inside an instance (`monomorphisation.md` §3.10.1).
/// A partial application keeps its auto-curry shape with the instance as its
/// target.
pub(crate) fn record_instance_dispatch(
    resolutions: &mut MethodResolutions,
    module: &ModuleFullPath,
    span: Span,
    instance: &Symbol,
) {
    if span == Span::SYNTHETIC {
        return;
    }
    let target = FQSymbol {
        module: module.clone(),
        symbol: instance.clone(),
    };
    let resolution = match resolutions.resolved_calls.get(&span) {
        Some(ResolvedCall::AutoCurry {
            applied_count,
            total_count,
            trait_resolution,
            ..
        }) => ResolvedCall::AutoCurry {
            target_name: instance.clone(),
            applied_count: *applied_count,
            total_count: *total_count,
            trait_resolution: trait_resolution.clone(),
        },
        _ => ResolvedCall::SigDispatch {
            target: CallableTarget::Binding(target.clone()),
        },
    };
    resolutions.resolved_calls.insert(span, resolution);
    resolutions
        .apply_refs
        .insert(span, ApplyRef::Dispatch(target));
}

/// Redirect a successor's site to its instance, installed in the caller's
/// current module (`register_mono_entry`).
#[inline(never)]
fn record_successor(
    state: &CheckState,
    resolutions: &mut MethodResolutions,
    site: SuccessorSite,
    instance: Symbol,
) {
    let module = &state.current_module;
    match site {
        SuccessorSite::Call(span) => record_instance_dispatch(resolutions, module, span, &instance),
        SuccessorSite::Value(span) => {
            resolutions.var_refs.insert(
                span,
                VarRef::Global(FQSymbol {
                    module: module.clone(),
                    symbol: instance,
                }),
            );
        }
    }
}

/// Collect every `Apply` site with its argument spans.
fn collect_apply_sites(expr: &Expr, out: &mut Vec<(Vec<Span>, Span)>) {
    if let Expr::Apply { args, span, .. } = expr {
        out.push((args.iter().map(Expr::span).collect(), *span));
    }
    crate::program::for_each_child_expr(expr, |child| collect_apply_sites(child, out));
}

/// The concrete type at `var`'s first occurrence in `declared`, read from
/// the structurally matching position of `concrete`.
fn binding_of(var: cranelisp_types::TypeId, declared: &Type, concrete: &Type) -> Option<Type> {
    match (declared, concrete) {
        (Type::Var(id), _) if *id == var => Some(concrete.clone()),
        (Type::Fn(declared_params, declared_ret), Type::Fn(params, ret))
            if declared_params.len() == params.len() =>
        {
            declared_params
                .iter()
                .zip(params)
                .chain(std::iter::once((declared_ret.as_ref(), ret.as_ref())))
                .find_map(|(declared, concrete)| binding_of(var, declared, concrete))
        }
        (Type::ADT(_, declared_args) | Type::TyConApp(_, declared_args), Type::ADT(_, args))
            if declared_args.len() == args.len() =>
        {
            declared_args
                .iter()
                .zip(args)
                .find_map(|(declared, concrete)| binding_of(var, declared, concrete))
        }
        _ => None,
    }
}

/// The chain's depth: its elements that count (§3.10.3).
fn chain_depth(chain: &[ChainLink]) -> usize {
    chain.iter().filter(|link| link.counts).count()
}

/// The one depth diagnostic (`monomorphisation.md` §3.10.3): located at the
/// successor's site, with the definition identity of the template whose
/// instance body holds it.
fn depth_refusal(
    chain: &[ChainLink],
    refused: &ChainLink,
    origin: &CallableOrigin,
    site: Span,
) -> CranelispError {
    let render = |ty: &Type| {
        cranelisp_types::render_type(
            ty,
            cranelisp_types::PrimitiveNaming::Qualified,
            cranelisp_types::VarNaming::Numbered,
        )
    };
    let named = match origin {
        CallableOrigin::TraitMethod {
            trait_name,
            impl_type,
            ..
        } => {
            let member = refused
                .template
                .symbol
                .as_ref()
                .split_once('.')
                .and_then(|(_, rest)| rest.split_once('$'))
                .map_or(refused.template.symbol.as_ref(), |(member, _)| member);
            format!("`{member}` of the implementation of `{trait_name}` for `{impl_type}`")
        }
        _ => format!("`{}`", refused.template),
    };
    let first = chain
        .iter()
        .find(|link| link.template == refused.template)
        .or_else(|| chain.first())
        .map_or_else(
            || render(&refused.signature),
            |link| render(&link.signature),
        );
    let mut location = ErrorLocation::from_span(site);
    location.fq = chain.last().map(|holder| holder.template.clone());
    CranelispError::TypeError {
        message: format!(
            "the instantiation of {named} exceeds the instantiation depth limit of \
             {INSTANTIATION_DEPTH_LIMIT}: first instantiated at `{first}`, refused at `{}`",
            render(&refused.signature)
        ),
        location,
    }
}

/// Collect bare `Var` references in value positions. An `Apply` callee is a
/// dispatch position and remains owned by `collect_apply_var_calls`.
fn collect_non_callee_var_values(expr: &Expr, out: &mut Vec<Span>) {
    match expr {
        Expr::Var { span, .. } => out.push(*span),
        Expr::Apply { callee, args, .. } => {
            if !matches!(callee.as_ref(), Expr::Var { .. }) {
                collect_non_callee_var_values(callee, out);
            }
            for arg in args {
                collect_non_callee_var_values(arg, out);
            }
        }
        _ => crate::program::for_each_child_expr(expr, |child| {
            collect_non_callee_var_values(child, out)
        }),
    }
}

/// Collect every `Apply`-of-bare-`Var` call to `self_name` (the OPPOSITE of
/// [`collect_apply_var_calls`], which excludes self-calls). Used by
/// `monomorphise_call` (FIXME 0374) to redirect a polymorphic fn's monomorphic
/// self-recursion to its own mono instance — the original `Polymorphic` def is
/// slot-less, so a by-name self-call would lower through a missing slot.
pub(super) fn collect_self_apply_calls(
    expr: &Expr,
    self_name: &Symbol,
    out: &mut Vec<(Span, Vec<Span>, Span)>,
) {
    if let Expr::Apply {
        callee, args, span, ..
    } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
        && name == self_name
    {
        let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
        // Carry the CALLEE `Var` span too: the self-call classifier
        // (`record_self_recursion_dispatch`) needs it to consult the frame-guarded
        // `is_recursion_self_ref` verdict `record_reference_target` recorded for
        // this callee during the recheck (a let-shadowed base has NO carrier).
        out.push((callee.span(), arg_spans, *span));
    }
    crate::program::for_each_child_expr(expr, |child| {
        collect_self_apply_calls(child, self_name, out)
    });
}

/// The canonical identity of a settled type's nominal head: the key an impl
/// for it is registered under (`design/typecheck/typecheck.md` §9.1.1).
///
/// An ADT gives its own `FQTypeName` with its arguments dropped (the
/// registration grain). A built-in scalar gives its identity in the synthetic
/// `primitives` module, where bootstrap installs it (spec §8.9.1). Any other
/// head has no identity; each caller classifies those heads itself.
pub(crate) fn receiver_identity(ty: &Type) -> Option<FQTypeName> {
    let scalar = |name: &str| {
        Some(FQTypeName::new(
            ModuleFullPath::from("primitives"),
            TypeName::from(name),
        ))
    };
    match ty {
        Type::Int => scalar("Int"),
        Type::Float => scalar("Float"),
        Type::Bool => scalar("Bool"),
        Type::String => scalar("String"),
        Type::ADT(fqtn, _) => Some(fqtn.clone()),
        Type::Var(_) | Type::Fn(..) | Type::TyConApp(..) => None,
    }
}

/// The bare name of [`receiver_identity`], for the primitive short-circuit and
/// diagnostics. Never an impl-existence key.
pub(crate) fn concrete_type_name(ty: &Type) -> Option<TypeName> {
    receiver_identity(ty).map(|identity| identity.name)
}

#[cfg(test)]
mod successor_tests;
#[cfg(test)]
mod tests;

fn ordered_generic_vars(scheme: &Scheme) -> Vec<cranelisp_types::TypeId> {
    let mut ids = Vec::new();
    cranelisp_types::collect_var_ids_ordered(&scheme.ty, &mut ids);
    ids.retain(|id| scheme.type_vars.contains(id));
    ids
}
