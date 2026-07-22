use std::collections::HashMap;

use cranelisp_types::{
    CranelispError, ErrorLocation, FQTraitName, Scheme, Span, Symbol, TraitDecl, TraitMethodKind,
    TraitMethodSig, TraitName, Type, TypeId, Visibility,
};

use super::*;
use crate::checker::{CheckState, TypeCheckEnv};

// ---------------------------------------------------------------------------
// Active Constraints (tracked during body checking)
// ---------------------------------------------------------------------------

/// Tracks trait constraints on type variables during inference.
/// Populated when a constrained scheme is instantiated, consulted during generalize.
#[derive(Debug, Clone, Default)]
pub struct ActiveConstraints {
    /// TypeId -> list of required fully-qualified trait names
    pub(crate) constraints: HashMap<TypeId, Vec<FQTraitName>>,
}

impl ActiveConstraints {
    /// Add a constraint on a type variable (idempotent — duplicates are ignored).
    pub fn add(&mut self, var_id: TypeId, trait_name: FQTraitName) {
        let traits = self.constraints.entry(var_id).or_default();
        if !traits.contains(&trait_name) {
            traits.push(trait_name);
        }
    }

    /// Get constraints for a type variable.
    #[allow(dead_code)]
    pub fn get(&self, var_id: TypeId) -> Option<&Vec<FQTraitName>> {
        self.constraints.get(&var_id)
    }

    /// Clear all active constraints (between top-level forms).
    #[allow(dead_code)]
    pub fn clear(&mut self) {
        self.constraints.clear();
    }

    /// Iterate over all (var_id, traits) pairs.
    pub fn all(&self) -> impl Iterator<Item = (&TypeId, &Vec<FQTraitName>)> {
        self.constraints.iter()
    }

    /// Collect constraints for a set of type variable IDs.
    /// Returns a constraints map suitable for Scheme.constraints.
    /// Note: does NOT follow the substitution — use `TypeChecker::generalize`
    /// for correct constraint propagation through unified vars.
    #[allow(dead_code)]
    pub fn collect_for_vars(&self, vars: &[TypeId]) -> HashMap<TypeId, Vec<FQTraitName>> {
        let mut result = HashMap::new();
        for &var_id in vars {
            if let Some(traits) = self.constraints.get(&var_id)
                && !traits.is_empty()
            {
                result.insert(var_id, traits.clone());
            }
        }
        result
    }
}

// ---------------------------------------------------------------------------
// Trait Registration
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Register a trait declaration.
    ///
    /// - Stores the TraitDecl in the trait registry
    /// - Registers each method as a constrained polymorphic symbol
    /// - Registers the trait name in the symbol table as TraitDecl
    pub(crate) fn register_trait_decl(
        &self,
        state: &mut CheckState,
        decl: &TraitDecl,
    ) -> Result<(), CranelispError> {
        // Same-module idempotency probe (S108 Wave-G convergence §3.3/§4.2).
        // This is the ONE legitimate fallback-less probe — a RAW current-module
        // table probe (`probe_module_entry_owned`: no chain-follow, no prelude
        // hop) that answers same-module IDENTITY, **not** name-freedom. The
        // name-freedom question (is this trait name already in scope via an
        // import/export or the prelude?) is the §8.6.4 seam, which ran FIRST at
        // the `check_form_register` `TraitDecl` arm; by the time control reaches
        // here the trait name is either free or the module's OWN prior decl.
        //
        // The cluster orchestration retries a module's typecheck FROM THE TOP
        // with no saved resume index when a declared submodule must be loaded
        // (`src/process_form.rs` `process_cluster_once` — "each pass re-derives
        // from `sexps`"). On the retry pass the parent's structural decls are
        // re-submitted while the prior pass's results are already committed to
        // live, so `register_trait_decl` is re-invoked for an already-registered
        // trait. A re-submission of the SAME declaration is a no-op (idempotent,
        // mirroring `deftype`; retry-from-top contract, S86 D3); a genuinely-
        // DIFFERENT same-module redeclaration of the name is rejected (spec
        // 07-traits §7.1 duplicate-trait rule, preserved for real conflicts).
        if let Some(cranelisp_types::ModuleEntry::TraitDecl { info: existing, .. }) =
            self.probe_module_entry_owned(&state.current_module, decl.name.as_ref())
        {
            if trait_decl_matches(&existing, decl) {
                // Idempotent retry-from-top re-submission — already registered
                // identically. Nothing to do.
                return Ok(());
            }
            return Err(CranelispError::TypeError {
                message: format!("trait {} already defined", decl.name),
                location: ErrorLocation::from_span(decl.span),
            });
        }

        let methods = self.classify_trait_methods(state, decl)?;

        // Kind is derived ONCE, HERE at declaration registration, from the head
        // shape (spec §7.1/§7.2.1; `design/typecheck/hkt.md` §5.1). A
        // parenthesized head (non-empty `type_params`) is higher-kinded IFF its
        // con_var is APPLIED `(a …)` somewhere in the method signatures; a
        // parenthesized head whose con_var is NEVER applied is MALFORMED and
        // rejected HERE, at `deftrait` (not at impl time — the old §5.4
        // "reject the bare-con_var impl-on-primitive at impl time" framing is
        // superseded). Every downstream consumer then reads `type_params` alone
        // — non-empty ⟺ HKT — never re-scanning method-body usage (Principle 24
        // "Resolve once"; the former usage-derived kind derivation here and the
        // one at `impl_check.rs` collapse onto this single declaration fact).
        if !decl.type_params.is_empty() {
            if let Some(method) = methods
                .iter()
                .find(|method| method_default_body(method).is_some())
            {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "higher-kinded trait `{}` method `{}` cannot have a default body",
                        decl.name, method.name
                    ),
                    location: ErrorLocation::from_span(method.span),
                });
            }
            let con_applied = methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|(_, p)| type_expr_uses_con_var(p, &decl.type_params))
                    || method_result_constraint(m)
                        .is_some_and(|ret| type_expr_uses_con_var(ret, &decl.type_params))
            });
            if !con_applied {
                // §7.2.1 malformed: a head type variable that is never applied is
                // not the higher-kinded form, and there is no kind-`*` trait with
                // a head type variable — conventional traits use the bare head and
                // `self`. Naming the fix (spec §7.1 example).
                let con = &decl.type_params[0];
                let example_method = decl.methods.first().map(|m| m.name.as_ref()).unwrap_or("m");
                return Err(CranelispError::TypeError {
                    message: format!(
                        "trait `{}`'s type parameter `{con}` is never applied \
                         `({con} …)`; a trait that returns the implementing type \
                         uses the bare head and `self`: \
                         `(deftrait {} ({example_method} [] self))`.",
                        decl.name, decl.name,
                    ),
                    location: ErrorLocation::from_span(decl.span),
                });
            }
            // Genuinely higher-kinded (con_var applied) — the declaration-derived
            // kind. `register_hkt_trait` only ever sees an applied-con_var decl.
            return self.register_hkt_trait(state, decl, methods);
        }

        // §7.1.1 OCCURRENCE RULE (S115 W4, FIXME 0709; `design/typecheck/traits.md`
        // §2 "Occurrence-rule enforcement"). CONVENTIONAL (bare-head, kind-`*`)
        // traits only — the HKT branch above already returned, so §7.2 methods are
        // exempt by construction, not by a flag. Every method signature MUST
        // mention the implementing type at least once, in parameter or return
        // position; a method that mentions it NOWHERE has nothing to dispatch on.
        //
        // Declaration-time, per method, BEFORE the trait entry is written
        // (Principle 18 — the invariant is enforced at the seam where the
        // malformed form is representable). This subsumes the downstream
        // check-gate leak: `(deftrait Zeroable (zed [] Int))` no longer registers,
        // so `(zed)` can never reach codegen as an `undefined function`.
        //
        // The occurrence forms are exactly the three §7.1.1 spellings, and they
        // are ONE syntactic signal: the frontend lowers a BARE param to
        // `TypeExpr::SelfType` (`ast_builder::build_method_sig`), a `:self`
        // annotation to `TypeExpr::SelfType` (`parse_annotation_name`), and a
        // `self` return to `TypeExpr::SelfType` (`build_type_expr`) — so the
        // predicate is a single `SelfType` search over the signature's type
        // expressions, the same signal `build_method_type` substitutes.
        //
        // BOUNDARY (the over-reach guard): reject on the CONJUNCTION
        // no-param-occurrence ∧ no-self-return, never on "concrete return" alone
        // and never on "nullary" alone. `(size [x] Int)` has an occurrence via its
        // bare param and is ACCEPTED; `(zed [] self)` has one via its return and is
        // ACCEPTED; `(cvt [:String s] Int)` has neither and is REJECTED.
        //
        // **SCOPE — by OCCURRENCE, not by parameter count (S115 W8; user ruling
        // 2026-07-21, scribed at §7.1.1 "The occurrence rule is broad, not a
        // nullary corner").** W4 shipped the narrow nullary-only guard pending
        // that ruling (FIXME 0770); the ruling widened it, and this is the
        // widening. A non-empty parameter list does NOT rescue a signature whose
        // every parameter is annotated with a type other than the implementing
        // type: `(deftrait Conv (cvt [:String s] Int))` is rejected on exactly
        // the same ground as `(deftrait Zeroable (zed [] Int))`. Cranelisp has no
        // explicit-qualification call syntax (no `<Foo as Trait>::method`), so
        // such a method is undispatchable BY CONSTRUCTION — no argument position
        // selects the impl, and the §3.3.3 return-ascription escape hatch needs a
        // `self` return this signature does not have. Accepting it merely defers
        // the fault to a misleading call-site `no impl of trait T for type X`
        // (0805) when the impl exists and nothing could ever dispatch.
        //
        // METHOD-LEVEL TYPE VARIABLES ARE UNAFFECTED: the rule bites only on the
        // ABSENCE of the implementing type. `(map-val [:(Fn [a] b) f x] self)` is
        // well-formed — `x` is bare and the return is `self`.
        for method in &methods {
            if !method_mentions_self(method) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "trait `{}` method `{}`: no occurrence of the implementing \
                         type to dispatch on — a trait method MUST mention the \
                         implementing type at least once: either a parameter \
                         carries it (a bare name `[x …]` or a `:self` annotation), \
                         or the return type is `self`",
                        decl.name, method.name,
                    ),
                    location: ErrorLocation::from_span(method.span),
                });
            }
        }

        // Allocate a fresh type variable for the trait's type parameter
        let (_, type_var_id) = self.fresh_var_id();

        // Register each method with a constrained polymorphic scheme. The
        // method binding inherits the trait's visibility (a Private trait's
        // methods are Private Defs) so a private trait does not leak its
        // operators as bare names through the prelude fallback
        // (`/review` I-1); within the trait's own subtree they stay reachable
        // (the `cranelisp_types::resolve` visibility check honours `in_subtree`).
        let method_entries = methods
            .iter()
            .map(|method| {
                self.build_trait_method_entry(
                    state,
                    &decl.name,
                    method,
                    type_var_id,
                    &decl.type_params,
                    decl.visibility,
                    decl.span,
                )
                .map(|entry| (method.name.clone(), entry))
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (name, entry) in method_entries {
            self.current_symbol_table_mut(state).insert(name, entry);
        }

        // Register in symbol table as TraitDecl entry
        self.current_symbol_table_mut(state).insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                info: cranelisp_types::TraitDeclInfo {
                    name: decl.name.clone(),
                    type_params: decl.type_params.clone(),
                    methods,
                },
                visibility: decl.visibility,
                docstring: decl.docstring.clone(),
            },
        );

        Ok(())
    }

    /// Register an HKT trait where type_params are type constructor variables.
    /// E.g., `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))`
    fn register_hkt_trait(
        &self,
        state: &mut CheckState,
        decl: &TraitDecl,
        methods: Vec<TraitMethodSig>,
    ) -> Result<(), CranelispError> {
        // Create fresh type var IDs for each constructor param
        let mut con_var_map: HashMap<Symbol, TypeId> = HashMap::new();
        for param_name in &decl.type_params {
            let (_, id) = self.fresh_var_id();
            con_var_map.insert(param_name.clone(), id);
        }
        let module = state.current_module.clone();

        // Build a modified decl with hkt_param_index set on each method
        let mut methods = methods;

        let mut method_entries = Vec::with_capacity(methods.len());
        for mi in 0..methods.len() {
            let method = methods[mi].clone();
            // Determine which param index carries the type constructor
            // find_hkt_param_index now expects &[(Symbol, TypeExpr)] per spec
            // — pass `method.params` directly.
            let param_idx = find_hkt_param_index(&method.params, &decl.type_params);
            methods[mi].hkt_param_index = Some(param_idx);

            // Create fresh regular type vars for any type variables in the signature
            // that are NOT constructor params
            let mut type_var_map: HashMap<Symbol, TypeId> = HashMap::new();

            let param_tys: Vec<Type> = method
                .params
                .iter()
                .map(|(_, p)| {
                    self.resolve_hkt_sig_type_expr(
                        p,
                        &mut type_var_map,
                        &module,
                        &con_var_map,
                        decl.span,
                    )
                    .map_err(cranelisp_types::CranelispError::from)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty = self
                .resolve_hkt_sig_type_expr(
                    method_result_constraint(&method).expect("HKT methods are required"),
                    &mut type_var_map,
                    &module,
                    &con_var_map,
                    decl.span,
                )
                .map_err(cranelisp_types::CranelispError::from)?;

            // Collect all var IDs (constructor + regular)
            let mut all_vars: Vec<TypeId> = con_var_map.values().copied().collect();
            all_vars.extend(type_var_map.values());
            all_vars.sort();
            all_vars.dedup();

            // Add trait constraint to constructor vars
            let fq_trait_name = FQTraitName::new(state.current_module.clone(), decl.name.clone());
            let mut constraints: HashMap<TypeId, Vec<FQTraitName>> = HashMap::new();
            for &con_id in con_var_map.values() {
                constraints.insert(con_id, vec![fq_trait_name.clone()]);
            }

            let method_scheme = Scheme {
                type_vars: all_vars,
                constraints,
                ty: Type::Fn(param_tys, Box::new(ret_ty)),
            };

            // Register the method name as a symbol with trait_origin. The method
            // inherits the trait's visibility (I-1 — see `register_trait_decl`).
            let mut builder = cranelisp_types::ModuleEntry::def(
                method_scheme,
                cranelisp_types::DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::NotDetermined,
                },
            )
            .visibility(decl.visibility)
            .param_names(method.params.iter().map(|(n, _)| n.clone()).collect())
            .trait_origin(fq_trait_name.clone());
            if let Some(doc) = method.docstring.clone() {
                builder = builder.docstring(doc);
            }
            method_entries.push((method.name.clone(), builder.build()));

            // trait_origin is already set on the ModuleEntry::Def above,
            // so no separate reverse lookup registration is needed.
        }

        for (name, entry) in method_entries {
            self.current_symbol_table_mut(state).insert(name, entry);
        }

        // Register in symbol table as TraitDecl entry (with hkt_param_index)
        self.current_symbol_table_mut(state).insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                info: cranelisp_types::TraitDeclInfo {
                    name: decl.name.clone(),
                    type_params: decl.type_params.clone(),
                    methods,
                },
                visibility: decl.visibility,
                docstring: decl.docstring.clone(),
            },
        );

        Ok(())
    }

    /// Register a single trait method with its constrained polymorphic scheme.
    #[allow(clippy::too_many_arguments)]
    fn build_trait_method_entry(
        &self,
        state: &mut CheckState,
        trait_name: &TraitName,
        method: &TraitMethodSig,
        type_var_id: TypeId,
        trait_type_params: &[Symbol],
        visibility: Visibility,
        span: Span,
    ) -> Result<cranelisp_types::ModuleEntry<C>, CranelispError> {
        let method_type =
            self.build_method_type(state, method, type_var_id, trait_type_params, span)?;

        // Build FQTraitName using the current module (where the trait is being defined)
        let fq_trait_name = FQTraitName::new(state.current_module.clone(), trait_name.clone());

        let mut constraints = HashMap::new();
        constraints.insert(type_var_id, vec![fq_trait_name.clone()]);

        let method_scheme = Scheme {
            type_vars: vec![type_var_id],
            constraints,
            ty: method_type,
        };

        // Register the method name as a symbol with trait_origin. The method
        // inherits the trait's visibility (I-1 — see `register_trait_decl`).
        let mut builder = cranelisp_types::ModuleEntry::def(
            method_scheme,
            cranelisp_types::DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::NotDetermined,
            },
        )
        .visibility(visibility)
        .param_names(
            method
                .params
                .iter()
                .map(|(n, _)| n.clone())
                .collect::<Vec<_>>(),
        )
        .trait_origin(fq_trait_name);
        if let Some(doc) = method.docstring.clone() {
            builder = builder.docstring(doc);
        }
        Ok(builder.build())
    }

    /// Build the function type for a trait method.
    ///
    /// Resolves `Self` type expressions to the type variable.
    /// TypeVars matching the trait's type parameters map to self_type;
    /// other TypeVars get fresh type variables (I3 fix).
    fn build_method_type(
        &self,
        state: &CheckState,
        method: &TraitMethodSig,
        type_var_id: TypeId,
        trait_type_params: &[Symbol],
        span: Span,
    ) -> Result<Type, CranelispError> {
        // FIXME 0590: route through the ONE resolver via the trait-sig wrapper.
        // `Self` and every trait type-parameter name (`trait_type_params`)
        // substitute `self_type` (here a var `Type::Var(type_var_id)`). Free
        // lowercase names mint into `var_map` for co-reference. A qualified type
        // ref (`:primitives/Int`) resolves canonically against the named module
        // through the shared `scope_resolve_in` seam (FIXME 0436 / spec §8.5).
        let self_type = Type::Var(type_var_id);
        let module = state.current_module.clone();
        let mut var_map: HashMap<Symbol, TypeId> = HashMap::new();

        let param_types: Vec<Type> = method
            .params
            .iter()
            .map(|(_, p)| {
                self.resolve_trait_sig_type_expr(
                    p,
                    &mut var_map,
                    &module,
                    &self_type,
                    trait_type_params,
                    span,
                )
                .map_err(cranelisp_types::CranelispError::from)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let ret_type = if let Some(result_constraint) = method_result_constraint(method) {
            self.resolve_trait_sig_type_expr(
                result_constraint,
                &mut var_map,
                &module,
                &self_type,
                trait_type_params,
                span,
            )
            .map_err(cranelisp_types::CranelispError::from)?
        } else {
            self.fresh_var()
        };

        Ok(Type::Fn(param_types, Box::new(ret_type)))
    }

    fn classify_trait_methods(
        &self,
        state: &CheckState,
        decl: &TraitDecl,
    ) -> Result<Vec<TraitMethodSig>, CranelispError> {
        decl.methods
            .iter()
            .map(|method| {
                let kind = match &method.tail {
                    cranelisp_types::Sexp::Annotated {
                        annotation,
                        subject,
                        ..
                    } => TraitMethodKind::Default {
                        body: cranelisp_frontend::build_expr(subject)?,
                        result_constraint: Some(cranelisp_frontend::parse_type_expr(
                            &annotation.format_flat(),
                        )?),
                    },
                    tail => {
                        let parsed = cranelisp_frontend::parse_type_expr(&tail.format_flat()).ok();
                        if let Some(ret_type) = parsed.filter(|ty| {
                            self.probe_trait_sig_type_expr(
                                &method.params,
                                ty,
                                &state.current_module,
                                &decl.type_params,
                                method.span,
                            )
                        }) {
                            TraitMethodKind::Required { ret_type }
                        } else {
                            TraitMethodKind::Default {
                                body: cranelisp_frontend::build_expr(tail)?,
                                result_constraint: None,
                            }
                        }
                    }
                };
                Ok(TraitMethodSig {
                    name: method.name.clone(),
                    docstring: method.docstring.clone(),
                    params: method.params.clone(),
                    kind,
                    span: method.span,
                    hkt_param_index: method.hkt_param_index,
                })
            })
            .collect()
    }

}

#[cfg(test)]
mod tests;
