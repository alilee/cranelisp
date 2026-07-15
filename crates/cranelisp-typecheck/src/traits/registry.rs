use std::collections::HashMap;

use cranelisp_types::{ErrorLocation, CranelispError, FQTraitName, Scheme,
    Span, Symbol, TraitDecl, TraitMethodSig, TraitName, Type, TypeId, Visibility,
};

use crate::checker::{CheckState, TypeCheckEnv};
use super::*;

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
    pub fn collect_for_vars(
        &self,
        vars: &[TypeId],
    ) -> HashMap<TypeId, Vec<FQTraitName>> {
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

        // If trait has type_params used in Applied position, use HKT registration path
        if !decl.type_params.is_empty()
            && decl.methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|(_, p)| type_expr_uses_con_var(p, &decl.type_params))
                    || type_expr_uses_con_var(&m.ret_type, &decl.type_params)
            })
        {
            return self.register_hkt_trait(state, decl);
        }

        // Allocate a fresh type variable for the trait's type parameter
        let (_, type_var_id) = self.fresh_var_id();

        // Register each method with a constrained polymorphic scheme. The
        // method binding inherits the trait's visibility (a Private trait's
        // methods are Private Defs) so a private trait does not leak its
        // operators as bare names through the prelude fallback
        // (`/review` I-1); within the trait's own subtree they stay reachable
        // (the `cranelisp_types::resolve` visibility check honours `in_subtree`).
        for method in &decl.methods {
            self.register_trait_method(state,
                &decl.name,
                method,
                type_var_id,
                &decl.type_params,
                decl.visibility,
                decl.span,
            )?;
        }

        // Register in symbol table as TraitDecl entry
        self.current_symbol_table_mut(state).insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                info: cranelisp_types::TraitDeclInfo {
                    name: decl.name.clone(),
                    type_params: decl.type_params.clone(),
                    methods: decl.methods.clone(),
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
    ) -> Result<(), CranelispError> {
        let mut local_next_id = self.next_id_snapshot();
        // Create fresh type var IDs for each constructor param
        let mut con_var_map: HashMap<Symbol, TypeId> = HashMap::new();
        for param_name in &decl.type_params {
            let (_, id) = self.fresh_var_id();
            con_var_map.insert(param_name.clone(), id);
        }

        // Build a modified decl with hkt_param_index set on each method
        let mut modified_decl = decl.clone();

        for (mi, method) in decl.methods.iter().enumerate() {
            // Determine which param index carries the type constructor
            // find_hkt_param_index now expects &[(Symbol, TypeExpr)] per spec
            // — pass `method.params` directly.
            let param_idx = find_hkt_param_index(&method.params, &decl.type_params);
            modified_decl.methods[mi].hkt_param_index = Some(param_idx);

            // Create fresh regular type vars for any type variables in the signature
            // that are NOT constructor params
            let mut type_var_map: HashMap<Symbol, TypeId> = HashMap::new();

            let param_tys: Vec<Type> = method
                .params
                .iter()
                .map(|(_, p)| resolve_type_expr_hkt(p, &con_var_map, &mut type_var_map, &mut local_next_id, decl.span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty =
                resolve_type_expr_hkt(&method.ret_type, &con_var_map, &mut type_var_map, &mut local_next_id, decl.span)?;

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
            self.current_symbol_table_mut(state).insert(method.name.clone(), builder.build());

            // trait_origin is already set on the ModuleEntry::Def above,
            // so no separate reverse lookup registration is needed.
        }

        // Register in symbol table as TraitDecl entry (with hkt_param_index)
        self.current_symbol_table_mut(state).insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                info: cranelisp_types::TraitDeclInfo {
                    name: modified_decl.name.clone(),
                    type_params: modified_decl.type_params.clone(),
                    methods: modified_decl.methods.clone(),
                },
                visibility: decl.visibility,
                docstring: decl.docstring.clone(),
            },
        );

        self.commit_next_id(local_next_id);
        Ok(())
    }

    /// Register a single trait method with its constrained polymorphic scheme.
    #[allow(clippy::too_many_arguments)]
    fn register_trait_method(
        &self,
        state: &mut CheckState,
        trait_name: &TraitName,
        method: &TraitMethodSig,
        type_var_id: TypeId,
        trait_type_params: &[Symbol],
        visibility: Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
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
        .param_names(method.params.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>())
        .trait_origin(fq_trait_name);
        if let Some(doc) = method.docstring.clone() {
            builder = builder.docstring(doc);
        }
        self.current_symbol_table_mut(state).insert(method.name.clone(), builder.build());

        // trait_origin is already set on the ModuleEntry::Def above,
        // so no separate reverse lookup registration is needed.

        Ok(())
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
        let mut local_next_id = self.next_id_snapshot();
        let self_type = Type::Var(type_var_id);

        // Pre-seed var_map: trait type params map to self_type.
        let mut var_map: HashMap<Symbol, Type> = HashMap::new();
        for param in trait_type_params {
            var_map.insert(param.clone(), self_type.clone());
        }

        // A qualified type ref in a method signature (`:primitives/Int`)
        // resolves canonically against the named module — the same
        // `resolve_type_expr_in_module` path the `defn`/`deftype`-field type
        // refs use (FIXME 0436 / spec §8.5). Bare names keep the intrinsic
        // fast-path inside `resolve_trait_type_expr`.
        let resolve_qualified =
            |tref: &cranelisp_types::TypeRef| -> Option<Type> {
                self.resolve_qualified_method_sig_type(state, tref, span)
            };

        let param_types: Vec<Type> = method
            .params
            .iter()
            .map(|(_, p)| {
                resolve_trait_type_expr(p, &self_type, span, &mut var_map, &mut local_next_id, &resolve_qualified)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let ret_type = resolve_trait_type_expr(
            &method.ret_type,
            &self_type,
            span,
            &mut var_map,
            &mut local_next_id,
            &resolve_qualified,
        )?;

        self.commit_next_id(local_next_id);
        Ok(Type::Fn(param_types, Box::new(ret_type)))
    }
}

#[cfg(test)]
mod tests;
