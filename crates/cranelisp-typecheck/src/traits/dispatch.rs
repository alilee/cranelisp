
use cranelisp_types::{ErrorLocation, CranelispError, FQTraitName,
    JitSymbol, ModuleEntry, ModuleFullPath, ResolvedCall,
    Span, Symbol, TraitMethodSig, TraitName, Type,
    TypeName,
};

use crate::checker::{CheckState, TypeCheckEnv};
use super::*;

// ---------------------------------------------------------------------------
// Method Resolution
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Try to resolve a call as a trait method.
    ///
    /// Returns Some(ResolvedCall::TraitMethod) if the callee is a trait method
    /// and the argument types resolve to a concrete impl.
    /// Returns None if the callee is not a trait method.
    pub(crate) fn try_resolve_trait_method(
        &self,
        state: &mut CheckState,
        callee_name: &Symbol,
        arg_types: &[Type],
        span: Span,
    ) -> Result<Option<ResolvedCall>, CranelispError> {
        // Check if this name is a trait method (via trait_origin on ModuleEntry::Def).
        // State-rooted: chain-follow from the current module's view per Principle 17.
        let trait_name = match self.method_to_trait_with_state(state, callee_name) {
            Some(tn) => tn,
            None => return Ok(None),
        };

        // Use hkt_param_index for dispatch argument selection (defaults to 0)
        let param_idx = self.hkt_param_idx_for_method(state, callee_name);
        let resolved_arg = match arg_types.get(param_idx) {
            Some(a) => self.apply_subst(state, a),
            // No dispatch argument at this position. This is the nullary
            // return-type-polymorphic case (e.g. `(deftrait T (z [] self))`):
            // the method's only type information is its `self` return, so
            // dispatch on the call's *return type* fixed by the call context
            // (`(add-i64 (z) 5)` fixes `(z)` to Int). Only valid when the
            // method's signature actually puts `Self` in return position —
            // otherwise return-type dispatch would be unsound.
            None => match self.method_return_dispatch_type(state, callee_name, span) {
                Some(ret_ty) => ret_ty,
                None => return Ok(None),
            },
        };

        let impl_type_name = match concrete_type_name(&resolved_arg) {
            Some(tn) => tn,
            // Type is still a variable — defer resolution (batch mode will
            // catch this during monomorphisation).
            None => return Ok(None),
        };

        // Check if an impl exists — if the name IS a trait method and the
        // type IS concrete but the impl DOESN'T exist, that's a type error.
        // State-rooted: chain-follow the trait reference from the current
        // module's view to the trait's defining module per Decision 45.
        if !self.has_impl_with_state(state, &trait_name, &impl_type_name) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "no impl of trait {} for type {}",
                    trait_name, impl_type_name
                ),
                location: ErrorLocation::from_span(span),
            });
        }

        // Primitive trait-method short-circuit (FIXME 0185).
        //
        // When the resolved (trait, method, impl_type) names a primitive
        // operator on a primitive type (e.g., (Num, +, Int) → "add-i64"),
        // emit `ResolvedCall::BuiltinFn` directly so backend inlines via
        // `try_emit_inline_primitive` instead of routing through the
        // trait-impl body wrapper. This preserves the pre-D43 inline
        // optimisation while keeping backend trait-free (the dispatch is
        // monomorphisation-keyed in typecheck, not trait-keyed in backend).
        if let Some(prim_name) = primitive_for_trait_method(&trait_name, callee_name, &impl_type_name) {
            return Ok(Some(ResolvedCall::BuiltinFn {
                name: Symbol::from(prim_name),
            }));
        }

        let mangled = format!(
            "{}.{}${}",
            trait_name, callee_name, impl_type_name
        );

        // Build FQTraitName — chain-follow the trait reference to its
        // defining module per Decision 45 Pattern B. `has_impl_with_state`
        // succeeded just above, so the chain-follow is guaranteed.
        let trait_defining_module = self
            .resolve_trait(state, trait_name.as_ref(), span)
            .map_err(cranelisp_types::CranelispError::from)?;
        let fq_trait_name = FQTraitName::new(trait_defining_module, trait_name);

        // Build FQTypeName for the impl type — works for both ADT and
        // intrinsic targets (Phase B Part 5).
        let fq_impl_type = self
            .resolve_type(state, &impl_type_name, span)
            .map_err(cranelisp_types::CranelispError::from)?;

        Ok(Some(ResolvedCall::TraitMethod {
            trait_name: fq_trait_name,
            method_name: callee_name.clone(),
            impl_type: fq_impl_type,
            mangled_name: JitSymbol::from(mangled.as_str()),
        }))
    }
}

// ---------------------------------------------------------------------------
// Primitive trait-method dispatch table (FIXME 0185)
// ---------------------------------------------------------------------------

/// Map `(trait, method, impl_type) → primitive jit name` for the small set
/// of Ring-0 operator impls that the typecheck-side optimisation collapses
/// from `ResolvedCall::TraitMethod` to `ResolvedCall::BuiltinFn`.
///
/// Per FIXME 0185 (filed by /dev (backend) Sprint 67 Wave 3), this restores
/// the inline-substitution optimisation that the backend's
/// `primitive_for_trait_method` deletion removed (Decision 43 close — backend
/// has no trait knowledge). The dispatch lives here because the resolution
/// is monomorphisation-keyed (which `(impl_type, method)` resolves to which
/// primitive name) and that information is available at typecheck time.
///
/// **Monomorphisation-keyed**, not **trait-keyed** — Decision 43 compatible.
/// Backend continues to handle `ResolvedCall::BuiltinFn { name }` via
/// `try_emit_inline_primitive(name)` without any trait knowledge.
///
/// The mapping mirrors the pre-D43 `primitive_for_trait_method` table in
/// `crates/cranelisp-backend/src/primitives_inline.rs` (deleted in Wave 3 row 6).
pub(crate) fn primitive_for_trait_method(
    trait_name: &TraitName,
    method_name: &Symbol,
    impl_type: &TypeName,
) -> Option<&'static str> {
    let t = trait_name.as_ref();
    let m = method_name.as_ref();
    let i = impl_type.as_ref();

    match (t, m, i) {
        // Num trait: arithmetic operators
        ("Num", "+", "Int") => Some("add-i64"),
        ("Num", "-", "Int") => Some("sub-i64"),
        ("Num", "*", "Int") => Some("mul-i64"),
        ("Num", "/", "Int") => Some("div-i64"),
        ("Num", "+", "Float") => Some("add-f64"),
        ("Num", "-", "Float") => Some("sub-f64"),
        ("Num", "*", "Float") => Some("mul-f64"),
        ("Num", "/", "Float") => Some("div-f64"),

        // Eq trait: equality operators
        ("Eq", "=", "Int") => Some("eq-i64"),
        ("Eq", "=", "Float") => Some("eq-f64"),
        ("Eq", "=", "Bool") => Some("eq-bool"),
        ("Eq", "=", "String") => Some("str-eq"),

        // Ord trait: comparison operators
        ("Ord", "<", "Int") => Some("lt-i64"),
        ("Ord", "<", "Float") => Some("lt-f64"),
        ("Ord", ">", "Int") => Some("gt-i64"),
        ("Ord", ">", "Float") => Some("gt-f64"),
        ("Ord", "<=", "Int") => Some("le-i64"),
        ("Ord", "<=", "Float") => Some("le-f64"),
        ("Ord", ">=", "Int") => Some("ge-i64"),
        ("Ord", ">=", "Float") => Some("ge-f64"),

        // Eq trait: inequality (default method)
        ("Eq", "!=", "Int") => Some("neq-i64"),
        ("Eq", "!=", "Float") => Some("neq-f64"),
        ("Eq", "!=", "Bool") => Some("neq-bool"),
        ("Eq", "!=", "String") => Some("neq-string"),

        // Display trait: show (string conversion)
        ("Display", "show", "Int") => Some("int-to-string"),
        ("Display", "show", "Float") => Some("float-to-string"),
        ("Display", "show", "Bool") => Some("bool-to-string"),
        ("Display", "show", "String") => Some("string-identity"),

        _ => None,
    }
}

// Continuation impl for the original trait-method block — split by the
// primitive_for_trait_method dispatch table inserted above per FIXME 0185.
impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Check if a callee name is a trait method (via trait_origin on ModuleEntry::Def).
    /// Default-rooted to `user` — for state-aware callers use
    /// [`Self::is_trait_method_with_state`].
    #[allow(dead_code)]
    pub(crate) fn is_trait_method(&self, name: &Symbol) -> bool {
        self.method_to_trait(name).is_some()
    }

    /// State-rooted variant of [`Self::is_trait_method`]. Chain-follows from
    /// `state.current_module` per Principle 17.
    pub(crate) fn is_trait_method_with_state(&self, state: &CheckState, name: &Symbol) -> bool {
        self.method_to_trait_with_state(state, name).is_some()
    }
}

// ---------------------------------------------------------------------------
// Self-in-return predicate (D-default dispatch — stays with try_resolve_trait_method)
// ---------------------------------------------------------------------------

/// Whether a `TypeExpr` references the trait's `Self` type anywhere within it.
/// Used to decide whether a nullary trait method is return-type-polymorphic
/// (its `self` is in the return position) so the call context can fix the
/// dispatch type. `TypeExpr::Applied` is NOT treated as Self-bearing unless one
/// of its arguments is `Self` — a `(Vec self)` return still dispatches on the
/// element, which is the structural-Self case handled here recursively.
pub(super) fn type_expr_references_self(texpr: &cranelisp_types::TypeExpr) -> bool {
    use cranelisp_types::TypeExpr;
    match texpr {
        TypeExpr::SelfType => true,
        TypeExpr::FnType(params, ret) => {
            params.iter().any(type_expr_references_self) || type_expr_references_self(ret)
        }
        TypeExpr::Applied(_, args) => args.iter().any(type_expr_references_self),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// HKT Method Resolution Helpers (on TypeChecker)
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Get the HKT param index for a method name, defaulting to 0.
    /// For mangled names like "Functor.fmap$Option", extracts the base method name first.
    ///
    /// Per Principle 17 — current-module-rooted; trait declarations reach
    /// here via the prelude's per-symbol `ModuleEntry::Import` bindings (or
    /// the user's explicit imports), which the underlying chain-follow
    /// follows back to the trait's defining module.
    fn hkt_param_idx_for_method(&self, state: &CheckState, name: &Symbol) -> usize {
        let name_str = name.as_ref();
        // Try direct lookup
        if let Some(idx) = self.find_hkt_param_index_in_registry(state, name_str) {
            return idx;
        }
        // For mangled names like "Functor.fmap$Option", extract the method name
        if let Some(dollar_pos) = name_str.find('$') {
            let prefix = &name_str[..dollar_pos];
            // Handle trait-qualified names: "Trait.method" -> "method"
            let base = if let Some(dot_pos) = prefix.rfind('.') {
                &prefix[dot_pos + 1..]
            } else {
                prefix
            };
            if let Some(idx) = self.find_hkt_param_index_in_registry(state, base) {
                return idx;
            }
        }
        0
    }

    /// Return the dispatch type for a **nullary return-type-polymorphic** trait
    /// method — one with no parameter to dispatch on, whose `self` lives in the
    /// return position (e.g. `(deftrait T (z [] self))`, `(default)`, `(zero)`).
    ///
    /// Returns `Some(concrete_return_type)` ONLY when BOTH hold:
    /// 1. the method's declared `ret_type` references `Self` (so the return type
    ///    *is* the impl type — dispatching on it is sound), AND
    /// 2. the call's return type recorded at `span` is concrete after subst.
    ///
    /// Returns `None` otherwise (not a Self-returning method, or the return type
    /// is still an unresolved var). The caller treats `None` as "cannot resolve
    /// here, defer". This is what lets the call-context type (`(add-i64 (z) 5)`
    /// fixing `(z)` to `Int`) select the concrete impl when there is no argument
    /// to dispatch on.
    fn method_return_dispatch_type(
        &self,
        state: &CheckState,
        method_name: &Symbol,
        span: Span,
    ) -> Option<Type> {
        if !self.method_self_in_return(state, method_name.as_ref()) {
            return None;
        }
        let recorded = state.expr_types.get(&span)?;
        let resolved = self.apply_subst(state, recorded);
        // Only dispatch when the return type is concrete; a residual var means
        // the call context has not fixed it yet — defer.
        concrete_type_name(&resolved)?;
        Some(resolved)
    }

    /// Whether the trait method `method_name` declares `Self` in its return
    /// position. Reads `ret_type`'s `Self` reference off the first visible
    /// `TraitDecl` declaring `method_name`, via the shared bulk trait-decl scan
    /// ([`Self::find_trait_method_decl`]). "Method not found in any visible
    /// trait decl" defaults to `false`.
    fn method_self_in_return(&self, state: &CheckState, method_name: &str) -> bool {
        self.find_trait_method_decl(state, method_name, |m| {
            type_expr_references_self(&m.ret_type)
        })
        .unwrap_or(false)
    }

    /// Walk trait declarations visible from `state.current_module` to find a
    /// method's `hkt_param_index`, via the shared bulk trait-decl scan
    /// ([`Self::find_trait_method_decl`]).
    ///
    /// The read returns the method's own `hkt_param_index: Option<usize>`, so
    /// the scan yields `Option<Option<usize>>` which is `.flatten()`ed:
    /// "method absent from every visible decl" (outer `None`) is DISTINCT from
    /// "method present but `hkt_param_index: None`" (inner `None`) — the HKT
    /// dispatch path relies on this distinction (§3.3).
    fn find_hkt_param_index_in_registry(
        &self,
        state: &CheckState,
        method_name: &str,
    ) -> Option<usize> {
        self.find_trait_method_decl(state, method_name, |m| m.hkt_param_index)
            .flatten()
    }

    /// Shared bulk trait-decl scan (S87 Finding S87-5 dedup): find the first
    /// `TraitDecl` visible from `state.current_module` (with the implicit-prelude
    /// outer-scope fallback) that declares a method named `method_name`, and
    /// return `read(method)`.
    ///
    /// Per Principle 17 shape 4 (bulk introspection — current-module-only):
    /// iterates the current module's symbol table; `Import`/`Reexport` entries
    /// are chain-followed to their terminal `TraitDecl` so traits imported
    /// (e.g. via the prelude) are reachable. On a current-module miss, consults
    /// the prelude outer scope iff the bit is ON (`prelude_fallback_target`;
    /// absence-is-OFF, never self-fallback) with `public_only = true` — only
    /// PUBLIC prelude `TraitDecl`s are reachable as a bare method (`/review`
    /// I-1).
    ///
    /// Returns `None` when no visible trait decl declares `method_name`. The
    /// caller decides the not-found default — `Self::find_hkt_param_index_in_registry`
    /// reads an `Option<usize>` field (so it sees `Option<Option<usize>>` and
    /// distinguishes absent from field-`None`); `Self::method_self_in_return`
    /// reads a `bool` and defaults not-found to `false` (§3.3). The single
    /// I-1 public-head filter lives here (one chokepoint, Principle 7).
    fn find_trait_method_decl<R>(
        &self,
        state: &CheckState,
        method_name: &str,
        read: impl Fn(&TraitMethodSig) -> R,
    ) -> Option<R> {
        if let Some(r) =
            self.find_trait_method_decl_in_module(state, &state.current_module, method_name, false, &read)
        {
            return Some(r);
        }
        // Inner miss — consult the prelude outer scope iff the bit is ON.
        let prelude = self.prelude_fallback_target(&state.current_module)?;
        self.find_trait_method_decl_in_module(state, &prelude, method_name, true, &read)
    }

    /// Iterate `module_path`'s symbol table for a `TraitDecl` carrying
    /// `method_name`, returning `read(method)`. Shared by the current-module
    /// probe and the prelude outer-scope fallback in
    /// [`Self::find_trait_method_decl`].
    ///
    /// `public_only` filters the scanned `module_path` bindings to PUBLIC heads
    /// only — set for the prelude outer-scope fallback hop so a Private prelude
    /// `TraitDecl` does not leak its methods as bare names (`/review` I-1).
    fn find_trait_method_decl_in_module<R>(
        &self,
        state: &CheckState,
        module_path: &ModuleFullPath,
        method_name: &str,
        public_only: bool,
        read: &impl Fn(&TraitMethodSig) -> R,
    ) -> Option<R> {
        // Staging-aware (FIXME 0179): iterate the unioned View when probing the
        // current module so in-cluster TraitDecl registrations are visible. For
        // the prelude fallback the prelude is never the staging module, so a
        // plain owned-name snapshot is sufficient. When `public_only`, drop
        // non-public head bindings before chain-following (I-1).
        let names: Vec<Symbol> = if *module_path == state.current_module {
            let r = self.current_symbol_table(state);
            r.view()
                .iter()
                .filter(|(_, entry)| !public_only || entry.is_public())
                .map(|(name, _)| name.clone())
                .collect()
        } else {
            let mut names = Vec::new();
            self.for_each_in_module(module_path, |name, entry| {
                if !public_only || entry.is_public() {
                    names.push(name.clone());
                }
            });
            names
        };
        for name in &names {
            if let Some(terminal) =
                self.resolve_terminal_entry_and_home(module_path, name.as_ref()).map(|(e, _home)| e)
                && let ModuleEntry::TraitDecl { info, .. } = terminal
            {
                for method in &info.methods {
                    if method.name.as_ref() == method_name {
                        return Some(read(method));
                    }
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests;
