use std::collections::HashMap;

use cranelisp_types::{ErrorLocation, CranelispError, FQTypeName, ModuleFullPath,
    Span, Symbol, TraitDecl, TraitDeclInfo, Type, TypeId,
    TypeName,
};


// ---------------------------------------------------------------------------
// Impl-target name extraction + trait-decl identity
// ---------------------------------------------------------------------------

/// Extract the head `TypeName` from an impl's `target: TypeExpr`. Used for
/// diagnostics + lookup at sites that previously consumed the retired
/// `TraitImpl.target_type: TypeName` field. Returns `None` for `SelfType`,
/// `FnType`, and bare `TypeVar` targets — these have no single head name.
/// Per spec §5.4 EBNF, an impl `target` always resolves to `Named` or
/// `Applied`, so callers may `.expect()` in production paths.
pub(super) fn impl_target_name(target: &cranelisp_types::TypeExpr) -> Option<&TypeName> {
    target.head_ref().map(|r| &r.name)
}

/// Extract the head TypeName, panicking if absent — for sites where spec
/// §5.4 guarantees a head name on the impl target.
pub(super) fn impl_target_name_or_panic(target: &cranelisp_types::TypeExpr) -> &TypeName {
    impl_target_name(target).expect("spec §5.4: impl target lowers to Named or Applied")
}

/// Whether an already-registered `TraitDeclInfo` is the SAME declaration as an
/// incoming `TraitDecl` — used to make `register_trait_decl` idempotent under
/// the cluster's retry-from-top re-submission (S86 D3) while still rejecting a
/// genuinely-different redeclaration of the same name (spec 07-traits §7.1).
///
/// `TraitDeclInfo`/`TraitMethodSig`/`TypeExpr` carry no `PartialEq` derive
/// (they live in `cranelisp-types`), so the match compares the surface that
/// uniquely identifies a declaration: trait name, type-parameter list, and each
/// method's name + parameter arity. A retry re-submits the identical parsed
/// decl, so all three agree; a conflicting redeclaration differs in at least
/// one (a method renamed, added, dropped, or its arity changed).
pub(super) fn trait_decl_matches(existing: &TraitDeclInfo, incoming: &TraitDecl) -> bool {
    existing.name == incoming.name
        && existing.type_params == incoming.type_params
        && existing.methods.len() == incoming.methods.len()
        && existing
            .methods
            .iter()
            .zip(incoming.methods.iter())
            .all(|(a, b)| a.name == b.name && a.params.len() == b.params.len())
}

// ---------------------------------------------------------------------------
// TypeExpr -> Type resolution (free functions)
// ---------------------------------------------------------------------------

/// Build the AST body for a known default trait method.
///
/// Hard-codes the bodies for the builtin default methods:
///   Eq.!=  → (not (= x y))
///   Ord.>  → (< y x)
///   Ord.<= → (not (< y x))
///   Ord.>= → (not (< x y))
pub(crate) fn build_default_body(
    trait_name: &str,
    method_name: &str,
    param_names: &[Symbol],
    span: Span,
) -> Result<cranelisp_types::Expr, CranelispError> {
    use cranelisp_types::Expr;

    if param_names.len() != 2 {
        return Err(CranelispError::TypeError {
            message: format!(
                "default method {trait_name}.{method_name}: expected 2 params, got {}",
                param_names.len()
            ),
            location: ErrorLocation::from_span(span),
        });
    }

    let x = Expr::var(param_names[0].clone(), span);
    let y = Expr::var(param_names[1].clone(), span);
    let not_var = Expr::var(Symbol::from("not"), span);
    let eq_var = Expr::var(Symbol::from("="), span);
    let lt_var = Expr::var(Symbol::from("<"), span);

    match (trait_name, method_name) {
        // != → (not (= x y))
        ("Eq", "!=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(eq_var),
                args: vec![x, y],
                span,
                resolved_call: None,
                inferred_type: None,
            }],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        // > → (< y x)
        ("Ord", ">") => Ok(Expr::Apply {
            callee: Box::new(lt_var),
            args: vec![y, x],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        // <= → (not (< y x))
        ("Ord", "<=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(lt_var),
                args: vec![y, x],
                span,
                resolved_call: None,
                inferred_type: None,
            }],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        // >= → (not (< x y))
        ("Ord", ">=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(lt_var),
                args: vec![x, y],
                span,
                resolved_call: None,
                inferred_type: None,
            }],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        _ => Err(CranelispError::TypeError {
            message: format!(
                "no hard-coded default body for {trait_name}.{method_name}"
            ),
            location: ErrorLocation::from_span(span),
        }),
    }
}

// `sexp_to_default_expr` retired in Sprint 72 Wave 1 — per S69 Submission 26,
// `TraitMethodSig.default_body: Option<Expr>` carries pre-parsed AST (vindication
// of the prior facade target). The Sexp→Expr lowering at trait-decl time now
// lives in the frontend `build_method_sig` path; the typecheck consumer simply
// clones the Expr. Decision-grounding: S69 Submission 26 + `design/arch/facades/typecheck.md` §"Typing rule".

/// Map a `TypeRef` to a `Type` for intrinsic scalar names, returning `None`
/// for non-intrinsic names. Caller decides how to handle unknown / user types.
/// Per C-13 (`Type::from_name` retired): intrinsic-bare-names resolve directly;
/// non-intrinsic names flow through ADT placeholders.
pub(super) fn type_from_intrinsic_ref(name: &cranelisp_types::TypeRef) -> Option<Type> {
    if name.module.is_some() {
        return None;
    }
    match name.name.as_ref() {
        "Int" => Some(Type::Int),
        "Bool" => Some(Type::Bool),
        "Float" => Some(Type::Float),
        "String" => Some(Type::String),
        _ => None,
    }
}

/// Resolve a TypeExpr in a trait context, substituting SelfType with the given type.
pub(crate) fn resolve_trait_type_expr(
    texpr: &cranelisp_types::TypeExpr,
    self_type: &Type,
    span: Span,
    var_map: &mut HashMap<Symbol, Type>,
    next_id: &mut TypeId,
) -> Result<Type, CranelispError> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::SelfType => Ok(self_type.clone()),
        TypeExpr::Named(name) => type_from_intrinsic_ref(name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown type: {name}"),
                location: ErrorLocation::from_span(span),
            }),
        TypeExpr::TypeVar(name) => {
            if let Some(ty) = var_map.get(name) {
                Ok(ty.clone())
            } else {
                let ty = crate::unify::fresh_var(next_id);
                var_map.insert(name.clone(), ty.clone());
                Ok(ty)
            }
        }
        TypeExpr::FnType(params, ret) => {
            let ps: Vec<Type> = params
                .iter()
                .map(|p| resolve_trait_type_expr(p, self_type, span, var_map, next_id))
                .collect::<Result<Vec<_>, _>>()?;
            let r = resolve_trait_type_expr(ret, self_type, span, var_map, next_id)?;
            Ok(Type::Fn(ps, Box::new(r)))
        }
        TypeExpr::Applied(name, args) => {
            // Regular ADT application: (Option Int), (List :a)
            // Use a placeholder FQTypeName — the bare name will be resolved
            // when the type flows through the module system.
            let fqtn = FQTypeName::new(ModuleFullPath::from(""), name.name.clone());
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| resolve_trait_type_expr(a, self_type, span, var_map, next_id))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::ADT(fqtn, resolved_args))
        }
        // Stacked trait-bound annotations (`:Eq :Display a`) are a *param-binder*
        // construct (constrained-fn parameters), not a trait-method-signature
        // construct: a trait method's parameter types are concrete types or
        // `Self`/type-vars, never a free constrained binder. Reject rather than
        // silently accept (FIXME 0346).
        TypeExpr::Bounds(_) => Err(CranelispError::TypeError {
            message: "trait bounds are not allowed in a trait-method signature \
                      type position".to_string(),
            location: ErrorLocation::from_span(span),
        }),
    }
}

// ---------------------------------------------------------------------------
// HKT Helpers (free functions)
// ---------------------------------------------------------------------------

/// Resolve a TypeExpr in HKT context, producing TyConApp for constructor variable applications.
pub(super) fn resolve_type_expr_hkt(
    texpr: &cranelisp_types::TypeExpr,
    con_var_map: &HashMap<Symbol, TypeId>,
    type_var_map: &mut HashMap<Symbol, TypeId>,
    next_id: &mut TypeId,
    span: Span,
) -> Result<Type, CranelispError> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            if let Some(&con_id) = con_var_map.get(&name_sym) {
                // Constructor variable application: (f a) -> TyConApp(f_id, [a])
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_hkt(a, con_var_map, type_var_map, next_id, span))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::TyConApp(con_id, resolved_args))
            } else {
                // Regular ADT application: (Option Int)
                let fqtn = FQTypeName::new(ModuleFullPath::from(""), name.name.clone());
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_hkt(a, con_var_map, type_var_map, next_id, span))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::ADT(fqtn, resolved_args))
            }
        }
        TypeExpr::TypeVar(name) => {
            if let Some(&con_id) = con_var_map.get(name) {
                // Bare constructor variable used as a type
                Ok(Type::Var(con_id))
            } else if let Some(&id) = type_var_map.get(name) {
                Ok(Type::Var(id))
            } else {
                let (ty, id) = crate::unify::fresh_var_id(next_id);
                type_var_map.insert(name.clone(), id);
                Ok(ty)
            }
        }
        TypeExpr::Named(name) => {
            Ok(type_from_intrinsic_ref(name).unwrap_or_else(|| { Type::ADT(FQTypeName::new(ModuleFullPath::from(""), name.name.clone()), vec![]) }))
        }
        TypeExpr::SelfType => {
            Err(CranelispError::TypeError {
                message: "Self is not allowed in HKT trait signatures".to_string(),
                location: ErrorLocation::from_span(span),
            })
        }
        TypeExpr::FnType(params, ret) => {
            let param_tys: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_hkt(p, con_var_map, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty = resolve_type_expr_hkt(ret, con_var_map, type_var_map, next_id, span)?;
            Ok(Type::Fn(param_tys, Box::new(ret_ty)))
        }
        // Trait bounds are a param-binder construct, not an HKT trait-method
        // signature construct — reject (FIXME 0346).
        TypeExpr::Bounds(_) => Err(CranelispError::TypeError {
            message: "trait bounds are not allowed in an HKT trait-method \
                      signature type position".to_string(),
            location: ErrorLocation::from_span(span),
        }),
    }
}

/// Resolve a TypeExpr for an HKT impl method.
/// Constructor variable applications are resolved to concrete ADT applications.
/// E.g., for `(impl Functor Option ...)`, `(f a)` becomes `(Option a)`.
pub(super) fn resolve_type_expr_hkt_impl(
    texpr: &cranelisp_types::TypeExpr,
    con_var_names: &[Symbol],
    target_fqtn: &FQTypeName,
    type_var_map: &mut HashMap<Symbol, TypeId>,
    next_id: &mut TypeId,
    span: Span,
) -> Result<Type, CranelispError> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            let fqtn = if con_var_names.contains(&name_sym) {
                // Constructor variable — resolve to the target ADT's FQTypeName.
                target_fqtn.clone()
            } else {
                // Non-constructor-var Applied type — use target module as fallback.
                FQTypeName::new(target_fqtn.module.clone(), name.name.clone())
            };
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| resolve_type_expr_hkt_impl(a, con_var_names, target_fqtn, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::ADT(fqtn, resolved_args))
        }
        TypeExpr::TypeVar(name) => {
            if let Some(&id) = type_var_map.get(name) {
                Ok(Type::Var(id))
            } else {
                let (ty, id) = crate::unify::fresh_var_id(next_id);
                type_var_map.insert(name.clone(), id);
                Ok(ty)
            }
        }
        TypeExpr::Named(name) => {
            Ok(type_from_intrinsic_ref(name).unwrap_or_else(|| { // Use target module as fallback for user-defined types.
                Type::ADT(FQTypeName::new(target_fqtn.module.clone(), name.name.clone()), vec![]) }))
        }
        TypeExpr::SelfType => {
            Err(CranelispError::TypeError {
                message: "Self is not allowed in HKT trait signatures".to_string(),
                location: ErrorLocation::from_span(span),
            })
        }
        TypeExpr::FnType(params, ret) => {
            let param_tys: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_hkt_impl(p, con_var_names, target_fqtn, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty = resolve_type_expr_hkt_impl(ret, con_var_names, target_fqtn, type_var_map, next_id, span)?;
            Ok(Type::Fn(param_tys, Box::new(ret_ty)))
        }
        // Trait bounds are a param-binder construct, not an HKT impl-method
        // signature construct — reject (FIXME 0346).
        TypeExpr::Bounds(_) => Err(CranelispError::TypeError {
            message: "trait bounds are not allowed in an HKT impl-method \
                      signature type position".to_string(),
            location: ErrorLocation::from_span(span),
        }),
    }
}

/// Check if a TypeExpr uses any of the constructor variable names in Applied position.
pub(super) fn type_expr_uses_con_var(texpr: &cranelisp_types::TypeExpr, con_names: &[Symbol]) -> bool {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            con_names.contains(&name_sym)
                || args.iter().any(|a| type_expr_uses_con_var(a, con_names))
        }
        TypeExpr::FnType(params, ret) => {
            params.iter().any(|p| type_expr_uses_con_var(p, con_names))
                || type_expr_uses_con_var(ret, con_names)
        }
        _ => false,
    }
}

/// Find the first parameter index that uses a constructor variable in Applied position.
pub(super) fn find_hkt_param_index(params: &[(Symbol, cranelisp_types::TypeExpr)], type_params: &[Symbol]) -> usize {
    for (idx, (_, param)) in params.iter().enumerate() {
        if type_expr_uses_con_var(param, type_params) {
            return idx;
        }
    }
    0 // fallback to first param
}

/// Determine the arity (number of type args) of a constructor variable in a trait declaration.
pub(super) fn con_var_arity(decl: &TraitDeclInfo, con_name: &Symbol) -> Option<usize> {
    for method in &decl.methods {
        for (_, param) in &method.params {
            if let Some(arity) = find_applied_arity(param, con_name) {
                return Some(arity);
            }
        }
        if let Some(arity) = find_applied_arity(&method.ret_type, con_name) {
            return Some(arity);
        }
    }
    None
}

/// Find the arity of a constructor variable name in a TypeExpr tree.
pub(super) fn find_applied_arity(texpr: &cranelisp_types::TypeExpr, con_name: &Symbol) -> Option<usize> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            if &name_sym == con_name {
                Some(args.len())
            } else {
                args.iter().find_map(|a| find_applied_arity(a, con_name))
            }
        }
        TypeExpr::FnType(params, ret) => {
            params.iter().find_map(|p| find_applied_arity(p, con_name))
                .or_else(|| find_applied_arity(ret, con_name))
        }
        _ => None,
    }
}
