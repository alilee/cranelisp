use cranelisp_types::{ErrorLocation, CranelispError, Span, Symbol, TraitDecl, TraitDeclInfo,
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

// ---------------------------------------------------------------------------
// HKT Helpers (free functions)
// ---------------------------------------------------------------------------
//
// FIXME 0590: the four `TypeExpr -> Type` mirror resolvers
// (`resolve_trait_type_expr`, `resolve_type_expr_hkt`,
// `resolve_type_expr_hkt_impl` here + `form.rs::check_type_expr`'s pre-walk)
// were collapsed onto the ONE canonical `crate::resolve::resolve_type_expr`
// driven by a `TypeExprCtx` head-resolution context. The trait-sig / HKT-sig /
// HKT-impl callers now construct a `TypeExprCtx` and call the sig wrappers on
// `TypeCheckEnv` (`resolve_trait_sig_type_expr`, `resolve_hkt_sig_type_expr`,
// `resolve_hkt_impl_type_expr`). The former never-error `Named` fabrication arms
// are DELETED — an unknown type name in a sig is a source error, resolved
// against the symbol table exactly as `defn`/`deftype`-field refs are.

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

#[cfg(test)]
mod tests;
