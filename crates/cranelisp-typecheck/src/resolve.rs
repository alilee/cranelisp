//! Resolve TypeExpr (source annotations) to Type.
//!
//! All resolution returns Result, never panics (addresses audit HIGH-4).
//!
//! Resolution matches directly on the terminal [`ModuleEntry`] reached by the
//! injected `resolve_terminal` closure — no intermediate snapshot map. The
//! closure (built by the caller, which owns the symbol table) performs the
//! current-module lookup + import chain-follow and hands back the terminal
//! entry; this module reads everything it needs off that entry: ADT
//! `FQTypeName` and arity from `TypeDef`, the bare `Type` variant from
//! `IntrinsicType`. Keeping resolve.rs on the boundary type `ModuleEntry`
//! (rather than the checker's internals) preserves its decoupling.

use std::collections::HashMap;

use cranelisp_types::{
    CodeStore, ModuleEntry, ResolveError, Span, Symbol, Type, TypeExpr, TypeId, TypeRef,
};

use crate::checker::type_def_view_of;

/// Resolve a type expression to a concrete type.
///
/// `var_map` maps type variable names (e.g., `:a`) to their allocated TypeIds.
/// It is `&mut` because a type-var name may be **minted on first sight** (see
/// `mint_free_var` below) and recorded here so that a later occurrence of the
/// same name — anywhere in the same resolution (`[:a x :a y]`, `:(Box a)`) —
/// resolves to the SAME `TypeId`.
///
/// `resolve_terminal` resolves a [`TypeRef`] to its terminal [`ModuleEntry`]
/// via the caller's symbol table (current-module lookup + import chain-follow),
/// returning `None` when the name is not reachable.
///
/// `mint_free_var` controls what happens when a `TypeVar` name misses `var_map`
/// (spec §3.3, [S109]):
///
/// - **`Some(alloc)` — annotation context** (`defn`/`fn` parameter, a value
///   annotation `:a form`, or a type var nested in an applied annotation
///   `:(Box a)`). A lowercase type variable the source author *writes* in an
///   annotation is implicitly universally quantified at the definition boundary,
///   *identically to an inference-generated variable*. A miss therefore **mints
///   a fresh unification variable** via `alloc()` (the checker's ordinary
///   `fresh_var_id` allocator), binds it in `var_map`, and returns `Type::Var`.
///   The minted var flows into exactly the same generalisation + §3.11 ambiguity
///   machinery as any inference-generated var — there is no parallel path.
/// - **`None` — type-definition context** (`deftype` field, trait-method sig).
///   A `TypeVar` that is not a declared type parameter is an unbound reference
///   and a miss is an error, as before. The case discrimination is entirely on
///   `TypeExpr::TypeVar` (a lowercase-leading identifier — the frontend routes
///   an uppercase name to `TypeExpr::Named`), so an unknown UPPERCASE type still
///   errors `TypeNotFound` regardless of `mint_free_var` (§3.9.3).
pub fn resolve_type_expr<C: CodeStore>(
    texpr: &TypeExpr,
    var_map: &mut HashMap<Symbol, TypeId>,
    resolve_terminal: &dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    mint_free_var: Option<&dyn Fn() -> TypeId>,
    span: Span,
) -> Result<Type, ResolveError> {
    match texpr {
        TypeExpr::Named(name) => resolve_named(name, resolve_terminal, span),

        TypeExpr::FnType(params, ret) => {
            let mut param_types = Vec::with_capacity(params.len());
            for p in params {
                param_types.push(resolve_type_expr(
                    p, var_map, resolve_terminal, mint_free_var, span,
                )?);
            }
            let ret_type = resolve_type_expr(ret, var_map, resolve_terminal, mint_free_var, span)?;
            Ok(Type::Fn(param_types, Box::new(ret_type)))
        }

        TypeExpr::TypeVar(name) => {
            if let Some(&id) = var_map.get(name) {
                Ok(Type::Var(id))
            } else if let Some(alloc) = mint_free_var {
                // Annotation-context miss: mint a fresh quantified var (spec §3.3
                // [S109]) and record it so later occurrences of this name in the
                // same resolution co-refer.
                let id = alloc();
                var_map.insert(name.clone(), id);
                Ok(Type::Var(id))
            } else {
                Err(ResolveError::TypeNotFound {
                    name: cranelisp_types::TypeName::from(name.as_ref()),
                    from_module: cranelisp_types::ModuleFullPath::from(""),
                    span,
                })
            }
        }

        TypeExpr::SelfType => Err(ResolveError::TypeNotFound {
            name: cranelisp_types::TypeName::from("Self"),
            from_module: cranelisp_types::ModuleFullPath::from(""),
            span,
        }),

        TypeExpr::Applied(name, args) => {
            resolve_applied(name, args, var_map, resolve_terminal, mint_free_var, span)
        }

        // A `Bounds([..])` annotation is NOT a concrete type — it is "an
        // unspecified type satisfying these trait bounds" (spec §3.9.2/§3.9.3,
        // FIXME 0346). It resolves to a *fresh constrained type variable*, not
        // to a `Type`, and the constraint must be accumulated onto the binder's
        // `Scheme.constraints`. That requires a fresh-var allocator and a
        // constraint sink (`active_constraints`) — neither of which this pure
        // `TypeExpr -> Type` resolver owns. The owning consumer
        // (`program.rs::register_defn_signature`, the try-type-then-trait site)
        // therefore intercepts `Bounds` *before* delegating here, so a `Bounds`
        // never reaches this arm in practice. Reaching it is an internal routing
        // bug; surface it rather than silently fabricating a concrete type.
        TypeExpr::Bounds(_) => Err(ResolveError::TypeNotFound {
            name: cranelisp_types::TypeName::from("<trait-bounds>"),
            from_module: cranelisp_types::ModuleFullPath::from(""),
            span,
        }),
    }
}

fn type_not_found(name: &TypeRef, span: Span) -> ResolveError {
    ResolveError::TypeNotFound {
        name: name.name.clone(),
        from_module: name
            .module
            .clone()
            .unwrap_or_else(|| cranelisp_types::ModuleFullPath::from("")),
        span,
    }
}

/// Resolve a named type by matching its terminal `ModuleEntry`.
///
/// A `TypeDef` (sum/enum) OR a single-ctor **product**'s ctor `Def`
/// (`Constructor { type_def: Some(..) }`, S79 dual facet) resolves to
/// `Type::ADT(info.name, [])` via [`type_def_view_of`]; `IntrinsicType` returns
/// its bare `Type` variant (`Type::Int`, etc.) directly.
fn resolve_named<C: CodeStore>(
    name: &TypeRef,
    resolve_terminal: &dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    span: Span,
) -> Result<Type, ResolveError> {
    match resolve_terminal(name) {
        Some(ModuleEntry::IntrinsicType { ty, .. }) => Ok(ty),
        Some(entry) => match type_def_view_of(&entry) {
            Some(info) => Ok(Type::ADT(info.name.clone(), vec![])),
            None => Err(type_not_found(name, span)),
        },
        None => Err(type_not_found(name, span)),
    }
}

/// Resolve an applied type constructor: `(Option Int)`, `(List :a)`.
///
/// Validates that the number of type arguments matches the ADT's declared
/// type-parameter count (`info.type_params.len()`).
fn resolve_applied<C: CodeStore>(
    name: &TypeRef,
    args: &[TypeExpr],
    var_map: &mut HashMap<Symbol, TypeId>,
    resolve_terminal: &dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    mint_free_var: Option<&dyn Fn() -> TypeId>,
    span: Span,
) -> Result<Type, ResolveError> {
    match resolve_terminal(name) {
        // Intrinsics are zero-arity; applied form short-circuits to the bare
        // `Type` (the parser can emit `Applied` with empty args).
        Some(ModuleEntry::IntrinsicType { ty, .. }) => Ok(ty),
        // `TypeDef` (sum/enum) OR a product ctor's type facet (S79 dual facet)
        // both answer as a type via `type_def_view_of`.
        Some(entry) => match type_def_view_of(&entry) {
            Some(info) => {
                // FIXME 0385: the builtin `Vec` (`primitives/Vec`) is genuinely
                // arity-1 (`(Vec a)`, spec §3.2.7) but is seeded with empty
                // `type_params` (no surface ctor / declared params — see
                // `src/bootstrap.rs` + `builtins.rs`). Its element type is carried
                // structurally in inference (`infer_vec_lit` builds
                // `Type::ADT(primitives/Vec, [elem])`), not via a declared param.
                // Without this carve-out `:(Vec Int)` fails the arity gate below
                // ("unknown type `Vec`"), leaving the §3.11.1 worked-example
                // disambiguation `(id :(Vec Int) [])` unfixable. Accept exactly one
                // type argument for the builtin `Vec` regardless of its (empty)
                // declared arity, resolving to `Type::ADT(primitives/Vec, [arg])`.
                if info.name.module.as_ref() == "primitives"
                    && info.name.name.as_ref() == "Vec"
                    && info.type_params.is_empty()
                {
                    if args.len() != 1 {
                        return Err(ResolveError::TypeNotFound {
                            name: name.name.clone(),
                            from_module: name
                                .module
                                .clone()
                                .unwrap_or_else(|| cranelisp_types::ModuleFullPath::from("")),
                            span,
                        });
                    }
                    let elem = resolve_type_expr(
                        &args[0], var_map, resolve_terminal, mint_free_var, span,
                    )?;
                    return Ok(Type::ADT(info.name.clone(), vec![elem]));
                }
                let expected_arity = info.type_params.len();
                if args.len() != expected_arity {
                    return Err(ResolveError::TypeNotFound {
                        name: name.name.clone(),
                        from_module: name
                            .module
                            .clone()
                            .unwrap_or_else(|| cranelisp_types::ModuleFullPath::from("")),
                        span,
                    });
                }
                let mut resolved_args = Vec::with_capacity(args.len());
                for a in args {
                    resolved_args.push(resolve_type_expr(
                        a, var_map, resolve_terminal, mint_free_var, span,
                    )?);
                }
                Ok(Type::ADT(info.name.clone(), resolved_args))
            }
            None => Err(type_not_found(name, span)),
        },
        None => Err(type_not_found(name, span)),
    }
}

#[cfg(test)]
mod tests;
