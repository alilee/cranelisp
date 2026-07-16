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
    CodeStore, FQTypeName, ModuleEntry, ResolveError, Span, Symbol, Type, TypeExpr, TypeId, TypeRef,
};

use crate::checker::type_def_view_of;

/// Head-resolution environment for the ONE `TypeExpr -> Type` walk (FIXME 0590).
///
/// The structural recursion, the `/`-guarded mint, the co-reference `var_map`
/// threading, and the ADT arity validation are written ONCE in
/// [`resolve_type_expr`]. What varies per call site is bundled here — this
/// object generalises the two closures the resolver historically took
/// (`resolve_terminal` + `mint_free_var`) with the head-binding *data* the four
/// former mirror resolvers each hand-rolled (Self substitution, HKT
/// constructor-variable interception). It carries NO recursion of its own — a
/// new resolution context is a new `TypeExprCtx` construction, never a second
/// `TypeExpr`-matching walk (the §5 fifth-mirror invariant).
pub(crate) struct TypeExprCtx<'a, C: CodeStore> {
    /// Resolve a [`TypeRef`] to its terminal [`ModuleEntry`] via the caller's
    /// symbol table (current-module lookup + import chain-follow), `None` when
    /// unreachable.
    pub resolve_terminal: &'a dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    /// Mint a fresh unification var for a `TypeVar` name that misses `var_map`.
    /// `Some` in annotation / trait-sig / HKT-sig contexts; `None` in the
    /// `deftype`-field / platform-sig contexts (a free-var miss there is
    /// `TypeNotFound`, §3.9.3).
    pub mint_free_var: Option<&'a dyn Fn() -> TypeId>,
    /// The `Self` substitution. `Some` in trait/impl-method sig contexts (a var
    /// `Type::Var(self_id)` in the decl, a concrete ADT in the impl); `None`
    /// elsewhere, where `SelfType` errors. The trait's type-parameter names
    /// (`self_params`) alias it.
    pub self_type: Option<Type>,
    /// Trait type-parameter names that resolve to `self_type` (e.g. `a` in
    /// `(deftrait (Eq a) ...)`). Empty outside trait/impl-sig contexts and in
    /// HKT contexts (there the trait params are constructor variables, carried
    /// in `con_vars`).
    pub self_params: &'a [Symbol],
    /// HKT constructor-variable interception; `None` outside HKT contexts.
    pub con_vars: ConVars<'a>,
    /// Whether a bare intrinsic scalar (`Int`/`Bool`/`Float`/`String`) resolves
    /// via the [`intrinsic_scalar`] fast-path BEFORE the symbol table (FIXME
    /// 0590 §3). `true` ONLY in the trait/HKT sig contexts — the former mirror
    /// resolvers resolved bare scalars unconditionally, so a sig naming `Int` in
    /// a module that does not reach `primitives` keeps working. `false` in the
    /// deftype-field / annotation / platform contexts, where a bare scalar must
    /// be import-reachable (spec §8.9.1 — `:Int` without an import is an
    /// `unknown type`; zero regression on those paths).
    pub scalar_fastpath: bool,
}

/// The three HKT constructor-variable regimes (Principle 20 — the "no con-vars"
/// / decl-`TyConApp` / impl-target-substitution distinction is explicit and
/// exhaustive, no boolean-flag drift).
pub(crate) enum ConVars<'a> {
    /// No constructor variables (every non-HKT context).
    None,
    /// HKT trait-decl sig: a bare con-var name → `Type::Var(id)`; a con-var
    /// head `(f a)` → `Type::TyConApp(id, args)`.
    Decl(&'a HashMap<Symbol, TypeId>),
    /// HKT impl-method sig: a con-var head `(f a)` → the impl target ADT
    /// `Type::ADT(target, args)`.
    Impl {
        names: &'a [Symbol],
        target: &'a FQTypeName,
    },
}

/// Map a bare `TypeRef` to a `Type` for the reserved intrinsic scalar names.
///
/// These names (`Int`/`Bool`/`Float`/`String`) are reserved and never
/// user-definable, so resolving them structurally is always correct. Retaining
/// the fast-path (FIXME 0590 §3) preserves the former mirror resolvers'
/// behaviour for a bare scalar named in a trait/HKT sig whose module does not
/// reach `primitives` by import.
fn intrinsic_scalar(name: &TypeRef) -> Option<Type> {
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

/// Resolve a type expression to a concrete type.
///
/// `var_map` maps type variable names (e.g., `:a`) to their allocated TypeIds.
/// It is `&mut` because a type-var name may be **minted on first sight** (see
/// `mint_free_var` below) and recorded here so that a later occurrence of the
/// same name — anywhere in the same resolution (`[:a x :a y]`, `:(Box a)`) —
/// resolves to the SAME `TypeId`.
///
/// `ctx.resolve_terminal` resolves a [`TypeRef`] to its terminal [`ModuleEntry`]
/// via the caller's symbol table (current-module lookup + import chain-follow),
/// returning `None` when the name is not reachable.
///
/// This is the SOLE `TypeExpr -> Type` walk in the crate (FIXME 0590 §5): the
/// former four mirror resolvers — trait-method sigs, HKT trait sigs, HKT impl
/// sigs, and the platform-sig pre-walk — all route here now, each supplying a
/// [`TypeExprCtx`] that varies only in head-binding *data*.
///
/// `ctx.mint_free_var` controls what happens when a `TypeVar` name misses
/// `var_map` (spec §3.3, [S109]):
///
/// - **`Some(alloc)` — annotation AND trait/HKT-sig contexts** (`defn`/`fn`
///   parameter, a value annotation `:a form`, a type var nested in an applied
///   annotation `:(Box a)`, or a free type var in a trait/HKT method sig). A
///   lowercase type variable the source author *writes* is implicitly
///   universally quantified at the definition boundary, *identically to an
///   inference-generated variable*. A miss therefore **mints a fresh unification
///   variable** via `alloc()` (the checker's ordinary `fresh_var_id`
///   allocator), binds it in `var_map`, and returns `Type::Var`. Whether that
///   minted var is treated as a RIGID skolem or a flexible var is the *caller's*
///   decision — this resolver only mints and records for co-reference.
/// - **`None` — type-definition context** (`deftype` field, platform sig).
///   A `TypeVar` that is not a declared type parameter is an unbound reference
///   and a miss is an error. The case discrimination is entirely on
///   `TypeExpr::TypeVar` (a lowercase-leading identifier — the frontend routes
///   an uppercase name to `TypeExpr::Named`), so an unknown UPPERCASE type still
///   errors `TypeNotFound` regardless of `mint_free_var` (§3.9.3).
///
/// **Qualified names never mint (F2/0589).** A type variable is a *bare*
/// lowercase identifier (spec §3.3: `a, b, elem, f`). A `TypeVar` name that
/// contains a `/` is a module-qualified reference (`user/int`) the frontend has
/// mis-tagged as a `TypeVar`; it can never be a type variable, so it does NOT
/// mint even in annotation context — it falls to the `TypeNotFound` error
/// naming the qualified string.
pub(crate) fn resolve_type_expr<C: CodeStore>(
    texpr: &TypeExpr,
    var_map: &mut HashMap<Symbol, TypeId>,
    ctx: &TypeExprCtx<C>,
    span: Span,
) -> Result<Type, ResolveError> {
    match texpr {
        TypeExpr::Named(name) => resolve_named(name, ctx, span),

        TypeExpr::FnType(params, ret) => {
            let mut param_types = Vec::with_capacity(params.len());
            for p in params {
                param_types.push(resolve_type_expr(p, var_map, ctx, span)?);
            }
            let ret_type = resolve_type_expr(ret, var_map, ctx, span)?;
            Ok(Type::Fn(param_types, Box::new(ret_type)))
        }

        TypeExpr::TypeVar(name) => resolve_type_var(name, var_map, ctx, span),

        // `Self` substitutes `ctx.self_type` in a trait/impl-method sig context;
        // everywhere else it is the existing `TypeNotFound("Self")` error. The
        // `None` arm is byte-behaviour identical to the pre-convergence
        // canonical resolver — zero regression on deftype/annotation/platform.
        TypeExpr::SelfType => match &ctx.self_type {
            Some(t) => Ok(t.clone()),
            None => Err(ResolveError::TypeNotFound {
                name: cranelisp_types::TypeName::from("Self"),
                from_module: cranelisp_types::ModuleFullPath::from(""),
                span,
            }),
        },

        TypeExpr::Applied(name, args) => resolve_applied(name, args, var_map, ctx, span),

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

/// Resolve a `TypeVar` name to a `Type`, dispatching the head-binding policy.
///
/// Order: (1) an HKT-decl constructor variable → `Type::Var(con_id)`;
/// (2) a trait type-parameter name aliasing `Self` → `ctx.self_type`;
/// (3) a `var_map` co-reference hit → `Type::Var(id)`; (4) a bare lowercase
/// miss under `mint_free_var` → mint + record (a `/`-qualified name is a
/// module-qualified reference, never a var — it must NOT mint, F2/0589);
/// (5) else `TypeNotFound`.
fn resolve_type_var<C: CodeStore>(
    name: &Symbol,
    var_map: &mut HashMap<Symbol, TypeId>,
    ctx: &TypeExprCtx<C>,
    span: Span,
) -> Result<Type, ResolveError> {
    // (1) An HKT-decl constructor variable used bare as a type. A con-var is
    // never a free var, so this precedes the mint.
    if let ConVars::Decl(con_map) = &ctx.con_vars
        && let Some(&con_id) = con_map.get(name)
    {
        return Ok(Type::Var(con_id));
    }
    // (2) A trait type-parameter name aliases `Self` (both resolve to
    // `self_type`; the former mirror pre-seeded `param -> self_type`).
    if ctx.self_params.contains(name)
        && let Some(self_ty) = &ctx.self_type
    {
        return Ok(self_ty.clone());
    }
    // (3) Co-reference: an earlier occurrence of this name already minted an id.
    if let Some(&id) = var_map.get(name) {
        return Ok(Type::Var(id));
    }
    // (4) Annotation / sig-context miss: mint a fresh var (spec §3.3 [S109]) and
    // record it for co-reference. Rigidity is decided by the caller.
    if let Some(alloc) = ctx.mint_free_var
        && !name.as_ref().contains('/')
    {
        let id = alloc();
        var_map.insert(name.clone(), id);
        return Ok(Type::Var(id));
    }
    Err(ResolveError::TypeNotFound {
        name: cranelisp_types::TypeName::from(name.as_ref()),
        from_module: cranelisp_types::ModuleFullPath::from(""),
        span,
    })
}

/// Resolve a named type by matching its terminal `ModuleEntry`.
///
/// The reserved intrinsic scalars (`Int`/`Bool`/`Float`/`String`) short-circuit
/// via [`intrinsic_scalar`] (FIXME 0590 §3). Otherwise a `TypeDef` (sum/enum)
/// OR a single-ctor **product**'s ctor `Def` (`Constructor { type_def: Some(..)
/// }`, S79 dual facet) resolves to `Type::ADT(info.name, [])` via
/// [`type_def_view_of`]; `IntrinsicType` returns its bare `Type` variant
/// directly. An unknown name errors — the never-error `Named` fabrication arms
/// of the former HKT mirror resolvers are DELETED (§3 ruling).
fn resolve_named<C: CodeStore>(
    name: &TypeRef,
    ctx: &TypeExprCtx<C>,
    span: Span,
) -> Result<Type, ResolveError> {
    if ctx.scalar_fastpath
        && let Some(ty) = intrinsic_scalar(name)
    {
        return Ok(ty);
    }
    match (ctx.resolve_terminal)(name) {
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
    ctx: &TypeExprCtx<C>,
    span: Span,
) -> Result<Type, ResolveError> {
    // HKT constructor-variable interception precedes the symbol-table
    // resolution: a con-var head is never an ordinary ADT application. Args
    // recurse through the ONE resolver so nested con-vars are intercepted too.
    let name_sym = Symbol::from(name.name.as_ref());
    match &ctx.con_vars {
        // Decl: `(f a)` where `f` is a con-var → `TyConApp(con_id, args)`.
        ConVars::Decl(con_map) if con_map.contains_key(&name_sym) => {
            let con_id = con_map[&name_sym];
            let mut resolved_args = Vec::with_capacity(args.len());
            for a in args {
                resolved_args.push(resolve_type_expr(a, var_map, ctx, span)?);
            }
            return Ok(Type::TyConApp(con_id, resolved_args));
        }
        // Impl: `(f a)` where `f` is a con-var → the target ADT `(Option a)`.
        ConVars::Impl { names, target } if names.contains(&name_sym) => {
            let target = (*target).clone();
            let mut resolved_args = Vec::with_capacity(args.len());
            for a in args {
                resolved_args.push(resolve_type_expr(a, var_map, ctx, span)?);
            }
            return Ok(Type::ADT(target, resolved_args));
        }
        _ => {}
    }
    match (ctx.resolve_terminal)(name) {
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
                    let elem = resolve_type_expr(&args[0], var_map, ctx, span)?;
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
                    resolved_args.push(resolve_type_expr(a, var_map, ctx, span)?);
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
