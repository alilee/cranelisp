//! The post-monomorphisation codegen AST — `MonoExpr`.
//!
//! `MonoExpr` is a parallel codegen view of [`Expr`](crate::Expr) whose every
//! node carries a [`ConcreteType`] **non-optionally** in place of `Expr`'s
//! `inferred_type: Option<Box<Type>>`. A representation-undetermined type (a
//! generic / `Type::Var` / unpinned higher-kinded head) is *structurally
//! unrepresentable* on a `MonoExpr` node — by construction of the type, not by a
//! downstream check (Principle 18 — enforce invariants structurally). This is the
//! fullest expression of the user ruling (2026-06-16): "remove passing generics to
//! the backend — they shouldn't even be REPRESENTABLE there." There is no `Type`
//! field on a `MonoExpr` node at all, so the backend — which (Phase 3) consumes
//! `MonoExpr` — *literally cannot* be handed a non-concrete or un-annotated
//! codegen node.
//!
//! **Phase 2a scaffold (produces-but-unused).** This module lands the `MonoExpr`
//! representation + the fallible builder [`MonoExpr::from_expr`]. It is dead code
//! until the mono pass produces it (Phase 2b, `cranelisp-typecheck`) and the
//! backend consumes it (Phase 3). The full arc —
//! `design/arch/concrete-boundary-type.md` — is the standing reference. The
//! builder is non-destructive over the source `Expr` (the backend still reads
//! `Expr.inferred_type` until Phase 3).
//!
//! # What `MonoExpr` carries beyond [`ConcreteType`]
//!
//! Mirroring `Expr` faithfully, every `MonoExpr` node carries its `span: Span`
//! (the backend overlays the global `MethodResolutions` side maps — `pattern_ctors`,
//! residual `resolved_calls` — keyed by span, so spans must survive into the
//! codegen view). `resolved_call: Option<Box<ResolvedCall>>` rides along on the
//! `Apply` and `Var` nodes where `Expr` carries it (the backend reads it directly
//! off the node). The `Annotate` node's `TypeExpr` annotation is **erased** in
//! `MonoExpr` (its only role is to constrain inference, already discharged by the
//! time mono runs; codegen reads the resolved `ty`, never the syntactic
//! `TypeExpr`) — [`MonoExpr::from_expr`] collapses `Annotate { expr, .. }` to its
//! inner `MonoExpr`. `Lambda` param `TypeExpr` annotations are likewise erased;
//! the lambda's `ConcreteType::Fn(..)` (its node `ty`) carries the concrete param
//! types.

use serde::{Deserialize, Serialize};

use std::collections::HashMap;

use crate::{
    ConcreteType, Expr, FQSymbol, FQTypeName, ModeSummary, NotConcrete, Pattern, ResolvedCall,
    Span, Symbol,
};

/// One arm of a monomorphised match expression — a [`Pattern`] (reused verbatim:
/// it carries no type annotation) plus a [`MonoExpr`] body.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonoMatchArm {
    pub pattern: Pattern,
    pub body: MonoExpr,
    pub span: Span,
    /// Advisory ownership site fact (S102 CS-A): the **borrowed-projection
    /// root binding** for this arm's pattern bindings — `Some(root)` when the
    /// arm's destructured bindings are borrowed views rooted in the named
    /// in-scope binding (`design/arch/ownership-inference.md` §4.4;
    /// `Symbol`-keyed matching the backend's `borrowed_vars` as-built —
    /// typecheck §13.6(d): shadowing ⇒ `None` ⇒ Decision-24 materialization).
    /// `None` ⇒ conservative (no provenance; treat as owned/materialized).
    #[serde(default)]
    pub provenance: Option<Symbol>,
    /// The resolved constructor's STORAGE identity for a `Pattern::Constructor`
    /// arm (S109 W1.2, `design/arch/dotted-ctor-canonical-keys.md` §10.2) — the
    /// `FQSymbol` whose `symbol` is the key under which the ctor's `Def` actually
    /// resolved in typecheck (canonical `Type.Ctor` for sum ctors; the type-name
    /// key for the product facet; a bare key for a legacy shape), carried from
    /// `MethodResolutions.pattern_ctors` (keyed by `Pattern::Constructor.span`).
    /// `Some` for `Pattern::Constructor` arms, `None` for `Wildcard`/`Var`.
    ///
    /// The backend reads this by DIRECT keyed lookup and NEVER re-resolves the
    /// bare pattern name context-free — a `None` on a ctor arm is a hard codegen
    /// error, not a silent fallback (Principle 18: the run-to-run wrong-tag
    /// nondeterminism of context-free re-resolution cannot re-open through a
    /// forgettable default).
    #[serde(default)]
    pub resolved_ctor: Option<FQSymbol>,
}

/// Post-monomorphisation codegen AST node.
///
/// Mirrors [`Expr`](crate::Expr)'s variants one-for-one with two differences:
/// every node carries `ty: ConcreteType` (NON-optional) in place of
/// `inferred_type: Option<Box<Type>>`, and the `Annotate` variant is **erased**
/// (it has no `MonoExpr` counterpart — [`MonoExpr::from_expr`] collapses it to its
/// inner node). `Lambda` carries no per-param `TypeExpr` (erased; the concrete
/// param types live in the node's `ConcreteType::Fn`).
///
/// **Structural guarantee:** there is no path from a `MonoExpr` to a `Type::Var`.
/// `ty` is a [`ConcreteType`], whose recursion is on `ConcreteType` itself.
///
/// # Advisory ownership site facts (S102 CS-A)
///
/// The allocation/capture-producing variants (`StringLit`, `Lambda`, `Apply`,
/// `VecLit`, `ConstrADT`) carry three advisory Class-B fields
/// (`design/arch/ownership-inference.md` §3.2/§3.3), written by typecheck's
/// ownership pass in one post-convergence walk and read by backend emission:
///
/// - `escapes: Option<bool>` — does the produced value escape its frame?
/// - `confined: Option<bool>` — do all RC ops on it stay on one strand?
/// - `unique_static: Option<bool>` — statically-proven uniqueness
///   (increment II; present-but-never-`Some` in increment I).
///
/// All are `#[serde(default)]`; **`None` ⇒ conservative**
/// (escapes / crossing / shared) — ignoring them is always sound (monotone
/// soundness, spine §6.1). `Apply` and [`MonoMatchArm`] additionally carry
/// `provenance: Option<Symbol>` — the borrowed-projection root binding
/// (spine §4.4), the one interprocedural fact the backend cannot re-derive
/// locally once a projection has crossed a call.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MonoExpr {
    IntLit {
        value: i64,
        span: Span,
        ty: ConcreteType,
    },
    FloatLit {
        value: f64,
        span: Span,
        ty: ConcreteType,
    },
    BoolLit {
        value: bool,
        span: Span,
        ty: ConcreteType,
    },
    StringLit {
        value: String,
        span: Span,
        ty: ConcreteType,
        // Advisory ownership site facts (enum-level rustdoc; None ⇒ conservative).
        #[serde(default)]
        escapes: Option<bool>,
        #[serde(default)]
        confined: Option<bool>,
        #[serde(default)]
        unique_static: Option<bool>,
    },
    Var {
        name: Symbol,
        span: Span,
        /// How a value-position trait-method reference was resolved by the
        /// typechecker — carried verbatim from `Expr::Var.resolved_call` (the
        /// backend reads it off the node). `None` for ordinary variable
        /// references.
        resolved_call: Option<Box<ResolvedCall>>,
        ty: ConcreteType,
    },
    Let {
        bindings: Vec<(Symbol, MonoExpr)>,
        body: Box<MonoExpr>,
        span: Span,
        ty: ConcreteType,
    },
    If {
        cond: Box<MonoExpr>,
        then_branch: Box<MonoExpr>,
        else_branch: Box<MonoExpr>,
        span: Span,
        ty: ConcreteType,
    },
    /// Lambda — `(fn [param ...] body)`. The per-param `TypeExpr` annotations of
    /// `Expr::Lambda` are **erased**: the concrete param types live in this node's
    /// `ty` (a `ConcreteType::Fn`).
    Lambda {
        params: Vec<Symbol>,
        body: Box<MonoExpr>,
        span: Span,
        ty: ConcreteType,
        // Advisory ownership site facts (enum-level rustdoc; None ⇒ conservative).
        #[serde(default)]
        escapes: Option<bool>,
        #[serde(default)]
        confined: Option<bool>,
        #[serde(default)]
        unique_static: Option<bool>,
    },
    Apply {
        callee: Box<MonoExpr>,
        args: Vec<MonoExpr>,
        span: Span,
        /// How this call was resolved by the typechecker — carried verbatim from
        /// `Expr::Apply.resolved_call` (the backend reads it off the node).
        resolved_call: Option<Box<ResolvedCall>>,
        ty: ConcreteType,
        // Advisory ownership site facts (enum-level rustdoc; None ⇒ conservative).
        #[serde(default)]
        escapes: Option<bool>,
        #[serde(default)]
        confined: Option<bool>,
        #[serde(default)]
        unique_static: Option<bool>,
        /// Borrowed-projection root binding for a projection-producing call
        /// (accessor / `vec-get` — `design/arch/ownership-inference.md` §4.4).
        /// `Symbol`-keyed; shadowing ⇒ `None` ⇒ Decision-24 materialization
        /// (typecheck §13.6(d)). `None` ⇒ conservative.
        #[serde(default)]
        provenance: Option<Symbol>,
    },
    Match {
        scrutinee: Box<MonoExpr>,
        arms: Vec<MonoMatchArm>,
        span: Span,
        /// true for compiler-generated match (e.g. from macro expansion)
        compiler_generated: bool,
        ty: ConcreteType,
    },
    VecLit {
        elements: Vec<MonoExpr>,
        span: Span,
        ty: ConcreteType,
        // Advisory ownership site facts (enum-level rustdoc; None ⇒ conservative).
        #[serde(default)]
        escapes: Option<bool>,
        #[serde(default)]
        confined: Option<bool>,
        #[serde(default)]
        unique_static: Option<bool>,
    },
    Trace {
        modules: Vec<Symbol>,
        body: Box<MonoExpr>,
        span: Span,
        ty: ConcreteType,
    },
    ParBind {
        bindings: Vec<(Symbol, MonoExpr)>,
        body: Box<MonoExpr>,
        span: Span,
        ty: ConcreteType,
    },
    /// Launch-and-continue — the post-mono twin of [`Expr::LaunchContinue`]
    /// (see its rustdoc). Codegen lowers `launched` to a detached supervised
    /// strand (the `IO_TAG_LAUNCH` runtime node, `design/backend/io-trampoline.md §15`)
    /// and proceeds with `continuation` without awaiting it. `ty` is the
    /// continuation's concrete type (the launched effect's result is discarded).
    LaunchContinue {
        launched: Box<MonoExpr>,
        continuation: Box<MonoExpr>,
        span: Span,
        ty: ConcreteType,
    },
    ConstrADT {
        type_name: FQTypeName,
        tag: usize,
        fields: Vec<MonoExpr>,
        span: Span,
        ty: ConcreteType,
        // Advisory ownership site facts (enum-level rustdoc; None ⇒ conservative).
        #[serde(default)]
        escapes: Option<bool>,
        #[serde(default)]
        confined: Option<bool>,
        #[serde(default)]
        unique_static: Option<bool>,
    },
}

impl MonoExpr {
    /// Returns the span of this node.
    pub fn span(&self) -> Span {
        match self {
            MonoExpr::IntLit { span, .. }
            | MonoExpr::FloatLit { span, .. }
            | MonoExpr::BoolLit { span, .. }
            | MonoExpr::StringLit { span, .. }
            | MonoExpr::Var { span, .. }
            | MonoExpr::Let { span, .. }
            | MonoExpr::If { span, .. }
            | MonoExpr::Lambda { span, .. }
            | MonoExpr::Apply { span, .. }
            | MonoExpr::Match { span, .. }
            | MonoExpr::VecLit { span, .. }
            | MonoExpr::Trace { span, .. }
            | MonoExpr::ParBind { span, .. }
            | MonoExpr::LaunchContinue { span, .. }
            | MonoExpr::ConstrADT { span, .. } => *span,
        }
    }

    /// Returns this node's concrete codegen type.
    pub fn ty(&self) -> &ConcreteType {
        match self {
            MonoExpr::IntLit { ty, .. }
            | MonoExpr::FloatLit { ty, .. }
            | MonoExpr::BoolLit { ty, .. }
            | MonoExpr::StringLit { ty, .. }
            | MonoExpr::Var { ty, .. }
            | MonoExpr::Let { ty, .. }
            | MonoExpr::If { ty, .. }
            | MonoExpr::Lambda { ty, .. }
            | MonoExpr::Apply { ty, .. }
            | MonoExpr::Match { ty, .. }
            | MonoExpr::VecLit { ty, .. }
            | MonoExpr::Trace { ty, .. }
            | MonoExpr::ParBind { ty, .. }
            | MonoExpr::LaunchContinue { ty, .. }
            | MonoExpr::ConstrADT { ty, .. } => ty,
        }
    }

    /// The ONLY way to obtain a `MonoExpr` from an [`Expr`]. Walks an
    /// `inferred_type`-annotated `Expr`, converting each node's `inferred_type`
    /// via [`ConcreteType::from_type`], and **fails at the first node whose
    /// `inferred_type` is absent or non-concrete** (returning
    /// [`NotConcrete::Var`] / [`NotConcrete::HktHead`]).
    ///
    /// This failure IS the unified ambiguity / could-not-monomorphise error
    /// (`design/arch/concrete-boundary-type.md` §1.3 / §2.6): a residual `Var` in
    /// a codegen-reaching position means no root pins it. The `Annotate` node is
    /// **erased** — it collapses to its inner `MonoExpr`. `Lambda` param `TypeExpr`
    /// annotations are **erased** — the concrete param types ride in the lambda's
    /// `ty` (`ConcreteType::Fn`).
    ///
    /// Non-destructive over the source `Expr` (Phase 2 is produces-but-unused).
    pub fn from_expr(
        expr: &Expr,
        pattern_ctors: &HashMap<Span, FQSymbol>,
    ) -> Result<MonoExpr, NotConcrete> {
        // The node-level concrete type: every non-erased node MUST carry an
        // `inferred_type`, and it MUST be concrete. An absent annotation is
        // treated as a residual `Var(0)` — the same "this position's type is not
        // representation-determined" failure (an un-annotated codegen node is as
        // illegal as a `Var`-typed one). The erased `Annotate` node is the one
        // node that reads no `ty` of its own.
        match expr {
            Expr::Annotate { expr: inner, .. } => MonoExpr::from_expr(inner, pattern_ctors),

            Expr::IntLit { value, span, .. } => Ok(MonoExpr::IntLit {
                value: *value,
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::FloatLit { value, span, .. } => Ok(MonoExpr::FloatLit {
                value: *value,
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::BoolLit { value, span, .. } => Ok(MonoExpr::BoolLit {
                value: *value,
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::StringLit { value, span, .. } => Ok(MonoExpr::StringLit {
                value: value.clone(),
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
            Expr::Var { name, span, resolved_call, .. } => Ok(MonoExpr::Var {
                name: name.clone(),
                span: *span,
                resolved_call: resolved_call.clone(),
                ty: node_ty(expr)?,
            }),
            Expr::Let { bindings, body, span, .. } => Ok(MonoExpr::Let {
                bindings: bindings
                    .iter()
                    .map(|(n, e)| Ok((n.clone(), MonoExpr::from_expr(e, pattern_ctors)?)))
                    .collect::<Result<_, NotConcrete>>()?,
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::If { cond, then_branch, else_branch, span, .. } => Ok(MonoExpr::If {
                cond: Box::new(MonoExpr::from_expr(cond, pattern_ctors)?),
                then_branch: Box::new(MonoExpr::from_expr(then_branch, pattern_ctors)?),
                else_branch: Box::new(MonoExpr::from_expr(else_branch, pattern_ctors)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::Lambda { params, body, span, .. } => Ok(MonoExpr::Lambda {
                // Param `TypeExpr` annotations are erased — the concrete param
                // types live in the lambda's `ty` (`ConcreteType::Fn`).
                params: params.iter().map(|(n, _)| n.clone()).collect(),
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors)?),
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
            Expr::Apply { callee, args, span, resolved_call, .. } => Ok(MonoExpr::Apply {
                callee: Box::new(MonoExpr::from_expr(callee, pattern_ctors)?),
                args: args
                    .iter()
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors))
                    .collect::<Result<_, NotConcrete>>()?,
                span: *span,
                resolved_call: resolved_call.clone(),
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
                provenance: None,
            }),
            Expr::Match { scrutinee, arms, span, compiler_generated, .. } => Ok(MonoExpr::Match {
                scrutinee: Box::new(MonoExpr::from_expr(scrutinee, pattern_ctors)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        // Carry the resolved-ctor STORAGE identity for a
                        // `Pattern::Constructor` arm from the typecheck sidecar
                        // (§10.2), keyed by the CONSTRUCTOR PATTERN's own span —
                        // the same key `check_constructor_pattern` writes under.
                        // `None` for `Wildcard`/`Var` arms (no ctor to resolve).
                        let resolved_ctor = match &arm.pattern {
                            Pattern::Constructor { span: pat_span, .. } => {
                                pattern_ctors.get(pat_span).cloned()
                            }
                            _ => None,
                        };
                        Ok(MonoMatchArm {
                            pattern: arm.pattern.clone(),
                            body: MonoExpr::from_expr(&arm.body, pattern_ctors)?,
                            span: arm.span,
                            provenance: None,
                            resolved_ctor,
                        })
                    })
                    .collect::<Result<_, NotConcrete>>()?,
                span: *span,
                compiler_generated: *compiler_generated,
                ty: node_ty(expr)?,
            }),
            Expr::VecLit { elements, span, .. } => Ok(MonoExpr::VecLit {
                elements: elements
                    .iter()
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors))
                    .collect::<Result<_, NotConcrete>>()?,
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
            Expr::Trace { modules, body, span, .. } => Ok(MonoExpr::Trace {
                modules: modules.clone(),
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::ParBind { bindings, body, span, .. } => Ok(MonoExpr::ParBind {
                bindings: bindings
                    .iter()
                    .map(|(n, e)| Ok((n.clone(), MonoExpr::from_expr(e, pattern_ctors)?)))
                    .collect::<Result<_, NotConcrete>>()?,
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::LaunchContinue { launched, continuation, span, .. } => {
                Ok(MonoExpr::LaunchContinue {
                    launched: Box::new(MonoExpr::from_expr(launched, pattern_ctors)?),
                    continuation: Box::new(MonoExpr::from_expr(continuation, pattern_ctors)?),
                    span: *span,
                    ty: node_ty(expr)?,
                })
            }
            Expr::ConstrADT { type_name, tag, fields, span, .. } => Ok(MonoExpr::ConstrADT {
                type_name: type_name.clone(),
                tag: *tag,
                fields: fields
                    .iter()
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors))
                    .collect::<Result<_, NotConcrete>>()?,
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
        }
    }
}

/// Reads a non-erased node's `inferred_type` and converts it to a
/// [`ConcreteType`]. An absent annotation is the same failure as a non-concrete
/// one: an un-annotated codegen node has no representation-determined type, so it
/// surfaces as [`NotConcrete::Var`] (the unified ambiguity / could-not-mono
/// error).
fn node_ty(expr: &Expr) -> Result<ConcreteType, NotConcrete> {
    match expr.inferred_type() {
        Some(ty) => ConcreteType::from_type(ty),
        // An un-annotated node is representation-undetermined — the same fact as a
        // residual `Var`. `NotConcrete::Var(0)` carries it (no real `TypeId` to
        // name; the sentinel marks "no concrete type at this position").
        None => Err(NotConcrete::Var(0)),
    }
}

/// A monomorphised function definition carrying a [`MonoExpr`] body.
///
/// The post-mono counterpart of [`MonoDefn`](crate::MonoDefn) (which wraps a
/// `Defn` with an `inferred_type`-annotated `Expr` body). Under the
/// concrete-boundary arc the mono pass builds this from the fully-annotated,
/// subst-resolved `Defn` body at the seam immediately after `apply_subst_to_defn`
/// (`design/arch/concrete-boundary-type.md` §2.4 "mono-population seam"). The
/// `from_expr` failure surfaces as the existing `CranelispError::TypeError`
/// ambiguity error.
///
/// **Phase 2a (produces-but-unused).** Lands the representation; the mono pass
/// (Phase 2b, `cranelisp-typecheck`) populates it; the backend (Phase 3) consumes
/// it. Carries the def's name + visibility-relevant identity alongside the body;
/// the symbol-table entry shape (GOT-slot / `UserFnState::Concrete`) is built by
/// `register_mono_entry` independently of the body's AST form.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonoDefnVariant {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub body: MonoExpr,
    pub span: Span,
    /// The callable's ownership summary ([`ModeSummary`]) — the
    /// **compile-in-hand carrier** the backend reads during
    /// `compile_to_module` (S102 CS-A; the persisted twin lives on the
    /// callable `DefKind` variant's `mode_summary` slot, read via
    /// `ModuleEntry::mode_summary()`). Written by typecheck's ownership pass
    /// in the same post-convergence walk that annotates the body's site
    /// facts. `None` ⇒ Decision-24 conservative
    /// (`design/arch/ownership-inference.md` §3.3).
    #[serde(default)]
    pub mode_summary: Option<ModeSummary>,
}

#[cfg(test)]
mod tests;
