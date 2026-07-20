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

/// How a `MonoExpr::Var` reference was resolved — the CLOSED sum at the
/// checked-program boundary (S114, FIXME 0653 prong 3; Principle 24 corollary
/// "resolution products travel typed" — `principles/24-resolve-once.md`;
/// design: `design/arch/typed-resolution-carrier.md`).
///
/// Constructed ONLY by typecheck, at its Var-resolution chokepoint.
/// **"Unresolved" has NO constructor**: a `Var` whose reference typecheck could
/// not classify as one of these two states is a LOCATED typecheck error at
/// view-build time, never a representable carrier state. This retires the
/// `Option<FQSymbol>` conflation on `MonoExpr::Var.resolved_target`, where
/// `None` meant both "local by design" (legal) and "unresolved by producer
/// bug" (the S113 check-gate-leak class) and the backend disambiguated by
/// convention (`variables` consult, hard-error on double miss). The
/// phase-boundary completeness gate is the constructor itself — a sweep is a
/// migration aid, never the mechanism.
///
/// **NOT `#[non_exhaustive]`** — deliberately. The closed sum IS the contract
/// (the same exception class as the ownership mode vocabulary, types
/// `CLAUDE.md` §Public-surface mechanics): a variant addition MUST break every
/// consumer match at compile time; a `_ =>` arm here would re-smuggle the
/// ambiguous default this type exists to kill.
///
/// **Dormant (S114 Phase 3, produces-but-unused).** The vocabulary lands ahead
/// of its wiring; the `MonoExpr::{Var,Apply}` field flip
/// (`resolved_target: Option<FQSymbol>` → `resolution: VarRef` /
/// `dispatch: ApplyRef`), the `MethodResolutions` sidecar split, and the
/// `CACHE_SCHEMA_VERSION` 21→22 bump land as ONE coordinated Phase-5 carrier
/// wave (`design/arch/typed-resolution-carrier.md` §4–§5).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum VarRef {
    /// A local binding — defn/fn param, `let` name, `match` var-pattern
    /// binding. Carries the BINDER IDENTITY typecheck bound this reference to:
    /// the bound name plus the span of the binding *form* that introduced it
    /// (the `let`/`fn`/`defn`/match-arm node — per-binder spans do not exist
    /// on the AST for params, so the form span is the honest grain).
    /// Frame/slot mapping stays backend-side (the backend's scope stack): this
    /// is a positive resolution verdict, not a storage locator.
    Local { binder: Symbol, binding_span: Span },
    /// A table-resolved reference — the storage FQ ("whichever storage key
    /// HIT" at typecheck's resolution chokepoint; `Resolved.storage_fq()`,
    /// never a written spelling — the 0620 rule). The backend keys ONE fetch
    /// on this and hard-fails on an entry miss.
    Global(FQSymbol),
}

/// How a `MonoExpr::Apply`'s dispatch identity is carried — the Apply-side
/// closed sum (S114, FIXME 0653 prong 3; design:
/// `design/arch/typed-resolution-carrier.md`).
///
/// Deliberately a SEPARATE sum from [`VarRef`]: an `Apply` has a third legal
/// state a `Var` does not — "the identity rides the callee expression" — and
/// sharing one shape would re-smuggle the ambiguous `None` the split exists to
/// kill (the S114 Phase-2 public-API assessment, SPRINT.md §Architecture
/// review (b)). Both variants are POSITIVE verdicts recorded by typecheck;
/// "unresolved" has no constructor here either.
///
/// **NOT `#[non_exhaustive]`** — closed sum, same rationale as [`VarRef`].
///
/// **Dormant (S114 Phase 3, produces-but-unused)** — see [`VarRef`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApplyRef {
    /// A dispatch-leg resolution recorded at this `Apply`'s span (BuiltinFn /
    /// TraitMethod / SigDispatch selection) — the storage FQ of the SELECTED
    /// mangled/mono entry.
    Dispatch(FQSymbol),
    /// No Apply-level dispatch: the identity is carried by the callee
    /// expression itself — its `Var`'s [`VarRef`] (local or global), or a
    /// computed callee value (closure call). Typecheck ASSERTS it looked and
    /// there is no dispatch selection at this node.
    ViaCallee,
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
        /// The resolved STORAGE identity for a table-resolved reference (S110
        /// 0583; `design/arch/backend-keyed-consumer.md` §1.1) — "whichever
        /// storage key HIT" at the typecheck resolution chokepoint, carried
        /// from `MethodResolutions.resolved_targets` (keyed by this `Var`'s
        /// span). `Some` for user-fn / primitive / constructor / effect /
        /// extern references; `None` for a local variable / lambda param (not
        /// table-resolved). The backend keys ONE fetch on this and hard-fails
        /// on a carrier-miss for a table-reference kind (Principle 24) — it
        /// never re-resolves the bare name.
        #[serde(default)]
        resolved_target: Option<FQSymbol>,
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
        /// The resolved STORAGE identity for a dispatch-leg resolution that
        /// resolves at this `Apply` (S110 0583;
        /// `design/arch/backend-keyed-consumer.md` §1.1) — the module-bearing
        /// FQ of the SELECTED mangled/mono entry, carried from
        /// `MethodResolutions.resolved_targets` (keyed by this `Apply`'s span).
        /// `None` when the callee reference itself carries the identity on its
        /// `Var` node. The backend keys ONE fetch on this (Principle 24).
        #[serde(default)]
        resolved_target: Option<FQSymbol>,
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
    ///
    /// # The REQUIRED sidecar parameters (S110 0583 — the §10 unforgettable
    /// template, Principle 18)
    ///
    /// `pattern_ctors` and `resolved_targets` are span-keyed sidecars produced
    /// by typecheck (`MethodResolutions`). A new view-build site cannot forget
    /// to thread the carriers because the signature demands them:
    /// `pattern_ctors` populates `MonoMatchArm.resolved_ctor`;
    /// `resolved_targets` populates `MonoExpr::{Var,Apply}.resolved_target`
    /// (`design/arch/backend-keyed-consumer.md` §1). Pass empty maps only for a
    /// view whose references are structurally resolver-free (all-local bodies).
    pub fn from_expr(
        expr: &Expr,
        pattern_ctors: &HashMap<Span, FQSymbol>,
        resolved_targets: &HashMap<Span, FQSymbol>,
    ) -> Result<MonoExpr, NotConcrete> {
        // The node-level concrete type: every non-erased node MUST carry an
        // `inferred_type`, and it MUST be concrete. An absent annotation is
        // treated as a residual `Var(0)` — the same "this position's type is not
        // representation-determined" failure (an un-annotated codegen node is as
        // illegal as a `Var`-typed one). The erased `Annotate` node is the one
        // node that reads no `ty` of its own.
        match expr {
            Expr::Annotate { expr: inner, .. } => MonoExpr::from_expr(inner, pattern_ctors, resolved_targets),

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
                resolved_target: resolved_targets.get(span).cloned(),
                ty: node_ty(expr)?,
            }),
            Expr::Let { bindings, body, span, .. } => Ok(MonoExpr::Let {
                bindings: bindings
                    .iter()
                    .map(|(n, e)| Ok((n.clone(), MonoExpr::from_expr(e, pattern_ctors, resolved_targets)?)))
                    .collect::<Result<_, NotConcrete>>()?,
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, resolved_targets)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::If { cond, then_branch, else_branch, span, .. } => Ok(MonoExpr::If {
                cond: Box::new(MonoExpr::from_expr(cond, pattern_ctors, resolved_targets)?),
                then_branch: Box::new(MonoExpr::from_expr(then_branch, pattern_ctors, resolved_targets)?),
                else_branch: Box::new(MonoExpr::from_expr(else_branch, pattern_ctors, resolved_targets)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::Lambda { params, body, span, .. } => Ok(MonoExpr::Lambda {
                // Param `TypeExpr` annotations are erased — the concrete param
                // types live in the lambda's `ty` (`ConcreteType::Fn`).
                params: params.iter().map(|(n, _)| n.clone()).collect(),
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, resolved_targets)?),
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
            Expr::Apply { callee, args, span, resolved_call, .. } => Ok(MonoExpr::Apply {
                callee: Box::new(MonoExpr::from_expr(callee, pattern_ctors, resolved_targets)?),
                args: args
                    .iter()
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors, resolved_targets))
                    .collect::<Result<_, NotConcrete>>()?,
                span: *span,
                resolved_call: resolved_call.clone(),
                resolved_target: resolved_targets.get(span).cloned(),
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
                provenance: None,
            }),
            Expr::Match { scrutinee, arms, span, compiler_generated, .. } => Ok(MonoExpr::Match {
                scrutinee: Box::new(MonoExpr::from_expr(scrutinee, pattern_ctors, resolved_targets)?),
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
                            body: MonoExpr::from_expr(&arm.body, pattern_ctors, resolved_targets)?,
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
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors, resolved_targets))
                    .collect::<Result<_, NotConcrete>>()?,
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
            Expr::Trace { modules, body, span, .. } => Ok(MonoExpr::Trace {
                modules: modules.clone(),
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, resolved_targets)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::ParBind { bindings, body, span, .. } => Ok(MonoExpr::ParBind {
                bindings: bindings
                    .iter()
                    .map(|(n, e)| Ok((n.clone(), MonoExpr::from_expr(e, pattern_ctors, resolved_targets)?)))
                    .collect::<Result<_, NotConcrete>>()?,
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, resolved_targets)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::LaunchContinue { launched, continuation, span, .. } => {
                Ok(MonoExpr::LaunchContinue {
                    launched: Box::new(MonoExpr::from_expr(launched, pattern_ctors, resolved_targets)?),
                    continuation: Box::new(MonoExpr::from_expr(continuation, pattern_ctors, resolved_targets)?),
                    span: *span,
                    ty: node_ty(expr)?,
                })
            }
            Expr::ConstrADT { type_name, tag, fields, span, .. } => Ok(MonoExpr::ConstrADT {
                type_name: type_name.clone(),
                tag: *tag,
                fields: fields
                    .iter()
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors, resolved_targets))
                    .collect::<Result<_, NotConcrete>>()?,
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
        }
    }

    /// Build a `MonoExpr` from a body `Expr`, **tolerating** non-concrete node
    /// types (`design/arch/concrete-boundary-type.md` §3.1.1) — the LENIENT
    /// counterpart of the strict, choke-pointed [`MonoExpr::from_expr`].
    ///
    /// Relocated here from the backend (S110 W0.b,
    /// `design/arch/backend-keyed-consumer.md` §5) so view construction has ONE
    /// home in `cranelisp-types` and typecheck becomes the sole mono-view
    /// producer. Same two REQUIRED sidecar parameters as [`MonoExpr::from_expr`]
    /// (Principle 18) — a lenient view carries the same `resolved_target` /
    /// `resolved_ctor` carriers as a strict one.
    ///
    /// **Remaining role.** The fallback for entries that legitimately have NO
    /// strictly-concrete body-AST (signature-driven ctor/accessor synthetic
    /// bodies whose field `Var`s carry the generic ctor template's `Type::Var`;
    /// generic / best-effort templates; REPL `__expr`; non-concretized
    /// macro-clause bodies). Every non-concrete / absent node type is filled
    /// with a placeholder (`ConcreteType::Int`, read ONLY via
    /// `signature_heap_category`, never the deleted `classify(Var)` panic), so
    /// the walk yields a total `MonoExpr`. Byte-identical to the strict builder
    /// on a fully-concrete body (every `node_ty` succeeds; carriers identical).
    pub fn lenient_from_expr(
        expr: &Expr,
        pattern_ctors: &HashMap<Span, FQSymbol>,
        resolved_targets: &HashMap<Span, FQSymbol>,
    ) -> MonoExpr {
        // The node's concrete type: the real one when concrete, else the
        // placeholder (never read for signature-driven bodies).
        let node_ty = |e: &Expr| -> ConcreteType {
            e.inferred_type()
                .and_then(|t| ConcreteType::from_type(t).ok())
                .unwrap_or(ConcreteType::Int)
        };
        let rec = |e: &Expr| MonoExpr::lenient_from_expr(e, pattern_ctors, resolved_targets);

        match expr {
            Expr::Annotate { expr: inner, .. } => rec(inner),
            Expr::IntLit { value, span, .. } => MonoExpr::IntLit { value: *value, span: *span, ty: node_ty(expr) },
            Expr::FloatLit { value, span, .. } => MonoExpr::FloatLit { value: *value, span: *span, ty: node_ty(expr) },
            Expr::BoolLit { value, span, .. } => MonoExpr::BoolLit { value: *value, span: *span, ty: node_ty(expr) },
            Expr::StringLit { value, span, .. } => MonoExpr::StringLit { value: value.clone(), span: *span, ty: node_ty(expr), confined: None, escapes: None, unique_static: None },
            Expr::Var { name, span, resolved_call, .. } => MonoExpr::Var {
                name: name.clone(),
                span: *span,
                resolved_call: resolved_call.clone(),
                resolved_target: resolved_targets.get(span).cloned(),
                ty: node_ty(expr),
            },
            Expr::Let { bindings, body, span, .. } => MonoExpr::Let {
                bindings: bindings.iter().map(|(n, e)| (n.clone(), rec(e))).collect(),
                body: Box::new(rec(body)),
                span: *span,
                ty: node_ty(expr),
            },
            Expr::If { cond, then_branch, else_branch, span, .. } => MonoExpr::If {
                cond: Box::new(rec(cond)),
                then_branch: Box::new(rec(then_branch)),
                else_branch: Box::new(rec(else_branch)),
                span: *span,
                ty: node_ty(expr),
            },
            Expr::Lambda { params, body, span, .. } => MonoExpr::Lambda {
                params: params.iter().map(|(n, _)| n.clone()).collect(),
                body: Box::new(rec(body)),
                span: *span,
                ty: node_ty(expr),
                confined: None,
                escapes: None,
                unique_static: None,
            },
            Expr::Apply { callee, args, span, resolved_call, .. } => MonoExpr::Apply {
                callee: Box::new(rec(callee)),
                args: args.iter().map(&rec).collect(),
                span: *span,
                resolved_call: resolved_call.clone(),
                resolved_target: resolved_targets.get(span).cloned(),
                ty: node_ty(expr),
                confined: None,
                escapes: None,
                provenance: None,
                unique_static: None,
            },
            Expr::Match { scrutinee, arms, span, compiler_generated, .. } => MonoExpr::Match {
                scrutinee: Box::new(rec(scrutinee)),
                arms: arms.iter().map(|arm| {
                    let resolved_ctor = match &arm.pattern {
                        Pattern::Constructor { span: pat_span, .. } => {
                            pattern_ctors.get(pat_span).cloned()
                        }
                        _ => None,
                    };
                    MonoMatchArm {
                        pattern: arm.pattern.clone(),
                        body: rec(&arm.body),
                        span: arm.span,
                        provenance: None,
                        resolved_ctor,
                    }
                }).collect(),
                span: *span,
                compiler_generated: *compiler_generated,
                ty: node_ty(expr),
            },
            Expr::VecLit { elements, span, .. } => MonoExpr::VecLit {
                elements: elements.iter().map(&rec).collect(),
                span: *span,
                ty: node_ty(expr),
                confined: None,
                escapes: None,
                unique_static: None,
            },
            Expr::Trace { modules, body, span, .. } => MonoExpr::Trace {
                modules: modules.clone(),
                body: Box::new(rec(body)),
                span: *span,
                ty: node_ty(expr),
            },
            Expr::ParBind { bindings, body, span, .. } => MonoExpr::ParBind {
                bindings: bindings.iter().map(|(n, e)| (n.clone(), rec(e))).collect(),
                body: Box::new(rec(body)),
                span: *span,
                ty: node_ty(expr),
            },
            Expr::LaunchContinue { launched, continuation, span, .. } => MonoExpr::LaunchContinue {
                launched: Box::new(rec(launched)),
                continuation: Box::new(rec(continuation)),
                span: *span,
                ty: node_ty(expr),
            },
            Expr::ConstrADT { type_name, tag, fields, span, .. } => MonoExpr::ConstrADT {
                type_name: type_name.clone(),
                tag: *tag,
                fields: fields.iter().map(&rec).collect(),
                span: *span,
                ty: node_ty(expr),
                confined: None,
                escapes: None,
                unique_static: None,
            },
        }
    }

    /// Build a `MonoExpr` from a SYNTHETIC, **all-local** body — the sanctioned
    /// entry point for compiler-synthesised bodies whose every reference is a
    /// local **by construction** (FIXME 0685;
    /// `design/arch/typed-resolution-carrier.md` §3.4): the deftype ctor body
    /// (`Expr::ConstrADT` over param `Var`s) and the field-accessor body
    /// (`(match self [(Ctor .. field ..) field])` — `self` param + `field`
    /// match-var), both synthesised in typecheck's `adt.rs` with
    /// [`Span::SYNTHETIC`] on every node. Classifying these `Var`s local is a
    /// POSITIVE verdict, not a silent default masking a table-reference miss.
    ///
    /// Two structural properties keep that distinction airtight (the
    /// distinction the [`VarRef`]/[`ApplyRef`] flip enforces):
    ///
    /// - **No resolution-map parameters.** The all-local license is the
    ///   signature itself — there is no `resolved_targets`/`var_refs` sidecar
    ///   to consult and none to forget, retiring the "pass empty maps for
    ///   all-local bodies" convention. `pattern_ctors` IS still taken: a
    ///   match-arm ctor identity is not a local — synthesis holds it in hand
    ///   and transports it through the sidecar keyed by the (synthetic)
    ///   pattern span, as the accessor body does.
    /// - **Always-on synthetic-span assertion** (tier-3 seam assert,
    ///   `design/arch/safety-invariants.md` §2). Every produced node's span
    ///   must be [`Span::SYNTHETIC`]; a real-span node panics. A real
    ///   (check-run) body routed through this builder would grant its table
    ///   references a silent local verdict — the assert bounds the license by
    ///   a machine-checked property instead of call-site discipline, so
    ///   "unresolved has no constructor" cannot be re-smuggled through this
    ///   door.
    ///
    /// **Dormant interior (S114 Phase 3).** Until the Phase-5 carrier flip
    /// this delegates to [`MonoExpr::lenient_from_expr`] with an empty
    /// resolution sidecar — byte-identical to the pre-0685 adt.rs callsites.
    /// At the flip its interior becomes the all-local MODE of the ONE shared
    /// lenient walk (every `Var` → `VarRef::Local { binder, binding_span:
    /// Span::SYNTHETIC }`, every `Apply` → `ApplyRef::ViaCallee`) — never a
    /// hand-built second node-construction walk
    /// (`design/arch/typed-resolution-carrier.md` §4).
    pub fn synthetic_local_from_expr(
        expr: &Expr,
        pattern_ctors: &HashMap<Span, FQSymbol>,
    ) -> MonoExpr {
        let mono = MonoExpr::lenient_from_expr(expr, pattern_ctors, &HashMap::new());
        assert_all_synthetic(&mono);
        mono
    }
}

/// Tier-3 seam assertion for [`MonoExpr::synthetic_local_from_expr`]: every
/// node of a synthesis body carries [`Span::SYNTHETIC`]. A real-span node here
/// means a check-run body reached the all-local builder — its table references
/// would be silently classified local, the exact ambiguity the
/// [`VarRef`]/[`ApplyRef`] flip exists to kill — an in-process producer-bug
/// breach, asserted always-on (`design/arch/safety-invariants.md` §2 tier 3;
/// the walked bodies are tiny per-ADT synthesis artefacts, so the check is
/// free).
fn assert_all_synthetic(m: &MonoExpr) {
    assert!(
        m.span() == Span::SYNTHETIC,
        "synthetic_local_from_expr: non-SYNTHETIC span {:?} on a synthesis-body node — \
         a real (check-run) body must go through from_expr/lenient_from_expr, never the \
         all-local builder (FIXME 0685; design/arch/typed-resolution-carrier.md §3.4)",
        m.span()
    );
    match m {
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::StringLit { .. }
        | MonoExpr::Var { .. } => {}
        MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
            for (_, e) in bindings {
                assert_all_synthetic(e);
            }
            assert_all_synthetic(body);
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            assert_all_synthetic(cond);
            assert_all_synthetic(then_branch);
            assert_all_synthetic(else_branch);
        }
        MonoExpr::Lambda { body, .. } | MonoExpr::Trace { body, .. } => assert_all_synthetic(body),
        MonoExpr::Apply { callee, args, .. } => {
            assert_all_synthetic(callee);
            for a in args {
                assert_all_synthetic(a);
            }
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            assert_all_synthetic(scrutinee);
            for arm in arms {
                assert_all_synthetic(&arm.body);
            }
        }
        MonoExpr::VecLit { elements, .. } => {
            for e in elements {
                assert_all_synthetic(e);
            }
        }
        MonoExpr::LaunchContinue { launched, continuation, .. } => {
            assert_all_synthetic(launched);
            assert_all_synthetic(continuation);
        }
        MonoExpr::ConstrADT { fields, .. } => {
            for f in fields {
                assert_all_synthetic(f);
            }
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
