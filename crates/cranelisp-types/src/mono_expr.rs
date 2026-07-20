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
/// **Live (S114 Phase 5 carrier flip).** Carried non-optionally on
/// [`MonoExpr::Var`]`.resolution`; produced totally by typecheck into
/// `MethodResolutions.var_refs` (keyed by `Var` span); transported by
/// [`MonoExpr::from_expr`] / [`MonoExpr::lenient_from_expr`], whose miss
/// behaviour is the phase-boundary gate ([`ViewBuildError::Unresolved`] /
/// the tier-3 seam assert). Serde-visible on the persisted `codegen_view`
/// (`CACHE_SCHEMA_VERSION` 22 window).
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
/// **Live (S114 Phase 5 carrier flip)** — carried non-optionally on
/// [`MonoExpr::Apply`]`.dispatch`; produced totally into
/// `MethodResolutions.apply_refs` (keyed by `Apply` span); see [`VarRef`].
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

/// [`MonoExpr::from_expr`]'s failure sum (S114 carrier flip;
/// `design/arch/typed-resolution-carrier.md` §4) — the strict view-build gate
/// distinguishes TYPE incompleteness from RESOLUTION incompleteness, because
/// the two route differently at `build_concrete_codegen_view`:
///
/// - [`ViewBuildError::NotConcrete`] — a node's type is absent / non-concrete
///   (the pre-flip `NotConcrete` failure, re-wrapped). Legitimate for
///   multi-sig `f$Var` variants and forward-reference result vars; the caller
///   MAY fall back to [`MonoExpr::lenient_from_expr`].
/// - [`ViewBuildError::Unresolved`] — a real-span `Var`/`Apply` has NO
///   `var_refs`/`apply_refs` verdict. This is the phase-boundary gate the
///   carrier exists for: a reference typecheck could not classify surfaces
///   HERE as a **located typecheck-phase error** — it MUST NOT be swallowed
///   into the lenient fallback (doing so re-opens the check-gate-leak class
///   one level up; the lenient walk seam-asserts on the same miss).
///
/// **NOT `#[non_exhaustive]`** — same closed-sum exception class as
/// [`VarRef`]/[`ApplyRef`] (types `CLAUDE.md` §Public-surface mechanics): the
/// NotConcrete-vs-Unresolved routing at the fallback seam is the load-bearing
/// consumer match, and a `_ =>` arm there would silently route a future
/// variant into the wrong leg.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewBuildError {
    /// Type incompleteness at a node — the caller may lenient-fall-back.
    NotConcrete(NotConcrete),
    /// Resolution incompleteness: a real-span reference with no typed verdict
    /// in the sidecar maps. `span`/`name` locate the reference (for an
    /// `Apply`, `name` is the callee head — the callee `Var`'s name when
    /// there is one). A located typecheck-phase error, never a fallback.
    Unresolved { span: Span, name: Symbol },
}

impl From<NotConcrete> for ViewBuildError {
    fn from(nc: NotConcrete) -> Self {
        ViewBuildError::NotConcrete(nc)
    }
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
        /// How this reference was resolved — the typed, NON-OPTIONAL carrier
        /// (S114 flip of the S110 `resolved_target: Option<FQSymbol>`;
        /// `design/arch/typed-resolution-carrier.md` §4). [`VarRef::Local`]
        /// carries the binder identity (backend: scope-stack read, hard
        /// invariant failure on a miss); [`VarRef::Global`] carries the
        /// storage FQ — "whichever storage key HIT" at typecheck's resolution
        /// chokepoint (`Resolved.storage_fq()`, the 0620 rule) — on which the
        /// backend keys ONE `entry_at` fetch (Principle 24). No
        /// `#[serde(default)]`: absence is unrepresentable — a persisted view
        /// missing the field is schema-invalid, not conservatively defaulted.
        resolution: VarRef,
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
        /// How this call's dispatch identity is carried — the typed,
        /// NON-OPTIONAL carrier (S114 flip of the S110
        /// `resolved_target: Option<FQSymbol>`;
        /// `design/arch/typed-resolution-carrier.md` §4).
        /// [`ApplyRef::Dispatch`] carries the storage FQ of the SELECTED
        /// mangled/mono entry (the backend keys ONE fetch on it, Principle
        /// 24); [`ApplyRef::ViaCallee`] is the POSITIVE no-Apply-level-dispatch
        /// verdict — the identity rides the callee expression (its `Var`'s
        /// [`VarRef`], or a computed closure value). No `#[serde(default)]`:
        /// absence is unrepresentable.
        dispatch: ApplyRef,
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

    /// The ONLY way to obtain a strict `MonoExpr` from an [`Expr`]. Walks an
    /// `inferred_type`-annotated `Expr`, converting each node's `inferred_type`
    /// via [`ConcreteType::from_type`], and **fails at the first node whose
    /// `inferred_type` is absent or non-concrete** (returning
    /// [`ViewBuildError::NotConcrete`]) **or whose resolution verdict is
    /// missing** (returning [`ViewBuildError::Unresolved`] — see "The
    /// view-build gate" below).
    ///
    /// The `NotConcrete` failure IS the unified ambiguity / could-not-monomorphise error
    /// (`design/arch/concrete-boundary-type.md` §1.3 / §2.6): a residual `Var` in
    /// a codegen-reaching position means no root pins it. The `Annotate` node is
    /// **erased** — it collapses to its inner `MonoExpr`. `Lambda` param `TypeExpr`
    /// annotations are **erased** — the concrete param types ride in the lambda's
    /// `ty` (`ConcreteType::Fn`).
    ///
    /// Non-destructive over the source `Expr`.
    ///
    /// # The REQUIRED sidecar parameters (S110 0583 template, Principle 18;
    /// typed since the S114 carrier flip)
    ///
    /// `pattern_ctors`, `var_refs`, and `apply_refs` are span-keyed sidecars
    /// produced by typecheck (`MethodResolutions`). A new view-build site
    /// cannot forget to thread the carriers because the signature demands
    /// them: `pattern_ctors` populates `MonoMatchArm.resolved_ctor`;
    /// `var_refs` populates `MonoExpr::Var.resolution`; `apply_refs`
    /// populates `MonoExpr::Apply.dispatch`. The maps are TOTAL over the
    /// paired check-run's real-span references (the producer contract,
    /// `design/arch/typed-resolution-carrier.md` §3) — the former "pass empty
    /// maps for all-local bodies" license is RETIRED (all-local bodies carry
    /// `VarRef::Local` entries; synthetic bodies go through
    /// [`MonoExpr::synthetic_local_from_expr`]).
    ///
    /// # The view-build gate (miss behaviour)
    ///
    /// - A real-span `Var`/`Apply` with no map entry fails as
    ///   [`ViewBuildError::Unresolved`] — the LOCATED typecheck-phase error
    ///   the carrier exists for.
    /// - The resolution verdict is read BEFORE the node's type: a node that
    ///   is both unresolved and non-concrete reports `Unresolved`, so a
    ///   resolution miss can never slip into the caller's `NotConcrete`
    ///   lenient fallback (where the same miss would seam-assert).
    /// - A [`Span::SYNTHETIC`] node with no map entry takes the all-local
    ///   verdict (`VarRef::Local { binding_span: Span::SYNTHETIC }` /
    ///   [`ApplyRef::ViaCallee`]): synthetic nodes are structurally OUTSIDE
    ///   span-keyed transport (one shared key — the maps cannot address them
    ///   individually; `typed-resolution-carrier.md` §3.4), and every
    ///   synthetic population is compiler-synthesised locals. A map entry
    ///   under the SYNTHETIC key (e.g. a synthesis-transported
    ///   `pattern_ctors` identity) still wins over the carve-out.
    pub fn from_expr(
        expr: &Expr,
        pattern_ctors: &HashMap<Span, FQSymbol>,
        var_refs: &HashMap<Span, VarRef>,
        apply_refs: &HashMap<Span, ApplyRef>,
    ) -> Result<MonoExpr, ViewBuildError> {
        // The node-level concrete type: every non-erased node MUST carry an
        // `inferred_type`, and it MUST be concrete. An absent annotation is
        // treated as a residual `Var(0)` — the same "this position's type is not
        // representation-determined" failure (an un-annotated codegen node is as
        // illegal as a `Var`-typed one). The erased `Annotate` node is the one
        // node that reads no `ty` of its own.
        match expr {
            Expr::Annotate { expr: inner, .. } => MonoExpr::from_expr(inner, pattern_ctors, var_refs, apply_refs),

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
            Expr::Var { name, span, resolved_call, .. } => {
                // Verdict BEFORE type: an unresolved reference must surface as
                // the located `Unresolved` gate error, never leak to the
                // caller's `NotConcrete` lenient fallback.
                let resolution = var_verdict(name, *span, var_refs).ok_or(
                    ViewBuildError::Unresolved { span: *span, name: name.clone() },
                )?;
                Ok(MonoExpr::Var {
                    name: name.clone(),
                    span: *span,
                    resolved_call: resolved_call.clone(),
                    resolution,
                    ty: node_ty(expr)?,
                })
            }
            Expr::Let { bindings, body, span, .. } => Ok(MonoExpr::Let {
                bindings: bindings
                    .iter()
                    .map(|(n, e)| Ok((n.clone(), MonoExpr::from_expr(e, pattern_ctors, var_refs, apply_refs)?)))
                    .collect::<Result<_, ViewBuildError>>()?,
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, var_refs, apply_refs)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::If { cond, then_branch, else_branch, span, .. } => Ok(MonoExpr::If {
                cond: Box::new(MonoExpr::from_expr(cond, pattern_ctors, var_refs, apply_refs)?),
                then_branch: Box::new(MonoExpr::from_expr(then_branch, pattern_ctors, var_refs, apply_refs)?),
                else_branch: Box::new(MonoExpr::from_expr(else_branch, pattern_ctors, var_refs, apply_refs)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::Lambda { params, body, span, .. } => Ok(MonoExpr::Lambda {
                // Param `TypeExpr` annotations are erased — the concrete param
                // types live in the lambda's `ty` (`ConcreteType::Fn`).
                params: params.iter().map(|(n, _)| n.clone()).collect(),
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, var_refs, apply_refs)?),
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
            Expr::Apply { callee, args, span, resolved_call, .. } => {
                // Verdict BEFORE walking children/type — same gate-first rule
                // as the `Var` arm; the error names the callee head.
                let dispatch = apply_verdict(*span, apply_refs).ok_or_else(|| {
                    ViewBuildError::Unresolved { span: *span, name: apply_head_name(callee) }
                })?;
                Ok(MonoExpr::Apply {
                    callee: Box::new(MonoExpr::from_expr(callee, pattern_ctors, var_refs, apply_refs)?),
                    args: args
                        .iter()
                        .map(|e| MonoExpr::from_expr(e, pattern_ctors, var_refs, apply_refs))
                        .collect::<Result<_, ViewBuildError>>()?,
                    span: *span,
                    resolved_call: resolved_call.clone(),
                    dispatch,
                    ty: node_ty(expr)?,
                    escapes: None,
                    confined: None,
                    unique_static: None,
                    provenance: None,
                })
            }
            Expr::Match { scrutinee, arms, span, compiler_generated, .. } => Ok(MonoExpr::Match {
                scrutinee: Box::new(MonoExpr::from_expr(scrutinee, pattern_ctors, var_refs, apply_refs)?),
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
                            body: MonoExpr::from_expr(&arm.body, pattern_ctors, var_refs, apply_refs)?,
                            span: arm.span,
                            provenance: None,
                            resolved_ctor,
                        })
                    })
                    .collect::<Result<_, ViewBuildError>>()?,
                span: *span,
                compiler_generated: *compiler_generated,
                ty: node_ty(expr)?,
            }),
            Expr::VecLit { elements, span, .. } => Ok(MonoExpr::VecLit {
                elements: elements
                    .iter()
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors, var_refs, apply_refs))
                    .collect::<Result<_, ViewBuildError>>()?,
                span: *span,
                ty: node_ty(expr)?,
                escapes: None,
                confined: None,
                unique_static: None,
            }),
            Expr::Trace { modules, body, span, .. } => Ok(MonoExpr::Trace {
                modules: modules.clone(),
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, var_refs, apply_refs)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::ParBind { bindings, body, span, .. } => Ok(MonoExpr::ParBind {
                bindings: bindings
                    .iter()
                    .map(|(n, e)| Ok((n.clone(), MonoExpr::from_expr(e, pattern_ctors, var_refs, apply_refs)?)))
                    .collect::<Result<_, ViewBuildError>>()?,
                body: Box::new(MonoExpr::from_expr(body, pattern_ctors, var_refs, apply_refs)?),
                span: *span,
                ty: node_ty(expr)?,
            }),
            Expr::LaunchContinue { launched, continuation, span, .. } => {
                Ok(MonoExpr::LaunchContinue {
                    launched: Box::new(MonoExpr::from_expr(launched, pattern_ctors, var_refs, apply_refs)?),
                    continuation: Box::new(MonoExpr::from_expr(continuation, pattern_ctors, var_refs, apply_refs)?),
                    span: *span,
                    ty: node_ty(expr)?,
                })
            }
            Expr::ConstrADT { type_name, tag, fields, span, .. } => Ok(MonoExpr::ConstrADT {
                type_name: type_name.clone(),
                tag: *tag,
                fields: fields
                    .iter()
                    .map(|e| MonoExpr::from_expr(e, pattern_ctors, var_refs, apply_refs))
                    .collect::<Result<_, ViewBuildError>>()?,
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
    /// producer. Same REQUIRED sidecar parameters as [`MonoExpr::from_expr`]
    /// (Principle 18) — a lenient view carries the same typed
    /// `resolution`/`dispatch`/`resolved_ctor` carriers as a strict one.
    ///
    /// **Tolerance is for TYPES only** (S114 carrier flip;
    /// `design/arch/typed-resolution-carrier.md` §3.5): resolution verdicts
    /// come from the same paired check-run and are equally TOTAL. A real-span
    /// `Var`/`Apply` with no `var_refs`/`apply_refs` entry is an in-process
    /// producer-bug breach and PANICS via an always-on tier-3 seam assertion
    /// (`design/arch/safety-invariants.md` §2) — it is never silently
    /// manufactured into a `Local`/`ViaCallee` verdict (the census closed via
    /// FIXME 0685: the only all-local population is the synthetic bodies,
    /// which take [`MonoExpr::synthetic_local_from_expr`], so this walk's
    /// real-span population has NO legitimate miss). A [`Span::SYNTHETIC`]
    /// node with no entry takes the all-local verdict — the same carve-out as
    /// the strict walk (synthetic nodes are structurally outside span-keyed
    /// transport).
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
        var_refs: &HashMap<Span, VarRef>,
        apply_refs: &HashMap<Span, ApplyRef>,
    ) -> MonoExpr {
        // The node's concrete type: the real one when concrete, else the
        // placeholder (never read for signature-driven bodies).
        let node_ty = |e: &Expr| -> ConcreteType {
            e.inferred_type()
                .and_then(|t| ConcreteType::from_type(t).ok())
                .unwrap_or(ConcreteType::Int)
        };
        let rec = |e: &Expr| MonoExpr::lenient_from_expr(e, pattern_ctors, var_refs, apply_refs);

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
                resolution: var_verdict(name, *span, var_refs).unwrap_or_else(|| {
                    // Always-on tier-3 seam assert (safety-invariants.md §2):
                    // lenient tolerance is for TYPES only — a real-span
                    // resolution miss is a producer bug, never a silent Local.
                    panic!(
                        "lenient_from_expr: no VarRef verdict for real-span Var `{name}` at \
                         {span:?} — resolution verdicts are TOTAL over the paired check-run \
                         (in-process producer bug; design/arch/typed-resolution-carrier.md §3.5)"
                    )
                }),
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
                dispatch: apply_verdict(*span, apply_refs).unwrap_or_else(|| {
                    // Always-on tier-3 seam assert — the Apply sibling of the
                    // Var-arm assert above.
                    panic!(
                        "lenient_from_expr: no ApplyRef verdict for real-span Apply of \
                         `{}` at {span:?} — resolution verdicts are TOTAL over the paired \
                         check-run (in-process producer bug; \
                         design/arch/typed-resolution-carrier.md §3.5)",
                        apply_head_name(callee)
                    )
                }),
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
    ///   signature itself — there is no `var_refs`/`apply_refs` sidecar
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
    /// **All-local mode of the ONE shared walk (S114 Phase 5 flip).** The
    /// interior delegates to [`MonoExpr::lenient_from_expr`] with empty
    /// resolution maps: under the shared walk's [`Span::SYNTHETIC`] carve-out
    /// every (asserted-synthetic) `Var` takes `VarRef::Local { binder,
    /// binding_span: Span::SYNTHETIC }` and every `Apply` takes
    /// [`ApplyRef::ViaCallee`] — the all-local mode is the span-directed
    /// behaviour of the one walk, never a hand-built second
    /// node-construction walk (`design/arch/typed-resolution-carrier.md` §4).
    /// The synthetic-span assert is what bounds the license: a real-span node
    /// in the body panics here (and the shared walk's real-span seam assert
    /// would refuse it a silent local verdict regardless).
    pub fn synthetic_local_from_expr(
        expr: &Expr,
        pattern_ctors: &HashMap<Span, FQSymbol>,
    ) -> MonoExpr {
        let mono =
            MonoExpr::lenient_from_expr(expr, pattern_ctors, &HashMap::new(), &HashMap::new());
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

/// The ONE resolution-verdict rule for a `Var` node, shared by the strict and
/// lenient walks (S114 carrier flip): a map hit carries typecheck's verdict; a
/// [`Span::SYNTHETIC`] miss takes the all-local verdict (synthetic nodes are
/// structurally outside span-keyed transport — `typed-resolution-carrier.md`
/// §3.4); a real-span miss is `None` — the caller decides the failure shape
/// ([`ViewBuildError::Unresolved`] strict; tier-3 seam panic lenient).
fn var_verdict(name: &Symbol, span: Span, var_refs: &HashMap<Span, VarRef>) -> Option<VarRef> {
    match var_refs.get(&span) {
        Some(v) => Some(v.clone()),
        None if span == Span::SYNTHETIC => Some(VarRef::Local {
            binder: name.clone(),
            binding_span: Span::SYNTHETIC,
        }),
        None => None,
    }
}

/// The `Apply` sibling of [`var_verdict`] — same three-way rule; the synthetic
/// all-local verdict is [`ApplyRef::ViaCallee`].
fn apply_verdict(span: Span, apply_refs: &HashMap<Span, ApplyRef>) -> Option<ApplyRef> {
    match apply_refs.get(&span) {
        Some(a) => Some(a.clone()),
        None if span == Span::SYNTHETIC => Some(ApplyRef::ViaCallee),
        None => None,
    }
}

/// The callee head name for `Apply` diagnostics: the callee `Var`'s name when
/// there is one (through erased `Annotate` layers), else a marker for a
/// computed callee.
fn apply_head_name(callee: &Expr) -> Symbol {
    match callee {
        Expr::Var { name, .. } => name.clone(),
        Expr::Annotate { expr, .. } => apply_head_name(expr),
        _ => Symbol::from("<computed callee>"),
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
