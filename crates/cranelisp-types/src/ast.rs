use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::{
    FQTypeName, ResolvedCall, Span, Symbol, SymbolRef, TraitName, TraitRef, Type, TypeName, TypeRef,
};

// --- Type Expressions ---

/// Type expression in annotations and trait signatures.
///
/// Syntactic-stage shape. The `Named` / `Applied` variants carry a `TypeRef`
/// (S69 Submission 27) — i.e. `(Option<ModuleFullPath>, TypeName)` — capturing
/// **as-written** qualification structurally. At AST construction the optional
/// module is whatever the user wrote (`Int` → `module: None`; `option/Option`
/// → `module: Some("option")`; `core.option/Option` → full path). Typecheck
/// resolves the optional module via the import graph at the `TypeName →
/// FQTypeName` lift site (`check_form` consulting current scope + imports),
/// producing `Type::ADT(FQTypeName, …)` at the resolved-stage boundary per
/// Decision 47.
///
/// The cascade from bare `TypeName` payloads to `TypeRef` payloads (S69
/// Submission 27) sharpens Decision 47's producer/consumer split: the
/// syntactic stage no longer carries "bare name slips through" — it carries
/// the qualification structurally, and typecheck resolves it. The `head_ref`
/// helper provides a uniform accessor for the head reference on `Named` and
/// `Applied`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeExpr {
    /// Named type with as-written qualification: `Int`, `Bool`, `option/Option`
    Named(TypeRef),
    /// Self type in trait methods: `Self`
    SelfType,
    /// Function type: `(Fn [Int Int] Bool)`
    FnType(Vec<TypeExpr>, Box<TypeExpr>),
    /// Type variable: `:a`, `:b`
    TypeVar(Symbol),
    /// Applied type constructor with as-written head qualification:
    /// `(Option Int)`, `(option/Option :a)`, `(List :a)`
    Applied(TypeRef, Vec<TypeExpr>),
    /// An unspecified type satisfying these trait bounds — a constrained type
    /// variable's annotation, carrying the run of stacked `:Trait` annotations
    /// on a single binder (`[:Eq :Display a]`, spec §3.9.2). Mutually exclusive
    /// with a concrete-type annotation in the same slot: a param annotation is
    /// *either* a concrete type (the other `TypeExpr` variants) *or* a set of
    /// trait bounds, never both. Holding one-of-{type, bounds} in the single
    /// `Option<TypeExpr>` param slot captures that exclusion by construction
    /// (FIXME 0346 ruled option (a) over a sidecar `{ty, bounds}` struct, which
    /// would model a state — both specified — that cannot exist). The
    /// `TraitRef`s carry as-written qualification (`:fmt/Display`); typecheck
    /// resolves them and accumulates the bounds onto the type variable's
    /// `Scheme.constraints` (spec §3.9.3 try-type-then-trait).
    Bounds(Vec<TraitRef>),
}

impl TypeExpr {
    /// Returns the head `TypeRef` for `Named` and `Applied` variants — the
    /// reference the typecheck resolver must lift to `FQTypeName`. Returns
    /// `None` for `TypeVar`, `SelfType`, and `FnType` (which have no single
    /// head identifier — `TypeVar` is a free name, `SelfType` is a marker
    /// resolved against the enclosing impl target, and `FnType` is
    /// structurally compound).
    pub fn head_ref(&self) -> Option<&TypeRef> {
        match self {
            TypeExpr::Named(r) | TypeExpr::Applied(r, _) => Some(r),
            _ => None,
        }
    }
}

// --- Patterns ---

/// Pattern in a match expression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    /// Constructor pattern: `(Some x)`, `None`, `(Cons h t)`,
    /// `(option/Some x)`, `(core.option/Some x)`.
    ///
    /// `name: SymbolRef` carries **as-written** qualification at the
    /// syntactic stage — the same shape that `TraitRef` and `TypeRef`
    /// use for trait and type references. The unqualified case
    /// (`module: None`) is the common one; explicit qualification is
    /// captured structurally rather than letting a "bare name slip
    /// through" the AST.
    ///
    /// **Current parser status (S70):** the frontend `build_pattern`
    /// preserves the source string verbatim — `(option/Some x)` lands
    /// in `SymbolRef { module: None, name: "option/Some" }`, NOT
    /// `module: Some("option"), name: "Some"`. The structural split at
    /// `/` is a follow-on lift tracked under the FQTypeName /
    /// qualified-pattern work (spec §6.2 EBNF currently treats
    /// `symbol-with-slashes` as a single `symbol` token; the parser
    /// follows). The `SymbolRef` shape on this variant is the
    /// **destination** for that lift — the type slot is ready before
    /// the parser populates it. Until the lift lands, qualified
    /// pattern names round-trip through the unqualified arm of the
    /// `SymbolRef` enum.
    ///
    /// The resolved-stage `FQSymbol` for the constructor lives in a
    /// **sidecar** (`MethodResolutions.pattern_ctors`, keyed by `span`)
    /// rather than as an annotation field on this variant — mirrors the
    /// producer/consumer split for `TraitRef`/`TypeRef` per Decision 47
    /// (FQ binding at resolved-stage boundaries). Pattern matching is
    /// consumed *post-typecheck* by backend codegen — that IS a
    /// resolved-stage boundary; the sidecar carries the FQ resolution
    /// without inflating the syntactic-stage AST shape. See
    /// `design/arch/bounded-contexts.md` §7 "FQTypeName binding" and
    /// `design/arch/cranelisp-types-solidness-sweep-s70.md` finding #4
    /// for the design grounding.
    ///
    /// Ring 0: nullary constructors only (empty bindings).
    Constructor {
        name: SymbolRef,
        bindings: Vec<Symbol>,
        span: Span,
    },
    /// Wildcard: `_`
    Wildcard { span: Span },
    /// Variable binding: `x` (binds the scrutinee to a name)
    Var { name: Symbol, span: Span },
}

/// One arm of a match expression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}

// --- Expressions ---

/// Expression AST node. Every variant carries a Span.
///
/// Spec traceability:
///   IntLit, FloatLit, BoolLit, StringLit -- spec 4.1 (Literals)
///   Var -- spec 4.2 (Variable Reference)
///   Let -- spec 4.3 (Let Expression)
///   If -- spec 4.4 (If Expression)
///   Lambda -- spec 4.5 (Lambda Expression)
///   Apply -- spec 4.6 (Function Application)
///   Match -- spec 4.8 (Match Expression)
///   Annotate -- spec 4.9 (Type Annotation)
///   VecLit -- spec 4.10 (Vec Literal)
///   Trace -- spec 12 (Runtime Model, implementation extension)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
    // --- Ring 0 exercised ---
    IntLit {
        value: i64,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    FloatLit {
        value: f64,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    BoolLit {
        value: bool,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Var {
        name: Symbol,
        span: Span,
        /// How a value-position trait-method reference was resolved by the
        /// typechecker. `None` for ordinary variable references and before
        /// typecheck; `Some` only when this `Var` names a trait method used
        /// in value position (e.g. `(let [f =] (f x y))` — the `=` binding),
        /// where the typechecker resolves the method against the Var's
        /// `inferred_type` and records the dispatch target here so backend
        /// can emit a dispatch-wrapper closure without re-deriving trait
        /// knowledge (Principle 16; Decision 43 — backend has no trait
        /// knowledge). Mirrors `Expr::Apply.resolved_call`: this is the
        /// value-position carrier the side map (overlaid onto `Apply` nodes
        /// only) cannot reach. Boxed to avoid bloating the `Expr` enum.
        #[serde(default)]
        resolved_call: Option<Box<ResolvedCall>>,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Let {
        bindings: Vec<(Symbol, Expr)>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    /// Lambda expression — `(fn [param ...] body)` (spec §4.5).
    ///
    /// Per spec §2.3.5 `fn_expr` the parameter list uses the same syntax as
    /// `defn` (spec §2.5 `annotated_param = annotation SYMBOL | SYMBOL`) —
    /// each parameter carries its own optional `:Type` annotation
    /// independently. The fused tuple `params: Vec<(Symbol, Option<TypeExpr>)>`
    /// is the structural enforcement of that invariant per Principle 18
    /// (replaces the prior parallel-vec `params: Vec<Symbol>` +
    /// `param_annotations: Vec<Option<TypeExpr>>` layout, whose `len()`
    /// lockstep invariant was unenforced). Mirrors `DefnVariant`'s shape per
    /// Principle 7 (single source of truth — the same semantic concept has
    /// one structural form).
    Lambda {
        params: Vec<(Symbol, Option<TypeExpr>)>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Apply {
        callee: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
        /// How this call was resolved by the typechecker.
        /// None before typecheck; Some after body checking.
        /// Boxed to avoid bloating the Expr enum (see design/typecheck/ast-annotation.md §4.3).
        #[serde(default)]
        resolved_call: Option<Box<ResolvedCall>>,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        span: Span,
        /// true for compiler-generated match (e.g. from macro expansion)
        compiler_generated: bool,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Annotate {
        annotation: TypeExpr,
        expr: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },

    // --- Defined, deferred to Ring 1 ---
    StringLit {
        value: String,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    VecLit {
        elements: Vec<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },

    // --- Defined, deferred to Ring 4 ---
    Trace {
        modules: Vec<Symbol>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    /// Parallel bind chain: produced by the bind! independence analysis pass.
    /// Semantically identical to a sequential `Let` for type-checking purposes,
    /// but codegen emits parallel IO dispatch via `IO_TAG_PAR`.
    /// spec: §10.12 (Automatic IO Scheduling)
    ParBind {
        bindings: Vec<(Symbol, Expr)>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    /// Launch-and-continue: produced by the same bind! independence analysis
    /// pass that emits [`Expr::ParBind`]. Marks an eligible *detached* effect —
    /// one whose result is discarded AND whose resource tokens are disjoint from
    /// the continuation's effects (spec §10.12.7) — so the backend lowers the
    /// `launched` sub-tree to a detached supervised strand (the `IO_TAG_LAUNCH`
    /// runtime node) and proceeds with the `continuation` without awaiting it.
    ///
    /// Semantically this is a sequential `Bind(launched, λ_. continuation)` for
    /// type-checking purposes: `launched` is an effect whose value is discarded
    /// and `continuation` produces this node's result (the node's
    /// `inferred_type` is the continuation's type). Codegen, however, emits the
    /// detached-strand dispatch rather than an ordinary `Bind` — exactly the
    /// `ParBind`→`IO_TAG_PAR` precedent.
    ///
    /// A **dedicated variant** (over extending `ParBind` with a `detached`
    /// discriminator) keeps structured-join (`ParBind`) and detached
    /// (`LaunchContinue`) representationally distinct per Principle 20: the
    /// backend's marker match selects the runtime node by the variant itself,
    /// not by reading a flag, so a structured-join site can never be
    /// mis-lowered as detached (or vice versa) by construction.
    ///
    /// spec: §10.12.7 (Launch-and-continue) — design: `design/backend/io-trampoline.md §15`,
    /// `design/int/bind-chain-analysis.md`.
    LaunchContinue {
        /// The detached effect sub-tree — lowered to a supervised strand and
        /// not awaited by the continuation. Its result is discarded.
        launched: Box<Expr>,
        /// The continuation that runs without awaiting `launched`. Produces this
        /// node's value.
        continuation: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    /// ADT construction — a language-level operation. Synthesised by the
    /// deftype expander as the body of every constructor's Defn (see
    /// `Expr` rustdoc in `ast.rs` and `bounded-contexts.md` §7
    /// §"DefKind" for the ctor-as-Def shape). Not user syntax; users write
    /// `(Some 42)` (an `Apply` against the constructor's name), which resolves
    /// to a Def whose body is this node.
    ///
    /// Backend lowers this however it chooses (inline alloc+tag+stores, libcall
    /// to a runtime helper, or hybrid). Backend choice; not visible to typecheck
    /// or to downstream readers of the AST.
    ConstrADT {
        type_name: FQTypeName,    // owning ADT (e.g., core.option/Option)
        tag: usize,                // discriminant within the ADT
        fields: Vec<Expr>,         // field value expressions
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
}

impl Expr {
    /// Constructs an `Expr::Var` with both annotation channels defaulted to
    /// `None` (`resolved_call` and `inferred_type`). This is the canonical
    /// construction shape — a bare variable reference at the syntactic stage,
    /// before typecheck overlays either annotation. Construction sites that
    /// build a `Var` from a `name` + `span` switch to this constructor so the
    /// annotation fields are not spelled at every call site (and so a future
    /// added annotation field defaults here, not at N call sites). Typecheck
    /// sets `resolved_call` / `inferred_type` post-construction via the
    /// annotate pass; tests and passes that need a non-default annotation use
    /// the struct literal directly.
    pub fn var(name: Symbol, span: Span) -> Expr {
        Expr::Var { name, span, resolved_call: None, inferred_type: None }
    }

    /// Returns the span of this expression.
    pub fn span(&self) -> Span {
        match self {
            Expr::IntLit { span, .. }
            | Expr::FloatLit { span, .. }
            | Expr::BoolLit { span, .. }
            | Expr::StringLit { span, .. }
            | Expr::Var { span, .. }
            | Expr::Let { span, .. }
            | Expr::If { span, .. }
            | Expr::Lambda { span, .. }
            | Expr::Apply { span, .. }
            | Expr::Match { span, .. }
            | Expr::VecLit { span, .. }
            | Expr::Annotate { span, .. }
            | Expr::Trace { span, .. }
            | Expr::ParBind { span, .. }
            | Expr::LaunchContinue { span, .. }
            | Expr::ConstrADT { span, .. } => *span,
        }
    }

    /// Returns the inferred type annotation, if set by typecheck.
    pub fn inferred_type(&self) -> Option<&Type> {
        match self {
            Expr::IntLit { inferred_type, .. }
            | Expr::FloatLit { inferred_type, .. }
            | Expr::BoolLit { inferred_type, .. }
            | Expr::StringLit { inferred_type, .. }
            | Expr::Var { inferred_type, .. }
            | Expr::Let { inferred_type, .. }
            | Expr::If { inferred_type, .. }
            | Expr::Lambda { inferred_type, .. }
            | Expr::Apply { inferred_type, .. }
            | Expr::Match { inferred_type, .. }
            | Expr::VecLit { inferred_type, .. }
            | Expr::Annotate { inferred_type, .. }
            | Expr::Trace { inferred_type, .. }
            | Expr::ParBind { inferred_type, .. }
            | Expr::LaunchContinue { inferred_type, .. }
            | Expr::ConstrADT { inferred_type, .. } => inferred_type.as_deref(),
        }
    }

    /// Sets the inferred type annotation on this expression node.
    pub fn set_inferred_type(&mut self, ty: Option<Box<Type>>) {
        match self {
            Expr::IntLit { inferred_type, .. }
            | Expr::FloatLit { inferred_type, .. }
            | Expr::BoolLit { inferred_type, .. }
            | Expr::StringLit { inferred_type, .. }
            | Expr::Var { inferred_type, .. }
            | Expr::Let { inferred_type, .. }
            | Expr::If { inferred_type, .. }
            | Expr::Lambda { inferred_type, .. }
            | Expr::Apply { inferred_type, .. }
            | Expr::Match { inferred_type, .. }
            | Expr::VecLit { inferred_type, .. }
            | Expr::Annotate { inferred_type, .. }
            | Expr::Trace { inferred_type, .. }
            | Expr::ParBind { inferred_type, .. }
            | Expr::LaunchContinue { inferred_type, .. }
            | Expr::ConstrADT { inferred_type, .. } => *inferred_type = ty,
        }
    }
}

// --- Top-Level Definitions ---

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Public,
    Private,
}

/// Function definition.
///
/// Unified representation for both single-sig and multi-sig functions.
/// Single-sig `(defn name [params] body)` has one variant in `variants`.
/// Multi-sig `(defn name ([p1] b1) ([p2] b2))` has multiple variants.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Defn {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub variants: Vec<DefnVariant>,
    pub visibility: Visibility,
    pub span: Span,
}

impl Defn {
    /// Returns the params (name + optional `:Type` annotation per spec
    /// §5.1.1) of a single-sig defn. Panics if multi-sig.
    ///
    /// The per-param `Option<TypeExpr>` carries `None` for an unannotated
    /// parameter and `Some(TypeExpr)` for the `:Type name` or `:Trait name`
    /// forms. Fused tuple shape per Principle 18 — see `DefnVariant`
    /// docstring.
    pub fn params(&self) -> &[(Symbol, Option<TypeExpr>)] {
        assert!(
            self.variants.len() == 1,
            "Defn::params() called on multi-sig defn '{}' with {} variants",
            self.name,
            self.variants.len()
        );
        &self.variants[0].params
    }

    /// Returns the body of a single-sig defn. Panics if multi-sig.
    pub fn body(&self) -> &Expr {
        assert!(
            self.variants.len() == 1,
            "Defn::body() called on multi-sig defn '{}' with {} variants",
            self.name,
            self.variants.len()
        );
        &self.variants[0].body
    }

    /// Returns a mutable reference to the body of a single-sig defn. Panics if multi-sig.
    pub fn body_mut(&mut self) -> &mut Expr {
        if self.variants.len() != 1 {
            unreachable!(
                "invariant: Defn::body_mut() called on multi-sig defn '{}' with {} variants",
                self.name,
                self.variants.len()
            );
        }
        &mut self.variants[0].body
    }

    /// Returns true if this defn has multiple signature variants.
    pub fn is_multi_sig(&self) -> bool {
        self.variants.len() > 1
    }
}

/// One variant of a multi-signature function.
///
/// Each parameter carries its own optional `:Type` annotation, fused into
/// the `params: Vec<(Symbol, Option<TypeExpr>)>` tuple — `None` for an
/// unannotated parameter, `Some(TypeExpr)` for the `:Type name` /
/// `:Trait name` forms. Per spec §5.1.1 EBNF (`annotated_param =
/// colon_prefix symbol | symbol`) the annotation is independently optional
/// per-param; the fused tuple shape is the structural enforcement of that
/// invariant per Principle 18 (replaces the prior parallel-vec
/// `params: Vec<Symbol>` + `param_annotations: Vec<Option<TypeExpr>>`
/// layout, whose `len()` lockstep invariant was unenforced).
///
/// There is no `return_type` field. Per spec §5.1 (L41) — "The return type
/// is always inferred; there is no return type annotation syntax."
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefnVariant {
    pub params: Vec<(Symbol, Option<TypeExpr>)>,
    pub body: Expr,
    pub span: Span,
}

/// Field in a data constructor.
///
/// Per spec §2.2.6 + spec §5.2 (`field_def = annotation SYMBOL | SYMBOL`) the
/// field name is always present — both grammar productions terminate in a
/// required `SYMBOL`. The type annotation is independently optional: a bare
/// field (`SYMBOL` only, no `:Type`) gets a synthesised `TypeExpr::TypeVar`
/// at parse time (see `cranelisp-frontend::ast_builder` bare-detection site),
/// so `type_expr: TypeExpr` is unconditional — ADT type-resolution consumers
/// always have a syntactic type to resolve, with the synthesised `TypeVar`
/// directing inference to fill in the bare case. Per Principle 7 (single
/// source of truth) the producer-side name `type_expr` (over the prior
/// facade's `ty`) is canonical.
///
/// Per Decision 39 (per-defn source coordinate system — substance manifested
/// in `design/arch/bounded-contexts.md` §7 and `repl/spec.md` §15.4), each
/// field carries its own `span` so "field has wrong type" diagnostics can
/// point at the field's source location (not the enclosing constructor).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDef {
    pub name: Symbol,
    pub type_expr: TypeExpr,
    #[serde(default)]
    pub span: Span,
}

/// Data constructor definition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorDef {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Trait method signature.
///
/// Per spec §5.3 EBNF:
/// ```text
/// required_method = '(' name docstring? '[' param+ ']' type_expr ')'
/// default_method  = '(' name docstring? '[' param+ ']' body ')'
/// param           = ':' type_expr symbol | symbol
/// ```
///
/// Both required and default methods carry named parameters — the
/// `param = ':' type_expr symbol | symbol` production always terminates in a
/// `symbol`. The type annotation is independently optional per-param.
/// Per spec §5.3.1, bare parameter names default to the implementing type;
/// the parser synthesises `TypeExpr::SelfType` for bare params at parse time
/// so `params: Vec<(Symbol, TypeExpr)>` is unconditional (consumers always
/// have a name + a syntactic type per param). This mirrors the
/// `Vec<(Symbol, Option<TypeExpr>)>` shape on `DefnVariant` (S69 Submission 23)
/// and `Expr::Lambda` (S69 Submission 24); for traits the synthesised-`SelfType`
/// convention means the `Option` collapses — the second element is always
/// some `TypeExpr` (either the user-written annotation or the synthesised
/// `SelfType`).
///
/// Per Principle 18 (enforce invariants structurally), name + annotation
/// belong together on each param rather than across parallel vectors. The
/// prior 8-field shape carried an implicit lockstep invariant —
/// `default_param_names.is_empty() == default_body.is_none()` — that no type
/// rule enforced; fusing names into `params` and dropping the separate
/// `default_param_names` field eliminates that invariant by construction.
/// Names belong with the params, not with the default body.
///
/// `default_body: Option<Expr>` carries the parsed AST of the default body
/// when one is present (S69 Submission 26 — vindication of the prior facade
/// target against the source's pre-Submission-26 `Option<Sexp>`). Building
/// the AST at trait-decl time catches structural errors in special forms
/// (`let`, `if`, `match`, etc.) immediately, rather than per-impl;
/// name resolution + type-checking remain deferred (per spec §5.4.5, default
/// bodies are typechecked against each impl's instantiated signature, so the
/// trait declaration clones the `Expr` into per-impl typecheck context).
///
/// `hkt_param_index: Option<usize>` identifies the parameter position that
/// uses the HKT constructor variable for higher-kinded traits per spec §5.3.2
/// (e.g., the `f` in `(deftrait (Functor f) (fmap [:(Fn [a] b) f :(f a) x] (f b)))`).
/// HKT traits forbid default-method implementations (spec §5.3.2), so
/// `hkt_param_index.is_some() ⇒ default_body.is_none()` is a parser invariant.
///
/// `span: Span` per Decision 39 (per-defn source coordinate system for
/// diagnostics; substance manifested in `design/arch/bounded-contexts.md` §7
/// and `repl/spec.md` §15.4).
///
/// `ret_type` (not `return_type`) per Principle 7 (single source of truth —
/// the producer-side naming is canonical).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitMethodSig {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub params: Vec<(Symbol, TypeExpr)>,
    pub ret_type: TypeExpr,
    pub span: Span,
    pub hkt_param_index: Option<usize>,
    pub default_body: Option<Expr>,
}

/// Trait declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDecl {
    pub name: TraitName,
    pub docstring: Option<String>,
    pub type_params: Vec<Symbol>,
    pub methods: Vec<TraitMethodSig>,
    pub visibility: Visibility,
    pub span: Span,
}

/// Trait implementation — syntactic-stage shape (S69 Submission 27).
///
/// Per spec §5.4 EBNF the `impl_form` treats `target_type` as one grammatical
/// unit:
/// ```text
/// impl_form   = '(' 'impl' trait_ref constraints? target_type method_def* ')'
/// target_type = qualified_symbol
///             | '(' qualified_symbol type_arg+ ')'
/// type_arg    = ':' trait_ref type_var | type_var
/// ```
/// The unified `target: TypeExpr` field captures that grammatical unit
/// directly — the simple `target_type = qualified_symbol` case lowers to
/// `TypeExpr::Named(TypeRef)` and the polymorphic
/// `target_type = '(' qualified_symbol type_arg+ ')'` case lowers to
/// `TypeExpr::Applied(TypeRef, Vec<TypeExpr>)`. The prior 6-field shape
/// (`target_type: TypeName + type_args: Vec<Symbol>`) was an implementation
/// detail with no Decision-level grounding and is replaced by the
/// 5-field target.
///
/// Per spec §4.2.2 + spec §2.3.4 qualified references like `fmt/Display` or
/// `core.option/Option` resolve via the module system. Both `trait_name:
/// TraitRef` and the `TypeRef`s inside `target: TypeExpr` carry
/// `Option<ModuleFullPath>` capturing as-written qualification (import alias
/// OR full path). Typecheck resolves aliases through the import graph,
/// producing `FQTraitName` / `FQTypeName` at the resolved-stage boundary per
/// Decision 47. The resolved-stage counterpart of this struct is
/// `ModuleEntry::TraitImpl { trait_name: FQTraitName, impl_type: FQTypeName,
/// methods, visibility }` stored on the trait's defining module per Decision
/// 45 — distinct type, FQ names throughout.
///
/// `type_constraints: Vec<(Symbol, TraitRef)>` carries polymorphic-impl
/// constraints — `(impl :(Display a) (Option a) …)` produces
/// `[("a", TraitRef::new(None, "Display"))]`. Constraints can themselves be
/// qualified (`:(fmt/Display a)`); `TraitRef`'s optional module captures that
/// uniformly. `type_args` (Vec<Symbol>) is no longer a separate field — the
/// type-variable bindings live structurally inside `target` (any
/// `TypeExpr::TypeVar` reachable from `target` is a polymorphic-impl
/// type-var introduced by this impl).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub trait_name: TraitRef,
    pub target: TypeExpr,
    pub type_constraints: Vec<(Symbol, TraitRef)>,
    pub methods: Vec<Defn>,
    pub span: Span,
}

/// Top-level form: the unit of compilation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TopLevel {
    Defn(Defn),
    Expr(Expr),
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
    TypeDef {
        name: TypeName,
        docstring: Option<String>,
        type_params: Vec<Symbol>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        span: Span,
    },
}

/// A complete compilation unit: all top-level forms from one module.
pub type Program = Vec<TopLevel>;

// ---------------------------------------------------------------------------
// Free variable analysis for Expr (used by bind chain independence analysis)
// ---------------------------------------------------------------------------

/// Compute the set of free variables in an expression.
///
/// Variables listed in `globals` (top-level functions, builtins) are excluded.
/// Dotted names (e.g., `Type.Constructor`, `Trait.method`) are always treated
/// as global references and excluded.
///
/// This is a pure AST traversal with no external dependencies, suitable for
/// pre-typecheck analysis passes.
pub fn free_vars_expr(expr: &Expr, globals: &HashSet<Symbol>) -> HashSet<Symbol> {
    match expr {
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. } => HashSet::new(),

        Expr::Var { name, .. } => {
            // Dotted names are always global references.
            if globals.contains(name) || name.contains('.') {
                HashSet::new()
            } else {
                let mut s = HashSet::new();
                s.insert(name.clone());
                s
            }
        }

        Expr::Let { bindings, body, .. } => {
            let mut fv = HashSet::new();
            let mut bound = HashSet::new();
            for (name, val_expr) in bindings {
                let val_fv = free_vars_expr(val_expr, globals);
                for v in val_fv {
                    if !bound.contains(&v) {
                        fv.insert(v);
                    }
                }
                bound.insert(name.clone());
            }
            let body_fv = free_vars_expr(body, globals);
            for v in body_fv {
                if !bound.contains(&v) {
                    fv.insert(v);
                }
            }
            fv
        }

        Expr::If { cond, then_branch, else_branch, .. } => {
            let mut fv = free_vars_expr(cond, globals);
            fv.extend(free_vars_expr(then_branch, globals));
            fv.extend(free_vars_expr(else_branch, globals));
            fv
        }

        Expr::Lambda { params, body, .. } => {
            let body_fv = free_vars_expr(body, globals);
            // Fused tuple shape — extract the parameter name (`.0`) from each
            // `(Symbol, Option<TypeExpr>)` entry; the optional annotation does
            // not participate in the body's free-variable set.
            let param_set: HashSet<Symbol> = params.iter().map(|(n, _)| n.clone()).collect();
            body_fv.into_iter().filter(|v| !param_set.contains(v)).collect()
        }

        Expr::Apply { callee, args, .. } => {
            let mut fv = free_vars_expr(callee, globals);
            for arg in args {
                fv.extend(free_vars_expr(arg, globals));
            }
            fv
        }

        Expr::Match { scrutinee, arms, .. } => {
            let mut fv = free_vars_expr(scrutinee, globals);
            for arm in arms {
                let arm_fv = free_vars_expr(&arm.body, globals);
                let bound: HashSet<Symbol> = match &arm.pattern {
                    Pattern::Constructor { bindings, .. } => bindings.iter().cloned().collect(),
                    Pattern::Var { name, .. } => {
                        let mut s = HashSet::new();
                        s.insert(name.clone());
                        s
                    }
                    Pattern::Wildcard { .. } => HashSet::new(),
                };
                for v in arm_fv {
                    if !bound.contains(&v) {
                        fv.insert(v);
                    }
                }
            }
            fv
        }

        Expr::Annotate { expr, .. } => free_vars_expr(expr, globals),

        Expr::VecLit { elements, .. } => {
            let mut fv = HashSet::new();
            for elem in elements {
                fv.extend(free_vars_expr(elem, globals));
            }
            fv
        }

        Expr::ParBind { bindings, body, .. } => {
            // ParBind bindings are independent (no binding references another).
            let mut fv = HashSet::new();
            for (_, val_expr) in bindings {
                fv.extend(free_vars_expr(val_expr, globals));
            }
            let bound: HashSet<Symbol> = bindings.iter().map(|(n, _)| n.clone()).collect();
            let body_fv = free_vars_expr(body, globals);
            for v in body_fv {
                if !bound.contains(&v) {
                    fv.insert(v);
                }
            }
            fv
        }

        Expr::Trace { body, .. } => free_vars_expr(body, globals),

        // `LaunchContinue { launched, continuation, .. }` — sequential
        // `Bind(launched, λ_. continuation)` for free-variable purposes: the
        // launched effect discards its result (it binds no name visible to the
        // continuation), so the free-var set is the union over both sub-trees.
        Expr::LaunchContinue { launched, continuation, .. } => {
            let mut fv = free_vars_expr(launched, globals);
            fv.extend(free_vars_expr(continuation, globals));
            fv
        }

        // `ConstrADT { type_name, tag, fields, span, inferred_type }` — see
        // `ast.rs` rustdoc. Free vars are the union over the field
        // expressions; `type_name` and `tag` are compile-time constants, not
        // value references.
        Expr::ConstrADT { fields, .. } => {
            let mut fv = HashSet::new();
            for field in fields {
                fv.extend(free_vars_expr(field, globals));
            }
            fv
        }
    }
}

