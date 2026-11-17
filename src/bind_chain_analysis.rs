//! Bind-chain independence analysis (`design/int/bind-chain-analysis.md`):
//! rewrites chains of the `bind` primitive into `Expr::ParBind` and
//! `Expr::LaunchContinue` nodes for automatic IO scheduling (spec §10.12).
//!
//! The pass runs over one cluster's expanded program before typecheck. Every
//! callee it reads (the `bind` primitive, a platform effect, the `sleep` timer
//! leaf) is identified by resolution, never by spelling (§3.1), and every node
//! it rebuilds keeps the span of the written node it replaces (§3.6), because
//! typecheck records expression types by span.

use std::collections::HashSet;

use cranelisp_platform::SchedulingClass;
use cranelisp_types::{
    CallableOrigin, CodeStore, Defn, Expr, FQSymbol, LinkerStore, MatchArm, ModuleFullPath,
    Pattern, Program, ResolutionScope, Resolved, Span, Symbol, TopLevel, TypeExpr, free_vars_expr,
};

/// Rewrite the bind chains of one single-signature definition (§5.3).
///
/// `scope` is the cluster's committed resolution scope and `declarations` the
/// names its program declares (§3.1, layers 3 and 2).
pub(crate) fn auto_schedule_defn<C: CodeStore, L: LinkerStore>(
    defn: &mut Defn,
    scope: &ResolutionScope<'_, C, L>,
    declarations: &ClusterDeclarations,
    current_module: &ModuleFullPath,
) {
    if defn.is_multi_sig() {
        unreachable!("invariant: auto_schedule_defn called on multi-sig defn");
    }
    let variant = &mut defn.variants[0];
    let mut locals: HashSet<Symbol> = variant.params.iter().map(|(p, _)| p.clone()).collect();
    collect_binders(&variant.body, &mut locals);
    let pass = Pass::new(scope, declarations, current_module, locals);
    let body = std::mem::replace(
        &mut variant.body,
        Expr::BoolLit {
            value: false,
            span: defn.span,
            inferred_type: None,
        },
    );
    variant.body = pass.transform(body);
}

// ---------------------------------------------------------------------------
// Callee identity (§3.1)
// ---------------------------------------------------------------------------

/// What a callee resolves to, as far as scheduling is concerned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Callee {
    /// The `bind` primitive bootstrap installs.
    Bind,
    /// The `sleep` timer leaf bootstrap installs.
    Sleep,
    /// A platform function, with the manifest's scheduling facts (§4).
    PlatformEffect {
        class: SchedulingClass,
        poll_shape: bool,
    },
    /// Anything else: a local, a cluster declaration, another terminal, or a
    /// spelling that does not resolve to exactly one declaration.
    Other,
}

/// The names a cluster's program declares (§3.1, layer 2). The program
/// reaches the pass before typecheck commits it, so the committed scope cannot
/// answer for these names.
pub(crate) struct ClusterDeclarations(HashSet<Symbol>);

impl ClusterDeclarations {
    pub(crate) fn of(program: &Program) -> Self {
        let mut names = HashSet::new();
        for item in program {
            match item {
                TopLevel::Defn(defn) => {
                    names.insert(defn.name.clone());
                }
                TopLevel::TraitDecl(decl) => {
                    names.extend(decl.methods.iter().map(|method| method.name.clone()));
                }
                TopLevel::TypeDef { constructors, .. } => {
                    for ctor in constructors {
                        names.insert(ctor.name.clone());
                        names.extend(ctor.fields.iter().map(|field| field.name.clone()));
                    }
                }
                TopLevel::TraitImpl(_) | TopLevel::Expr(_) => {}
            }
        }
        ClusterDeclarations(names)
    }

    /// True for a bare spelling the cluster declares, or one qualified by the
    /// current module.
    fn declares(&self, spelling: &str, current_module: &ModuleFullPath) -> bool {
        match spelling.rsplit_once('/') {
            Some((module, name)) if !module.is_empty() && !name.is_empty() => {
                module == current_module.as_ref() && self.0.contains(name)
            }
            _ => self.0.contains(spelling),
        }
    }
}

/// The rewrite of one definition: the one callee resolution (§3.1) and the
/// chain transform that reads it.
struct Pass<'r, 'a, C: CodeStore, L: LinkerStore> {
    scope: &'r ResolutionScope<'a, C, L>,
    declarations: &'r ClusterDeclarations,
    current_module: &'r ModuleFullPath,
    /// Every name any binder in the definition binds (§3.1, layer 1).
    locals: HashSet<Symbol>,
    bind: FQSymbol,
    sleep: FQSymbol,
}

impl<'r, 'a, C: CodeStore, L: LinkerStore> Pass<'r, 'a, C, L> {
    fn new(
        scope: &'r ResolutionScope<'a, C, L>,
        declarations: &'r ClusterDeclarations,
        current_module: &'r ModuleFullPath,
        locals: HashSet<Symbol>,
    ) -> Self {
        Pass {
            scope,
            declarations,
            current_module,
            locals,
            bind: crate::bootstrap::bind_primitive(),
            sleep: crate::bootstrap::sleep_primitive(),
        }
    }

    /// What `callee` resolves to: a lexical binder, then a cluster
    /// declaration, then the committed scope. Every miss declines.
    fn callee(&self, callee: &Expr) -> Callee {
        let Expr::Var { name, span, .. } = callee else {
            return Callee::Other;
        };
        if self.locals.contains(name) || self.declarations.declares(name, self.current_module) {
            return Callee::Other;
        }
        match self.scope.resolve(name, *span) {
            Ok(resolved) => self.classify(&resolved),
            Err(_) => Callee::Other,
        }
    }

    fn classify(&self, resolved: &Resolved<C>) -> Callee {
        if resolved.canonical == self.bind {
            return Callee::Bind;
        }
        if resolved.canonical == self.sleep {
            return Callee::Sleep;
        }
        match resolved.entry.callable().map(|callable| &callable.origin) {
            Some(CallableOrigin::PlatformEffect {
                scheduling_class,
                poll_shape,
            }) => Callee::PlatformEffect {
                class: *scheduling_class,
                poll_shape: *poll_shape,
            },
            _ => Callee::Other,
        }
    }

    /// The callee identity of a direct call; `Other` for any other expression.
    fn callee_of_call(&self, expr: &Expr) -> Callee {
        match expr {
            Expr::Apply { callee, .. } => self.callee(callee),
            _ => Callee::Other,
        }
    }

    /// True for `(bind io (fn [x] body))` whose callee is the primitive.
    fn starts_chain(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::Apply { callee, args, .. }
            if args.len() == 2
            && matches!(&args[1], Expr::Lambda { params, .. } if params.len() == 1)
            && self.callee(callee) == Callee::Bind)
    }

    // -----------------------------------------------------------------------
    // Transform
    // -----------------------------------------------------------------------

    fn transform(&self, expr: Expr) -> Expr {
        if self.starts_chain(&expr) {
            let (chain, final_body) = self.collect_chain(expr);
            self.rebuild_chain(chain, final_body)
        } else {
            self.recurse_children(expr)
        }
    }

    /// Flatten a chain into its steps and the terminal body (§3.2). The first
    /// application that is not a step is the terminal body.
    fn collect_chain(&self, mut expr: Expr) -> (Vec<BindStep>, Expr) {
        let mut steps = Vec::new();
        while self.starts_chain(&expr) {
            let Expr::Apply {
                callee,
                mut args,
                span: application,
                ..
            } = expr
            else {
                unreachable!("invariant: a chain step is an application")
            };
            let (
                Some(Expr::Lambda {
                    mut params,
                    body,
                    span: lambda,
                    ..
                }),
                Some(effect),
            ) = (args.pop(), args.pop())
            else {
                unreachable!("invariant: a chain step is (bind effect (fn [x] body))")
            };
            let Some((binder, annotation)) = params.pop() else {
                unreachable!("invariant: a chain step's lambda has one parameter")
            };
            steps.push(BindStep {
                binder,
                annotation,
                effect,
                application,
                callee: *callee,
                lambda,
            });
            expr = *body;
        }
        (steps, expr)
    }

    /// Group a flat chain (§3.5) and fold it back right to left (§3.6).
    fn rebuild_chain(&self, chain: Vec<BindStep>, final_body: Expr) -> Expr {
        let mut segments: Vec<Segment> = Vec::new();
        let mut group: Vec<BindStep> = Vec::new();
        let mut bound_so_far: HashSet<Symbol> = HashSet::new();

        for step in chain {
            let schedulable = matches!(
                self.callee_of_call(&step.effect),
                Callee::PlatformEffect { class, .. } if class != SchedulingClass::Sequential
            );
            let mut all_bound = bound_so_far.clone();
            all_bound.extend(group.iter().map(|s| s.binder.clone()));

            if schedulable && is_independent(&step.effect, &all_bound) {
                group.push(step);
            } else {
                flush_par_group(&mut segments, &mut bound_so_far, std::mem::take(&mut group));
                bound_so_far.insert(step.binder.clone());
                segments.push(Segment::Sequential(Box::new(step)));
            }
        }
        flush_par_group(&mut segments, &mut bound_so_far, group);

        let mut result = self.transform(final_body);
        for segment in segments.into_iter().rev() {
            result = match segment {
                Segment::Sequential(step) => {
                    let step = *step;
                    let effect = self.transform(step.effect);
                    // Launch-and-continue (§3.7): declining is always sound.
                    if self.launch_eligible(&step.binder, &effect, &result) {
                        Expr::LaunchContinue {
                            launched: Box::new(effect),
                            continuation: Box::new(result),
                            span: step.application,
                            inferred_type: None,
                        }
                    } else {
                        make_bind(BindStep { effect, ..step }, result)
                    }
                }
                Segment::Parallel(steps) => {
                    let span = steps[0].application;
                    let bindings = steps
                        .into_iter()
                        .map(|step| (step.binder, self.transform(step.effect)))
                        .collect();
                    Expr::ParBind {
                        bindings,
                        body: Box::new(result),
                        span,
                        inferred_type: None,
                    }
                }
            };
        }
        result
    }

    // -----------------------------------------------------------------------
    // Launch-and-continue eligibility — the E1/E2/E3 predicate
    // (design/arch/effect-concurrency.md §4.1; spec/10-io.md §10.12.7)
    // -----------------------------------------------------------------------

    /// The launch-eligibility predicate (§4.1). A bind step `(bind io_expr (fn [name]
    /// continuation))` whose `io_expr` is either a single platform effect OR a whole
    /// discarded **bind sub-tree** may be lowered as a detached supervised strand
    /// (`Expr::LaunchContinue`) instead of an ordinary `Bind` iff ALL of:
    ///
    /// - **(E1) Result-discarded** — `name` is unused in `continuation`
    ///   (`!free_vars(continuation).contains(name)`): no one awaits the launched
    ///   value, so detaching does not change the program's value (§10.12.7 step 1).
    /// - **(E2) Value-locality** — the launched effect's resource value must not flow
    ///   into a same-token continuation effect. A fresh, non-shared value (the
    ///   `accept`-minted `conn`) yields a fresh, disjoint token by construction (§4
    ///   fact 2). This is the load-bearing disjointness *witness*: token VALUES are
    ///   dynamic/runtime (§5/§8.1), so disjointness is derived from value provenance,
    ///   not token comparison. **BOTH arms run the SAME literal free-var disjointness**
    ///   (`free_vars(launched) ∩ free_vars(cont) == ∅`, modulo globals; FIXME 0478 —
    ///   Principle 7, one E2 core): a shared free var means the launched value also
    ///   flows into the continuation, so it cannot be proven token-disjoint and is
    ///   refused. A module-global pool handle appears as a shared free var ⇒ refused.
    ///   The §B4 launch LOOP keeps its control value OUT of the token operand
    ///   (`(let [m (sub n 1)] (bind (rd n …) (fn [_] (recur m))))` — io free {n}, cont
    ///   free {m} ⇒ disjoint ⇒ launches), so the unified check does not over-refuse it.
    ///   (The former single-step-only narrow `continuation_shares_resource_handle`
    ///   leading-operand check was a deviation with a soundness hole — aliased-handle
    ///   and user-fn-wrapped same-token reorders slipped through — now closed.)
    /// - **(E3) No shared-singleton-token effect** — every effect position in the
    ///   launched expression must be a `ResourceSerial` per-value-minted-token leaf,
    ///   never `Commutative` (token-0, unrestricted) nor `Sequential` (the global
    ///   token-1), and (for poll-shape leaves) never a literal-`0` leading token
    ///   operand (the dynamic shared singleton). An **opaque user-fn** in an effect
    ///   position is an unknown footprint and is likewise refused — which is why the
    ///   handler must be inlined to platform leaves for the launch to fire. **Timer
    ///   refinement:** a resource-free `sleep` timer leaf (`Callee::Sleep`) is
    ///   ALSO permitted as a sub-tree effect position — it carries no shared token and
    ///   no observable side-effect stream, so it reorders nothing observable when
    ///   detached as a sub-tree member (it is NOT independently launch-shaped; the
    ///   single-step arm below still refuses it).
    ///
    /// Declining to detach is ALWAYS sound (§10.12.7), so every failure path lowers
    /// as an ordinary `Bind`.
    fn launch_eligible(&self, name: &Symbol, io_expr: &Expr, continuation: &Expr) -> bool {
        let globals: HashSet<Symbol> = HashSet::new();

        // (E1) Result-discarded — the launched binder is unused in the continuation.
        if free_vars_expr(continuation, &globals).contains(name) {
            return false;
        }

        if self.starts_chain(io_expr) {
            // SUB-TREE case (the S96 C-fanout extension): walk every effect position
            // of the already-collected local bind sub-tree (Principle 7 — no
            // interprocedural analysis; the handler is inlined down to platform
            // leaves so the footprint is purely local).
            for effect in self.subtree_effect_positions(io_expr) {
                // A `ResourceSerial` per-value-minted-token leaf (E3) OR the
                // resource-free `sleep` timer leaf (the §4.1 timer-leaf refinement —
                // `Callee::Sleep`). A timer touches no shared resource and
                // produces no observable side-effect stream, so it is sound to carry
                // INSIDE a launched sub-tree (it is NOT independently launch-shaped —
                // the single-step arm below still refuses it).
                if !self.is_launchable_leaf(effect) && self.callee_of_call(effect) != Callee::Sleep
                {
                    return false; // (E3) — non-ResourceSerial / token-0 / opaque.
                }
            }
            // (E2) Value-locality witness: no free variable shared with the
            // continuation (a fresh, non-shared value ⇒ a disjoint token).
            let s_free = free_vars_expr(io_expr, &globals);
            let c_free = free_vars_expr(continuation, &globals);
            s_free.is_disjoint(&c_free)
        } else {
            // SINGLE-STEP case: E3 (`is_launchable_leaf` — ResourceSerial only, refuse
            // Commutative/Sequential/token-0/opaque) + E2 (value-locality).
            //
            // E2 is the SAME literal free-var disjointness the sub-tree arm computes
            // above (FIXME 0478 — Principle 7, one E2 core): the launched leaf and the
            // continuation must share NO free variable (modulo globals). A launched
            // effect whose resource value also flows into the continuation cannot be
            // proven to ride a token disjoint from a continuation effect's, so detaching
            // it could reorder two same-token effects across the launch boundary —
            // refused. The former narrow `continuation_shares_resource_handle`
            // (leading-operand-only) check was a deviation with a soundness hole (it
            // permitted aliased-handle + user-fn-wrapped same-token reorders); the
            // unified disjointness closes it. The legitimate §B4 launch LOOP keeps its
            // control value OUT of the token operand — e.g. `(let [m (sub n 1)] (bind
            // (rd n …) (fn [_] (recur m))))` — so io free {n}, cont free {m} ⇒ disjoint
            // ⇒ still launches.
            let s_free = free_vars_expr(io_expr, &globals);
            let c_free = free_vars_expr(continuation, &globals);
            self.is_launchable_leaf(io_expr) && s_free.is_disjoint(&c_free)
        }
    }

    /// (E3) for a single effect position: a `ResourceSerial` platform leaf,
    /// refusing `Commutative` (token 0), `Sequential` (token 1), an opaque
    /// call, and a literal-`0` dynamic token on a poll-shape leaf.
    fn is_launchable_leaf(&self, effect: &Expr) -> bool {
        match self.callee_of_call(effect) {
            Callee::PlatformEffect {
                class: SchedulingClass::ResourceSerial,
                poll_shape,
            } => !(poll_shape && leading_token_is_zero(effect)),
            _ => false,
        }
    }

    /// The effect positions of a launched bind sub-tree: each step's effect
    /// plus the tail, so a non-leaf tail is refused too.
    fn subtree_effect_positions<'e>(&self, subtree: &'e Expr) -> Vec<&'e Expr> {
        let mut effects: Vec<&Expr> = Vec::new();
        let mut cursor = subtree;
        loop {
            if self.starts_chain(cursor)
                && let Expr::Apply { args, .. } = cursor
            {
                effects.push(&args[0]);
                if let Expr::Lambda { body, .. } = &args[1] {
                    cursor = body;
                    continue;
                }
            }
            effects.push(cursor);
            break;
        }
        effects
    }

    // -----------------------------------------------------------------------
    // Child recursion
    // -----------------------------------------------------------------------

    /// Recurse into sub-expressions without touching this node's structure.
    fn recurse_children(&self, expr: Expr) -> Expr {
        match expr {
            Expr::Let {
                bindings,
                body,
                span,
                inferred_type,
            } => Expr::Let {
                bindings: bindings
                    .into_iter()
                    .map(|(n, v)| (n, self.transform(v)))
                    .collect(),
                body: Box::new(self.transform(*body)),
                span,
                inferred_type,
            },
            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
                inferred_type,
            } => Expr::If {
                cond: Box::new(self.transform(*cond)),
                then_branch: Box::new(self.transform(*then_branch)),
                else_branch: Box::new(self.transform(*else_branch)),
                span,
                inferred_type,
            },
            Expr::Lambda {
                params,
                body,
                span,
                inferred_type,
            } => Expr::Lambda {
                params,
                body: Box::new(self.transform(*body)),
                span,
                inferred_type,
            },
            Expr::Apply {
                callee,
                args,
                span,
                resolved_call,
                inferred_type,
            } => Expr::Apply {
                callee: Box::new(self.transform(*callee)),
                args: args.into_iter().map(|a| self.transform(a)).collect(),
                span,
                resolved_call,
                inferred_type,
            },
            Expr::Match {
                scrutinee,
                arms,
                span,
                compiler_generated,
                inferred_type,
            } => Expr::Match {
                scrutinee: Box::new(self.transform(*scrutinee)),
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: self.transform(arm.body),
                        span: arm.span,
                    })
                    .collect(),
                span,
                compiler_generated,
                inferred_type,
            },
            Expr::VecLit {
                elements,
                span,
                inferred_type,
            } => Expr::VecLit {
                elements: elements.into_iter().map(|e| self.transform(e)).collect(),
                span,
                inferred_type,
            },
            Expr::Annotate {
                annotation,
                expr,
                span,
                inferred_type,
            } => Expr::Annotate {
                annotation,
                expr: Box::new(self.transform(*expr)),
                span,
                inferred_type,
            },
            Expr::ParBind {
                bindings,
                body,
                span,
                inferred_type,
            } => Expr::ParBind {
                bindings: bindings
                    .into_iter()
                    .map(|(n, v)| (n, self.transform(v)))
                    .collect(),
                body: Box::new(self.transform(*body)),
                span,
                inferred_type,
            },
            Expr::Trace {
                modules,
                body,
                span,
                inferred_type,
            } => Expr::Trace {
                modules,
                body: Box::new(self.transform(*body)),
                span,
                inferred_type,
            },
            // Idempotency (§5.2): a pre-existing `LaunchContinue` (from a prior pass, or
            // built by a future caller) recurses its children without re-grouping —
            // exactly like the `ParBind` arm above.
            Expr::LaunchContinue {
                launched,
                continuation,
                span,
                inferred_type,
            } => Expr::LaunchContinue {
                launched: Box::new(self.transform(*launched)),
                continuation: Box::new(self.transform(*continuation)),
                span,
                inferred_type,
            },
            Expr::ConstrADT {
                type_name,
                tag,
                fields,
                span,
                inferred_type,
            } => Expr::ConstrADT {
                type_name,
                tag,
                fields: fields.into_iter().map(|f| self.transform(f)).collect(),
                span,
                inferred_type,
            },
            // Leaf nodes.
            leaf @ (Expr::IntLit { .. }
            | Expr::FloatLit { .. }
            | Expr::BoolLit { .. }
            | Expr::StringLit { .. }
            | Expr::Var { .. }) => leaf,
        }
    }
}

// ---------------------------------------------------------------------------
// Chain steps and reconstruction
// ---------------------------------------------------------------------------

/// One chain step and the three written nodes it consumes (§3.2): the
/// application's span, the callee node itself, and the lambda's span.
struct BindStep {
    binder: Symbol,
    annotation: Option<TypeExpr>,
    effect: Expr,
    application: Span,
    callee: Expr,
    lambda: Span,
}

/// A segment of the rebuilt chain.
enum Segment {
    /// Boxed to balance the variant sizes.
    Sequential(Box<BindStep>),
    /// Two or more data-independent schedulable steps.
    Parallel(Vec<BindStep>),
}

/// Flush the current parallel group: two or more steps become a parallel
/// segment, one is demoted to sequential, none is a no-op.
fn flush_par_group(
    segments: &mut Vec<Segment>,
    bound_so_far: &mut HashSet<Symbol>,
    mut group: Vec<BindStep>,
) {
    bound_so_far.extend(group.iter().map(|step| step.binder.clone()));
    match group.len() {
        0 => {}
        1 => {
            if let Some(step) = group.pop() {
                segments.push(Segment::Sequential(Box::new(step)));
            }
        }
        _ => segments.push(Segment::Parallel(group)),
    }
}

/// Rebuild a sequential step as the triple the user wrote, with only the
/// lambda body replaced (§3.6). It takes no span, so a rebuilt node can carry
/// only the span its written node had.
fn make_bind(step: BindStep, body: Expr) -> Expr {
    Expr::Apply {
        callee: Box::new(step.callee),
        args: vec![
            step.effect,
            Expr::Lambda {
                params: vec![(step.binder, step.annotation)],
                body: Box::new(body),
                span: step.lambda,
                inferred_type: None,
            },
        ],
        span: step.application,
        resolved_call: None,
        inferred_type: None,
    }
}

/// True if none of the names in `bound_names` appear free in `expr`.
fn is_independent(expr: &Expr, bound_names: &HashSet<Symbol>) -> bool {
    if bound_names.is_empty() {
        return true;
    }
    let globals = HashSet::new();
    free_vars_expr(expr, &globals).is_disjoint(bound_names)
}

/// True if `effect` is an `Apply` whose first argument is a literal `0` — the
/// token-0 shared-singleton dynamic token of a poll-shape `(token, capacity, …)`
/// leaf (§4.1 E3 / `poll-support.md §3.4`).
fn leading_token_is_zero(effect: &Expr) -> bool {
    matches!(effect, Expr::Apply { args, .. }
        if matches!(args.first(), Some(Expr::IntLit { value: 0, .. })))
}

/// Every name a binder in `expr` binds: lambda parameters, `let` bindings,
/// match-pattern binders and `ParBind` bindings (§3.1, layer 1). Nesting is
/// ignored, which only ever turns a recognition into a decline.
fn collect_binders(expr: &Expr, out: &mut HashSet<Symbol>) {
    match expr {
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (name, value) in bindings {
                out.insert(name.clone());
                collect_binders(value, out);
            }
            collect_binders(body, out);
        }
        Expr::Lambda { params, body, .. } => {
            out.extend(params.iter().map(|(name, _)| name.clone()));
            collect_binders(body, out);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_binders(scrutinee, out);
            for arm in arms {
                match &arm.pattern {
                    Pattern::Constructor { bindings, .. } => out.extend(bindings.iter().cloned()),
                    Pattern::Var { name, .. } => {
                        out.insert(name.clone());
                    }
                    Pattern::Wildcard { .. } => {}
                }
                collect_binders(&arm.body, out);
            }
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_binders(cond, out);
            collect_binders(then_branch, out);
            collect_binders(else_branch, out);
        }
        Expr::Apply { callee, args, .. } => {
            collect_binders(callee, out);
            args.iter().for_each(|arg| collect_binders(arg, out));
        }
        Expr::VecLit { elements, .. } => elements.iter().for_each(|e| collect_binders(e, out)),
        Expr::ConstrADT { fields, .. } => fields.iter().for_each(|f| collect_binders(f, out)),
        Expr::Annotate { expr, .. } => collect_binders(expr, out),
        Expr::Trace { body, .. } => collect_binders(body, out),
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            collect_binders(launched, out);
            collect_binders(continuation, out);
        }
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod identity_tests;
