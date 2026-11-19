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

/// Rewrite the bind chains of one single-signature definition (§5.3), with
/// its parameters as the root scope (§3.8).
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
    let params = variant.params.iter().map(|(p, _)| p.clone()).collect();
    let mut pass = Pass::new(scope, declarations, current_module, params);
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
    /// The binders whose region contains the position being read (§3.8):
    /// extended on entry to a region and truncated on exit.
    locals: Vec<Symbol>,
    bind: FQSymbol,
    sleep: FQSymbol,
}

impl<'r, 'a, C: CodeStore, L: LinkerStore> Pass<'r, 'a, C, L> {
    fn new(
        scope: &'r ResolutionScope<'a, C, L>,
        declarations: &'r ClusterDeclarations,
        current_module: &'r ModuleFullPath,
        locals: Vec<Symbol>,
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

    /// The effect, binder and continuation body of `(bind io (fn [x] body))`
    /// whose callee is the primitive.
    fn chain_step<'e>(&self, expr: &'e Expr) -> Option<(&'e Expr, &'e Symbol, &'e Expr)> {
        let Expr::Apply { callee, args, .. } = expr else {
            return None;
        };
        let [effect, Expr::Lambda { params, body, .. }] = args.as_slice() else {
            return None;
        };
        let [(binder, _)] = params.as_slice() else {
            return None;
        };
        (self.callee(callee) == Callee::Bind).then_some((effect, binder, body))
    }

    fn starts_chain(&self, expr: &Expr) -> bool {
        self.chain_step(expr).is_some()
    }

    // -----------------------------------------------------------------------
    // Binder scope (§3.8)
    // -----------------------------------------------------------------------

    /// Brings `names` into scope and returns the mark that `exit` restores.
    fn enter(&mut self, names: impl IntoIterator<Item = Symbol>) -> usize {
        let mark = self.locals.len();
        self.locals.extend(names);
        mark
    }

    fn exit(&mut self, mark: usize) {
        self.locals.truncate(mark);
    }

    // -----------------------------------------------------------------------
    // Transform
    // -----------------------------------------------------------------------

    fn transform(&mut self, expr: Expr) -> Expr {
        if self.starts_chain(&expr) {
            let mark = self.locals.len();
            let (chain, final_body) = self.collect_chain(expr);
            let rebuilt = self.rebuild_chain(chain, final_body);
            self.exit(mark);
            rebuilt
        } else {
            self.recurse_children(expr)
        }
    }

    /// Flatten a chain into its steps and the terminal body (§3.2). The first
    /// application that is not a step is the terminal body. Each step is read
    /// under the binders before it, and every step's binder is left in scope
    /// for the terminal body.
    fn collect_chain(&mut self, mut expr: Expr) -> (Vec<BindStep>, Expr) {
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
            let schedulable = matches!(
                self.callee_of_call(&effect),
                Callee::PlatformEffect { class, .. } if class != SchedulingClass::Sequential
            );
            let depth = self.enter([binder.clone()]);
            steps.push(BindStep {
                binder,
                annotation,
                effect,
                schedulable,
                depth,
                application,
                callee: *callee,
                lambda,
            });
            expr = *body;
        }
        (steps, expr)
    }

    /// Group a flat chain (§3.5) and fold it back right to left (§3.6). The
    /// terminal body is read under every step's binder, and the scope is cut
    /// back to each step's depth before its effect is read.
    fn rebuild_chain(&mut self, chain: Vec<BindStep>, final_body: Expr) -> Expr {
        let mut segments: Vec<Segment> = Vec::new();
        let mut group: Vec<BindStep> = Vec::new();
        let mut bound_so_far: HashSet<Symbol> = HashSet::new();

        for step in chain {
            let mut all_bound = bound_so_far.clone();
            all_bound.extend(group.iter().map(|s| s.binder.clone()));

            if step.schedulable && is_independent(&step.effect, &all_bound) {
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
                    self.exit(step.depth);
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
                    let mut bindings = Vec::with_capacity(steps.len());
                    for step in steps.into_iter().rev() {
                        self.exit(step.depth);
                        bindings.push((step.binder, self.transform(step.effect)));
                    }
                    bindings.reverse();
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

    /// The launch-eligibility predicate (`design/arch/effect-concurrency.md`
    /// §4.1). A step `(bind io_expr (fn [name] continuation))` whose `io_expr`
    /// is one platform effect or a whole discarded bind sub-tree may lower to
    /// a detached `Expr::LaunchContinue` iff all of:
    ///
    /// - **(E1) Result discarded:** `name` is not free in `continuation`.
    /// - **(E2) Value locality:** `io_expr` and `continuation` share no free
    ///   variable. Token values are dynamic, so disjointness is derived from
    ///   value provenance: a shared variable, a module-global handle included,
    ///   may carry the same token and is refused. A launch loop that keeps its
    ///   control value out of the token operand
    ///   (`(let [m (sub n 1)] (bind (rd n …) (fn [_] (recur m))))`) stays
    ///   disjoint.
    /// - **(E3) No shared-singleton token:** every effect position is a
    ///   launchable leaf (`is_launchable_leaf`). Inside a sub-tree a `sleep`
    ///   timer leaf is also accepted; it is never launched on its own.
    ///
    /// Declining is always sound (spec §10.12.7): the step stays a `bind`.
    fn launch_eligible(&mut self, name: &Symbol, io_expr: &Expr, continuation: &Expr) -> bool {
        let globals: HashSet<Symbol> = HashSet::new();
        let c_free = free_vars_expr(continuation, &globals);
        if c_free.contains(name) {
            return false;
        }
        let leaves_launchable = if self.starts_chain(io_expr) {
            self.subtree_leaves_launchable(io_expr)
        } else {
            self.is_launchable_leaf(io_expr)
        };
        leaves_launchable && free_vars_expr(io_expr, &globals).is_disjoint(&c_free)
    }

    /// (E3) over a launched sub-tree: each step's effect, read under the
    /// sub-tree's earlier binders, and the tail.
    fn subtree_leaves_launchable(&mut self, subtree: &Expr) -> bool {
        let mark = self.locals.len();
        let mut cursor = subtree;
        let launchable = loop {
            match self.chain_step(cursor) {
                Some((effect, binder, body)) => {
                    if !self.is_subtree_leaf(effect) {
                        break false;
                    }
                    self.enter([binder.clone()]);
                    cursor = body;
                }
                None => break self.is_subtree_leaf(cursor),
            }
        };
        self.exit(mark);
        launchable
    }

    fn is_subtree_leaf(&self, effect: &Expr) -> bool {
        self.is_launchable_leaf(effect) || self.callee_of_call(effect) == Callee::Sleep
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

    // -----------------------------------------------------------------------
    // Child recursion
    // -----------------------------------------------------------------------

    /// Recurse into sub-expressions without touching this node's structure.
    /// Each binder is in scope over its region (§3.8); every other form binds
    /// nothing.
    fn recurse_children(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Let {
                bindings,
                body,
                span,
                inferred_type,
            } => {
                let mark = self.locals.len();
                let mut transformed = Vec::with_capacity(bindings.len());
                for (name, value) in bindings {
                    let value = self.transform(value);
                    self.enter([name.clone()]);
                    transformed.push((name, value));
                }
                let body = Box::new(self.transform(*body));
                self.exit(mark);
                Expr::Let {
                    bindings: transformed,
                    body,
                    span,
                    inferred_type,
                }
            }
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
            } => {
                let mark = self.enter(params.iter().map(|(name, _)| name.clone()));
                let body = Box::new(self.transform(*body));
                self.exit(mark);
                Expr::Lambda {
                    params,
                    body,
                    span,
                    inferred_type,
                }
            }
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
                    .map(|arm| {
                        let mark = self.enter(pattern_binders(&arm.pattern));
                        let body = self.transform(arm.body);
                        self.exit(mark);
                        MatchArm {
                            pattern: arm.pattern,
                            body,
                            span: arm.span,
                        }
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
            } => {
                let bindings: Vec<(Symbol, Expr)> = bindings
                    .into_iter()
                    .map(|(name, value)| (name, self.transform(value)))
                    .collect();
                let mark = self.enter(bindings.iter().map(|(name, _)| name.clone()));
                let body = Box::new(self.transform(*body));
                self.exit(mark);
                Expr::ParBind {
                    bindings,
                    body,
                    span,
                    inferred_type,
                }
            }
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
    /// The effect calls a platform function of a non-`Sequential` class (§3.3),
    /// read under the binders before this step.
    schedulable: bool,
    /// The scope depth before this step's binder: its effect's scope (§3.8).
    depth: usize,
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

/// The names a match arm's pattern binds.
fn pattern_binders(pattern: &Pattern) -> Vec<Symbol> {
    match pattern {
        Pattern::Constructor { bindings, .. } => bindings.clone(),
        Pattern::Var { name, .. } => vec![name.clone()],
        Pattern::Wildcard { .. } => Vec::new(),
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod identity_tests;
