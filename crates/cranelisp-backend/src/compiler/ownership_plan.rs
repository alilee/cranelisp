//! The ownership plan: the ONE producer of every move, duplicate and drop
//! decision for a compiled body (`design/backend/uniform-counting.md` §3).
//!
//! Every binder owns one reference, and on every path each owned reference is
//! consumed exactly once: by a move at its last use, or by a drop where it
//! becomes dead (§1). One backward walk over the body, in the emitter's
//! evaluation order, derives:
//!
//! - for each variable occurrence, the binder it denotes and whether it moves
//!   or duplicates;
//! - the binders dead at their introduction, and the binders dropped at each
//!   branch or arm entry;
//! - for each closure creation, one capture occurrence per captured name.
//!
//! The emitter reads these facts and decides nothing. Captures of the body
//! being planned belong to its environment: every use duplicates and nothing
//! drops them.
//!
//! Under `CRANELISP_NO_OWNERSHIP` (`moves_off`) every use duplicates, and the
//! binder whose last use it was is dropped once the consuming position has
//! taken the value. That is rule U1's uniform reference (§2): balanced, with
//! every copy-on-write update taking the copy arm.
//!
//! Facts are keyed by node address. The body is borrowed for the whole
//! compilation, so no key can be rebuilt underneath the plan.

use std::collections::{BTreeSet, HashMap, HashSet};

use cranelisp_types::{ApplyRef, MonoExpr, Pattern, ResolvedCall, Symbol};

use super::control_flow::find_free_vars;

/// The identity of one owned binder within one plan.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub(crate) struct BinderId(u32);

/// What a use of an owned binder does with its reference.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Use {
    /// The binder's own reference travels; nothing is emitted.
    Move,
    /// One increment; the binder keeps its reference.
    Duplicate,
}

/// What one variable occurrence denotes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Occurrence {
    /// An owned binder of this body.
    Owned { binder: BinderId, use_: Use },
    /// A capture of this body: its environment owns it, so a use duplicates.
    Capture,
}

/// One captured name at a closure creation, in capture-layout order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CaptureEntry {
    pub(crate) name: Symbol,
    pub(crate) occurrence: Occurrence,
}

/// Where a binder is introduced.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Intro {
    /// The body's parameter at this position.
    Param(usize),
    /// The `index`th binding of the `let` (or `par-bind`) at `node`.
    Let { node: usize, index: usize },
    /// Pattern slot `slot` of arm `arm` of the match at `node`. A variable
    /// pattern is slot 0.
    Arm {
        node: usize,
        arm: usize,
        slot: usize,
    },
}

/// The address key of a node.
pub(crate) fn node_key(node: &MonoExpr) -> usize {
    node as *const MonoExpr as usize
}

/// Is the callee of this application evaluated as a value, so that it is a
/// consuming position? One predicate for the plan and the emitter's dispatch.
///
/// A callee is evaluated when it is a computed expression or a local or
/// captured closure, and for the auto-curry arm that curries a closure value.
/// Every other dispatch names a table callable and evaluates nothing.
pub(crate) fn callee_is_evaluated(
    callee: &MonoExpr,
    resolved_call: Option<&ResolvedCall>,
    dispatch: &ApplyRef,
    resolves_locally: impl Fn(&Symbol) -> bool,
) -> bool {
    match resolved_call {
        Some(ResolvedCall::AutoCurry {
            trait_resolution, ..
        }) => {
            let apply_target = match dispatch {
                ApplyRef::Dispatch(fq) => Some(fq),
                ApplyRef::ViaCallee => None,
            };
            matches!(
                crate::compiler::apply::classify_auto_curry_target(
                    apply_target,
                    trait_resolution.as_deref(),
                    callee,
                ),
                crate::compiler::apply::AutoCurryTarget::ClosureValue
            )
        }
        Some(_) => false,
        None => match callee {
            MonoExpr::Var { name, .. } => resolves_locally(name),
            _ => true,
        },
    }
}

/// The operands a node consumes, in evaluation order: the ONE definition of
/// operand order (`uniform-counting.md` §3.2). The plan walks it backwards;
/// the linearity check, `consumed_within` and the emitter's operand evaluator
/// walk it forwards.
pub(crate) struct OperandSequence<'n> {
    /// The callee, evaluated before every other operand when the application
    /// evaluates it (`callee_is_evaluated`).
    pub(crate) callee: Option<&'n MonoExpr>,
    /// The other operand expressions, left to right.
    pub(crate) exprs: Vec<&'n MonoExpr>,
    /// The node then creates a continuation closure whose capture point
    /// follows every operand expression (`par-bind`, launch-continue).
    pub(crate) continuation: bool,
}

/// Where an evaluated operand's value goes in its node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OperandSlot {
    /// The application's callee.
    Callee,
    /// Position `.0` of [`OperandSequence::exprs`].
    Expr(usize),
}

impl<'n> OperandSequence<'n> {
    /// The operand expressions in evaluation order, each with the slot its
    /// value fills. This order is the definition every reader walks: the
    /// callee first, then the other operands left to right.
    pub(crate) fn in_order(
        &self,
    ) -> impl DoubleEndedIterator<Item = (OperandSlot, &'n MonoExpr)> + '_ {
        let callee = self.callee.map(|callee| (OperandSlot::Callee, callee));
        let exprs = self
            .exprs
            .iter()
            .enumerate()
            .map(|(position, expr)| (OperandSlot::Expr(position), *expr));
        callee.into_iter().chain(exprs)
    }
}

/// The operand sequence of `node`, or `None` for a node outside it: a
/// branching or binding node, which orders its children by construction, or a
/// leaf. `evaluates_callee` is the plan's answer for an application.
pub(crate) fn operand_sequence(
    node: &MonoExpr,
    evaluates_callee: bool,
) -> Option<OperandSequence<'_>> {
    let (callee, exprs, continuation) = match node {
        MonoExpr::Apply { callee, args, .. } => (
            evaluates_callee.then_some(callee.as_ref()),
            args.iter().collect(),
            false,
        ),
        MonoExpr::VecLit { elements, .. } => (None, elements.iter().collect(), false),
        MonoExpr::ConstrADT { fields, .. } => (None, fields.iter().collect(), false),
        MonoExpr::ParBind { bindings, .. } => {
            (None, bindings.iter().map(|(_, init)| init).collect(), true)
        }
        MonoExpr::LaunchContinue { launched, .. } => (None, vec![launched.as_ref()], true),
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::StringLit { .. }
        | MonoExpr::Var { .. }
        | MonoExpr::Let { .. }
        | MonoExpr::If { .. }
        | MonoExpr::Match { .. }
        | MonoExpr::Lambda { .. }
        | MonoExpr::Trace { .. } => return None,
    };
    Some(OperandSequence {
        callee,
        exprs,
        continuation,
    })
}

/// The capture list of a lambda body: its free names that resolve here,
/// sorted for a deterministic layout.
fn lambda_capture_names(
    params: &[Symbol],
    body: &MonoExpr,
    resolves: impl Fn(&Symbol) -> bool,
) -> Vec<Symbol> {
    let mut names: Vec<Symbol> = find_free_vars(body, params)
        .into_iter()
        .filter(|name| resolves(name))
        .collect();
    names.sort();
    names
}

/// The ownership facts of one compiled body.
#[derive(Debug, Default)]
pub(crate) struct OwnershipPlan {
    intros: HashMap<Intro, BinderId>,
    dead_at_intro: HashSet<BinderId>,
    occurrences: HashMap<usize, Occurrence>,
    /// Binders dropped on entry to branch `.1` of the `if` or `match` at `.0`.
    entry_drops: HashMap<(usize, usize), Vec<BinderId>>,
    /// Moves off: binders dropped once the node at the key has completed.
    post_drops: HashMap<usize, Vec<BinderId>>,
    /// Moves off: binders whose last use was this match's scrutinee, dropped
    /// at every arm entry once the arm holds the scrutinee value.
    scrutinee_drops: HashMap<usize, Vec<BinderId>>,
    captures: HashMap<usize, Vec<CaptureEntry>>,
    evaluated_callees: HashSet<usize>,
}

impl OwnershipPlan {
    /// Plan `body`, whose parameters are `params` and whose environment holds
    /// `captures`. `moves_off` selects U1's uniform reference.
    pub(crate) fn build(
        body: &MonoExpr,
        params: &[Symbol],
        captures: &[Symbol],
        moves_off: bool,
    ) -> Self {
        let mut builder = Builder {
            plan: OwnershipPlan::default(),
            next: 0,
            env: captures
                .iter()
                .map(|name| (name.clone(), Res::Capture))
                .collect(),
            moves_off,
        };
        let mut param_ids = Vec::with_capacity(params.len());
        for (i, name) in params.iter().enumerate() {
            let id = builder.introduce(Intro::Param(i));
            builder.env.push((name.clone(), Res::Owned(id)));
            param_ids.push(id);
        }
        let mut live = Live::new();
        builder.walk(body, &mut live, Pos::Result);
        for id in param_ids.iter().rev() {
            builder.env.pop();
            builder.retire(*id, &mut live);
        }
        debug_assert!(
            live.is_empty(),
            "every owned binder is introduced inside the planned body"
        );
        builder.plan
    }

    /// The binder introduced at `intro`, if the plan saw that introduction.
    pub(crate) fn binder_at(&self, intro: Intro) -> Option<BinderId> {
        self.intros.get(&intro).copied()
    }

    /// Is `binder` dead at its introduction (no use follows)?
    pub(crate) fn dead_at_intro(&self, binder: BinderId) -> bool {
        self.dead_at_intro.contains(&binder)
    }

    /// What the variable occurrence `node` denotes; `None` for a global.
    pub(crate) fn occurrence(&self, node: &MonoExpr) -> Option<Occurrence> {
        self.occurrences.get(&node_key(node)).copied()
    }

    /// The binders dropped on entry to branch `branch` of `node`.
    pub(crate) fn entry_drops(&self, node: usize, branch: usize) -> &[BinderId] {
        self.entry_drops
            .get(&(node, branch))
            .map_or(&[], Vec::as_slice)
    }

    /// The binders dropped once `node` has completed (moves off only).
    pub(crate) fn post_drops(&self, node: &MonoExpr) -> &[BinderId] {
        self.post_drops
            .get(&node_key(node))
            .map_or(&[], Vec::as_slice)
    }

    /// The binders dropped at every arm entry of the match `node` (moves off).
    pub(crate) fn scrutinee_drops(&self, node: usize) -> &[BinderId] {
        self.scrutinee_drops.get(&node).map_or(&[], Vec::as_slice)
    }

    /// The captures of the closure created at `node`.
    pub(crate) fn captures(&self, node: &MonoExpr) -> Option<&[CaptureEntry]> {
        self.captures.get(&node_key(node)).map(Vec::as_slice)
    }

    /// Does the plan evaluate the callee of the application `node`?
    pub(crate) fn evaluates_callee(&self, node: &MonoExpr) -> bool {
        self.evaluated_callees.contains(&node_key(node))
    }

    /// The operand sequence of `node` as this plan evaluates it.
    ///
    /// # Panics
    /// When `node` has no operand sequence.
    pub(crate) fn operands<'n>(&self, node: &'n MonoExpr) -> OperandSequence<'n> {
        operand_sequence(node, self.evaluates_callee(node)).expect(
            "an operand-sequence node: application, Vec literal, constructor, par-bind or launch",
        )
    }

    /// The binders of this body whose reference is consumed inside `node`'s
    /// evaluation and that were introduced outside it.
    ///
    /// A lenient spark evaluates such a subtree in a thunk whose captures all
    /// duplicate; the frame then drops exactly these binders where the
    /// sequential evaluation would have consumed them, so both arms of the
    /// create-gate consume the same references.
    pub(crate) fn consumed_within(&self, node: &MonoExpr) -> Vec<BinderId> {
        let mut consumed = BTreeSet::new();
        let mut introduced = HashSet::new();
        self.collect_consumed(node, &mut consumed, &mut introduced);
        consumed
            .into_iter()
            .filter(|binder| !introduced.contains(binder))
            .collect()
    }

    fn collect_consumed(
        &self,
        node: &MonoExpr,
        consumed: &mut BTreeSet<BinderId>,
        introduced: &mut HashSet<BinderId>,
    ) {
        let key = node_key(node);
        if let Some(Occurrence::Owned {
            binder,
            use_: Use::Move,
        }) = self.occurrences.get(&key)
        {
            consumed.insert(*binder);
        }
        if let Some(drops) = self.post_drops.get(&key) {
            consumed.extend(drops.iter().copied());
        }
        if let Some(drops) = self.scrutinee_drops.get(&key) {
            consumed.extend(drops.iter().copied());
        }
        if let Some(entries) = self.captures.get(&key) {
            for entry in entries {
                if let Occurrence::Owned {
                    binder,
                    use_: Use::Move,
                } = entry.occurrence
                {
                    consumed.insert(binder);
                }
            }
        }
        for ((at, _), drops) in &self.entry_drops {
            if *at == key {
                consumed.extend(drops.iter().copied());
            }
        }
        match node {
            MonoExpr::Let { bindings, body, .. } => {
                for (index, (_, init)) in bindings.iter().enumerate() {
                    if let Some(id) = self.binder_at(Intro::Let { node: key, index }) {
                        introduced.insert(id);
                    }
                    self.collect_consumed(init, consumed, introduced);
                }
                self.collect_consumed(body, consumed, introduced);
            }
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_consumed(cond, consumed, introduced);
                self.collect_consumed(then_branch, consumed, introduced);
                self.collect_consumed(else_branch, consumed, introduced);
            }
            MonoExpr::Match {
                scrutinee, arms, ..
            } => {
                self.collect_consumed(scrutinee, consumed, introduced);
                for (arm_index, arm) in arms.iter().enumerate() {
                    for slot in 0..pattern_binders(&arm.pattern).len() {
                        if let Some(id) = self.binder_at(Intro::Arm {
                            node: key,
                            arm: arm_index,
                            slot,
                        }) {
                            introduced.insert(id);
                        }
                    }
                    self.collect_consumed(&arm.body, consumed, introduced);
                }
            }
            MonoExpr::Apply { .. }
            | MonoExpr::VecLit { .. }
            | MonoExpr::ConstrADT { .. }
            | MonoExpr::ParBind { .. }
            | MonoExpr::LaunchContinue { .. } => {
                for (_, operand) in self.operands(node).in_order() {
                    self.collect_consumed(operand, consumed, introduced);
                }
            }
            MonoExpr::Trace { body, .. } => self.collect_consumed(body, consumed, introduced),
            // A closure body has its own plan; its captures were read above.
            MonoExpr::Lambda { .. }
            | MonoExpr::Var { .. }
            | MonoExpr::IntLit { .. }
            | MonoExpr::FloatLit { .. }
            | MonoExpr::BoolLit { .. }
            | MonoExpr::StringLit { .. } => {}
        }
    }
}

/// The names a pattern binds, in slot order.
pub(crate) fn pattern_binders(pattern: &Pattern) -> &[Symbol] {
    match pattern {
        Pattern::Var { name, .. } => std::slice::from_ref(name),
        Pattern::Constructor { bindings, .. } => bindings,
        Pattern::Wildcard { .. } => &[],
    }
}

#[derive(Clone, Copy, Debug)]
enum Res {
    Owned(BinderId),
    Capture,
}

/// Where a consumed value goes, which fixes where moves off drops the binder
/// whose last use it was.
#[derive(Clone, Copy)]
enum Pos {
    /// A result or binding position: the receiver holds the value itself.
    Result,
    /// An operand of the node at this key, which consumes it when it runs.
    Operand(usize),
    /// The scrutinee of the match at this key.
    Scrutinee(usize),
}

type Live = HashSet<BinderId>;

struct Builder {
    plan: OwnershipPlan,
    next: u32,
    env: Vec<(Symbol, Res)>,
    moves_off: bool,
}

impl Builder {
    fn introduce(&mut self, intro: Intro) -> BinderId {
        let id = BinderId(self.next);
        self.next += 1;
        self.plan.intros.insert(intro, id);
        id
    }

    /// Leave `binder`'s scope, walking backwards: if no use followed its
    /// introduction it is dead there.
    fn retire(&mut self, binder: BinderId, live: &mut Live) {
        if !live.remove(&binder) {
            self.plan.dead_at_intro.insert(binder);
        }
    }

    fn resolve(&self, name: &Symbol) -> Option<Res> {
        self.env
            .iter()
            .rev()
            .find(|(bound, _)| bound == name)
            .map(|(_, res)| *res)
    }

    /// Classify one use of `binder` at a position whose value goes to `pos`.
    fn use_binder(&mut self, binder: BinderId, live: &mut Live, at: usize, pos: Pos) -> Use {
        let last = live.insert(binder);
        if !last {
            return Use::Duplicate;
        }
        if !self.moves_off {
            return Use::Move;
        }
        let drops = match pos {
            Pos::Result => self.plan.post_drops.entry(at),
            Pos::Operand(parent) => self.plan.post_drops.entry(parent),
            Pos::Scrutinee(node) => self.plan.scrutinee_drops.entry(node),
        };
        drops.or_default().push(binder);
        Use::Duplicate
    }

    fn capture_entries(
        &mut self,
        names: Vec<Symbol>,
        live: &mut Live,
        at: usize,
    ) -> Vec<CaptureEntry> {
        names
            .into_iter()
            .map(|name| {
                let occurrence = match self.resolve(&name) {
                    Some(Res::Owned(binder)) => Occurrence::Owned {
                        binder,
                        use_: self.use_binder(binder, live, at, Pos::Result),
                    },
                    _ => Occurrence::Capture,
                };
                CaptureEntry { name, occurrence }
            })
            .collect()
    }

    /// Walk `node` BACKWARDS: on entry `live` holds the binders live after it;
    /// on return, the binders live before it.
    fn walk(&mut self, node: &MonoExpr, live: &mut Live, pos: Pos) {
        let key = node_key(node);
        match node {
            MonoExpr::IntLit { .. }
            | MonoExpr::FloatLit { .. }
            | MonoExpr::BoolLit { .. }
            | MonoExpr::StringLit { .. } => {}
            MonoExpr::Var { name, .. } => match self.resolve(name) {
                None => {}
                Some(Res::Capture) => {
                    self.plan.occurrences.insert(key, Occurrence::Capture);
                }
                Some(Res::Owned(binder)) => {
                    let use_ = self.use_binder(binder, live, key, pos);
                    self.plan
                        .occurrences
                        .insert(key, Occurrence::Owned { binder, use_ });
                }
            },
            MonoExpr::Let { bindings, body, .. } => {
                let ids: Vec<BinderId> = (0..bindings.len())
                    .map(|index| self.introduce(Intro::Let { node: key, index }))
                    .collect();
                for ((name, _), id) in bindings.iter().zip(&ids) {
                    self.env.push((name.clone(), Res::Owned(*id)));
                }
                self.walk(body, live, Pos::Result);
                for (index, (_, init)) in bindings.iter().enumerate().rev() {
                    self.env.pop();
                    self.retire(ids[index], live);
                    self.walk(init, live, Pos::Result);
                }
            }
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let after = live.clone();
                let mut then_live = after.clone();
                self.walk(then_branch, &mut then_live, Pos::Result);
                let mut else_live = after;
                self.walk(else_branch, &mut else_live, Pos::Result);
                let before: Live = then_live.union(&else_live).copied().collect();
                self.record_entry_drops(key, 0, &before, &then_live);
                self.record_entry_drops(key, 1, &before, &else_live);
                *live = before;
                self.walk(cond, live, Pos::Result);
            }
            MonoExpr::Match {
                scrutinee, arms, ..
            } => {
                let after = live.clone();
                let mut arm_lives = Vec::with_capacity(arms.len());
                for (arm_index, arm) in arms.iter().enumerate() {
                    let names = pattern_binders(&arm.pattern);
                    let ids: Vec<BinderId> = (0..names.len())
                        .map(|slot| {
                            self.introduce(Intro::Arm {
                                node: key,
                                arm: arm_index,
                                slot,
                            })
                        })
                        .collect();
                    for (name, id) in names.iter().zip(&ids) {
                        self.env.push((name.clone(), Res::Owned(*id)));
                    }
                    let mut arm_live = after.clone();
                    self.walk(&arm.body, &mut arm_live, Pos::Result);
                    for id in ids.iter().rev() {
                        self.env.pop();
                        self.retire(*id, &mut arm_live);
                    }
                    arm_lives.push(arm_live);
                }
                let before: Live = arm_lives.iter().flatten().copied().collect();
                for (arm_index, arm_live) in arm_lives.iter().enumerate() {
                    self.record_entry_drops(key, arm_index, &before, arm_live);
                }
                *live = before;
                self.walk(scrutinee, live, Pos::Scrutinee(key));
            }
            MonoExpr::Lambda { params, body, .. } => {
                let names = lambda_capture_names(params, body, |name| self.resolve(name).is_some());
                let entries = self.capture_entries(names, live, key);
                self.plan.captures.insert(key, entries);
            }
            MonoExpr::Apply {
                callee,
                resolved_call,
                dispatch,
                ..
            } => {
                let evaluated =
                    callee_is_evaluated(callee, resolved_call.as_deref(), dispatch, |name| {
                        self.resolve(name).is_some()
                    });
                if evaluated {
                    self.plan.evaluated_callees.insert(key);
                }
                self.walk_operands(node, evaluated, live);
            }
            MonoExpr::VecLit { .. }
            | MonoExpr::ConstrADT { .. }
            | MonoExpr::ParBind { .. }
            | MonoExpr::LaunchContinue { .. } => self.walk_operands(node, false, live),
            MonoExpr::Trace { body, .. } => self.walk(body, live, Pos::Result),
        }
    }

    /// Walk `node`'s operand sequence backwards: the continuation's capture
    /// point first, then each operand expression from the last.
    fn walk_operands(&mut self, node: &MonoExpr, evaluated: bool, live: &mut Live) {
        let key = node_key(node);
        let Some(sequence) = operand_sequence(node, evaluated) else {
            unreachable!("walk_operands is called only for an operand-sequence node");
        };
        if sequence.continuation {
            let names = self.continuation_capture_names(node);
            let entries = self.capture_entries(names, live, key);
            self.plan.captures.insert(key, entries);
        }
        for (_, operand) in sequence.in_order().rev() {
            self.walk(operand, live, Pos::Operand(key));
        }
    }

    /// The captures of the continuation `node` creates: the continuation's
    /// free names that resolve here, sorted. A `par-bind`'s binding names are
    /// its continuation's own parameters.
    fn continuation_capture_names(&self, node: &MonoExpr) -> Vec<Symbol> {
        let (body, own): (&MonoExpr, HashSet<&Symbol>) = match node {
            MonoExpr::ParBind { bindings, body, .. } => {
                (body, bindings.iter().map(|(name, _)| name).collect())
            }
            MonoExpr::LaunchContinue { continuation, .. } => (continuation, HashSet::new()),
            _ => unreachable!("only par-bind and launch-continue create a continuation"),
        };
        let mut names: Vec<Symbol> = find_free_vars(body, &[])
            .into_iter()
            .filter(|name| !own.contains(name) && self.resolve(name).is_some())
            .collect();
        names.sort();
        names
    }

    fn record_entry_drops(
        &mut self,
        node: usize,
        branch: usize,
        before: &Live,
        branch_live: &Live,
    ) {
        let mut drops: Vec<BinderId> = before.difference(branch_live).copied().collect();
        if drops.is_empty() {
            return;
        }
        drops.sort();
        self.plan.entry_drops.insert((node, branch), drops);
    }
}

// =============================================================================
// The linearity check (`uniform-counting.md` §2, U1's seam assertion)
// =============================================================================

/// A plan that does not consume every owned reference exactly once on every
/// path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LinearityViolation(pub(crate) String);

/// The owned references held at a program point; `None` once the path has
/// left the body through a tail jump.
type Held = Option<BTreeSet<BinderId>>;

impl OwnershipPlan {
    /// Check, walking FORWARDS in evaluation order, that every owned reference
    /// of the body with `param_count` parameters is consumed exactly once on
    /// every path: no use or drop after consumption, branches that agree at
    /// every join, and nothing held when the body returns.
    ///
    /// A tail jump needs no special case: it ends its path, and nothing
    /// executes after it before the body's end, where nothing may be held.
    pub(crate) fn check_linearity(
        &self,
        body: &MonoExpr,
        param_count: usize,
    ) -> Result<(), LinearityViolation> {
        let mut held: BTreeSet<BinderId> = BTreeSet::new();
        for i in 0..param_count {
            if let Some(id) = self.binder_at(Intro::Param(i)) {
                self.hold(id, &mut held)?;
            }
        }
        let mut state = Some(held);
        self.check(body, &mut state)?;
        match state {
            Some(held) if !held.is_empty() => Err(LinearityViolation(format!(
                "binders {held:?} are still held when the body returns"
            ))),
            _ => Ok(()),
        }
    }

    fn hold(&self, id: BinderId, held: &mut BTreeSet<BinderId>) -> Result<(), LinearityViolation> {
        if !held.insert(id) {
            return Err(LinearityViolation(format!(
                "binder {id:?} introduced twice"
            )));
        }
        if self.dead_at_intro(id) {
            held.remove(&id);
        }
        Ok(())
    }

    fn consume(
        id: BinderId,
        held: &mut BTreeSet<BinderId>,
        what: &str,
    ) -> Result<(), LinearityViolation> {
        if held.remove(&id) {
            Ok(())
        } else {
            Err(LinearityViolation(format!(
                "{what} of binder {id:?}, which holds no reference here"
            )))
        }
    }

    fn read(
        &self,
        occurrence: Occurrence,
        held: &mut BTreeSet<BinderId>,
    ) -> Result<(), LinearityViolation> {
        match occurrence {
            Occurrence::Capture => Ok(()),
            Occurrence::Owned {
                binder,
                use_: Use::Move,
            } => Self::consume(binder, held, "move"),
            Occurrence::Owned {
                binder,
                use_: Use::Duplicate,
            } => {
                if held.contains(&binder) {
                    Ok(())
                } else {
                    Err(LinearityViolation(format!(
                        "duplicate of binder {binder:?}, which holds no reference here"
                    )))
                }
            }
        }
    }

    fn check(&self, node: &MonoExpr, state: &mut Held) -> Result<(), LinearityViolation> {
        let key = node_key(node);
        let Some(held) = state.as_mut() else {
            return Ok(());
        };
        match node {
            MonoExpr::IntLit { .. }
            | MonoExpr::FloatLit { .. }
            | MonoExpr::BoolLit { .. }
            | MonoExpr::StringLit { .. } => {}
            MonoExpr::Var { .. } => {
                if let Some(occurrence) = self.occurrences.get(&key) {
                    self.read(*occurrence, held)?;
                }
            }
            MonoExpr::Let { bindings, body, .. } => {
                for (index, (_, init)) in bindings.iter().enumerate() {
                    self.check(init, state)?;
                    if let (Some(held), Some(id)) = (
                        state.as_mut(),
                        self.binder_at(Intro::Let { node: key, index }),
                    ) {
                        self.hold(id, held)?;
                    }
                }
                self.check(body, state)?;
            }
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.check(cond, state)?;
                let branches = [then_branch.as_ref(), else_branch.as_ref()];
                self.check_branches(key, &branches, |_| Vec::new(), state)?;
            }
            MonoExpr::Match {
                scrutinee, arms, ..
            } => {
                self.check(scrutinee, state)?;
                let bodies: Vec<&MonoExpr> = arms.iter().map(|arm| &arm.body).collect();
                let slots: Vec<usize> = arms
                    .iter()
                    .map(|arm| pattern_binders(&arm.pattern).len())
                    .collect();
                self.check_branches(
                    key,
                    &bodies,
                    |arm| {
                        // Owned pattern binders, introduced at arm entry.
                        (0..slots[arm])
                            .filter_map(|slot| {
                                self.binder_at(Intro::Arm {
                                    node: key,
                                    arm,
                                    slot,
                                })
                            })
                            .collect::<Vec<_>>()
                    },
                    state,
                )?;
            }
            MonoExpr::Lambda { .. } => self.check_captures(key, held)?,
            MonoExpr::Apply { .. }
            | MonoExpr::VecLit { .. }
            | MonoExpr::ConstrADT { .. }
            | MonoExpr::ParBind { .. }
            | MonoExpr::LaunchContinue { .. } => {
                let sequence = self.operands(node);
                for (_, operand) in sequence.in_order() {
                    self.check(operand, state)?;
                }
                if sequence.continuation
                    && let Some(held) = state.as_mut()
                {
                    self.check_captures(key, held)?;
                }
            }
            MonoExpr::Trace { body, .. } => self.check(body, state)?,
        }
        self.check_post_drops(key, state)
    }

    fn check_captures(
        &self,
        key: usize,
        held: &mut BTreeSet<BinderId>,
    ) -> Result<(), LinearityViolation> {
        for entry in self.captures.get(&key).map_or(&[][..], Vec::as_slice) {
            self.read(entry.occurrence, held)?;
        }
        Ok(())
    }

    fn check_post_drops(&self, key: usize, state: &mut Held) -> Result<(), LinearityViolation> {
        if let (Some(held), Some(drops)) = (state.as_mut(), self.post_drops.get(&key)) {
            for id in drops {
                Self::consume(*id, held, "post-use drop")?;
            }
        }
        Ok(())
    }

    fn check_branches(
        &self,
        key: usize,
        bodies: &[&MonoExpr],
        pattern_ids: impl Fn(usize) -> Vec<BinderId>,
        state: &mut Held,
    ) -> Result<(), LinearityViolation> {
        let Some(start) = state.clone() else {
            return Ok(());
        };
        let mut joined: Option<Held> = None;
        for (branch, body) in bodies.iter().enumerate() {
            let mut held = start.clone();
            for id in self
                .scrutinee_drops
                .get(&key)
                .map_or(&[][..], Vec::as_slice)
            {
                Self::consume(*id, &mut held, "scrutinee drop")?;
            }
            for id in self.entry_drops(key, branch) {
                Self::consume(*id, &mut held, "branch-entry drop")?;
            }
            for id in pattern_ids(branch) {
                self.hold(id, &mut held)?;
            }
            let mut branch_state = Some(held);
            self.check(body, &mut branch_state)?;
            joined = Some(match (joined, branch_state) {
                (None, end) => end,
                (Some(None), end) | (Some(end), None) => end,
                (Some(Some(a)), Some(b)) if a == b => Some(a),
                (Some(Some(a)), Some(b)) => {
                    return Err(LinearityViolation(format!(
                        "branches of node {key:#x} disagree at the join: {a:?} versus {b:?}"
                    )));
                }
            });
        }
        // A match with no arms only reaches its panic.
        *state = joined.unwrap_or(None);
        Ok(())
    }
}

/// Planted faults for the linearity check's detection proof.
#[cfg(test)]
impl OwnershipPlan {
    /// Remove one branch-entry or introduction drop. Returns whether one existed.
    pub(crate) fn plant_missing_drop(&mut self) -> bool {
        if let Some(key) = self.entry_drops.keys().min().copied() {
            let drops = self.entry_drops.get_mut(&key).expect("key just read");
            drops.pop();
            return true;
        }
        if let Some(id) = self.dead_at_intro.iter().min().copied() {
            self.dead_at_intro.remove(&id);
            return true;
        }
        false
    }

    /// Turn one duplicate into a move. Returns whether one existed.
    pub(crate) fn plant_extra_move(&mut self) -> bool {
        let target = self
            .occurrences
            .iter()
            .filter(|(_, occ)| {
                matches!(
                    occ,
                    Occurrence::Owned {
                        use_: Use::Duplicate,
                        ..
                    }
                )
            })
            .map(|(key, _)| *key)
            .min();
        let Some(key) = target else {
            return false;
        };
        if let Some(Occurrence::Owned { use_, .. }) = self.occurrences.get_mut(&key) {
            *use_ = Use::Move;
        }
        true
    }
}

#[cfg(test)]
mod tests;
