---
number: 0518
target: /dev            # cranelisp-typecheck (narrow)
filed_by: /arch
filed_at: 2026-07-04
sprint_filed: 102
refers_to: >
  crates/cranelisp-typecheck/src/ownership/transfer.rs (Walker.bindings, walk_var,
  param_root, drain_escaped, bind_pattern, drop_shadowed_provenance);
  crates/cranelisp-typecheck/src/ownership/confinement.rs (Confiner.param_idx);
  design/typecheck/ownership-inference.md §13.6(d)/(g)/(h)/(i), §5.3, §13.7;
  design/arch/ownership-inference.md §"The boundary" (boundary invariant);
  sprints/SPRINT.md §Notes 2026-07-04 (Wave 8c-R F4)
status: open
---

# F4 — the pass5 ownership walker must model lexical scope (Wave-8c-R2 cure)

## Ruling summary (the four questions the Wave-8c-R brief posed)

**Severity — SOUNDNESS, ABI-bearing. /dev is right; /review's "precision-only" is refuted.**
F4 flips a `param_modes` entry from `Owned` (truth) to `Borrowed` (narrowed) in the current
code, reachable by a real (non-synthetic-span) `MonoExpr`. `param_modes` is exactly the ABI
half `ModeSummary::abi_eq` compares (`crates/cranelisp-types/src/ownership.rs:192-195` compares
`param_mode(i)` + `result` only). The narrowing rides the *symbol-keyed* `bindings` map, not any
span-keyed fact, so span synthesis is irrelevant — it is reachable regardless.

**MonoExpr invariant — NONE.** `MonoExpr::from_expr` copies binding names verbatim (`n.clone()`)
at every `Let`/`Lambda`/`Match`/`ParBind` seam (`crates/cranelisp-types/src/mono_expr.rs:337-345,
353-357, 378-390, 412-417`); monomorphisation substitutes types, not names; the frontend's only
renaming is opt-in `x#` auto-gensym in quasiquote templates. The walker MAY NOT rely on
binding-name uniqueness. Boundary-invariant pinned in `design/arch/ownership-inference.md`
§"The boundary".

**Root-cause verdict — root cure, not another seam patch.** B1 (single-level drain), B3
(match-seam shadow-drop mirror), F4 (unscoped map) are the third instance of one class: the
walker does not model lexical scope. Per `feedback_review_root_cause_and_duplication` (P7/P8),
recurrence mandates a root cure: a single scope-discipline refactor of the walker
(save/restore of shadowed `bindings` on scope entry/exit).

**Cure placement — (a) walker-internal scope save/restore. Contained in `cranelisp-typecheck`;
NO `cranelisp-types` edit.** Rejected (b) MonoExpr alpha-rename invariant: larger surface, a
schema-relevant commitment on a serialised boundary type, for a bug local to one walk
(Principle 8; Principle 7 — the boundary type should not absorb a burden the one consumer can
carry).

**Does F4 gate Wave 11? YES** — same tier as 0512. It is latent at the current seam (nothing
consumes `param_modes` for emission until Wave-11 mechanisms + the R3 `AbiSurface` mode-vector
widening land), so golden diff is EMPTY today; it becomes a UAF/double-free the moment a
mechanism treats the narrowed `Borrowed` as "no retain". Must land **before** Wave 11.

---

## Issue — the concrete trace

`Walker.bindings: HashMap<Symbol, BindState>` is flat and never scope-restored. `Let`
(`transfer.rs:287`), `ParBind` (`:351`), and match-arm `bind_pattern` (`:527`) INSERT bindings
but never remove them on scope exit. A name shared between a param/outer binding and a
**branch-sibling** inner binding leaks the stale inner `BindState` past its lexical scope.

Reachable shape (well-typed; param `a` non-`Copy`, shadowed in one `if` branch, used in the
sibling branch):

```
(defn f [a g] (if c (let [a (gcells g)] (use a))   ; then-branch: shadows param a
                    (consume a)))                   ; else-branch: means the PARAM a
```

Trace in current code:
1. `walk(If)` walks `then_branch` first (`:298`). The inner `(let [a …] …)` does
   `drop_shadowed_provenance(a)` then `bindings.insert(a, {origin: Projection/Fresh,
   param_idx: None})` — **overwriting the param entry for `a`**. No restore on let exit.
2. `walk(else_branch)` → `(consume a)`. `walk_var(a, Arg{Owned,..})` reads `bindings[a]` = the
   leaked INNER state. `param_root(a)` (`:182`) sees `param_idx: None`, origin `Projection`/
   `Fresh` → returns `None` → `classify_param_use` (`:375`) is **never called**.
3. `param_modes[0]` stays `Borrowed`. Truth is `Owned` (the param is consumed in the else
   branch). `Borrowed ⊏ Owned` → narrowing below truth → Wave-11 elides the retain → early
   free → UAF/double-free.

The direction is always a narrowing (a *missed* widen), never a spurious widen, so it is purely
unsound-below-truth — no false-positive offsets it.

**Sibling walker — confinement is SOUND, do not confuse the two.** `Confiner.param_idx`
(`confinement.rs:62`) has the same scope-unawareness, but its direction is opposite: a shadowed
name spuriously matching a param sets `spark_ops[i] = true` (Crossing/atomic) — an
over-approximation toward ⊤, which is sound. Shadowing only ADDS false matches to confinement;
it never removes a real one. So confinement is not a Wave-11 soundness blocker. Apply the same
scope discipline there for precision + to stop the class recurring in a sibling walker, but it
is not gating (lower priority).

## Proposed resolution — the scope-stack mechanism

Give the `Walker` a scope-frame stack so binding-name resolution is lexically faithful. The
transfer walk is the soundness-gating target; confinement gets the same treatment for precision.

**What is saved / when.** On entering a binding scope (`Let`, `ParBind`, each `Match` arm), for
every name the scope binds, record `(name, prior: Option<BindState>)` where `prior` is the
value `bindings` held for that name *before* insertion (`None` if unbound). On scope EXIT, replay
in reverse: `Some(old)` ⇒ reinsert `old`; `None` ⇒ remove. Params are the base frame and are
never restored away. A `Vec<(Symbol, Option<BindState>)>` per scope frame is sufficient.

**LET/LET* ordering is already correct — preserve it.** The current loop walks each RHS BEFORE
inserting that binding (`:284` then `:287`), and inserts each binding before the next RHS, so
`[a (Some x) b (Some a)]` correctly sees `a` when walking `b`'s RHS (sequential-let). Keep this;
only add the frame push (before the loop) and the frame restore (after `drain_escaped`, at
`Let`/`ParBind` exit).

**Match arms each get their own frame.** `bind_pattern` currently leaks arm N's bindings into
arm N+1 and past the match — the same class. Push a frame at arm entry, restore at arm exit
(before walking the next arm). This subsumes the arm-leak half of F4.

**Interaction with the F1 drain (`drain_escaped`).** The drain re-walks binding RHSs after the
body walk and must resolve each RHS's free vars in that RHS's *defining* scope (enclosing +
this-let's earlier bindings, but NOT the binding being drained itself). Run the drain BEFORE the
frame restore (enclosing + this-let bindings still live). For the self-alias RHS (`(let [a a] …)`,
the `case`/`cond` macro shape), re-walk each RHS with the binding-being-drained temporarily
restored to its shadowed (`prior`) value, so `var(a)` resolves to the OUTER `a`, not itself —
which is the correct sequential-let reading and removes the infinite re-push at its root.

**The `(name, ctx)` dedup in `drain_escaped` — role downgraded, retirement OPTIONAL.** That
dedup exists today to paper over the self-alias non-termination that the unscoped map causes
(`transfer.rs:472-503` + §13.6(g) doc). Once the drain re-walks RHSs in their defining scope
(above), the self-alias no longer self-resolves, so the dedup is no longer *load-bearing for
termination* — it degrades to a defensive bound. `/dev` MAY retire it (preferred — it is a
Principle-7 win, the workaround retires with its cause) or keep it as a pure defensive cap; if
kept, record it as defensive, not as the termination mechanism.

**B1 drain fixpoint and B3 shadow-drop STAY.** They address different problems and must not be
removed by this refactor:
- **B1** (`drain_escaped` fixpoint) is escape *propagation* (forward info), orthogonal to name
  resolution. Scope discipline only removes its self-alias termination hazard.
- **B3** (`drop_shadowed_provenance` at Let + `bind_pattern`) is the sound conservative action
  at a genuine *cross-boundary* Symbol collision: provenance leaves the walk as a bare `Symbol`
  (`MonoExpr` `provenance: Option<Symbol>`) that the backend re-resolves against its own
  `borrowed_vars`. Scope discipline makes the walker's *detection* of "is this root shadowed
  here" precise, but the drop-to-`None` (⇒ Decision-24 materialize) stays as the boundary-safe
  behaviour. Keep it; do not assume the scope-stack retires it.
- **B4** (cap-exhaustion ⊤ reset, §13.6(h)) is untouched.

## Failing-cell-first — the negative cell + witnesses

**The branch-sibling ABI-narrowing negative cell (write it first, RED before the fix).** In
`transfer.rs` `#[cfg(test)] mod tests`, build the `MonoExpr` for
`(if c (let [a <fresh>] (use a)) (consume a))` with `params = [(a, String)]` (non-`Copy`) and a
`TransferEnv` fixture where `consume`'s summary has `param_mode(0) == Owned`. **Order matters:**
the shadowing `let` MUST be in the branch walked first (then-branch) and the bare param use in
the sibling (else-branch) — that is the ordering the walker exhibits. Assert
`result.summary.param_modes[0] == Mode::Owned`. RED today (`Borrowed`); GREEN after the cure.
Add the twin where the shadow is in the else-branch and the param use in the then-branch (the
cure must fix both orderings). Add a match-arm variant:
`(match g [(Box a) (use a)] [_ (consume a)])` with param `a` — arm-binding leak, same assertion.

**Witnesses that MUST hold (the Wave-8c/8c-R soundness contract):**
- **Golden CLIF diff EMPTY** across all pre-existing intentional guards (the cure is
  emission-neutral at the current seam — nothing consumes `param_modes` for emission yet).
- **Toggle-off field-identical** (`CRANELISP_NO_OWNERSHIP` set) — the cure lives entirely inside
  the gated `run_pass5` region.
- **ABI half now CORRECT for the branch-sibling shape** — the new cells above are GREEN
  (`param_modes[0] == Owned`), and add a same-shape `check_forms`/`TestFixture` e2e cell if the
  shape is facade-reachable, so the fix is pinned at both the unit seam and the pass seam.
- **Self-alias terminates without the dedup being load-bearing** — a cell building
  `(let [__case__ __case__] …)` (or driving the `case` macro through `TestFixture`) completes
  (no hang) and, if the dedup is retired, still terminates via scope discipline alone.
- **Precision twins hold** — the never-escaping local-aggregate and unshadowed-provenance twins
  that Wave-8c/8c-R added stay GREEN (no regression toward over-widening).

**Baseline expectation:** fail set stays EXACTLY the pre-existing intentional guards (13 at the
Wave-8c-R baseline `3770 / 3757 / 13 / 1`), plus the new green cells. No genuine RED beyond the
named guards.

## §13.6(i) correction (design/typecheck/ — /typecheck-owned; action as part of this FIXME)

§13.6(i) currently records F4 as an *observation* ("recorded, NOT actioned"). On resolution,
rewrite it as the actioned cure and reconcile the neighbouring sections:
- **§13.6(i):** state the scope-save/restore mechanism (frame stack; save shadowed `BindState`
  on `Let`/`ParBind`/`Match`-arm entry, restore on exit); severity = ABI-half soundness
  (not precision); confinement's opposite-direction over-approximation is sound and gets the
  same discipline for precision only; F4 is the third instance of the scope-modeling class and
  this is its root cure.
- **§13.6(g):** strike the "residual precision gap" self-aliasing-shadow-chain caveat
  (`(let [a (Some x)] (let [a a] a))`) — scope discipline reaches the outer binding, so the
  masking is gone. Record whether the `(name, ctx)` dedup was retired or downgraded to
  defensive.
- **§13.6(d):** note that scope discipline makes shadow *detection* precise, and the
  `drop_shadowed_provenance` drop stays as the cross-boundary Symbol-collision safe action.
- **§13.7 (`transfer.rs` matrix):** add the branch-sibling ABI-narrowing negative cell + its
  both-orderings twin + the match-arm-leak cell + the self-alias-terminates cell to the mode/
  flow-join and projection-depth matrices (P23 — the strategy's scenario space named).

## Operational implication / Context

- **Gates Wave 11** (ABI-half soundness precondition, same tier as 0512). Land in the Wave-8c-R2
  change-set before backend mechanisms consume summaries. The R3 `AbiSurface` mode-vector
  widening (currently a pre-Wave-11 item) must not fold in a narrowed `param_modes`.
- **No `cranelisp-types` edit**, no `CACHE_SCHEMA_VERSION` bump, no facade/public-api change —
  the cure is crate-interior to `cranelisp-typecheck`. If implementation surprisingly needs a
  boundary change, STOP and file `target: /arch` before publishing.
- **One agent, source-touching, serial** (shared working tree). Same-file contention: this
  touches `ownership/transfer.rs` (+ optionally `confinement.rs`); coordinate with any other
  open ownership change-set.
