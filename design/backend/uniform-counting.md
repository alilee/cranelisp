# Uniform reference counting (reading U′)

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`. Subordinate to
> [backend.md](backend.md).
>
> **Status**: adopted target design, **not built**. The user chose reading U′
> on 2026-11-15 ([S123 rulings](../../sprints/SPRINT.md)). Until `dev` lands it,
> the as-built counting rules are in [ring2-rc.md](ring2-rc.md),
> [ownership-codegen.md](ownership-codegen.md) §3, §6 and §13.3–§13.7,
> [transitive-drop-glue.md](transitive-drop-glue.md) §6,
> [binding-indirection-consume.md](binding-indirection-consume.md) and the
> tail-transfer section of [binding-scope.md](binding-scope.md). Each of those
> points here. When this design lands, the superseded sections are deleted in
> the same change-set, not annotated.
>
> **Authority**: `spec/12-runtime.md` §12.3.1 (release of unreachable values)
> and §12.4.3 (lenient evaluation is unobservable). The option framing is the
> [option paper](../arch/ownership-stratum-options.md) §3 with the
> [S123 architecture review](../../sprints/s123-architecture-review.md) §3.
> Principles governing the structure:
> [07](../arch/principles/07-single-source-of-truth.md),
> [11](../arch/principles/11-single-pipeline-mode-parameters.md),
> [24](../arch/principles/24-resolve-once.md) and
> [25](../arch/principles/25-narrowing-carries-its-check.md).

## 1. The rule

**Every binder owns one reference. On every path, each owned reference is
consumed exactly once: by a move at its last use, or by a drop where it
becomes dead. Every other use duplicates.**

- **A use is a consuming position.** Every position that receives a heap value
  consumes it: a call argument to any callee (user functions, closures, inline
  builtins, Vec operations, constructors, externs and platform effects), a
  `let` initialiser, a match scrutinee, a function or branch result, a
  tail-call argument, and a capture at closure or spark creation. There is no
  borrowing position. A read-only operation such as `vec-len` releases its
  operand after reading it.
- **Duplicate** means one increment at the use. **Move** means the slot's own
  reference travels and nothing is emitted. **Drop** means one release through
  the type's canonical glue (`emit_typed_rc_dec`, unchanged).
- **A binder becomes dead** immediately after its last use, immediately after
  its introduction if it has no use, and at the entry of a branch or arm that
  does not use it while another one does. A death that is not a last use is a
  drop at that point.
- **Nothing is released at scope exit or before a tail jump.** Every reference
  is already consumed by then, so the tail-call flushes and scope cleanup have
  no counting role.

### 1.1 The user's reading, confirmed with one refinement

The three statements the user gave hold as written, with one change to the
first:

| User's statement | In this design |
|---|---|
| Parameters are owned and released on exit | Owned, and released **where they die**, which is before exit for a parameter that is unused or used only on another branch |
| A caller that keeps a value increments it before the call; the last use moves without incrementing | Duplicate and move, applied to every consuming position, not only calls |
| A function returning an updated copy mutates in place when the count is 1 and clones otherwise | Rule U2 below, for every copy-on-write builtin |

**Why not release at exit.** A binder moved on one branch and not on the other
holds a reference at exit on one path only. Releasing at exit would need a
runtime flag per binder, or a fix-up at each branch end. Dropping it at the
entry of the branch that does not use it is the same release placed where the
path is still known. It also frees a dead alias before a later update, so
`(let [a v] (vec-set v 0 1))` updates in place instead of copying.

## 2. The closed list

Two rules are not uniform counting. Each preserves complexity and is defined
against a uniform reference that stays reachable, as Principle 25 requires.

| Rule | What it preserves | Uniform reference | Check |
|---|---|---|---|
| **U1 — last-use move**, with the death-point drops of §1 | A uniquely held value reaches a copy-on-write operation with count 1, so a direct or wrapped update loop is linear; dead values are freed as soon as they die | **Moves off**: every use duplicates, and a binder is dropped at its death point, so a last use becomes a duplicate followed by a drop. Correct and balanced, tail calls included; every update copies | Structural: one plan pass (§3) is the only producer of move, duplicate and drop decisions. Seam assertion: a debug-build linearity check of each body's plan (every owned reference consumed exactly once on every path) runs before emission. Differential: moves on and moves off agree on output and heap balance |
| **U2 — in-place update at count 1** | O(1) `vec-set` and `vec-push`, and the in-place arm of every COW builtin | **Always copy** | The runtime `rc == 1` probe is itself the check. The copy arm stays reachable, and under moves off it is always taken |

The static uniqueness proof that elides the probe
([ownership-codegen.md](ownership-codegen.md) §6.4) is retired: the probe is
one load and one compare, and the proof is a second opinion that can disagree
with it.

**A tail self-call has no counting rule.** It is a jump, which the language
requires for constant stack depth. Every reference is already consumed when the
arguments finish, so the jump releases nothing and overwrites the parameter
slots with the new arguments.

**Not in the list, and unchanged by this design.** These are representation,
placement or atomicity decisions, not counting, and none is implicated in the
faults in §6:

- the nullary-tag guard on `Mixed` values ([ring2-rc.md](ring2-rc.md) §2.2);
- canonical drop glue ([transitive-drop-glue.md](transitive-drop-glue.md));
- category before operation
  ([non-concrete-release-contract.md](non-concrete-release-contract.md) §3);
- stack placement for `NoEscape`, non-atomic RC for `Confined` and one-word
  value flattening ([ownership-codegen.md](ownership-codegen.md) §4, §5, §7),
  each with its existing analysis-off fallback;
- the IO node's release and the trampoline balance
  ([ring2-rc.md](ring2-rc.md) §3.5).

Whether to retire the stack-placement and `Confined` elisions too is an open
question for the user (§9).

## 3. Structure: one ownership plan per compiled body

- **The plan pass.** Before a body's emission, one pass walks its concrete
  body backwards in evaluation order and produces:
  - for each variable occurrence, the binder it denotes and **move** or
    **duplicate**;
  - for each binder introduction and each branch or arm entry, the binders
    dropped there;
  - for each closure or spark creation, one capture occurrence per captured
    binder, classified like any other occurrence.
- **The emitter reads the plan and decides nothing.** It increments on
  duplicate, emits nothing on move, releases on drop, and lowers every
  consuming position to consume its operand. No emission site inspects
  argument syntax, provenance or names to decide a count.
- **Binder identity is resolved once, by the plan** (Principle 24). The
  emitter maps the plan's binder identity to its `ScopeChain` slot and never
  resolves a name to decide ownership. The slot store and frame structure of
  [binding-scope.md](binding-scope.md) remain; its name-to-slot resolution
  becomes the plan's.
- **Evaluation order is defined once.** The plan and the emitter visit a
  node's children through one shared order definition, so "last" in the plan is
  last in the emitted code. This is the design's main dependency: a lowering
  that evaluates an operand out of that order would make a move precede a
  later duplicate of the same reference.
- **Plan facts are keyed by node identity within one body compilation.** The
  body is borrowed immutably for the whole compilation, so no pass can clone or
  rebuild a node underneath the key.
- **Order of passes.** Spark admission
  ([lenient-eval.md](lenient-eval.md)) runs first, because a sparked
  initialiser's free variables are captures at the binding position rather than
  occurrences inside it. Then the plan, then emission.
- **Nested bodies.** Each lambda, spark thunk, value-position wrapper and
  continuation body has its own plan. Its captures belong to its environment,
  whose drop glue releases them, so a use of a capture inside the body always
  duplicates.

## 4. Lowering by construct

| Construct | Lowering under §1 |
|---|---|
| Variable | Its plan entry: move, or duplicate |
| Call to any callee | Each argument is a consuming position. The callee owns every heap parameter and returns an owned result. A closure callee that is itself a temporary is consumed after the call |
| Inline read-only builtin (`vec-len`, `vec-get`, accessors) | Consumes its operand and releases it after reading; a projected element or field is duplicated before that release |
| Copy-on-write builtin (`vec-set`, `vec-push`) | The source is always owned (U2): in place at count 1, otherwise copy and release the source. The new element is consumed into the vector |
| Constructor | Each field argument is consumed into the new value |
| `let` | The initialiser's value is moved into the binder; the binder follows §1 |
| `if` | Each branch entry drops the binders live before the `if` and unused in that branch |
| `match`, constructor pattern | The match owns the scrutinee value. At arm entry it duplicates each bound field, then drops the scrutinee, then drops the arm's dead binders |
| `match`, variable pattern | The binder takes the scrutinee value itself: no duplicate, no drop |
| `match`, nullary or literal pattern | The scrutinee is dropped at arm entry |
| `fn` value or spark | One capture occurrence per captured binder at creation |
| Tail self-call | Arguments as for a call; then the jump. No flush |
| Function or branch result | A consuming position: the result is owned by the receiver |
| Extern and platform calls, IO combinators | Already consuming ([ring2-rc.md](ring2-rc.md) §3.3, §3.5); unchanged |

The variable-pattern row means there are no uncounted aliases, so the
last-use alias map in `heap.rs` has nothing to record.

## 5. What retires

Every row is a counting decision that the plan subsumes. The first thirteen are
the audit's deciders ([audit](../../audits/cranelisp-backend-s122.md) F4).

| Decider or mechanism | Replaced by |
|---|---|
| `value_provenance` and `yields_owned_temporary` | Every position consumes; nothing asks whether a value is a temporary |
| `independent_match_results` | Arm results are owned by §1 |
| `operand_live_binding_root` | The plan's binder identity |
| `compute_last_uses` and `register_alias` | The plan; there are no uncounted aliases (§4) |
| `slot_holds_frame_owned_reference` | Every binder owns |
| `tco_slot_disposition` and the §6 TCO predicate | No tail-jump releases |
| The consuming claims (`consuming_cow_arguments`, `return_cow_source_in_scope`) | U1's move gives the source its count |
| `scrutinee_lifetime_for_arm` and the per-arm release plan | §4's match rows |
| `has_cleanup_targets` in `protect_return_value` | Results are owned; no return protect |
| The skip in `pop_scope_with_cleanup` | Scope exit releases nothing |
| The `MonoExpr::Var` gates in `compile_consuming_arg_list` and `element_consuming_inc` | The plan entry |
| `tail_arg_protect` and `maybe_protect_tail_arg_alias` | No tail-jump releases |
| `protect_escaping_borrows_before_tail_jump` | No borrowed views |
| `SourceOwnership::Borrowed`, the static copy arm and the static uniqueness proof | U2 with an owned source |
| Borrow-elision emission and the borrow arm of `EntryConvention` | No borrowing position |
| Parameter promotion (FIXME 0720's entry increment) | No borrowed parameters |
| The capture-return increment and the closure-result protect | A capture used in a body is duplicated |
| The opt-in spark-capture borrow (`CRANELISP_CAPTURE_BORROW`) | Captures follow §1 |

The audit's two observed decider disagreements (F4) become unconstructable,
because one decider remains.

## 6. Coverage of the filed faults

Each row states why the design excludes the fault. None is measured yet; §8
lists the evidence that would.

| Filing | Shape | Under this design |
|---|---|---|
| [ACT-1030](../../sprints/actions/ACT-1030-let-wrapped-tail-forward-uaf-intake.md) | A `let`-wrapped tail argument forwards a borrowed alias with no reference | `alias` owns its reference; the jump releases nothing |
| [ACT-1029](../../sprints/actions/ACT-1029-alias-map-same-name-overwrite-lead.md) | A same-name alias overwrites the name-keyed alias map | No alias map; liveness is per binder identity |
| L2, borrowed pattern view through a branch | Root released at the jump | No borrowed views |
| L3, promotion read by name | A borrowed binder shadowing a promoted parameter is released at scope exit | No promotion |
| L4, borrowed parameter forwarded to another slot | The receiving slot is owned; nothing increments | No borrowed parameters |
| L5, nullary arm forwarding bare | No protect call | No protect needed |
| L6, heap-free nested scope | Return protect gated on cleanup targets | No return protect |
| L7, consuming COW unseen by the flushes | A `let`-bound or branch-nested COW source also released at the jump | No flushes |
| L9, `(vec-push v (vec-len v))` | Copy arm releases nothing while exit skips `v` | The first `v` duplicates; `vec-len` consumes the last; the push sees count 1 |
| L10, alias through a non-`Var` scrutinee | The alias does not extend its root's last use | No aliases |
| [ACT-1026](../../sprints/actions/ACT-1026-binder-forwarding-join-consumed-in-frame-leak-intake.md) | A forwarding join's value reaches `vec-len` unreleased | `vec-len` consumes its operand |
| [ACT-1028](../../sprints/actions/ACT-1028-let-bound-vec-set-returned-leak-intake.md) | `(let [w (vec-set v 0 5)] w)` returned leaks 1 | Every step consumes; predicted balanced. Its mechanism is unattributed, so a leak that survives is outside the counting rules and returns to `qa` |
| L8 | Refuted at S122 | Moot |

**The wrapper copy** ([carry triage](../../tests/plan/s123-carry-triage.md)
§8). Read at source: `compile_consuming_arg_list` increments every heap
variable argument, at its last use too, so the caller's reference survives
the call and the wrapper's update sees count 2. U1 moves it. **Prediction**,
asserted with a named falsifier: under this design the L1–L4 wrapper loops of
triage §8 take the in-place arm on every iteration. Falsified by any copy in
those loops.

**The 556-allocation residue under the toggle** (triage §8.2) is an
observation of the as-built analysis-off lowering. That lowering is replaced
(§7), so the residue is not an observable of this design. `qa` decides whether
it needs a filing before the change lands.

## 7. Landing shape

- **One change-set cuts emission over.** Old and new rules cannot coexist
  site by site, because a mix is unbalanced, and a second emission path is
  excluded by Principles 08 and 11. The superseded design sections and the
  retired source go in the same change-set.
- **The analysis-off toggle selects U1's uniform reference.** Under
  `CRANELISP_NO_OWNERSHIP` the plan classifies every use as duplicate and
  places a drop after each last use, and the analysis consumers outside
  the list keep their existing fallbacks. The toggle's cache key is unchanged
  (`CacheInvalidReason::OwnershipToggle`, `CacheManifest::ownership_disabled`),
  and `BUILD_ID` already invalidates objects from an earlier compiler.
- **No backend public API change is expected.** `dev` confirms with an
  unchanged baseline.
- **Cross-crate facts for `arch`, not deltas.** The backend stops reading
  borrow modes from `ModeSummary`, so those typecheck outputs lose their
  emission consumer (review §3.5; arch's follow-on packet). The toggle's
  meaning, as `cranelisp_types::ownership_analysis_off` documents it, widens
  to "moves off". Neither changes a signature.
- **Every golden-CLIF fixture changes.** Re-baselining is `qa`'s and `test`'s.

## 8. Evidence conditions for `qa`

- The ACT-1030 guard, ACT-1026's D1-M and D1-L, and a committed ACT-1028 cell
  GREEN armed with `CRANELISP_RC_DEC_CHECK`, with their controls balanced, in
  `--run`, `--link` and the REPL.
- The ACT-1029 R1 pair and the leads L2, L4–L7, L9 and L10 run once each as
  measured cells: armed, halves observed separately.
- A detection proof for the plan's linearity check: a planted missing drop and
  a planted extra move each fire, and the unplanted body stays silent.
- The moves-on/moves-off differential over the ownership generator, armed,
  with the generator's new axes (tail-argument shape, COW step, shadowing,
  consume position; audit R4).
- In-place counts: the direct and wrapper loops of triage §8 all in place, and
  the exemplar warm solve's in-place count reported beside its time.
- The cost measurement under the decision rule the user fixes beforehand
  (review §3.4): exemplar warm solve and the contention benchmark against
  current emission, and the full suite's wall time.

**Expected cost direction.** Moves remove the caller increments at every
last-use argument. Duplicates are added for each bound pattern field and for
each non-last use passed to a read-only builtin, where borrow elision skipped
them before. The net is unknown. The asymptotic claim, asserted with a
falsifier, is that this design takes the in-place arm wherever current emission
does: falsified by a workload whose in-place count falls.

## 9. Open questions

- **For the user: retire stack placement and `Confined` non-atomic RC too?**
  They read ownership facts but not for counting, and no filed fault involves
  them. Keeping them leaves two analysis consumers and their fallbacks.
  Retiring them is simpler and costs allocation and, under contention, atomic
  traffic. Recommendation: keep them in S123 and decide on the cost
  measurement.
- **Falsifiers this design carries.** A move followed by a duplicate of the
  same binder in emitted code (an evaluation-order mismatch); any
  counting decision in emission that reads something other than the plan.
