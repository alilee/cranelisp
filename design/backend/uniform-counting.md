# Uniform reference counting (reading U′)

> **Owner**: `design`, narrow-deployed to `cranelisp-backend`. Subordinate to
> [backend.md](backend.md).
>
> **Status**: **built** at the S123 W2 cutover (reading U′, chosen by the user
> on 2026-11-15). This is the backend's one counting design. The sections it
> replaced are deleted from [ring2-rc.md](ring2-rc.md),
> [ownership-codegen.md](ownership-codegen.md),
> [transitive-drop-glue.md](transitive-drop-glue.md),
> [non-concrete-release-contract.md](non-concrete-release-contract.md) and
> [binding-scope.md](binding-scope.md); cited section numbers stay there as
> one-line retirement stubs. §3.2 (operand order) and §3.3 (wrapper template)
> are built. `qa` judged the W2 evidence adequate on 2026-11-16, and U′ is
> within the user's cost bound (`tests/plan/s123-evidence-delta.md` §3.9 and
> §3.10). [Section 8](#8-evidence-conditions-for-qa) lists the conditions
> that evidence answers. Under
> [Principle 27](../arch/principles/27-dev-tier-optimises-only-against-blow-up.md)
> rules U1 and U2 are the dev tier's kept optimisations: each holds an update
> loop's growth rate.
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
| **U1 — last-use move**, with the death-point drops of §1 | A uniquely held value reaches a copy-on-write operation with count 1, so a direct or wrapped update loop is linear; dead values are freed as soon as they die | **Moves off**: every use duplicates, and the binder whose last use it was is dropped once the receiving position has taken the value (§2.1). Correct and balanced, tail calls included | Structural: one plan pass (§3) is the only producer of move, duplicate and drop decisions. Seam assertion: a debug-build linearity check of each body's plan (every owned reference consumed exactly once on every path) runs before emission; its detection proof is the plan's module tests. Differential: §2.1 |
| **U2 — in-place update at count 1** | O(1) `vec-set` and `vec-push`, and the in-place arm of every COW builtin | **Always copy** | The runtime `rc == 1` probe is itself the check. The copy arm stays reachable; under moves off every update whose source is a variable operand takes it (§2.1) |

### 2.1 Moves off, and what the differential claims

As built, moves off places the drop by where the value goes:

- **An operand** (call argument, builtin operand, constructor field). The
  binder is dropped after the consumer has run. The consumer sees the
  duplicate and the binder's own reference, so a COW update **copies**.
- **A scrutinee.** The binder is dropped at every arm entry, once the arm
  holds the scrutinee value.
- **A result position** (a `let` initialiser, a branch or arm result, a body
  result). The binder is dropped as soon as the variable has been evaluated.
  The value then travels with the binder's count, so a value forwarded through
  a branch, `let` body or arm reaches a later COW operand as a temporary and,
  at count 1, **updates in place**. For example, `(vec-set (if c v w) 0 1)`
  updates in place under both toggles when `v` is unshared.

**Decision (S123 W2).** The claim that every update copies under moves off is
withdrawn. It was a consequence of the first wording, not a requirement. No
rule depends on it, because U2's probe is sound whichever arm it takes. Making
it hold would need a result-position drop deferred to the eventual consumer
through every branch and binding, which is a second placement rule kept only to
make the oracle copy.

What the moves-on/moves-off differential claims:

- the two legs agree on program output;
- each leg is heap-balanced on its own, armed with `CRANELISP_RC_DEC_CHECK`;
- the linearity check is silent on both.

It claims nothing about in-place counts. The legs differ in in-place counts by
design, so a difference there is not a finding. The copy arm stays exercised
under moves off at every variable operand.

### 2.2 No static uniqueness proof

The static uniqueness proof that elided the probe is retired. The probe is one
load and one compare, and the proof was a second opinion that could disagree
with it.

### 2.3 Tail self-calls

**A tail self-call has no counting rule.** It is a jump, which the language
requires for constant stack depth. Every reference is already consumed when the
arguments finish, so the jump releases nothing and overwrites the parameter
slots with the new arguments.

**A tail call is a self-call only when the plan does not evaluate its callee.**
A callee the plan evaluates is a local or captured binder, or a computed
expression. That callee is a closure value, so the call is a closure call, even
when the binder is spelled like the enclosing function. Shadowing
(`spec/04-expressions.md` §4.3) makes the local binder the call's target.

- **Why the plan decides (decision, S123 W2).** An evaluated callee is a
  consuming occurrence the plan has classified. A jump would skip it and leave
  the plan unbalanced. The emitter therefore asks the plan, through the one
  shared predicate the plan uses for callee evaluation.
- **As built, narrower than one source of truth.** One other reader of the
  self-call predicate does not ask the plan: the spark SCC classifier. It can
  count a shadowed local call as self-recursive. Converging both readers on
  the plan's answer is `dev`'s follow-up.

### 2.4 Outside the list

These are representation, placement or atomicity decisions, not counting, and
none is implicated in the faults in §6:

- the nullary-tag guard on `Mixed` values ([ring2-rc.md](ring2-rc.md) §2.2);
- canonical drop glue ([transitive-drop-glue.md](transitive-drop-glue.md));
- category before operation
  ([non-concrete-release-contract.md](non-concrete-release-contract.md) §3);
- one-word value flattening ([ownership-codegen.md](ownership-codegen.md) §7),
  with its analysis-off fallback;
- the IO node's release and the trampoline balance
  ([ring2-rc.md](ring2-rc.md) §3.5).

**Placement mechanisms leave the dev tier.** Stack placement and value
flattening change only a constant, so Principle 27 retires them in S124
(stack placement at B1), and
non-atomic RC for `Confined` retired at S123 W4
([ownership-codegen.md](ownership-codegen.md) §0, §5). Confined counting
already had no consumer under U′: its only emission site was the return
protect's increment, which §5 retires. Every emitted RC operation is atomic,
except the inline helpers under the unsound `CRANELISP_NONATOMIC_RC` probe
([ownership-codegen.md](ownership-codegen.md) §5.2).

## 3. Structure: one ownership plan per compiled body

- **The plan pass.** Before a body's emission, one pass walks its concrete
  body backwards in evaluation order and produces:
  - for each variable occurrence, the binder it denotes and **move** or
    **duplicate**;
  - for each binder introduction and each branch or arm entry, the binders
    dropped there;
  - for each closure creation, one capture occurrence per captured binder,
    classified like any other occurrence. Spark thunks are §3.1.
- **The emitter reads the plan and decides nothing.** It increments on
  duplicate, emits nothing on move, releases on drop, and lowers every
  consuming position to consume its operand. No emission site inspects
  argument syntax, provenance or names to decide a count. The one body without
  a plan is a generated wrapper, whose counts §1 fixes in advance (§3.3).
- **Binder identity is resolved once, by the plan** (Principle 24). The
  emitter maps the plan's binder identity to its `ScopeChain` slot and never
  resolves a name to decide ownership. The slot store and frame structure of
  [binding-scope.md](binding-scope.md) remain; its name-to-slot resolution
  becomes the plan's.
- **Evaluation order is defined once** (§3.2), so "last" in the plan is last
  in the emitted code. This is the design's main dependency: a lowering that
  evaluates an operand out of that order would make a move precede a later
  duplicate of the same reference.
- **Plan facts are keyed by node identity within one body compilation.** The
  body is borrowed immutably for the whole compilation, so no pass can clone or
  rebuild a node underneath the key.
- **Order of passes.** The plan, then emission. Spark admission
  ([lenient-eval.md](lenient-eval.md)) does not change the plan's input; the
  plan reads a sparked subtree in its sequential position.
- **Nested bodies.** Each lambda, spark thunk and continuation body has its
  own plan. Its captures belong to its environment, whose drop glue releases
  them, so a use of a capture inside the body always duplicates. Generated
  wrappers follow the forwarding template instead (§3.3).

### 3.1 Spark thunks (decision, S123 W2)

A lenient spark's thunk is a clone of the sparked subtree that the backend
synthesizes during emission. The plan never saw that clone, so its node keys
are not plan keys. As built:

- **Every capture of a spark thunk duplicates.** The frame keeps its
  references while the spark runs.
- **The frame drops at the forcing point.** After the force, the frame drops
  exactly the binders whose references the sequential evaluation of that
  subtree would have consumed (the plan's moves and drops inside it, less the
  binders it introduces). Both arms of the create gate therefore consume the
  same references, and the drop set still comes from the plan alone.

The first wording moved a capture at its last use instead. The as-built form
is adopted:

- **It keeps one plan.** The plan reads one body in one evaluation order. A
  plan over the synthesized thunk would need spark admission to run first and
  rewrite the plan's input, which would give the plan's key two shapes.
- **It costs no in-place update.** Inside a thunk a capture use duplicates
  under either form (above), so a COW on a captured value copies either way.
- **Its cost.** One increment and one release per moved capture per spark, and
  a value dead inside a sparked subtree lives until the force rather than until
  the spark ends. Spark count is bounded by the create-gate budget.

Balance across the lenient and sequential arms is measured by the parallel ≡
serial fixtures with heap balance (`tests/s99_fixtures.rs`). It stays asserted
beyond them. Falsifier: a sparked initializer that is unbalanced under the
armed check while the same program under `CRANELISP_NO_LENIENT` balances.

### 3.2 Operand order (decision, S123 W2)

The order in which a node consumes its operands has one definition. The plan,
the linearity check, `consumed_within` and the emitter all read it. Each
lowering of these nodes receives its operands as values and never evaluates an
operand expression itself.

| Node | Operand sequence, in evaluation order |
|---|---|
| Apply, every dispatch arm (static, GOT, extern, platform, builtin, IO combinator, closure call, auto-curry, tail self-call) | The callee when `callee_is_evaluated` holds, then the arguments left to right |
| Vec literal | Elements left to right |
| Constructor | Fields left to right |
| `par-bind` | Binding expressions left to right, then the continuation's capture point |
| Launch-continue | The launched expression, then the continuation's capture point |

- **Its readers.** The plan walks the sequence backwards. The check and
  `consumed_within` walk it forwards. The emitter's one operand evaluator walks
  it forwards and returns the values. The lenient force barrier stays inside
  the evaluator, at the operand's position.
- **What `dev` removes.** The per-kind child loops in the three plan walks, the
  tail self-call's own argument loop, the Vec literal's element loop, and every
  call that passes an argument slice to an evaluator. The order test that
  walks its own miniature traversal is not evidence of agreement. `dev`
  replaces it with the §8 cells.
- **Nodes outside the sequence.** Branching and binding nodes order their
  children by construction, so they need no shared sequence.
  - A condition or scrutinee is evaluated in the block that branches on it.
  - A `let` binder is published only after its initializer
    ([binding-scope.md](binding-scope.md)). An occurrence of an unpublished
    binder is a located codegen error, because emission reaches a binder only
    through its plan identity.
  - A closure's captures are taken at one program point, one per name, so
    their relative order cannot place a move before a duplicate.
  - `trace` has one child.
- **Grade.** Structural for the operand-list nodes. Reordering their emission
  means editing the one definition, and the plan moves with it. Two faults
  remain expressible, each a local edit at one site: iterating the evaluator's
  values in another order, or evaluating an operand expression directly. The
  §8 cells, with their detection proof, measure both. The order of the
  branching and binding nodes is asserted, with the §9.2 falsifier.
- **Rejected: a detective order check in emission.** It would record each
  occurrence as emission reaches it and compare that order with the plan. Doing
  so needs path-sensitive bookkeeping across Cranelift blocks: a second walker
  that would itself need a detection proof, running on every debug compile. The
  shared sequence removes the fault it would detect, at lower cost.

### 3.3 Generated wrappers: the forwarding template (decision, S123 W2)

A generated wrapper builds no plan. Every one is admitted as one fixed
template, the counts §1 gives the only body a wrapper can have. This covers the
function-as-value wrapper, the trait-method-as-value wrapper and the
auto-curry wrapper.

- **Shape.** The body is one saturated call of the wrapper's target. Its
  arguments are the environment's applied captures in capture order, then the
  wrapper's parameters in order. Nothing else is evaluated, bound or branched
  on. The call's lowering is the first applicable rule of
  [compile-to-module.md](compile-to-module.md) §12, or the closure-value call
  for a curried closure.
- **Counts**, as the plan would give `(fn [p…] (target c… p…))` with
  environment captures `c…`:
  - **Each parameter moves.** It is used once, and that use is its last.
  - **Each applied capture duplicates**, with one increment by its heap
    category. A capture use always duplicates (§3).
  - **A curried closure-value target is called with the environment's
    reference.** The plan would duplicate that capture and release it after
    the call (§4, call row). The environment keeps the target alive across the
    call, so the template emits neither.
  - **The target consumes every argument.** Every §12 rule and the
    closure-value call do, as direct application does (§4).
- **One assembly site.** One template function builds the argument vector and
  emits the template's increments. It is the only RC emission in a wrapper
  body, and all three wrappers call it. Function and trait-method values pass
  no captures. The curry wrapper's direct capture increment moves into this
  function.
- **The creation side is planned.** The curry closure's applied arguments and
  a closure-value target are ordinary operands of their Apply (§3.2). Only the
  wrapper's body is templated.
- **Both polarities.** The template is the same under moves off. A planned
  body would duplicate each parameter and drop it after the call, which changes
  only in-place counts. §2.1 claims nothing about those.
- **Why not plan wrappers.** A plan needs a typed body to walk. Three of the
  call's lowerings have no expression form: the closure-value call through
  `CODE_PTR`, the inline constructor and the inline Vec operation. Building one
  would mean synthesizing a body per wrapper and compiling it through a second
  body compiler. The result would be a plan whose answer is the constant
  above.
- **Grade.** The shape is structural: one assembly site. The counts are
  measured by the §8 wrapper cells, with their detection proof. This narrowing
  carries its own check, as Principle 25 requires.
- **Trigger to plan wrappers instead.** A wrapper body that needs a binder, a
  branch, a second use of a parameter, or a target that does not consume an
  argument.

### 3.4 Typing obligations of a planned body

The plan is type-blind: it counts references by binder. Emission discharges
each decision by a type, either the binder's recorded type or the type of the
node it reads. A position typed as non-owning therefore turns a planned drop
into no release, while the linearity check stays silent. That is the shape of
both open findings on synthetic bodies: an accessor's lost input release
(G-1), and the in-place `vec-set` that strands an owning old element (R1).

The obligations hold for every planned body. They bind most on bodies that the
pipeline synthesizes rather than the user writes: field accessors, constructor
bodies and trait-method instances.

1. **Parameters carry their signature's concrete type.** The frame takes each
   parameter's type from the body's signature, and every binder records a
   concrete type; an occurrence is not a source. A missing signature type is
   a located refusal that the census counts
   ([release contract](non-concrete-release-contract.md) §7.3, §7.4 step 2;
   built at S124 B4).
2. **A counted node agrees with its binder.** A scrutinee, operand or result
   occurrence carries the same concrete type as its binder's record. The
   scrutinee release reads the node and a drop reads the binder, so both must
   classify alike.
3. **Field types come from the constructor**, as the keyed field types
   instantiated at the scrutinee's concrete type. They never come from the
   accessor's result type.
4. **Counted positions are concrete.** The residual-variable faces of
   FIXME 0903, a generic accessor's `self` and generic trait-method instances,
   stay under
   [non-concrete-release-contract.md](non-concrete-release-contract.md), whose
   shallow-release arm was deleted at S124 B4; no fix may reintroduce one.
5. **An owned element is released by its type** (R1).
   - An operation that discharges an element it owns releases that element
     through the element type's canonical glue. For example, the in-place
     `vec-set` arm releases its overwritten element.
   - The release comes from the same element-release source that the copy
     arm's callback uses (Principle 07).
   - Where the element type owns heap but is unknown at the site, emission
     raises a located error instead of skipping the release. This includes the
     value-position and curry `vec-set` wrappers, which recover the element
     type from the value's function type.

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
| `fn` value | One capture occurrence per captured binder at creation |
| Lenient spark | Every capture duplicates; the frame drops at the forcing point (§3.1) |
| Tail self-call | Arguments as for a call; then the jump. No flush. A callee the plan evaluates is never a self-call (§2.3) |
| Function or branch result | A consuming position: the result is owned by the receiver |
| Extern and platform calls, IO combinators | Already consuming ([ring2-rc.md](ring2-rc.md) §3.3, §3.5); unchanged |

The variable-pattern row means there are no uncounted aliases, so the
last-use alias map in `heap.rs` has nothing to record.

## 5. What retires

Every row is a counting decision that the plan subsumes, and all are deleted
from source. The first thirteen are the audit's deciders
([audit](../../audits/cranelisp-backend-s122.md) F4). The table maps an old
name met in a record or comment to what replaced it.

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

Each row states why the design excludes the fault. `qa` confirmed the faults
live before the cutover; none is yet measured against it, and §8 lists the
evidence that would.

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
§8). Before the cutover the caller incremented every heap variable argument,
at its last use too, so the caller's reference survived the call and the
wrapper's update saw count 2. U1 moves it. **Prediction**, asserted with a
named falsifier: the L1–L4 wrapper loops of triage §8 take the in-place arm on
every iteration. Falsified by any copy in those loops. `qa` measured 0 of 999
in place before the cutover.

**The 556-allocation residue under the toggle** (triage §8.2) was an
observation of the retired analysis-off lowering, so it is not an observable
of this design.

## 7. As landed

- **One change-set cut emission over.** Old and new rules cannot coexist site
  by site, because a mix is unbalanced, and a second emission path is excluded
  by Principles 08 and 11. The retired source and the superseded design
  sections went together.
- **The analysis-off toggle selects U1's uniform reference** (§2.1). Stack
  placement reads no facts under it. The toggle's cache key is unchanged
  (`CacheManifest::ownership_disabled`), so a cache written in one polarity is
  never loaded in the other, and `BUILD_ID` invalidates objects from an earlier
  compiler.
- **No backend public API change.** `dev` reported `public-api.txt` +0 at
  the cutover and at each W2 fix.
- **Cross-crate facts for `arch`, not deltas.** The backend no longer reads
  borrow modes from `ModeSummary`, so those typecheck outputs have no emission
  consumer (review §3.5; arch's follow-on packet). The toggle's meaning, as
  `cranelisp_types::ownership_analysis_off` documents it, widens to "moves
  off". Neither changes a signature.
- **The golden-CLIF corpus was re-baselined** by `test`, with attribution, in
  the same wave.

## 8. Evidence conditions for `qa`

- The ACT-1030 guard, ACT-1026's D1-M and D1-L, and a committed ACT-1028 cell
  GREEN armed with `CRANELISP_RC_DEC_CHECK`, with their controls balanced, in
  `--run`, `--link` and the REPL.
- The ACT-1029 R1 pair and the leads L2, L4–L7, L9 and L10 run once each as
  measured cells: armed, halves observed separately.
- A detection proof for the plan's linearity check: a planted missing drop and
  a planted extra move each fire, and the unplanted body stays silent. The
  check proves the recorded plan linear. It cannot see emitted order (§3.2),
  wrapper bodies (§3.3) or a release lost to a type (§3.4), so the next three
  conditions are separate.
- **Operand order (§3.2).** Cells that run armed in both polarities, for
  example one per row of the §3.2 table. Each reuses a binder twice within one
  operand sequence, first as a duplicate and then as a move, such as
  `(add-i64 (vec-len v) (vec-len v))`. Each balances and gives the right
  output.
  - Detection proof, positive leg: reversing only the emitter evaluator's
    iteration turns the Apply cell RED under the armed check.
  - Negative leg: reversing the shared sequence itself leaves every cell
    green, because the plan and the emitter move together.
- **Wrapper template (§3.3).** Cells that run armed in both polarities:
  - a curried heap capture called twice, such as
    `(let [g (f [1 2])] (add-i64 (g 1) (g 2)))`;
  - a curried closure-value target;
  - a function value over a consuming heap target;
  - a trait method used as a value with a heap argument;
  - a constructor used as a value with a heap field.

  Detection proof: removing the template's capture increment fires the armed
  check in the first cell, a second increment leaves an allocation
  outstanding, and the unplanted template balances.
- **Typing obligations (§3.4).** Armed, in both polarities:
  - accessors over a scalar-field product and over an owning-field product,
    such as the golden `Point.x` and `Box.items`;
  - in-place `vec-set` over an owning element: a nested Vec, a closure and a
    heap ADT.

  Each balances. A balanced flat-String `vec-set` is a control, not coverage
  of the owning case.
- The moves-on/moves-off differential over the ownership generator, armed,
  with the generator's new axes (tail-argument shape, COW step, shadowing,
  consume position; audit R4).
- In-place counts: the direct and wrapper loops of triage §8 all in place, and
  the exemplar warm solve's in-place count reported beside its time.
- The cost measurement under the decision rule the user fixes beforehand
  (review §3.4): exemplar warm solve and the contention benchmark against
  the pre-cutover emission (`f5822487`), and the full suite's wall time.

**Expected cost direction.** Moves remove the caller increments at every
last-use argument. Duplicates are added for each bound pattern field and for
each non-last use passed to a read-only builtin, where borrow elision skipped
them before the cutover. The net is unknown. The asymptotic claim, asserted
with a falsifier, is that this design takes the in-place arm wherever the
pre-cutover emission did: falsified by a workload whose in-place count falls.

## 9. Open questions

### 9.1 Confined non-atomic RC — decided

The user ruled on 2026-11-16 to simplify the dev path to the optimisations
that prevent asymptotic blow-up (Principle 27). The backend classifier and its
census retired at S123 W4; typecheck keeps producing its confinement and escape
facts. The as-built state is [ownership-codegen.md](ownership-codegen.md)
§5. Reopening confined counting is a release-tier design, under that
section's re-entry rule.

### 9.2 Falsifiers this design carries

- A move followed by a duplicate of the same binder in emitted code (an
  evaluation-order mismatch, §3.2), including one at a branching or binding
  node outside the shared sequence.
- A generated wrapper whose emitted counts differ from the forwarding
  template's (§3.3).
- A planned drop or consumption of a heap value that emits no release (§3.4).
- Any counting decision in emission that reads something other than the plan.
- A plan binder resolution that disagrees with typecheck's local-binder
  identity. The plan resolves a name against its own environment. The trigger
  for keying it on typecheck's local-binder identity instead is one such
  disagreement observed.
