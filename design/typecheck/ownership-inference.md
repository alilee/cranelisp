# Ownership inference — typecheck interior

**Status:** current design, verified against source on 2026-09-21.
**Owner:** `design`, narrow-deployed to `cranelisp-typecheck`.
**Governed by:** the [ownership-inference spine](../arch/ownership-inference.md)
(lattice, typecheck→backend contract, per-dimension conservative values and the
differential oracle) and [safety invariants](../arch/safety-invariants.md) §3 (the
monotone provenance frame, whose enumerated rule table is §3.3 here). Where this
document and either disagrees, they govern.
**Carrier contract:** `crates/cranelisp-types/src/ownership.rs` rustdoc owns the exact
`Mode`, `ResultMode`, `ParamFlow` and `ModeSummary` guarantees. Backend consumption is
[ownership codegen](../backend/ownership-codegen.md).

The pass infers, for every concrete callable in a cluster, how each parameter's
reference is used and where the result may point, so the backend can omit reference
counting operations it can prove unnecessary. Everything it publishes is a claim that a
consumer acts on. Absence is always the safe reading.

- §1 Purpose, placement and components
- §2 Call classification, the summary and site facts
- §3 The fixpoint, the walk and its rule table
- §4 Borrow-through-projection and may-alias links
- §5 Confinement
- §6 Instance summaries
- §7 The write path
- §8 Functions used as values
- §9 Declared primitive facts
- §10 The toggle, absence and refusal
- §11 Observability and evidence
- §12 Residuals and triggered extensions
- [Former section numbers](#former-section-numbers)

---

## 1. Purpose, placement and components

### 1.1 Soundness frame

- A published fact is a claim a consumer may elide an operation on. For example, the
  backend omits a callee's return protect exactly when a summary is present and says
  `ResultMode::Fresh`.
- Every fact is monotone-sound on its own. Widening toward `Owned`, `Retained`, escaping,
  crossing, not-unique or may-alias only loses precision.
- **`Fresh` is the exception.** It is the result axis's strongest claim, not its
  conservative point. Any rule that produces `Fresh` must prove that no parameter reaches
  the result.
- Absence is the single spelling of the conservative point: no summary, no site fact, no
  value-use mark. Consumers read summaries only through the carrier's conservative
  accessors, which treat a missing or short vector as `Owned` / `Retained` / spark-set.
- The reference semantics is the all-`Owned` lowering. An analysed program must behave
  and balance its heap exactly as it does with analysis off. The spine's differential
  oracle measures that end to end, and it is why the analysis has no observable effect
  in `spec/`.

### 1.2 Placement and universe

- The pass runs once per cluster, as the last step of `finalize_check_result_inner`,
  after `finalize_annotations_and_publish`. At that point monomorphisation has settled,
  callees are written and every concrete codegen view has been rebuilt.
  `instantiate_demands` runs it once more, after a reload demand set drains
  ([monomorphisation](monomorphisation.md) §3.8.6).
- It adds no pipeline stage, no store and no graph. It reads the cluster through the
  ordinary staging-aware accessor and writes through the ordinary publication funnel.
- **The universe is the cluster's strict-concrete bodies.** A member is a binding with a
  codegen view, a `Life::Concrete` arm carrying its checked AST, and a body that satisfies
  `cranelisp_types::is_strict_type_concrete`. Ordinary concrete functions and mono
  instances qualify. Synthesised constructor and accessor bodies do not; they read as
  absent at their call sites. The strict predicate is exported beside the strict view
  builder so the two cannot drift.

### 1.3 Components

| Module (`crates/cranelisp-typecheck/src/ownership/`) | Responsibility |
|---|---|
| `classify.rs` | The call classification (§2.1) and the `Copy` predicate (§2.2) |
| `transfer.rs` | The pure body walk: summary, site facts, harvested dependency set, value uses (§3.3–§3.5) |
| `fixpoint.rs` | The driver: toggle, universe, the three strata, refusal, and the callee-fact environments (§3, §10) |
| `confinement.rs` | Strand classification, `spark_ops` and `confined` facts (§5) |
| `uniqueness.rs` | `result_unique` and `unique_static` (§7) |
| `publish.rs`, `sites.rs` | The publication funnel and the one post-convergence site-fact annotation walk |
| `trace.rs` | `CRANELISP_OWNERSHIP_TRACE` |

The walks never touch the symbol table. Callee facts arrive through the `TransferEnv`
and `UniqEnv` traits. Production supplies the cluster environments in `fixpoint.rs`, and
unit tests supply map-backed fixtures (Principle 5).

---

## 2. Call classification, the summary and site facts

### 2.1 Call classification

Per-parameter modes attach only to statically resolved calls. Each `Apply` is classified
from its `resolved_call` first, then from its callee's shape:

| `Apply` shape | Class |
|---|---|
| `SigDispatch` to a binding, overload arm or macro clause | summarised (the owner symbol) |
| `SigDispatch` to any other target | Decision-24 |
| `TraitMethod` | summarised (the mangled implementation) |
| `BuiltinFn` | summarised (a declared leaf, §9) |
| `AutoCurry`, or an unknown future `ResolvedCall` variant | Decision-24 |
| no `resolved_call`, `Var` callee resolving to a concrete user function or a declared leaf | summarised |
| no `resolved_call`, `Var` callee resolving to a constructor or platform effect | Decision-24 (pinned boundary) |
| no `resolved_call`, `Var` callee that is a local binding or does not resolve | Decision-24 (a closure value) |
| computed (non-`Var`) callee | Decision-24 |

- A callee's kind comes from its binding's `CallableOrigin` and `Life`. Plain and
  trait-method concrete callables are user functions. Rust primitives are declared leaves
  whether concrete, inline or host-promised. Constructors and platform effects are pinned
  boundaries. A cluster member is always a user function.
- No primitive is recognised by name (Principle 19). The pass cannot tell a declared leaf
  from an inferred summary except by kind.
- A lambda is analysed inside its enclosing walk. A lambda that flows as a value is a
  closure, and its call sites are Decision-24.

### 2.2 The summary

One `ModeSummary` per callable, defined in `cranelisp-types`:

| Field | Half | Meaning |
|---|---|---|
| `param_modes` | ABI | `Copy`, `Borrowed` or `Owned` per parameter |
| `result` | ABI | where the result may point (the result axis below) |
| `param_flow` | advisory | where an `Owned` parameter's reference goes: `Consumed ⊑ IntoResult ⊑ Retained` |
| `spark_ops` | advisory | may the callee run a reference-count operation on the parameter off the calling strand (§5) |
| `result_unique` | advisory | is the result a proven unique root (§7) |

- `ModeSummary::abi_eq` compares exactly the ABI half. The live-redefinition gate compares
  `abi_eq_opt`, and a same-type redefinition that changes the ABI half is currently
  rejected (`repl/spec/18-redefinition.md` §18.1.2; `sprints/actions/ACT-0953-decouple-live-slot-abi-from-ownership-inference.md`).
- `param_flow` makes escape interprocedural: `(defn keep [x] (Some x))` has `x`
  `IntoResult`, while a string length primitive has its argument `Consumed`. `spark_ops`
  does the same for confinement, and `result` for projection and aliasing. The summary
  carries nothing the backend can derive inside one function.
- `Copy` is decided by type and a `Copy` parameter is never widened. Otherwise the mode
  lattice is `Borrowed ⊑ Owned`.

**The result axis** is a finite join-semilattice. For `i ≠ j`:

| Join | Result |
|---|---|
| `Fresh ⊔ Fresh` | `Fresh` |
| `AliasOf(i) ⊔ AliasOf(i)`; `ProjectionOf(i) ⊔ ProjectionOf(i)` | unchanged |
| `AliasOf(i) ⊔ ProjectionOf(i)` | `MayAliasOf(i)` |
| `Fresh ⊔` any claim reaching only `i` | `MayAliasOf(i)` |
| any claim reaching `i` `⊔` any claim reaching `j` | `MayAliasAny` |

- `Fresh` and the unconditional per-index claims are atoms. The optimistic seed is `Fresh`
  because it is the right guess, not because it is the bottom (§3.2).
- `AliasOf` and `ProjectionOf` are reserved for claims that hold on every path.
  `MayAliasOf` and `MayAliasAny` are the conditional points.
- `MayAliasAny` carries no index. It deliberately weakens a join of two distinct
  unconditional parameters, because the axis has no point for "definitely a parameter,
  index unknown". Tightening that arm requires adding such a point.

**`Copy` classification.** A type is `Copy` exactly when the shared value-layout algorithm
admits it (`cranelisp_types::value_layout_with_lookup`, looked up through checked
declarations by `fixpoint.rs::checked_value_layout`). Agreement with backend flattening is
safety-critical: bit-copying an unflattened heap object omits its required increment.
Typecheck therefore does not reproduce any layout rule.

- A present staged binding takes precedence even when its layout is ineligible. Only an
  absent staged key falls through to published metadata, and nested types in other
  modules use their published declarations.
- The lookup releases each storage borrow before recursing and materialises no temporary
  table.
- The [R5 value-representation contract](../arch/interfaces.md#r5-value-representation-flattening)
  and the `crates/cranelisp-types/src/heap.rs::value_layout_with_lookup` rustdoc govern the
  boundary.

### 2.3 Site facts

The walk keys advisory facts by node span. `sites::annotate` writes them once, after all
three strata converge, onto the stored codegen view:

- `escapes` — on string literals, vector literals, constructor applications, lambdas and
  applications;
- `confined` — the confinement verdict for the same allocation sites (§5);
- `unique_static` — only `Some(true)` is ever written (§7.2);
- `provenance` — the root of a borrowed projection, on the projecting `Apply` and on a
  match arm (§4).

`None` is conservative on every axis, and a backend that ignores all of them is correct.
The provenance symbol is the formal parameter's name (§3.4). Every production consumer
tests only its presence, and `MonoMatchArm.provenance` has no reader (§12).

---

## 3. The fixpoint, the walk and its rule table

### 3.1 Strata

Three worklist strata run over the walkable members, each after the previous one
converges:

1. **modes** — `param_modes`, `param_flow`, `result` and the escape and provenance facts;
2. **confinement** — `spark_ops` and `confined` facts, over the converged modes (§5);
3. **uniqueness** — `result_unique` and `unique_static`, over both (§7).

No stratum reads a later one, so the stratification is exact.

### 3.2 The modes worklist

- **Seed.** Each walkable member starts optimistic: `Copy` by type or else `Borrowed`,
  result `Fresh`, flow `Consumed`, spark bits clear. The seed is the working environment
  the walk reads. It is never publishable.
- **Publishable map.** A separate map is written only from a completed walk's output. A
  member that is never walked is absent, never seeded. The seed is dropped before
  publication.
- **Order and re-entry.** All walkable members are queued once, in table iteration order,
  with an in-queue set. No topological seeding is applied, and the persisted call graph is
  not consulted. A member's walk harvests the in-cluster callees whose summaries it
  actually read (its `DepSet`). When a member's summary changes, every member whose
  `DepSet` names it is re-queued, **including itself**. The self edge is what lets a
  self-recursive body reach its fixpoint; guarding it away would hide non-convergence.
- **Replace on update.** Each visit's output replaces the stored summary. Joining instead
  would force an ascending chain, but would degrade every exact `AliasOf(i)` to
  `MayAliasOf(i)` at the first visit.
- **Cap.** The visit cap is `universe × (max parameters + 4) + 32`. All three strata use
  that value with separate counters. Exhausting it in any stratum refuses the whole cluster
  (§10.2), so non-termination costs precision and never publishes a claim.
- **Termination, stated honestly.** Every rule is monotone in the callee summaries it
  reads, but the seed is a claim rather than the lattice bottom, so the Kleene argument
  does not start. The known oscillating class, a self-call that permutes its parameters,
  settles once its reach set holds two indices (§3.3). No shape is proven unable to
  oscillate. The refuter is the refusal trace line firing on a corpus compile (§11), and
  the next step would be join-on-update after a callable's first visit (§12).

### 3.3 The walk and its rule table

One pre-order walk per visit tracks an **origin** per binding:

| Origin | Claim |
|---|---|
| `Fresh` | no parameter reaches this value |
| `Unconditional { root, param, projection }` | this value is parameter `param` (or a borrowed view of it) on every path |
| `Conditional { params, projection, cow }` | this value may reach any parameter in the sorted index set `params`, and may be fresh on some path; `cow` is its may-alias link set (§4.5) |

The origin is walk-internal and never crosses the summary boundary.
`origin_to_result_mode` collapses it at the return. No reached parameter gives `Fresh`.
Exactly one gives `AliasOf` or `ProjectionOf` from an unconditional origin, or
`MayAliasOf` from a conditional one. Two or more give `MayAliasAny`. The hard-claim arms
match only `Unconditional`, so a conditional origin cannot publish a hard claim.

**Use contexts** decide how a use widens a reached parameter:

| Context | Parameter effect |
|---|---|
| neutral read, callee position, argument to a `Borrowed` or `Copy` position | none |
| argument to an `Owned` position | `Owned`, joined with the callee's flow |
| argument to a Decision-24 site; escaping capture | `Owned`, `Retained` |
| field of an aggregate | `Owned`, joined with the flow the aggregate's own context gives it |
| return position | `Owned`, `IntoResult` |

An ordinary use widens every parameter the origin reaches, except through an
unconditional projection. A clean borrowed view must not make its parameter `Owned`,
which is the rc-free read path §4 exists for. A capture widens the whole reach set.

**The rule table.** The table is normative (safety invariants §3c). A change to
`transfer.rs` that adds or alters a rule missing from this table is rejected in review.
A *narrowing* publishes a claim stronger than the join of its inputs and needs a recorded
structural justification.

| Rule | Construct | Behaviour | Class |
|---|---|---|---|
| Rule 1 | variable use | a bound name yields its origin verbatim; a free name is a value-use mark (§8) and `Fresh` | precision-preserving |
| Rule 2 | `let` / `par` binding | the RHS is walked neutral; its origin, including `cow`, is bound unchanged (§3.4, §3.5) | precision-preserving |
| Rule 3 | match-arm binding | a whole-value pattern binds the scrutinee's origin verbatim; a destructured field binds a projection of it, unconditional only when the scrutinee is unconditional and otherwise conditional over the scrutinee's reach and links; a whole-value binding that escapes re-walks the scrutinee in that context | widening |
| Rule 4 | `if` / match join | union of the reach sets and link sets; the variant is the ⊤-ward of the two operands (`Unconditional ⊑ Conditional`); `projection` only when every reaching operand is one; a definite origin survives only when both operands are unconditional on the same parameter and kind; independent of operand order | widening |
| Rule 5 | vector literal / constructor | the container's origin is the join of its elements' origins (never unconditionally `Fresh`); elements are walked as fields; the node's escape fact is its context's | widening |
| Rule 6 | projection out (`ProjectionOf(k)` callee) | argument `k` unconditional: an unconditional projection plus a provenance fact; conditional: a conditional projection, **and** force `escapes = true` at every carried link span; fresh: `Fresh` | precision-preserving; the link force only adds increments |
| Rule 7 | capture | an escaping lambda, or the launched side of `LaunchContinue`, computes its free-variable set: each captured binding widens every parameter it reaches, and a fresh or conditional binding is queued as escaping (§3.5). A non-escaping lambda's body is walked as its own frame's return, with an isolated escape list and the enclosing parameter state restored afterwards. A lambda value is `Fresh` | widening |
| Rule 8 | static call | arguments are walked at the callee's modes and flows (absent summary: `Owned`, `Retained`); the result follows the callee's `ResultMode`: `AliasOf(k)` gives argument `k`'s origin, `MayAliasOf(k)` joins `Fresh` with argument `k`, `MayAliasAny` joins `Fresh` with every argument, and a conditional outcome adds this call's span to `cow`; `Fresh` and an absent summary give `Fresh` (§10.4); an index past the call's arguments reads the frame's whole parameter set (a parameterless frame reads `Fresh`). A Decision-24 call walks its arguments as Decision-24 and yields `Fresh` | precision-preserving |
| Rule 9 | return | `origin_to_result_mode`, above | precision-preserving |
| Rule 10 | joined spark / suspension | `par` right-hand sides are neutral (a joined spark is a strand fact for §5, not a frame escape); the launched side of `LaunchContinue` is an escaping capture (rule 7); the continuation keeps the enclosing context | widening |

Rules 3, 5 and 7 were once unjustified narrowings and are the corrections this frame
exists to keep closed. Rules 4, 8 and 9 are the anchors they compose with.

### 3.4 Lexical scope and parameter reach

- **Scopes.** Each `let`, `par` and match arm pushes a frame recording the prior origin of
  every name it binds, and restores it on exit. Parameters are the base frame. The
  confinement walk keeps the same discipline for its parameter index. `MonoExpr` carries
  no alpha-renaming guarantee (stdlib `case` and `cond` expand to `(let [a a] …)`), so no
  walk may assume binder names are unique.
- **Reach is fixed at the mint** (Principle 24). An origin carries parameter indices from
  the moment it is created. No site maps a binding name to a parameter index. Resolving a
  root symbol at read time answers whatever that name denotes *there*, which is the
  defect class the table below records.
- **Totality of `param`.** `Unconditional` has four mint sites: the per-parameter seed,
  rule 4's definite arm, rule 6's unconditional arm and rule 3. Each is the seed or
  inherits an unconditional operand. A projection of, or pattern bind on, a `Fresh` value
  is `Fresh`, so an unconditional origin that reaches no parameter does not compile.
  - That absence is *structural*.
  - *Correct inheritance* is *measured*, by the subject/control pairs below: a present but
    wrong index type-checks as well as a right one.
- **`root`** survives only for the symbol-keyed provenance fact, and it always names the
  formal parameter. `drop_shadowed_provenance` at the `let`, `par` and pattern-binding
  seams drops facts rooted at a rebound name. `bind_pattern`'s `shadow` flag suppresses
  only the arm provenance fact, and never changes the bindings' reach. Minting `Fresh`
  there would be the false-`Fresh` narrowing.

Shapes that must publish their truth. Each subject has a one-identifier rename control in
`crates/cranelisp-typecheck/src/ownership/transfer/tests.rs`, and runtime faces in
`tests/shadowed_param_reach_stale_rc_dec.rs`:

| Row | Program (primitives imported) | Truth |
|---|---|---|
| A | `(defn f [flag a b] (let [a (if flag a b)] (if flag a (str-concat a "!"))))` | `result=MayAliasAny` |
| B | `(defn g [p] (f true "lit" p))`, calling A | not `Fresh` (`MayAliasOf(0)`) |
| C | `(defn f [a n] (let [x a] (let [a n] x)))`, `a:String`, `n:Int` | `modes=[Owned, Copy]`, `result=AliasOf(0)`, `flow=[IntoResult, Consumed]` |
| C′ | C with the inner binding's right-hand side a fresh literal | as C |
| C″ | `(defn f [a b] (let [x a] (let [a b] x)))`, both `String` | `modes=[Owned, Borrowed]`, `flow=[IntoResult, Consumed]` |

Before the reach was carried, C aborted with a stale reference-count decrement. C′ ran one
increment short and exited cleanly, and C″ matched its control under a rename but differed
from the analysis-off run. No single oracle catches the whole class: rename-control parity
detects C′, only the on/off differential detects C″, and the ABI half is observable only
at the module tier.

### 3.5 Binding-mediated escape

- A fresh or conditional binding used in an escaping context is recorded as escaping.
  Unconditional bindings need no record, because widening the parameter they carry is
  their whole handling.
- At the end of each `let` and `par`, before its frame is restored, `drain_escaped`
  re-walks each recorded binding's right-hand side in the escaping context, so the folded
  parameters widen and the allocation's escape fact flips. The drain repeats until this
  scope's entries settle, because re-walking one binding can newly escape an earlier one
  in the same chain (`[a (Some x) b (Some a)]`, `b` returned). Entries from outer scopes
  pass upward.
- Each right-hand side is re-walked in its *defining* scope: the binding being drained is
  temporarily restored to its prior value. A `(name, context)` set caps re-walks. It is a
  defensive bound, because the escape list is keyed by symbol.
- A match arm's whole-value binding has no drain. The match removes its entries and
  re-walks the scrutinee instead (rule 3).

### 3.6 Cost budget

- One linear walk per visit, with no unification, substitution, scheme instantiation or
  `Type` traffic; the walk reads only `ConcreteType`. A design change that makes the walk
  unify or instantiate leaves this budget and needs a fresh ruling.
- Site facts cost one extra walk per callable after convergence.
- Interactive cost is bounded by the redefinition transaction's affected set. A body-only
  edit that leaves the ABI half unchanged adds one walk per re-checked callable.

---

## 4. Borrow-through-projection and may-alias links

### 4.1 Projection sites

A projection is a match-arm constructor-field binding, a call to a callable whose
summary says `ProjectionOf(i)`, or a vector element read (`vec-get`, declared
`ProjectionOf(0)`). There is no projection node. The rules attach to these three shapes.

### 4.2 The rules

1. A projection of a `Borrowed` value with root `r` is `Borrowed` with root `r`, not with
   the intermediate value. Chains flatten to one root, so there is one soundness obligation
   per chain rather than one per link.
2. A projection of an `Owned` local is `Borrowed` with that local as its root.
3. A borrowed projection emits no increment when extracted and no decrement when released.
   The root's owning reference is the whole accounting.
4. A borrowed projection is never eligible for last-use transfer. Every use of it counts
   as a use of its root, so the root's release, or its copy-on-write in-place eligibility,
   is ordered after the last use of every projection rooted in it. Typecheck supplies the
   provenance. The backend owns ordering and emission. Without this rule a root reaching
   last use with a count of one would mutate in place under a live view.
5. **Escape materialises.** A borrowed projection reaching an escape edge (return, store
   into an escaping value, capture by an escaping closure, a suspension) does not widen the
   root. It takes one increment at the edge and is an owned reference from then on. The
   read path stays free of reference counting, and only real escapes pay, exactly once.

### 4.3 Why a borrow never outlives its root

- **In the root's own frame:** rule 4 orders the root's release after every rooted use.
- **Passed to a synchronous static call:** the callee's extent nests in the caller's, and
  the root stays live across the call. The argument composes inductively down any static
  call chain.
- **Captured by a joined spark:** the structured join lies within the capturing frame's
  extent.
- **Across any escape edge:** impossible, because rule 5 has already materialised the
  borrow.

### 4.4 Interprocedural projection

- A borrowed result is ABI-bearing. A caller compiled against `Fresh` decrements the result
  as a temporary, which is a double free against a still-owned field. A caller compiled
  against `ProjectionOf` emits no decrement, which leaks if the callee actually returned a
  fresh value.
- The result therefore sits in the ABI half, participates in `abi_eq`, and reads `Fresh`
  when absent (§10.4).
- A caller roots the call's result at its own argument's root (rule 6).
- Generated accessor bodies are outside the analysed universe (§1.2), so an accessor call
  reads an absent summary.
- The existing ad-hoc borrow cases are reproduced as inferred cases:
  - match-scrutinee field borrows are rules 2 and 3 at the arm;
  - spark-capture borrows are rule 3 with the joined-spark case of §4.3;
  - the vector-operation temporary-versus-field hazard is rule 4.

### 4.5 May-alias links

A copy-on-write result may be its argument's own reference on the in-place path, or a
fresh copy on the other. When such a value passes through two or more links in one frame
(nested calls, or a `let`) and is then projected out, every link whose accounting includes
a consumer-emitted release needs its protect.

- **The obligation belongs to the value** (Principle 25). A conditional origin carries the
  spans of every `MayAliasOf` call that created a link on its chain. Rules 8, 2 and 4 union
  and carry those spans, and rule 6 forces the escape fact at all of them. The backend's
  escape-gated retain then balances each release.
- **The number of consumer arms is fixed.** A chain shape is covered by composition, not
  by teaching the projection arm another syntactic shape. Composition is closed only while
  every composition rule is order-independent at its join. The `join_lattice_*` property
  cells assert that (§11). A rule that reads its answer off one operand breaks closure
  without adding an arm.
- **Negative control.** A chain returned whole and projected by the caller has no
  projection in the frame, so no link is forced. The return publishes `MayAliasOf` and the
  return protect covers it.
- **Contingency.** Links are walk-internal and need no persisted field while the linking
  call's node is in the consuming cluster's walk. If a link is created inside an imported,
  summarised user function, and a caller-frame span cannot drive the backend's retain,
  the obligation must ride the summary. That is a `cranelisp-types` and cache-schema
  change, routed to `arch`.

---

## 5. Confinement

- **Strands.** Each surviving reference-count operation site is classified:
  - *parent*: ordinary body code;
  - *potential fork*: a `par` right-hand side, and every position the backend's lenient
    lowering could spark (`let` right-hand sides and application arguments);
  - *deferred*: the launched side of `LaunchContinue` and deferred continuations.

  Spark placement is decided inside the backend, so typecheck over-approximates it. The
  confinement argument rests on which operations exist, not on where sparks are placed.
- **Verdict.** A cell is confined exactly when every surviving operation on it, across
  every frame that can reach it, runs on the parent strand of the cell's owning strand.
  Operations elided by §4 contribute nothing. That is why confinement runs after modes.
- **Interprocedural.** A callee's `spark_ops[i]` is set when it has a surviving operation
  on anything rooted in parameter `i` in a fork or deferred context, or passes the
  parameter to a callee whose bit is set. Declared leaves have their bits clear.
- **Fixpoint.** The bit is interprocedural, so the stratum is a worklist. When a member's
  bits widen, every other member whose `DepSet` names it is re-queued. Bits only move from
  clear to set.
- **Binary verdict.** The emitted fact is confined or crossing. There is no representation
  of values transferred across a join; §12 gives the trigger for adding one.
- **The shared-board shape.** A value captured by sparks by borrow and read through
  rc-free projections has no surviving operation on the spark side, so it is confined
  even while a live borrow crosses threads. A spark that materialises (a copy-on-write copy
  retaining elements of the shared value) puts surviving increments on the retained
  elements, and those elements are correctly crossing.

---

## 6. Instance summaries

- A monomorphised instance's summary is state on the instance's own entry and view. It
  inherits the instance's canonical identity ([monomorphisation](monomorphisation.md)
  §3.5).
- Instances register in the demanding module, so one realisation can exist in two
  modules. Re-inference is deterministic over the same inputs, so duplicates carry equal
  summaries. No cross-module summary store exists.
- There is no memo across checks. `TypeCheckEnv` is built per check call, and the in-pass
  map converges each callable once per compile. A cross-check memo would need a
  session-owned field threaded from Binary/int, which is a cross-crate signature change.
  §12 gives the trigger.
- Mode is not part of instance identity. A specialisation mechanism would need its own
  design and must not widen the key.

---

## 7. The write path

### 7.1 Mechanisms

- **Permission is dynamic and backend-owned.** The general reuse discriminator is an
  entry check for a count of one: one branch per call, copying once and then updating in
  place. Reuse tokens stay inside a function and off the ABI.
- **A static proof elides the check.** Where typecheck proves uniqueness, the backend may
  skip the dynamic check. Everywhere else the check runs. Typecheck's contribution only
  removes checks.
- **Uniqueness never enters the ABI.** A callee cannot demand a unique argument; there is
  no third mechanism.
- **Eligibility is per type.** `UniqClusterEnv::layout_eligible` admits reuse only for
  string and ADT values that have no value layout, that is, heap values. Scalars and
  functions are never reuse targets.

### 7.2 The uniqueness stratum

- **Greatest fixpoint.** `result_unique` is a must-property. It starts `true` for every
  walkable member, narrows to `false`, and re-enters through the same `DepSet` edges.
  `false` is conservative and falls back to the dynamic check.
- **Admission.** `unique_static = Some(true)` is written on a fresh-producing node whose
  value is a proven unique single-use root:
  1. it is a fresh allocation, or a call result **whose callee's `result_unique` proves
     it**. `result == Fresh` never suffices, because a callee may stash the value it
     returns;
  2. it has exactly one consuming use on every path, counted flow-insensitively (a
     projection read is not consuming, and over-counting only demotes);
  3. its type is eligible (§7.1).
- **Chaining.** A callee's `result_unique` lets its result seed the caller's proof, which
  is the success metric: a fused `(map inc (map dec v))` pipeline runs as two in-place
  passes (`tests/ownership_reuse.rs`).
- Conditional results (`MayAliasOf`, `MayAliasAny`) are never unique roots, because their
  callees cannot prove `result_unique`.

---

## 8. Functions used as values

A named function with a non-trivial summary may be both called statically and used as a
value. Every closure invocation must reach an entry that follows the uniform Decision-24
convention.

- **Ruling.** The canonical body compiles against its inferred ABI, and its slot targets
  that body. Using the function as a value goes through a Decision-24 adapter: take every
  argument owned, call the moded body through the slot, then emit the adaptations the ABI
  difference requires. That means a decrement after the call for each `Borrowed`
  parameter, and an increment to turn a `ProjectionOf` result into the `Fresh` result
  closures promise. The adapter is needed only for a value-used function whose summary is
  not already Decision-24.
- **Considered: widening the whole summary to `Owned` whenever a value use exists.**
  Rejected: one `(map f …)` anywhere would silently degrade every static call to `f`, and
  adding a value use would become an ABI-changing redefinition.
- **Typecheck's half.** The walk records value uses (rule 1). Publication marks each
  value-used concrete callable owned by this table (`set_value_use`). The summary gives
  the adaptation sequence mechanically.
- **The invariant.** Every code pointer that can reach a closure value targets a
  Decision-24 entry. Typecheck makes it checkable, and the backend's emission makes it
  true ([ownership codegen](../backend/ownership-codegen.md)).

---

## 9. Declared primitive facts

### 9.1 Where they live

- Each primitive declaration row in `crates/cranelisp-primitives/src/declarations.rs`
  carries its finished `ModeSummary`. The constructors in
  `crates/cranelisp-primitives/src/ownership_facts.rs` build it.
- No name-keyed fact table exists anywhere. Typecheck reads a leaf's summary from its
  entry, like any other callee.
- Facts follow the extern-consumption audit in the backend RC design:
  - "returns an argument unchanged" is `AliasOf`;
  - "retains an argument" is `Retained`;
  - decrementing before return is `Consumed`;
  - an argument that is only read is declared `Borrowed` as an analysis fact, while the
    extern keeps consuming by convention and the caller adapts at the extern site.

### 9.2 Consumption and reachability

- Declared leaves are constant boundary conditions. They are never queued and cost the
  fixpoint nothing.
- The cluster environments resolve callees through
  `TypeCheckEnv::resolve_terminal_entry_and_home_scoped`. That is the ordinary scope
  resolution, including the prelude fallback and its public-only filter, so declared facts
  reach modules that see primitives only through the prelude. A fallback-free probe would
  leave every leaf absent in ordinary user code, silently disabling the whole table.
- In-cluster members short-circuit before resolution (§10.3).
- Primitives are never redefined. A fact change is a compiler-version change, which
  invalidates caches through the schema version (§10.5).

### 9.3 Families

| Family | Declared facts |
|---|---|
| `vec-get` (inline) | `[Borrowed, Copy]`, `Consumed`, `ProjectionOf(0)`: the element read is rc-free against the vector's root |
| `vec-set` (inline) | `[Owned, Copy, Owned]`, `MayAliasOf(0)` |
| `vec-push` (inline) | `[Owned, Owned]`, `MayAliasOf(0)` |
| `string-identity` | `[Owned]`, `IntoResult`, `AliasOf(0)` |
| scalar operations | all `Copy`, `Fresh` |
| other heap primitives | uniform per row: heap parameters at the declared mode, `Consumed`, `Fresh` |

Copy-on-write is decided at runtime. The count-of-one path returns parameter 0's own
reference and only the shared path copies, so `Fresh` would be false for `vec-set` and
`vec-push`. Declaring `Fresh` there once let a return protect be dropped on the in-place
path.

---

## 10. The toggle, absence and refusal

### 10.1 The toggle

- When `cranelisp_types::ownership_analysis_off()` is true (`CRANELISP_NO_OWNERSHIP`),
  `run_pass5` returns at entry. No summary, site fact or value-use mark is produced, and
  persisted payloads are field-identical to an unanalysed compile. Backend reads the same
  accessor, so there is one switch.
- **Considered: running the analysis and having consumers ignore its output.** Rejected
  for three reasons:
  - it would hide the compile cost the toggle exists to measure;
  - redefinition would compare summaries in a configuration meant to reproduce the
    unanalysed session;
  - caches would persist facts the polarity says do not exist.

### 10.2 Refusal

- If any stratum exhausts the cap, the whole cluster publishes nothing: no summary, no
  site fact and no value-use mark.
- The refusal is a value on the cluster result (stratum, visits, cap, universe size). The
  publication funnel checks it too, and the trace reports it.
- The refused module compiles exactly as under the toggle, whose safety the differential
  oracle already measures.
- **Considered: publishing a ⊤ summary instead.** Rejected. A hand-written ⊤ literal once
  carried `Fresh`, the strongest claim, on the result axis, and for its whole life nothing
  detected it. No literal constructor of a published summary exists.
- **Considered: refusing only the non-converged component.** Rejected: it needs a
  strongly-connected-component pass to buy precision on a path that should be
  unreachable.
- **Grade.** The published map has a single write site, fed by walk output. That is
  structural as far as it goes, but beyond it the grade is *asserted with a named
  falsifier*: a walkable member that is queued and never walked. Today that cannot happen
  only because the queue and the member index are built from the same list.
- The confinement refusal arm is unexercised. It needs a spark-propagating chain with a
  tuned cap.

### 10.3 Residual-parameter frames and the member fence

- A member whose scheme still has a non-concrete parameter type (non-`Fn` scheme, arity
  mismatch, or a residual variable) refuses per-parameter seeding. It is not seeded, not
  walked and publishes nothing. Its callers read it as absent, which matches the
  Decision-24 lowering it actually receives.
- `residual_param_frames` keeps the exact keyed set for the trace. It explains which
  frames took this path and is not a zero-count gate.
- **Member fence.** A member with no walk output this compile must read as absent inside
  the pass. It must never read a summary persisted on its entry by an earlier compile,
  which REPL redefinition and incremental compilation make possible within a session.
  `ClusterEnv::summary_of`, `UniqClusterEnv::summary_of` and
  `UniqClusterEnv::result_unique_of` consult the member set before any chain-follow.

### 10.4 An absent callee result reads `Fresh`

- **Premise.** A callee compiled with no summary is lowered by Decision-24, which returns
  an independently owned result. `Fresh` is therefore consistent with that lowering at the
  caller.
- For refused clusters, residual frames and the toggle, the premise is the unanalysed
  lowering itself, which the oracle measures.
- For host-promised externs and callables outside the universe, such as generated
  accessors, the premise is asserted and load-bearing. `(defn get-inner [b] (inner b))`
  over a product accessor publishes `Fresh`.
- **Falsifier:** a callable reachable at an absent summary that returns a parameter's
  reference without materialising it.
- **Considered: reading absence as ⊤ on the result axis.** Rejected: it contradicts
  `ModeSummary::is_abi_conservative`'s published equivalence (absent ≡ all-`Owned` /
  `Fresh`). That is a `cranelisp-types` semantic change and is the user's decision.

### 10.5 Persisted meaning

- Summaries persist on `Life::Concrete` and on the codegen view, and cache-restored
  callees are read through them. A change to what an unchanged program's published
  summaries *mean* requires a `CACHE_SCHEMA_VERSION` bump in the same change-set, even
  when no serialised shape moves.
- The build identity does not substitute for the bump: an uncommitted build stamps the
  previous revision.
- The bump is a backend cache edit. Typecheck names the need when it changes meaning.

---

## 11. Observability and evidence

- **Trace.** `CRANELISP_OWNERSHIP_TRACE` dumps each cluster's summaries and site verdicts,
  one line for a refusal, and one for residual-parameter frames. It is silent and costs
  only an environment read when unset.
- **Test seams.** The walk and strata are pure over map-backed environments.
  `compute_cluster_with_cap` exposes the cap, so a cap of 0 forces refusal.
- **Module evidence** follows the submodules (Principle 23):

| Test home (`crates/cranelisp-typecheck/src/ownership/`) | What it discriminates |
|---|---|
| `classify/tests.rs` | every §2.1 row, including pinned boundaries and closure-valued sites; `Copy` delegation |
| `transfer/tests.rs` | the `join_lattice_*` property cells (commutative, associative, idempotent, link union, ⊤-ward variant, two indices publish ⊤); each rule-table row; escape and capture edges; the §3.4 subject/control pairs; an out-of-range index reads ⊤ |
| `fixpoint/tests.rs` | convergence of permuting self-calls; transitive `spark_ops` with the caller visited first; both refusal legs; the member fence with its non-member twin; staged-declaration layout for `Copy` and reuse |
| `confinement/tests.rs` | strand classes, the join, shadowed-parameter precision |
| `uniqueness/tests.rs` | single-use admission, multi-use and conditional negatives, chaining |
| `publish/tests.rs` | placement and staging; a refused cluster writes nothing |

- **Solution evidence.** Independent evidence lives in `tests/ownership_fences.rs`
  (projection, escape and declared-fact rows), `tests/s117_ownership_witnesses.rs`,
  `tests/ownership_reuse.rs`, `tests/safety_oracle_lane.rs` (copy-on-write chains under
  both toggles), `tests/false_fresh_provenance_residual.rs` and
  `tests/shadowed_param_reach_stale_rc_dec.rs`.
- **Joins.** When touching a join, merge or fold here, extend the property cells rather
  than only the program-shape cells. Shape cells over one tree cannot fail on an
  operand-order asymmetry.

---

## 12. Residuals and triggered extensions

| Item | Status and trigger |
|---|---|
| Join-on-update after a callable's first visit (§3.2) | Extension. Trigger: the refusal line firing on a corpus compile |
| Excluding `Copy` parameters from reach sets | Extension: sound, and slightly more precise. Trigger: a measured precision loss attributable to `Copy` positions |
| A transferred-across-join confinement point (§5) | Extension; needs a whole-lifetime happens-before argument per cell. Trigger: measurement showing a material share of atomic operations on values built on a spark and handed across its join |
| Cross-check summary memo (§6) | Extension. Trigger: REPL turn latency showing material re-inference cost |
| Symbol-keyed escape list (§3.5) | Precision residual on the advisory half: `(let [a (Some x)] (let [a a] a))` leaves `x` `Consumed`. Trigger for correctness review: an escape drained by a scope that did not bind it, observable as a lost or duplicated allocation escape fact under a shadow |
| Symbol-keyed provenance (§2.3, §3.4) | Retained as the safe direction; consumers test presence only. Falsifier: a backend site that binds the symbol, or any reader of `MonoMatchArm.provenance`, which would call for binder identities instead of names |
| Mutual-import cycles | Accepted precision loss: an importee whose pass has not run reads absent |
| Imported copy-on-write links (§4.5) | Contingency: routes to `arch` as a carrier and schema change |
| Absent-callee `Fresh` premise (§10.4) | Asserted; falsifier stated there. Attributing the two populations is `qa`'s |

---

## Former section numbers

Source comments, tests and other documents cite this document's earlier numbering. Read
them as follows:

- §0, §1 → §1
- §2.1 / §2.2 / §2.3 → §2.1 / §2.2 / §2.3
- §3.1 / §3.2 / §3.3 / §3.4 → §1.2 / §3.1–§3.2 / §3.3 / §3.6
- §4.1–§4.4 → §4.1–§4.4
- §5 (§5.1–§5.4) → §5
- §6 → §6
- §7, §7.1, §7.2, §7.3 → §7.1, §7.2 and §6
- §8 → §8
- §9.1 / §9.2 / §9.3 → §9.1 / §9.2 / §9.3
- §10 → §10.1, §12
- §11 → §11
- §12 → §12
- §13.1 (carrier items 1–12) → §2.2 and the `crates/cranelisp-types/src/ownership.rs` rustdoc; toggle §10.1
- §13.2 (change-sets CS-1…CS-4) → §1.3
- §13.3 → §3.2 (re-entry from the harvested `DepSet`)
- §13.4 → §9
- §13.5 → §10.1
- §13.6(b) → §2.3
- §13.6(c) → §2.2 result axis; §3.3 rules 4 and 9
- §13.6(d) → §3.4
- §13.6(e) → §3.2
- §13.6(g) → §3.5
- §13.6(h), "blocker 4" → §10.2
- §13.6(i) → §3.4
- §13.6(j), §13.6(k) → §3.3 rule 7
- §13.7 → §11
- §14.1–§14.4, §14.6 → §7
- §14.5 → §2.2 (`Copy`) and §7.1 (eligibility)
- §15, §15.1, §15.3, §15.4 → §2.2 result axis, §3.3 rules 8–9 and §9.3
- §15.2 → §9.2
- §16 (§16.1–§16.5) → §3.3
- §17 (§17.1–§17.7) → §4.5
- §18.2 (O-1, O-2) → §10.3
- §18.3 (O-3) → §3.3 rule 8
- §19.1, §19.2 → §2.2 result axis
- §19.3, §19.4 → §3.3
- §19.5 → §10.2
- §19.6 → §10.3
- §19.7 → §10.4, §3.2
- §19.8 → §3.2
- §19.9 → §10.5, §11
- §19.10, §20.7 → §12
- §20.1 (rows A–C″) → §3.4 table
- §20.2, §20.3, §20.4 → §3.4
- §20.5 → §10.5 (schema), §12 (provenance)
- §20.6 → §3.4, §11
- §15.5 → `crates/cranelisp-typecheck/CLAUDE.md` §"`Def.callees` completeness contract"

The staging plans, per-sprint measurements and superseded rulings behind the former
§§13–20 are in Git history.
