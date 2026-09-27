# Monomorphisation — typecheck interior

**Status:** current design, verified against source on 2026-09-21.
**Owner:** `design`, narrow-deployed to `cranelisp-typecheck`.
**Subordinate to:** [`typecheck.md`](typecheck.md) §9.3.
**Governed by:**
- [the unified symbol-table lifecycle](../arch/symbol-table-lifecycle.md) — the `Life`
  machine and its settlement funnels;
- [the full-signature identity contract](../arch/s122-overload-reorder-publication.md);
- the monomorphisation reload seed in `design/arch/bounded-contexts.md` §2;
- Principles 20, 24 and 26;
- the language rules in `spec/03-types.md` §3.6.3, §3.10 and §3.11 and
  `spec/05-definitions.md` §5.1.2.

**Elaborated by:**
- [result-context specialization](result-context-specialization.md) — how a complete
  substitution demand is derived and replayed;
- [non-concrete producer obligations](non-concrete-producer-obligations.md) — how each
  producer population reaches the funnel.

Monomorphisation turns every *used* generic callable into concrete instances, and makes
it impossible for a non-concrete callable to be compiled. The primary mechanism is
representation. The ambiguity scan and the mint-time refusal are backstops.

- §1 The invariant: only concrete callables are realised
- §2 Settlement through the funnel
- §3 Monomorphisation from roots
- §4 The ambiguity backstop
- §5 Fold accumulators and generalisation order
- §9 Residual parameters at the mint
- §11 Multi-signature definitions
- §12 Evidence
- §13 Residuals and triggered extensions
- [Former section numbers](#former-section-numbers)

Numbers 6–8 and 10 are unused so that the cited numbers stay stable.

---

## 1. The invariant: only concrete callables are realised

> A callable has a slot and a codegen view if and only if its type is fully concrete
> (`Type::is_concrete()`: no `Type::Var`, no unresolved constructor head).

- **Realisation.** `Life::Concrete { slot, realization, … }` is constructed only by the
  lifecycle's `settle_concrete` funnel. The funnel checks concreteness, accepts the
  realisation, and mints or rebinds the slot in one act.
- **Templates.** A non-concrete callable is `Life::Template { body, kind }`. It has no
  field for a slot or a view, and it is a monomorphisation source, never a codegen
  target. `kind` keeps *why* the variables are open:
  - `Constrained` — pinned per use through trait constraints;
  - `Parametric` — pinned by nothing but the use.

  The Pass-1 interim state is `Life::Declared`.
- **"Unconstrained" is not "concrete".** `id : ∀a. a → a`, or a higher-order function
  returning `(Box a)`, has no constraints and still carries a variable. A gate keyed on
  empty constraints once slotted such definitions, and the residual variable reached
  heap classification as a segfault. Only the concreteness predicate decides
  realisation.
- **Consequence.** A type variable cannot reach codegen as a callable value. A reached
  use of a template with no instance is a missing-slot failure, never a silent fallback.
  Monomorphisation from roots (§3) supplies the instances.

## 2. Settlement through the funnel

### 2.1 Where the decision is made

The funnel is the only place this crate decides "concrete or not". Every producer settles
through `settle_concrete` or `settle_template`:

- ordinary definitions after Pass 2;
- definitions whose constraints turn out spurious at re-generalisation;
- multi-signature clause variants (§11);
- monomorphised instances (§3);
- synthesised constructors and accessors;
- trait-implementation methods.

None allocates a slot itself. Each population's route is recorded in
[non-concrete producer obligations](non-concrete-producer-obligations.md) §2.

Scheme generalisation for sibling instantiation is a separate decision from settlement.
It lets a polymorphic helper's generalised scheme reach later siblings and never grants a
slot. Conflating the two either slots a non-concrete definition or suppresses the
generalisation the fold accumulator depends on (§5).

---

## 3. Monomorphisation from roots

### 3.1 Components

| Component | Location | Responsibility |
|---|---|---|
| `pass4_monomorphise` | `crates/cranelisp-typecheck/src/program/mono_collect.rs` | per-window driver over one definition family (§3.3) |
| `collect_mono_call_sites` and its collectors | same file | find use sites (local parametric calls, imported constrained calls, dispatch to a template) and derive a complete `MonoDemand` for each |
| `monomorphise_call` | `crates/cranelisp-typecheck/src/traits/monomorphise.rs` | instantiate a template from a demand, verify constraints, recheck the body in its defining scope, and install the instance |
| `monomorphise_synth` | same file | derive an instance of a synthesised template from its recipe, with no body recheck |
| `monomorphise_inner_parametric_hops` | same file | successor discovery inside a rechecked body |
| `record_self_recursion_dispatch` | same file | a self-call inside an instance dispatches to that instance |
| `register_mono_entry` | same file | publish through `install_instance` with the demand's `InstanceLink` |
| `instantiate_demands` | `crates/cranelisp-typecheck/src/form.rs` | map-free replay entry (§3.8) |

There is one engine. Replay, the multi-signature drain's template arm and every window
enter the same core. A second instantiation entry point is rejected (Principle 7).

### 3.2 Roots

- A concrete top-level definition, and the synthetic `__expr` definition, is a root at
  its concrete type.
- `register_test_fn_mono_roots` gives a degenerate polymorphic `test-*` function a
  concrete `(Fn [] (Option String))` instance under its bare name.
- A reload demand set is a root set (§3.8).
- A generic definition is not a root. It is specialised only through a concrete use. A
  template nothing instantiates is dead for codegen, which is correct under rank-1
  inference (spec §3.10).

### 3.3 The driver and its settlement windows

`finalize_check_result_inner` settles every input monomorphisation reads before it runs
the driver:

1. `regeneralize_defn_schemes`, then re-resolution of deferred trait calls;
2. multi-signature registration (`resolve_multi_sig_overloads`);
3. the top-level overload drain (`resolve_pending_overloads`), then the final auto-curry
   drain;
4. `regeneralize_only_polymorphic`, then test-function roots;
5. the ambiguity scan (§4) and the unresolved-dispatch signal;
6. `finalize_multi_sig_variant_types` (§11.3), then the declared-bound check
   ([typecheck §9.2.1](typecheck.md#921-declared-bounds-are-discharged-at-settlement));
7. **window 1:** `pass4_monomorphise` over the `MultiSig` family;
8. **window 2:** `pass4_monomorphise` over the `SingleSig` family;
9. the sweep and `finalize_annotations_and_publish`, then ownership inference.

- **Families.** `collect_defns_for_mono` partitions every top-level definition into
  exactly one family, and a debug assertion checks the partition. The multi-signature
  family reads each clause variant's body. `Defn::body()` asserts a single variant, so
  the single-signature family cannot reach those bodies.
- **Why both windows follow settlement.** A multi-signature clause is settled concrete
  only after the drain and step 6. A single-signature body that consumes a
  multi-signature return sees a concrete argument type only after the same point. Both
  windows therefore read settled state (Principle 26), and a demand's substitution is
  never provisional.
- **Admission.** A demand is admitted only when every generalised variable has a
  concrete substitution. A use whose type is still residual is not queued: a deeper root
  or sibling may pin it, and an unpinned codegen-reaching use is §4's.
- **Idempotence.** Each invocation owns its own `seen` set. Installation reuses an
  existing instance and its slot. Each window reads the substitution only after it has
  settled, so a re-reached demand derives the same key.
- **Standing rule.** The windows are an enumerated set. A new `pass4_monomorphise`
  invocation at another settlement point is an architectural event. File it to `arch`
  for the class ruling rather than adding it (`design/arch/fixmes/0776-arch-settlement-seam-multiplicity-register-row.md`).
  The auto-curry drain's seams are the sibling instance
  (`design/typecheck/auto-curry.md` §1.2).

### 3.4 Termination

- Monomorphic recursion (spec §3.10) means a recursive call uses the instantiation in
  force, not a growing type.
- A self-call inside an instance dispatches to that instance
  (`record_self_recursion_dispatch`).
- From a finite root set the reachable demand set is finite, and deduplication makes each
  distinct demand mint once.

### 3.5 Instance identity — complete generic substitution

The demand's `InstanceLink` supplies the instance key once, through
`InstanceLink::instance_key`. Collection, worklist deduplication, recursion, minting and
`install_instance` retain that same link.

- Its `CallableTarget` identifies the defining binding or the selected overload arm.
- `type_args` records the concrete substitutions in structural first-occurrence order
  within the template scheme. A repeated generic variable occupies one position.
  Result-only variables occupy positions even when the function has no value
  parameters.

[Result-context specialization](result-context-specialization.md) owns the derivation
and replay collaboration. Typecheck keeps no second instance-name composer. The recursive
key encoding belongs to `cranelisp-types`, and overload-member naming is separate (§11.5).
`concrete_type_name` serves nominal trait lookup, not instance identity.

### 3.6 Output

An instance is an ordinary concrete entry installed through the lifecycle, and the
backend compiles it like any other concrete body. Monomorphisation adds no boundary type.
A successor-discovery datum that would have to cross the crate boundary goes to `arch`
first.

### 3.7 Cross-module body-recheck scoping

A constrained or parametric function defined in an imported module is instantiated in
the **caller's** module, with its own slot. Its body is rechecked with the defining
module as `home`. Three facts are load-bearing. Getting one wrong produces a spurious
`no impl of trait T for type X`:

1. **The recheck switches `state.current_module` to `home`,** so the body's bare
   references resolve in the defining module's imports.
2. **Constraint verification resolves through the instantiation's original→fresh
   variable map**, never through raw scheme variable identifiers. Across modules those
   are stale and can collide with a caller variable.
3. **Impl lookup for verification roots at the trait's home**
   through the shared satisfaction step
   (`crates/cranelisp-typecheck/src/traits/dispatch.rs::trait_satisfaction`;
   [typecheck §9.1.1](typecheck.md#911-impl-existence-is-keyed-by-the-receivers-identity)). Every trait
   implementation is recorded in the trait's defining module.

The implementation-level statement, and the unit test that guards these facts, are in
`crates/cranelisp-typecheck/CLAUDE.md` §"Cross-module monomorphisation".

### 3.8 "Instantiate this symbol at these types" — `instantiate_demands`

### 3.8.1 The capability

- After a from-source module reload, same-module instances whose callers survive must be
  re-minted.
- Replaying a remembered driver form was insufficient: it covered only one past
  instantiation, and it re-ran whatever ill-typedness that form had acquired.
- Reload therefore requests instantiation of named templates at recorded substitution
  vectors: data, not forms. Binary/int captures the demand set
  (`src/worker.rs::capture_reload_instantiation_demands`). Its transaction and remapping
  are specified in `design/int/s122-closure.md` §2.

### 3.8.2 Replay

- `instantiate_demands` seeds the ordinary driver and engine with
  `MonoDemand { template, type_args, site }`. Its source rustdoc is the entry-point
  contract.
- The selected template's own scheme interprets `type_args`, in the same order
  collection uses.
- Replay checks the vector's length before binding. It then reconstructs the whole
  signature, verifies constraints and rechecks the body in its defining scope. Value
  arity never defines the vector length.
- Instances install in the demanding module through the funnel. A repeated demand reuses
  its instance and slot.
- **Dispositions:**
  - a missing home is a load-and-retry gap (`Err(CheckError::Gap)`);
  - an absent or changed template, a malformed vector or a rejected constraint is a
    per-root stale-demand warning, and other roots continue;
  - a rejected root installs nothing partial;
  - hard invariant failures propagate.
- Replay uses `Span::SYNTHETIC`, so it writes into no live span-keyed carrier. The
  result has no display and no unresolved dispatch sites.

### 3.8.3 Ownership of the halves

| Half | Owner |
|---|---|
| instantiate at the given substitutions | typecheck (this section) |
| codegen the instances | nothing new: they are ordinary `Life::Concrete` entries with a body realisation |
| capture the live demand set before the replacing commit, and re-request it after the reload settles | Binary/int |

### 3.8.4 Public surface

`instantiate_demands` is the crate's one public entry point for this capability. It sits
beside `check_forms`, consumes the `cranelisp-types` `MonoDemand`, and adds no boundary
type, cache-schema or ABI effect. Its approval and binding contract are in
`design/arch/bounded-contexts.md` §2.

### 3.8.5 What replay must not become

- It adds no caller of `monomorphise_call`, and does not duplicate the driver.
- A hybrid of keyed read and form replay is rejected.
- The acceptance falsifiers are:
  - two separately minted instantiations of one template both survive a reload;
  - a stale, ill-typed driver record does not break reload;
  - repeating a demand set is idempotent;
  - a declined demand leaves no residue next to a valid demand for the same template;
  - a gap is not a decline.

### 3.8.6 Demand completion includes ownership inference

- After the complete demand set drains successfully, `instantiate_demands` runs the
  ordinary ownership pass once over the same environment and state, then returns
  `instantiate_demand_roots`'s result.
- Otherwise replayed instances would carry no summary, and a consumer could not tell that
  omission from a refusal.
- **Constraints:**
  1. Ownership runs once after every accepted root has registered, so interdependent
     re-mints converge in one fixpoint.
  2. The ownership universe predicate is unchanged. Arriving through replay does not make
     a body eligible.
  3. The analysis-off and non-convergence shapes are retained. Completion promises that
     the producer ran, not that every instance has a summary.
  4. Publication goes only through the ownership funnel. In cluster mode, reads see
     staging over live. A live-only same-module entry may inform the fixpoint but is not
     written.
- A hard demand error returns before ownership inference. Stale-root warnings drain with
  valid roots, and inference covers the accepted set.
- The two producer units are in `crates/cranelisp-typecheck/src/form/tests.rs`. The first
  mint must carry equal fresh summaries on the entry and on its view, in live mode and in
  cluster mode. In cluster mode the instance and its summaries appear only in staging, and
  live keeps its keys and payloads.

### 3.9 The instance engine's state channels

`monomorphise_call` is a phase-delimited driver: look up the template, reconstruct the
signature from the demand and check that its key equals the demand's key, verify
constraints, recheck the body, record self-recursion dispatch, build the annotated
instance, then build its codegen view and install it. The phase helpers' rustdoc
states each phase's local contract. The driver threads four mutable channels through
`CheckState`, and a helper extracted, merged or reordered without honouring them
mis-monomorphises. The symptom is a spurious `no impl of trait T for type X`, a wrong
ambiguity refusal on a valid program, or a crash one instantiation hop deeper.

1. **`current_module`.** Constraint verification and the body recheck each switch it
   to the defining module (§3.7), and each restores it before propagating its own
   result. A phase that returns an error before restoring leaks the defining module
   into its caller.
2. **The check-run side state** — method resolutions, expression types, pending
   auto-curry sites and pending overload resolutions. `recheck_body_for_mono` takes
   them before the recheck, returns the instance's own resolutions and expression
   types, and restores the enclosing state. Later phases read that returned harvest.
   The codegen view is built from the same per-instance resolutions (the check-run
   pairing rule in `design/arch/backend-keyed-consumer.md` §1.1.3). Re-reading
   `state.method_resolutions` there reads the enclosing run's map: two instances of
   one template would collide at a shared span, and a template checked in another run
   would lose its pattern constructors.
3. **`subst`.** The instance's signature and body settle on the live substitution,
   which building the annotated instance then reads. Each recursive mint of an inner
   hop saves and restores the substitution around its own call, inside the successor
   helpers. Lifting that isolation into the driver lets one instantiation's
   accumulator bindings leak into its siblings, which re-collapses the fold
   accumulator (§5).
4. **The recheck context** (`mono_recheck_self`). The driver installs the same-cluster
   template set and, for a multi-signature clause, the concrete self-recursion
   identity, and restores the previous context unconditionally so nested rechecks do
   not inherit either fact (§11.3.4).

Evidence: `crates/cranelisp-typecheck/src/traits/monomorphise/tests.rs` (distinct
instances of one template, annotations on the instance AST, rechecked constructor
values in the caller's module) and the cross-module, collector and multi-signature
cells in §12.

---

## 4. The ambiguity backstop

### 4.1 Role

- The funnel makes a residual variable at codegen unrepresentable. Monomorphisation makes
  the template set exactly the set never used as a value.
- The ambiguity scan catches what both leave behind: a codegen-reaching value whose type
  no reachable instantiation pins.
- It produces the located user diagnostic (spec §3.11.1). It is not the mechanism that
  keeps variables out of codegen.

### 4.2 Position-complete

`find_ambiguous_top_level_form`, in
`crates/cranelisp-typecheck/src/program/finalize/ambiguity.rs`, applies its verdict at
every value position the shared child enumeration `for_each_child_expr` visits, not only
at `let` bindings. Those positions are:

- binding values and `par` bindings;
- call arguments;
- match scrutinees and arms;
- `if` branches;
- vector elements and constructor fields;
- return positions.

A partially polymorphic ADT that reaches codegen through a non-`let` position is rejected
as an unpinned `let` binding is.

### 4.3 The verdict

- The verdict is **full concreteness**: a codegen-reaching value whose resolved type is
  not `is_concrete()` is ambiguous. No representation-based exemption exists. `(Vec a)`,
  `(Fn [a] a)`, `(Option a)` and a bare variable all reject when unpinned, even when their
  machine shape is determinate.
- It is the same predicate the funnel applies and the backend's `ConcreteType` boundary
  encodes, so the two sides agree by construction.
- **Scheme-quantified variables are allowed.** A value position inside a generic
  template's own body may mention its quantified variables. They are pinned at each
  instantiation.
- **Resolved dispatch positions are exempt.** At a trait-method dispatch position the
  scan reads the dispatch outcome: only a genuinely unresolved return-type-polymorphic
  dispatch is ambiguous. A dispatch resolved by its arguments or its context is exempt
  even when its recorded surface type is a stale variable
  ([return-poly dispatch signal](return-poly-dispatch-signal.md)).

### 4.4 Where it fires

- It fires once, in finalization (§3.3 step 5):
  - after the overload drain, so a clause pinned by a sibling self-call is scanned with its
    settled types;
  - after `regeneralize_only_polymorphic`, so a caller left spuriously polymorphic at drain
    time is scanned as concrete;
  - before the sweep, which empties the expression-type map it reads;
  - before either monomorphisation window, so an ambiguous form is rejected before it
    seeds a demand.
- Multi-arity definitions are scanned by the same pass, per clause, with that clause's
  settled signature supplying its allowed variables (§11.3).
- A generic definition whose variables are quantified is a legitimate template, not an
  ambiguity (spec §3.11.3).

### 4.5 Diagnostic

- The raised error is `CranelispError::TypeError`, located at the offending value.
- `AmbiguousForm::message` owns the wording. It names the clause and parameter when known
  and cites §3.11. It never names the internal `__expr` binder, and it never cites
  independent clause checking as the reason (§11.1).

---

## 5. Fold accumulators and generalisation order

- **The fold canary.** A fold helper whose polymorphic accumulator is distinct from its
  element type must keep that distinction. Three things preserve it:
  - generalisation and settlement stay separate decisions (§2.1);
  - a demand is admitted only when fully concrete (§3.3);
  - recheck substitution isolation keeps an inner instance from specialising the
    enclosing template.

  Distinct full signatures of the helper are distinct instances. An identical re-reach is
  deduplicated.

### 5.1 Generalisation-ordering debt

- **Root cause.** A function's scheme is generalised when its own body check ends, which
  can be before a forward-referenced helper's body has tied the shared variables. The
  scheme is then over-generalised.
- **Compensation.** `resettle_polymorphic_schemes`, called at each form boundary from
  `crates/cranelisp-typecheck/src/program/body.rs`, compensates by re-running the
  idempotent generalisation. It is sound: it moves only toward more-tied schemes, and no
  over-tie shape exists.
- **Its cost is a named debt.** It is O(forms × definitions), and it helps only when the
  tie-completing helper is checked first. With the helper defined last, the scheme still
  under-ties. No current program is known to reproduce that shape.
- **The cures.** Each is linear and complete for every order:
  - generalise in callee-first order over the harvested call edges; or
  - defer the writeback to finalization, once every body in the cluster has run.

  Either retires the re-settle. Take one when this seam is next opened for another
  reason.

---

## 9. Residual parameters at the mint

- The collector admits a demand only after every generalised variable has a concrete
  substitution.
- The minter validates vector length, reconstructs the complete function signature and
  refuses a residual parameter type with the located ambiguity error.
- The strict concrete-body builder and lifecycle settlement keep their own boundary
  checks.
- `InstanceLink::instance_key` consumes the demand's already-concrete substitutions and
  never receives an inference variable. There is no argument-only name composer left that
  could observe one.

### 9.3 Why the refusal is at the mint

A residual parameter once reached a debug-only assertion inside the argument mangler.
Debug builds, which include the REPL, panicked, while release builds produced the
ambiguity error later. Refusing at the earliest non-concrete observation makes every build
and mode produce the same located error. A genuinely unpinned multi-signature clause
parameter is now rare, because sibling self-calls pin clause parameters (§11), and it is
reported as the ambiguity the equivalent standalone function would raise.

---

## 11. Multi-signature definitions

### 11.1 The rule

A multi-signature `defn` is inference-equivalent to its clauses written as separate,
mutually recursive top-level functions that share one dispatched name (spec §5.1.2). A
self-call from one clause to a sibling is an ordinary call. It selects the sibling by
arity, and among same-arity clauses by argument types (§7.4.4), then unifies its
arguments with that clause's parameters, pinning them. There is no independence barrier.

```lisp
(defn rp4
  ([p rot]     (let [q (rp4 p rot 0)] p))        ; infers (Fn [Int Int] Int)
  ([p rot idx] (add-i64 p (add-i64 rot idx))))   ; (Fn [Int Int Int] Int)
```

### 11.2 One inference path

- Each clause is an internal `{name}__v{i}` variant definition. Pass 1 registers its
  signature exactly as a single-signature definition does, and Pass 2 checks its body.
- A call to an overloaded base is deferred as a pending overload resolution and drained
  by `resolve_pending_overloads`.
- **That drain's unification is the back-flow.** No bespoke clause routine exists.

### 11.3 Ordering

- `resolve_multi_sig_overloads` (`crates/cranelisp-typecheck/src/program/register/multi_sig.rs`)
  registers the base's dispatch table and the clause entries before the drain.
  Selection tolerates variable parameters, so a call selects the right clause before
  its types are concrete.
- The ambiguity scan runs after the drain, over multi-arity definitions exactly as over
  single ones (§4.4).
- `finalize_multi_sig_variant_types` promotes each back-flow-pinned clause from its
  `$Var` template to a concrete entry (Phase A), and refreshes persisted return types
  (Phase B).
- The concrete key, the `OverloadVariant` fields, the re-annotation name map and every
  self-call dispatch derive from **one** `mangle_sig` over the finalised clause parameter
  types (Principle 7). No concrete `$Var` entry survives.

### 11.3.1 Two drain passes

- Pass 1 resolves **self-calls**, calls to the base from inside one of its own clause
  bodies. They **unify**, which is monomorphic recursion within the letrec group.
  Instantiating them freshly would discard the pin.
- Pass 2 resolves **external calls**. A call selecting a concrete clause unifies and
  dispatches to it. A call selecting a template clause monomorphises at that call's
  arguments, so two external uses at different types never conflict.
- **Why the tag.** The same surface call must unify in one position and instantiate in the
  other, and argument concreteness cannot tell them apart. So each pending entry carries
  an `is_self_call` tag.
- **The tag's limits:**
  - it is textual: the active recursion name equals the base or starts with
    `{base}__v`, so a user definition literally named `f__v1` would misclassify;
  - the overload gate that queues the entry has the lexical-shadow guard of §11.8.7.

### 11.3.2 Self-call dispatch is derived after the drain

- A self-call's dispatch target must not be recorded mid-drain. In a chain of two or more
  delegating clauses, a callee clause may still be a `$Var` template when its caller's
  self-call drains. Phase A then removes that template, and the recorded dispatch
  dangles.
- **Design.** Pass 1 unifies and records **no** dispatch. It defers the site
  (`deferred_self_call_dispatch`). `finalize_multi_sig_variant_types` then records each
  deferred dispatch from the same `mangle_sig` that produced the concrete entry.
- Six carriers must agree, and do by construction:
  - the concrete entry key;
  - the base's `OverloadVariant`;
  - `resolved_overloads`;
  - the re-annotation name map;
  - the self-call's `resolved_calls` entry;
  - its dispatch-target carrier.
- **Considered: re-pointing the carriers Phase A misses.** Rejected: a provisional record
  repaired later leaks through any carrier the repair forgets (Principles 22 and 26).
  Deferral makes the name a pure function of settled state.
- External calls drain in pass 2 over settled types and need no deferral.

### 11.3.3 Definition-site overlap on written signatures

- Two same-arity clauses whose *written* parameter signatures unify are a dispatch
  ambiguity. It is reported at the definition, naming both clauses.
- The check runs before the drain, by design: the spec makes the judgment on the
  signatures as written, never on inferred types (spec §5.1.2).
  `(defn t ([x] x) ([:Int y] y) ([a b] (t "s")))` is rejected, and annotating
  `([:String x] x)` is the remedy.
- Call-site ambiguity remains as the backstop.

### 11.3.4 Recursion inside a monomorphised clause

- While a template clause is rechecked at a concrete instantiation,
  `CheckState.mono_recheck_self` (`MonoRecheckContext`) carries the instance's
  recursion context. The context is saved and restored around nested rechecks.
- **Same-instantiation self-call.** A self-call at the same instantiation resolves inline
  to the instance. The callee node is retyped to the instance's concrete signature, which
  is exact at a monomorphic-recursion site and scoped to the recheck.
- **Cross-arity sibling self-call.** It defers normally, and the recheck's scoped drain
  resolves it against the settled overload set (§11.8.3).

### 11.4 Constrained and polymorphic clauses

- A clause whose scheme keeps variables or constraints is its own one-variant template
  under its normalised `$Var` selector, and the base's `OverloadVariant` names that
  selector.
- It is reached through the drain, not through the single-signature collectors, which
  keep excluding multi-signature definitions because `Defn::body()` asserts a single
  variant.
- In drain pass 2, an external call that selects a template clause is monomorphised at the
  call's concrete arguments, and the resolution records the instance.
- The entry's own lifecycle state decides template versus concrete, so `OverloadVariant`
  carries no extra field.
- The same-arity overlap rule (§11.3.3) keeps a polymorphic `[:a x]` clause and a
  concrete `[:Int x]` clause of the same arity apart. The admissible cell is a template
  clause at a non-overlapping arity.

### 11.5 Determinism of overload selectors

- `OverloadVariant.mangled_name` is persisted, so a template clause's selector must be
  session-independent. `mangle_type` spells every variable as the constant `Var`.
- Two admitted same-arity clauses cannot collide, because a collision implies their
  signatures unify (§11.3.3).
- An inference-only constructor-head spelling never reaches a finalised selector.
- A selector is private. Once a concrete call selects a template, the instance key comes
  from the authored family and complete settled signature (§3.5). Concrete arguments are
  never appended to the selector to form a second executable identity.

### 11.8 The settled-overload harvest

#### 11.8.3 Harvest from settled state

- A poly hop inside a concrete multi-signature clause body is minted by window 1, the
  multi-signature family (§3.3). The clause is settled concrete by then, and its minted
  dispatches reach the publication rebuild.
- Overload dispatch inside a monomorphised body is settled by **one scoped invocation of
  the real drain**. `recheck_body_for_mono` takes the outer pending list, checks the
  body, drains just the body's own deferrals, then restores the outer list.
- The scoped drain gives the full concrete/template split and return-variable
  unification by construction.
- **Considered: a bespoke inner dispatch scan.** Rejected: it partially re-implemented
  the drain, wrote template selectors into frozen views and orphaned pending entries.
- The scoped drain also resolves cross-arity sibling self-calls (§11.3.4).

#### 11.8.7 Lexical shadows at the call head

- A `let`, `fn` or parameter binding lexically shadows a same-named top-level definition
  (spec §4.6). This is distinct from the definition-over-import conflict of spec §8.6.4:
  the boundary is binder kind, not name collision.
- **The overload gate** enters overload dispatch only when the name is not locally bound
  or is the genuine recursion self-reference (`CheckState::is_recursion_self_ref`).
- **The self-recursion writer** inside an instance reads the frame-guarded verdict
  materialised as a carrier. A self-application whose callee span has no global `var_refs`
  carrier is a shadow, and gets no dispatch. It then compiles as the local call it is.
  Re-evaluating the frame guard there would be unsound, because the frames are gone when
  the writer runs.

#### 11.8.8 The name is a trigger; the carrier is the identity

- Every name-scanning mono collector treats the callee name only as a candidate.
  Identity is the per-span resolution carrier.
- `program::support::callee_has_keyed_carrier` is the one guard. It proceeds only for a
  `VarRef::Global` at the callee span. The top-level collectors read the state's
  `var_refs`, and the recheck consumers read the recheck's harvested `var_refs`.
- A callee with no carrier resolved to a local, and dispatching it by name would
  wrong-value the shadow (Principle 24).

#### 11.8.9 Imported multi-signature bases

- A base imported from another module is invisible to the local overload tables.
  `maybe_rehydrate_imported_overload_base` chain-follows the callee at the application
  seam. When the name ends at another module's overloaded entry, it mirrors the entry
  into the local tables and records the base's home in `CheckState.overload_homes`.
- The one drain keys the dispatch by the bare base name through `mangle_sig`, then
  overrides the dispatch target's module with the recorded home.
- **Residual, tripwired rather than redesigned.** The qualified face re-derives the bare
  base name by splitting the reference. That is sound while stored entries are uniformly
  bare-mangled. Retire it by carrying the storage base name on the rehydrated overload
  record.

#### 11.8.10 Settlement windows

- The harvest runs at exactly the two windows of §3.3, both after overload settlement and
  in family order, multi-signature then single-signature.
- The idempotence obligations are the ones §3.3 lists:
  - reuse of the slot on re-installation;
  - a per-invocation `seen` set;
  - a substitution read only after it has settled;
  - pending-list isolation in rechecks.
- Adding a window is governed by §3.3's standing rule.

#### 11.8.11 Consumption through a wrapper

- A multi-signature return consumed inside a single-signature wrapper, and reaching a
  separately monomorphised consumer through the wrapper's parameter, must re-mint against
  the settled element type. The window-2 single-signature harvest runs after settlement,
  so the wrapper's inner demand derives from settled state.
- The drain also retypes a dispatched callee node to the **selected** clause's concrete
  signature. Otherwise the node would keep the base's pre-dispatch instantiation and ship
  a residual variable into the strict view.
- **Acceptance bar.** The multi-signature program and its two-function twin both compile
  and agree (`tests/mc_x4_consume_at_distance_0719.rs`), per the spec §5.1.2
  equivalence.

---

## 12. Evidence

- **Funnel boundary.** `adt::tests::polymorphic_constructors_are_slotless_templates`, and
  the lifecycle's own settlement cells.
- **Collectors, demands, windows and multi-signature cells.** The test files under
  `crates/cranelisp-typecheck/src/program/mono_collect/`, including the batch, carrier
  and multi-signature topic files, and
  `crates/cranelisp-typecheck/src/program/register/multi_sig/tests.rs`.
- **Cross-module scoping.**
  `program::mono_collect::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope`.
- **Replay.** `crates/cranelisp-typecheck/src/form/tests.rs` (§3.8).
- **Solution tier.** `tests/multi_arity_clause_param_51_2.rs` (back-flow, recursive
  polymorphic clauses against their standalone twins), `tests/multi_sig_base_mono_carrier_loss.rs`,
  `tests/multi_sig_poly_callee_cross_arity_mono.rs`, `tests/shadowing_scope_lookup.rs`,
  `tests/mc_x4_consume_at_distance_0719.rs`, and the fold canary
  `mono_tier2_fold_accumulator_not_over_monomorphised` in `tests/regression.rs`.
- **Inversion fences** that must keep rejecting:
  - same-arity written-signature overlap (§11.3.3);
  - a bare unresolved return-type dispatch (§4.3);
  - a duplicate method import (spec §8.6.4).

## 13. Residuals and triggered extensions

| Item | Status and trigger |
|---|---|
| Generalisation-order debt (§5.1) | Compensated. A test pinning a reverse-order under-tie as a known boundary is `qa`'s to allocate. Trigger for the linear cure: the next change opening the generalisation seam |
| Textual self-call tag (§11.3.1) | Documented limitation. Trigger: a real definition named `{base}__v{n}` |
| Qualified imported-base re-derivation (§11.8.9) | Tripwired. Trigger: a storage entry that is not bare-mangled |
| A new settlement window (§3.3) | Not to be added. Trigger: any need for one, which files to `arch` |
| Stale concurrency note | `crates/cranelisp-typecheck/src/checker.rs`'s `new_with_staging` rustdoc says the environment is not `Sync`, but the type keeps `Send + Sync` through its unsafe implementation, with single-cluster non-sharing as the precondition. A `dev` documentation repair |

---

## Former section numbers

- §0, §1 (incl. the S119 and S121 amendments) → §1
- §2.1–§2.4 → §1, §2.1
- §3.1, §3.3, §3.4 → §3.1, §3.3, §3.2
- §3.2 (the `(Box a)`-through-HOF gap) → §3.3 (admission by complete substitution)
- §3.5, §3.6, §3.7 → unchanged
- §3.8.1–§3.8.6 → unchanged; §3.8.5 now lists the replay falsifiers
- §4.1–§4.6 → §4.1–§4.5; the verdict is full concreteness (§4.3)
- §5, §5.1 → unchanged
- §6, §6.1 (the `Polymorphic` variant) → §1 (`Life::Template`)
- §7, §8 → §12, §3.4
- §9, §9.1–§9.7 → §9, §9.3
- §10, §11.7 → the header
- §11.1–§11.5 → unchanged
- §11.6 (return-type dispatch framing) → [return-poly dispatch signal](return-poly-dispatch-signal.md)
- §11.8.1, §11.8.2 → §11.8.3
- §11.8.4, §11.8.5, §11.8.6 → §12 (inversion fences); no carrier shape changed
- §11.8.7–§11.8.11 → unchanged; §11.8.10 now records two windows

Change history, the superseded pre-drain harvest window and the per-sprint evidence are in
Git history.
