# Monomorphisation from roots — design intent (structural slot-gate first)

Owner: `/design` (typecheck triad). Subordinate to `design/typecheck/typecheck.md` §9.3.
Companion: `design/typecheck/traits.md` §7 (the as-built batch pipeline this doc
*completes*, not replaces). Sprint 84 Cluster A — **re-grounded mid-Phase-5 on the
structural slot-gate-first model** (user architectural ruling 2026-06-16; resolves
FIXME 0376).

Contract this designs against:

- `design/arch/principles/20-model-invariants-by-representation.md` — **the spine.**
  The S84 generalisation: *a GOT slot is the value-capability of a CONCRETE callable
  — a def has a slot ⟺ its type is fully concrete (`Type::is_concrete()`).* The gate
  predicate is `is_concrete()`, **not** `constraints.is_empty()` — "concrete" and
  "unconstrained" are different predicates.
- `design/arch/bounded-contexts.md` §2 (structural-gate-primary paragraph) + §7
  ("Callability is structural" — slot ⟺ concrete) + §3 invariant 9 (backend RC
  soundness).
- `design/arch/fixmes/0374-…` (re-shaped — the corrected slot gate AND the
  systematic mono land together), `0375-…` (the codegen-side assert, now a backstop
  not a mechanism), `0373-…` part (ii) (the ambiguity rule, now a secondary backstop).
- `sprints/SPRINT.md` §"Architecture review (Phase 2)" point 1 + §5 "Cluster A
  re-shape" — binding: **Tier-2 EXTENDS the existing per-`(Def, type-args)`
  enumeration; a second monomorphisation entry point is rejected** (Principle 7).
- `crates/cranelisp-types/src/types.rs` — `Type::is_concrete()` (LANDED by /arch
  this sprint; one additive `public-api.txt` line) — the gate predicate.

This doc pins the *design intent*. It authors no code (design only). The primary
mechanism is the **structural slot-allocation gate**; the systematic
monomorphisation makes the slot-less set genuinely the never-used-as-a-value set;
the `contains_var` ambiguity check is a **secondary backstop**.

---

## 0. The re-grounding — what changed and why

The Phase-3 version of this doc framed Tier-2 concreteness around the
**`contains_var()` ambiguity check as the primary mechanism**, with the
monomorphisation pass chasing coverage *shape-by-shape* (HOF-arg shape, nested
generic, arg-position, …). A user architectural ruling mid-Phase-5 **inverts the
primacy**, and a leak was pinpointed:

- **The leak (the root).** The S83 slot-allocation gate tests `constraints.is_empty()`
  (no trait bounds) where it must test `is_concrete()` (no `Type::Var`). A
  generic-but-unconstrained def (`id : ∀a. a→a`, or a HOF whose result is `(Box a)`)
  has **empty constraints AND a `Type::Var`**, so it fell into the `else` arm →
  `UserFnState::Concrete { got_slot }` *while carrying a `Type::Var`* → reached
  `HeapCategory::classify(Type::Var)` → the unsound `<1024` RC guard → the
  `(Box a)`-through-HOF SIGSEGV (Wave-0 guard
  `mono_tier2_generic_adt_field_through_hof_no_crash`). **"Unconstrained" ≠
  "concrete".**

- **The inversion.** The **slot gate is the enforcing mechanism**: a def has a slot
  ⟺ it is concrete. A non-concrete def is slot-less *by construction* → it cannot be
  emitted as a value → it never reaches `classify(Type::Var)` as a callable address.
  "Is this def concrete?" becomes **"does it have a slot?"** — a structural property
  of the data model (Principle 18/20), not a downstream `contains_var()` check.

- **Coverage is forced by the representation, not chased shape-by-shape.** With the
  gate corrected, the generic def is slot-less ⇒ to be *used* it MUST be
  monomorphised to a concrete (slotted) instance. Systematic mono-from-roots mints a
  concrete slotted instance for **every reachable use**; anything left slot-less is
  either *never-used-as-a-value* (fine — the generic template is dead for codegen) or
  the 0373(ii) **ambiguity error** (a genuinely-unpinnable top-level var). The pass no
  longer enumerates a list of shapes; it follows reachability and the representation
  tells it what is still missing (anything reached but slot-less-and-non-concrete).

- **The ambiguity check is demoted to a backstop.** It still fires — for a genuinely
  unconstrained-AND-unpinnable top-level var — but it is no longer *the mechanism*
  that prevents the SIGSEGV (the slot gate is). Likewise the `contains_var()`
  pre-codegen debug-assert and 0375's `classify(Type::Var)→unreachable!` are
  backstops over a door already shut upstream (Principle 18 — the structural form is
  strictly stronger than the assert).

- **Scope refinement (Wave 0).** The genuine residual mono gap is **narrow**: the
  `(Box a)`-field-carrying-`Type::Var`-through-HOF instance. /arch + /qa confirmed the
  **bare-`Int` HOF shapes are ALREADY correctly monomorphised** — they pass the
  corrected gate with correct `Int` slots and are GREEN-stay regression guards, NOT
  in scope. The Phase-3 shape-by-shape list is retired in favour of "reachable, and
  the representation says what's missing."

---

## 1. The invariant — slot ⟺ concrete (the structural primary)

> **A GOT slot is the value-capability of a CONCRETE callable. A def's `fn_state`
> carries a slot ⟺ its finalised type is fully concrete (`Type::is_concrete()` — no
> `Type::Var`, no `TyConApp`-head var). A non-concrete-def-with-slot is
> unconstructable.**

This is the S84 generalisation of Principle 20 (BC §7). It subsumes two species of
slot-less def under one predicate:

| Def species | Constraints | Concrete? | Slot? | Why slot-less |
|---|---|---|---|---|
| Concrete callable (`add$Int+Int`, a non-generic defn) | empty | **yes** | **yes** | — it is directly callable |
| Constrained template (`cmp : ∀a. Eq a ⇒ …`) | non-empty | no | no | vars pinned per-call by trait dictionaries |
| **Plain parametric / generic (`id : ∀a. a→a`, `(Box a)`-result HOF)** | **empty** | **no** | **no** | unpinned type vars; only mono instances are callable |

The third row is the leak the re-shape closes: it has **empty constraints** (so the
S83 `constraints.is_empty()` gate admitted it) yet a `Type::Var` (so it is **not**
concrete and must be slot-less). Both slot-less species differ only in *why* their
vars are unpinned (trait dictionaries vs nothing at all); both are slot-less because
neither is directly callable as a value — only their concrete monomorphised
instances are.

**Consequence for codegen.** A `Type::Var` can no longer reach
`HeapCategory::classify` *as a callable value* because the slot-emission door is shut
upstream: a non-concrete def is slot-less, `callable_got_slot()` returns `None`, and
no `call_indirect` is wired through a never-populated slot. This is the §1 invariant
of the Phase-3 doc ("no `Type::Var` reaches codegen") re-derived from the
representation rather than from a downstream check — and it is *total by
construction* (Principle 18), not contingent on the ambiguity check catching every
case.

The `Type::contains_var()` debug-assert before codegen and 0375's
`classify(Type::Var)→unreachable!` are the **backstops** — seam-local tripwires that
turn any *future* regression of the slot gate into an immediate, located panic
rather than a silent use-after-free. They are not the prevention mechanism.

---

## 2. The corrected slot-allocation gate (the primary mechanism)

### 2.1 The predicate change — `constraints.is_empty()` → `is_concrete()`

The determination point in `finalize_check_form` finalises a Pass-1
`UserFnState::NotDetermined` entry into its determined `fn_state`. The S83 code
branches on `!trial_scheme.constraints.is_empty()`:

```text
// AS-BUILT (the leak):
if !trial_scheme.constraints.is_empty() {
    fn_state = Constrained(cf)            // slot-less
} else {
    got_slot = allocate_got_slot()        // ← admits a generic-unconstrained def
    fn_state = Concrete { got_slot }      //   with a residual Type::Var
}
```

The corrected gate adds the concreteness test as the slot-eligibility predicate.
Three determined states, gated structurally:

```text
// CORRECTED:
if !trial_scheme.constraints.is_empty() {
    fn_state = Constrained(cf)            // trait-bounded template — slot-less
} else if !trial_scheme.ty.is_concrete() {
    fn_state = Polymorphic { … }          // generic-unconstrained — slot-less (NEW arm)
} else {
    got_slot = allocate_or_reuse_slot()
    fn_state = Concrete { got_slot }      // fully concrete — slotted
}
```

The `Concrete { got_slot }` arm is now constructed **only when the finalised type is
fully concrete** (`trial_scheme.ty.is_concrete()`). The pairing
`Concrete { got_slot } ∧ non-concrete-type` becomes **unconstructable** — exactly
the Principle-20 representation form.

> **Note on the predicate operand.** The gate tests the *finalised callable type*
> the entry is determined to. `trial_scheme.ty` is the generalised function type at
> the determination point. `is_concrete()` (no `Type::Var`/`TyConApp` anywhere in
> params or result) is the eligibility predicate. /dev confirms the exact field path
> on the as-built `Scheme`; the design intent is "the function type the entry would
> be slotted under."

### 2.2 The exact gate sites + reuse legs

| Site | `program.rs` line | Role | Change |
|---|---|---|---|
| Single-sig determination | `:947` | `Constrained` vs `Concrete{slot}` | **Insert the `is_concrete()` gate** between them → `Polymorphic` for the non-concrete-unconstrained case |
| Multi-sig variant determination | `:1143` (`else`-arm slot at `:1165`) | per-`__vN` determination | **Same insertion** — a multi-sig *variant* whose finalised type still carries a `Type::Var` is `Polymorphic`, not `Concrete{slot}` |
| Single-sig generalize-writeback | `:919` | writes the generalized scheme back (pure-parametric) | The `constraints.is_empty()` guard here is the **0344 generalize-before-cross-defn-use** writeback — it governs *scheme* writeback for sibling instantiation, NOT slot allocation. It stays keyed on `constraints.is_empty()` (its job is pure-parametric scheme generalisation; a generic-unconstrained def DOES want this writeback so sibling uses see an instantiable polymorphic view). **Re-confirm it does not also flip a slotted state.** |
| Multi-sig generalize-writeback | `:1129` | same, multi-sig | Same as `:919` — scheme writeback, stays `constraints.is_empty()`. |
| False-positive-constrained demotion | `:1312` | `regeneralize_defn_schemes` demoting a falsely-constrained template back to concrete | **Gains the concreteness condition.** A constrained template demoted because its constraints vanished must only be re-slotted `Concrete` **if its scheme is now concrete**; if it generalised to a still-generic unconstrained type, it demotes to `Polymorphic` (slot-less), not `Concrete{slot}`. Today the demotion path is `scheme.constraints.is_empty() && Constrained` → allocate slot; the corrected path is `… && scheme.ty.is_concrete()` → `Concrete{slot}`, else `Polymorphic`. |

**The slot-allocation legs (`:947`/`:1143`/`:1312`) take the `is_concrete()`
predicate; the scheme-writeback legs (`:919`/`:1129`) keep `constraints.is_empty()`
because they govern scheme generalisation, not slot allocation.** The distinction is
load-bearing: conflating them would either re-leak (slot a non-concrete def) or
suppress the 0344 generalisation (break the fold). /dev must keep the two concerns
separate at each site.

### 2.3 The slot-less arm — distinct variant `Polymorphic` (NOT a reuse)

**Decision: a NEW `UserFnState` variant, working name `Polymorphic`** — slot-less,
sibling to `Constrained`. Rationale (reuse rejected):

- **Reuse `NotDetermined` — REJECTED.** `NotDetermined` is the *Pass-1 interim*:
  "callability not yet determined, Pass-2 has not run." A generic-unconstrained def
  IS determined (Pass-2 ran; it is determined to be parametric). Reusing
  `NotDetermined` would conflate "awaiting determination" with "determined
  parametric", and any reader that treats `NotDetermined` as "needs finalisation"
  (e.g. a redefinition / re-check path) would mis-handle a settled generic def. The
  interim-vs-determined honesty Principle 20 demands ("name the interstage
  explicitly") forbids overloading the interim arm for a determined state.
- **Reuse `Constrained` — REJECTED.** `Constrained(Box<ConstrainedFn>)` carries a
  trait-bound body (`ConstrainedFn { variant, scheme }`) and means "vars pinned by
  trait dictionaries." A plain parametric def has **no** trait constraints; forcing
  it into `Constrained` would (a) require synthesising an empty-constraint
  `ConstrainedFn` (misleading), and (b) collapse the *why* distinction BC §7 +
  Principle 20 make explicit. The two are siblings, not the same state.
- **New `Polymorphic` variant — CHOSEN.** Slot-less, carries the parametric body
  payload it needs for later monomorphisation (the `DefnVariant` + `Scheme`, same
  shape `Constrained` carries minus the trait-dictionary semantics — /arch
  determines the exact payload; the minimum is what `monomorphise_call` needs to
  re-check the body at concrete types, which the existing `Constrained`/pure-
  parametric path already reads). It makes `Concrete{slot} ∧ non-concrete-type`
  unconstructable and keeps the *why*-distinction legible to every exhaustive
  matcher.

> **The exact `Polymorphic` payload shape is a `cranelisp-types` change owned by
> /arch.** /design names the *need* (a slot-less determined-parametric arm carrying
> enough body to monomorphise); /design does NOT author the `cranelisp-types`
> variant. See §6 for the /arch FIXME + the cache-bump consequence.

### 2.4 `callable_got_slot()` answers `None` structurally for `Polymorphic`

`ModuleEntry::callable_got_slot()` (`module.rs:1194`) matches
`Concrete { got_slot } → Some(*got_slot)` and falls through to `None` for every
other arm. The new `Polymorphic` arm answers `None` **structurally** — same as
`Constrained` and `NotDetermined` — so the backend's `resolve_got_target`
(`compiler/mod.rs:186`) gets `None` and never wires a `call_indirect` through a
non-existent slot. **No backend slot-read change is required** (0374 FIXME confirms
this); the only backend touch is 0375's now-can't-fire assert, in a later wave.

The eligibility helpers `is_eligible_for_mono` / the `Filter` rustdoc at
`module.rs:618`–`635` (`ast.is_some() AND kind != Overloaded AND kind != UserFn {
fn_state: Constrained(_) }`) must be re-read: a `Polymorphic` def IS a mono target
(it is exactly the thing that must be monomorphised), so the filter that today
excludes `Constrained` should treat `Polymorphic` as *eligible-for-mono*, the same
way it treats a pure-parametric `Concrete`-with-`ast` today. /arch + /dev confirm the
filter arm; the design intent is "`Polymorphic` is monomorphisable, not skipped."

---

## 3. Systematic monomorphisation — extending `pass4_monomorphise`

With the gate corrected, the generic-unconstrained def is **slot-less** ⇒ it cannot
be emitted as a value ⇒ monomorphisation MUST mint a concrete (slotted) instance for
every reachable use, or the program fails to link that use. This is the forcing
function: coverage is no longer optional or shape-enumerated — a missed reachable
instance is a *missing slot*, a hard failure, not a silent unsound fallback. The
representation tells the pass what is still missing.

### 3.1 What landed (Tier 1 + 1.5) — the spine Tier 2 EXTENDS, not forks

S83 (`5634dd3`, `9e57330`) delivered the **polymorphic-result-hop** subset. The
enumeration spine is in place; Tier 2 widens its *coverage*, adds no second entry
point (Principle 7 — /arch Phase-2 ruling, binding):

| Element | Location | Role |
|---|---|---|
| `pass4_monomorphise` | `program.rs:2300` | per-cluster entry; runs in `finalize_check_result_inner` (`program.rs:1438`) |
| `collect_local_parametric_calls` | `program.rs:2491` | collector — local pure-parametric callees, **gated to bare-`Var` result** (Tier 1) |
| `collect_imported_constrained_calls` | `program.rs:2454` | collector — cross-module constrained / pure-parametric (0355) |
| `monomorphise_call` | `traits.rs:1271` | core — instantiate `(Def, arg-types)`, verify, re-check body, register mono entry with its own GOT slot |
| `monomorphise_inner_parametric_hops` | `traits.rs:1731` | **recursive** successor discovery (Tier-1 multi-hop / Tier-1.5 cross-module) |
| `collect_apply_var_calls` | `traits.rs:1888` | walks `Apply`-of-bare-`Var` call sites |
| `register_mono_entry` | `traits.rs:1458` | registers the mono `Def` + GOT slot; dedup by preserving an existing entry's slot |
| `entry_is_monomorphisable_polymorphic` | `program.rs:2540` | per-instance "is this a thing to specialise" gate |

**The coverage gap is in successor discovery, not the core.** `monomorphise_call`
already instantiates at concrete arg-types, re-checks the body in the right scope,
registers the mono entry with a slot, and recurses. What Tier 1 narrows is *which
reachable instances get discovered* — specifically the **`(Box a)`-field-through-HOF**
shape.

### 3.2 The Wave-0-refined gap — `(Box a)`-field-carrying-`Type::Var`-through-HOF

The genuine residual (Wave-0, deterministic SIGSEGV 5/5 at HEAD): a **polymorphic
fn-value passed through a higher-order function whose result is a generic ADT
carrying a `Type::Var` field** (the `(Box a)` shape). The result-hop machinery's
backward gate (`collect_local_parametric_calls`'s bare-`Var`-result trigger,
`program.rs:2516`–`2520`) does not seed an instance here because:

- the HOF call site's *result* is not a bare unbound `Type::Var` — it is a *concrete
  ADT constructor application* (`Box`) whose **field** carries the residual var; the
  bare-`Var`-result trigger misses it, and
- the polymorphic fn-value flows through an *argument position* of the HOF, not an
  `Apply`-of-bare-`Var` at the seeding site, so `collect_apply_var_calls` does not
  walk it.

**The bare-`Int` HOF / nested-generic / arg-position shapes are ALREADY covered** —
they monomorphise cleanly to concrete `Int` instances today (GREEN-stay guards). The
Tier-2 deliverable is *only* the ADT-field-through-HOF gap. The Phase-3 broad
shape-list is retired.

### 3.3 Tier-2 shape — a reachable-instance worklist seeded from roots

Generalise the collectors + the inner-hop recursion into a **single worklist-driven
fixpoint over reachable `(Def, concrete-type-args)` instances**, keeping the existing
core unchanged:

```text
roots    := concrete instantiations the cluster's top-level forms demand
worklist := roots
done     := ∅                              // cluster-level dedup (§3.5)
while worklist non-empty:
    inst = (Def, concrete-type-args) = worklist.pop()
    if mangled_key(inst) ∈ done: continue
    done.insert(mangled_key(inst))
    mono = monomorphise_call(Def, concrete-type-args)   // existing core; slots the instance
    for succ in reachable_polymorphic_instances(mono.body, mono_expr_types):
        // successor discovery widened to reach the (Box a)-field-through-HOF shape:
        //   - Apply-of-bare-Var result hops (as today), PLUS
        //   - a polymorphic fn-value flowing into a HOF argument position whose
        //     result ADT carries a Type::Var field
        if succ still has a residual Type::Var after this instantiation:
            continue          // not pinnable HERE — a deeper root / sibling may pin it;
                              // if NO reachable instantiation ever pins it, §4's
                              // ambiguity backstop has already rejected the owning form
        worklist.push(succ)
```

This is the existing recursion made breadth-first, cluster-global, and widened in
successor discovery from "result-hop `Apply`s" to "also the ADT-field-through-HOF
reachable instance." `monomorphise_inner_parametric_hops` is the as-built
depth-first, hop-restricted version of the `for succ` loop; Tier 2 widens its
successor set to reach the `(Box a)` shape and lifts dedup to the cluster level.

### 3.4 The root set

Roots are the concrete instantiations the cluster's **own top-level forms** demand,
after Pass-2 body-check + the first `regeneralize_defn_schemes` (`program.rs:1349`):

- A non-generic top-level defn (finalised scheme empty `type_vars`, concrete type) is
  a root at its single concrete instantiation — and is `Concrete{slot}` per §2.
- A top-level expression (synthetic `__expr` defn) is a root at its concrete type.
- A generic top-level defn (now `Polymorphic`, slot-less) is **NOT a root on its
  own** — it is specialised only through a concrete call site. If nothing reachable
  instantiates it concretely, it is dead for codegen and emits no instance (the
  generic template is never compiled — the rank-1 HM property the 0373 investigation
  ratified). **This is exactly why the slot-less arm is sound: a never-instantiated
  generic def having no slot is correct, not a gap.**

This matches the existing pass4 seeding; Tier 2 reframes "scan defn bodies for
parametric call sites" as "seed the worklist from concrete top-level instantiations
and chase reachable successors", with the slot-less-ness of `Polymorphic` defs as the
representation-level signal that a reached-but-unslotted instance still needs a
concrete mint.

### 3.5 Dedup — the cluster-level `done` set keyed on the mangled name

Key each instance by the existing mangled name `build_mangled_name(fn_name,
param_types)` (`traits.rs:1905`) — `name$T1+T2` — which is already the dedup key the
per-pass4 `seen: HashMap<String, JitSymbol>` map uses (`program.rs:2396`) and which
`register_mono_entry` already preserves-slot-on-collision. **Tier 2 promotes this
from a per-pass4-call `seen` map to a cluster-level `done` set** so a diamond of hops
converging on one specialisation is minted exactly once across the whole worklist.
No new key scheme — the mangled name IS the GOT-slot / JIT-symbol identity the backend
links against, so it must be the dedup identity (Principle 7).

### 3.6 No new boundary item for the mono output

Per the /arch Phase-2 ruling (point 1, confirmed): Tier 2 produces **more instances
of the existing `MonoDefn`/`Defn` shape** through the existing enumeration. Each
worklist instance lands as an ordinary concrete `UserFn` `Def` with a `Concrete {
got_slot }` `fn_state` registered by `register_mono_entry`. `MonoDefn` is already a
`cranelisp-types` public item (`lib.rs:223`); coverage grows, the output type does
not. **The one `cranelisp-types` shape change is the `Polymorphic` *input* arm (§2.3
/ §6), not the mono *output*.**

> **If the worklist needs a successor-discovery datum that does not fit on
> `Defn`/the re-checked AST and must cross the crate boundary**, that is a FIXME
> `target: /arch`, not a silent boundary change. The design's expectation is that it
> does not — successor discovery reads the re-checked body's `mono_expr_types`
> (already in hand inside `monomorphise_call`).

---

## 4. The ambiguity check (0373 ii) — SECONDARY backstop

### 4.1 Role — demoted from mechanism to backstop

The Phase-3 doc made the `contains_var()` ambiguity check the *primary* concreteness
enforcement. **It is now a secondary backstop.** The slot gate (§2) is what makes a
residual `Type::Var` at codegen structurally impossible; the systematic mono (§3) is
what makes the slot-less set genuinely the never-used-as-a-value set. The ambiguity
check catches only the residue both leave: a **genuinely unconstrained-AND-unpinnable
top-level var** — a var that is free at a top-level root, not a quantifiable scheme
variable, and that *no reachable instantiation pins*. The canonical shape: an
unannotated empty-collection literal at the top level with no use that pins the
element type.

It is a real, retained check — it produces the user-facing diagnostic for an
ambiguous program — but it is no longer the thing standing between a `Type::Var` and
the SIGSEGV. That role belongs to the representation.

### 4.2 Where it fires (unchanged seam, demoted prose)

**At the post-inference generalisation/finalisation boundary of each top-level form,
BEFORE `pass4_monomorphise` runs.** Inside `finalize_check_result_inner`
(`program.rs:1340`), after the first `regeneralize_defn_schemes` (`program.rs:1349`)
and before the Pass-4 call (`program.rs:1438`). Ordering rationale unchanged:
generalisation must have run (to distinguish a quantified scheme var — fine — from a
free-at-root un-generaliseable var — ambiguous); it must run before Pass 4 so an
ambiguous form is rejected rather than seeding an unpinnable worklist instance.

> **Generic-defn nuance (retained).** A *generic* top-level defn legitimately has
> `Type::Var`s in its finalised scheme (`type_vars` non-empty) — that is the point of
> a polymorphic definition, and it is `Polymorphic` (slot-less, §2) and NOT compiled
> on its own (§3.4). The ambiguity check fires only on a var **free at the root and
> not quantified into the scheme** — a var that survives generalisation *unquantified*
> because it is neither bound by a use-site instantiation nor closed over by the
> scheme. A var quantified into the scheme is fine. **The slot-less `Polymorphic`
> state and the ambiguity error are NOT the same thing**: `Polymorphic` is the
> normal, sound state of a usable generic def (its vars are quantified, pinned per
> use); the ambiguity error is the *unusable* case (a free var no use can pin).

### 4.3 Error variant + diagnostic wording (unchanged)

- **Today (this sprint):** raise `CranelispError::TypeError { message, location }`
  (the existing variant typecheck constructs, `program.rs:2032`/`:2041`). No new
  `cranelisp-types` item; no cross-crate surface change.
- **After FIXME 0098 Phase 3:** the dedicated `CheckError::AmbiguousType` —
  `cranelisp-typecheck`-internal, NOT surfaced cross-crate.

Wording (design pins; /dev lands):

```
ambiguous type: this expression's type contains an unconstrained type variable
that no use pins to a concrete type; add a type annotation to disambiguate
```

For a named top-level defn, the located form:

```
ambiguous type for `<name>`: an unconstrained type variable remains after
inference (no use pins it); add a type annotation
```

`ErrorLocation`: `span` from the offending form, `fq` when the form is a named defn
(master doc §8.1 producer policy).

---

## 5. The 0344/0349 fold canary — distinct-instance vs reuse discipline

**The pinned sprint risk (convergent finding, two agents).** The
`collect_local_parametric_calls` result-var gate deliberately preserves the 0344
fold-accumulator's shape: a fold helper threading a polymorphic accumulator *distinct
from the element type* (`vec-reduce`) must NOT collapse `b`, `a`, and `Vec` onto one
var when a sibling Vec-accumulator use is checked (`program.rs:900`–`924` writeback;
the `saved_subst` isolation at `traits.rs:1806`). The corrected gate and the widened
successor discovery **must not re-collapse this**.

Two properties together preserve it:

1. **The slot gate does not touch the fold writeback.** Per §2.2, the
   generalize-before-cross-defn-use writeback legs (`:919`/`:1129`) stay keyed on
   `constraints.is_empty()` — they are the 0344 fix and govern *scheme* writeback,
   not slot allocation. The `is_concrete()` predicate is inserted only on the
   slot-allocation legs (`:947`/`:1143`/`:1312`). The fold accumulator's polymorphic
   scheme writeback is unchanged.

2. **The worklist's residual-`Var` defer + `saved_subst` isolation.** §3.3's "if
   `succ` still has a residual `Type::Var`, don't enqueue it" preserves the property
   the bare-`Var`-result gate bought: an instance is only minted once concrete, so the
   fold accumulator's deliberately-preserved polymorphic shape is not forcibly
   collapsed by an over-eager successor enqueue. The existing `saved_subst` isolation
   around the inner recursion keeps a mono recheck's substitution from leaking into
   the parent's preserved scheme.

**Distinct-instance discipline.** The cluster-level `done` set (§3.5) keyed on the
mangled `name$T1+T2` creates each *distinct* concrete instance exactly once and reuses
the slot of an identical prior instance (`register_mono_entry`'s preserve-on-collision).
Distinct instantiations of the fold helper (`reduce$Int+Vec` vs `reduce$Bool+Vec`) are
distinct mangled keys → distinct slotted instances, never collapsed; an identical
re-reach is deduped, not re-minted. The discipline is "distinct concrete type-args ⇒
distinct instance; identical ⇒ reuse" — and the residual-`Var` defer ensures a
*still-polymorphic* shape is never forced into a premature concrete instance.

**The canary guards** (must stay green through the Tier-2 widening — name them in the
/dev change-set):

- The existing 0344/0349 unit tests in `cranelisp-typecheck`.
- The Wave-0 e2e canary `mono_tier2_fold_accumulator_not_over_monomorphised`.

---

## 6. Cross-crate impact — the `Polymorphic` variant + cache bump

The §2.3 decision (a **new `UserFnState::Polymorphic` variant**, not a reuse) has a
`cranelisp-types` + cache consequence that is **/arch-owned and /backend-owned**, NOT
/design's to author:

| Item | Owner | Disposition |
|---|---|---|
| `Type::is_concrete()` gate predicate | /arch | **LANDED** this sprint (`crates/cranelisp-types/src/types.rs`; one additive `public-api.txt` line). The gate uses it. |
| New `UserFnState::Polymorphic` variant (slot-less, carries the parametric body to monomorphise) | **/arch** | Additive enum variant in `cranelisp-types` (`module.rs` `UserFnState`). One additive variant, no `public-api.txt` removal. `UserFnState` already serde-derives. **FILE FIXME `target: /arch`** (§6.1) for the exact payload shape. |
| `CACHE_SCHEMA_VERSION` 5→6 bump | **/backend** | The serde shape of `UserFnState`/`DefKind` changes when the variant lands → bump (`crates/cranelisp-backend/src/cache/mod.rs:154`, no-serde-shape-change-without-a-bump). Lands in the SAME change-set as the variant. |
| Mono output (`MonoDefn`/`Defn` instances) | typecheck | No new boundary item — more instances through the existing enumeration (§3.6). |
| Backend slot-read | /backend | No change — `callable_got_slot()`→`None` for `Polymorphic` (§2.4); 0375's `classify(Type::Var)` assert is a later-wave backstop. |

**Coordination ordering for Wave 1.** If /dev implements the gate against a not-yet-
landed `Polymorphic` variant, it is blocked on the `cranelisp-types` change. So:
either /arch lands the `Polymorphic` variant + /backend lands the cache bump *first
in Wave 1's change-set*, then /dev wires the gate; or the FIXME (§6.1) is resolved at
Wave-1 entry. The variant + the cache bump + the gate correction are **one atomic
change-set** (Principle 20's "the collapse and its timing-wall resolution land
together").

### 6.1 FIXME to file — `target: /arch` (the `Polymorphic` variant shape)

This doc resolves FIXME 0376 (the re-grounding). It surfaces **one** cross-crate need
the re-grounding cannot satisfy itself: the exact shape of the new
`UserFnState::Polymorphic` variant in `cranelisp-types`. /design names the need; /arch
authors the variant. A `target: /arch` FIXME is filed alongside this re-grounding (see
`design/arch/fixmes/0377-*.md`) requesting:

- a slot-less `UserFnState::Polymorphic` arm, sibling to `Constrained`, carrying the
  minimum parametric body `monomorphise_call` needs to re-check at concrete types
  (the `DefnVariant` + `Scheme`, mirroring `ConstrainedFn` minus the trait-dictionary
  semantics — /arch decides whether to reuse a `ConstrainedFn`-shaped payload or a
  leaner parametric payload);
- the `eligible-for-mono` filter (`module.rs:618`–`635`) to treat `Polymorphic` as a
  mono target (not skipped like `Constrained`);
- the coordinated `CACHE_SCHEMA_VERSION` 5→6 bump (flagged to /backend) in the same
  change-set.

---

## 7. Unit-test seams (Phase-5 authoring by /qa + /dev)

Per the per-fix discipline (`memory/feedback_unit_test_per_fix.md`), the design names
the typecheck-seam unit tests; /qa + /dev author them in Phase 5. Narrow,
deterministic, in-crate (`TestFixture`, `checker/test_support.rs`), no codegen.

**(a) The gate — a generic-unconstrained def gets NO slot; its concrete instance
DOES.** Seam: `check_via_forms` over a generic-unconstrained defn (`(defn id [x] x)`),
assert its `fn_state` is `Polymorphic` (slot-less; `callable_got_slot()` → `None`).
Then, in a cluster where `id` is used at a concrete type, assert the mono instance
`id$Concrete` is registered with `fn_state: Concrete { got_slot: Some(_) }` and its
stored type `is_concrete()`. This pins the §1 invariant (slot ⟺ concrete) at the
typecheck seam — the exact property 0375's later assert relies on. Names:
`monomorphisation::tests::generic_unconstrained_def_is_slotless` +
`…::concrete_instance_of_generic_def_is_slotted`.

**(b) The `(Box a)`-through-HOF instance is monomorphised concrete (Wave-0 red flips
green).** Seam: `check_via_forms` over the `(Box a)`-field-carrying-`Type::Var`-
through-HOF cluster, assert the worklist mints the concrete `Box`-instance mono `Def`
(mangled name present) AND that its stored scheme / annotated body
`is_concrete()` (no residual `Type::Var`). Name:
`monomorphisation::tests::box_field_through_hof_monomorphises_concrete`. The e2e
counterpart is the Wave-0 `mono_tier2_generic_adt_field_through_hof_no_crash`
flipping green (/qa-owned, coordinated).

**(c) The 0344 fold canary stays correct.** Seam: the existing 0344/0349 unit tests
stay green through the gate + successor-discovery widening; assert the fold helper's
distinct-element-vs-accumulator polymorphic scheme is NOT collapsed (the `vec-reduce`
shape), and distinct instantiations (`reduce$Int+Vec` vs `reduce$Bool+Vec`) mint
distinct slotted instances. Names: the existing 0344/0349 tests +
`monomorphisation::tests::fold_accumulator_distinct_instances_not_collapsed`.

**(d) The 0373(ii) ambiguity error fires on a genuinely-unpinnable top-level var.**
Seam: `check_via_forms` over a top-level form whose finalised type leaves an
un-generalisable free `Type::Var` (unannotated empty-collection literal at top level,
no pinning use), asserting `Err(CranelispError::TypeError { message, .. })` matching
the §4.3 wording (post-0098: `Err(CheckError::AmbiguousType { .. })`). **NEGATIVE
companion:** a generic top-level defn (`(defn id [x] x)`) is `Polymorphic`, NOT an
ambiguity error — its scheme vars are quantified, not free-at-root. This negative is
the guard distinguishing "quantified scheme variable / sound `Polymorphic`" from
"un-generalisable free root var / ambiguous". Names:
`monomorphisation::tests::unconstrained_toplevel_var_is_ambiguous` +
`…::generic_defn_is_polymorphic_not_ambiguous`.

The e2e tier (cross-mode SIGSEGV-class repros + the all-modes-concreteness-equivalence
guard) is /qa's Wave-0 sprint-wide authoring per `sprints/SPRINT.md` §Waves — out of
this doc's seam scope, noted for coordination.

---

## 8. Risk

| Risk | Bound |
|---|---|
| **Re-leak: the `is_concrete()` predicate is inserted on the wrong leg** (slotting a non-concrete def, or suppressing the 0344 scheme writeback). | §2.2 separates the two concerns explicitly: `is_concrete()` on the slot-allocation legs (`:947`/`:1143`/`:1312`); `constraints.is_empty()` retained on the scheme-writeback legs (`:919`/`:1129`). The unit tests (a) + (c) pin both halves. /review confirms the leg split. |
| **0344/0349 fold over-monomorphisation** — re-collapsing the deliberately-preserved accumulator scheme. | §5: the writeback legs are untouched; the residual-`Var` defer + `saved_subst` isolation preserve the property the bare-`Var` gate bought; distinct mangled keys keep distinct instances distinct. The 0344/0349 unit tests + `mono_tier2_fold_accumulator_not_over_monomorphised` are the guards. **The sprint's pinned risk.** |
| **Enumeration non-termination** on recursive instantiation. | Bounded by monomorphic-recursion enforcement (rank-1 HM, 0373 i) — a recursive self-call is at the defn's own generic vars, not a growing type; the self-name guards (`program.rs:2501`, `traits.rs:1895`) skip fn→itself. The reachable `(Def, concrete-type-args)` set from a finite root set is finite; the cluster-level `done` set makes the worklist strictly decreasing. **State this Invariant in `traits.md §7` when the code lands.** |
| **`Polymorphic` variant lands late** → /dev blocked. | §6 coordination: the variant (/arch) + cache bump (/backend) + gate (/dev) are one atomic Wave-1 change-set, OR the §6.1 FIXME is resolved at Wave-1 entry. The variant is additive (no removal), so the blast radius is the exhaustive matchers over `UserFnState` (each forced to name the new state — the Principle-20 cascade, mechanical). |
| **Successor over-collection** (minting unused concrete instances). | Sound (extra concrete instances are correct, just unused); dead-instance pruning is a later perf concern, rejected as premature (Principle 6). The `done` set bounds duplication; reachability from real roots bounds the family. |

---

## 9. Cross-references

- `design/typecheck/typecheck.md` §9.3 — master-doc monomorphisation pointer (this
  doc is its structural-slot-gate-first elaboration).
- `design/typecheck/traits.md` §6–§7 — constrained polymorphism + the as-built batch
  pipeline this doc completes; the termination Invariant (§8) lands there with the code.
- `design/arch/principles/20-model-invariants-by-representation.md` — the S84
  generalisation (slot ⟺ `is_concrete()`); the spine of §1–§2.
- `design/arch/bounded-contexts.md` §2 (structural-gate-primary) + §7 ("Callability
  is structural") + §3 invariant 9.
- `design/arch/fixmes/0374-…` (re-shaped — corrected gate + systematic mono together),
  `0375-…` (backend assert as backstop), `0373-…` (rank-1 HM + ambiguity rule).
- `crates/cranelisp-types/src/types.rs` — `Type::is_concrete()` (gate predicate) +
  `Type::contains_var()` (debug-tripwire backstop).
- `crates/cranelisp-types/src/module.rs:1710` — `UserFnState` (the `Polymorphic` arm
  lands here, /arch-owned, §6).
- `crates/cranelisp-typecheck/src/{program,traits}.rs` — the gate sites (§2.2) + the
  enumeration spine (§3.1).
