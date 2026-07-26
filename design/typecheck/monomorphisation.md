# Monomorphisation from roots — design intent (structural slot-gate first)

Owner: `/design` (typecheck triad). Subordinate to `design/typecheck/typecheck.md` §9.3.
Companion: `design/typecheck/traits.md` §7 (the as-built batch pipeline this doc
*completes*, not replaces). Sprint 84 Cluster A — **re-grounded mid-Phase-5 on the
structural slot-gate-first model** (user architectural ruling 2026-06-16; resolves
FIXME 0376). **Wave 2 — §4 re-grounded again to make the §3.11.1 ambiguity check
POSITION-COMPLETE and built on the shared `Type::is_representation_undetermined()`
predicate** (belt-and-braces ruling 2026-06-16; resolves FIXME 0380, closes the 0379
positional hole).

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

- **The ambiguity check is demoted to a backstop.** It still fires — now
  **position-complete** (every codegen-reaching value position, §4.2) and built on the
  shared `Type::is_representation_undetermined()` predicate (§4.3) — for a value whose
  type is representation-undetermined at codegen and that no reachable instantiation
  pins. But it is no longer *the mechanism* that prevents the SIGSEGV (the slot gate
  is). Likewise the `contains_var()` pre-codegen debug-assert and 0375's WIDENED
  RC-site backstop (§4.5) are backstops over a door already shut upstream (Principle 18
  — the structural form is strictly stronger than the assert). The typecheck check and
  the backend backstop share ONE predicate, so they agree by construction (belt-and-
  braces, FIXME 0379/0380).

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

> **S119 amendment — the invariant is site-independent (FIXME 0924).** §2 below
> states the gate as a property of `finalize_check_form`'s determination points.
> Two *other* sites construct `UserFnState::Concrete { got_slot }` and were never
> brought under it: `adt.rs::synthesise_one_accessor` (`:618-637`) for a polymorphic
> product's field accessor, and `traits/impl_check.rs` (`:1043,1078-1090`) for a
> trait-impl method, the latter via `scheme::mono` over a `fn_type` that still
> carries `Type::Var`. Both therefore hand backend the exact
> `Concrete{slot} ∧ non-concrete-type` pairing §2.1 declares unconstructable, and
> `design/backend/non-concrete-release-contract.md` §2.4 measures the result as
> **memory-unsafe** (a wild `atomic_rmw` on a scalar payload ≥ `NULLARY_TAG_THRESHOLD`),
> not merely leaky. The ruling is **P-1**: no site may construct
> `Concrete { got_slot }` for a scheme whose type is not `is_concrete()`, enforced
> by converging all three decision points onto ONE helper. Full statement, the
> A-MINT accessor-instantiation rule, and the F2 mangle ruling (which **rejects** a
> widened `mangle_trait_method` key in favour of this doc's §3.5
> `build_mangled_name`): **`non-concrete-producer-obligations.md`**.

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

The `Type::contains_var()` debug-assert before codegen and 0375's RC-site backstop
(WIDENED S84 Wave 2 — `panic iff classify == Mixed && ty.is_representation_undetermined()`,
§4.5) are the **backstops** — seam-local tripwires that turn any *future* regression
of the slot gate into an immediate, located panic rather than a silent use-after-free.
They are not the prevention mechanism. The backend backstop shares the same
`Type::is_representation_undetermined()` predicate the typecheck position-complete
ambiguity check (§4) uses, so the two sides agree by construction (Principle 7,
Principle 18; FIXME 0379/0380).

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

### 3.5 Dedup — keyed on the canonical home-qualified mangled name

Key each instance by the canonical mangled name `build_mangled_name(home,
fn_name, param_types)` (`traits/monomorphise.rs`), which is also the dedup key the
per-pass4 `seen: HashMap<String, JitSymbol>` map uses and which
`register_mono_entry` preserves-slot-on-collision. No new key scheme — the mangled
name IS the GOT-slot / JIT-symbol identity the backend links against, so it must be
the dedup identity (Principle 7). **The name path and the dedup-key path are the same
function** (`build_mangled_name`) over the same inputs, so the two grains cannot
disagree (the FIXME-0508 collapse point closed).

#### Mangled-name grammar (FIXME 0519 — the ONE canonical lossless mangler)

```
{home}/{bare}${recursive-concrete-sig}
```

- **`home`** = the DEFINING module's `ModuleFullPath` — the `home:
  Option<&ModuleFullPath>` threaded through `monomorphise_call` (FIXME 0355) when
  `Some` (imported generic), else `state.current_module` (local fn). Home-qualifying
  the key distinguishes two same-named imported generics `a/twist` vs `b/twist`
  registered into ONE consumer table → cures the **0508** silent wrong-dispatch.
- **`recursive-concrete-sig`** = each concrete param type mangled by the ONE canonical
  **total** type-mangler `program::mangle_type` (Principle 7 — single-sourced; the
  multi-sig `mangle_sig` composer routes its type components through the same
  function). `mangle_type` recurses EVERY concrete `Type` variant:
  - `ADT(fqtn, args)` → `{fqtn}$arg1+arg2+…` recursing args (`…/Vec$Int` ≠
    `…/Vec$String`) → cures the **0483** ADT-arg-erasure SIGBUS. The head is the
    FQTypeName (`{type-home}/{Name}`), so cross-module same-named types never collide.
  - `Fn(params, ret)` → `Fn(p1,p2,…;ret)` recursing params + ret in a balanced-paren
    form (nested `Fn` extents stay unambiguous). The `Fn` param is NEVER dropped →
    cures the latent third collision axis (two instantiations differing only in a
    concrete `Fn`-typed param no longer collide).
  - `TyConApp`, scalars — present as distinguishing text.

**Collision-free BY CONSTRUCTION (Principle 20):** the name is a pure function of
(defining home, bare name, recursively-mangled concrete sig); two instantiations
differing in any one distinguishing fact mint different names, and the "two distinct
instantiations → one name" state is unrepresentable. **Cache-safe:** all three facts
are persisted (module path, symbol, concrete param types) and compile-order-
independent; the grammar change bumps `CACHE_SCHEMA_VERSION` 12→13 (the mangled name is
the persisted `.meta.json` / symbol-table identity). The retired predecessor
(`build_mangled_name(fn_name, param_types)` = `{bare}${head-types}`) was lossy on THREE
axes: ADT args erased (`concrete_type_name` returned only `fqtn.name`), `Fn` params
dropped (`filter_map`→None), and home-independent. `concrete_type_name` survives only
for trait-impl TARGET naming (impl-on-type-constructor, head-name only).

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

### 3.7 Cross-module body-recheck scoping — the three load-bearing facts (S83, FIXME 0355)

A constrained (trait-bound) fn defined in an imported module and *called*
cross-module is collected by `collect_imported_constrained_calls`
(`program.rs`) → `monomorphise_call` (`traits.rs`). The resulting mono variant
(`cmp$Int+Int`) is an ordinary concrete `UserFn` `Def` registered in the
**caller's** module with its own GOT slot; the existing concrete-mono codegen
path wires it and its trait-method callees — **no backend special-case**. §3.5
covers how the instance is *named* (home-qualified mangle). This subsection
covers how its body is *re-checked correctly*, which is a separate correctness
concern.

The mono path threads `home: Option<&ModuleFullPath>` — the **defining** module,
`Some` for an imported generic, else `state.current_module` — into
`get_constrained_fn`, `recheck_body_for_mono`, `resolve_inner_constrained_calls`,
and `verify_constraints`. Three scoping facts are load-bearing; get any one
wrong and the call mis-typechecks, with the characteristic symptom being a
**spurious `no impl of trait T for type X`**:

1. **Body re-check switches `state.current_module` to `home`.** The body's bare
   references (`show`, `str-concat`, trait methods) must resolve in the defining
   module's import context, not the caller's. Without the switch a name the
   defining module imported but the caller does not is reported unresolved.

2. **Constraint verification resolves through the instantiation map, not the raw
   scheme var_ids.** `scheme.constraints` are keyed by the scheme's ORIGINAL
   quantified var_ids; only the FRESH instantiated vars are unified into
   `state.subst`. Cross-module the original var_ids are stale **and may
   collide** with a caller var — observed: `cmp`'s constraint var resolving to
   the caller's `IO` (from `main`'s `Pure`), yielding "no impl of Eq/Display for
   IO". `instantiate_and_resolve` returns the original→fresh `var_mapping`;
   `verify_constraints` resolves each constrained var through it first. The
   local same-module path masked this because the original var_id happened to
   stay live in `state.subst`.

3. **Impl lookup for verification roots in `home` too.** `verify_constraints`
   runs with `current_module` switched to `home`, so `has_impl_with_state` finds
   a defining-module-local (non-prelude) trait impl. A run that only exercised
   prelude-resident impls masked this via the prelude outer scope; a
   `helper`-module-local trait/impl exposes the gap.

Guarded by
`program::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope`.

---

## 4. The §3.11.1 ambiguity check (0373 ii) — SECONDARY backstop, POSITION-COMPLETE, predicate-shared

### 4.1 Role — demoted from mechanism to backstop

The Phase-3 doc made the `contains_var()` ambiguity check the *primary* concreteness
enforcement. **It is now a secondary backstop.** The slot gate (§2) is what makes a
residual `Type::Var` at codegen structurally impossible; the systematic mono (§3) is
what makes the slot-less set genuinely the never-used-as-a-value set. The ambiguity
check catches only the residue both leave: a value whose type is
**representation-undetermined at a codegen-reaching position** — carrying a free
`Type::Var` in a position where the machine representation depends on it, that *no
reachable instantiation pins*. Two canonical shapes: an unannotated empty-collection
literal at the top level with no use that pins the element type; and a `Mixed`-shaped
ADT (`(Option a)`, `(Box a)`) carrying a free var reaching a value position.

It is a real, retained check — it produces the user-facing diagnostic for an
ambiguous program — but it is no longer the thing standing between a
representation-undetermined value and the SIGSEGV. That role belongs to the
representation (the slot gate) plus the belt-and-braces backend backstop (§4.5).

### 4.2 Position-complete traversal — EVERY codegen-reaching value position

**Re-grounding (FIXME 0380, belt-and-braces ruling 2026-06-16).** The Phase-3/0376
prose framed the check as a **root-type-only** / `let`-binding-only scan. /review
(FIXME 0379) found that framing **positionally incomplete**: a `Mixed`-shaped ADT
carrying a free `Type::Var` reaches codegen through *non-`let`* value positions — a
match scrutinee (`(Pure (match (id Non) …))`), a fn-call arg, a vec element
(`(first-tag [(id Non)])`), a ctor field, an if-branch, a `ParBind` binding — and is
**reached-but-not-checked** by the `let`-only scanner. (The backend
`classify(Type::Var)→unreachable!` backstop cannot catch it either — a `Mixed` ADT
routes to `classify_adt` by ctor shape, and the free var rides invisibly in the
unused args, never reaching the `Type::Var` arm. So both guards miss it:
exit-0-by-luck-of-shape, one data-ctor-field deref from a `<1024` use-after-free.)

The corrected check is **position-complete**: it fires the per-node verdict on the
resolved type at **every codegen-reaching value position** the recursion already
visits — not only `let` bindings.

**The recursion was already complete; only the per-node *check* was `let`-gated.**
`find_ambiguous_let_binding` (`program.rs:1522`) already recurses into all children
via `for_each_child_expr` (`program.rs:52`); it just only *applied the verdict* on
`Expr::Let { bindings }` binding values. The correction lifts the verdict out of the
`Expr::Let`-only guard and applies it at every value-producing child:

| Value position | `Expr` node | Today | Corrected |
|---|---|---|---|
| `let` binding value | `Expr::Let { bindings }` | checked | checked (unchanged) |
| fn-call argument | `Expr::Apply { args }` | recursed-not-checked | **checked** |
| match scrutinee + arm bodies | `Expr::Match { scrutinee, arms }` | recursed-not-checked | **checked** |
| `if` branches | `Expr::If { then, else_ }` | recursed-not-checked | **checked** |
| vec literal elements | `Expr::VecLit { elements }` | recursed-not-checked | **checked** |
| constructor fields | `Expr::ConstrADT { args }` | recursed-not-checked | **checked** |
| parallel-let binding | `Expr::ParBind { bindings }` | recursed-not-checked (the check matched `Expr::Let`, not `ParBind`) | **checked** |
| nested `let` / return positions | (any) | recursed-not-checked | **checked** |

**Functions to add/extend (`crates/cranelisp-typecheck/src/program.rs`).** /design
names the seam; /dev lands it:

- **Rename + generalise `find_ambiguous_let_binding` → `find_ambiguous_value_position`**
  (or keep the name and widen the body — /dev's call; the design intent is that it is
  **no longer `let`-gated**). The per-node verdict is applied to the resolved type of
  *every* value-producing child `for_each_child_expr` visits, by reading each child's
  type from `child.inferred_type()` / `state.expr_types.get(&child.span())` resolved
  through `state.subst` (the exact mechanism the `let`-leg already uses,
  `program.rs:1535`–`1543`).
- **`find_ambiguous_top_level_form`** (`program.rs:1503`) is unchanged in shape — it
  walks each `defn.variants[].body` through the now-position-complete scanner, so the
  generalisation is transparent to it.
- **The local heuristic `is_ambiguous_codegen_reaching_type` (`program.rs:1584`) is
  RETIRED** (§4.3) — its body is replaced by a call to the shared predicate.

### 4.3 Shared predicate — `Type::is_representation_undetermined()`, NOT a local heuristic

The per-node verdict — *"is this value representation-undetermined at codegen?"* —
comes from the **shared `cranelisp-types` predicate
`Type::is_representation_undetermined()`** (`crates/cranelisp-types/src/types.rs`,
landed S84 Wave 2 by /arch, commit `ec219e2`), **not** a typecheck-local heuristic.

The old local `is_ambiguous_codegen_reaching_type` (`program.rs:1584`) — the
`Vec`-excluding, ADT-arg-free-var inline approximation — is **retired**: its body is
replaced by a call to the shared predicate. The two crates (typecheck error +
backend panic) thereby decide "dangerous" by the **same predicate** and cannot drift
(Principle 7 single-source-of-truth; Principle 18 enforce-invariants-structurally;
Principle 20 model-invariants-by-representation). The anti-drift rationale is the
whole point of the belt-and-braces ruling: a typecheck-side heuristic that
approximates the backend `Mixed` verdict but cannot *call* it WILL diverge (it did —
/review found it both too narrow on the dangerous direction and `Vec`-keyed on a bare
string coupled across the crate boundary). A single predicate consumed by both sides
makes "the typecheck error and the backend panic agree" true **by construction**, not
by parallel maintenance.

The predicate's verdict (per the `cranelisp-types` rustdoc, the source of truth):

- **TRUE** for a bare `Type::Var`; a `Type::TyConApp` (HKT head var); and a non-`Vec`
  `Type::ADT` carrying a free `Type::Var` anywhere in its args (`(Option a)`,
  `(Box a)` — the `Mixed`-family case the bare-`Var` panic missed, the 0379 hole).
- **FALSE** for `Type::Fn` (always a heap closure — RC-uniform), `(Vec a)`
  (uniformly heap, RC element-type-independent), any fully concrete type, and a
  `Type::ADT` with **no** free var (the legitimate type-known nullary-tag `Mixed`
  case).

**On the typecheck side the predicate is DIRECTLY the verdict** — there is no
`Mixed`-gating step here (that gate is the *backend's* half, §4.5). Under full
monomorphisation-from-roots (§3), a *genuinely free* var in a codegen-reaching value
position means **no root pins it** → the program is ambiguous (0373(ii)) regardless of
the value's heap category, so the conservative `true` is a **correct rejection, never
a false positive**. (The `Vec`/`Fn` FALSE arms are not false-negatives either: those
are structurally uniformly-heap, RC element-type-independent — sound to leave
polymorphic.)

### 4.4 Where it fires (the seam, unchanged ordering)

**At the post-inference generalisation/finalisation boundary of each top-level form,
BEFORE `pass4_monomorphise` runs.** Inside `finalize_check_result_inner`
(`program.rs:1340`), after the first `regeneralize_defn_schemes` (`program.rs:1349`)
and before the Pass-4 call (`program.rs:1438`). Ordering rationale unchanged:
generalisation must have run (to distinguish a quantified scheme var — fine — from a
free-at-root un-generaliseable var — ambiguous); it must run before Pass 4 so an
ambiguous form is rejected rather than seeding an unpinnable worklist instance. The
*site* is unchanged by the re-grounding; only the *coverage at that site* widens from
`let`-binding values to every value position.

> **Generic-defn nuance (retained).** A *generic* top-level defn legitimately has
> `Type::Var`s in its finalised scheme (`type_vars` non-empty) — that is the point of
> a polymorphic definition, and it is `Polymorphic` (slot-less, §2) and NOT compiled
> on its own (§3.4). The position-complete check fires only on a var **free at the
> root and not quantified into the scheme** — a var that survives generalisation
> *unquantified* because it is neither bound by a use-site instantiation nor closed
> over by the scheme. A var quantified into the scheme is fine — and a value position
> whose resolved type still mentions a quantified scheme var inside the generic
> template's *own* body is sound (it is pinned at each concrete instantiation by mono;
> the check reads the *resolved-through-`state.subst`* type, so within a concrete mono
> instance the var is already substituted away). **The slot-less `Polymorphic` state
> and the ambiguity error are NOT the same thing**: `Polymorphic` is the normal, sound
> state of a usable generic def (its vars are quantified, pinned per use); the
> ambiguity error is the *unusable* case (a free var no use can pin).

### 4.5 The belt-and-braces split — typecheck diagnostic + backend backstop

The position-complete check is **one of two position-complete sides** that, together,
make "no representation-undetermined value reaches an RC site" **total** (BC §3
invariant 9, belt-and-braces ruling 2026-06-16):

- **Typecheck side (this check) — the user-facing diagnostic.** A clean type error
  with a source location at the offending value position. It is the program-author's
  signal: "this value is ambiguous; pin it." Position-complete across every value
  position `for_each_child_expr` visits.
- **Backend side (FIXME 0375, /design(backend)'s `ring2-rc.md` §1.6) — the
  position-complete backstop.** The 0375 panic is WIDENED to trip on **any** type
  satisfying the shared predicate at an RC site, gated behind the backend's own
  `classify == Mixed` verdict: `panic iff classify(ty, tables) == Mixed &&
  ty.is_representation_undetermined()`. This covers both the bare `Type::Var` AND the
  `Mixed`-ADT-with-free-var family the as-specified `classify(Type::Var)→unreachable!`
  missed. The `Mixed` gate excludes a table-determined `NeverHeap`/`AlwaysHeap` ADT
  carrying a free var (so the backend never panics on a representation-*determined*
  ADT). Codegen visits every value, so the backstop is position-complete by
  construction — the ground-truth tripwire that turns any future gate/check regression
  into a located compiler-bug panic, not a silent UAF (Principle 18).

Both sides decide "dangerous" by the **same** `Type::is_representation_undetermined()`
predicate, so they cannot drift. The three-layer story (slot gate primary §2 →
typecheck position-complete check §4 → backend RC backstop §4.5, all sharing the
predicate) is the belt-and-braces statement of BC §3 invariant 9. The
position-completeness is what makes the *secondary* typecheck backstop actually total:
a non-`let`-position `Mixed`-ADT-with-free-var that the slot gate did not catch
upstream is rejected here cleanly, before it reaches the backend's own
position-complete backstop.

### 4.6 Error variant + diagnostic wording (unchanged)

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

### 5.1 Generalization-ordering debt — `resettle_polymorphic_schemes` compensates, does not cure (FIXME 0509)

**Recorded S103 Phase 3 (`/design`), resolving FIXME 0509.** The S102 CS-488c
fix for 0488(c) (fold-bodied scheme over-generalization) landed
`resettle_polymorphic_schemes` (`program.rs:1714`), which re-runs the existing
idempotent generalization eagerly at each form boundary. Review confirmed it
**sound** (monotone toward more-tied; no over-tie shape exists) and the right
shape for the S102 guard set — but it **compensates for the true root cause
rather than curing it**, and that debt is now on the record so a future pass
knows the seam:

- **Root cause.** The 0344 generalize-writeback (`:919`/`:1129`,
  `constraints.is_empty()`-keyed — see §2.2, §5) fires at the end of a fn's own
  body check, **before** its forward-referenced helper's body has tied the
  shared type vars. The scheme is generalized against a not-yet-tied
  environment, over-generalizing.
- **Chosen fix cost — O(forms × defns), worst-case O(n²).** The eager re-settle
  re-runs `generalize` + `apply_subst` at every form boundary; an
  all-polymorphic module pays quadratic `generalize`/`apply_subst`. Within the
  Principle-6 budget for the S102 guard set at observed module sizes, but a
  named cost, not a free one.
- **Coverage gap (reverse definition order).** The eager re-settle only helps
  when the tie-completing helper is body-checked **before** the consuming
  sibling's form. In **reverse order** (consumer defined first, tie-completing
  helper last) the scheme still under-ties — the *same* 0488(c) under-tie
  symptom, merely uncovered. Not a regression, not an over-tie; a known boundary
  with **no repro today** (all current fixtures define helpers-first).
- **The principled cures (each O(n), complete for all orderings), for a future
  promotion decision.** (a) **Topo-order** the per-form generalization so a fn
  generalizes only after its forward callees' bodies run — the harvested
  `call_graph_edges` (S101 0470/0472; the same forward edges pass5 walks —
  ownership-inference §13.3) already give the dependency order a Kahn sort
  consumes; or (b) **defer the 0344 writeback entirely to finalize**, generalizing
  once when every body in the cluster has run. Either retires the eager re-settle
  and its quadratic cost and closes the reverse-order gap.

**Disposition (S103): documentation-sufficient — no promotion this sprint.** The
eager fix ships as-is; the reverse-order gap is not a write-path blocker (pass5
reads *converged* schemes at the finalisation seam, after all bodies and all
re-settles — ownership-inference §3.1). Promotion to the O(n) topo-order/deferred
cure is a candidate for the sprint that opens `program.rs`'s generalization seam
for another reason. **`/qa` boundary test requested** (FIXME target `/qa` if not
picked up inline): a reverse-order under-tie fixture pinning the gap as a *tested
boundary* — a known limitation with a red-or-xfail guard — rather than a latent
surprise a future edit silently widens.

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
the §4.6 wording (post-0098: `Err(CheckError::AmbiguousType { .. })`). **NEGATIVE
companion:** a generic top-level defn (`(defn id [x] x)`) is `Polymorphic`, NOT an
ambiguity error — its scheme vars are quantified, not free-at-root. This negative is
the guard distinguishing "quantified scheme variable / sound `Polymorphic`" from
"un-generalisable free root var / ambiguous". Names:
`monomorphisation::tests::unconstrained_toplevel_var_is_ambiguous` +
`…::generic_defn_is_polymorphic_not_ambiguous`.

**(e) Position-complete: a `Mixed`-ADT-with-free-var in a NON-`let` value position is
rejected (FIXME 0379/0380 hole closed).** This is the unit seam /dev should add
alongside the retirement of the `let`-only gate, paired with /qa's position-complete
e2e negative guards. Seam: `check_via_forms` over a bare-prelude cluster with an inline
`Mixed` ADT (`(deftype (Opt a) (Non []) (Som [:a v]))`) + `(defn id [x] x)`, with the
ambiguous value `(id Non)` placed in each non-`let` codegen-reaching position in turn
— **match scrutinee** (`(Pure (match (id Non) [Non 0 (Som v) 1]))`), **fn-call arg**,
**vec element** (`(first-tag [(id Non)])`), **ctor field**, **if-branch** — and assert
EACH yields the ambiguity error (`Err(CranelispError::TypeError { message, location })`
with the offending value's span), via the shared `Type::is_representation_undetermined()`
predicate firing at that position. **The `let`-position case (already caught today)
stays an asserted positive control.** Names:
`monomorphisation::tests::mixed_adt_free_var_in_match_scrutinee_is_ambiguous` +
`…_in_call_arg_…` + `…_in_vec_element_…` + `…_in_ctor_field_…` + `…_in_if_branch_…`.
The e2e counterparts are /qa's position-complete negative guards (an unpinned
`Mixed`-ADT-free-var in each non-`let` position must error rather than compile-and-run
exit-0) — authored this wave, coordinated. This (e) seam + /qa's e2e are the regression
guard that the position-complete traversal stays total against future refactors.

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

## 9. FIXME 0432 — multi-clause `defn` self-call: the panic→clean-error root fix (S90 R2 layer a)

> **S112 SUPERSEDED-IN-PART by §11 (leg a, FIXME 0642; /arch A2).** §9 was written
> under the DRIFTED §5.1.2 ("each clause checked independently / no back-flow"), and
> §9.5's "NOT a multi-clause inference change" bullet is **REVERSED** by the S111-
> settled spec: a multi-signature `defn` is now inference-equivalent to its clauses
> written as **separate mutually-recursive functions**, so a sibling self-call DOES
> pin a clause's params (`sum-to`/`rp4` now INFER, not "annotate-or-ambiguous"). The
> Pass-4 concreteness gate §9.3 STANDS as a backstop — it now fires only for a
> **genuinely** unpinned clause param (no sibling self-call reaches it), the true
> §3.11 ambiguity. The new back-flow design is **§11**; read it as the current
> intent where it disagrees with §9.

**Sprint 90, /arch Phase-2 R2(a)** — pulled in as a Pillar-3 prerequisite
(`design/arch/repl-embedded-agent.md §11.3`, `sprints/SPRINT.md` §"Architecture
review" Q4). The agentic-REPL's importable-symbol indexer (Pillar 3) typechecks
**arbitrary reachable library modules** at index time; a `0432`-shaped module would
**panic-crash the REPL** in the agent's debug build. This section designs the
**typecheck root fix** (layer a). Layer b — the int-side eval-thread `catch_unwind`
floor — is `/design (int)`'s, not designed here.

### 9.1 The defect — Face B (the typecheck face)

`design/arch/fixmes/0432-multi-clause-defn-self-call-codegen.md` Face B. An
**unannotated** multi-clause `defn` whose body recursively self-calls across
variants:

```lisp
(defn sum-to ([n] (sum-to n 0))
             ([n acc] (if (primitives/eq-i64 n 0) acc
                          (sum-to (primitives/sub-i64 n 1) (primitives/add-i64 acc n)))))
```

Without annotations the cross-variant self-recursion cannot pin the second
variant's param types from the first variant's call. The result is a **partial mono
instance** whose param vector still carries a residual `Type::Var`
(`[Int, Var(62)]` in the FIXME). It reaches `build_mangled_name`
(`monomorphise.rs:1004`) and trips the `debug_assert!` at `:1016`:

> `build_mangled_name(sum-to) saw a non-concrete param type (lossy-name hazard …): [Int, Var(62)]`

### 9.2 The two-face divergence — debug panics, release clean-errors

The divergence the FIXME records (REPL → panic; `--run` → clean ambiguous-type
error) is a **debug-vs-release `debug_assert!` artifact**, and locating it pins the
seam exactly:

- **The mint runs inside Pass 4** (`pass4_monomorphise` → `monomorphise_call`,
  `program.rs:1880`). The residual-`Var` param vector is computed at
  `monomorphise_call` **P1** (`monomorphise.rs:108–117`): `instantiate_and_resolve`
  leaves a param `Var` unpinned, then `build_mangled_name` is called on it at `:117`.
- **In a debug build** (`cargo run`/`nextest` — the agent's only build) the `:1016`
  `debug_assert!` is **live** and fires *inside Pass 4*, **before** the §4 ambiguity
  backstop is reached → the unwind escapes (REPL has no catch on the eval thread →
  crash).
- **In a release build** (`--run`) the `debug_assert!` is **compiled out**; the mint
  silently produces a lossy mangled name, Pass 4 returns, and the §4 backstop
  `find_ambiguous_top_level_form` (`program.rs:1913`) catches the residual var at the
  *finalisation* boundary and raises the clean

  > `ambiguous type; add an annotation to pin the type of the polymorphic value bound in \`sum-to\``

So the clean error **already exists** on the release path; the panic is the debug
path reaching the mangler tripwire *before* that backstop. **The fix is to move the
verdict earlier — to the mint seam — so both builds converge on the clean error and
the mangler is never reached with a non-concrete param.**

### 9.3 The seam — guard `monomorphise_call` P1, before `build_mangled_name`

**The fix is an early concreteness gate at `monomorphise_call` P1, between
`instantiate_and_resolve` and `build_mangled_name`** (`monomorphise.rs`, after the
`concrete_param_types` binding at `:111–115`, before `:117`). This is the **only**
place where a residual-`Var` param vector is handed to the mangler; guarding here is
necessary and sufficient for Face B.

The gate:

1. After `concrete_param_types` is bound (`:111`), test
   `concrete_param_types.iter().all(Type::is_concrete)` — the **same predicate** the
   `:1016` `debug_assert!` tests, lifted from a release-erased assertion to a live
   `Result`-returning check.
2. On a **non-concrete** param, return `Err(CranelispError::TypeError { … })` —
   **not** `Ok(None)` (which means "not a mono target" and would silently skip the
   instance) and **not** a panic. The error propagates via the existing `?` chain
   out of `pass4_monomorphise` exactly as the §4 backstop's error does.
3. `build_mangled_name` is then reached **only** with all-concrete params. Its
   `:1016` `debug_assert!` stays as a **pure tripwire** for a *future* unrelated
   spurious-mint site (it should now be unreachable for 0432; keep it — it is the
   §4.5 "ground-truth tripwire" discipline, Principle 18). The gate is the *clean
   path*; the assert is the *belt-and-braces backstop* behind it — exactly the
   two-layer shape §4.5 already establishes for the codegen-reaching ambiguity.

**Why P1 and not the §4 backstop alone.** The §4 backstop fires at the
*finalisation* boundary, which in release is *after* Pass 4 returns — too late to
stop the debug `debug_assert!` that fires *during* Pass 4. The §4 backstop is
position-complete over **top-level value positions**, but the residual-`Var`
**mono-instance param vector** is an *intermediate Pass-4 artifact*, not a
top-level value position it scans. The mint seam is where the non-concrete param
first becomes observable; catching it there is the minimal, on-path fix. (The §4
backstop remains as the finalisation-boundary guard for the *other* ambiguity
shapes; this gate is its Pass-4-interior sibling for the mono-mint shape.)

### 9.4 Intended error — converge REPL and `--run` on one message

The gate's error **MUST match the release-path message both faces of the bug already
converge toward**, so REPL and `--run` produce *identical* diagnostics (the
convergence the FIXME demands and `s84-concrete-types-ambiguity-ruling` mandates: a
residual var reaching the mangler is a **clean type error, never a panic**).

- **Message shape** — reuse the established §3.11.1 / `find_ambiguous_top_level_form`
  wording so the suite's existing ambiguous-type assertions hold and the user sees
  one consistent diagnostic:

  > `ambiguous type; add an annotation to pin the type of the polymorphic value monomorphised in \`{fn_name}\` (a residual unbound type variable reached a codegen position)`

  This is the **same template** `finalize_mono_codegen_view` (`monomorphise.rs:475`)
  already raises for the `MonoExpr::from_expr` `NotConcrete::Var` case — i.e. the
  fix **reuses the existing mono-ambiguity diagnostic**, just fired one step earlier
  (at the param-vector gate, before mangling) instead of at the body-conversion gate
  (after mangling, after registration). /dev's choice whether to factor the shared
  wording into one helper or mirror it; the design intent is **one message, fired at
  the earliest non-concrete observation**.
- **Location** — `ErrorLocation::from_span(call_span)` (or the defn span, matching
  the existing P7 site `:482`) so the user gets a source pointer to the offending
  self-call / definition. Either is acceptable; `call_span` points at the
  ambiguity-inducing self-call, which is the more actionable hint.
- **Error type** — `CranelispError::TypeError` today (matching the §4 backstop and
  the P7 site); migrates to `CheckError::AmbiguousType` post-FIXME-0098 with the rest
  of the typecheck error surface. No new error variant.

### 9.5 What this fix is NOT

- **NOT Face A.** Face A (annotated params → codegen `undefined function`) is a
  **backend/codegen** lowering defect (bare in-body name → mangled variant symbol),
  owned by `/design (backend)` + `/dev (src/)`. This typecheck fix addresses Face B
  only. The two faces have different owners; the repros disambiguate (0432 §"Proposed
  resolution").
- ~~**NOT a multi-clause inference change.**~~ **[S112 REVERSED — see §11.]** Under
  the drifted §5.1.2 this bullet held that the cross-variant self-call must NOT infer
  (propagating the first clause's call-shape into the second clause's params was
  "out of scope and arguably undesirable"). The S111-settled §5.1.2 makes that
  propagation **required**: `sum-to`/`rp4` type-check by exactly the back-flow this
  bullet declined. §11 designs it. The Pass-4 gate below (§9.3) is unchanged but now
  fires only when a clause param is *genuinely* unpinned after the self-call drain.
- **NOT the §3.11.1 backstop's job.** §4's position-complete scanner is unchanged;
  this gate is additive and Pass-4-interior. The two coexist — different positions,
  same predicate family (`is_concrete` here / `is_representation_undetermined` in §4;
  both reject a residual codegen-reaching `Var`).

### 9.6 Test seams (Phase-5 authoring by /qa + /dev)

- **Unit (typecheck, mandatory per CLAUDE.md "unit test per fix")** — the 0432 Face-B
  shape (unannotated multi-clause `defn` + cross-variant self-call) checked through
  `check_forms`/`pass4_monomorphise` asserts `Err(TypeError{ message contains
  "ambiguous type" … })` — **not** a panic. Pin it in `cranelisp-typecheck` (the
  S81-close ledger already tracks a 0344-tier unit red; this is its 0432 sibling). The
  test is **debug-built** (the panic only fired in debug), so it directly guards the
  divergence: pre-fix it panics, post-fix it returns the clean `Err`.
- **e2e (warranted — REPL/`--run` convergence)** — the same form via the REPL path and
  the `--run` path produce the **identical** ambiguous-type error (no panic, no
  divergence). This is the cross-mode guard the FIXME's two-face divergence demands;
  it also exercises the agent-validator path once layer b lands. `/qa` owns the
  narrow repro (0432 `target: /qa → /typecheck`); it converts the existing failing
  repro from RED to GREEN at the same diagnostic.
- **Containment interaction** — layer b (int `catch_unwind`) is independently tested by
  `/design (int)` / `/qa`; this fix removes the *trigger*, so post-fix a 0432-shaped
  module index produces a clean type error caught as a normal indexing failure rather
  than exercising the catch. Both land; the catch is the floor, the root fix removes
  the panic.

### 9.7 Cross-crate impact — zero edges

Confirmed **zero** `cranelisp-types` / `public-api.txt` / cache-schema impact
(matches `repl-embedded-agent.md §11.8`): the fix is an interior `Result` arm in
`monomorphise_call`, reusing the existing `CranelispError::TypeError` and the
existing `Type::is_concrete()` predicate. No new boundary type, no new variant, no
baseline movement. It is a **behaviour fix inside an existing crate**.

---

## 10. Cross-references

- `design/typecheck/typecheck.md` §9.3 — master-doc monomorphisation pointer (this
  doc is its structural-slot-gate-first elaboration).
- `design/typecheck/signature-match.md` — the Pillar-3 type-signature match predicate
  (S90 R6); a sibling typecheck capability that *consumes* the same `cranelisp-types`
  `Scheme`/`Type` this doc's mono instances produce.
- `design/arch/repl-embedded-agent.md §11.3` — the 0432 two-layer containment ruling
  (layer a = this §10 root fix; layer b = int `catch_unwind`).
- `design/arch/fixmes/0432-multi-clause-defn-self-call-codegen.md` — the defect
  (Face A backend / Face B this fix).
- `design/typecheck/traits.md` §6–§7 — constrained polymorphism + the as-built batch
  pipeline this doc completes; the termination Invariant (§8) lands there with the code.
- `design/arch/principles/20-model-invariants-by-representation.md` — the S84
  generalisation (slot ⟺ `is_concrete()`); the spine of §1–§2.
- `design/arch/bounded-contexts.md` §2 (structural-gate-primary + position-complete
  note) + §7 ("Callability is structural") + §3 invariant 9 (belt-and-braces: shared
  predicate + typecheck position-complete check + widened backend backstop).
- `design/arch/fixmes/0374-…` (re-shaped — corrected gate + systematic mono together),
  `0375-…` (backend assert as backstop, WIDENED), `0373-…` (rank-1 HM + ambiguity
  rule), `0379-…` (the positional hole) + `0380-…` (this §4 re-ground).
- `design/backend/ring2-rc.md` §1.6 — the parallel backend grounding for the WIDENED
  0375 RC-site backstop (the other half of the belt-and-braces split, §4.5).
- `crates/cranelisp-types/src/types.rs` — `Type::is_concrete()` (gate predicate) +
  `Type::is_representation_undetermined()` (the SHARED ambiguity/backstop predicate,
  §4.3) + `Type::contains_var()` (debug-tripwire backstop).
- `crates/cranelisp-typecheck/src/program.rs` — `find_ambiguous_top_level_form`
  (`:1503`) + the position-complete value-position scanner (was
  `find_ambiguous_let_binding` `:1522`); the retired local heuristic
  `is_ambiguous_codegen_reaching_type` (`:1584`).
- `crates/cranelisp-types/src/module.rs:1710` — `UserFnState` (the `Polymorphic` arm
  lands here, /arch-owned, §6).
- `crates/cranelisp-typecheck/src/{program,traits}.rs` — the gate sites (§2.2) + the
  enumeration spine (§3.1).

---

## 11. Multi-signature `defn` = separate mutually-recursive functions (S112 leg a, FIXME 0642)

**Status:** DESIGN + AS-BUILT AMENDMENTS. Phase-3 DESIGN (S112), then the W2 leg-(a)
change-set landed (uncommitted) and the W2 /review returned a BLOCK; the **W2.1
remediation** amendments below record what implementation legitimately discovered and
pin the fix for the Blocker: §11.3.1 (the as-built two-pass drain + self-call tag,
review deviation (ii)), §11.3.2 (the B1 self-call-`SigDispatch` fix shape), the
§11.3.3 paragraph (MS-6 definition-site check landed + M1 RULED — pre-drain check
is the specified WRITTEN-signature behaviour, user 2026-07-18), §11.4 step 3
(review deviation (i) — filter retained, drain-driven), and §11.5 (M3 double-mangle
note). Supersedes §9's drifted posture (banner atop §9). The binding spec is `spec/05-definitions.md` §5.1.2 +
§5.1.1 + §5.13.1 and §3.3 (annotations descriptive, no added rigidity), S111
commit `c9f05b64`. /arch directive (A2): **one inference path** — clause inference
rides the EXISTING §5.13.1 two-pass register-then-check machinery; do NOT keep a
bespoke multi-sig routine with the no-back-flow barrier "locally patched out."

### 11.1 The settled rule and the anchor

A multi-signature `defn` is **inference-equivalent to its clauses written as
separate, mutually-recursive top-level functions** that share one dispatched name.
A self-call from one clause to a sibling is an **ordinary call**: it resolves (by
arity, then same-arity by argument types, §7.4.4) to a specific sibling clause and
unifies the argument types with that clause's parameter types — pinning them, just
as a call to any separate function would. There is no independence barrier.

Anchor (0642), un-annotated:

```lisp
(defn rp4
  ([p rot]     (let [q (rp4 p rot 0)] p))        ; MUST infer (Fn [Int Int] Int)
  ([p rot idx] (add-i64 p (add-i64 rot idx))))   ; (Fn [Int Int Int] Int)
```

`add-i64` pins the 3-arg clause to `(Fn [Int Int Int] Int)` from its own body; the
2-arg clause's `(rp4 p rot 0)` resolves to that clause and pins `p`, `rot : Int`.
Identical to two separate mutually-recursive functions. The "multi-arity
memory-safety saga" dissolves: the earlier UAF was an artifact of the drift +
monomorphise-by-sibling, not a real defect — once the back-flow pins the 2-arg
clause's params to `Int`, a `(rp4 "x" "y")` call is a plain type error (String ≠
Int), never a wrong-accept.

### 11.2 The mechanism already exists — the barrier and the ordering are the bugs

The `{name}__v{i}` internal variant `Def`s ARE the "separate mutually-recursive
functions": Pass 1 (`check_form_register_multi_sig`) registers each clause's
signature via the SAME `register_defn_signature` a single-sig defn uses; Pass 2
(`check_form_body_multi_sig`) checks each clause body. A self-call to an overloaded
base is deferred at `infer.rs` as a `pending_overload_resolution` and drained by
`resolve_pending_overloads` (`register.rs:471`), which unifies the call's args with
the selected variant's params — **this unification IS the back-flow.** Two things
block it today:

1. **The barrier: LEG-1 `AmbiguityScanPhase::ClauseIndependence`**
   (`finalize.rs:1158`, `find_ambiguous_top_level_form`) runs the ambiguity scan
   PRE-drain over multi-arity defns with each clause's own param free-vars
   *subtracted* from `allowed_vars` (the CS-4.1 "clause params are non-polymorphic"
   structural subtraction, `finalize.rs:560–571`). It errors on `rp4`'s unpinned
   `p`/`rot` **before** the drain can pin them. This is the no-back-flow barrier.

2. **The ordering: concrete mangling precedes the drain.**
   `resolve_multi_sig_overloads` (Pass 2.5, `finalize.rs:1092`) runs BEFORE
   `resolve_pending_overloads` (Pass 5, `finalize.rs:1179`). It calls
   `resolve_variant_types` → `apply_subst`, reads the still-`Var` clause params,
   mangles `rp4$Var`, and installs a `Concrete{got_slot}` entry with a non-concrete
   body — a codegen leak waiting for a call. `refresh_multi_sig_variant_ret_types`
   (`register.rs:234`) already refreshes RETURN types post-drain but not params or
   the mangled NAME.

### 11.3 The design — collapse the scan, order the drain before concrete mangling

Two coordinated changes; both are "route through the existing machinery," not new
routines.

**(A) Collapse the ambiguity scan to ONE post-drain pass.** Delete
`AmbiguityScanPhase::ClauseIndependence` and its pre-drain call site, the
`collect_pending_overload_result_vars` benign-var scan, and the per-clause
param-free-var subtraction (`finalize.rs:560–571`). Multi-arity defns are scanned
by the SAME post-drain pass single-clause defns use (the former
`AmbiguityScanPhase::ValueScan`, now the only phase), with per-clause `allowed_vars`
computed the SAME way as a single-clause defn: the free vars of that clause's
**settled** (`apply_subst`-applied, post-drain) signature from
`accumulator.defn_type_vars[__vN]`. Consequences, each matching the spec:

- A clause param pinned by a sibling self-call (`rp4`'s `p`/`rot`) is concrete
  post-drain → not flagged. **(back-flow admitted)**
- A clause left **genuinely polymorphic** (`([:a x] x)`) has a non-empty
  `allowed_vars` from its own scheme → `defn_is_polymorphic` skip → admissible
  (§5.1.2 "a genuinely-polymorphic clause is admissible"), exactly as a single-sig
  polymorphic defn is.
- A clause param that is **genuinely** unpinned at a codegen-reaching position
  (neither its own body nor any sibling self-call pins it) → the §3.11 ambiguity
  error — the same disposition the equivalent standalone function would get. The
  `AmbiguousForm` message keeps its per-clause form (names the arity clause + param)
  but drops the false "each arity clause is type-checked independently (§5.1.2)"
  rationale (`finalize.rs:45–48`) — the settled reason is "the equivalent standalone
  function would also fail to infer it (§3.11)."

**(B) Order the concrete mangling to observe post-drain types.** The dispatch
selection during the drain needs only the `__vN` signatures (arity +
`types_compatible` shape) and a STABLE per-clause name to record in `SigDispatch` —
`select_unique_overload_variant` already tolerates a `Var` param (`types_compatible(Var,_)
= true`), so a call selects the right *clause* pre-concretisation. The **concrete
mangled name, the `Concrete` entry, the `OverloadVariant.{param_types,ret_type,
mangled_name}`, and the `SigDispatch` record for each self-call MUST all derive
from ONE `mangle_sig` over the FINALISED (post-drain, subst-applied) clause param
types** (Principle 7 — one mangle source, so entry-name and dispatch-name agree by
construction). Mechanically /dev picks either: (i) move
`resolve_multi_sig_overloads`'s concrete-variant registration to run after
`resolve_pending_overloads`, keeping only the dispatch table (`register_overloaded_base`,
selectable on `Var`-carrying params) before the drain and recording each
`SigDispatch` from the post-drain concrete mangle; or (ii) extend the existing
post-drain `refresh_multi_sig_variant_ret_types` to also refresh param types,
re-mangle, migrate the `$Var`→`$Int` entry, and patch the recorded `SigDispatch`
spans. (i) is the cleaner "resolve once"; (ii) is smaller-diff. Design intent: the
persisted concrete mangle reflects the back-flow; no `$Var` concrete entry survives.

### 11.3.1 As-built — the two-pass drain + the `is_self_call` tag (review deviation (ii): SOUND)

Implementation found the (A)/(B) sketch under-specified in one structural respect the
W2 /review accepted as SOUND (deviation (ii)): **concreteness of a call's arguments
alone does not classify how a self-call must be resolved.** The drain
(`resolve_pending_overloads`, `register.rs:665`) is therefore **two passes** over
`pending_overload_resolutions`, keyed on a new per-call `is_self_call` tag (added to
the pending tuple in `checker.rs` `CheckState` ~`:186`, set at the `infer.rs`
overload gate ~`:605`):

- **Pass 1 — self-calls UNIFY (monomorphic recursion).** A call to overloaded base
  `name` from inside one of `name`'s own `{name}__vN` clause bodies is a sibling
  self-call within the **letrec group** the §5.1.2 "separate mutually-recursive
  functions" equivalence names. It **unifies** the selected clause's params with the
  call args — pinning whichever side is unbound (the back-flow). It MUST NOT
  monomorphise: a fresh instantiation would discard the pin, leaving `rp4`/`rp15`'s
  poly clause forever unpinned and the whole §5.1.2 back-flow inert. Pass 1 runs FIRST
  so every clause's params are settled before any external dispatch selects.
- **Pass 2 — external calls dispatch-concrete or monomorphise.** An external call to a
  now-CONCRETE clause (own-annotated, or pinned concrete by a pass-1 self-call) unifies
  + dispatches to the concrete mangle; an external call to a genuinely-poly / trait-
  constrained TEMPLATE clause monomorphises at THIS call's args (fresh instantiation)
  so two external calls at distinct concrete types never conflict by globally pinning
  one template — the MS-2 two-instantiation cell.

**Why concreteness-alone was insufficient (the Phase-3 gap).** The same surface call
`(f …)` needs opposite treatment: a self-call must UNIFY (pin the sibling clause's
params in place), an external call must INSTANTIATE (leave the template unpinned).
Concrete args are present in both cases, so args-concreteness cannot distinguish them;
the monomorphic-recursion-vs-fresh-instantiation distinction is load-bearing and
orthogonal to concreteness. Hence a *tag*, not a concreteness test. (The pass-2
bifurcation is then keyed on the *clause's* concreteness, which is a different, sound
test — a pinned-concrete clause is a single callable; a `$Var` template is a mono
source.)

**The tag's three caveats (recorded; do not silently rely on).**

- **(a) Classification is textual.** `d == name || d.starts_with("{name}__v")` over
  `state.current_defn`. A user defn literally named `f__v1` calling overloaded `f`
  would false-positive as a self-call. Obscure; documented limitation, not fixed here.
- **(b) Mono-recheck blind spot (review finding I1) — FIXED, see §11.3.4.** During a
  template clause's mono recheck `current_defn` is the template's mangled name
  (`g$Var…`), not `g` or `g__vN`, so an inner self-call classifies as *external* and
  monomorphises rather than unifying — the seam of I1 (a genuinely-poly recursive
  clause wrong-rejects with an internal-name leak). **§11.3.4 records the as-built I1
  fix** (a mono-recheck monomorphic-recursion context) and its residual **R1**
  cross-arity boundary.
- **(c) Shadowing-blind (inherited, review M2).** The gate keys on
  `state.overloads.contains_key(name)` and does not account for a local binding
  shadowing `name`. Pre-existing single-sig blindness, **inherited** by the multi-sig
  path — not introduced by leg (a).

### 11.3.2 The B1 Blocker — the self-call `SigDispatch` MUST be derived post-drain

**Review Blocker B1.** The as-built self-call branch (`register.rs` ~`:770–780`)
derives its dispatch name **mid-drain**: immediately after its own `unify` it computes
`post = apply_subst(selected-clause-params)` and records
`SigDispatch(mangle_sig(base, post))` when `post` is concrete, else the `$Var`
template name. This is **order-dependent and B1-defective**. In a ≥2-hop delegation
chain — a 3-clause `f3` where clause 1's self-call targets clause 2 and clause 2's
self-call targets clause 3 — when clause 1's self-call is drained, clause 2's params
may still be `Var` (clause 2 is pinned only when *its* self-call drains later in the
same pass-1 loop). Clause 1's dispatch then records clause 2's `$Var` template name.
`finalize_multi_sig_variant_types` Phase A subsequently promotes clause 2 to `Concrete`
and **removes** the `$Var` template, re-pointing `OverloadVariant` /
`resolved_overloads` / the re-annotation name map — but **not**
`method_resolutions.resolved_calls` / the `record_dispatch_target` carrier. The
recorded `$Var` dispatch dangles → `user/f3$Var+Var` reaches codegen. This already
violates §11.3(B)'s existing MUST ("SigDispatch for each self-call MUST derive from ONE
`mangle_sig` over the FINALISED post-drain types") and is exactly the P22/P24
"resolution recorded against a name a later pass invalidates" recurring class the
review escalated.

**Fix shape — Option (1), DEFERRAL: derive the self-call `SigDispatch` in the
post-drain phase, never mid-drain (pinned normative for /dev).** Pass 1 keeps the
UNIFY (the back-flow must pin *during* the drain) but records **no** `SigDispatch`; it
defers each self-call site (span + selected clause identity) to a post-drain worklist.
`finalize_multi_sig_variant_types` — which **already** computes each clause's finalised
concrete mangle to register its `Concrete` entry (Phase A) — derives each deferred
self-call's `SigDispatch` from that SAME `mangle_sig` over the finalised post-drain
concrete params, **once**, and records it (plus `record_dispatch_target`).

**Why (1) over (2) (Principle 24 acid test).** The review named two candidates: (1)
defer the self-call `SigDispatch` to a post-drain fixup, or (2) have Phase A re-point
every resolved-call carrier it currently misses. Principle 24's test — *does the
outcome depend on pending-list order?* — separates them: under (1) the dispatch name is
a pure function of the finalised subst (confluent, order-independent), computed once,
after everything settles, with **nothing provisional to invalidate** — order-
independence *by construction*. Under (2) the name is still recorded provisionally
mid-drain and then repaired; any carrier the repair forgets re-leaks (the precise
failure mode B1 already is), and a future carrier added elsewhere is silently missed
again — order-dependence is *patched*, not eliminated, reproducing the published-
pointer hazard (Principle 22). **Choose (1)** — it makes order-dependence unrepresentable
rather than repaired.

**The carrier set that MUST agree** (all derived from ONE `mangle_sig` over the
finalised post-drain concrete clause params — Principle 7):

1. the `Concrete{got_slot}` symbol-table entry KEY (`concrete_mangled`, Phase A
   `st.insert`);
2. the base `DefKind::Overloaded` `OverloadVariant.{param_types, ret_type,
   mangled_name}` for clause `i` (Phase A re-point);
3. `state.resolved_overloads[base][i]` (Phase A re-point; also read by a rehydrating
   REPL cluster);
4. `multi_sig_mangled_names[base][i]` — the re-annotation name map that drives
   `finalize_annotations_and_publish` (Phase A re-point);
5. `state.method_resolutions.resolved_calls[self_call_span]` — the `SigDispatch` for
   each self-call (**the B1-missed carrier**);
6. the `record_dispatch_target` S110-0583 sig-dispatch carrier at the same self-call
   span (**also fed by that resolution; moves post-drain with (5)**).

Carriers 1–4 already agree (Phase A single-sources them). The fix moves the derivation
of **5–6** into the same post-drain pass and the same `mangle_sig` source, so all six
agree by construction. **The external-call branch is UNAFFECTED**: it runs in pass 2
after all self-calls have drained, so its `apply_subst(param_types)` is already fully
settled and its `mangle_sig` agrees with Phase A — only the pass-1 self-call branch,
exposed to intra-pass ordering, needs the deferral. /dev must add the u3 unit pin
(review I3) at the seam in the same change-set.

### 11.3.3 §5.1.2 dispatch coherence — definition-site check on WRITTEN signatures (MS-6 + M1 RULED)

Leg (a) added the same-arity-*unifiable* **definition-site** overlap check the
Phase-3 note flagged as owed (`register.rs:438–465`, in `resolve_variant_types`):
two same-arity clauses whose `concrete_params` unify (`types_compatible`) are now a
dispatch-ambiguity error **reported at the definition** (both clauses named by arity
index), not deferred to a call-site `Ambiguous`. The strict-equal duplicate case is
its exact-match subcase at the same site (`[:Int x]` + `[:a x]` now caught at the
definition, not only via a later `Ambiguous`). The call-site
`OverloadSelection::Ambiguous` stays as the residual backstop. This satisfies the
§5.1.2 MUST ("reported at the definition, both colliding clauses named").

**The pre-drain placement is the specified behaviour (M1 RULED, user 2026-07-18).**
`resolve_variant_types` (Pass 2.5) runs BEFORE `resolve_pending_overloads` (the
drain), so the overlap verdict reads each clause's params **as written** — the
pre-inference parameter annotations — not the types the back-flow drain later
settles. This is exactly what the spec now requires: the unifiability judgment "is
made on the clause signatures *as written* — the pre-inference parameter
annotations — never on the types inference later settles" (`spec/05-definitions.md`
§5.1.2, "[Settled 2026-07-18 (user ruling, M1)]"). The as-landed pre-drain check
implements precisely this reading; it is **correct as implemented**, not a
conservative approximation to be revisited.

```lisp
(defn t ([x] x) ([:Int y] y) ([a b] (t "s")))
```

This probe is **rejected by design**. The `[x]` clause's *written* signature (`x`
unannotated) can unify with the `[:Int y]` clause's `[Int]`, so the two same-arity
clauses are a definition-site ambiguity — **notwithstanding** that the internal
`(t "s")` self-call would pin `[x]` to `[String]` and thereby settle the two
disjoint post-drain. The spec ratifies exactly this outcome for exactly this
program (`spec/05-definitions.md` §5.1.2: the `(defn t ([x] x) ([:Int y] y) ([a b]
(t "s")))` worked example, "rejected **by design**"). The remedy is to annotate so
the written signatures are disjoint — `([:String x] x)`. The pre-drain check's
verdict (`[Var]` vs `[Int]`, `types_compatible(Var,Int)=true` → reject) is therefore
the specified verdict, and no /spec framing is owed: M1 is closed.

### 11.3.4 As-built — the I1 fix: a mono-recheck monomorphic-recursion context (review SOUND) + the R1 boundary

Caveat (b) of §11.3.1 (the mono-recheck blind spot) is the I1 defect: a genuinely-poly
recursive clause — e.g. the 1-arg clause of `(defn g ([x] (if true x (g x))) ([a b]
a))`, whose standalone twin `(defn g1 [x] (if true x (g1 x)))` accepts and runs — was
wrong-rejected, with the internal `user/g$Var$Int` mangle leaking into the diagnostic.
Root cause: during the mono recheck of the `$Var` template clause instantiated at
`Int`, the inner self-call `(g x)` classifies as *external* under the textual
`current_defn` tag (which is the template mangle `g$Var`, not `g`/`g__vN`), so it
pushes a `pending_overload_resolution` **after** the sole drain has already been taken
— an entry nothing ever resolves, leaving a residual var.

**The fix — design candidate 1, adjudicated SOUND by W2 /review.** A
monomorphic-recursion *context* threaded through the recheck, so an inner self-call to
the base at the same instantiation resolves **inline** as monomorphic recursion,
exactly as the standalone twin's self-call does:

- **The context.** `CheckState.mono_recheck_self: Option<(base, instance_mangled,
  instance_params, instance_ret)>` (`checker.rs:208–222`). Set ONLY at the drain's
  pass-2 template-instantiation site, via a new `origin_base: Option<&Symbol>` param on
  `monomorphise_call` (`traits/monomorphise.rs:185–201`). It is **stack-saved and
  restored** around the recheck; an inner hop's `monomorphise_call` passes `origin_base:
  None`, so a nested recheck runs with the context cleared — **nesting-safe** by
  construction (the §5 `saved_subst` isolation discipline, extended to this context).
- **The inline gate** (`infer.rs:608–655`). When `mono_recheck_self` names the called
  base AND the call's arity matches AND the call's `apply_subst`-resolved args **equal**
  the instance's concrete params (`ip == resolved_args`, same instantiation), the call
  resolves inline: unify the instance's params/return with the call, record
  `SigDispatch` to `instance_mangled`, and return — no pending entry pushed. A call at
  *different* args (a distinct instance or a sibling clause) falls through to the
  ordinary defer.
- **The load-bearing callee-`Var` retype** (`infer.rs:647–651`). The callee node — the
  overloaded base `Var`, which otherwise carries the polymorphic union type — is
  recorded (`record_expr_type` on `callee.span()`) as the instance's concrete
  `Fn(instance_params, instance_ret)`. This is **semantically exact**: at a
  monomorphic-recursion site the base occurrence *is* the instance. It is **correctly
  scoped**: `recheck_body_for_mono` save/restores `expr_types`, so the concrete typing
  lands only in the mono harvest, never in the outer program's type map. Without it,
  `finalize_mono_codegen_view::from_expr` hard-errors `NotConcrete::Var` on the still-
  polymorphic callee node (the from_expr gate requires every harvested node concrete).

Guarded green by `multi_arity_clause_param_51_2::recursive_poly_clause_accepted_
matches_standalone_twin` (the same-arity probe + its standalone-twin oracle fence).

**The R1 boundary — a KNOWN LIMIT of the as-built gate (review residual, Important).**
The inline gate fires only for a **same-instantiation** self-call (same arity, args ≡
the instance's concrete params). A **cross-arity** sibling self-call from a
genuinely-poly template clause is NOT covered: its args differ from the instance
params (different arity), so the gate does not fire, the call re-defers a pending entry
the drain has taken, and it orphans — the same wrong-reject-with-internal-name-leak
shape I1 fixed for the same-arity case. Probe:

```lisp
(defn g2 ([:a x] (g2 1 2)) ([:Int a :Int b] (add-i64 a b)))
;; (g2 5)  — the standalone twin (a poly 1-arg fn calling a concrete 2-arg fn)
;;           accepts and returns 3; the multi-sig g2 wrong-rejects.
```

Here the 1-arg poly clause's body self-calls the **2-arg** sibling `(g2 1 2)`; during
the 1-arg clause's mono recheck (`instance_params` = `[Int]`, arity 1) the arity guard
(`ip.len() == arg_types.len()` → `1 != 2`) skips the inline path.

- **Spec status:** wrong-reject under the §5.1.2 separate-mutually-recursive-functions
  equivalence (the standalone twin — a poly 1-arg fn delegating to a concrete 2-arg fn
  — accepts and runs `(g2 5)` = 3). **No regression:** this shape was *also* rejected
  pre-leg-(a) (it needed the same back-flow that did not exist); leg (a) narrows the
  rejected set, it does not widen it.
- **Natural fix direction (recorded, NOT designed now).** The inline gate could extend
  to a cross-arity sibling by resolving the self-call against the **post-drain-settled
  overload set** for the base (the `resolved_overloads`/`OverloadVariant` clauses,
  already concrete at Phase A) rather than only the single active instance: select the
  sibling clause by arity+args from that settled set and dispatch to its concrete
  mangle, exactly as the standalone twin's ordinary call would. This is a one-mechanism
  extension of the existing `mono_recheck_self` inline path (widen its match set from
  "this instance" to "the base's settled clauses"), not a new machinery — but it needs
  the settled overload set reachable at the recheck seam, which the current context
  does not carry. /testing pins the failing e2e (W4); **fix-or-carry is /sprint's later
  call** — this doc records the boundary and the direction, no full design this wave.

### 11.4 The constrained-poly × multi-sig cell (USER-RULED IMPLEMENT-IN-SPRINT)

A trait-constrained clause is spec-admissible under the equivalence rule — a
standalone `(defn g [:a x] (+ x x))` (`Num a`) is a constrained fn, so its multi-sig
twin `([:a x] (+ x x))` must be too. Today it is rejected-by-construction:
`collect_single_sig_defns` (`finalize.rs:1521`, the former `collect_defns`) filters
`if defn.is_multi_sig() { None }`, so `detect_constrained_fns` and
`pass4_monomorphise` never see multi-sig clauses; meanwhile
`register_mangled_variants` force-installs a bogus `Concrete{got_slot}` over the
clause's `Var` params. The `ConstrainedFn` single-variant invariant rustdoc
(`module.rs:2302`) documents the mutual-exclusion.

**Design — each constrained clause rides the standalone constrained-template path;
`ConstrainedFn` stays single-variant.** The key move: a constrained clause is its
OWN one-variant `ConstrainedFn` template under its own internal/mangled name, NOT a
new multi-variant `ConstrainedFn`. So `ConstrainedFn`'s field shape does **not**
change — only its rustdoc invariant note does (which asserts multi-sig ×
constrained is impossible). Steps:

1. **Keep the per-clause `Constrained` template.** `check_form_body_multi_sig`
   already sets a `__vN` to `UserFnState::Constrained(cf)` when its trial scheme has
   constraints (`body.rs:479–493`) — that stays. What changes is that Pass 2.5 must
   NOT overwrite it with a `Concrete` entry.

2. **`resolve_variant_types` / `register_mangled_variants` bifurcate on
   `trial_scheme.constraints.is_empty()`.** A constrained (or genuinely-polymorphic)
   clause is NOT a single concrete callable: register/keep a `Constrained` template
   entry under the clause's normalized-var mangle (`mangle_sig` over its
   `Var`-carrying params, e.g. `g$Var`) and record THAT name in the base's
   `OverloadVariant.mangled_name`. A concrete clause keeps today's path.

3. **The `is_multi_sig` filter in `collect_single_sig_defns` is RETAINED — the cell
   is DRAIN-DRIVEN, not filter-removal-driven (as-built, review deviation (i):
   ACCEPTED).** The Phase-3 sketch prescribed *removing* the filter so multi-sig
   clauses feed `detect_constrained_fns` / `pass4_monomorphise` as standalone
   constrained fns. Implementation found that literal removal unsound:
   `Defn::body()` / `Defn::params()` **assert single-variant**
   (`cranelisp-types/src/ast.rs:460`) and panic on a multi-sig defn, and the
   downstream single-sig readers would otherwise scan only variant 0. A constrained /
   genuinely-poly clause is instead reached through the **DRAIN**, not through
   `collect_single_sig_defns`: the `infer.rs` overload gate (~`:605`) keys a call to
   an overloaded base on `state.overloads` and defers it as a
   `pending_overload_resolution` (same-cluster registration + cross-cluster
   rehydration of `resolved_overloads`); at **pass 2** of the drain (§11.3.1) an
   *external* call whose selected clause is a `$Var` TEMPLATE entry — kept slot-less
   by the §11.4 bifurcation in `resolve_variant_types` (`register.rs`, the
   `is_template` re-key branch) — routes through `monomorphise_call` at the call's
   concrete args, producing/reusing concrete instances (`g$Var$Int`, …) via the
   established constrained-fn machinery, no backend special-case (§3.7 of the
   typecheck CLAUDE.md). This is the design — a drain-driven cell that rides the
   existing overload-resolution path — **not** a deviation from intent; only the
   *mechanism* (route via the drain, keep the filter) differs from the Phase-3
   filter-removal sketch, which the single-variant `Defn` accessor invariant forbids.

4. **Dispatch to a constrained clause routes through monomorphisation.** At the
   drain, `select_unique_overload_variant` picks the clause; when the entry at its
   `OverloadVariant.mangled_name` is `Constrained`, the call monomorphises at the
   concrete args and records the resolution to the INSTANCE, not the template
   (reading the entry kind — **no `OverloadVariant` field needed**, Principle 7; the
   kind already lives on the entry, persisted, rehydrated cross-cluster). The
   §5.1.2 same-arity-overlap rule keeps a constrained `[:a x]` clause and a concrete
   `[:Int x]` clause of the same arity a dispatch-ambiguity error — the admissible
   cell is a constrained clause at a NON-overlapping arity (as in the anchor:
   1-arg constrained + 2-arg concrete).

**`cranelisp-types` impact — no field change; rustdoc-only.** `ConstrainedFn`
(single-variant) and `OverloadVariant` (`{param_types, ret_type, mangled_name}`)
keep their shapes. The `ConstrainedFn` rustdoc invariant note + the "Future-state
note" (`module.rs:2302–2329`) become stale (they assert the filter makes multi-sig ×
constrained unconstructable) and must be updated to record that a constrained
multi-sig clause is now a legal one-variant template feeding the standalone mono
path. That file is /arch-owned → filed as FIXME `target: /arch` (see the report).
**`CACHE_SCHEMA_VERSION` 20→21 in the leg-(a) change-set** (settled: /arch ruling
on FIXME 0644, 2026-07-18, adopting /qa's §7.4 falsification in
`tests/plan/s112-0628-ic-wave.md`). The earlier "no bump" rationale here rested on
the premise that a stale schema-20 cache from the old compiler cannot contain leg
(a)'s state because the old compiler rejected the program — that premise is
**falsified** by the S111 B-2 wrong-accept family: `lf1`/`lf2`/`rp15`/`rp19`-shaped
programs WERE accepted by the old compiler, and `register_mangled_variants`
force-installed bogus `Concrete{got_slot}` entries over `Var` params, so `$Var`-mangled
`Concrete` state persists in schema-20 `.meta.json`. Under leg (a)'s model (§11.3(B):
no `$Var` concrete entry survives — a `$Var` mangle must reference a
`Constrained`/`Polymorphic` template) those same persisted bytes change meaning
(`cranelisp-types` CLAUDE.md's "meaning change to what an existing field records"),
and cache-hit typecheck bypass on unchanged source would resurrect the bogus entry
(the CS-2/P25 cache-trust class; source-hash does not save it). Leg (a) therefore
rides the sprint's single 20→21 window: it merges before b2 and carries the one bump
in its own change-set (b2 does NOT re-bump); if leg (a) ever landed alone it would
take the 20→21 bump itself. **Guard:** the AG-1 leg-(a) stale-cache cell (a cached
schema-20 module carrying a `$Var`-`Concrete` entry is refused wholesale on load) —
the failing-not-ignored repro that the bump satisfies.

### 11.5 Determinism obligation on the admitted-polymorphic/constrained mangle

`OverloadVariant.mangled_name` is persisted in `DefKind::Overloaded` in `.meta.json`;
a fresh-build byte-identity is a /qa gate. For a genuinely-polymorphic or constrained
clause the mangle must be a **normalized, session-independent var spelling — never a
`t{id}`**. This is already satisfied by the ONE canonical mangler
(`support.rs::mangle_type`, FIXME 0519): `Type::Var(_) => "Var"` — a constant, not
the var's `TypeId`. So a 1-arg poly clause is `f$Var`, a 2-arg is `f$Var+Var`;
distinct arities are distinct, and any two same-arity clauses that would mangle
identically necessarily can-unify → the §5.1.1 dispatch-ambiguity error, so no two
distinct admitted clauses ever collide on `$Var`. The one spelling to keep OUT of a
persisted overload mangle is `TyConApp(id) => "TyCon{id}"` (session-dependent), but
`TyConApp` is inference-only and resolved before a variant is finalised — the design
requires the finalised clause param types feeding `mangle_sig` to be `TyConApp`-free
(they are, post-substitution). If a future change ever wanted position-sensitive var
spellings, it MUST be a canonical left-to-right renumbering (`a,b,c…`), never raw
ids; the constant `"Var"` is sufficient and deterministic today.

**Known grammar wart — template mono instances DOUBLE-mangle (review M3).** When an
external call monomorphises a `$Var` template clause (§11.3.1 pass 2 / §11.4 step 3),
`monomorphise_call` builds the instance name over the *already-mangled* template name,
so a 1-arg poly clause `g$Var` instantiated at `Int` mints `g$Var$Int` (two `$`
segments), not `g$Int`. This is **deterministic** — a pure function of (template name,
concrete args) — so the fresh-build byte-identity obligation (§11.5, /qa gate) holds;
it is not a soundness or collision hazard. But `$Var$Int` **leaks into diagnostics and
persisted `.meta.json` names**, where it reads oddly. Recorded as a known mangled-name-
grammar wart under the FIXME-0519 one-canonical-mangler context (§3.5); **no redesign
this sprint** — a grammar that collapses the template segment for an instance would be
a §3.5-wide change, out of leg-(a) scope.

### 11.6 Leg (c) framing only — return-type-dispatch codegen (repro-gated)

Leg (c) is repro-gated (SPRINT §Architecture review) and NOT designed here (no
backend fix). Recorded for fast Phase-5 routing: the well-formed conventional
return-poly trait (`(deftrait Zeroable (zed [] self))` + Int/Float impls) with a
RESOLVED use (`:Int (zed)` → selects `Zeroable.zed$Int`) must run end-to-end
(§7.1.1 note; §3.3.3 MUST (d)). The 0628-tail `undefined function: zed` leak is on
that resolved path — the backend calls `zed` bare instead of the resolved instance.
The typecheck-**producer**-side attribution (if the repro lands producer-side inside
the schema-21 window) is: populate the `resolved_targets` span-keyed sidecar
(`backend-keyed-consumer.md`; `design/typecheck/return-poly-dispatch-signal.md`) at
the resolved return-type-dispatch call span with the concrete instance's storage
key (`Zeroable.zed$Int`), so the backend does a keyed fetch (`entry_at`) rather than
re-resolving the bare method name (which has no concrete GOT slot). If the repro is
mode/context-dependent and fires only backend-side, it is `/design(backend)`'s. The
pinned cross-mode repro comes first (standing dual-path rule); attribution follows
evidence.

### 11.8 The W2 mono/carrier family — one settled-overload-derived producer change-set (R1×2 + R2 + D3)

**Status:** DESIGN (S113 Phase 3, /design(typecheck)). The S112-pinned family
(`tests/multi_arity_clause_param_51_2.rs` R1×2, `tests/multi_sig_base_mono_carrier_loss.rs`
R2, `tests/multi_sig_poly_callee_cross_arity_mono.rs` D3) shares ONE root and lands
as ONE producer change-set (arch Q2/revision 3; SPRINT §Scope B). This section
records the D3 call-chain evidence (the arch-Q2 obligation, produced BEFORE the fix),
the settled-state ordering finding that unifies the three, and the fix shape. TB-24,
D1, and the D2 accept path are producer-side siblings recorded in `traits.md` §D2/§TB-24
(dispatch/impl-target seams) — they are NOT part of this mono-harvest change-set.

#### 11.8.1 D3 call-chain evidence — where the mono request is dropped (attribution VERDICT)

The D3 repro (primitives-only):
```lisp
(defn idpoly [x] x)                              ; genuinely-poly single-sig callee
(defn build ([n]     (build n 0))                ; 1-arg clause delegates cross-arity
             ([n acc] (if (eq-i64 n 0) acc
                          (build (sub-i64 n 1) (add-i64 acc (idpoly n))))))
(build 3)   ; → codegen error … undefined function: idpoly
```

Both `build` clauses settle **concrete** (`build$Int`, `build$Int+Int`): the 2-arg
clause is pinned `Int` by the primitive ops, the 1-arg clause by its `(build n 0)`
self-call to the 2-arg clause. Neither is a `$Var` template, so neither is
monomorphised via `monomorphise_call`/`recheck_body_for_mono` — they register as
concrete mangled variants directly (`register_mangled_variants`, §11.3(B) Phase A).

**The drop point.** `pass4_monomorphise` (`finalize.rs:1015`) is the ONLY seam that
mints a mono instance for a poly callee and records its `SigDispatch`. Its work list
comes from `collect_mono_call_sites` (`mono_collect.rs:119`), which iterates the defn
set `single_sig_defns = collect_single_sig_defns(working_program)` (`finalize.rs:999`).
`collect_single_sig_defns` (`finalize.rs:1391`) **filters out every multi-sig defn**
(`if defn.is_multi_sig() { None }`). Therefore `build`'s clause bodies are never
scanned; the inner call `(idpoly n)` in the 2-arg clause body is never collected by
`collect_local_parametric_calls`; `idpoly$Int` is never minted; the concrete variant
`build$Int+Int` reaches codegen with a bare `idpoly` call whose name has no GOT slot
→ backend keyed read misses → `undefined function: idpoly`.

The filter is **retained by design** — `Defn::body()`/`params()` assert single-variant
and panic on a multi-sig defn (`cranelisp-types/src/ast.rs:460`; §11.4 step 3) — so the
multi-sig path was routed through the DRAIN instead. But the drain
(`resolve_pending_overloads`) records `SigDispatch` for **overloaded-base dispatch
calls** only; it does **not** mint mono instances for a *distinct poly callee* reached
from a clause body. So a poly hop in a multi-sig clause body falls into the gap between
the two mechanisms: the single-sig mono-collect (excluded by the filter) and the drain
(which does not mint leaf instances).

**Verdict: CONFIRMED typecheck-only, producer-side, P26-shaped, same family as R2
(`class=carrier-loss`).** The backend is a pure keyed consumer (BC §3 invariant 10) —
the fix is architecturally excluded from it; the sole admissible backend delta is
**diagnostic hardening** (raw Cranelift `undefined function` → the located P24
hard-fail at the keyed seam, `backend-keyed-consumer.md` §1.2). No `cranelisp-types`
diff. The "cross-arity" framing in the repro is the /port-found shape, **not** the
load-bearing mechanism: the excluded-body fault fires for a poly hop in *any* multi-sig
clause body; the cross-arity delegation is why the clause is *reached* at all in the
/port program. /dev verifies the minimal-firing form during implementation (the fix
covers both).

#### 11.8.2 The unifying root — the harvest does not cover multi-sig dispatch, and where it partially does it runs PRE-drain

R1, R2, D3 are three faces of one gap: **the monomorphisation harvest does not cover
multi-sig dispatch/bodies, and the one place it partially does — the pass-4 mono
recheck — runs before the overload set is settled.**

- **D3** — a concrete multi-sig CLAUSE body's inner poly hop is never scanned
  (`collect_single_sig_defns` filter, §11.8.1).
- **R2** — a multi-sig-BASE dispatch call `(h 1)→h$Int` inside a monomorphised body
  (`ga$Int`, minted at pass-4). During `recheck_body_for_mono`, the inner scans handle
  only CONSTRAINED self-recursion (`resolve_inner_constrained_calls`) and
  monomorphisable-poly hops (`monomorphise_inner_parametric_hops`) — **neither handles
  an overloaded-base dispatch**, so `(h 1)` gets no `SigDispatch`/`resolved_target`
  carrier and the backend keyed read misses (`class=carrier-loss`).
- **R1** — a cross-arity sibling self-call from a poly TEMPLATE clause's mono recheck.
  The inline `mono_recheck_self` gate (`infer.rs:608–655`) fires only for the
  SAME-instantiation self-call; a cross-arity sibling's args differ (different arity),
  the gate skips, the call re-defers a pending entry the drain has taken, and it orphans
  as a wrong-reject with an internal-name leak (§11.3.4 R1 boundary).

The **ordering** is the structural cause. In `finalize_check_result_inner`:
`pass4_monomorphise` (line 1015) → `regeneralize_defn_schemes` (1024) → drain
`resolve_pending_overloads` (1046, **the multi-sig settlement point**) →
`regeneralize_only_polymorphic` (1073) → ambiguity scan (1088) →
`finalize_multi_sig_variant_types` (1122, **Phase A promotes back-flow-pinned clauses
to Concrete — the final settled overload state**) → re-annotate (1137+). Pass-4, where
R1/R2's mono rechecks happen, runs **pre-drain**: the base `OverloadVariant`s are
registered (Pass 2.5, line 990) but back-flow promotions have not run, so a self-call
to a back-flow-pinned sibling would resolve to its `$Var` template mangle, not the
concrete one — the exact pre-settlement hazard §11.3.2 (B1) fought. **This is why the
§11.3.4 R1 direction says the settled overload set "is not reachable at the recheck
seam."**

#### 11.8.3 The fix — a settled-overload-derived harvest for multi-sig-touching cases

One change-set, one settled source (P26 "Record from settled state"; P24 "Resolve
once"): every multi-sig-touching mono resolution derives from the **post-drain,
post-Phase-A overload set** — the base `OverloadVariant`s after
`finalize_multi_sig_variant_types` (the concrete mangles the drain already recorded in
each caller's `SigDispatch`, so the harvest agrees with the drain by construction).
Three legs off that one source:

**AS-LANDED (S113 W2a, review APPROVE — records the settled state, P26).** The design's
three legs were implemented, and the R1/R2 pair was **superseded in review** by a cleaner
P7 unification (see below). What landed:

- **Leg D3 — a SECOND `pass4_monomorphise` at the post-Phase-A settlement point** (option
  (i) below, `finalize.rs:1132–1160`). The single-sig pass-4 collector
  `collect_single_sig_defns` was generalised to `collect_defns_for_mono(program,
  MonoDefnFamily::{SingleSig|MultiSig})` — **one parameterized fn at two settlement
  points, not a forked sibling** (arch W2a pin). The `MultiSig` family iterates each
  concrete clause variant's body (never `defn.body()`, which panics on a multi-sig defn)
  and feeds it to the SAME `pass4_monomorphise`, run AFTER `finalize_multi_sig_variant_types`
  (so every clause is settled concrete) and BEFORE the sweep/re-annotate (so the minted
  `idpoly$Int` + its `SigDispatch` reach the accumulator that rebuilds each variant's
  `codegen_view`). A `debug_assert_eq!` pins that `SingleSig + MultiSig` **partition every
  top-level `Defn` exactly once** (P18 — a later-added defn family reaching neither fails
  loudly).
- **Legs R1 + R2 — ONE scoped invocation of the real drain** (`recheck_body_for_mono`,
  `monomorphise.rs:784–843`), replacing BOTH the design's bespoke `resolve_inner_multi_sig_dispatch`
  scan (R2) AND the inline-gate widening (R1). The design's bespoke scan was implemented
  and **rejected in review** as a partial re-implementation of the drain (it wrote the
  template `$Var` mangle into a frozen mono view, did no return-var unification, and
  orphaned post-drain pendings). The landed shape: `recheck_body_for_mono` **isolates the
  outer `pending_overload_resolutions` via `mem::take`**, runs the body check (which defers
  the body's own overloaded-base dispatch calls), invokes the **one real drain**
  `resolve_pending_overloads` scoped to just those deferrals, then restores the outer
  pendings (`register.rs`'s drain widened to `pub(crate)`). This gives **full
  concrete/template bifurcation + return-var unification by construction** (P7 — one drain,
  no second implementation). It subsumes R1's cross-arity boundary: the same-instantiation
  self-call still resolves **inline** (the `mono_recheck_self` gate, unchanged, `infer.rs:615`
  — never pushed, so drain pass 1 is a no-op in a mono recheck), while a **cross-arity**
  sibling self-call now simply **defers and the scoped drain resolves it** against the
  settled overloads — so the §11.3.4 "widen the inline gate" direction was **not needed**;
  the scoped drain covers it. Because `recheck_body_for_mono` fires at BOTH pass-4
  settlement points, R1/R2 hold for any minted body regardless of which point drove it.

**Ordering — option (i) landed.** These resolutions MUST read the **settled** overload
set; the design offered **(i)** a post-`finalize_multi_sig_variant_types` harvest vs **(ii)**
threading the settled set to pre-drain pass-4. **(i) landed** for D3 (the second
`pass4_monomorphise` at `finalize.rs:1132`) — the P26/P24 "record once from settled state"
shape, leaving the single-sig pass-4 (line ~1015) and its 0349 → `regeneralize_defn_schemes`
chain untouched. The recheck-seam scoped drain (R1/R2) needed no relocation at all — it
settles the body's own deferrals in place via the mem::take isolation, so the pre-settlement
`$Var` hazard §11.3.2 closed never reopens (a genuinely-poly selected clause monomorphises
to a concrete instance, never a slot-less `$Var` template mangle).

#### 11.8.4 Pin-4 entanglement — carrier family lands before R1-variant flips are judged

The prelude-`+` R1 variant (MC-R1v) is entangled: the trait-`+` standalone twin itself
hits carrier-loss (the doubled `user/user/fb$Int+Int` prefix — R2-family evidence,
`tests/plan/s113-test-plan.md` MC-E1). **Binding sequencing for W2** (a design
constraint on the change-set, not on the code): land/verify the carrier family (R2 +
D3, legs above) BEFORE judging the R1-variant flips. A non-flip of MC-R1v after the R1
inline-gate widening is NOT a failed fix — check the carrier face first (does the twin
now run under the R2 leg?), and only then re-attribute. If the doubled `user/user/`
prefix survives the carrier fix it is a distinct mangle/keying defect (R4 register-row
candidate) — pin it separately, do not fold silently.

#### 11.8.5 Inversion fences — what must STILL reject after the accept/carrier fixes land (spec-diff)

The W2 family is accept-side (D2, TB-24) and carrier-side (R1/R2/D3) — it mints
instances and writes carriers for calls in **already-accepted** programs, and roots
dispatch differently. It touches **no reject seam**, so every §5.1.2/§3.11/§8.6.4
rejection is preserved by construction. Named so /dev + /review do not overshoot into a
wrong-accept (the S112-1 dominant hazard):

- **§5.1.2 same-arity-unifiable definition-site ambiguity STILL rejects.** The
  unifiability judgment on WRITTEN clause signatures (the pre-drain MS-6/M1 check,
  §11.3.3) is untouched — the mono harvest runs post-drain over already-accepted clauses
  and cannot resurrect a definition rejected earlier. `(defn t ([x] x) ([:Int y] y) …)`
  stays rejected (§5.1.2, settled M1).
- **§3.11 bare-`(zed)` ambiguity STILL fires.** The D2 home-rooting changes only WHERE
  the impl is looked up; a return-type-dispatch call with no concrete dispatch type still
  returns `None` at `try_resolve_trait_method` step 3 (`concrete_type_name` = `None`) and
  defers to the §3.11 gate. Only the RESOLVED cell (`:Int (zed)`) accepts.
  (`spec_07_traits.rs::return_type_dispatch_unresolved_bare_call_clean_ambiguity_neg`
  stays GREEN.)
- **§8.6.4 duplicate method-import conflict STILL rejects** (traits.md §7.0.1 watch-cell
  (b)) — a different, earlier seam than dispatch.

This is the spec-diff (arch process rule, S112 finding): the spec cases touched — §7.11.2
(a)–(e), §5.1.2 (cross-arity self-call / clause-as-separate-fn / same-arity-unifiable
reject), §3.11 (resolved-vs-ambiguous) — are each covered by a design cell (§11.8.3 legs
+ traits.md §7.0.1/§3.2) or a named inversion fence above. The diff is **empty**: no spec
case touched by this family is unaddressed, and every must-still-reject cell is named.

#### 11.8.6 No schema bump — carrier + settlement check (arch Q5/revision 4)

All three legs write only to existing carriers — `MethodResolutions.resolved_calls`
(`SigDispatch`) and `.resolved_targets` (`FQSymbol`), and mono entries via
`register_mono_entry` — with **no shape change**, so **W2 = no `CACHE_SCHEMA_VERSION`
bump** (the expectation SPRINT §Scope B pins). Writing MORE span→resolution entries for
a program that previously **failed to compile** is additive population, not a
meaning-change to a persisted field. There is no stale-cache resurrection hazard: unlike
leg (a) — whose 20→21 bump was forced because old-compiler-ACCEPTED programs had bogus
`$Var`-`Concrete` persisted entries (§11.5) — all three W2 programs were **rejected /
codegen-failed** by the old compiler (D3/R2 codegen `undefined function`; R1
wrong-reject typecheck error), so no successful `.meta.json` was ever persisted for them
and no AG-1 stale-cache cell arises. **If** implementation discovers any persisted-carrier
shape change is required (e.g. an `OverloadVariant` field), STOP and file FIXME
`target: /arch` — do NOT design around it (SPRINT §Scope B constraint).

#### 11.8.7 Let-shadowing at the call head — rulings 4 & 5 (re-routed into W2, /sprint 2026-07-19)

Two S112 shadowing pins (`tests/shadowing_scope_lookup.rs`) were re-routed from src/ into
W2. Both assert the §4.6/§5.1.2 rule: **a `let`/`fn`/param binding lexically shadows a
same-named top-level defn — a call to that name inside the binding's scope MUST resolve to
the LOCAL binding.** Ruling 5 is typecheck (designed here, at R1's gate); ruling 4's
evidence contradicts the typecheck routing (reported below).

**Spec-diff — the lexical-shadow class vs the §8.6.4 conflict class (requirement (b)).**
These pins are the **§4.6 lexical-shadow** class, categorically DISTINCT from the §8.6.4
def-over-binding conflict class:
- **§4.6/§5.1.2 — lexical shadow (local WINS, always legal).** A `let`/`fn`/param binding
  is an ephemeral LEXICAL binding, not a module registration. It shadows any outer binding
  of the same name within its scope — including the module's own top-level defn. This is
  the fundamental lexical-scoping rule; the inner reference resolves to the nearest
  enclosing binding. `(defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))` — the inner `(s1 x)` is
  the local identity, full stop.
- **§8.6.4 — def-over-in-scope-binding conflict (error, never a shadow).** A top-level
  DEFINITION (`defn`/`deftype`/…) over a name already in scope via IMPORT/export/prelude
  is a compile-time CONFLICT (`reject_def_over_binding`; the "no outer scope — prelude is
  an implicit import" ruling). A same-MODULE prior def is redefinition (allowed).
- **The boundary is binder KIND, not name-collision.** §8.6.4 governs *definitions*
  (registering binders) colliding with *imports*; §4.6 governs *lexical bindings* (let/fn/
  param) shadowing *anything*. A `let` is neither a definition nor subject to §8.6.4 — so
  a `let` shadowing the module's own defn is a pure §4.6 shadow, doubly-not-a-conflict (not
  a def; and even a def would be same-module redefinition). No overlap with the pins.

**Ruling 5 — the multi-sig overload gate bypasses local scope (DESIGNED, typecheck).** The
gate at `infer.rs:604` — `if Expr::Var { name } && state.overloads.contains_key(name)` —
consults the GLOBAL overloads table by name **without first consulting local scope**, so a
let-shadowed multi-sig base (`(defn t1 [x] (let [m1 (fn [y] y)] (m1 x)))`, `m1` a base)
enters the overload-dispatch path, defers past the drain, and wrong-rejects
(`undefined variable: t1`) — the local binding never gets a look-in.

**Fix — local-scope-first, reusing the recursion-self-ref discriminator (composes with the
R1 leg).** The guard must skip the overload path for a USER shadow while STILL admitting a
genuine self-recursive multi-sig self-call (the §5.1.2 back-flow path) AND the R1 mono
recheck's cross-arity self-call. The exact discriminator already exists — it is the same
one `record_reference_target`'s self-recursion carve-out uses (`checker.rs:1489`):

> `is_recursion_self_ref(state, name)` ≝ `state.current_defn.as_deref() == Some(name) &&
> state.env.lookup_frame(name) == state.current_defn_frame` — TRUE iff `name` resolves at
> the enclosing defn's recursion-binding frame (the self-reference), FALSE for a `let`/`fn`
> binding that resolves at a DEEPER frame or a param of a differently-named enclosing defn.

Gate the outer `if` with `(state.env.lookup(name).is_none() || is_recursion_self_ref(state,
name))`: enter the overload path iff `name` is NOT locally bound at all, OR it is the
genuine recursion self-reference. **No schema bump:** a shadowed call SKIPS the overload
gate and falls through to ordinary local inference (callee infers as the local `fn` value →
indirect call, no carrier) — no new carrier, no shape change (requirement (d) ✓).

**AS-LANDED (S113 W2a→W2 close, `infer.rs:604`+, review APPROVE).** The guard landed as
designed. One composition-argument correction (recorded honestly for P26): my Phase-3 text
claimed "during a mono recheck the self-call's base is NOT locally bound (`recheck_body_for_mono`
binds only the instance mangle)" — **that claim is FALSIFIED**: a `let`-rebind of the BASE
name inside a mono-recheck body DOES locally bind the base, so `env.lookup(base)` is `Some`
there. The **ruling-5 gate composition survives the correction** — a let-rebound base in a
mono recheck is exactly the case the guard is FOR (local wins), and it is pinned by
`ruling5_composition_let_shadowed_multi_sig_base_in_mono_recheck`. The other verified
composition facts hold: a locally-shadowed call never defers (so the §11.8.3 scoped drain
never sees it — `monomorphise.rs:809`), R1 same-instantiation self-calls resolve inline
without pushing, and nested rechecks see an empty pending list (the `mem::take` isolation).

**Ruling 4 — single-sig hang: LANDED as a typecheck PRODUCER fix (correcting my Phase-3
"not typecheck" verdict).** My Phase-3 evidence — that `record_reference_target`'s
frame-guarded shadow gate (`checker.rs:1489`) correctly records **no** `resolved_targets`
carrier for a let-rebind (the `lookup_frame("s1")` = let frame `F+1` ≠ `current_defn_frame`
= `F` discrimination) — was CORRECT, but its conclusion ("therefore the fault is downstream
in `MonoExpr`/backend") was wrong. The producer fix consumes exactly that frame-guarded
verdict, in typecheck:

- **`record_self_recursion_dispatch` (`monomorphise.rs:387`) consumes the verdict via
  CARRIER-PRESENCE on the callee span.** The mono self-recursion carrier writer collects
  self-`Apply` calls (`collect_self_apply_calls` — which now carries the **callee span**
  alongside the arg/self spans, `monomorphise.rs:1189`) and, before minting a `SigDispatch`,
  checks `resolutions.resolved_targets.contains_key(callee_span)`. A genuine self-call
  recorded a callee carrier (the base resolves at the recursion frame → `record_reference_target`
  wrote it); a **deeper-frame `let`/`fn`/param shadow recorded NONE** (the shadow gate
  returned early). So a self-apply whose callee span carries **no** carrier is a shadow:
  record **no** `SigDispatch`, **no** carrier → the `Apply` reaches the backend fully bare →
  `compile_var_apply` → `variables` → **indirect local call** — fixing both the TCO-self-loop
  hang and the non-tail wrong-value sibling.
- **Why carrier-presence, not re-evaluating the frame guard (review ruling — the faithful
  consumption).** `record_self_recursion_dispatch` runs in the recheck EPILOGUE, when the
  scope frames of the body check are already **torn down** — the frames are dead at the
  classifier, so directly re-running `is_recursion_self_ref` there would be unsound (it has
  no live frames to consult). The `resolved_targets` carrier, recorded DURING the body check
  when the frames were live, is the durable materialisation of that same verdict. Reading it
  is the faithful, resolve-once (P24) consumption — the shadow discriminator is computed
  ONCE (at `infer_var`) and every downstream consumer reads the carrier, never re-derives.

**Verdict (ruling 4): a typecheck producer defect, FIXED in typecheck.** The Phase-3
"downstream / not typecheck" verdict is retracted — the carrier-absence IS the signal, and
the mono self-recursion writer was the producer that ignored it (minting a name-matched
`SigDispatch` for a shadow). The `MonoExpr`/backend local-before-name path was never the
locus; the producer simply must not emit a keyed dispatch for a carrier-absent (shadowed)
self-apply. This is the same discipline generalised to the pass-4 collectors in §11.8.8.

#### 11.8.8 The scan discipline realised — name is a TRIGGER, carrier is the IDENTITY (FIXME 0653 second prong)

Ruling 4's producer fix (§11.8.7) is one instance of a general rule the W2 close generalised
across every name-scanning mono collector, closing **FIXME 0653's second prong**: a name-scan
collector's AST callee **name** is only a TRIGGER for consideration; the reference's
**identity** is the per-span recorded `resolved_targets` carrier. A callee whose span carries
NO carrier resolved to a §4.6 **local** — a `let`/`fn`/param binding shadowing a top-level
constrained/parametric fn — because `record_reference_target`'s frame-guarded shadow gate
declined to record it. Minting/dispatching such a call by name-match would silently wrong-value
the shadow to the top-level fn (the same class as the ruling-4 hang, one hop out).

**The ONE shared guard (P7): `program::support::callee_has_keyed_carrier(resolved_targets,
callee_span)`** (`support.rs:18`) — returns TRUE (proceed) iff the callee span carries a
`resolved_targets` entry, FALSE (skip — it is a shadow) otherwise. Consumed at **six** sites:
the five pass-4/mono-recheck collectors — `collect_local_parametric_calls`,
`collect_imported_constrained_calls`, `collect_constrained_calls_excluding_self` (top-level,
reading `state.method_resolutions.resolved_targets`), and `resolve_inner_constrained_calls` /
`monomorphise_inner_parametric_hops` (mono-recheck epilogue, reading the harvested
`resolutions.resolved_targets`) — plus the self-apply collector (§11.8.7). This is the
P26/P24 shape at its cleanest: the shadow verdict is computed ONCE (the frame guard at
`infer_var`), materialised ONCE (the carrier), and every collector reads the carrier rather
than re-deriving from a name — the name-scan is a candidate generator, the carrier is the
authority. Cross-ref FIXME 0653 (the corollary this realises: resolved identity, not a bare
name, is the currency past a resolution seam).

#### 11.8.9 MC-X2 — imported multi-sig bases: lazy rehydration + carrier home-override (P24, review conditionally-sound)

A multi-sig base IMPORTED from another module is invisible to the local `state.overloads` /
`resolved_overloads` tables (those are seeded from the local registration path), so a call
`(h 1)` to an imported base `h` — bare after import, or qualified `mlib/h` — never entered
the overload-dispatch path and mis-resolved. Landed cure:

- **Lazy rehydration** — `infer.rs::maybe_rehydrate_imported_overload_base` (`infer.rs:588`,
  called at the `infer_apply` callee seam) chain-follows `name` to its terminal entry; when
  that terminates at an `Overloaded` entry in a DIFFERENT module, it mirrors the local
  rehydration into `state.overloads` + `state.resolved_overloads` AND records the base's HOME
  in a new transient `CheckState.overload_homes: HashMap<Symbol, ModuleFullPath>` (`checker.rs:193`).
  Idempotent (guards on `contains_key`); a base referenced both bare and qualified double-keys
  `overload_homes` harmlessly (both map to the same home).
- **Carrier home-override at the ONE drain** — `resolve_pending_overloads` (`register.rs:868`)
  keys the `SigDispatch` mangle by the BARE base name via the ONE `mangle_sig`
  (`register.rs:861–862` — Phase-A-consistent: the stored concrete clause `Def` is `h$Int` in
  `mlib`, and the bare-name mangle serves both the bare and qualified faces), then **overrides
  the `resolved_target`** to `{home, mangled}` from `overload_homes` — because
  `record_dispatch_target`'s `SigDispatch` arm assumes the mono lives in `current_module`
  (true only for a LOCAL base). A local base has no `overload_homes` entry → no override. This
  also cures the same current-module face for the W2a scoped-drain carrier (§11.8.3 — it is
  the ONE drain both paths use, P7).

**Review verdict: conditionally sound.** The qualified-face mangle re-derives the bare base
name from the qualified reference (`rsplit('/')`) rather than carrying the storage base name
as resolved data — the P24-corollary smell (FIXME 0653: a bare name re-derived past a
resolution seam). It is sound TODAY (the storage entry is uniformly bare-mangled, Phase-A
consistent), so it landed with a **tripwire row in the 0632 register** rather than a redesign.
**Retirement path:** carry the storage base name as resolved data (an FQ on the rehydrated
overload record) so the mangle reads it rather than re-splitting the reference — folds into the
0653 "resolved identity is the currency" sweep. Recorded here so the S114 P26 sweep (typecheck.md
§9.7) picks up `overload_homes` and this re-derivation as classified carriers.

#### 11.8.10 The settlement harvest window — the SETTLED three-invocation shape (S114 W7, W3-review Important-2)

**Status:** SETTLED CONTRACT (S114 W7 /design(typecheck); the W3-review
Important-2 disposition). The W3 review found that the number of
`pass4_monomorphise` *invocations* — the "settlement harvest windows" — grew
**1 → 2 → 3** across S112 → S113 → S114, and routed the choice here:
**scribe the settled multi-window shape with its idempotence obligations as the
documented contract, OR design the single-settlement convergence as an S115 work
item.** Verdict: **SCRIBE** — the three windows are each a legitimately-distinct
settlement point, the idempotence is verified (W3 review: "P26 acid test PASSES
on the re-harvest; a pre-drain mint cannot disagree with its re-derivation;
idempotence verified in code"), and the convergence is NOT free (it must
re-derive the 0349 → `regeneralize_defn_schemes` → `register_test_fn_mono_roots`
ordering — §below). The single-settlement convergence is recorded as a NOTED
S115 option, not committed.

**The three windows (all `finalize.rs`, in `finalize_check_result_inner`):**

| # | Site | Family | Settlement window it records from | Why a distinct window |
|---|---|---|---|---|
| 1 | `finalize.rs:1023` | `SingleSig` | **PRE-drain** (immediately before the FIXME-0349 `regeneralize_defn_schemes`) | The common-case harvest; its call-site result propagation (`monomorphise_call`) pins caller result vars so the 0349 re-generalize collapses a spuriously-poly caller to its true mono scheme. It MUST run pre-drain because 0349 + `register_test_fn_mono_roots` consume its output. |
| 2 | `finalize.rs:1168` | `MultiSig` | **post-`finalize_multi_sig_variant_types`** (Phase-A concrete promotion) | D3 (§11.8.3): a multi-sig CLAUSE body's inner poly hop (`(idpoly n)` in `build`) is invisible pre-settlement — the clause is a `$Var` template until Phase A promotes it concrete. `Defn::body()` panics on a multi-sig defn, so window 1's `SingleSig` family structurally cannot reach these bodies. |
| 3 | `finalize.rs:1191` | `SingleSig` (RE-harvest) | **post-drain + post-Phase-A** (same window as #2) | MC-X4/X4b (§3.1): a single-sig body consuming a MULTI-SIG fn's bare return (`(mycount (build 3))`) had that arg type as a residual `Var` at window 1 — a multi-sig return settles only in the drain + Phase A. Re-running the `SingleSig` harvest lets `resolve_expr_types` re-derive the consumer's arg concrete and mint the instance. |

Windows 2 and 3 share ONE post-settlement window (the §11.8.3 "one parameterized
`pass4_monomorphise` at two settlement points" precedent, extended to the
single-sig consumer face); only window 1 is pre-settlement, and it is the fast
common path whose *misses* are exactly the set window 3 re-covers.

**Idempotence obligations (the contract — currently only code comments; scribed here).**
The multi-window shape is sound iff re-running a harvest over an already-harvested
defn set re-derives byte-identical instances. Four obligations, each with its
as-built mechanism:

1. **`got_slot` preservation.** A re-minted instance MUST reuse the existing GOT
   slot, never allocate a second. Mechanism: `register_mono_entry` preserves the
   entry's `got_slot` on re-registration (`mono_collect.rs:1186` comment). A
   regression here is a double-slot for one callable — a Principle-20/24 keyed
   identity break.
2. **Monotone-subst arg stability.** Window 3's `resolve_expr_types` re-derives
   each consumer's arg type through `state.subst`, which only ever grows toward
   ground between windows (a settled var never un-settles — the monotone-soundness
   spine, `ownership-inference.md` §2.1, applied to the type substitution). So an
   arg concrete at window 1 stays that exact concrete at window 3; a residual `Var`
   at window 1 becomes concrete (never a *different* concrete). The concreteness
   gate therefore re-admits the SAME concrete args — the P26 acid test ("recording
   the same datum later yields the same value") holds by the subst's monotonicity.
3. **Per-invocation `seen`.** Each `pass4_monomorphise` call owns a FRESH
   `seen: HashMap<String, JitSymbol>` (`mono_collect.rs:70`) — dedup is
   WITHIN an invocation, not across. This is what makes windows 1 and 3 both
   safe to scan the SAME `single_sig_defns` (obligation 1 handles the cross-window
   re-mint), and it is the source of the cost note below.
4. **Pending-isolation.** A mono-recheck body's own overloaded-base dispatch
   deferrals are settled in place by `recheck_body_for_mono`'s `mem::take` of the
   outer `pending_overload_resolutions` (§11.8.3 R1/R2), so a harvest at window 2
   or 3 cannot orphan or double-drain the outer pendings — the top-level drain
   (window boundary) sees an unperturbed pending list.

**Cost note (obligation 3's price).** Because `seen` is per-invocation, window 3
re-runs every mono-recheck window 1 already performed for the single-sig family
— **the single-sig mono-recheck work is done twice** for any defn whose instances
were already minted at window 1 (the re-mint is a no-op on the symbol table by
obligation 1, but the body re-check + `from_expr` view rebuild are repeated). For
the common program (few multi-sig-return consumers) this is a small constant over
an already-walked form; it is not perf-sensitive today. It IS the concrete cost a
single-settlement convergence would recover.

**The NOTED S115 convergence option (NOT committed).** A single post-settlement
harvest per family — drop window 1, run each of `SingleSig`/`MultiSig` ONCE at the
post-drain/post-Phase-A window — would halve the single-sig mono-recheck work
(obligation-3 cost) and collapse three windows to two (one per family, at one
settlement point). It is **not free**: window 1 feeds the FIXME-0349
`regeneralize_defn_schemes` chain and (transitively) `register_test_fn_mono_roots`,
whose ordering is load-bearing (a blanket third re-generalize would overwrite a
mono-root's minted concrete scheme — the `finalize.rs:1073` hazard). Converging
requires re-deriving that ordering so the 0349 collapse still sees window-1's
result-var pinning at a post-settlement single harvest — a real design task, not a
mechanical de-dup. Recorded as an S115 candidate seeded by this section; the
scribed three-window shape is the operative contract until then.

**Standing rule — a FOURTH window forces the /arch class ruling.** Three
settlement-harvest windows is the escalation threshold (the recurring-class rule:
3rd instance across the arc ⇒ `/arch` assessment — the P24/P26 authoring
precedent). The three windows are each justified by a distinct settlement point
(pre-drain common path; post-Phase-A multi-sig bodies; post-settlement single-sig
consumers). **A FOURTH `pass4_monomorphise` invocation — a fourth "harvest at a
new settlement point" — is NOT to be added ad-hoc; it is the trigger for an
`/arch` class ruling** on whether the "harvest at N settlement points" pattern
should converge to a single settlement-driven mechanism (the noted S115 option
promoted). File `target: /arch` rather than adding the invocation. This is the
harvest-window analogue of the P26 "record from settled state" boundary: the
windows are a finite, enumerated set, and growing the set is an architectural
event, not an implementation convenience.

#### 11.8.11 The 0719 wrapper-indirection consume-at-distance — window-3 re-derivation, not a fourth window (S115)

**Status:** DESIGN (S115 Phase 3, `/design`(typecheck)). Realizes the §5.1.2
EQUIVALENCE-TWIN bar for the `carrier-loss` consume-at-distance variant
(`tests/mc_x4_consume_at_distance_0719.rs`; FIXME 0719, retargeted `/testing`,
deletes in the pin commit). Extends the window-3 SingleSig re-harvest
(§11.8.10 window 3, `finalize.rs:1191`), NOT a fourth window (§11.8.10 standing
rule).

**The reduced axis (from the test's complete reduction).** Neither the seed
(`[0]` ≡ `[]`), the stdlib verbs, nor an ADT wrapper is load-bearing — every
single/double-axis synthetic is GREEN (born-green controls 1–3). The SOLE
discriminator is the **wrapper indirection**: a multi-sig `peers` whose bare
`(Vec a)` return is consumed inside a WRAPPER single-sig defn
(`(defn run-elim [idx] (vec-len (peers idx)))`), whose result then flows through
that wrapper's monomorphisation into a separately-monomorphised poly consumer
(`vec-len`). Called directly in `main` — `(vec-len (peers 3))` — the SAME
multi-sig `peers` is GREEN (window 3 already covers the top-level SingleSig
consumer of a multi-sig return, §11.8.10 window-3 row). The failing shape is
exactly the exemplar's `peers`/`eliminate-from-peers` axis: `peers` consumed
inside a wrapper, never at a concrete site. Today the wrapper case leaks
`ambiguous type … monomorphised in \`user/peers$Var$Int\`` — the element `Var`
reaches codegen. The two-function twin
(`(defn peers [idx] (peers-helper idx []))`) compiles and returns 3, so by the
§5.1.2 acid test the multi-sig RED is a `wrong-reject`, not a genuine ambiguity.

**The seam and the gap.** Window 3 re-derives a SingleSig consumer's arg concrete
via `resolve_expr_types` over `state.subst` post-drain/post-Phase-A — the window at
which the multi-sig `peers`' element back-flow (§11.3.1: the 1-arg clause's `[]`
seed unifies with the 2-arg clause's `vec-push acc idx` element = `Int`) has
settled. For the DIRECT `(vec-len (peers 3))` the consumer arg is a top-level
expression whose return var is in `state.subst` and re-derives concrete. For the
WRAPPER case, `(peers idx)` sits inside `run-elim`'s body, and `idx` is
`run-elim`'s BOUND PARAMETER — the "free-var-through-bound-parameter distance"
axis (s114 §11 item 5 / §12): the element `Var` of `peers`' return is a free var
that flows through the wrapper's parameter to the downstream `vec-len`. The mono
instance of `peers` minted from within `run-elim`'s harvested body derives its
type args from the call site's fresh instantiation of `peers`' scheme; if
`run-elim`'s body harvest does not re-run `resolve_expr_types` at the SETTLED
window (so the fresh element var re-unifies against `peers`' back-flow-pinned
concrete return), the instance mints as `peers$Var$Int` — the element `Var`
un-settled, reaching codegen.

**The fix — derive the wrapper-indirected instance from SETTLED state (P26).**
The consumer-harvest keying for the wrapper case must re-derive the inner
`(peers idx)` instance's element type at the **post-drain/post-Phase-A settlement
window** (window 3), where `peers`' element back-flow is pinned — never from
`run-elim`'s pre-settlement view. This is the §11.3.2 B1 precedent
(*"the self-call `SigDispatch` MUST be derived post-drain"* — a carrier derived
from settled state, never a provisional record patched later) and the §11.8.9
single-sourcing discipline, generalized one indirection level: window 3's
`resolve_expr_types` re-derivation must reach INTO a single-sig wrapper defn body
whose monomorphisation consumes a multi-sig return through a bound parameter, so
the inner multi-sig instance re-mints against the settled element concrete. The
monotone-subst stability obligation (§11.8.10 obligation 2) makes this safe: the
element var only moves toward ground between window 1 and window 3 (a residual
`Var` at window 1 becomes `Int`, never a different concrete), so the re-derivation
re-admits the SAME concrete instance the twin infers.

**Placement discipline — NOT a fourth window.** The fix EXTENDS the existing
window-3 SingleSig re-harvest's reach (the wrapper defn is a SingleSig consumer
whose body harbours the distance-consumed multi-sig call), it does not add a new
`pass4_monomorphise` invocation. If `/dev` finds window 3 STRUCTURALLY cannot
reach the wrapper-inner `peers` element from settled state — e.g. the wrapper's
mono-view subst is isolated from `peers`' cluster settlement and a genuinely-new
settlement point is required — that is the §11.8.10 standing-rule trigger: STOP
and file `target: /arch` for the harvest-window class ruling rather than adding a
fourth window. The expectation recorded here is that the reach is a re-derivation
extension within window 3 (the same `resolve_expr_types`-over-settled-subst
mechanism window 3 already runs), not a new window.

**Acceptance (§5.1.2 EQUIVALENCE-TWIN bar — binding).** The X4b "monomorphise OR
reject cleanly" bar is too weak (it lets a §5.1.2 wrong-reject read green). The bar
is: `multi_sig_return_through_wrapper_indirection_infers` AND its twin
`two_function_equivalent_through_wrapper_indirection_green` BOTH compile AND agree
on output (exit 3 = `(vec-len [3 2 1])`), `--run` + `--link`. Must-hold GREEN: the
four born-green controls (param-distance recursive-consumer × {seed [], seed [0]},
untyped-ADT-field distance, cross-module untyped-field distance) — the fix must not
regress them. **Unit tier (`/dev`, METHOD §2.2):** at the window-3 re-derivation
seam, the wrapper-indirected multi-sig instance re-mints with the element concrete
(not `$Var`) from settled subst; a pre-settlement mint would disagree. **Exemplar
rider on flip:** `/port`'s `make-grid`/`peers` collapse trigger re-words per s114
§12 item 5 (owner `/port`, next touch).

### 11.7 Cross-references

- `spec/05-definitions.md` §5.1.2 (settled back-flow) + §5.1.1 (dispatch coherence)
  + §5.13.1 (two-pass) + §3.3 (annotations descriptive).
- `design/arch/fixmes/0642-…` — leg (a) + the superseded-repro unwind list.
- `crates/cranelisp-typecheck/src/program/{finalize,register,body,support}.rs` — the
  scan-collapse (finalize), the drain/mangle ordering (register), the per-clause
  `Constrained` determination (body), the `mangle_type` determinism (support).
- `crates/cranelisp-types/src/module.rs:2292–2334` — `OverloadVariant` /
  `ConstrainedFn` (rustdoc update, /arch).
