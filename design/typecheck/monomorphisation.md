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
- **NOT a multi-clause inference change.** The fix does **not** attempt to make the
  unannotated cross-variant self-call *infer* (that would require propagating the
  first variant's call-shape into the second variant's param types — a real inference
  extension, out of scope and arguably undesirable: the spec's favour-annotation
  posture means a public-entry/private-accumulator split *should* annotate). The fix
  makes the *currently-ambiguous* program **fail cleanly** instead of panicking — it
  converts a robustness defect into a correct, located type error. The combined
  multi-sig + tail-recursive idiom compiles once the user annotates (the primer's
  separated forms, 0432 §"Operational implication").
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
