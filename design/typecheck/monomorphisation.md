# Monomorphisation from roots — design intent (Tier 2 + ambiguity check)

Owner: `/design` (typecheck triad). Subordinate to `design/typecheck/typecheck.md` §9.3.
Companion: `design/typecheck/traits.md` §7 (the as-built batch pipeline this doc
*completes*, not replaces). Sprint 84 Cluster A.

Contract this designs against:

- `design/arch/bounded-contexts.md` §2 (typecheck monomorphisation-from-roots note)
  + §3 invariant 9 (backend RC soundness).
- `design/arch/fixmes/0374-typecheck-tier2-full-monomorphisation-from-roots.md`
  (Tier-2 — the primary deliverable here).
- `design/arch/fixmes/0373-…` part (ii) (the unconstrained-var ambiguity rule —
  a /spec *rule* realised by a /typecheck *check*, designed in §3 below).
- `sprints/SPRINT.md` §"Architecture review (Phase 2)" point 1 — Cluster A
  coherence ruling (binding): **Tier-2 EXTENDS the existing per-`(Def, type-args)`
  enumeration; a second monomorphisation entry point is rejected** (Principle 7,
  single source of truth).

This doc pins the *design intent* for the systematic completion. It names the
exact functions to extend, the worklist/fixpoint shape, the dedup discipline, the
firing point of the ambiguity check, and the unit-test seams. It authors no code
(Phase 3 = design).

---

## 1. The invariant Tier 2 must make total

> **No `Type::Var` reaches the codegen boundary under any reachable
> instantiation.** Every reachable fn instance has fully concrete parameter AND
> result types.

This is the prerequisite for `/backend`'s 0375 (turning `HeapCategory::classify`'s
`Type::Var` arm into an assert and retiring the unsound `<1024` RC guard). While a
`Type::Var` can flow to codegen, `classify(Type::Var) -> Mixed` emits a guarded
RC-inc whose `<1024` immediate-vs-pointer heuristic mis-reads a negative / large
`Int` as a heap pointer → use-after-free (BC §3 invariant 9; the 0373 root cause).

The detector for the invariant already exists: `Type::contains_var()`
(`crates/cranelisp-types/src/types.rs:55`), today a `debug_assert!` tripwire
before codegen. Tier 2 + the ambiguity check (§3) are what make that assertion
*unconditionally satisfiable* — they turn a debug-only tripwire into a structural
guarantee (Principle 18, enforce invariants structurally). The typecheck-side
ambiguity error and the backend-side assert (0375) are complementary halves of one
invariant: together they make a residual `Type::Var` at codegen structurally
impossible.

---

## 2. Tier 2 — systematic full monomorphisation from roots

### 2.1 What landed (Tier 1 + 1.5) and where it stops

S83 (`5634dd3`, `9e57330`) delivered the **polymorphic-result-hop** subset. The
enumeration spine is already in place and is what Tier 2 extends — NOT forks:

| Element | Location | Role |
|---|---|---|
| `pass4_monomorphise` | `program.rs:2300` | per-form entry; runs inside `finalize_check_result_inner` (`program.rs:1438`) |
| `collect_constrained_calls_excluding_self` | `program.rs:2593` | collector — local trait-constrained callees |
| `collect_imported_constrained_calls` | `program.rs:2454` | collector — cross-module constrained / pure-parametric callees (0355) |
| `collect_local_parametric_calls` | `program.rs:2491` | collector — local pure-parametric callees, **gated to bare-`Var` result** (Tier 1) |
| `monomorphise_call` | `traits.rs:1271` | core — instantiate `(Def, arg-types)`, verify constraints, re-check body, register mono entry |
| `recheck_body_for_mono` | `traits.rs:1602` | re-check the body at concrete param/ret types in the callee's home scope |
| `monomorphise_inner_parametric_hops` | `traits.rs:1731` | **recursive** — monomorphise inner hops a just-rechecked body reached (Tier 1 multi-hop / Tier 1.5 cross-module) |
| `register_mono_entry` | `traits.rs:1458` | register the mono `Def` + GOT slot; **dedup by preserving an existing entry's slot** |
| `entry_is_monomorphisable_polymorphic` | `program.rs:2540` | gate — a `UserFn` that is constrained OR pure-parametric-with-`ast` |

**The coverage gap is in the COLLECTORS, not the core.** `monomorphise_call` +
`monomorphise_inner_parametric_hops` already (a) instantiate at concrete
arg-types, (b) re-check the body in the right scope, (c) register the mono entry
with a GOT slot, and (d) recurse into deeper hops. What Tier 1/1.5 narrows is
*which call sites get collected as roots of that recursion*. The narrowing gates,
each a current subset-coverage gap:

1. **`collect_local_parametric_calls`'s bare-`Var`-result gate**
   (`program.rs:2516`–`2520`). Collects ONLY when the call site's result type
   resolves to a bare unbound `Type::Var`. This was the precision instrument that
   fixed the result-hop SIGSEGV while preserving 0344 (the fold-accumulator
   over-unification). **Gap:** a local pure-parametric callee whose result is
   *concrete* but whose **parameter** instantiation still leaves a `Type::Var`
   somewhere reachable (e.g. an identity-shaped hop applied at a still-generic
   argument that only a deeper caller pins) is not collected here.

2. **The `home != current_module` gate on `collect_imported_constrained_calls`**
   (`program.rs:2466`) and the symmetric `home == current_module` on
   `collect_local_parametric_calls` (`program.rs:2523`) partition cross-module vs
   local. That partition is correct; the gap is that **neither collector fires
   for a call whose callee is concrete-at-this-site but transitively reaches a
   polymorphic instance through an argument that is itself a polymorphic
   instance** — the transitive closure is only chased *inside* a mono recheck
   (`monomorphise_inner_parametric_hops`), never seeded from a top-level concrete
   call that is not itself a result-hop.

3. **Pattern / let / match-bound polymorphic instances.** The collectors walk
   `Apply`-of-bare-`Var` only (`collect_apply_var_calls`, `traits.rs:1888`). A
   polymorphic value reached through a `let` binding, a match-arm binding, or a
   higher-order argument position that is later applied is not an
   `Apply`-of-bare-`Var` at the binding site, so no instance is seeded there. Tier
   1's result-hop repro happened to surface as an `Apply`; the systematic case
   does not.

### 2.2 Tier-2 shape — a reachable-instance worklist seeded from roots

The design generalises the three collectors + the inner-hop recursion into a
**single worklist-driven fixpoint over reachable `(Def, concrete-type-args)`
instances**, keeping the existing core (`monomorphise_call` and friends)
unchanged. The shape:

```
roots        := the concrete instantiations demanded directly by the
                top-level forms of THIS cluster (the program roots reachable
                from this check_forms call)
worklist     := roots
done         := ∅                         // dedup set, keyed below
while worklist non-empty:
    inst = (Def, concrete-type-args) = worklist.pop()
    if key(inst) ∈ done: continue
    done.insert(key(inst))
    mono = monomorphise_call(Def, concrete-type-args)   // existing core
    // discover successors: every Apply / let-bound / match-bound polymorphic
    // instance reachable in mono's RE-CHECKED body, now at concrete types
    for succ in reachable_polymorphic_instances(mono.body, mono_expr_types):
        if succ has any residual Type::Var after applying the instantiation:
            // not pinnable from this instantiation — defer; a deeper root
            // or a sibling instantiation may pin it. If NO reachable
            // instantiation ever pins it, §3's ambiguity check has already
            // rejected the owning top-level form.
            continue
        worklist.push(succ)
```

This is **exactly the existing recursion made breadth-first and total**.
`monomorphise_inner_parametric_hops` is the as-built *depth-first, hop-restricted*
version of the `for succ in …` loop; Tier 2 widens its successor-discovery from
"result-hop `Apply`s" to "every reachable polymorphic instance" and lifts the
recursion out of per-call depth-first into the cluster-level worklist so dedup is
global.

### 2.3 The root set — what seeds the enumeration

The roots are the concrete instantiations the cluster's **own top-level forms**
demand. Concretely, after Pass 2 body-check + the first `regeneralize_defn_schemes`
(`program.rs:1349`), for each top-level form in `working_program`:

- A non-generic top-level defn (its finalised scheme has empty `type_vars`) is a
  root at its single concrete instantiation. Its body's `Apply`/binding sites are
  the first successors.
- A top-level expression (the synthetic `__expr` defn) is a root at its concrete
  type.
- A generic top-level defn (non-empty `type_vars`) is **NOT a root on its own** —
  it is only ever specialised through a concrete call site. If nothing in the
  reachable graph instantiates it concretely, it is dead for codegen and emits no
  instance (the generic template is never compiled; this is the rank-1 HM
  property the 0373 investigation ratified — see `traits.md §7` Invariants).

This matches the existing pass4 seeding (it scans every defn body in `defns` for
call sites) — Tier 2 reframes "scan defn bodies for constrained/parametric call
sites" as "seed the worklist from the concrete top-level instantiations and chase
their reachable successors." The root set is **the same forms pass4 already
iterates**; the change is that successor discovery becomes total and global-dedup.

### 2.4 Dedup of identical instances

Key each instance by `(FQSymbol of the Def, canonical concrete-type-args)`. The
canonical form is the existing mangled name `build_mangled_name(fn_name,
param_types)` (`traits.rs:1905`) — `name$Type1+Type2` — which is already the dedup
key the `seen: HashMap<String, JitSymbol>` map uses in pass4 (`program.rs:2396`)
and which `register_mono_entry` already preserves-slot-on-collision. **Tier 2
promotes this from a per-pass4-call `seen` map to a cluster-level `done` set so a
diamond of hops converging on one specialisation is created exactly once across
the whole worklist, not once per outer call site.** No new key scheme; the mangled
name IS the identity (it must be, because it is also the GOT-slot / JIT-symbol
identity the backend links against).

### 2.5 Staying inside the existing output shape — no new boundary item

Per the /arch Phase-2 ruling (point 1, CONFIRMED): Tier 2 produces **more
instances of the existing `MonoDefn`/`Defn` shape** through the existing
enumeration. Each worklist instance lands as an ordinary concrete `UserFn` `Def`
registered (with its own GOT slot) by `register_mono_entry`, exactly as the
result-hop subset does today. No new `cranelisp-types` DTO, no boundary-signature
change, no `interfaces.md` / BC shape change. `MonoDefn` is already a
`cranelisp-types` public item (`lib.rs:223`); the coverage of the enumeration
grows, its output type does not.

> **If the implementation discovers it CANNOT stay inside this shape** — e.g. the
> worklist needs a successor-discovery datum that does not fit on `Defn`/the
> re-checked AST and must cross the crate boundary — that is a FIXME
> `target: /arch`, NOT a silent boundary change (per the task constraint and
> Principle 7). The design's expectation, grounded in the structural argument
> above, is that it does NOT: successor discovery reads the re-checked body's
> `mono_expr_types` (already in hand inside `monomorphise_call`) and produces more
> of the same `Def` instances.

### 2.6 Exact functions to extend

| Function | Tier-2 change |
|---|---|
| `pass4_monomorphise` (`program.rs:2300`) | Becomes the worklist driver: seed roots from the cluster's top-level concrete instantiations; drive the fixpoint; hold the cluster-level `done` dedup set. The three `collect_*` calls fold into root-seeding + successor-discovery. |
| `collect_local_parametric_calls` (`program.rs:2491`) | Drop the bare-`Var`-result gate as the *sole* trigger; generalise to "any reachable polymorphic instance at a concrete instantiation." The 0344-preservation that the gate bought is re-secured by §2.2's residual-`Var` defer (a successor with a residual `Type::Var` is not enqueued; it is only an instance once concrete) + the existing subst-isolation in `monomorphise_inner_parametric_hops` (`traits.rs:1806`, `saved_subst`). **This is the highest-risk edit** — see §4. |
| `monomorphise_inner_parametric_hops` (`traits.rs:1731`) | Successor-discovery generalises from "`Apply`-of-bare-`Var` result-hops" to "every reachable polymorphic instance" (incl. let-bound / match-bound / higher-order-applied), via a widened `collect_apply_var_calls` (or a sibling walker covering binding positions). Its recursion either remains (depth-first within a recheck) and feeds the cluster worklist, or is subsumed by the worklist — an implementation choice for /dev, bounded by "one enumeration spine." |
| `collect_apply_var_calls` (`traits.rs:1888`) | Extend to discover polymorphic instances at non-`Apply` positions (let/match bindings that are later applied). |
| `entry_is_monomorphisable_polymorphic` (`program.rs:2540`) | Unchanged in shape; it is the per-instance "is this a thing to specialise" gate and already accepts both constrained and pure-parametric `UserFn`s. |

**No second entry point is introduced.** Everything threads through
`pass4_monomorphise` → `monomorphise_call`. This is the Principle-7 constraint the
/arch review made binding.

---

## 3. The unconstrained-var ambiguity check (0373 part ii)

### 3.1 Rule

A top-level form whose finalised type, after inference + generalisation, still
contains a `Type::Var` that **no reachable instantiation pins** is a **type
error** (ambiguous; no Haskell-style defaulting). This is the /spec rule (0373 ii)
realised as a /typecheck check. It is what makes the §1 invariant *total by
construction*: a residual `Type::Var` at a top-level root is rejected here, before
any instance is enumerated, so the worklist never tries to compile an
unpinnable instance.

> **Generic-defn nuance.** A *generic* top-level defn legitimately has
> `Type::Var`s in its finalised scheme (`type_vars` non-empty) — that is the whole
> point of a polymorphic definition, and it is NOT compiled on its own (§2.3). The
> ambiguity check must therefore fire on a var that is **free at the root and not
> a generaliseable scheme variable** — i.e. a var that survives generalisation
> *unquantified* because it is neither bound by a use-site instantiation nor
> closed over by the scheme. The canonical shape: a top-level expression (or a
> non-generic defn) whose result type the inference left as an un-generalisable,
> un-pinnable `Type::Var` (classic example: an empty-collection literal at the top
> level with no annotation and no use that pins the element type). A var that
> IS quantified into the scheme is fine — it becomes concrete at each use site or,
> if it has no use site, the defn is dead and never compiled.

### 3.2 Where it fires

**At the post-inference generalisation/finalisation boundary of each top-level
form, BEFORE `pass4_monomorphise` runs.** Concretely, inside
`finalize_check_result_inner` (`program.rs:1340`), after the first
`regeneralize_defn_schemes` (`program.rs:1349`) — which is exactly the point each
defn's scheme is finalised through the global substitution — and **before** the
Pass-4 call at `program.rs:1438`. Ordering rationale:

- Generalisation must have run so the check can distinguish a quantified scheme
  variable (fine) from an un-generalisable free root var (ambiguous).
- It must run before Pass 4 so an ambiguous form is rejected rather than seeding an
  unpinnable worklist instance — the worklist's §2.2 "defer a residual-`Var`
  successor" relies on the *roots* already being pin-guaranteed; this check is what
  guarantees it.

The check is a small pass: for each finalised top-level form, take its finalised
type, apply the final substitution, and for each `Type::Var` it
`contains_var()`-detects, ask "is this var quantified into the form's scheme?" If a
detected var is free-at-root and not quantified, raise the error.

### 3.3 Error variant + diagnostic wording

**Current error model (as-built):** typecheck returns
`cranelisp_types::CranelispError`, not a crate-internal `CheckError`. The
`CheckError` migration (FIXME 0098 Phase 3) has **not** landed — the crate has no
`CheckError` enum yet (master doc §2.1 drift register). So the design lands in two
layers, both typecheck-internal:

- **Today (this sprint):** raise `CranelispError::TypeError { message, location }`
  — the existing variant typecheck already constructs (`program.rs:2032`,
  `:2041`, etc.). No new `cranelisp-types` item; `TypeError` already exists, so
  **no `cranelisp-types` baseline move** and no cross-crate surface change (this
  matches the /arch Phase-2 point-4 assessment: the ambiguity enforcement adds at
  most a typecheck-internal error case, not a boundary DTO).
- **After FIXME 0098 Phase 3:** the dedicated variant is **`CheckError::AmbiguousType`**
  — a `cranelisp-typecheck`-internal enum variant, NOT surfaced cross-crate (the
  `CheckError` enum is crate-internal per 0098; it projects to the boundary only
  through the existing `From`/display machinery). The migration carries this
  variant alongside the others (`TypeError`, `Gap`, …); it forces no `cranelisp-types`
  edit because `CheckError` lives in `cranelisp-typecheck` post-0098.

**Confirmation the variant stays typecheck-internal:** in both layers the error is
constructed inside typecheck and crosses the boundary only as the already-existing
`CranelispError`/`CheckError` surface. No NEW cross-crate item is required. If a
future need surfaces the ambiguity case as a *distinct* boundary variant (e.g. the
REPL formatter wants to special-case it), that is the two-update baseline
discipline + a FIXME `target: /arch` — flagged here, not assumed.

**Diagnostic wording** (the design pins the message; /dev lands it):

```
ambiguous type: this expression's type contains an unconstrained type variable
that no use pins to a concrete type; add a type annotation to disambiguate
```

For a named top-level defn, prefer the located form (the `ErrorLocation.fq` is
determinable per master doc §8.1 producer policy):

```
ambiguous type for `<name>`: an unconstrained type variable remains after
inference (no use pins it); add a type annotation
```

`ErrorLocation`: populate `span` from the offending form, `fq` when the form is a
named defn (links to per-defn source for rich display), per master doc §8.1.

---

## 4. Risk

| Risk | Bound |
|---|---|
| **Enumeration non-termination on recursive instantiation.** A polymorphic-recursive call (a defn that calls itself at a *larger* type) could enqueue an unbounded family of distinct instances. | **Bounded by monomorphic-recursion enforcement.** Cranelisp is rank-1 HM with **monomorphic recursion enforced** (0373 part i; `program.rs` recursion check). A recursive self-call is at the defn's *own* generic vars, not a growing type — `collect_local_parametric_calls` / `collect_apply_var_calls` already skip a call from a fn to ITSELF (`self_name` guard, `program.rs:2501`, `traits.rs:1895`). So the set of distinct `(Def, concrete-type-args)` instances reachable from a finite root set is finite, and the `done` dedup set (§2.4) makes the worklist strictly decreasing. The fixpoint terminates. **This is the load-bearing soundness argument for termination** and must be stated in the as-built `traits.md §7` Invariants when the code lands. |
| **0344 / 0349 regression** (re-collapsing a deliberately-kept polymorphic scheme via mono recheck leaking into the parent subst). | The bare-`Var`-result gate that Tier 1 used to avoid this is *replaced*, not removed: §2.2's residual-`Var` defer (don't enqueue an instance that still has a `Type::Var`) + the existing `saved_subst` isolation around the inner recursion (`traits.rs:1806`) together preserve the property the gate bought. **The 0344 / 0349 unit tests are the regression guard** and must stay green through the Tier-2 widening — name them explicitly in the /dev change-set. |
| **Successor over-collection** (enqueueing instances that are never actually codegen-reachable, bloating compile output). | Acceptable for correctness (extra concrete instances are sound, just unused); dead-instance pruning is a *later* perf concern, rejected as premature per Principle 6. The dedup set bounds duplication; reachability from real roots bounds the family. |
| **Cluster-vs-REPL root set.** A REPL eval's roots are the single just-entered form plus the additive cluster; a `--run`/`--link` cluster's roots are all top-level forms. | The root set is "the top-level forms of THIS `check_forms` call" (§2.3) — uniform across modes because `pass4_monomorphise` already runs per-cluster in `finalize_check_result_inner`. No mode-specific seeding. |

---

## 5. Unit-test seams (Phase-5 authoring by /qa + /dev)

Per the per-fix discipline (`memory/feedback_unit_test_per_fix.md`), the design
names the typecheck-seam unit tests; /qa + /dev author them in Phase 5. Both seams
are narrow, deterministic, in-crate (`TestFixture`, `checker/test_support.rs`), no
codegen.

**(a) A previously-residual-`Var` instance is now monomorphised concrete.**
Seam: after `check_via_forms` over a cluster containing a polymorphic hop reached
at a concrete type *beyond* the Tier-1 result-hop subset (e.g. a let-bound or
parameter-position polymorphic instance, or a concrete-result hop whose parameter
instantiation Tier 1 left un-monomorphised), assert that the symbol table now
carries the mangled mono `Def` (`name$Concrete`) AND that its stored scheme /
annotated body contains **no `Type::Var`** (`!instance_type.contains_var()`). This
pins the §1 invariant at the typecheck seam — the exact property 0375's codegen
assert will later rely on. Name candidate:
`monomorphisation::tests::tier2_param_position_hop_monomorphises_concrete`.

**(b) The ambiguity error fires on a genuinely-unconstrained top-level var.**
Seam: `check_via_forms` over a top-level form whose finalised type leaves an
un-generalisable free `Type::Var` (e.g. an unannotated empty-collection literal at
the top level with no pinning use), asserting the result is
`Err(CranelispError::TypeError { message, .. })` whose message matches the §3.3
wording (and, post-0098, `Err(CheckError::AmbiguousType { .. })`). **Plus a
NEGATIVE companion:** a *generic* top-level defn (legitimately `type_vars`
non-empty, e.g. `(defn id [x] x)`) MUST NOT raise the ambiguity error — its scheme
vars are quantified, not free-at-root. This negative is the guard that the check
distinguishes "quantified scheme variable" (fine) from "un-generalisable free root
var" (ambiguous) — the §3.1 generic-defn nuance. Name candidates:
`monomorphisation::tests::unconstrained_toplevel_var_is_ambiguous` and
`monomorphisation::tests::generic_defn_is_not_ambiguous`.

The e2e tier (cross-mode SIGSEGV-class repros for Tier 2) is /qa's Wave-0
sprint-wide authoring per `sprints/SPRINT.md` §Waves — out of this doc's seam
scope, noted for coordination.

---

## 6. Cross-references

- `design/typecheck/typecheck.md` §9.3 — master-doc monomorphisation pointer (this
  doc is its Tier-2 + ambiguity elaboration).
- `design/typecheck/traits.md` §6–§7 — constrained polymorphism + the as-built
  batch pipeline this doc completes; the termination Invariant (§4) lands there
  when the code does.
- `design/arch/bounded-contexts.md` §2 + §3 invariant 9 — the architecture
  conclusion (records the direction in prose; needs no amendment this sprint per
  /arch Phase-2 point 1).
- `design/arch/fixmes/0374-…` (Tier 2), `0373-…` (rank-1 HM + ambiguity rule),
  `0375-…` (/backend codegen-side assert — the complement to §3).
- `crates/cranelisp-types/src/types.rs:55` — `Type::contains_var()`, the shared
  detector both halves of the invariant use.
- `crates/cranelisp-typecheck/src/{program,traits}.rs` — the enumeration spine
  (function map in §2.1).
