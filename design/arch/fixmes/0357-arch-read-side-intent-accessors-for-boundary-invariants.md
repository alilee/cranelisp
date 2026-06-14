---
number: 0357
target: /arch
filed_by: /sprint
filed_at: 2026-06-14
sprint_filed: 82
refers_to: crates/cranelisp-types/src/module.rs (ModuleEntry, DefBuilder, callable_got_slot/mark_constrained_template), design/arch/principles/ (candidate new Principle), design/arch/bounded-contexts.md §7, design/arch/fixmes/0356-arch-moduleentry-callability-structural-not-accessor.md, design/arch/CLAUDE.md §"String Newtypes"
status: open
---

# Model cross-field invariants by representation (sum types), accessors only as fallback — the "180 locations" root

## Issue (user observation, S82 close)

Multiple S82 fixes were constrained or inflated by an "update ~180 locations" propagation
cost (the `0354`/`0356` callability invariant; echoed by the S69 "fuse the parallel vecs"
lesson and Decision 35's flat `got_slot`). The user asked: *do we use helpers/constructors
to manage that propagation?*

Grounded finding (workspace grep): **construction is encapsulated; reads are not.**
- **Construction** goes through `DefBuilder` (`ModuleEntry::def(scheme, kind).got_slot(n).build()`)
  — defaults centralized, so adding a *field* is cheap (e.g. S82's `TypeExpr::Bounds`
  cascaded lightly).
- **Reads** are ~**514 `ModuleEntry::Def` sites** + **435 `got_slot` mentions**,
  overwhelmingly raw pattern-matches (`Def { got_slot: Some(slot), .. }`) and raw field
  reads (`entry.got_slot.unwrap()`) against `pub` fields. **No read chokepoint.**

Consequence — the propagation cost is asymmetric: **adding a field is cheap; changing a
cross-field invariant is the 180-site problem**, because each raw reader independently
encodes how the fields combine. `0354` was exactly this: "constrained template ⟹ no
callable slot" spanned two `pub` fields and ~180 raw readers each had to be trusted to
respect it; one (`resolve_got_target`) didn't → SIGSEGV.

## Proposed resolution (representation-first — user-directed, S82 close)

The fundamental fix for a cross-field invariant is **representation: make the illegal
state unconstructable**, not enforce it by read-discipline. Candidate new Principle:

> **Model a cross-field invariant as a sum type whose variants are exactly the legal
> states.** When two+ fields are *correlated* (one constrains the other), collapse them
> into one `enum` with one variant per legal state, each carrying exactly the data valid
> in that state; construct the right variant **once, at the point the state is known**
> ("parse, don't validate"). The illegal combination then has no representation, and every
> reader matches exhaustively (compiler-enforced) — no accessor, no convention.
>
> Discriminator (keeps it from becoming "enum everything"): **correlated fields with few
> legal states → sum type; genuinely independent fields → leave flat** (collapsing
> independents is wrong and combinatorial). The cross-field-invariant test is "is there a
> field combination that is constructable but meaningless?" — if yes, it's a sum type.
>
> **Intent-accessor + sole-writer (the `0356` shape) is the explicit FALLBACK**, used only
> where the sum-type collapse is genuinely blocked (e.g. a hard timing/sequencing
> constraint, or a churn cost that must be staged) — and when used, it is a bridge to the
> representation form, not the destination.

Worked example (the `0354`/`0356` case) — `got_slot` is a field on `ModuleEntry::Def`
parallel to `kind: DefKind`, where `DefKind::UserFn{ constrained_fn }` lives. Three
concrete representations for `/arch` to weigh (user-surfaced, S82 close):

- **Option A (preferred) — move `got_slot` INTO `DefKind`.** Slot lives on the *callable*
  kind variants; non-callable kinds (`ConstrainedTemplate`, `Macro`) have no slot field.
  ```rust
  enum DefKind {
      UserFn { got_slot: GotSlot },        ConstrainedTemplate { constraints },
      Primitive { got_slot: GotSlot },     Constructor { got_slot: GotSlot },
      Macro { … }, …
  }
  ```
  Co-locates the slot with its determinant (callability is a kind property; `constrained_fn`
  already lives in `DefKind`). `Def`'s shared payload (`scheme`/`ast`/`code`/`callees`)
  untouched. Cost: `got_slot` repeats across callable kinds (honest duplication); **amends
  Decision 0035** (flat-field SSOT).
- **Option B — split `Def` into more `ModuleEntry` variants** (`CallableDef{got_slot,…}` vs
  `TemplateDef{constraints,…}`). Outermost match distinguishes callability. Cost: heavier —
  grows the already-large outer enum + forces duplicating/factoring `Def`'s shared fields
  for a one-field problem.
- **Option C — sibling `Callability` enum on `Def`** (`enum Callability{ Direct{got_slot},
  Template{constraints} }`). A's slot extracted into a nested enum rather than inlined into
  `DefKind`; viable but reads less directly than A (two kind-ish discriminators).

`/sprint` read: **A is cleanest** (least disturbance; collapses the invariant where both
fields already belong). The genuine work A forces is the Decision-0035 amendment + the
timing wall (defer Pass-1 slot allocation past Pass-2 constraint detection, or a `Pending`
kind names the interstage) — exactly the "pay it properly" cost.

**The timing wall is the crux (and a feature):** `got_slot` is allocated Pass 1, before
constrained-ness is known Pass 2 — so the current code constructs entries *in an
indeterminate state* (the latent root). A sum type forces resolving WHEN the state is
known: defer slot allocation past detection, or add an explicit `Pending` variant for the
interstage. "Parse, don't validate" pushes the determination to the boundary.

Scope of work: (1) decide the Principle (representation-first; accessor-fallback) + its
boundary; (2) inventory cross-field invariants in `cranelisp-types` boundary types (start
`ModuleEntry`/`SymbolTable` — look for constructable-but-meaningless field combinations);
(3) collapse each into its sum type, resolving its timing wall; cascade readers to
exhaustive matches. Sequence the `ModuleEntry`/`got_slot` collapse **with `0356`/`0355`**
(same surface) to avoid double-churn. Amends Decision 0035 (flat `got_slot` field) — record
the amendment, don't reverse silently.

## Operational implication / Context

Forward-looking architectural improvement, not an S82 blocker (the S82 SSOT accessors hold
the line). It is the *root* under the recurring "180 locations" friction — addressing it
reduces fix effort + recurrence risk for every future cross-field invariant change. Bundle
the `ModuleEntry` slice with `0356` (callability structural) + `0355` (cross-module mono);
treat the Principle decision as the gating first step.
