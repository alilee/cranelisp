---
number: 0377
target: /arch
filed_by: /design
filed_at: 2026-06-16
sprint_filed: 84
refers_to: crates/cranelisp-types/src/module.rs (UserFnState ~line 1710, ConstrainedFn ~line 1789, eligible-for-mono filter ~line 618-635), crates/cranelisp-backend/src/cache/mod.rs:154 (CACHE_SCHEMA_VERSION), design/typecheck/monomorphisation.md §2.3/§6, design/arch/fixmes/0374-*.md, design/arch/principles/20-model-invariants-by-representation.md, design/arch/bounded-contexts.md §7
status: open
---

# Add a slot-less `UserFnState::Polymorphic` variant for determined-but-non-concrete unconstrained generic defs

## Issue

The S84 Cluster-A re-shape (Principle 20 generalisation; BC §7; FIXME 0374) corrects
the GOT-slot-allocation gate from `constraints.is_empty()` to `is_concrete()`. With
the corrected gate, a **determined-but-non-concrete unconstrained generic def**
(`id : ∀a. a→a`, a HOF whose result is `(Box a)` — empty constraints, but a residual
`Type::Var`) must NOT be `UserFnState::Concrete { got_slot }` (the leak the re-shape
closes) and must NOT be `UserFnState::Constrained(_)` (it carries no trait
constraints). It needs a **third determined-and-slot-less state**.

`UserFnState` (`crates/cranelisp-types/src/module.rs:1710`) today has exactly three
arms — `NotDetermined` (Pass-1 interim), `Concrete { got_slot }`, `Constrained(Box<ConstrainedFn>)`
— none of which is the right home:

- **`NotDetermined`** means "Pass-2 has not run; callability not yet known." A generic
  def IS determined (Pass-2 ran; it is determined to be parametric). Reusing it
  conflates interim with determined — Principle 20 forbids overloading the interim arm
  for a settled state.
- **`Constrained(Box<ConstrainedFn>)`** carries a trait-bound body and means "vars
  pinned by trait dictionaries." A plain parametric def has no trait constraints;
  forcing it here collapses the *why*-distinction BC §7 + Principle 20 make explicit.

/design's design call (`design/typecheck/monomorphisation.md` §2.3): a **new slot-less
`UserFnState::Polymorphic` variant**, sibling to `Constrained`, differing only in *why*
the vars are unpinned (unpinned type vars vs trait dictionaries). The exact payload
shape + the cache consequence are `cranelisp-types`/`cranelisp-backend` boundary work
owned by /arch + /backend — /design names the need; /arch authors the variant.

## Proposed resolution

Land in `cranelisp-types` (additive — no `public-api.txt` removal):

1. **A new `UserFnState::Polymorphic` arm**, slot-less, carrying the minimum
   parametric body `traits.rs::monomorphise_call` needs to re-check the body at
   concrete types — the `DefnVariant` + `Scheme`, mirroring `ConstrainedFn` minus the
   trait-dictionary semantics. /arch decides whether to reuse a `ConstrainedFn`-shaped
   payload (`{ variant: DefnVariant, scheme: Scheme }`) or introduce a leaner
   parametric payload type; either is acceptable to /design provided it carries enough
   to monomorphise. `callable_got_slot()` (`module.rs:1194`) answers `None` for the
   arm structurally (same fall-through as `Constrained`/`NotDetermined`) — confirm no
   slot match is added.

2. **The eligible-for-mono filter** (`module.rs:618`–`635`, currently
   `ast.is_some() AND kind != Overloaded AND kind != UserFn { fn_state: Constrained(_) }`)
   must treat `Polymorphic` as a **mono target** (it is exactly the thing that must be
   monomorphised), NOT skip it the way it skips `Constrained`. Confirm the filter arm.

3. **`CACHE_SCHEMA_VERSION` 5→6 bump** (`crates/cranelisp-backend/src/cache/mod.rs:154`)
   in the SAME change-set — the serde shape of `UserFnState`/`DefKind` changes when
   the variant lands (the no-serde-shape-change-without-a-bump discipline). This bump
   is /backend's; flag to /backend at Wave-1 entry.

The additive-variant cascade (every exhaustive `match` over `UserFnState` in typecheck
+ backend forced to name the new state) is the mechanical Principle-20 cascade — it
surfaces every reader that must decide how to treat a determined-parametric def.

## Operational implication / Context

**Wave-1 coordination (atomic change-set, Principle 20 "the collapse and its
timing-wall resolution land together").** /dev(typecheck) cannot wire the corrected
gate against a not-yet-landed `Polymorphic` variant. So either:
- /arch lands the variant + /backend lands the cache bump FIRST in Wave 1's
  change-set, then /dev wires the gate (`program.rs:947`/`:1143`/`:1312`) + the
  systematic mono; or
- this FIXME is resolved at Wave-1 entry before /dev proceeds.

`Type::is_concrete()` (the gate predicate) already LANDED this sprint
(`crates/cranelisp-types/src/types.rs`); this FIXME is the remaining `cranelisp-types`
shape change the re-shape requires. Resolves alongside FIXME 0374's gate correction.
