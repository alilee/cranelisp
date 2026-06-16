---
number: 0375
target: /backend
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 83
refers_to: design/arch/bounded-contexts.md §3 invariant 9, crates/cranelisp-backend/src/heap.rs (HeapCategory::classify Type::Var arm ~line 456, emit_rc_inc_guarded ~line 191)
status: open
---

# Backend: make classify(Type::Var) unreachable; retire the <1024 RC guard from the Type::Var path (keep it for nullary-tag ADT discrimination)

> **BACKSTOP SUPERSEDED BY THE CONCRETE-BOUNDARY-TYPE ARC (S84 user ruling 2026-06-16; /arch design `design/arch/concrete-boundary-type.md`; tracked by FIXME 0383).** The user ruled the goal is that generics are *not representable* at the backend boundary. Under the arc, `HeapCategory::classify` takes a `ConcreteType` (no `Var` variant), so the `classify(Type::Var)→panic` backstop this FIXME specifies becomes **inexpressible — there is no `Var` arm to make unreachable** (Phase 3). The TWO real edits in the "Proposed resolution" below SURVIVE the re-framing: **(1) retire the `<1024` guard from the representation-undetermined path** (it just happens via the `ConcreteType` switch — the guard's `Type::Var`/`Mixed`-with-var caller no longer exists), and **(2) KEEP the `<1024` guard for type-known nullary-tag ADT discrimination** (that path classifies a fully-concrete `ConcreteType::ADT` with no var — unchanged). So this FIXME's *disposition* (retire-from-var-path, keep-for-nullary-tag) is correct and folds into Phase 3; only its *mechanism* (an assert/panic on a `Var` arm) is dropped in favour of the structural foreclosure. The interim DEFERRED state (FIXME 0381) holds until the arc's Phase 3 lands. This FIXME closes at Phase 3 (backend consumes `ConcreteType`).

## Issue

`HeapCategory::classify` (`crates/cranelisp-backend/src/heap.rs`) is the single source of truth for whether the RC inc/dec at a call boundary (BC §3 invariant 2) treats a value as a heap pointer. For concrete types it is exact (`Int`/`Bool`/`Float` → `NeverHeap`; `String`/`Fn` → `AlwaysHeap`; `ADT` → constructor-shape verdict). For `Type::Var` it has **no** static knowledge and falls back to `Mixed`, which emits the `<1024` runtime RC guard (`emit_rc_inc_guarded`).

The `<1024` guard is **unsound** on the `Type::Var` path: a negative or `≥ 1024` `Int` flowing through a polymorphic position is misread as a heap pointer, and the dec path frees it (use-after-free). The guard is sound ONLY for its legitimate origin — discriminating a bare nullary ADT tag (provably `tag < 1024`) from a heap pointer **within a single `Mixed` ADT whose type is known**. The full statement is recorded at `bounded-contexts.md` §3 invariant 9.

## S84 RE-SHAPE — backstop, NOT mechanism (re-evaluation per the user ruling, 2026-06-16)

**Re-evaluated against the user's "slot ⟺ concrete" ruling (Principle 20 S84 generalisation; BC §7).** The question posed: does 0375 collapse into the representation invariant, or remain a meaningful separate change? **Determination: 0375 REMAINS a meaningful change, but its FRAMING shifts from *mechanism* to *backstop*.**

Under the re-shaped 0374, a `Type::Var` can no longer reach codegen *as a value* because the **slot-emission door is shut for non-concrete defs by construction** (the slot gate tests `is_concrete()`; a non-concrete def is slot-less; the slot-less arm returns `None` at `callable_got_slot()`/`resolve_got_target`). The codegen-side `classify(Type::Var)` arm is therefore no longer the thing that *prevents* the `(Box a)`-through-HOF SIGSEGV — the upstream typecheck slot gate is. 0375's panic is now a **structural backstop**: an assert that documents and pins the invariant at the codegen seam, which under correct 0374 can never fire. This is exactly the Principle 18 relationship (the structural upstream form is strictly stronger than the downstream assert; the assert is still worth landing as the seam-local tripwire that turns any *future* regression of the slot gate into an immediate, located panic rather than a silent UAF).

It does **not** collapse to nothing: the `<1024` `emit_rc_inc_guarded` call-site removal on the `Type::Var` path is still a real codegen edit (removing dead-once-0374-lands but currently-live unsound code), and keeping the guard for its sound origin (nullary-tag ADT discrimination) is still a real disposition. So 0375 lands as written, re-titled in intent.

## Proposed resolution

**Gated on FIXME 0374 (/typecheck — the corrected slot gate + Tier-2 systematic mono).** Once 0374 makes a non-concrete def slot-less (so no `Type::Var`-typed value reaches codegen):

1. Make the `Type::Var` arm of `HeapCategory::classify` (`crates/cranelisp-backend/src/heap.rs:456`) an `unreachable!`/`panic!` naming the invariant **and its upstream owner** ("a `Type::Var` at codegen is a compiler bug — the typecheck slot gate (`is_concrete()`, BC §7) forbids slotting a non-concrete def; this arm is a structural backstop, not the prevention mechanism"), rather than the silent `Mixed` fallback. **Split `TyConApp` off** — keep its `Mixed` fallback (separate HKT question; folding it into the panic would crash valid HKT codegen).
2. Retire the `<1024` guard (`emit_rc_inc_guarded`) from the `Type::Var`-originated path. **Keep it ONLY** for nullary-tag ADT discrimination within `Mixed` ADTs (its sound origin — type known, tags bounded). The two `Mixed` reasons are separable at `classify`, not at the 15 guarded-RC call sites — so the fix is `classify`-local, no call-site refactor, no new `HeapCategory` variant.

Land with a backend unit test pinning that (a) a `Mixed` ADT still discriminates nullary tags correctly and (b) the `Type::Var` arm now panics (`#[should_panic]`). E2e = /qa's cross-mode SIGSEGV repros. No baseline move (backend-internal). Assess the e2e need with /qa.

## Operational implication / Context

Gated on FIXME 0374 (/typecheck — Tier 2). Companion: FIXME 0373 part (iii) (/spec — relax §12.1 representation wording, also Tier-2-gated). This is the codegen-soundness payoff of full monomorphisation: with the guard gone from the polymorphic path, representation becomes fully backend-internal (the §12.1 relaxation's enabling condition). Architecture conclusion: `bounded-contexts.md` §3 invariant 9.
