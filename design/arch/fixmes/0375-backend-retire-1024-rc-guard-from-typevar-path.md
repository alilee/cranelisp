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

## Issue

`HeapCategory::classify` (`crates/cranelisp-backend/src/heap.rs`) is the single source of truth for whether the RC inc/dec at a call boundary (BC §3 invariant 2) treats a value as a heap pointer. For concrete types it is exact (`Int`/`Bool`/`Float` → `NeverHeap`; `String`/`Fn` → `AlwaysHeap`; `ADT` → constructor-shape verdict). For `Type::Var` it has **no** static knowledge and falls back to `Mixed`, which emits the `<1024` runtime RC guard (`emit_rc_inc_guarded`).

The `<1024` guard is **unsound** on the `Type::Var` path: a negative or `≥ 1024` `Int` flowing through a polymorphic position is misread as a heap pointer, and the dec path frees it (use-after-free). The guard is sound ONLY for its legitimate origin — discriminating a bare nullary ADT tag (provably `tag < 1024`) from a heap pointer **within a single `Mixed` ADT whose type is known**. The full statement is recorded at `bounded-contexts.md` §3 invariant 9.

## Proposed resolution

**Gated on FIXME 0374 (/typecheck — Tier 2 full monomorphisation).** Once Tier 2 guarantees that no `Type::Var` reaches codegen:

1. Make the `Type::Var` arm of `HeapCategory::classify` an `assert`/`panic!` (a `Type::Var` at codegen is now a compiler bug — concreteness is an upstream guarantee), rather than the silent `Mixed` fallback.
2. Retire the `<1024` guard (`emit_rc_inc_guarded`) from the `Type::Var`-originated path. **Keep it ONLY** for nullary-tag ADT discrimination within `Mixed` ADTs (its sound origin — type known, tags bounded).

Land with a backend unit test pinning that (a) a `Mixed` ADT still discriminates nullary tags correctly and (b) the `Type::Var` arm now panics (the assert is the structural guard). Assess the e2e need with /qa.

## Operational implication / Context

Gated on FIXME 0374 (/typecheck — Tier 2). Companion: FIXME 0373 part (iii) (/spec — relax §12.1 representation wording, also Tier-2-gated). This is the codegen-soundness payoff of full monomorphisation: with the guard gone from the polymorphic path, representation becomes fully backend-internal (the §12.1 relaxation's enabling condition). Architecture conclusion: `bounded-contexts.md` §3 invariant 9.
