---
number: 0381
target: /typecheck
filed_by: /dev
filed_at: 2026-06-16
sprint_filed: 84
refers_to: design/typecheck/monomorphisation.md §2-§3 (slot gate + systematic mono), design/backend/ring2-rc.md §1.6 (the gated bare-Var panic), design/arch/bounded-contexts.md §3 invariant 9
status: open
---

# The 0375 backend backstop is blocked on 0374 — the prelude compiles GENERIC bodies whose value positions carry sound, scheme-quantified free vars (bare `Type::Var` AND `Mixed`-ADT-with-free-var)

## Issue

While landing the S84 Wave 2 belt-and-braces backend backstop (the widened
`HeapCategory::classify` panic, FIXME 0375/0379), I discovered that the
**prelude/stdlib compiles GENERIC-FUNCTION BODIES whose value positions carry
sound, scheme-quantified free type variables** — reaching `HeapCategory::classify`
at RC sites. The backstop panic (as specified: `panic iff classify == Mixed &&
ty.is_representation_undetermined()`) fired on the valid prelude, crashing
prelude-using tests. Two distinct shapes, BOTH sound:

1. **Bare `Type::Var`** — a constructor-arg field value in a generic body:
   `compile_constr_adt` → `compile_consuming_arg_list`
   (`crates/cranelisp-backend/src/compiler/apply.rs:485`) → `classify(Var(0))`.
   (234 e2e failures when bare-`Var` panicked.)

2. **`Mixed`-shaped ADT carrying a free var** — e.g. `(List a)` `[Var(47)]` in
   `collections.list`'s generic body:
   `classify(ADT(collections.list/List, [Var(47)]))` → `Mixed` → panic. (83 e2e
   failures with the ADT-only-scoped panic.)

Reproduced deterministically:

```
echo "(option/Some 1)" > user.cl   # any prelude-touching program
CRANELISP_LIB=tests/fixtures/ cranelisp --run user.cl
# → panic in module 'prelude' / 'collections.list': classify ... ty = ADT(.../List, [Var(47)])
```

This means the design premise behind `ring2-rc.md §1.6` ("post-0374, **no
`Type::Var` reaches codegen**, so the backstop is unreachable") is **not yet
total**: the structural slot gate (`monomorphisation.md` §2 — slot ⟺
`is_concrete()`) makes a generic def *slot-less* (`Polymorphic`), but a slot-less
generic def's **body is still being compiled** for the prelude/stdlib (the value
positions inside it reach RC classification with the body's quantified free vars).
Per `monomorphisation.md` §3.4 the generic template "is never compiled" — but in
practice it IS, so its sound polymorphic value positions reach the backend.

This is a **0374 (Wave-1) gap surfaced by the Wave-2 backstop**, NOT a
position-completeness gap in the §3.11.1 ambiguity check. Both shapes are SOUND
polymorphic values (the var is quantified into the enclosing generic defn's
scheme), so the typecheck position-complete check correctly ADMITS them (they are
not ambiguous — pinned per-instantiation at each concrete call site; the check's
`allowed_vars` set excludes a scheme-quantified var from the verdict). The backend,
lacking scheme context, cannot tell a sound quantified var from a genuinely
unpinned one — the predicate says "representation-undetermined" for both.

## Proposed resolution

Extend the structural slot gate / systematic mono so a slot-less `Polymorphic`
generic def's **body is NOT emitted to codegen at all** (it is compiled only as
concrete monomorphised instances per `monomorphisation.md` §3.4 — "the generic
template is never compiled"); OR ensure every RC-classification site is reached
only POST-monomorphisation so the value's type is always concrete at `classify`.

Until then, the **ENTIRE 0375 backend backstop stays DEFERRED** —
`classify(Type::Var)` / `classify(TyConApp)` AND `classify(Mixed-ADT-with-
free-var)` keep their conservative non-crashing `Mixed` fallback (the operatively
load-bearing safety net per `ring2-rc.md §1.6` Risk "premature landing"). The S84
Wave 2 change-set landed the **TYPECHECK half only** — the POSITION-COMPLETE
§3.11.1 ambiguity check (`cranelisp-typecheck::program::find_ambiguous_value_position`),
which IS the load-bearing fix that closes the 0379 hole (it rejects a
genuinely-unpinned `(Option a)` while admitting a sound scheme-quantified one).

When this FIXME is resolved (0374 made total — no free var in any compiled body),
re-arm the backstop by restoring the gated `panic!` in
`crates/cranelisp-backend/src/heap.rs` `HeapCategory::classify` (the exact code is
in an inline comment there):

```rust
if category == HeapCategory::Mixed && ty.is_representation_undetermined() {
    panic!("... BC §3 invariant 9 ...");
}
```

and flip the three deferred unit tests
(`test_var_is_mixed_fallback_backstop_deferred`,
`test_tyconapp_is_mixed_fallback_backstop_deferred`,
`test_mixed_adt_with_free_var_is_mixed_backstop_deferred`) to `#[should_panic]`.

## Operational implication / Context

- **The 4 §3.11.1 acceptance guards (`mono_ambiguous_{match_scrutinee,call_arg,
  ctor_field,if_branch}_rejected_neg`) flip GREEN on the TYPECHECK half alone** —
  they are rejected at typecheck by the position-complete check, never reaching
  codegen, so the deferred backend backstop does not weaken them.
- The deferral is the correct disposition under `ring2-rc.md §1.6`'s own gating:
  the backstop is a *strict downstream* of 0374, and 0374 is not yet total. Landing
  the panic now is *strictly worse* than the `Mixed` fallback (it crashes the valid
  prelude instead of running it).
- Re-arming is a ~3-line restore once 0374 is total; the diff is noted inline in
  `heap.rs`.
