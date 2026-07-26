---
number: 0891
target: /design
filed_by: /dev
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/backend/transitive-drop-glue.md §3.4 D2; crates/cranelisp-backend/src/compiler/fn_compiler.rs::emit_heap_binding_decs
status: open
---

# D2's entry check has exactly one escapee: the generic ctor template's own parameter

## Issue

`transitive-drop-glue.md` §3.4 D2 predicted the entry check's answer:

> **Entry check for slice S1:** `/dev` enumerates every release call site that
> cannot supply a concrete type *before* migrating. The expected answer is none
> — the residual-`Var` path is a *classification* path used by the generic ctor
> template, which constructs and never releases.

**The second half is false.** The generic constructor `Def`'s own template body
both constructs AND releases, and W3 hit it at slice S5, the moment
`emit_heap_binding_decs` became type-directed. Reproduced by the 0810 control
`control_let_bound_int_payload_scrutinee_balances`, whose program is
`(deftype B (Mk [v]))` — no type parameters at all:

```
codegen failed for user/B.Mk: release site in 'B.Mk' reached a non-concrete
type Var(0); canonical drop glue is keyed on the concrete type and there is no
shallow fallback
```

Note the shape: `B` is monomorphic. The residual `Var` is not about generics —
it is an **undeclared constructor field**, whose type typecheck leaves as a
type variable. The ctor `Def` is codegen'd once, so its parameter's signature
type is that `Var` and its runtime representation is the uniform i64
(`signature_heap_category`'s `Err` arm → `Mixed`, FIXME 0394).

The mechanism, read at the seam:

1. the template's body is `MonoExpr::ConstrADT`, whose fields are compiled by
   `compile_consuming_arg_list`;
2. that emits a **guarded `rc_inc`** on the `Var`-typed parameter (it classifies
   `Mixed`);
3. `pop_scope_with_cleanup` then emits the balancing **guarded `rc_dec`** at
   template exit.

So the pair is a matched counted-borrow discharge on a value the just-built box
also references — never the last reference, so nothing is ever stranded there.
It is not a type-directed teardown and cannot become one: one template body
serves every value the constructor is ever applied to.

## What W3 did, and why it is not a fallback arm

`emit_heap_binding_decs` carries ONE explicit, named branch: a binding whose
type is not concrete takes the guarded shallow dec, with the reasoning above in
a comment at the site. Every other release site keeps D2's rule verbatim —
`emit_typed_rc_dec` still hard-errors on a non-concrete type, so post-call
decs, match wrapper releases, capture slots and Vec element releases have no
escape hatch.

This is recorded rather than resolved because the choice belongs to `/design`:
the alternative readings are (a) the branch is correct and D2's prose should
name this class as the one admitted exception, (b) the template's inc/dec pair
should not exist at all (the box takes the reference; the template owes
nothing), which is a producer-side change with its own balance consequences, or
(c) FIXME 0394 should close — undeclared ctor field types become concrete — and
the branch deletes with it.

## Proposed resolution

`/design` rules between (a)/(b)/(c) and amends §3.4 D2's entry-check
expectation to match what the migration measured. If (a), the §11 no-interim
list should name this branch explicitly so `/review` can tell it from the
shallow fallback the migration exists to delete.

## Context

- Found: S118 W3 slice S5, `/dev`(backend).
- The branch is at `emit_heap_binding_decs`; the paired inc is
  `compile_consuming_arg_list`'s guarded inc.
- Behaviour at HEAD before the migration was identical (the legacy
  `emit_rc_dec_with_inline_drop_glue` early-returned on a non-ADT type and fell
  through to the same guarded dec), so this is a documentation/ruling gap, not
  a behaviour change introduced by W3.
