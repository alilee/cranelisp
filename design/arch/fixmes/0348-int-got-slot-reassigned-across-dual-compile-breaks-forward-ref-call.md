---
number: 0348
target: /design
filed_by: /dev
filed_at: 2026-06-14
sprint_filed: 82
refers_to: src/worker.rs (got-slot allocation + the dual compile_to_module of the entry module), crates/cranelisp-typecheck/src/program.rs (mono-variant creation reorders slots), design/arch/fixmes/0347-backend-monomorphise-polymorphic-fn-with-lambda-and-fold.md (defect 2 re-attribution), tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify (the 0344 e2e)
status: open
---

# 0347 defect (2) re-attributed: the 0344 e2e wrong-value is an int GOT-slot REASSIGNMENT bug, not a backend mono/codegen bug

## Issue (S82 Wave 2 /dev backend finding)

The 0347 fixme attributed defect (2) — `(reduce add-i64 0 [1 2 3])` returns
exit 0 instead of 6 — to "the monomorphisation/codegen of the recursive
helper" in **backend**. Narrowing the repro in the backend crate shows the
backend codegen is **correct**; the defect is an **int GOT-slot allocation
instability** exposed by definition order (which the 0344 typecheck fix made
observable).

### Minimal repro — the trigger is DEFINITION ORDER, nothing else

`reduce` defined BEFORE `reduce-loop` (forward reference) → exit 0 (WRONG):

```clojure
(import [primitives [add-i64 ge-i64 vec-len vec-get Pure]])
(defn reduce [f init v] (reduce-loop f init v (vec-len v) 0))
(defn reduce-loop [f acc v :primitives/Int len :primitives/Int i]
  (if (ge-i64 i len) acc
    (reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))
(defn main [] (Pure (reduce add-i64 0 [1 2 3])))
```

The SAME program with `reduce-loop` defined FIRST → exit 6 (CORRECT). The
`collect`/`(Vec a)` sibling from the 0344 e2e is NOT required to trigger it —
forward-reference ordering alone is the trigger.

### Root cause — `reduce`'s got_slot is REASSIGNED between the two compiles

The entry module is compiled by `compile_to_module` **twice** (the
typecheck-product `[__expr]` batch, then the `[…, __expr]` batch). In the
forward-ref case the GOT-slot assignment is **not stable across the two
passes**:

- when `main` is compiled, `resolve_got_target("reduce")` reads
  `reduce.got_slot == 2` and bakes `__cranelisp_got_user[2]` into main's call;
- at GOT-data emission, `reduce.got_slot == 0` and `reduce-loop.got_slot == 2`.

So main's baked slot 2 now points at **`reduce-loop`**, not `reduce`. main
calls `reduce-loop` with `reduce`'s arguments → the fold never runs → returns
the initial accumulator `0`.

Backend evidence (CLIF, `CRANELISP_CODEGEN_DUMP`):
- BROKEN: `main` calls `__cranelisp_got_user + 16` (slot 2); GOT-emission has
  `reduce@0`, `reduce-loop@2`, `main@1`.
- WORKING: `main` calls `__cranelisp_got_user + 0` (slot 0); GOT-emission has
  `reduce@2`, `reduce-loop@1`, `reduce$Int+Vec@3` (a mono variant exists),
  `main@1`.

`resolve_got_target` faithfully reads whatever `got_slot` the entry carries —
the bug is that the entry's `got_slot` **changes** (reduce: 2 → 0) between
main's compile and the final emission, while main's baked call is frozen at the
stale value. Backend's CLIF for `reduce`/`reduce-loop` is byte-identical
between the working and broken orderings (only func-id numbers differ), which
is why this is NOT a backend codegen defect.

## Proposed resolution

Owning surface: **int** (GOT-slot allocation across the entry-module dual
compile) — possibly with **typecheck** (the forward-ref / mono-variant-creation
reorders which symbols get slots). The fix must guarantee a symbol's `got_slot`
is **stable for the lifetime of a module's GOT** once any caller has baked a
call against it — i.e. slots are allocated once and never reassigned across the
two `compile_to_module` passes (or both passes see one frozen slot map). The
0344-introduced polymorphism is the trigger, but the slot-reassignment hazard
is pre-existing and orthogonal to the inference change.

## Operational implication / Context

- **0347 defect (1) IS fixed in backend this sprint** (S82 W2 /dev): the
  span-derived inner-fn names (`__lambda_…`, `__wrap_…`, `__wrap_op_…`,
  `__wrap_tmv_…`, `__curry_…`, `__par_cont_…`) now carry a
  monomorphisation discriminator (the sanitized enclosing-fn name), so N mono
  copies of one source span no longer collide on `define_function`. Unit guard:
  `cranelisp-backend compiler::tests::inner_fn_discriminator_uniquifies_per_mono_instance`.
- **0347 defect (2) is NOT a backend fix** — it is this slot-reassignment bug.
  The 0344 e2e (`polymorphic_accumulator_fold_does_not_over_unify`) stays RED
  until int/typecheck stabilizes slot assignment. It is a known failing guard,
  carried forward.
- **The typecheck `expr_contains_lambda` band-aid gate (program.rs) is now safe
  to remove with respect to defect (1)** — the backend no longer collides on
  monomorphised lambda names. (Removing it may re-expose defect (2)'s slot
  instability for the higher-order examples; that is the int/typecheck work
  above, not a reason to keep the gate.) `/dev (backend)` cannot edit typecheck;
  this is the note for the typecheck follow-up.
