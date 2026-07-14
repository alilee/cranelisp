---
number: 0585
target: /arch
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: monomorphisation of a generic function referenced in VALUE position —
  the collection that mints a concrete mono instance must be UNIFORM across every
  value position (Apply arg, Let/ParBind binding value, if-branch, match-arm value,
  vector element, …). Currently per-position whitelisted → each new position leaks
  the slot-less template to codegen. Recurring class, 3rd instance.
status: open
---

# Recurring class → /arch — value-position monomorphisation must be uniform across ALL value positions, not per-position patched

## The recurrence (3 instances, same root)

A generic user fn referenced as a VALUE (not a call) must have a concrete mono
minted at its inferred type, or the slot-less `UserFnState::Polymorphic` template
reaches the backend and leaks (`backend/literals.rs:191` → `undefined variable`
codegen error). The minting collection has been PATCHED PER-POSITION three times:

1. **0374** — higher-order-fn arg position (`(map gcount xs)`).
2. **0488** — imported generic value ref.
3. **0571** — `Let`/`ParBind` binding value (`(let [f gcount] …)`), S109.

Each fix widened `collect_parametric_fn_value_args`
(`crates/cranelisp-typecheck/src/program.rs:3172-3187`) to one more whitelisted
position. **The class is not closed:** `/review` (S109, 0571) found concrete
generic value refs in **if-branch / match-arm / vector-element** positions STILL
leak — `((if c gcount gother) [1 2])` mints nothing (neither branch `Var` is an
Apply arg nor a Let value) → slot-less template → the same D1 codegen leak just
"cured." This is per-variant patching of an operation that must be uniform.

## The uniform shape already exists 20 lines away

`find_ambiguous_value_position` (`program.rs:1950-2028`) walks **every** value
position via `for_each_child_expr` with a callee exclusion, and dies §3.11.1 for
*indeterminate* generic bindings — uniformly, all positions. The MINT side should
mirror exactly that structure: verdict on every non-callee `Var` that resolves to a
concrete-`Fn` monomorphisable-polymorphic entry → mint. Then the whitelist is
deleted and the class is structurally closed (the `for_each_child_expr` walk can't
miss a position).

## The /arch ask (recurring class = architecture problem, not instance)

Per the `/review` recurring-defect-class discipline: instance-patching this a 4th
time is the smell. Design the uniform collection (mirror the ambiguity scan's
`for_each_child_expr` walk) so mint and die share ONE value-position enumeration —
the mint-or-die decision is made at every value position by construction, no
whitelist. Record the invariant so a future value-position addition can't
reintroduce the leak (candidate: a debug-assert / structural guard that a
concrete generic `Var` reaching codegen is impossible). `/qa` adds the
value-position × {mint, die} matrix (if / match / vector cells are the missing
REDs).

## S109 disposition

The **instance** (if/match/vec leak) is fixed in the S109 **0571.2** `/dev` pass
via the uniform collect (the fix is local). This FIXME is the **class** record for
`/arch` — the structural guard + the invariant — which may pair with the S110
backend-boundary centrepiece (0583): both are "one operation, re-derived per site,
must be single-sourced." `/qa` owns the value-position matrix.
