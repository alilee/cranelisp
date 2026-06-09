---
number: 0306
target: /dev
filed_by: /sprint
filed_at: 2026-06-10
sprint_filed: 77
refers_to: crates/cranelisp-typecheck/src/infer.rs (resolve_value_position_trait_methods + is_trait_method_with_state), crates/cranelisp-backend/src/compiler/literals.rs (compile_var locals-first ordering)
status: open
---

# Value-position trait-method resolution: local-shadow annotation false-positive

## Issue

Sprint 77 RT6 added a typecheck pass (`resolve_value_position_trait_methods`)
that annotates a bare `Expr::Var` in value position with a `resolved_call` when
the name is a trait method with a concrete function `inferred_type`. The
predicate (`is_trait_method_with_state`) consults the **module symbol table
only**, not local scope. A local binding that *shadows* a trait-method name —
e.g. `(let [show (fn [x] (add-i64 x 1))] (let [g show] (g 42)))` — and has a
concrete `Fn` `inferred_type` therefore gets a **bogus `resolved_call`** attached
to the local-shadow Var at the annotation layer. The language permits this
shadowing (locals-first lookup, §8.6.1).

**Not a live miscompile**: backend `compile_var` checks `self.variables.get(name)`
BEFORE the `resolved_call` branch, so the shadow returns the correct local value
(verified: the shadow case returns `:primitives/Int 43`). The wrong annotation is
masked only by backend ordering. Surfaced by the RT6 `/review` gate (Suggestion).

## Proposed resolution

Either (a) gate the value-position predicate on "name is NOT locally bound at
this point" (so the annotation is never attached to a shadowing local), or
(b) keep the backend-ordering reliance but add a `cranelisp-typecheck` unit test
for the adversarial shadow case documenting that the annotation may be present
but is correctly overridden by backend locals-first dispatch. (a) is cleaner.

## Operational implication / Context

Low priority — no behavioural bug today; defends against a future backend
refactor that reorders the locals check. Stage 2 quality item.
