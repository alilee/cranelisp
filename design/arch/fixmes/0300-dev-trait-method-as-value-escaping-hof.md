---
number: 0300
target: /dev
filed_by: /qa
filed_at: 2026-06-09
sprint_filed: 77
refers_to: tests/trait_imports.rs::{trait_method_short_name_resolves_as_value_for_eq_string,trait_method_short_name_resolves_as_value_for_display_show_int} (FAILING), tests/stdlib_trait_impls.rs::{stdlib_num_float_mappable_path,stdlib_eq_string_mappable_path} (FAILING), spec/07-traits.md §7.6, sprints/SPRINT.md §"W3 / W-MacroTrait" (RT6), tests/plan/ledger.md (RT6)
status: open
---

# Trait method as a first-class value — dispatch wrapper not emitted when the method escapes

## Issue

Per spec §7.6 (a MUST that already exists — no /spec change needed), a trait
method MUST be usable as a first-class value: `(let [f show] (f 42))`,
`(let [f =] (f "hi" "hi"))`. The dispatch-wrapper closure is emitted for DIRECT
application but NOT (or WRONGLY) when the method name escapes as a value /
HOF argument. Four failing tests, two distinct symptoms:

**Symptom A — method-as-value not resolved (`undefined variable`):**

- `trait_method_short_name_resolves_as_value_for_display_show_int`
  (`(let [f show] (f 42))`, §7.6):
  ```
  Error: codegen error at 8..12: codegen failed for /: codegen error at 8..12:
         undefined variable: show
  ```
- `trait_method_short_name_resolves_as_value_for_eq_string`
  (`(let [f =] (f "hi" "hi"))`, §7.6): same shape — `=` not resolved as a value.

The method name bound in a `let` (escaping the call site) has no dispatch-wrapper
closure emitted, so codegen reports the bare method name as an undefined variable.

**Symptom B — method-as-value resolves but dispatches to the WRONG impl:**

- `stdlib_num_float_mappable_path` — `(let [f +] (f 1.0 2.0))` MUST return `3.0`;
  observed `:primitives/Float inf.0` (dispatched to the Int `+` impl, not Float).
- `stdlib_eq_string_mappable_path` — `(let [f =] (f "x" "x"))` MUST return
  `:primitives/Bool true`; observed `:primitives/Bool false` (wrong/Int-ish impl).

When the method DOES resolve as a value, the wrapper is not specialised to the
argument types at the call site, so it picks a default/first impl instead of the
correct one for the runtime argument types.

## Proposed resolution

Phase-3 design call (typecheck + backend; not pre-authored per Principle 8). A
possible non-breaking addition flagged by /arch Phase-2 Q4: a
`ResolvedCall::TraitMethodValue` variant (`ResolvedCall` is `#[non_exhaustive]`)
so the method-as-value path carries the receiver/dispatch info the wrapper needs.
If confirmed in Phase 5, /arch authors the variant + baseline regen + interfaces/
BC cascade in one change-set. The wrapper must (a) be emitted whenever the method
escapes as a value, and (b) dispatch on the actual argument types at application,
matching the direct-application path.

## Operational implication / Context

S77 W-MacroTrait (RT6). Owner: /dev typecheck + backend. §7.6 MUST already
exists — no /spec change. The four failing tests are the durable record +
regression guards. Symptom A (undefined) and Symptom B (wrong impl) are likely
the same root (escaping wrapper) at two stages; verify both clear together.
