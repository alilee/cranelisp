---
number: 0300
target: /arch
filed_by: /dev
filed_at: 2026-06-09
sprint_filed: 77
refers_to: tests/trait_imports.rs::{trait_method_short_name_resolves_as_value_for_eq_string,trait_method_short_name_resolves_as_value_for_display_show_int} (FAILING), tests/stdlib_trait_impls.rs::{stdlib_num_float_mappable_path,stdlib_eq_string_mappable_path} (FAILING), spec/07-traits.md §7.6, crates/cranelisp-types/src/ast.rs (Expr::Var), crates/cranelisp-types/src/check.rs (ResolvedCall), crates/cranelisp-typecheck/src/infer.rs (infer_var) + traits.rs (try_resolve_trait_method) + program.rs (annotate), crates/cranelisp-backend/src/compiler/literals.rs (compile_var / compile_operator_as_value), sprints/SPRINT.md §"W-MacroTrait" (RT6), tests/plan/ledger.md (RT6)
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

---

## /dev backend investigation (S77 W-MacroTrait, 2026-06-09) — CONFIRMED cross-crate; re-targeted /arch

`/dev` narrow-deployed on `cranelisp-backend` investigated both symptoms
first-hand (REPL repro with `tests/fixtures/preludes/test-standard.cl` as
`prelude.cl`). Findings, evidence, and the **precise contract** the fix needs.

### Repro (verbatim REPL output, TestStandard prelude)

```
(= "hi" "hi")                  => :primitives/Bool true      ; direct works
(let [f =] (f "hi" "hi"))      => :primitives/Bool false     ; SYMPTOM B (wrong impl)
(let [f show] (f 42))          => Error: undefined variable: show   ; SYMPTOM A
(let [f +] (f 1.0 2.0))        => :primitives/Float inf.0     ; SYMPTOM B (Int impl on Floats)
(let [f =] (f 1 1))            => :primitives/Bool true       ; passes ONLY because Int is the hard-coded default
```

### Both symptoms have ONE root: backend has no trait knowledge (Decision 43),
and the value-position trait-method reference carries no resolution.

When `(let [f =] (f "hi" "hi"))` is checked, `(f "hi" "hi")` is an `Apply`
whose callee is the **local** `f` — not the trait method `=`. Trait-method
resolution in `infer_apply` keys on the callee name, sees `f` (a local), and
records nothing. The trait method `=` appears only as a **bare `Expr::Var` in
value position** (the let binding). That Var:

- receives `inferred_type` from the span-keyed `expr_types` side map (post
  final-substitution → concrete `Fn([String,String], Bool)`), but
- receives **no `ResolvedCall`** — `ResolvedCall` is recorded only for
  `Expr::Apply` (infer.rs:454/460, program.rs:192–197), and `Expr::Var` has
  **no `resolved_call` field** to carry one (ast.rs:155–160).

Backend's `compile_var` (literals.rs:108) therefore has only the bare name:

- **Symptom A (`show`):** `show` is not an operator (`operator_primitive_name`
  returns None — literals.rs:205–219) and `is_known_function("show")` is false
  (no GOT slot for the bare trait-method name — only the per-impl mangled
  entries `Display.show$Int` etc. exist). → falls through to
  `undefined variable: show` (literals.rs:156–159). **Correct backend
  behaviour given no resolution** — backend cannot pick an impl.
- **Symptom B (`=`, `+`):** `compile_operator_as_value` (literals.rs:230) builds
  a wrapper that GOT-indirects to the **hard-coded Int primitive** —
  `operator_primitive_name` maps `"=" → "eq-i64"`, `"+" → "add-i64"`
  unconditionally (literals.rs:205–219). So the String/Float wrapper calls
  `eq-i64`/`add-i64` on pointers / float-bit-patterns → `false` / `inf.0`.

The existing passing e2e `tests/spec_07_traits.rs::operator_as_first_class_value`
uses `(let [op +] (op 4 5))` with **Int** args — green ONLY because the wrapper
is Int-hard-coded; its own comment admits "Not all operator-as-value forms are
reliably first-class across surfaces." §7.6 was never truly satisfied beyond
the Int happy-path.

### Why NOT a pure-backend fix (boundary verdict)

Both symptoms need impl selection: map `(method, concrete operand types)` →
the impl's mangled/primitive name. That mapping is **trait knowledge**, which
Decision 43 deliberately removed from backend ("dispatch is monomorphisation-
keyed in typecheck, not trait-keyed in backend" — traits.rs:1050–1059). The
parallel **already-correct** path is `ResolvedCall::AutoCurry.trait_resolution`:
typecheck resolves the trait method (via `try_resolve_trait_method`, producing
either `BuiltinFn { name: "eq-f64" }` for primitive-implemented methods or
`TraitMethod { mangled_name: "Eq.=$String" }` otherwise) and stashes it on the
curry resolution; backend's `emit_curry_target_call` (control_flow.rs:1341)
just emits the call to that name. Value-position is the **zero-args-applied**
analogue of auto-curry and wants the identical treatment. Backend cannot and
must not re-introduce the deleted `(Trait, method, Type) → primitive` intercept.

### The precise contract (what /arch + /typecheck must produce; what backend consumes)

This is the `ResolvedCall::TraitMethodValue` decision flagged in SPRINT.md §Q4
and the original "Proposed resolution" — **CONFIRMED needed**. The minimal
contract:

1. **`cranelisp-types` (/arch):** `Expr::Var` gains a `resolved_call:
   Option<Box<ResolvedCall>>` field (mirrors `Expr::Apply`; `#[serde(default)]`
   so cached ASTs deserialize). This is the carrier — without it there is **no
   channel** to hand a value-position resolution to backend (the side map is
   overlaid onto Apply nodes only; lib.rs:1353–1357 + program.rs:192–197).
   - A **new `ResolvedCall` variant may not even be required.** The existing
     `TraitMethod { mangled_name, .. }` and `BuiltinFn { name }` carry exactly
     what the wrapper needs (the callable name); arity comes from the Var's
     `inferred_type` (`Fn` param count). If /arch prefers an explicit
     `TraitMethodValue` for legibility/serde-stability that is fine, but the
     functional minimum is **reuse `TraitMethod`/`BuiltinFn` on a Var-carried
     `resolved_call`**. (`ResolvedCall` is `#[non_exhaustive]` so a variant is
     non-breaking either way.)
   - Cascade in the same change-set per baseline-diff discipline: regenerate
     `crates/cranelisp-types/public-api.txt`, update `interfaces.md` /
     `bounded-contexts.md §7` for the new `Expr::Var` field.

2. **`cranelisp-typecheck` (/typecheck):** in a post-body deferred pass
   (sibling of `resolve_deferred_trait_calls`, infer.rs:588), for each
   `Expr::Var` that is a trait method (`is_trait_method_with_state`) used in
   value position (not the callee of an enclosing Apply), read the Var's final
   `inferred_type` from `expr_types`, take its `Fn` param types, call
   `try_resolve_trait_method(name, param_types, span)`, and record the result
   on the Var's span in `method_resolutions.resolved_calls`. The annotate pass
   (program.rs:180) then writes it onto `Expr::Var.resolved_call` — extend
   `annotate_expr_from_maps`'s Apply-only overlay to also cover `Expr::Var`.
   - Constraint already satisfied: `infer_var` does NOT reject trait methods as
     values (only constrained/multi-sig fns are rejected — infer.rs:230–264),
     consistent with §7.6 allowing it. No new rejection needed.

3. **`cranelisp-backend` (/dev, this crate — small, lands after 1+2):**
   `compile_var` gains an early branch: if the Var carries
   `resolved_call: Some(TraitMethod { mangled_name } | BuiltinFn { name })`,
   emit a zero-capture dispatch-wrapper closure that calls that name with arity
   = `inferred_type` param count — reusing the `compile_fn_as_value` /
   `emit_wrapper_call` machinery (for `TraitMethod`/mangled) and the
   `BuiltinFn` inline path (mirroring `emit_curry_target_call`,
   control_flow.rs:1341–1370). This **replaces** the hard-coded Int
   `compile_operator_as_value` path for resolved methods; the bare-Int
   fallback may stay for unresolved bare operators (back-compat) or be removed
   once typecheck resolves all of them. `compile_var`'s signature must take the
   Var's `resolved_call` + `inferred_type` (currently it takes only
   `name, span` — mod.rs:976 passes them).

### Disposition

Cannot be completed within the `cranelisp-backend` boundary this invocation:
items 1 (cranelisp-types, /arch-owned) and 2 (cranelisp-typecheck) are
prerequisites for item 3. Backend made **no source changes** (build clean).
The four e2e tests stay **failing-not-ignored** as the durable regression
guards. **Route:** /arch authors the `Expr::Var.resolved_call` field (+ variant
if chosen) with user review per the explicit-Decision-review rule, then
/typecheck implements item 2, then /dev(backend) implements item 3 and resolves
this FIXME. Leave **open** until all three land and all four tests pass.
