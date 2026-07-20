---
number: 0705
target: /qa
filed_by: /dev (cranelisp-typecheck, S114 W7)
filed_at: 2026-07-20
sprint_filed: 114
scheduled: S114 W7 disposition (attribution + auto-curry cell re-locus) → backend fix
refers_to: tests/shadowing_scope_lookup.rs::let_shadowed_trait_operator_auto_curry_resolves_to_local; crates/cranelisp-typecheck/src/program/mono_collect.rs::resolve_auto_curry; crates/cranelisp-backend (fn-as-value wrapper / AutoCurry codegen); SPRINT.md §Notes 2026-07-20 rider-batch entry ("fn-as-value wrapper reached codegen with no GOT-slot carrier")
status: open
---

# AutoCurry over a §4.6 LOCAL closure target reaches codegen with no GOT-slot carrier

## Severity
Important (a spec-valid program fails to compile; blocks the MS-P7-sibling
trait-shadow auto-curry cell from going fully green).

## Context — the W7 trait-shadow fix that surfaced it

The W3-review Important-1 trait-shadow mis-dispatch fix landed (W7, typecheck):
a `let`/`fn`/param binding that shadows a trait method/primitive now resolves to
the LOCAL closure at ALL call-position seams — the infer_apply post-unify block,
the auto-curry filler, `resolve_deferred_trait_calls` (carrier-verdict guard),
and `resolve_auto_curry` (carrier-verdict guard). Two of the three shadow cells
flipped GREEN:

- `let_shadowed_trait_operator_call_resolves_to_local_not_dispatch` — GREEN
- `let_shadowed_trait_operator_call_repl_resolves_to_local` — GREEN

The third — the AUTO-CURRY cell — did NOT flip to the correct value (0). Instead
its symptom CHANGED: it no longer mis-dispatches to `Num.+` (returns 3); it now
fails at codegen:

```
codegen error: fn-as-value wrapper for '+' reached codegen with no GOT-slot
carrier (S110 W2 keyed read; backend-keyed-consumer.md §1.2/§10)
```

This is the MC-E1 "a non-flip is evidence" pattern: the typecheck fix is the
discriminating experiment; the auto-curry cell's non-flip-to-green proves a
SEPARATE defect downstream. It re-attributes OUT of typecheck.

## The defect is BACKEND and NOT trait-specific — minimal repro

`resolve_auto_curry` now correctly produces `ResolvedCall::AutoCurry { target_name:
"+", trait_resolution: None }` with `ApplyRef::ViaCallee` (the local carrier — the
callee `Var` has `VarRef::Local`, so `mono_collect.rs:807-819` records no
`Dispatch` FQ). The BACKEND then tries to emit a fn-as-value wrapper for the bare
`target_name` and looks up its GOT slot — but a LOCAL closure has no GOT slot.

It is NOT specific to trait names. A NON-trait local closure auto-curry fails
identically (PrimitivesOnly, `--run`):

```clojure
(defn f [] (let [g (fn [a b] 0)] ((g 1) 2)))
(defn main [] (Pure (f)))
```
→ `codegen error: fn-as-value wrapper for 'g' reached codegen with no GOT-slot
carrier`

The FULL call works: `(let [g (fn [a b] 0)] (g 1 2))` → exit 0. Only the PARTIAL
application (auto-curry) of a local closure hits the gap.

This is the "fn-as-value wrapper reached codegen with no GOT-slot carrier, fails
even impl-present" defect the S114 rider-batch flagged unpinned to /qa
(SPRINT.md §Notes, 2026-07-20). This FIXME supplies the minimal repro
(`((g 1) 2)`) proving it is a general backend AutoCurry-over-local-target gap.

## Requested disposition (/qa)

1. Re-attribute the auto-curry cell: `tests/shadowing_scope_lookup.rs::
   let_shadowed_trait_operator_auto_curry_resolves_to_local`'s `// defect:` locus
   currently reads `class=wrong-scope-lookup locus=…infer.rs:933-958` — that
   typecheck mis-dispatch is FIXED. Re-locus to the backend AutoCurry-over-local
   carrier-loss (or the general fn-as-value-wrapper-for-local seam). The class is
   arguably `carrier-loss` (an AutoCurry with a ViaCallee/local carrier reaches
   backend with no GOT target).
2. The backend fix: an AutoCurry whose callee resolved `VarRef::Local` must curry
   the LOCAL closure value (captured from the scope stack), not look up
   `target_name`'s GOT slot. A born-green control worth adding: the non-trait
   local `((g 1) 2)` above (isolates the gap from trait dispatch).
3. Typecheck side is complete: `resolve_auto_curry` + `resolve_deferred_trait_calls`
   consult the `VarRef` carrier verdict; the local closure is correctly NOT
   dispatched. No further typecheck work is owed for this cell.
