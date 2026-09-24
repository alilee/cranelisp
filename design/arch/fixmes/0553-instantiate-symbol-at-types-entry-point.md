---
number: 0553
target: /design (int)
filed_by: /arch
filed_at: 2026-07-10
sprint_filed: 106
refers_to: src/worker.rs::capture_reload_instantiation_demands;
  src/worker.rs::extend_reload_demands;
  crates/cranelisp-typecheck/src/form.rs::instantiate_demands;
  tests/plan/s122-evidence-delta.md;
  repl/spec/18-redefinition.md
status: open
---

# Reload re-instantiates the captured mono-variant set, not a replayed source form

Also carries S121 `src/` audit finding F-1 (reload design and Binary/int
realization diverged); [ACT-0965](../../../sprints/actions/ACT-0965-src-audit-residuals.md)
defers to this filing for it.

## Obligation

After a from-source reload, the reload driver re-requests instantiation of the
live `$`-mangled mono-variant set as data — a named polymorphic symbol at each
recorded concrete type tuple — instead of replaying the last `__expr` source
form. Form replay covered only the latest expression and could re-inject an
ill-typed stale `__expr`.

## Current state (verified 2026-09-24)

- Form replay is retired: `capture_instantiation_drivers`, the
  `reload_module` extra-form path and the `__expr` read are absent from
  `src/redefine.rs` and `src/session_v4/lifecycle.rs`.
- `src/worker.rs::capture_reload_instantiation_demands` captures `MonoDemand`
  values and `extend_reload_demands` feeds them into the ordinary cluster
  publisher, consuming the typecheck `instantiate_demands` entry point.
- This work sits in the active S122 Binary/int stream. Its redefinition
  evidence (Q1/Q7 in the S122 evidence delta) is not yet accepted: generic
  replacement, overload-family reorder and foreign-template generation
  correspondence each carry open findings there.

## Closure

The S122 Q1/Q7 reload/redefinition evidence is accepted by `qa`, and
`design/int/int.md` records the demand-capture mechanism as current.
