---
number: 0500
target: /dev (cranelisp-frontend)
filed_by: /sprint
filed_at: 2026-07-03
sprint_filed: 101
refers_to: tests/plan/coverage-audit-s101.md §3 (frontend row), design/arch/fixmes/0485-frontend-macro-clause-exhaustion-diagnostic-internal-span.md, sprints/METHOD.md §2.2
status: open
---

# Frontend rendered-diagnostic unit tier — cure the P6 diagnostic-surface exemption at unit grain

## Issue

The S101 coverage audit judged frontend's unit tier structurally GOOD with one named gap: **no tests assert rendered user-facing diagnostic quality**. The "error tests use substring" standard institutionalizes weak assertions for all diagnostics (miss-pattern P6; live exhibits: 0485 — internal span `1000056..`, Debug FQSymbol dump, recursion-bottom noise in the macro clause-exhaustion diagnostic; 0490 — misleading phantom-member error). Diagnostic-emitting submodules have no per-submodule scenario coverage for what the message must and must not contain.

## Proposed resolution

Per METHOD §2.2 (submodule × scenario-class): add a rendered-diagnostic unit tier to the diagnostic-emitting submodules — assert real spans (never synthetic/internal `1000000+` spans), no `Debug`-format dumps in user-facing text, the named-symbol and expected-form parts of each message, and negative assertions on internal artifacts. Fixing 0485 itself belongs to that FIXME; this one is the *tier*, so the 0485 class cannot recur silently.

## Operational implication / Context

Sibling of 0495–0498 (per-crate unit-tier drains from the audit's submodule thinness map). Rides frontend's next D/D/R touch; small enough to pair with the 0485 fix in one change-set.
