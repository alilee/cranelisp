# design/typecheck/

Solution design documents for the Cranelisp typechecker (inference, traits, monomorphisation). Owned by `/design`, narrow-deployed to this crate.

## Purpose

These documents describe *how* the typechecker solves problems — algorithms, data structures, internal architecture, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/03-types.md`, `spec/07-traits.md` — the *language definition* (what behaviour is correct)

## What to Document

- **Inference engine**: Algorithm W implementation, unification, occurs check, substitution strategy
- **Constraint solving**: trait constraint propagation, constrained polymorphism detection
- **ADT type checking**: constructor inference, pattern exhaustiveness, type parameter instantiation
- **Monomorphisation**: specialisation collection, cross-module specialisation, cache interaction
- **Scope and environment**: scope stack design, variable resolution, module interaction
- **Design evolution**: what changed and why across sprints, and what was considered but rejected (per-sprint history lives in the docs themselves and `sprints/archive/`)

## Conventions

- One file per major subsystem (e.g., `inference.md`, `traits.md`, `monomorphisation.md`)
- Include typing rules in judgement notation where they clarify the algorithm
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none

## Document index (durable vs historical) — the triage of record

Maintained by `/design` (triaged S109, FIXME 0578). An agent designing against
this crate reads the **durable** docs; the **historical** docs are retained for
the audit trail only and each carries a top-of-file `HISTORICAL` banner — do not
treat them as current design intent. When a durable doc and a historical doc
disagree, the durable doc (and current source) wins.

**Master.** `typecheck.md` — the single source of design intent; every other doc
is subordinate.

**Durable subsystem docs** (one-per-subsystem, current):
`inference.md`, `traits.md`, `monomorphisation.md`, `adt.md`,
`ownership-inference.md`, `hkt.md`, `signature-match.md`, `auto-curry.md`,
`io-types.md`, `check-form-api.md` (the per-form pipeline API; a `// spec:` anchor
for `program/tests.rs`), `ast-annotation.md` (the AST-co-located annotation model).

**Active subordinate feature docs** (scoped elaborations of a subsystem doc, live):
`fixme-0365-field-accessor-dotted.md` (dotted field accessors → subordinate to
`adt.md`), `dotted-ctor-registration.md` (dotted `Type.Ctor` capability, S109 →
subordinate to `adt.md`), `s87-traits-decomposition.md` (the `traits/` module cut +
`monomorphise_call` phase boundaries — retained as the active decomposition
**precedent**, cited by the `program.rs` split design), `program-decomposition.md`
(the S109 `program.rs` module-cut sign-off),
`type-expr-resolver-convergence.md` (S110 FIXME 0590 — the four-mirror `TypeExpr`
resolver single-source refactor → subordinate to `inference.md` + `traits.md`),
`return-poly-dispatch-signal.md` (S110 R16/R17 — the unresolved-return-poly
dispatch signal + the typecheck→int carrier → subordinate to `traits.md` +
`monomorphisation.md`).

**Historical working docs** (`HISTORICAL`-bannered; completed/superseded, audit
trail only): `sprint50-fixes.md`, `phase-b-plan.md`, `implementation-slice-s66.md`,
`wave-3a-check-form.md`, `s76-resolution-and-enablement.md`, `step4-macro-deps.md`,
`s87-fq-walk-consolidation.md`, `dashmap-migration.md`, `stateless-tc-impl.md`.
(The last two describe now-as-built structure under the retired `TypeChecker`
name — the as-built types are `TypeCheckEnv` + `CheckState`, `traits.md §1.1`.)
