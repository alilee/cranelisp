---
id: ACT-1080
title: A return-annotation mismatch reports the body's type as expected and the annotation as actual
status: open
priority: advisory
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - repl/spec/05-error-presentation.md
  - tests/repl_negative.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

Reported by `dev`(frontend). Re-run by `qa` at the REPL on the debug build
of `7888c515`, 2026-11-18, no prelude.

| Input | Diagnostic |
|---|---|
| `(defn f [] :primitives/Int 3.5)` | `type mismatch: expected primitives/Float, got primitives/Int` |
| `(defn h [] :primitives/Float 3)` | `type mismatch: expected primitives/Int, got primitives/Float` |
| Control: `(defn g [:primitives/Int x] x)` then `(g 3.5)` | `type mismatch: expected primitives/Int, got primitives/Float` |
| Control: `(primitives/add-i64 1 2.5)` | `type mismatch: expected primitives/Int, got primitives/Float` |

Both subjects read the same on the release build of 2026-11-18 00:11 (the
W2 tree), so the wording predates W3. Earlier trees were not run.

## Classification: a defect, low harm

- **Requirement.** REPL §5.3 requires a type error to name the expected type
  and the actual (inferred) type. The annotation states what is expected;
  the body's type is the inferred one.
- **Face.** The two types are right and their roles are exchanged. The
  program is refused, as it must be, at the right location.
- **Class:** `diagnostic-role-swap`.

## Attribution

- **Mechanism: a hypothesis.** The return annotation and the body's type
  reach unification in the opposite order to an argument and its parameter.
  Not observed at its seam.
- **Owner:** typecheck, provisionally.
- **Refuted if** the controls also read reversed, or a subject reads
  correctly.
- **Why coverage missed it.** The cells under REPL §5 assert that both type
  names appear (`type_error_names_expected_type_fully_qualified`,
  `type_error_names_actual_type_fully_qualified`), on argument mismatches.
  None asserts which role each name takes, and none uses a return
  annotation.

## Evidence allocation

`test`, in `tests/repl_negative.rs`, `// spec: repl/spec/05-error-presentation.md §5.3`,
`// defect: class=diagnostic-role-swap locus=cranelisp-typecheck return-annotation unification found=S124 owner=/dev`:

- **REPRO-1080.** Both subjects above: the text after `expected` names the
  annotation's type and the text after `got` names the body's. The
  argument-mismatch control keeps its roles. REPL and `--run`.
- Expected on arrival: both subjects RED on the exchanged roles; the
  control green.

`dev`(typecheck) owes one module row at the seam it finds.

## Disposition

Correct or carry is the user's decision
([METHOD §2.4](../METHOD.md#24-deferral)). It ends no program and refuses
none it should accept. `qa` retains this intake.

## Completion evidence

REPRO-1080's subjects fail on the roles, then pass; the control passes
throughout.
