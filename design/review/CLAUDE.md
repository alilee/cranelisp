# design/review/

Review infrastructure for the Cranelisp reimplementation. Owned and maintained by the `/review` skill.

## Purpose

This directory contains review checklists, ring-completion reports, and code quality standards that the `/review` skill applies when evaluating code produced by compiler skills. The checklists are derived from:

1. **`src/CLAUDE.md`** -- cross-cutting source conventions for all compiler skills
2. **`design/arch/CLAUDE.md`** -- architectural principles and string newtype rules
3. **`sketch/audits/*.md`** -- 59 structural findings (15 HIGH, 23 MEDIUM, 21 LOW) from the prototype audit

The prototype's structural debts are the primary input. Every HIGH finding represents a pattern that must NOT be reintroduced. The review process exists to catch these patterns early -- before they accumulate into the same complexity that made the prototype unmaintainable.

## Files

| File | Purpose |
|---|---|
| `CLAUDE.md` | This file. Ownership, directory description, review workflow. |
| `checklist.md` | General review checklist applicable to ALL rings. |
| `ring0-checklist.md` | Ring 0 specific review criteria. |
| `ring0-report.md` | Ring 0 completion report -- findings, quality assessment, interface cleanliness. |
| `ring1-checklist.md` | Ring 1 specific review criteria (heap layout, RC correctness, string opacity, ADT codegen, closures, naming). |
| `naming-convention-review.md` | Cross-skill naming convention review (`cranelisp_` prefix removal). |
| `sprint2-wave2-review.md` | Sprint 2 Wave 2 per-crate code review -- findings, checklist walkthrough, design doc assessment. |
| `ring1-report.md` | Ring 1 completion report -- **PASS**. 779 tests, 0 failures, all review findings resolved, no blocking usability findings. |

Future files (created at ring completion):

| File | Purpose |
|---|---|
| `ring2-checklist.md` | Ring 2 specific review criteria (traits, modules, constrained poly, GOT cross-module) |
| `ring2-report.md` | Ring 2 completion report |
| `ringN-*.md` | Pattern continues per ring |

## Review Workflow

### When Review Happens

1. **After significant work units**: A compiler skill completes a major subsystem (e.g., `/typecheck` finishes the unification module). The skill invokes `/review` for feedback.
2. **At ring boundaries**: Before a ring is declared complete, `/review` performs a full ring review against the ring-specific checklist and produces a completion report.
3. **On request**: Any skill can invoke `/review` for targeted feedback on a specific concern.

### Review Session Steps

1. Read the relevant ring checklist (e.g., `ring0-checklist.md`).
2. Read the relevant audit file(s) for the modules being reviewed.
3. Check the general `checklist.md` for cross-cutting concerns.
4. Report findings to the skill that owns the code.
5. Escalate architectural concerns to `/arch`.
6. Record ring-level observations for the ring completion report.

### Authority Model

`/review` has **advisory authority** -- findings are recommendations, not mandates. Skills decide whether to act immediately or defer. However:

- At ring completion gates, outstanding HIGH review findings must be explicitly acknowledged (accepted or deferred with rationale) before the gate passes.
- `/review` can escalate to `/arch` if a finding represents an architectural boundary violation.
- `/review` can file usability findings to `/qa`'s usability register if a review reveals user-facing quality issues.

## Deriving Checklists

Each ring checklist is derived from three sources:

1. **Source conventions** (`src/CLAUDE.md`) -- the rules every skill agreed to follow.
2. **Audit findings** -- the specific patterns we learned NOT to do from the prototype. Each ring exercises different subsystems, so each ring's checklist highlights the audit findings relevant to that ring's scope.
3. **Ring-specific constraints** -- properties unique to that ring (e.g., Ring 0 has no heap allocation; Ring 1 introduces RC; Ring 2 introduces traits and modules).

The general `checklist.md` covers items that apply regardless of ring.

## Cross-References

- `src/CLAUDE.md` -- source conventions (error handling, code structure, naming, scope management)
- `design/arch/CLAUDE.md` -- architectural principles, string newtypes, crate DAG
- `design/arch/interfaces.md` -- boundary type definitions
- `design/arch/roadmap.md` -- ring acceptance criteria
- `sketch/audits/typechecker.md` -- typechecker structural debts (7 HIGH, 7 MED, 7 LOW)
- `sketch/audits/codegen.md` -- codegen structural debts (5 HIGH, 7 MED, 5 LOW)
- `sketch/audits/module.md` -- module system structural debts (3 HIGH, 6 MED, 5 LOW)
- `sketch/audits/cache.md` -- cache structural debts (3 HIGH, 7 MED, 5 LOW)
- `tests/plan/strategy.md` -- test strategy and quality criteria
- `tests/plan/usability.md` -- usability register for user-facing findings
