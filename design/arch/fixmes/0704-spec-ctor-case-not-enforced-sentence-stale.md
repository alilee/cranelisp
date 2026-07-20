---
number: 0704
target: /spec
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: spec/05-definitions.md §5.2.7 ("Constructor names are conventionally capitalized, but this is not enforced")
status: open
---

# §5.2.7 "capitalization not enforced" contradicts §5.2.2 [S113]

## Severity
Minor (spec-internal contradiction; no user question — the ruling is settled)

## Issue

`spec/05-definitions.md` §5.2.7 still says *"Constructor names are
conventionally capitalized, but this is not enforced."* That is false since the
S113 ruling and implementation: §5.2.2 [S113] states a ctor name MUST be a bare
**uppercase** symbol and that lowercase ctor names are rejected as ill-formed,
and the implementation enforces it in both arms (probe on HEAD `8b2c3e20`:
`(deftype Shape circle)` → parse error; the list-arm gate is
`build_constructor_def`'s `is_uppercase_start` check, S113 W3).

## Proposed resolution

Delete or invert the §5.2.7 sentence to match §5.2.2 (e.g. "Constructor names
MUST be capitalized (§5.2.2)"). Scribe-only; the semantics are already ruled
(2026-07-19) — no user arbitration needed for the correction itself.

## Context

Found during /review of `8b2c3e20` while verifying the deftype-ctor
trailing-form fix and the 0701 fixture disposition against §5.2's grammar.
