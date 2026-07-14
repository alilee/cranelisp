---
number: 0594
target: /design
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: design/typecheck/inference.md (no rigid/skolem section) vs crates/cranelisp-typecheck/CLAUDE.md §Rigid written type variables
status: open
---

# design/typecheck/ has no record of the rigid written-type-var model

## Severity
Important (design-doc staleness against shipped code — the standard Important
example).

## Issue

W6.2 (`b2bfb760`) added a genuine inference-model extension: rigid skolems,
an asymmetric unification seam (`unify_with_rigid`/`unify_var`), a
three-field transient state group on `CheckState` (`rigid_vars`,
`written_var_scope`, `suppress_rigid_annotations`), and Pass-1→Pass-2 scope
threading (`defn_var_scopes`). `grep -l rigid design/typecheck/*.md` → zero
hits: the model exists only in the crate `CLAUDE.md` (correct as the code's
voice) and rustdoc. `design/typecheck/inference.md` — the `/design`-owned
statement of what the inference engine IS — does not know written vars can be
rigid, which unify seam enforces the asymmetry, or why rigidity is transient
inference state (never serialized, no cranelisp-types change).

## Proposed resolution

`/design` (typecheck) adds a rigid-written-var section to inference.md (or a
subordinate doc): the MUST-1..4/SCOPE-5 contract mapping, the
one-seam/body-scoped/threaded-scope triad, the suppression flag's intent, and
the FV-15-vs-SCOPE-5 lambda tension (see 0592) as an open design note.
Natural to fold into the S110 0590 resolver-convergence design round.

## Context

Filed by `/review` on b2bfb760 per workflow step 9 (design-doc completeness
for a modified major subsystem).
