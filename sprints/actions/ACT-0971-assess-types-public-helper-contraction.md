---
id: ACT-0971
title: Assess types public helper contraction before proposing an API removal
status: open
priority: advisory
from: sprint
to: arch
filed_at: 2026-09-21
refers_to:
  - crates/cranelisp-types/src/module.rs
  - crates/cranelisp-types/src/mono_expr.rs
  - design/arch/interfaces.md
  - design/arch/concrete-boundary-type.md
---

## Candidates, not approved API changes

The S122 boundary-guide assessment identified two related public-surface
questions for the types context:

- `settle_template` and `settle_concrete` reportedly have no callers outside
  the types crate; assess whether their visibility can be narrowed.
- Direct `MonoExpr::lenient_from_expr` consumers in binary/backend reportedly
  reside in tests. Assess production reachability before proposing removal:
  the types-owned synthetic-local wrapper delegates to it and has production
  consumers, so a direct-call census alone does not prove dead code.

Recheck the callers and the standing obligations first. If contraction is
justified, present the exact API delta, consumer impact and expected baseline
change for the user's pre-implementation approval. No removal, replacement
mechanism or baseline change is authorised by this action. Keep rustdoc-only
cleanup with ACT-0966.
