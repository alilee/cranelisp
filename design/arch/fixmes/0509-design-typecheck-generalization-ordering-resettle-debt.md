---
number: 0509
target: /design (cranelisp-typecheck)
filed_by: /sprint
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-typecheck/src/program.rs:1714 (resettle_polymorphic_schemes), :1004 (check_form_body); design/typecheck/ (crate design doc)
status: open
---

# `resettle_polymorphic_schemes` compensates for a generalization-ordering bug rather than curing it — record the debt + the reverse-order gap

## Issue (Wave-8a review, Q5 + finding 2d)

CS-488c fixes 0488(c) (fold-bodied scheme over-generalization) with `resettle_polymorphic_schemes`, which re-runs the existing idempotent generalization eagerly at each form boundary. The review confirmed it SOUND (monotone toward more-tied; no over-tie shape exists) and APPROVED it as the right shape for the sprint's guard set — but it compensates for the true root cause rather than curing it:

- **Root cause**: the 0344 generalize-writeback fires at the end of a fn's own body check, before its forward-referenced helper's body has tied the shared vars.
- **Root-cause cures** (each O(n), complete for all orderings): (a) topo-order the per-form generalization so a fn generalizes only after its forward callees' bodies run; or (b) defer the 0344 writeback entirely to finalize.
- **Chosen fix cost**: O(forms × defns) — worst case O(n²) `generalize`+`apply_subst` for an all-polymorphic module (Principle 6 — complexity budget).
- **Coverage gap (2d)**: the eager re-settle only helps when the tie-completing helper is body-checked BEFORE the consuming sibling's form. **Reverse definition order** (consumer defined first, tie-completing helper last) still under-ties — the SAME 0488(c) under-tie symptom, merely uncovered. Not a regression, not an over-tie; a known boundary with no repro today.

## Proposed resolution

A `/design(typecheck)` note in the crate design doc capturing: (i) that generalization ordering is now handled by eager re-settle rather than a principled topo-order, (ii) the O(n²) cost, (iii) the reverse-order under-tie gap — so a future pass knows the seam and can decide whether to promote to the O(n) topo-order/deferred-writeback cure. Optionally request a `/qa` boundary test pinning the reverse-order shape as a known limitation (so it is a tested boundary, not a latent surprise).

## Operational implication

Non-blocking for Wave 8b (same-crate pass5 ladder). A documentation-sufficient debt record + optional boundary test; the eager fix ships as-is this sprint. Full evidence: `sprints/SPRINT.md` §Notes Wave-8a review entry.
