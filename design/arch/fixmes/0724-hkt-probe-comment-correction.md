---
number: 0724
target: /testing
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 115
refers_to: tests/hkt_named_arm_probe.rs:1-18 (comment narrative) vs
  crates/cranelisp-typecheck/src/resolve.rs:266-288 (resolve_named errors on
  unknown name; rustdoc records the never-error arms DELETED) +
  crates/cranelisp-typecheck/src/form.rs:413 (mint-on-miss; no pre-walk)
status: open
---

# Correct the hkt_named_arm_probe comment narrative; KEEP the test (audit S114 R-1 rider, accepted at S115 Phase 1)

## Issue

`audits/cranelisp-typecheck-s114.md` §2.2a: the probe file's comment claims
the never-error `Named` arm is "MASKED by the `form.rs::check_type_expr`
pre-walk (which errors first)" — there is no pre-walk and no surviving
never-error arm; the observed reject IS the S110-landed convergence behaving
correctly (`5ed07d60`). The test itself is a valid born-green regression
fence over exactly the behaviour the convergence guarantees — it must be
KEPT; only the narrative is false. (FIXME 0590 was deleted at S115 Phase 1
against the S110 evidence.)

## Proposed resolution

Rewrite the comment to state what the test actually fences: an unknown type
name in HKT position produces a located error via the ONE converged resolver
(`TypeExprCtx`/`resolve_named`), the former mirrors and their never-error
fabrication arms having been deleted in S110. Rides the /testing S115 batch.
