---
number: 0905
target: /dev (backend)
filed_by: /review (backend)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/compiler/fn_compiler/ctor_template_admission_tests.rs::assert_balanced_guarded_pair
status: open
---

# I-CT cells count `iconst.i64 1024` occurrences without pinning the guard predicate's structure or polarity

## Severity
Important

## Issue

`assert_balanced_guarded_pair` asserts the load-bearing "same predicate / no
polarity gap" half of invariant I-CT (`transitive-drop-glue.md` §4.1) by
counting occurrences of the text `iconst.i64 1024` — expecting `fields * 2`
(one per inc guard, one per dec guard). That count does not prove the inc and
dec share the same comparison, polarity, or guarded control-flow path:

- an inverted dec-side comparison (releasing bare nullary tags, skipping
  pointers) keeps the count at 2 per field while breaking I-CT exactly in the
  polarity-gap direction the assertion message claims to fence;
- a threshold constant materialized for an unrelated purpose would satisfy
  the count without either half being guarded at all.

§10's own standard: "Unit tests assert emitted call identity and control-flow
ordering, not only text presence." The other three assertions in the helper
(atomic add/sub counts, `count_release_ops`) are genuine pins; this one is
text presence standing in for structure. Principle 23 (Tests mirror module
composition — the cell must pin the scenario it names); Principle 18 (Enforce
invariants structurally) points at the stronger cure.

## Proposed resolution

Either (a) strengthen the CLIF assertion to inspect the comparison and branch
guarding each `atomic_rmw` (same comparison op, same polarity, threshold
operand, the atomic op inside the guarded block), or (b) factor the shared
guard decision into one pure production predicate both emitters consume
(`emit_rc_inc_guarded_atomicity` / `emit_rc_dec_guarded` sharing a single
guard-emission helper), unit-pinned once — the crate's established
ONE-predicate pattern (`CLAUDE.md` §"RC-emission gates that are ONE
predicate"). Option (b) makes the polarity gap unrepresentable rather than
merely tested for.

## Context

- Surfaced by the delegated Codex review of `ee324bc4` (S118); verified by
  the adjudicator against the test source.
- Does not invalidate the cells: balance counts, glue absence, and the
  concrete-heap-field boundary are real pins under the current type-keyed
  gate. The gap is confined to the predicate-identity assertion.
- Whatever lands should survive the 0903 re-land unchanged — the cells are
  documented as key-independent and must stay so.
