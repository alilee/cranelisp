---
number: 0529
target: /design
filed_by: /dev
filed_at: 2026-07-06
sprint_filed: 103
refers_to: design/int/session-transaction.md §10 T1 (the two coherent-stale pins' flip-note, ~lines 850–857), tests/repl_redefinition.rs::redefine_concrete_to_overloaded_caller_survives_coherent_stale
status: open
---

# The T1 full-cure flip-note over-predicts a clean recompile for the concrete→Overloaded pin — the honest outcome is the CS-3 error-blocked floor

## Issue

`design/int/session-transaction.md` §10 T1's flip-note (the paragraph naming the
two coherent-stale pins to flip) reads: under the cure "the compiled caller is
**recompiled** against the new definition (or broken+trapped with provenance), so
their `:primitives/Int 6` old-chain pin flips to the cured value". The `/qa`
Phase-5 test comment on
`redefine_concrete_to_overloaded_caller_survives_coherent_stale` sharpened this to
a concrete prediction: g(5) = 5 (the Int arm).

Landing CS-1/2/3 (this wave) shows that prediction is unachievable for the
concrete→`Overloaded` shape. The caller `(defn g [y] (f y))` is UNANNOTATED — with
`f` overloaded there is nothing to pin `y` to `Int`, so g's recompile is a genuine
"ambiguous type; add an annotation" error (identical to what `--run` would report
for the regenerated file). The T1 module-grain reload therefore **fails**, and per
CS-3 the turn degrades to the §14.4 error-blocked floor: the session survives, the
`stale:` print is kept (informational), and subsequent expressions are refused
until the user annotates/repairs `g`. It is neither "recompiled to 5" nor a
per-symbol "broken+trapped with provenance" (that path is concrete-single-sig
only) — it is the **third, correct** outcome CS-3 already specifies.

## Proposed resolution

Tighten the §10 flip-note to enumerate the third outcome explicitly: a T1
downgrade whose regenerated module is ill-typed (e.g. an unannotated caller made
ambiguous by an overloaded target) does not "recompile to a cured value" — it
takes the CS-3 §14.4 error-blocked floor. Keep the polymorphic sibling's clean
"recompiled to 5" as the illustrative success case; add the overloaded sibling as
the CS-3 illustrative failure case. The implementation and the flipped e2e pins
already encode this; only the doc prose over-predicts.

## Operational implication / Context

Not a defect — the impl matches CS-3 as designed. This is a doc-coherence
correction so a future reader does not treat "recompiles to 5" as the guaranteed
overloaded-flip outcome. The flipped test already carries the corrected
disposition inline with a pointer to this FIXME.
