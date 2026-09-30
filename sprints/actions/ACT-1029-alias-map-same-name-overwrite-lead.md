---
id: ACT-1029
title: A same-name alias binder may overwrite a live alias's root in the last-use map, so an in-place COW mutates a box that a live view still reads
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - crates/cranelisp-backend/src/heap.rs::compute_last_uses
  - crates/cranelisp-backend/src/heap.rs::register_alias
  - design/backend/ownership-codegen.md §13.3
  - design/backend/binding-scope.md
  - tests/plan/s122-evidence-delta.md
  - spec/12-runtime.md §12.3.1
---

## Observation

This lead comes from source reading: `review`(backend) finding R1
(`.local/s122-backend-combined-review-result.md`). No run has yet exercised
the mechanism.

- **Map behaviour.** `register_alias` inserts `alias → root` into a map that
  is keyed by name and never scoped. A later alias binder with the same name
  over a different root overwrites the entry.
- **Consequence.** Pre-order uses of the still-live outer binder are then
  credited to the new root. The original root's last use can move earlier,
  and an in-place COW, or the self-tail consuming claim, at that use acts on
  a box the outer binder still views.
- A non-alias rebinding leaves the entry in place. That can only delay a last
  use, which is the safe direction.
- **Predicted faces:**
  - **Tail:** `(match x [a (go … (vec-push x 1) (vec-len (match y [a a])) a)])`
    claims `x` at the push, and two loop slots share one reference.
  - **Value:** the `let` twin shows the in-place write through the outer
    alias.
- **Class:** `binder-name-underkey` (predicted), with a `uaf` face
  (predicted). This is memory-unsafe if confirmed.

## Attribution

- **Status.** Unconfirmed. The first control was not marginal; see §Probe.
- **Existing, not an S122 regression.**
  - The `let` alias edge has carried the overwrite since S103.
  - The variable-pattern match edge is new in S122. At HEAD `e4062202`, its
    base shape already faults (A-T).
- **Scope of the S122 correction.** It is narrower than a scope-correct map.
  A-T and A-V discriminate the base shape only.
- **Refuted if** the redesigned subject balances armed with the correct
  value, and its push calls the copy extern.

## Probe (user-approved, 2026-09-30)

- **T0.** The first pair's control stopped armed (`USE-AFTER-FREE`), and
  its subject never ran. So R1 is **neither confirmed nor refuted**.
  - The control's fault is not this mechanism. It is new intake
    [ACT-1030](ACT-1030-let-wrapped-tail-forward-uaf-intake.md).
  - Both halves nested the inner binder in a `let`-wrapped tail argument,
    which carries that fault. QA's pair design was not marginal.
- **Redesigned delta, settled.** The R1 cell in
  [the evidence delta](../../tests/plan/s122-evidence-delta.md#act-1029-r1-probe--t0-control-fault-and-redesigned-delta-2026-09-30)
  moves the inner same-name match into a `let` around the tail call. Its
  halves differ only in the inner binder name.
  - Each half is observed on its own.
  - The CLIF shows the push lowering in each half, which is the last-use
    decision at its own seam.
- **Class.** `binder-name-underkey` stays a prediction. The committed cell
  takes that `// defect:` line only when the discriminator confirms it.
- **Owners on confirmation.** `design`(backend) designs a scope-correct alias
  map, for example keyed by the resolved binder or restored at scope exit.
  `dev`(backend) implements it. The fix-or-carry decision is the user's.

## Completion evidence

One of these:
- the redesigned R1 cell's subject balances, and its push calls the copy
  extern, so this lead is refuted;
- a committed RED goes GREEN after the correction, with its control
  balanced.
