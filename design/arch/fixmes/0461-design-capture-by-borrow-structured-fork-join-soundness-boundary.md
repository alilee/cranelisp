---
number: 0461
target: /design
filed_by: /arch
filed_at: 2026-07-02
sprint_filed: 99
refers_to: design/backend/ring2-rc.md §5.5 (borrowed variables), design/backend/lenient-eval.md §2.5/§4.4 (apply-arg spark emission), design/arch/effect-concurrency.md §3.1 (arch scope authority)
status: open
---

# Pin the capture-by-borrow-across-structured-fork-join soundness boundary (Wave-0-gated)

## Issue

Sprint 99 proposes **capture-by-borrow across structured fork-join** as the in-track
cure for atomic-RC cache-line bouncing (contention term (b)): a rayon spark's capture of
an enclosing-scope binding is a **borrow**, not a retain, because structured join proves
the parent frame outlives every spark — eliding the per-copy atomic-RC inc/dec on shared
parent cells *without* Phase-H non-atomic RC.

This is a **candidate gated on the Wave-0 measurement**, not a commitment. But its
soundness boundary must be pinned *before* any `/dev` implementation, because it is a
"skip the inc" optimisation of exactly the kind that produced S98 bug #2 (FIXME 0494:
`find_var_type_in_expr` starved a required consuming-inc → heap corruption). A wrong
borrow/retain classification is a use-after-free.

## Arch soundness boundary (the ruling `/design`/backend implements within)

The mechanism is a **generalisation of the existing `borrowed_vars` discipline**
(`ring2-rc.md` §5.5) to a new binding-introduction site (spark-capture instead of
match-arm field binding). It is NOT a new RC discipline. Three conditions bound it:

1. **Structural-join gate (load-bearing).** Borrow-elision is admissible **only** for a
   spark that is structurally joined within the capturing frame's dynamic extent — the
   rayon fork-join / `Par` / apply-arg-create-gate path where the expression does not
   return until every branch joins (spec §12.4.3). It MUST NOT apply to a **detached
   launch** (`LaunchContinue`, §8.1) — a fire-and-forget effect has no join inside the
   parent's extent, so its captures MUST retain. The `Par`-vs-`LaunchContinue` grouping
   discriminator (effect-concurrency.md §, the joined/detached decision) already carries
   this signal; the gate reads it, it is not a new analysis.

2. **Coarse only — no escape analysis (the Principle-8 line).** The *only* retain is on
   the spark's **return value**, and it MUST flow through the **already-audited**
   machinery: the consuming convention (Decision 24) at the join plus the §5.6
   capture-return-inc rule. There is **no per-capture escape decision** — every capture
   of a joined spark borrows; the return-value path is the single escape and it reuses
   the path S98 just hardened (FIXME 0497). Any classification that requires value-flow
   analysis to prove a capture does-not-escape is **Phase-H escape analysis** and is OUT
   OF SCOPE. The clean interim line: *structural join ⇒ borrow; anything needing
   non-escape analysis ⇒ Phase H.*

3. **Read-only borrow (no COW hazard).** Cranelisp values are immutable; the spark reads
   the borrowed cell, never mutates through it — so §5.5's Vec-COW-mutate-in-place hazard
   (the reason §5.5 gates last-use on `borrowed_vars`) does not arise here. The borrow is
   rc-invisible, which *preserves* owner-side rc reasoning (including the parent's COW
   last-use accounting) rather than perturbing it.

## Operational implication / Context

- **Contingent on Wave-0 funding.** If Wave 0's decision table lands on "(b) atomic-RC
  bouncing dominant", this cure is funded and `/design`/backend pins the contract into
  `ring2-rc.md` §5.5 (the borrowed-Var generalisation) + `lenient-eval.md` §4.4 (the
  apply-arg emission that skips the capture inc / return-path retain) within this
  boundary. If Wave 0 refutes (contention dominant even at saturation), this defers with
  the rest of the mechanism waves — but the boundary above stands as the record.
- **Survives Phase H.** The borrowed/owned classification is permanent in the RC model;
  Phase H's escape/thread-locality analysis feeds a *sharper* signal into the same
  classification (widening the profitably-parallel set), exactly as §3.1 frames the
  contention-aware gate as shaped-to-be-subsumed.
- Arch scope authority: `design/arch/effect-concurrency.md` §3.1 (updated S99 to name
  this candidate). Complements FIXME 0459 (the floor-scope doc alignment).
</content>
</invoke>
