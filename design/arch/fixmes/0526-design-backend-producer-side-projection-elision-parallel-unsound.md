---
number: 0526
target: /arch  # retargeted by /sprint 2026-07-05: no /design skill exists; producer-side vs consumer-side memory-model soundness + increment-II framing is a cross-boundary /arch ruling (design/backend/ownership-codegen.md content edits remain /backend's on /arch's ruling)
filed_by: /dev   # cranelisp-backend, S102 Wave 14
filed_at: 2026-07-05
sprint_filed: 102
refers_to: design/backend/ownership-codegen.md §3.3 (Result modes and provenance — the compute_last_uses extension), §3.3 AS-BUILT box
status: open
---

# §3.3 producer-side projection elision is parallel-unsound — landed a consumer-driven narrowing

## Issue

The §3.3 design specifies **producer-side** in-frame projection elision: elide the
`vec-get` element inc unconditionally at the read whenever the ownership pass set
a `provenance` fact, then materialize/lend at every consumer, keeping the root
live across the frame via the `compute_last_uses` provenance extension; plus
`ResultMode::ProjectionOf` propagation across the function-return boundary
(callee returns an un-inc'd borrowed view, direct caller treats it as borrowed).

Implementation (S102 Wave 14) proved this model **parallel-unsound** and reverted
it. Root cause: a borrowed view that **escapes the producing function** — returned
(`get0 [v] (vec-get v 0)`), stored into a Vec/ADT, or passed to an `Owned`
position — carries no protective reference. Under lenient (parallel) eval a
sibling strand's COW/free of the root races the borrowed read. Reproduced as
**f4_sudoku same-seed non-determinism** under `MALLOC_PERTURB_` (the release
binary false-greened; the debug binary + same-seed repetition exposed the race —
`memory/feedback_verify_fix_not_symptom_absence.md`). The `compute_last_uses`
extension orders *in-frame* liveness but cannot order across the backend's
spark-frame restructuring (the FIXME-0525 lesson, one strand over): the
strict-`MonoExpr` provenance analysis cannot see that the backend relocates the
read/its consumer onto a separate strand whose join the escaping view outlives.

What landed instead (I-G1 100%, F1 rc_inc 1.54%→100%): a **consumer-driven**
elision — a direct `vec-get` projection passed DIRECTLY into a `Borrowed`
parameter collapses its inc+dec pair. This is the sole shape where the borrowed
element provably never escapes the enclosing expression and never outlives the
root's fork-join-guaranteed liveness. It captures the entire F1 machinery-tax
class but NOT: the return-boundary `ProjectionOf`/`AliasOf` propagation, the
`Let`-binding `borrowed_vars` join, or the `compute_last_uses` extension.

## Proposed resolution (for /design)

Re-frame §3.3's interprocedural half. Candidate directions:

1. **Confinement gate.** Only elide a projection the ownership pass proves
   `Confined` (never has RC ops on >1 strand). The escaping-projection race is
   exactly a Crossing edge; a Confined-gated producer-side elision may be sound.
   (Note: F1's `vec-get` is classified Crossing yet the *consumer-driven*
   elision is safe there because the borrow does not escape — so confinement is
   necessary but the escape/return boundary is the sharper discriminant.)
2. **Defer the escaping-projection cases to increment II** (uniqueness /
   mutable-borrow), where the root's mutation/liveness is statically pinned.
3. **Keep §3.3 consumer-driven** (as landed) as the increment-I terminal state;
   promote the producer-side model to the increment-II design.

The design paragraphs are retained in `ownership-codegen.md` §3.3 as the target;
the AS-BUILT box records the pivot and the reproduction. No further backend work
is owed at increment I — the I-G1 acceptance gate passes on the landed seam.

## Operational implication / Context

Byte-identical-off holds (the whole seam sits behind the moded summary check).
The typecheck-side `provenance`/`ProjectionOf` site facts are still sound and
still emitted — the backend simply consumes a strict subset of them at increment
I. No `cranelisp-types` or typecheck change is implied by this FIXME.

## §3.3 re-frame AUTHORED (S103 Phase 3, `/design`(backend))

Per the `/arch` Phase-2 direction ruling (direction 3 + gating from direction 1),
the §3.3 prose re-frame is authored in `design/backend/ownership-codegen.md`:

- The **consumer-driven** elision is recorded as the increment-I **terminal**
  state (settled, I-G1 100%, no further backend work owed at increment I) — the
  new S103 RE-FRAME box atop §3.3.
- The **producer-side / escaping-projection** model **promotes to increment II**,
  gated by the **Q4 uniqueness/confinement proof**: a projection may be lent past
  the consumer seam only when its root is proved `Confined` OR uniquely owned
  across the escape. It is coupled to the reuse-token / static-uniqueness
  machinery (§6.4) and the confinement axis (§5), and staged as the **II-B3
  deferred rider** in the new §14.2 ladder (past the close-short seam; serves no
  II-G gate — I-G1 is already 100% on the consumer-driven seam).

No `cranelisp-types` or typecheck change is implied; the site facts already
emitted are consumed as a wider subset when II-B3 lands. **Left open for `/arch`
to close** (target `/arch`) now that the backend content edit is landed.
