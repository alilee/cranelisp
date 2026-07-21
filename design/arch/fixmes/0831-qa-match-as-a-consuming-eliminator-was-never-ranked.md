---
number: 0831
target: /qa
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/plan/risks.md + tests/plan/memory-safety-coverage.md §3 — `match`
  as a CONSUMING eliminator of an owned temporary was never ranked as a risk,
  across ~15 sprints of RC work, because every risk row frames the flow by where
  a value COMES FROM (return, capture, container, loop-carry), never by what
  eliminates it
status: open
---

# Risk register: `match` was ranked as a producer of bindings, never as a consumer of the scrutinee

## The risk question (METHOD §2.2), answered

FIXME 0810 is a Blocker-class memory-corruption defect in a shape as ordinary as
`(match (f x) [(Some v) …])` — the single most common expression in any
`Option`-returning program, and ~99.6% of the exemplar's per-solve leak residue.
It was never ranked. Why:

1. **Every risk row is framed by the value's ORIGIN, not its ELIMINATION.** The
   memory-safety flow-space in `memory-safety-coverage.md` §3 and the ownership
   spine's five queries (*param borrowed? escapes frame? crosses thread? uniquely
   owned? how duplicated?*) all ask where a value came from and where it goes.
   None asks **who frees it at the point of use**. `match` is the language's only
   construct that simultaneously (a) owns a temporary, (b) hands a *projection* of
   it to an arm, and (c) must decide the release order between the two. That
   third property has no row anywhere in the register.

2. **`match` was catalogued under pattern matching, not under memory.** The
   defect classes the project tracks around `match` are exhaustiveness, arm-type
   agreement, and ctor-resolution (`resolver-mirror`, `drop-glue-underkey`). Its
   RC role appears only as a *binding* concern — "the arm binds a projection" —
   which reads as a read, not a transfer.

3. **The nearest prior sightings were both mis-scoped to their symptom.**
   FIXME 0781 (fixed W4c) was framed as "yielding nodes are not `Var` nodes" — a
   *syntactic-classification* defect. FIXME 0782 (open) was framed as "two
   release paths both fire" — a *seam-duplication* defect. Neither was framed as
   "the match/owned-temporary contract is unspecified", which is the class both
   belong to and which 0810 completes: for a scrutinee this frame owns, the seam
   currently has NO correct spelling — inline leaks it, let-bound frees it early
   (0810), and a consuming var-pattern arm frees it twice (0782).

4. **The instrument agreed with the model.** The standing RC face is a
   differential (ownership ON vs OFF). This class is toggle-independent in every
   cell measured, so the differential reports GREEN; and 0782's double-release
   does not perturb the alloc counters at all under `--run`. A risk nobody ranked
   was also a risk nothing could have surfaced accidentally.

## Requested action

A risk row (and, per `tests/CLAUDE.md` §"Coverage by definition variants", a
variant matrix) for the **eliminator/consumer** axis:

> For every construct that CONSUMES a value it owns while handing a projection
> of that value onward — `match` (ctor and var patterns), field accessors,
> `vec-get` on a temporary container, destructuring `let` if it lands — is there
> a `{scrutinee/container provenance: fresh | let-bound | borrowed param} x
> {projection escapes the construct: yes | no} x {payload: scalar | heap}`
> matrix, both polarities?

The 0810 batch fills exactly one column of that matrix and shows the row-to-row
outcomes INVERT (under a ctor pattern the let-bound spelling is the broken one;
under a var pattern the let-bound spelling is the correct one) — which is the
signature of a seam that has grown per-spelling rules instead of one derived
answer, i.e. the standing duplication class.

## Context

- `tests/match_owned_temporary_scrutinee_0810.rs` — the 14 committed cells.
- FIXME 0830 (`/qa`) — the generative-harness half: the harness's generation
  space is one eliminator axis short of emitting these shapes by itself.
- FIXME 0810 (record, `/testing`), FIXME 0782 (`/dev`), FIXME 0781 (fixed).
