---
number: 0462
target: /docs
filed_by: /docs
filed_at: 2026-06-28
sprint_filed: 95
refers_to: user/getting-started.md §"Automatic parallelism" (the "Independent IO actions run concurrently" bullet), spec/10-io.md §10.12.4.1, user/guide/parallel-collections.md
status: open
---

# IO-concurrency user surface needs the per-resource-capacity honest scope — land with the S96 web rewrite

## Issue
S95 added `spec/10-io.md §10.12.4.1` ("Resource Capacity — Token Pools"): a
resource (non-zero token) carries a platform-declared **capacity** *N*; up to *N*
effects on that token run concurrently and the (N+1)th **parks** (observable as
wall-clock latency); capacity-1 is serial-and-ordered; distinct tokens are
independent. This is **platform-author-facing only** — supplied via the Rust API
`effect_on_resource_with_capacity(token, capacity, f)`. A cranelisp program writes
**zero** concurrency primitives and does **not** choose *N* (the auto-IO model).

The current user surface for IO concurrency is one bullet in
`user/getting-started.md §"Automatic parallelism"`:

> **Independent IO actions run concurrently.** When the compiler can see that two
> effects do not depend on one another, it schedules them at the same time.

That sentence is accurate but **unscoped** — it presents IO overlap as
unconditional, with no mention that effects sharing one resource are bounded by
that resource's capacity (the canonical case: *N* queries sharing an *N*-connection
pool; the sum in flight ≤ *N*). This is the IO-axis analogue of the S94
honest-scope clause already carried on the pure-compute axis in
`user/guide/parallel-collections.md` ("a performance property with a known limit").
The IO axis currently lacks its matching honest caveat.

## Why this is deferred to S96 (not written in S95)
Per the project's FIXME-drain policy, deferral is legitimate only for a Phase-H /
effect-concurrency-track / unmet-trigger dependency. This is the **third** case:

1. **No worked example exists yet.** The web platform rewrite + the
   server-with-no-spawn demo (the concrete connection-pool case that makes capacity
   legible to a reader) is **S96** work. Writing the honest paragraph now, with no
   example to anchor it, risks the exact over-promise the task warns against —
   implying the *programmer* controls *N* when the *platform author* does.
2. **The getting-started bullet stays accurate as-is in the interim** — it states
   the overlap truth correctly; it is merely unscoped, not wrong. No user is
   misled today (the only platform shipped is `stdio`, single-resource).
3. **Cohesion.** The honest clause + worked example + the "you don't pick N; the
   platform does" framing are one coherent edit best made alongside the S96 web
   material, not split across two sprints.

## Proposed resolution (S96, with the web platform rewrite)
When the S96 web/server material lands:

1. **Scope the getting-started bullet.** Add a short honest clause: independent IO
   effects overlap, **but effects sharing one resource are bounded by that
   resource's capacity — a ceiling the platform declares, not the program** — so a
   pool of *N* admits up to *N* concurrently and further effects wait. Cross-link
   `spec/10-io.md §10.12.4.1` for the normative rule.
2. **Anchor it to the connection-pool worked example** from the server demo (the
   canonical "*N* queries, *N*-connection pool" shape).
3. **Decide placement** — a short note in getting-started vs. a dedicated
   `user/guide/` page on the auto-IO model, paralleling `parallel-collections.md`.
   Likely the latter, given the web rewrite supplies enough surface.

## Operational implication / Context
- **No cross-ref from `parallel-collections.md` to resource pools.** Deliberately
  excluded: that page is the **pure-compute** axis (rayon CPU sparks, spark budget,
  the allocator/RC contention floor). Resource capacity / token pools are the
  **IO-effect** axis (the reactor, per-resource permits) — a distinct substrate.
  Cross-linking the two would conflate independent mechanisms and confuse readers.
  The two honest-scope caveats are siblings in spirit, not in subject.
- Low urgency, no defect: §10.12.4.1 is `concurrency-runtime`-gated; the default
  build and the shipped `stdio` platform are unchanged, so no current user-facing
  behaviour contradicts the docs. This FIXME is the durable trigger so the honest
  IO-scope clause is not forgotten once S96 gives it a concrete anchor.
