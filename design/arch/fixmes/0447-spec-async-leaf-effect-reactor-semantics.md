---
number: 0447
target: /spec
filed_by: /arch
filed_at: 2026-06-27
sprint_filed: 93
refers_to: spec/10-io.md §10.12 (§10.12.4, §10.12.6), spec/12-runtime.md §12 (§12.4.3, §12.5), spec/04-expressions.md §4.12, design/arch/effect-concurrency.md §5/§6/§8/§9/§10/§11/§14/§15, design/arch/platform-interface.md §6.8
status: deferred
---

# Spec cascade for the async-leaf effect + host-reactor concurrency model (effect-concurrency slice 2)

## Disposition (S93 /spec — slice-2 half actioned, substance deferred)

`/spec` evaluated the slice-2 question — **what, if anything, is user-visible in the
language spec at slice 2?** — against the ratified model (`effect-concurrency.md` §8/§11/§14)
and the landed-dormant ABI-v7 contracts. **Ruling: slice 2 surfaces nothing new
user-visible.** The async-leaf effect + host reactor are an execution *substrate* that
changes how extracted-concurrent work runs, never which work is eligible, with results
observationally identical to sequential per §12.4.3. The per-effect concurrency descriptor,
and the **strand-id / observability event stream, are dev/tooling-facing only — NOT a
user-invokable language feature** (the model itself pins the sinks as "minimal and
dev-facing, REPL-visible like `trace`", feature-gated/byte-identical-when-off). So the
strand-id earns **no §4.12 / §12 user-facing change**; its visibility ruling is recorded
instead as the non-normative §10.12.6 item 2.

**Landed this sprint (slice-2 minimal hook):**
- `spec/10-io.md §10.12.6` (new, **informative**) — records that the concurrency model's
  execution substrate exists and is sliced; pins the three facts (substrate changes
  execution not extraction → observationally identical to sequential; substrate +
  descriptor + strand-id are implementation/tooling-facing not language features;
  the explicit control surface is committed-but-not-yet-present and will be specified
  at the slice it surfaces). No new user surface authored.
- `spec/10-io.md §10.12.4` — the **within-token source-ordering** invariant (the §8
  `SerialGroup` carry-through) is now stated normatively, so the slice-2 semaphore
  lowering cannot silently weaken an already-observable guarantee (a behaviour-preservation
  pin for existing behaviour, not new surface).

**Deferred to the slice in which each surfaces** (the substantive §12 cascade — these
introduce genuinely user-visible semantics and must be specced *with* their behavioural
delivery, not against dormant contracts):
- **Launch-and-continue (un-joined effect) semantics + supervisor policy** → the
  build-step-4 slice (`effect-concurrency.md` §14: launch-and-continue + supervisor,
  co-landed). Owes a §12 supervisor-behaviour note + the §12.4.3 / §12.5 admission of an
  un-joined strand (TCO + observational-equivalence interaction).
- **The control-combinator layer** (`race` / `select` + structured cancellation;
  `timeout` derived) → the build-step-6 combinator slice (`effect-concurrency.md` §9/§14).
  Owes a §12 home for their typing + semantics as in-language `IO`-constructing functions.

This FIXME stays **open-as-deferred** (target `/spec`) as the durable cascade record;
`/sprint` re-triggers it when build-step-4 / build-step-6 behavioural delivery lands.

---

## Original filing (/arch, S93)

## Issue

Sprint 93 opened **slice 2** of the effect-concurrency track and landed its
cross-crate **layout contracts** (gated, dormant):

- `cranelisp_types::{ConcurrencyDescriptor, Poll, PollFn}` — the per-effect
  concurrency descriptor generalizing `SchedulingClass` (token + cardinality +
  inert-until-slice-4 global_budget + blocking), and the poll-ABI primitives;
- `cranelisp_platform::{HostCtx, Waker, WakerVTable, PollFn, ConcurrentPlatformFn}` —
  the host-reactor C-ABI (the A2 async-leaf model) + the v7 poll-shape manifest
  entry; `ABI_VERSION` bumped 6→7;
- `cranelisp_intrinsics::{StrandId, StrandEvent}` — the strand-identity
  correlation newtype + the (slice-2-kinds-only) observability event stream.

The **architecture** of this model is ratified in `design/arch/effect-concurrency.md`
and cascaded into `platform-interface.md` §6.8 + `bounded-contexts.md` §3/§5/§6.
The **language specification** has not yet been updated to match. Per the
manifestation-site discipline (`effect-concurrency.md` §15), the spec cascade is
`/spec`-owned; `/arch` files this FIXME and does **not** author spec text.

The spec sections that need to evolve as the model moves from contract to
behaviour:

1. **spec/10-io.md §10.12 (Automatic IO Scheduling)** — the scheduling-class
   trichotomy (`Sequential`/`Commutative`/`ResourceSerial`, §10.12.4) generalizes
   to the **concurrency descriptor**: token (conflict domain), **cardinality**
   (pool size = safe parallelism — the new bounded-pool expressiveness, not just
   serial-per-token), global budget (backpressure — reserved/inert), and the
   **blocking?** pool-routing bit. The descriptor is the platform's whole
   concurrency contract; it stays a **trust boundary** (the compiler does not
   verify a `Commutative`/cardinality claim, exactly as today). The async substrate
   does not change *extraction* (the §10.12.1 dataflow-independence + §10.12.4
   token analysis stand verbatim) — it changes *execution*. The **within-token
   source-ordering** invariant (`SerialGroup`) must be stated to survive the
   semaphore lowering (a bare permit gives exclusion but not order).

2. **spec/10-io.md §10.12 + spec/12-runtime.md §12.5 — launch-and-continue
   semantics.** An effect whose result is discarded and whose tokens do not
   conflict with the continuation may be **launched and not joined** (the
   un-`spawn`'d server fan-out, §4). The TCO interaction (§12.5) and the
   observational-equivalence guarantee (§12.4.3) need to admit this.

3. **spec/12-runtime.md §12 — supervisor model + the eventual combinator layer.**
   Launch-and-continue creates an un-joined strand; a fire-and-forget handler that
   panics has no join point. The **supervisor default** (per-effect-kind: 500 + log
   + drop-that-request — NOT a silent strand, NOT a whole-server abort, §10) is a
   scheduler/platform-declared policy that stays out of the pure language but is an
   observable runtime behaviour the spec should pin. The **fork-join error-slot
   ferry** across §12.4.3 joins (worker-side capture → join-side first-error
   re-raise) is the substrate; §12.4.3 should gain the propagation sentence (the
   `Par` "first error" non-determinism caveat, §10, is named not papered over).
   The **control combinator layer** (`race`/`select` + structured cancellation;
   `timeout` derived, §9) is in-language typed functions constructing
   trampoline-interpreted IO-ADT nodes (the `Par`-node mechanism class) — NOT
   special forms, NOT platform effects. When delivered, their typing + semantics
   need a §12 home.

4. **spec/04-expressions.md §4.12 / spec/12-runtime.md §12 — strand-id /
   observable-event surface, ONLY IF user-visible.** The observability event stream
   (`StrandEvent`, strand-correlated by `StrandId`, the `turn`-id successor) is, in
   slice 2, a **dev-facing / REPL-visible** sink (sibling to `trace` / `io_trace`),
   feature-gated and byte-identical-when-off. **If** the strand-id or the
   observable-event surface becomes a **user-visible language feature** (a queryable
   correlation id, an in-language event handler), it needs a §4.12 / §12 note. If it
   stays dev-facing only (the slice-2 intent), no user-facing spec change is owed —
   flag this conditionally so `/spec` rules on visibility rather than assuming it.

## Proposed resolution

`/spec` evaluates and authors the §10.12 / §12 (and conditionally §4.12) changes
above, sequenced with the slice-2 *behavioural* delivery (these are
behaviour-pinning edits — they should land with or just behind the reactor
implementation, not against the dormant contracts alone). The landed interface
types (named above) are the concrete vocabulary the spec text can reference for
the descriptor fields, the poll/reactor shape, and the strand-correlation id. The
spec §12.1 "every value is one machine word" relaxation is a *separate* cascade
(FIXME 0373) and is not in scope here.

## Operational implication / Context

- **No defect, no failing test** — this is a spec-cascade change request for a
  ratified architecture whose contracts have landed, the correct use of a
  `target: /spec` FIXME (per `memory/feedback_no_fixme_with_failing_test.md`).
- The normative architecture is `design/arch/effect-concurrency.md`; the ABI
  cascade is `platform-interface.md` §6.8; the per-surface manifestation is
  `bounded-contexts.md` §3/§5/§6. This FIXME is the spec half of the §15
  manifestation map.
- Trigger to action: slice-2 (and successor-slice) behavioural delivery. Filed now
  (not deferred) because the contracts are landed and the spec is the one
  manifestation site `/arch` cannot author — leaving it un-filed would lose the
  cascade record at exactly the surface that needs the cross-skill handoff.
