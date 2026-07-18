---
number: 26
title: Record from settled state
---

# Principle 26 — Record from settled state

> **DRAFT** — authored S112 W3 (2026-07-18) under the standing recurring-class
> escalation rule (3rd instance across a wave ⇒ `/arch` assessment; instances
> B1/I1/R1, all at cranelisp-typecheck's multi-sig seam — the W2/W2.1 review
> record, `sprints/SPRINT.md`). **Pending user ratification at S112 Phase-7
> close**, per the close-only register rule (the P21/P23/P24/P25 precedent).
> Cited as DRAFT until then.

**Statement.** A resolution — a dispatch target, a mangled name, a recorded
type, any datum derived from in-flight inference state and consumed later — is
recorded only from **settled** state: state whose owning pass has finalised
it. Every resolution carrier (a span-keyed sidecar, a name map, an overload
table, a pending worklist) has an owning pass and therefore a **temporal
window**:

- a derived **value** may be recorded only at or after the settlement point of
  the inputs it was derived from;
- a resolution **request** (a pending/worklist entry) may be recorded only
  while the pass that drains it is still ahead.

A write outside the window is the defect, in either direction: a value derived
mid-pass from still-unsettled inputs (B1 — a `SigDispatch` computed mid-drain
recorded a sibling clause's `$Var` template name that the post-drain
finalisation then removed), or a request pushed after its owner has already
run (I1 — a mono-recheck self-call pushed a `pending_overload_resolution`
entry after the sole drain had been taken; nothing ever resolves it).

Two admissible shapes when a resolution is wanted before its inputs settle:

1. **Defer.** Record the *site* (span + what to derive), and derive at the
   settlement point, once, as a pure function of the finalised state — the
   `design/typecheck/monomorphisation.md` §11.3.2 mechanism: nothing
   provisional exists, so nothing can be invalidated; order-independence holds
   *by construction*.
2. **Derive on demand** after settlement — the consumer reads finalised state
   through a keyed fetch at its own, later, time (the I1 fix's shape: the
   inline monomorphic-recursion gate resolves against the instance's
   already-settled params instead of posting a request to a finished pass).

The inadmissible shape: **record provisionally, repair afterwards.** The
repair must enumerate every carrier the provisional value reached; a carrier
the repair forgets dangles silently (B1: Phase A re-pointed four carriers and
missed two), and a carrier added later is missed by construction —
order-dependence is *patched*, not eliminated (Principle 22's
published-pointer hazard in temporal form). The §11.3.2 adjudication rejected
exactly this candidate.

**Acid test — Principle 24's, applied to time instead of place.** *Does the
recorded value depend on where within the pass the record was made?* If
recording the same datum earlier or later in the drain/worklist iteration
could yield a different value, the record is premature — its correctness
depends on incidental intra-pass order, the same divergence surface P24 names
for ambient scans. Dually for requests: *is the pass that owns this carrier
guaranteed still ahead?* If not, the write is lost by construction and should
be unrepresentable or a loud seam failure (Principle 18/25), never a
silently-orphaned entry.

**Rationale.** Three instances in one sprint, one root — the S112 W2/W2.1 arc
in cranelisp-typecheck's multi-sig seam:

- **B1** (review Blocker): the self-call `SigDispatch` derived mid-drain; in a
  ≥2-hop delegation chain the selected clause's params were still `Var`, so
  the recorded dispatch named a `$Var` template the post-drain finalisation
  removes — `user/f3$Var+Var` reached codegen. Fixed by deferral: pass 1
  records **no** `SigDispatch`; `finalize_multi_sig_variant_types` derives all
  six carriers from ONE `mangle_sig` over the finalised post-drain params
  (§11.3.2).
- **I1**: the mono-recheck of a `$Var` template clause classified its inner
  self-call as external and pushed a pending entry **after** the drain had
  run — a request posted to a mailbox whose reader exited; the orphaned entry
  surfaced as a wrong-reject with an internal-mangle leak. Fixed by
  derive-on-demand: the `mono_recheck_self` inline gate (§11.3.4).
- **R1** (open known-limit): the cross-arity variant of I1 — the inline gate's
  same-instantiation guard doesn't cover a cross-arity sibling self-call, so
  the call re-defers into the taken drain and orphans (§11.3.4). R1 is the
  defect this principle names, never counter-evidence (the S110 P24
  discipline: intent first; violating code is an instance of the class).

Two of the three closed under one mechanism — the class closes by mechanism,
not instance-patching (Principle 25's lesson). And the hazard is intrinsic to
multi-pass inference, not to this seam: any pass-ordered analysis with a
settlement point — the overload drain, Phase-A finalisation, generalisation,
the ownership fixpoint, cache persist — reproduces it wherever a record is
derived early or requested late. The cache-trust class (CS-2: a persisted
resolution consumed after the state that produced it changed) is the
inter-*session* instance of the same shape, guarded at its trust boundary per
Principle 25.

**Relationship to existing principles.** Principle 24 fixes *where* a
resolution is derived (one stage, one keyed-lookup chain; downstream keyed
reads only); this principle fixes *when* it may be recorded (only from
finalised inputs — one settlement, everything downstream of it). Principle 22
gives a published pointer a retention owner in space; this gives a published
resolution a temporal window. Principles 18/25 supply the enforcement ladder:
prefer making the out-of-window write unrepresentable (the deferral removes
the premature value's representation), else assert it at its seam (a worklist
push after its drain has run is a hard invariant failure, not a lost write).

**Consequence.**

- The §11.3.2 six-carrier deferral is the mechanism template: sites deferred
  during the pass, ONE derivation at the settlement point feeding every
  carrier (Principle 7).
- **R1's fix MUST take the settled-state shape** — §11.3.4's recorded
  direction (resolve the cross-arity sibling self-call against the
  post-drain-settled overload set), never a provisional record plus repair.
- `/review` REJECT shapes: a mid-pass provisional resolution record paired
  with a post-hoc carrier repair; a pending-worklist push reachable after its
  owning drain without a hard failure.
- On ratification, a classification sweep of resolution-recording sites
  (carrier → owning pass → window; each write in-window or deferred) is a
  well-defined audit task, analogous to P24's enumeration-vs-scan sweep.
  Until then, code found writing outside a window is an instance of the
  defect class, not counter-evidence.
