---
number: 0859
target: /qa
filed_by: /sprint
filed_at: 2026-07-23
sprint_filed: 117
refers_to: audits/cranelisp-primitives-s116.md §3 R-2
status: deferred
target_sprint: 118
---

# Verify primitive ownership declarations against production behavior

## Accepted recommendation

The user accepted Sprint-116 primitives-audit recommendation R-2 during Sprint
117 Phase 1.

Define production-path witnesses for every nontrivial declaration class:
Borrowed scalar-result, AliasOf, ProjectionOf, and MayAliasOf. Begin with
ordinary behavioral tests, existing compiler artifacts or CLIF assertions, and
Run/Link/REPL behavior. A false change made only in `ownership_facts.rs` must
break a witness; tests that merely restate the table do not satisfy the
recommendation.

Allocator/RC tracing, fault injection, detector modes, and diagnostic hooks are
outside Sprint 117's cyber-check boundary. If adequate verification cannot be
achieved without them, return the smallest missing seam to the user.

## Sprint 117 evidence and partial disposition

The declaration inventory now carries the ownership facts directly, and nine
ordinary production witnesses are GREEN: five CLIF witnesses and four
Run/Link/REPL value/lifetime twins. Isolated false-declaration experiments
established:

- `str-len: Borrowed → Owned` REDs the existing production CLIF polarity;
- `string-identity: AliasOf(0) → Fresh` REDs the existing return-transfer
  witness;
- `vec-set: MayAliasOf(0) → Fresh` REDs
  `r2_may_alias_summary_protects_control_flow_merged_return`, because the
  producer-side control-flow-merged return loses its non-`Fresh` protect;
- direct `vec-get` and `vec-set` CLIF is correctly invariant under declaration
  mutation because it implements inline body semantics, so those tests remain
  body guards; and
- typecheck transfer units distinguish Projection from Fresh and Alias
  provenance, and conditional MayAlias COW-link/escape provenance from
  unconditional Alias.

The attempted Projection production shapes included direct return, wrapper
return, retained-root use, return adaptation, and bounded two-function
producer/consumer compositions. `ProjectionOf(0) → Fresh` was emission-inert
in all of them: an escaping heap element is materialised as an owned reference
in either case. This invalidated the earlier proposed downstream-consumer
mutation gate; `tests/plan/s117-test-plan.md` §4 now records the observed
boundary rather than claiming a nonexistent RC distinction.

## Deferred gap

R-2 is not fully closed because there is no declaration-sensitive production
artifact witness for `vec-get: ProjectionOf(0)`. The exact missing seam is a
normal compiler artifact in which changing only the primitive declaration
from `ProjectionOf(0)` to `Fresh` changes emitted ownership behavior while the
specialised inline `vec-get` body remains truthful. No bounded Sprint-117
source shape exposed such a seam.

This gap does not justify a test-only fact override, cross-crate projection
carrier, allocator/RC tracing, fault injection, detector mode, or diagnostic
hook. It also does not justify claiming that Projection and Alias must have
different production RC after both escaping results have been materialised.

## Future resolution and user disposition

Target Sprint 118 must first survey real production consumers of projected
provenance beyond the bounded shapes attempted here. It then returns one of
two evidence-backed dispositions to the user:

1. identify a stable existing production artifact affected by
   `ProjectionOf(0) → Fresh`, add the ordinary-source witness, repeat the
   isolated mutation, and close R-2; or
2. demonstrate that materialisation intentionally erases every production RC
   distinction at the current language boundary, and ask the user whether
   typecheck transfer evidence plus direct body guards is sufficient to accept
   R-2, or whether a separately designed observable semantic requirement is
   desired.

Any proposed cross-crate carrier or new observation surface requires `/arch`
review and explicit user approval before implementation.

## /qa S119 Phase-3 disposition (2026-07-26) — DISPOSITION 2 RETURNED TO THE USER, with a recommendation

The S118 close-gate obligation ("dispositioned … or returned as disposition 2
— never silently carried") went undischarged at S118; discharged now. Record:
`tests/plan/s119-test-plan.md` §8.3.

**Disposition 2 is returned.** The S117 survey was bounded-complete and its
structural finding stands: materialisation erases every production RC
distinction for projected provenance at the current language boundary — an
escaping heap element is an owned reference under either declaration. No
S118/S119 surface changes that; the S119 Spine-1 contract rules the *release*
of non-concrete values, not projection-provenance emission. No production
consumer of the distinction exists, so no declaration-sensitive witness can
exist without manufacturing an observation surface, which this FIXME itself
rules out.

**Recommendation to the user:** accept R-2 on the existing evidence (typecheck
transfer units distinguishing Projection provenance + direct inline-body
guards + the nine S117 production witnesses), **with a named revival
trigger**: the moment projection provenance becomes emission-live —
ownership-inference increment II (uniqueness/reuse tokens), or option-2
adoption re-staging elision into `--release` under the differential lane —
the declaration-sensitive witness obligation revives automatically as a plan
row of that sprint. Second-order support: option-1 typed handles
independently narrow the declaration-table risk class representationally.

**On the user's answer:** accept ⇒ this FIXME deletes, the revival trigger
records in `tests/plan/PLAN.md`; a designed observable requirement wanted ⇒
re-target `/arch` for the seam design. Routed to the user via `/sprint` at the
Phase-3 exit gate.
