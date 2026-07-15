---
number: 24
title: Resolve once
---

# Principle 24 — Resolve once

> Authored S110 Phase 3 (motivating context: FIXME 0583, the backend name
> resolver — the "two resolvers, one name" mirror class that recurred 3× in
> S109; user directive S109 P5). **Ratification at S110 Phase-7 close** per the
> close-only register rule (the P21/P23 precedent).

**Statement.** A semantic identity — a name, a type, a member, a dispatch
target — is derived at exactly ONE pipeline stage and crosses every stage
boundary as a resolved, fully-qualified VALUE (`FQSymbol`, `FQTypeName`, a
storage key). Downstream stages perform keyed reads against that value and
hard-fail on a miss (Principle 18); they never re-derive the identity from the
written name, and they never carry a second copy of the derivation rules.

**Rationale.** A re-derivation downstream is a second resolver, and two
resolvers for one name WILL diverge — not hypothetically but as a recurring
defect class: the backend's `resolve_driven` global scan re-resolving names
typecheck had already resolved produced the S109 one-hop-vs-multi-hop `unknown
constructor` cascade, the silent nullary-ctor-as-closure wrong-value split,
and the DC-11 scrutinee-directed wrong-tag RUN-TO-RUN NONDETERMINISM (3
instances, one root — FIXME 0583). The same shape recurs within a stage:
typecheck's four written-type-var resolver mirrors each minting on their own
(0590), the per-position value-mint whitelist re-deciding "is this a value
position" at each site (0585), and the twice-derived ADT-entry construction
(bootstrap ≡ adt.rs, audit R-2) where one keying change had to be hand-applied
to both copies. Principle 7 states single-source; this principle binds the
STAGE question P7 leaves open — the source is the stage where the identity is
first derived, and everything after it is a consumer. Re-derivation is not
merely duplication: the downstream copy runs in a different context (different
scope, different precedence inputs, different iteration order), so its
divergence is silent and often nondeterministic.

**Consequence.** Resolution results are recorded where resolution happens (the
producing stage's chokepoint) and transported as data — on the AST/mono node
or a span-keyed sidecar, persisted with the entry when the consumer can run
from cache. The consumer's read is a direct keyed fetch: no precedence walk,
no import-chain re-follow, no fallback scan; a missing key is a hard, located
error, never a re-derivation (a keyed-read-else-re-resolve hybrid is the
Principle-8 half-measure and is a review REJECT). Where several sites inside
one stage need the same derivation, it is one function with thin callers, and
the carrier parameter is REQUIRED so a new site cannot forget it
(Principle 18's unforgettable-parameter form). Instances unified under this
principle: 0583 (backend keyed-lookup consumer — the typecheck→backend seam;
`design/arch/backend-keyed-consumer.md`), the S109 §10/DC-11 pattern-position
cure (retrospectively its first application), 0590 (one written-type-var
resolver), 0585 (one value-position enumeration for mint and die), R-2 (one
ADT-entry derivation, `cranelisp_types::build_adt_entries`). The backend's
end-state under this principle is a PURE keyed-lookup consumer: zero name
resolution, zero bare-type-name resolution (BC §3 invariant 10).
