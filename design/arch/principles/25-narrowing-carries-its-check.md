---
number: 25
title: Narrowing carries its check
---

# Principle 25 — Narrowing carries its check

> Authored S111 as the candidate principle of the memory-safety assessment
> (`design/arch/safety-invariants.md` §5; motivating context: the S111
> memory-safety ledger — every defect found incidentally, none structurally
> prevented). **RATIFIED at S111 Phase-7 close (user-approved 2026-07-18) as a
> SINGLE principle** — the split alternative (differential-checkability vs
> assert-at-seam as two principles) was offered and declined; the three parts
> are one idea: an elision is measured against its conservative reference.
> Per the close-only register rule (the P21/P23/P24 precedent).

**Statement.** Narrowing carries its check: a safety elision is defined
against, and checkable against, its conservative fallback.

1. **Reference semantics (conservative-at-⊤).** Wherever a static judgment
   licenses eliding a safety operation (an RC protect/inc, an atomic op, a
   distinct glue symbol, a bounds or validity check), the conservative
   behavior at the monotone ⊤ — performing the operation unconditionally — is
   the *reference semantics*. The optimized artifact is correct **by
   definition** iff observationally equivalent (behavior + heap balance) to
   the conservative one. An elision whose conservative fallback is not
   reachable has nothing to be checked against and is architecturally
   inadmissible.

2. **Every narrowing is a deliberate, checked act.** Widening is free
   (monotone soundness, `design/typecheck/ownership-inference.md` §2.1);
   narrowing is never free. Each narrowing names its **justification** (a
   truthful, reachable leaf fact; an enumerated monotone rule of the
   analysis; a structural witness) and its **check** at the strongest
   applicable tier of the assertion ladder
   (`design/arch/safety-invariants.md` §2): unconstructable representation →
   by-construction witness → seam assertion (always-on `assert!` for
   in-process breach; diagnosed error at trust boundaries) → standing
   differential equivalence against the conservative fallback. Green example
   suites and adversarial review are **discovery, not checks** — they find
   instances; they never close a class.

3. **A foundational safety invariant is asserted at its seam, not merely
   tested.** An invariant the safety argument relies on (register:
   `design/arch/safety-invariants.md` §4) either has no representation for
   its violation or is asserted where it could break, so a violation names
   its seam the moment it happens. A register row at `example-tested` or
   `unasserted` status is an open item against `/arch`.

**Relationship to existing principles.** This is the **enforcement arm of
monotone soundness**: `ownership-inference.md` §2.1 makes the conservative
point permanently safe; P25 makes it the reference every departure is
measured against. It is Principle 18's genus applied to the
*dynamic-judgment* case (where no dep-ban or visibility rule can bite),
Principle 20's producer discipline extended from data shape to analysis
claims, and the public-API discipline's "every `pub` is a deliberate act"
mirrored onto elisions.

**Motivating context (S111).** The sprint's memory-safety ledger — the 0641
false-`Fresh` family, the 0633/0640 glue-keying collisions, the CS-4
wrong-accepts, 0604's ~320-run unlocatable phantom write — was found entirely
by adversarial review and incident; the two fixes that closed their classes
did so by assertion mechanism (CS-2's always-on seam asserts + diagnosed
`CacheStale` at the cache trust boundary; CS-1.2's decoder witness with the
round-trip test as the injectivity verification), and the instance-patches
each needed an adversarial follow-up to find the next layer. The mechanism,
not the instance, closes a class.

**Consequence.** The foundational-invariant register
(`design/arch/safety-invariants.md` §4, R1–R13) is the maintained ledger of
this principle's obligations: `/arch` re-audits it at every Phase-2
architecture review, and a new safety-eliding surface (a new analysis, mangle
family, persisted carrier, or trust boundary) adds its row **in the
change-set that introduces it** — arriving unregistered is the defect. The
principle is the binding frame for the S112 memory-safety-soundness
mechanism: the mechanism builds to it (`safety-invariants.md` §3 + §6
cascade), never the reverse.
