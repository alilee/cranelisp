---
number: 0827
target: /design
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/typecheck/traits.md §2 "Occurrence-rule enforcement (§7.1.1,
  S115 — FIXME 0709)" vs crates/cranelisp-typecheck/src/traits/registry.rs:162–221
  (shipped W4, widened W8 `6e4b3612`)
status: open
---

# `traits.md` §2's occurrence section is still `Status: DESIGN`, and it never recorded that the W4 implementation shipped NARROWER than the design it states

## Severity

Important (design-doc staleness against shipped code — and the stale doc is the
one artefact that would have made the W4/W8 divergence visible)

## Issue

Two problems, one of them load-bearing for the sprint's own root-cause account.

**(a) Staleness.** The section is headed **"Status: DESIGN (S115 Phase 3,
`/design`(typecheck))"** and reads throughout in the future tense ("is today
accepted silently", "`/dev` settles the exact call site", "no new parsing"). The
check shipped at W4 and was widened at W8 (`6e4b3612`). It should read as the
record of what is built: the seam is
`registry::register_trait_decl`, conventional branch, per method, before the
write; the predicate is `traits/type_resolve.rs::method_mentions_self`; the HKT
exemption is by **branch return** (`register_hkt_trait` returns at :159, above
the loop), not by a flag. The section should also cite the 2026-07-21 user
ruling and spec §7.1.1 `[S115]` ("The occurrence rule is broad, not a nullary
corner") as the settled scope, superseding FIXME 0770.

**(b) The design already stated the ruled scope — and the implementation
diverged from it silently.** §2 says, and has said since Phase 3:

> Do NOT reject on "concrete return" alone; reject only on the *conjunction*
> no-param-occurrence ∧ no-self-return.

That conjunction **is** `!method_mentions_self(method)` — the W8 rule. W4
nevertheless shipped `params.is_empty() && !method_mentions_self(method)`, a
strictly narrower guard, recorded only in a code comment plus FIXME 0770. So the
divergence was not merely "a user ruling that was never dispatched": **the design
of record already specified the wide rule, and the narrowing was introduced at
implementation time without the design doc being amended to hold it.** A W4-time
comparison of §2 against `registry.rs` would have shown it.

That matters for how the lesson is generalised. `/sprint` has recorded the
implementation-side rule "a provisional implementation scope carries a back-edge
to its ruling" (`87bb383a`, FIXME 0807 actioned). This case adds a second edge
the back-edge rule does not cover: a provisional scope that departs from the
**design doc** must be recorded **in the design doc**, not only in a code comment
and a FIXME — otherwise the doc silently certifies behaviour the code does not
have, and the triad's own drift check (`/review` step 2: read
`design/{crate}/{crate}.md` as the standard) is reading a standard the code was
already known to miss.

**(c) Minor.** The closing "**Unit tier (`/dev`, METHOD §2.2)**" paragraph
enumerates three cells; seven ship
(`registry/tests.rs::occurrence_rule_*`), including the nested-occurrence
predicate cell and the two arity-column rejects. Either update the enumeration
or state the intent and stop enumerating (an enumeration that drifts is the
weaker of the two).

## Requested

1. Retitle to a shipped-state record (status, seam, predicate, HKT-by-branch-
   return), citing spec §7.1.1 `[S115]` + the 2026-07-21 ruling.
2. Add a short paragraph stating (b) explicitly, so the next provisional
   narrowing is recorded where the standard lives.
3. Fix or drop the unit-tier enumeration.

No code change is implied; the shipped behaviour matches what §2 already
specified.
