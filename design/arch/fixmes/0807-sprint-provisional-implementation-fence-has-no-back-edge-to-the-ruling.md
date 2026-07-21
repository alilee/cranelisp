---
number: 0807
target: /sprint
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: sprints/METHOD.md §2.2/§3.3 (FIXME lifecycle); precedent —
  FIXME 0770 (/spec) → user ruling 2026-07-21 → spec/07-traits.md §7.1.1 [S115]
  scribed → the implementation widening never scheduled (S115 W8, this wave);
  the pattern-sibling gate just landed for coverage annotations is 0803/0804
status: open
---

# A deliberately-provisional implementation scope, fenced pending a user ruling, has no back-edge — the ruling lands in the spec and the widening is never scheduled

## Issue

S115 W4 shipped the §7.1.1 occurrence-rule guard **narrow on purpose**
(`params.is_empty() && !method_mentions_self(...)`), because the spec's prose and
its §7.1.4 worked examples disagreed on scope. That was the right call, and it
was fenced properly: a named unit cell
(`occurrence_rule_shipped_scope_accepts_annotated_param_with_concrete_return`)
pinned the *provisional* scope so a widening would have to be a deliberate
re-decision, and FIXME 0770 carried the question to `/spec` for the user.

The user ruled (option (b), 2026-07-21). `/spec` scribed it at §7.1.1 ("The
occurrence rule is broad, not a nullary corner" [S115]). 0770 was then correctly
resolved and deleted — **by its target, `/spec`, whose obligation the scribing
discharged in full.** But the ruling's *implementation* consequence had no
carrier at all: the fence cell went on passing (it asserted the provisional
polarity, so it could only pass), no FIXME targeted `/dev`, and no plan row
existed. The gap surfaced only because `/docs` re-probed the behaviour live in
Phase 6a and found `(deftrait Conv (cvt [:String s] Int))` still accepted, the
fault leaking to a misleading call-site `no impl of trait user/Conv for type
primitives/String` (FIXME 0805). Between the ruling and that probe, the compiler
was knowingly diverging from a settled spec MUST with nothing in the system
saying so.

The structural point: **a FIXME's target is the skill that answers the question,
not the skill that must change because of the answer.** When the answer is a
user ruling on semantics, the answering skill is always `/spec` — so the
implementation half of every such ruling is, by construction, un-carried. The
provisional fence cell is a *record* of the divergence, but it is not an
*instrument*: it is green while the divergence persists and reddens only when
someone independently decides to fix it. Its polarity is exactly backwards for
detection.

This is the same class the project just ruled on for coverage annotations
(0803/0804: a spec change CLEARS the coverage annotations it invalidates, and the
close gate reports cleared-and-unrestored rows). That gate covers *test
traceability* drifting under a changed spec. The identical hazard for
*implementation* deliberately parked under an unsettled spec has no gate.

## Proposed resolution

`/sprint` to decide the mechanism; two shapes seem available, and I have no
authority over either:

1. **A resolution back-edge on the FIXME itself** — a `/spec`-targeted FIXME that
   parks an implementation may carry a "on ruling, re-target" field, so
   resolving it *re-files* rather than deletes: `/spec` scribes, then hands a
   fresh `target: /dev` FIXME naming the seam and the fence cell to re-decide.
   The scribing skill knows the ruling landed; nobody else does.
2. **A register of provisional scopes** with a wave-gate scan, the way
   `design/arch/fixmes/` is scanned — an implementation that ships knowingly
   narrower/broader than the spec it implements is a tracked item until the spec
   settles and the code matches, and the sprint cannot close over an entry whose
   spec half is settled and whose code half is not.

Either way the ask is the same: **the settling of a normative question must
schedule the implementation that was waiting on it**, and the fence cell should
not be the only thing standing between a settled MUST and an unenforced one.

## Context

- The widening itself landed in S115 W8 (this wave). The fence cell was not
  deleted — it was re-pointed to the *ruled* scope with its polarity flipped
  (`occurrence_rule_rejects_annotated_param_method_with_no_self_occurrence`), so
  a future narrowing must again be a deliberate re-decision.
- Elapsed divergence here was short (one sprint) and the blast radius was zero —
  the `/testing` W5a fixture repairs had already made the corpus ready, and the
  stdlib/examples/exemplar sweep found no occurrence at all. That is luck about
  *this* ruling's shape, not evidence the mechanism is sound: a ruling that
  widened a rule the corpus actually used would have been found the same way —
  by a user-proxy probing by hand in Phase 6.
- `/sprint` disclosed this as a dispatch miss when commissioning W8, which is
  why this is filed as a method gap rather than an attribution.
