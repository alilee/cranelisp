---
id: ACT-0950
title: Rule whether design/, spec/, audits/ and user/ become citation roots — the checker validates doc→source citations only, and ~214 doc→doc citations are stale today
status: open
priority: advisory
from: qa
to: qa
sprint: 120
filed_at: 2026-08-30
refers_to:
  - scripts/verify-citations.py
  - tests/plan/s120-evidence-delta.md
---

## Request

`SOURCE_ROOTS` in `scripts/verify-citations.py` names source trees only, so a
citation from one document to another — `design/arch/facades/typecheck.md`
from a design doc, the retired `tests/plan/strategy.md` from `sprints/ROADMAP.md` line 3 —
is never resolved, even from a scanned document. ACT-0946 widened the roots to
the scheduling surfaces and `.claude/`/`.agents/`; it deliberately stopped
there.

Measured 2026-08-30 (`tests/plan/s120-evidence-delta.md` §1 row J): adding
`design/`, `spec/`, `audits/` and `user/` as roots to the ACT-0946 configuration
surfaces 214 new `PATH` findings in the live corpus — 165 cited from `design/`,
24 from `tests/plan/`, 18 from `sprints/`, 4 from `repl/`, 2 from `spec/`, 1
from `crates/`. Most are citations to retired facade specs and moved design
documents on lines that lack an exemption marker.

This is the same class ACT-0946 closed — a claim a single file-open refutes —
at roughly six times the volume, and it is the class a reader following a
design cross-reference hits. Measurement vocabulary: 214 is a
**measured-findings** count (checker output at candidate configuration J),
not an enrolment count. ACT-0946's own widening counted 28 candidate
enrolments at ruling time (this filing's figure; the ruled text is
unrecoverable) and finally **enrolled 21** baseline entries — repairs during
Waves 4–6 absorbed the rest (final diff +21/−26, 610 → 605;
`tests/plan/s120-evidence-delta.md` §2 C4 and §4.1). A repair-reduced
enrolment here would likewise be smaller than 214, but still several times
S120's, so it needs its own ruling under the ratchet's widening rule
(ACT-0946 ruling item 5, now carried by the
`scripts/citation-drift-baseline.txt` header and the evidence delta's C4),
and repair-before-widen may be the better disposition for some owners.

Returns to the next product sprint's scope gate; not for S120.

## S122 approved disposition

On 2026-09-10 the user approved the shared document-mechanism pilot in
`sprints/SPRINT.md`, superseding the narrow root-expansion request and its
completion checklist below. The existing checker source was reopened: its
fixed target roots still omit design/spec/audits/user. The pilot addresses that
gap through a shared reference resolver plus independently discovered document
establishment to root `CLAUDE.md`, rather than a standalone root-list patch.
The original measurement below remains historical evidence only.

Sprint coordinates the shared design, QA evidence, test-owned checker adoption
and document-owner repairs. Candidate validation in Magic is read-only; Magic
cutover and upstream publication remain subsequent operations. Existing debt
must be mapped or repaired explicitly, with any proposed residual exceptions
returned to the user. No automatic baseline migration is approved.

## Original completion evidence (superseded by S122 disposition)

- A ruling on which of the four roots join, and on repair-versus-enrol per
  citing-document owner, with the measured count at ruling time.
- If widened: the baseline diff satisfies the ratchet's widening rule —
  ACT-0946 ruling item 5, carried by the `scripts/citation-drift-baseline.txt`
  header and `tests/plan/s120-evidence-delta.md` §2 C4 — with the new roots
  substituted, and `tests/citation_drift.rs` gains a planted doc→doc fault and
  a clean doc→doc citation in its fence.
