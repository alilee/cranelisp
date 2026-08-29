---
number: 0939
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: design/arch/principles/11-single-pipeline-mode-parameters.md — states
  the single-pipeline rule and its Sprint-26 origin, but not the audit test that
  distinguishes a compliant shared spine from an early mode branch
status: open
---

# Principle 11 amendment: the acid test is early-branch duplication, not divergence in meaning

## Issue

Principle 11 states the rule ("one compilation pipeline… the difference is a parameter
on a shared function") and names the Sprint-26 dual-pipeline defect as the canonical
anti-pattern. What it does not give is a test an auditor can apply, and the obvious
test that fills the gap is too weak.

The sharp form the user gave in S102: the disease is **not** only "two paths that MEAN
different things." It is **branching early on mode and thereby duplicating work that is
actually the same on both paths** — even when the two paths currently produce identical
meaning. Duplicated code can encapsulate identical meaning; the duplication is the
disease, present from the early branch, and divergent meaning is just the symptom that
surfaces later when one copy gets a fix and the other doesn't (which is exactly how
FIXME 0514 arose). So auditing by "do these paths diverge in meaning?" exonerates
early-branch duplication that has not drifted yet.

**The test: did an early mode branch fork into arms that re-do the same work?**

**The cure:** a shared spine with the branch pushed LATE and NARROW — only the
genuinely-different bit forks, as far downstream as possible, ideally branching on the
real discriminant (e.g. cluster membership) rather than a mode proxy. Target shape is
one seam reached only by the modes it applies to, with no mode boolean. `src/exe.rs`'s
`validate_main` is the in-repo exemplar.

Two instances the current wording did not prevent. S98 FIXME 0499 — `(select [])` was
fatal under `--run` but silently returned an unsound null in the REPL; the cause was a
dual host *wrapper* (the REPL hand-rolled a partial mirror of the shared
error-observation sequence), and routing through the shared driver closed the whole bug
class. S102 FIXME 0484 — the name-collision rejection was implemented at the REPL commit
gate only, so batch `--run` silently kept the old def-wins behaviour; the user flagged
the mode divergence as the tell that the rejection had to move to the shared typecheck
path.

The root `CLAUDE.md` §Pipeline already says a REPL/`--run`/`--link` divergence is always
a defect. What is missing is the diagnostic that catches it *before* it diverges.

## Proposed resolution

Amend `11-single-pipeline-mode-parameters.md` with a **Consequence** or **Audit test**
paragraph carrying: the acid-test question; the "meaning-divergence is the symptom, not
the disease" framing; the shared-spine / late-narrow-branch cure with `validate_main`
cited as the exemplar; and the 0499 dual-*wrapper* vs dual-*driver* distinction — a
wrapper finding can be fixed narrowly and immediately, a genuine dual-driver regression
escalates to `/arch`, and either way the enforcement lands at the shared seam rather
than a mode-specific gate.

Per `design/arch/principles/CLAUDE.md`, amending the text does not change the four import blocks,
but the Configuration-consistency audit applies.
