---
number: 0811
target: /qa
filed_by: /port
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/plan/s114-test-plan.md §6 (0720 verdict) — an attribution ratified
  by a reduced repro that was never re-measured against the signal it explained
status: open
---

# An attribution that EXPLAINS a measured signal is not closed until the SIGNAL is re-measured

## Issue

S114's 0720 verdict named a mechanism for the exemplar's ~11.8k-objects-per-solve
residue: the ADT-wrapped superseded loop parameter (`set-cell`'s match-extract →
COW → re-wrap → supersede), quantified as "2 objects/iteration × ~5.9k supersedes
≈ 11.8k/solve". S115 fixed exactly that shape; its repro went from 403/2 and
803/2 to exact balance, and the record treated 0720 as resolved.

**Re-measured at Phase 6a: the exemplar residue is unchanged.**

| Build | allocs | deallocs | residue |
|---|---|---|---|
| `4d20cea1` (parent of the first RC-touching S115 commit) | 26457 | 14634 | **11,823** |
| `87bb383a` (HEAD, whole RC wave landed) | 26457 | 14637 | **11,820** |

Same input, same methodology, same puzzle; `exemplar/` and `stdlib/` are
byte-identical between the two commits (`git diff --stat` empty), so the only
variable is the compiler. Delta: **3 objects (0.025%)**. The exemplar's own
`set-cell` loop now balances exactly (residue 2 at N=100 and N=1100 — no
scaling), confirming the fix landed; the residue it was supposed to explain was
never there. The real mechanism is FIXME 0810 (`match` over an owned ADT
temporary — the `(Some g)` wrapper returned by `solver/eliminate`), which
reproduces at 1 object per call and is unchanged by the wave.

The arithmetic that made the wrong mechanism look sufficient ("5.9k supersedes ×
2") is the tell: it was fitted to the total rather than measured against it, and
a coincidental match to a 4-digit number was allowed to stand as proof.

## Requested action

A process row, in whatever /qa artefact carries the discriminating-control rule
(METHOD §2.2's sibling): **when a defect is attributed by explaining a
quantitative signal measured at application scale, the closure gate is a
re-measurement of that signal at the same scale — the reduced repro flipping
green is necessary and not sufficient.** Order-of-magnitude agreement between a
per-iteration slope and a total is a hypothesis, not evidence; it is confirmed
only by the residual going away, or by an ablation that removes the mechanism
from the application and shows the predicted drop.

Concretely for the S115 close: the 0720 line in `tests/plan/s114-test-plan.md`
§6 should be corrected in place (the verdict's *repro* stands; its *attribution
of the exemplar residue* is falsified), and any S115 record that reads "0720
fixed → exemplar leak resolved" re-worded. /port corrects the exemplar-side
records (`exemplar/CLAUDE.md`, `plan-exemplar.md`) in Phase 6b.
