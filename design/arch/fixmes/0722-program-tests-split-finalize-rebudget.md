---
number: 0722
target: /dev (typecheck deployment)
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/program/tests.rs (10,576 lines, 213
  tests, zero inner modules) + crates/cranelisp-typecheck/src/program/finalize.rs
  (1,517 lines vs ~820 design estimate / ~1,200 ceiling) +
  design/typecheck/program-decomposition.md §3 (the designed split + its
  rejected-alternative box + citation-update list)
status: open
---

# Execute the designed program/tests.rs split; re-budget finalize.rs at the harvest-window seams (audit S114 R-3, accepted at S115 Phase 1)

## Issue

`audits/cranelisp-typecheck-s114.md` §2.2c, accepted by the user at S115
Phase 1: the S109 0580 design (`program-decomposition.md` §3) ordered a
per-submodule test split with an explicit rejected-alternative box for the
one-file shape — and Stage B landed the file cut WITHOUT the split; the
rejected alternative is what shipped, silently, and the file has since grown
+40%. The accepted S108 R-4 done criterion ("splits alongside per METHOD §2.2
attributability") is unmet. `finalize.rs` exceeds both its design estimate
and the accepted ceiling; the §11.8.10 harvest-window structure is the
natural cut line. This is the second carry of a half-executed acceptance —
a further silent drop is not an option (METHOD §2.4 2× escalation).

## Proposed resolution

Audit R-3 Done criteria: per-submodule sibling test files per the §3
distribution table (a RED attributes to a production submodule by file); no
`program/` submodule exceeds ~1,200 lines (finalize.rs cut at the
harvest-window seams, `monomorphisation.md` §11.8.10's table cites the
function-level boundaries); the citation-update list in the design (CLAUDE.md
test-path names, `tests/plan` citations) executed; suite green at each stage
per the design's staged plan. The S108-R-4/0580 done criterion is finally met
in full. If any part is judged undeliverable, supersede the
rejected-alternative box in `program-decomposition.md` §3 explicitly — either
outcome ends the silent design/tree divergence.
