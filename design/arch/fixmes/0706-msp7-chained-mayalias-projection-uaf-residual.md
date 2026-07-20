---
number: 0706
target: /qa
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: crates/cranelisp-typecheck/src/ownership/transfer.rs walk_apply ResultMode::ProjectionOf (68cd7a96) / tests/safety_oracle_lane.rs MS-P7 pin scope
status: open
---

# MS-P7 residual: chained may-alias + projection-out still double-frees (`--link` abort) — the W7 fix covers only the single-link face

## Severity
Blocker

## Issue

The W7 MS-P7 fix (`68cd7a96`, transfer.rs `ProjectionOf` arm escape-force)
closes the FLAT shape — `(vec-get (vec-set v 0 9) 0)` returns 9 in all modes
(probe-verified). But the fix protects exactly ONE may-alias link (the
immediately-projected container). A chain of length ≥2 in one frame still
double-decs an INNER link. Two deterministic repros (this VM, HEAD
`89d2f09c`, `PrimitivesOnly` prelude; `--run` returns the correct value,
`--link` binary aborts `corrupted double-linked list`, exit 134, 2/2 runs):

```clojure
;; (a) nested COW: (vec-get (vec-set (vec-set v 0 1) 1 2) 0)
(defn f [v] (vec-get (vec-set (vec-set v 0 1) 1 2) 0))
(defn main [] (Pure (f [9 9 9])))    ; --run exit 1 (correct); --link ABORT

;; (b) let-bound intermediate: single set over an alias binding, projected out
(defn f [v] (let [w (vec-set v 0 1)] (vec-get (vec-set w 1 2) 0)))
(defn main [] (Pure (f [9 9 9])))    ; --run exit 1 (correct); --link ABORT
```

Control (negative): the whole-value nested transfer is CLEAN —
`(defn f [v] (vec-set (vec-set v 0 1) 1 2))` +
`(defn main [] (Pure (vec-get (f [9 9 9]) 0)))` → exit 1 both modes. So the
open face is chained-may-alias × projection-in-the-same-frame, not nested COW
per se.

Not a regression: pre-W7 the flat face (the chain's outer link) aborted, so
both repros necessarily aborted too; the fix cannot have introduced it (the
escape-force only ADDS incs; the failure is in the too-many-decs direction).
Repro (b) shows the projected container DOES get the fix's escape-force
(Apply container, `Conditional` via the `w` binding) — the double-dec is on
the inner link, i.e. this is a 4th reaching context of the §3.7 `MayAliasOf`
family (chained links), not a mis-fire of the W7 arm.

Consequences for Phase 5 close accounting:

1. `safety_oracle_lane.rs` MS-P7 "FIXED S114 W7 … GREEN regression guard"
   pins only the flat shape; the `class=uaf` family stays OPEN.
2. The "3 stable REDs exact" certification arithmetic must grow by the new
   pins (per the §11 counting convention: intended new REDs are named).
3. SPRINT.md / plan §3.6 "MS-P7 FIXED" language needs a scope note
   (single-link face fixed; chained face carried).
4. FIXME 0693's binding clause ("fence must land before or with the W7
   escape-fact correction") now compounds: S115 will land FURTHER
   escape-fact corrections for this family — the producer/mirror
   disagreement fence must precede or accompany them.

## Proposed resolution

/qa adjudicates the family scope and orders: /testing pins (a) and (b) as
failing-not-ignored cells (the pin is the record + trigger; this FIXME then
closes — no double record); fix = S115 typecheck ownership scope, designed at
the family grain (every may-alias link whose accounting includes a
consumer-emitted release needs its protect — not another per-consumer arm;
route the design question to /design(typecheck), see the review report's
mirror note on transfer.rs encoding backend temp-drop policy in prose).

## Context

Found by /review at the W7 final-gate review (dispatch probe list item 1:
"nested projections"). Cite Principle 7 (the producer-side arm mirrors the
backend's temp-drop policy with no shared predicate — 0693's class one level
up) and the S111 §3.7 reaching-context census (this is context 4).

## ADJUDICATED (/qa, Phase 5 close, 2026-07-20) — delete with the pin commit

Family verdict accepted as filed; durable record =
`tests/plan/s114-test-plan.md` §3.6 "SECOND ADJUDICATION" + §7 ledger row +
§11.1. Summary: W7 closed the immediate-link face ONLY; faces (a)+(b) are
S115 typecheck-ownership carry at the family grain ("every may-alias link
whose accounting includes a consumer-emitted release needs its protect" —
no 5th per-context arm), the design question routes to /design(typecheck)
first; the review-noted If/Match Conditional-container face is an S115
probe-first row (no pre-committed RED); 0693's fence must land before/with
the S115 fix (its re-anchored trigger already binds this). Phase-7
certification: stable-REDs-exact = 5 incl. the two chained pins.

**Deletion trigger:** /testing's chained-face pin commit (repros a+b as
failing-not-ignored `class=uaf` cells + the whole-value GREEN control).
The pins are the record + trigger; this file deletes IN that commit per
the no-FIXME-with-failing-test rule. Not deleted at adjudication time
because the pins were not yet in the tree (parallel /testing close-out
held the build); whoever lands the pins deletes this file in the same
change-set.
