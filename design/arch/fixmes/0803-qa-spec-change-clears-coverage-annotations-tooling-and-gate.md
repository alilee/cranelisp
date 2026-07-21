---
number: 0803
target: /qa
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: sprints/METHOD.md §2.2 "A spec change clears its coverage
  annotations" (the binding rule) + tests/plan/spec_coverage_reconcile.py
  (modes --check/--propose; it already detects "true gaps" and builds the
  test→spec index keyed by (spec-file, §anchor)) + tests/plan/spec_link_check.py
  (the test→spec direction) + root CLAUDE.md §"Requirements/Test Traceability"
  (the annotation convention, which does not yet describe invalidation)
status: open
---

# Spec-change-clears-coverage: the marker, the report, and the close gate

## Issue

User-directed mechanism (2026-07-21), now binding in METHOD §2.2. The band
(`[Tested …]`) asserts that a named test validates the requirement **as
written**. When the requirement changes, that assertion becomes a claim about
prose that no longer exists — and **nothing notices**, because the citation is
still *live*: the named test still exists and still passes. The linter checks
that a test with that name exists, not that it still validates the current
prose.

**The reporting already exists; the invalidation trigger does not.**
`spec_coverage_reconcile.py` already detects true gaps (headings/MUSTs with no
covering test), stale-pending (`[S{M}]` rows that DO have a cover), and dead
citations. Clearing on a normative change is what moves a changed-underneath
row out of the invisible class and into the class the linter already reports.

**S115's worked failure** (the reason this is not bookkeeping): a user ruling
widened §7.1.1's occurrence rule from a nullary corner to a general
requirement. The spec was scribed; the band stayed green; the covering test
still existed and still passed — and **the implementation was never widened**.
It surfaced only when `/docs` probed it by hand in Phase 6a, a full wave later.
Under the rule, the row clears → the linter reports it uncovered → `/testing`
walks the backlinks → the covering test is found to exercise only the nullary
cell → the added non-nullary cell goes RED → the missing implementation is
mechanically visible in the same wave.

Same day, softer face: `/repl` found a `repl/spec.md` §1.4 row annotated
`[Tested tests/repl_negative::display_neg_type_always_qualified]` whose
behaviour a probe contradicts (FIXME 0802) — a `[Tested]` row asserting what
the binary refutes.

## Proposed resolution

`/qa` owns the band and the coverage process, so the mechanism's three
mechanical parts are yours:

1. **A distinct cleared marker.** `[S{M}]` already means "not yet tested,
   scheduled". A row *cleared by a normative change* is a different thing —
   it had coverage, the requirement moved, and the covering set is known and
   needs re-judging. Decide whether to reuse `[S{M}]` (simple, loses the
   distinction) or add e.g. `[Uncovered S{M} — was tests/…]` which **preserves
   the prior covering set as the starting point for the backlink walk**. The
   second is strictly more useful to `/testing` and costs one regex.
2. **Report it.** Extend `--check` so cleared rows surface as their own bucket,
   separate from never-covered gaps; the walk `/testing` needs (covering tests
   for a §anchor) is already answerable from the existing index.
3. **The close gate.** No row may be cleared-and-unrestored at sprint close
   without an explicit recorded carry. Wire it wherever the suite/coverage
   gates already run so it cannot be forgotten rather than remembered.
4. **The convention line.** Root `CLAUDE.md` §"Requirements/Test Traceability"
   describes the band but not invalidation; it needs the clear-on-change
   sentence and the invalidation-vs-judgment split (any skill may clear; only
   `/qa` restores). That file is not `/sprint`'s or `/qa`'s to edit unilaterally
   — raise it with the user or route to `/arch` once the marker is settled, so
   the canonical convention and METHOD agree.

Sequencing note: settle the marker (item 1) before `/spec` or `/repl` start
clearing, so the first cleared rows are written in the final vocabulary rather
than migrated later.
