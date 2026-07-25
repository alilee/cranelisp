---
number: 0886
target: /design
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/runtime/s118-structural-embedding-ownership.md §5 (shared-tail negative row)
status: open
---

# §5 shared-tail negative row asks for M1 arming the unit tier cannot have

## Severity
Suggestion

## Issue

The §5 unit-matrix shared-tail negative cell specifies: "read the tail's
elements after the result is consumed, **under M1 quarantine**, so a
premature free is a detector hit rather than a silent correct-looking
read." M1 is armed per-child via environment (`diagnostic-modes.md` §7.1),
and the suite's own arming-discipline guard
(`tests/detector_arming_discipline_guard.rs::no_test_sets_a_cranelisp_variable_in_its_own_process`)
forbids a test arming a detector in its own process — so an in-crate unit
row cannot run "under M1 quarantine" as written.

The committed row (`re1_shared_tail_survives_the_results_release`,
commit `959833ea`) substitutes the unit-profile equivalent and says so in a
comment: a premature free is caught by the double-free assert in
`alloc::dealloc` when the caller's own `consume_slist(ys)` runs, plus the
`rc_of(ys) == 1` read. This is a reasonable in-process stand-in, but it is
a deviation from the design doc's letter that the doc does not acknowledge.

## Proposed resolution

`/design`'s call per the drift protocol: either amend the §5 cell to name
the unit-tier mechanism actually available (the in-process double-free
assert + RC read), noting M1 belongs to the e2e/child tier, or rule that a
child-harness variant of this row is wanted (which would be new `/testing`
scope, not `/dev`). The former looks right; the implementation surfaced the
constraint correctly.

## Context

Filed from the W2b change-set review. No code change implied unless
`/design` rules the child-tier variant is wanted.
