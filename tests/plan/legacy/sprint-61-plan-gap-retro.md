# Sprint 61 — Phase 3a Plan-Gap Retrospective

**Author**: `/qa` (Sprint 61 Wave 5 / Slice 5 Item J)
**Date**: 2026-04-22
**Scope**: Retrospective on `/qa`'s Phase 3a test-case derivation for
Sprint 61 Slice 2 (exemplar solver `test-unsolvable`) — what was missed,
what class of compiler bug went undiscovered by pre-implementation test
coverage, and what corrective coverage additions land in Ring 1 / Ring 2
test plans.

## Summary

Slice 2 surfaced a three-layer defect (Layer 1 algorithmic, Layer 2
aggregate-regression, Layer 3 inline-ADT-arg-wrapping-Vec codegen). Layer
3 — a backend RC-emission defect where an inline `(Ctor [val])`
expression passed as a function argument corrupted the inner Vec's
length — is the component this retrospective addresses. It fell outside
existing test coverage because `/qa`'s ring test plans lacked a
property-level assertion for the inline-ADT-arg shape.

The Phase 3a plan-level shortfall is distinct from the coverage-gap
shortfall and both are documented below.

## Layer-level breakdown

| Layer | Component | Fix owner | Pre-Slice-2 test coverage |
|---|---|---|---|
| 1 | `eliminate` returns `None` on same-value fixed cell | `/port` | Absent (exemplar-only behaviour; no property test) |
| 2 | Sudoku backtracking regression under naive Layer 1 patch | `/backend` (aggregate-regression under Layer 3) | N/A — artefact of Layer 3 |
| 3 | inline-ADT-arg-wrapping-Vec RC double-drop | `/backend` | **Absent — this retrospective's subject** |

## Plan-level gap (Phase 3a / Slice 2)

`/qa`'s Phase 3a derived Slice 2 test coverage by deferring to
`/port`'s branch-selection (branch (a) = /port reduces; branch (b) =
/port hands off with repro). The deferral was plan-level — the test
case list under `tests/plan/ring4.md §"Slice 2 branch-b outcome"` was
written as "author these tests once /port's reduction completes".

**What was missed**: a property-level assertion independent of branch
selection. A test of the form "for every unsolvable puzzle string,
solver returns Unsolvable" would have fired pre-Slice-2 against the
pre-fix `eliminate` contract (Layer 1), surfacing the algorithmic hole
before /port hit the 2-day reduction cap. The property test does not
require reduction work — it's a spec-level assertion (puzzle →
Unsolvable) against the semantic contract of `solve`.

**Corrective change**: `tests/plan/ring4.md §"Slice 2 branch-b outcome"`
should gain an explicit property-level row alongside the T-S2-1 /
T-S2-2 rows. This is a Ring-4-level finding and lands in the ring4
plan (not ring1/ring2), because it concerns the exemplar's semantic
contract, not a compiler codegen property. It is noted here for
completeness but the primary corrective coverage is ring1 / ring2 (see
below) where the Layer 3 defect actually lives.

## Coverage-gap (Ring 1 / Ring 2)

The Layer 3 defect is a **Ring 1 / Ring 2 codegen bug**: inline ADT
construction (`(Ctor [val])`) holding a heap-typed field (`Vec`),
passed as an argument to a function that unpacks the ADT and operates
on the inner Vec under consuming calling convention, double-drops the
inner Vec through the consuming-arg RC path. The bug class is:

> **Inline-ADT-arg class**: `(f (Ctor [heap-val]))` where `f` performs
> `match` + operation on the heap field under consuming convention,
> MUST be semantically equivalent to
> `(let [x (Ctor [heap-val])] (f x))` in ALL observable properties
> (inner heap value, RC balance, subsequent reads of derived values).

Ring 1 plan (`tests/plan/ring1.md`) covers closures, ADTs, and RC
balancing but does NOT include a row for the inline-arg-vs-let-arg
equivalence. Ring 2 plan (`tests/plan/ring2.md`) covers consuming /
borrowing calling conventions at cross-module boundaries but similarly
does not include a row for inline-ADT-arg shape.

### What Ring 1 should cover (corrective additions)

A property-level test class that, for every primitive and heap field
type `T` and every single-field ADT constructor `Ctor`, asserts:

```
(f (Ctor [v]))  ≡  (let [x (Ctor [v])] (f x))
```

in terms of:
- final computed value
- `alloc_count` / `dealloc_count` balance after execution
- `bytes_current` equality before and after
- no SIGSEGV / SIGTRAP / runtime panic

for `T` ∈ `{Int, Bool, String, Vec Int, Vec String, Option Int, Option
String}` and a representative `f` that `match`es the ADT and returns
(or operates on) the inner value.

### What Ring 2 should cover (corrective additions)

Extend the Ring 2 cross-module + consuming-convention table with the
inline-ADT-arg shape: the same `(f (Ctor [v]))` ≡ `(let [x ...])`
equivalence, but with `f` defined in a different module from the one
constructing the ADT. This exercises the consuming calling convention
across module boundaries for inline-constructed ADTs — the shape where
Slice 2 Layer 3 actually landed (solver.cl constructs inline Grids
via set-cell; user-code elsewhere constructs `(Some (some-vec))` etc.).

## Corrective coverage entries (landed in this wave)

- `tests/plan/ring1.md §"New Tests"` — appended inline-ADT-arg class
  (see ring1.md for the authoritative row).
- `tests/plan/ring2.md §"Cross-Subsystem Interaction Tests"` —
  appended inline-ADT-arg cross-module row (see ring2.md).

Tests are NOT authored in this wave — this is a test-plan expansion
only. Tests get authored when the plan is scheduled (likely S62
concurrency audit + RC-invariant audit, or a later RC-property sprint).

## New failing tests surfaced by the retrospective

None in this wave. The retrospective is a plan-level expansion; no new
tests are authored. If the plan's inline-ADT-arg rows are later
authored and fire against a codegen regression, those failures land in
`tests/plan/baseline.md` per the standard ledger discipline.

## Takeaway for future Phase 3a work

`/qa`'s Phase 3a derivation should include at least one property-level
row per defect class independent of the owning skill's branch
selection. The property row doesn't require the user-proxy skill's
reduction to be authored — it's a spec-level contract assertion that
can be written pre-implementation and will fire immediately if the
contract is violated. This is a lighter-weight form of the
"failing-tests-first" rule (`qa.md §"Spec-Scope Test Coverage"`) — not
every spec requirement needs full Phase 3a coverage, but every defect
class discovered during a sprint should spawn a property-level row in
the appropriate ring plan before the sprint closes, so the next
sprint's Phase 3a can consume the row directly.

## References

- `memory/feedback_cross_skill_minimal_repro.md` — minimal-repro
  discipline that governed the Slice 2 branch-(b) handoff.
- `memory/feedback_repros_join_suite.md` — reductions join the suite
  permanently.
- `memory/feedback_repro_handoff.md` — repros live in `tests/`, not
  `exemplar/`; this retrospective is a follow-on to that discipline.
- `design/backend/ring2-rc.md §5.5` — the `borrowed_vars` rule that
  fixed the Layer 3 defect; names the regression shape explicitly.
- `tests/exemplar_solver_correctness.rs` — the Slice 2 regression
  guards (T-S2-1 / T-S2-2), now inlined per the repro-handoff protocol.
