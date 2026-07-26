---
number: 0761
target: /qa
filed_by: /dev (cranelisp-backend, S115 W3b)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/helpers/e2e.rs::SafetyMatrix (the `check_rc_balance` face); design/backend/s115-carrier-and-rc-sweep.md §2.3
status: open
---

# The standing RC instrument is DIFFERENTIAL, and every leak W3b found is toggle-independent — it passed on both sides

## Severity

Important — an instrument that is blind to a whole defect class is worse than
no instrument, because its green is read as coverage. Four separate
per-iteration leaks shipped under it in one wave.

## Issue (METHOD §2.2 — the instrumentation question, answer (b))

`SafetyMatrix`'s RC face (`tests/helpers/e2e.rs`, `check_rc_balance`) asserts:

```rust
assert_eq!(imbalance(&rc_on), imbalance(&rc_off), "...")
```

— the ownership-ON alloc imbalance EQUALS the ownership-OFF one. That is the
right instrument for *elision* defects (the analysis removed an op the
conservative lowering keeps). It is **structurally blind** to a leak both
lowerings share.

Every defect isolated in S115 W3b is exactly that:

| shape | ON | OFF | differential verdict |
|---|---|---|---|
| curried local closure escaping its frame (0749) | 201/1 | 201/1 | **PASS** (equal) |
| plain lambda returned through two `let`s (0749) | 301/101 | 301/101 | **PASS** |
| `VecLit` returned through one `let` (0749) | 201/101 | 201/101 | **PASS** |
| closure capturing a Vec-of-Strings (0760) | 401/201 | 401/201 | **PASS** |

Only FIXME 0753's residual was toggle-ASYMMETRIC (403/402 ON vs 403/403 OFF),
and that one was caught — by a human reading `/dev`'s reported numbers, not by
the lane.

`design/backend/s115-carrier-and-rc-sweep.md` §2.3 already states the correct
bar in prose — *"`allocs == deallocs` EXACTLY at each face (never leak →
under-count)"* — but nothing standing asserts it. It is applied by hand, per
shape someone thought to write, at review time.

## Proposed resolution

`/qa`: add an **exact-balance lane** — `allocs == deallocs` asserted
absolutely, not differentially — over a matrix that crosses the two axes this
wave proved independent:

- **owning type**: Vec-of-scalars / Vec-of-heap / ADT-with-heap-field / closure
  -with-capture / closure-capturing-a-closure / nested (ADT whose field is a
  Vec of ADTs — the `f4_sudoku::solve-range` shape);
- **position**: a `let`-bound local; a `Borrowed` argument temporary; a value
  RETURNED from its defining frame (the 0749 axis — the one the W3 change-set
  measured only in the non-escaping shape and declared balanced); returned
  through N `let`s (N ∈ {0,1,2} — the depth axis that separated D from F);
  a TCO loop-carried param; a closure-env capture.

Both toggles, and `--link` as well as `--run` (W3b verified all four faces
agree by hand: C 201/201, C2 301/301, F 301/301 in both modes).

Keep the differential face — it answers a different question. Add the exact
one beside it, and make the exact one the `s115-carrier-and-rc-sweep.md` §2.3
acceptance instrument it already claims to be.

Suggested seed shapes (all measured at W3b HEAD, all EXACT there, so they
land GREEN and are regression guards, not defect repros) are in the FIXME 0749
and 0760 bodies and in the `/dev` W3b report.

## /qa S118 Phase-3 disposition (2026-07-25) — requirement rides now; the standing LANE defers to S119

The exact-balance REQUIREMENT is already the operative instrument for the
whole S118 Track-B family: every committed baseline RED in the
0810/0760/transitive/program-result/conj set asserts absolute
`allocs == deallocs` (not the differential), and the new S118 W1 rows (0726
tripwire, 0830 eliminator positions) are exact-balance by specification
(`tests/plan/s118-test-plan.md` §4.2). What defers is the standing
owning-type × position exact-balance LANE as a harness feature: building it
while ~21 cells of the same matrix are RED adds no discrimination and
competes with W1's detection-proof capacity. S119 is the right window — the
flipped Track-B cells then seed the lane GREEN as regression fences, and the
`s115-carrier-and-rc-sweep.md` §2.3 claim becomes true of a standing
instrument rather than hand-applied. Deferral is `/qa`'s, recorded here per
protocol; this FIXME stays open as the S119 trigger.

## /qa S119 Phase-3 disposition (2026-07-26) — the trigger has fired; the lane lands this sprint in normative form

The S118 deferral's condition is met: the Track-B cells flipped GREEN at S118
W3 and can seed the lane. Plan of record: `tests/plan/s119-test-plan.md` §4.5,
under the §5.1 normative-form proposal (paper §7 decision 5):

- **Vehicle:** `tests/gen_ownership_flows.rs` (already the owning-type ×
  position harness, 12 positions incl. the S118 eliminator rows). `/testing`
  reconciles its matrix against this FIXME's axes (borrowed argument
  temporary; returned through N ∈ {0,1,2} lets; TCO loop-carried; closure-env
  capture; matched positions) and fills gaps; both toggles; a `--link` face.
- **Form:** absolute exact balance (this FIXME's ask) is the legal degenerate
  form for these macro-free free-standing children, PROVIDED the binary
  carries one executed ambient-zero control; remaining `balance_exclusion`
  entries each cite an open defect or are removed.
- The lane row folds into `PLAN.md` at Phase 6/7 and this FIXME **deletes when
  the lane lands** (the S119 stage-1 `/testing` authoring window).

Filed by `/dev`(backend) at S115 W3b under the METHOD §2.2 instrumentation
clause: answer (b) — the instrument exists but is blind, and the correction is
cross-crate (it lives in `tests/`, `/qa`'s and `/testing`'s territory), so it is
named and routed rather than landed with the fix. The in-crate half DID land:
`typed_release_kind` is now the ONE type-directed release classification with an
exhaustive dispatch, and `is_fresh_construction` is exhaustive over `MonoExpr`.
