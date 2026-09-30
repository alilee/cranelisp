---
id: ACT-1028
title: A let-bound vec-set of a parameter, returned from the function, leaks one block
status: deferred
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - tests/join_forwards_its_binder.rs::match_arm_forwarding_a_compile_time_cow_copy_keeps_it_live
  - tests/plan/s122-evidence-delta.md
  - spec/12-runtime.md §12.3.1
---

## Observation

Measured armed, `--run --no-cache`, on the working-tree binary `a423324d…`.
Sources: QA's V1 probes (`.local/s122-1024-v1-qa/probe-run4.txt`) and
`test`'s V1c halves (`.local/s122-backend-v1c-test/halves.txt` `457cda79…`).
`main` is `(defn main [] (Pure (vec-len (f (vec-push [] 1)))))` in each
shape.

| Shape of `f` | Allocs/deallocs | Result |
|---|---|---|
| `(defn f [v] (let [w (vec-set v 0 5) n (vec-len v)] w))` (`d2c_ctl`, compile-time copy) | 3/2, exit 1 | Leaks 1 at HEAD `e4062202` and in the working tree, analysis on and off |
| `(defn f [v] (let [w (vec-set v 0 5)] w))` (in-place twin) | 2/1, exit 1, `rc_inc=3 rc_dec=1` | Leaks 1 |
| `(defn f [v] (let [w (match (vec-set v 0 5) [r r])] w))` (`d2c_ctl2`) | exit 1 | Balanced with analysis on; leaks 1 with it off |

- **Sibling, not reduced:** `b2`,
  `(let [a (match (vec-set v 0 5) [r r]) n (vec-len v)] (vec-push a n))`,
  leaks 1 in every toggle.
- **Class:** `rc-miscount`, a leak. No fault has been observed.
- **Where it shows.** D2-C's control is `d2c_ctl`. The pair subtracts this
  leak, so D2-C does not show it.

## Attribution

**Unknown.**

- It is not the compile-time copy path: the in-place twin leaks the same
  block.
- The R3 ruling does not claim it for
  [ACT-1026](ACT-1026-binder-forwarding-join-consumed-in-frame-leak-intake.md).
  ACT-1026's literal-valued join returned from `f` balances.
- No mechanism has been observed at a seam.
- **Missing: a control.** No committed cell exists, because no measured
  one-difference control balances. The L-CC pair was withdrawn at V1c because
  both of its halves leak
  ([V1c record](../../tests/plan/s122-evidence-delta.md#act-1024--v1c-record-and-the-l-cc-disposition-2026-09-30)).

## Disposition

**Carried to S123 (user-approved carry, 2026-09-30).** It was carried with
ACT-1026 as L-CC and is now its own filing because its attribution is
unknown. This is the first deferral.

- **V2 (S122)** re-runs the V1c halves once on the fixed binary as a
  diagnostic observer. A fault in either half stops V2. A count change is
  recorded here and does not gate ACT-1024 or ACT-1027.
- **V2 result: no count change and no fault.** The run is
  `.local/s122-backend-v2-test/halves-v2.txt`, `32f668a4…`, on binary
  `6c5001c2…`.
  - The in-place half reads 2/1 and the `d2c_ctl` half 3/2, the same under
    both import lines.
  - `d2c_sub` now equals its control: 3/2 with no fault.
  - These are absolute counts on no-prelude children and are diagnostic only.
- **S123, before `dev`:**
  - `test` builds a committed failing cell with a balanced one-difference
    control. An unmeasured candidate is the same `f` without its `let`,
    `(defn f [v] (vec-set v 0 5))`, with the same `main`. If that control
    does not balance, `test` stops and reports to QA.
  - QA attributes the mechanism with a control, then routes it to its owner.

## Completion evidence

- A committed cell was observed RED, then GREEN with its control balanced.
- D2-C's comment names this action while the leak stands. Once the leak is
  fixed, the comment says in the past tense that the control leaked.
