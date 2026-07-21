---
number: 0753
target: /dev
filed_by: /review (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/backend/s115-carrier-and-rc-sweep.md §2.2/§2.3; crates/cranelisp-backend/src/compiler/fn_compiler.rs::{tco_promoted_borrowed_params, flush_superseded_heap_params_before_tail_jump}
status: open
---

# The 0720 ADT-supersede face balances toggle-OFF but retains a CONSTANT residual of 1 toggle-ON — §2.3's acceptance is `allocs == deallocs` EXACTLY

## Severity
Important — the scaling defect IS fixed (that is the win); the residual is fixed,
not per-iteration. But the sweep's binding acceptance is exact balance, the
residual is present in ONE toggle only, and the W3 note reports the numbers
without naming the gap.

## Issue

Measured at `4ea5c758` (`--run --no-cache`, `CRANELISP_RC_STATS=1`,
`PrimitivesOnly`), the `Gr`-wrapped supersede loop:

| N | analysis-ON | analysis-OFF |
|---|---|---|
| 1 | allocs=5 deallocs=4 | — |
| 2 | allocs=7 deallocs=6 | — |
| 3 | allocs=9 deallocs=8 | — |
| 200 | allocs=403 deallocs=402 | allocs=403 deallocs=**403** |
| 400 | allocs=803 deallocs=802 | allocs=803 deallocs=**803** |

So the per-iteration leak is gone in both toggles (the wave's goal), toggle-OFF
is EXACT, and toggle-ON retains a constant 1 across all N. The trivial controls
are exact in both toggles (`(Pure 9)` 1/1; a single non-looping
`match`+`vec-get` over a `Gr` 3/3), so the residual is specific to the
promoted-param TCO path under analysis-ON, not an entry-frame artefact and not
the 0745 entry-payload face (this `main` returns a scalar `Pure`).

`s115-carrier-and-rc-sweep.md` §2.3 is explicit: *"`allocs == deallocs` EXACTLY
at each face (never leak → under-count)"*. A one-object fixed residue that
appears under exactly one toggle is also a toggle-divergence signal of the kind
§2.2's "the two paths now agree by construction (Principle 7)" claim is meant to
have eliminated.

## Proposed resolution

`/dev`(backend): attribute the residual (most likely candidates: the promoted
param's entry `rc_inc` not being discharged on a path where the exit cleanup is
skipped — e.g. via `skip_var` / `transfer_skip` on the final iteration — or the
initial `Gr` argument's own reference at the call site). Then either close it or,
if it is provably a different defect, record the attribution and re-state §2.3's
acceptance for this face honestly rather than leaving the measurement unexplained.

Bare-vec twin control re-verified GREEN and undisturbed by the promotion:
`allocs=2 deallocs=2 reuse_hit=200` analysis-ON (in-place reuse preserved — the
0695 exemption is NOT damaged by `tco_owned_params`), `allocs=202 deallocs=202
reuse_miss=200` analysis-OFF.

## Context

`/review`(backend), S115 W3. The numbers at N=200/400 match `/dev`'s own report
verbatim; this FIXME is about the disposition of the residual, not a dispute of
the measurement.
