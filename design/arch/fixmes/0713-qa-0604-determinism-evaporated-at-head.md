---
number: 0713
target: /qa
filed_by: /stdlib
filed_at: 2026-07-20
sprint_filed: 114
status: open
refers_to: design/arch/fixmes/0604-index-feed-phantom-prelude-write-race.md
  (the phantom `bit-and → primitives/bit-and` defect this is new evidence for) +
  its "Deterministic repro recipe" §; tests/plan/s114-test-plan.md §11 item 1
  (the S115-early 0604 plan of record).
---

# NEW EVIDENCE for 0604: the "25/25 deterministic" reproduction EVAPORATED at HEAD `31101126` (S114 Phase-6a)

## What was measured

The 0604 file records, as "the single most valuable asset this defect has ever
had," a **25/25 deterministic** reproduction on THIS VM (aarch64 Linux, kernel
7.0.0-27-generic) of the phantom undeclared-public `bit-and → primitives/bit-and`
entry, using the documented recipe with the **debug** binary:

```bash
printf '(import [num.bits [bit-and]])\n(import [primitives [Int]])\n(defn use-it [:Int x] :Int (bit-and x 7))\n' > /tmp/di.cl \
  && CRANELISP_LIB=/home/alilee/cranelisp/stdlib \
     ./target/debug/cranelisp --no-cache --run /tmp/di.cl
```

At current HEAD (`31101126`, post Phase-5 close; debug binary rebuilt at HEAD),
the phantom `ambiguous bare name 'bit-and'` poison fires **0 times across 85
runs** (25 exact-recipe + 25 with-main variant + a further 30 exact-recipe
batch). Every run instead reaches the clean import (the recipe's only residual
error is `entry module has no 'main' function`, i.e. the `num.bits/bit-and`
super-import resolved without meeting a second distinct terminal). The num.bits
self-test (REPL discover-tests recipe) is also stable 27/27 across 5 runs.

## Why this matters to the S115-early plan (please fold into 0604, do not treat as a separate defect)

The 0604 §"Next investigative step" plan of record hinges on the 25/25
determinism: *"25/25 determinism means one run names the writer of the phantom
entry and its origin"* — a single `CRANELISP_MODULE_TRACE=1` run at
`commit_staging_to_live` is expected to name the foreground writer. **That
one-run-names-it assumption no longer holds on this VM at this HEAD.** Either:

1. the phantom was incidentally suppressed by the S114 carrier/settlement work
   (the same window in which the `concurrency.md` "bare ctor crashes" warning
   stopped reproducing — 6a/docs — and the FIXME-0476 `(apply-it Some 7)` crash
   was verified fixed, /stdlib 6a), OR
2. 0604's timing/scheduling sensitivity shifted again (history: /sprint 16/16,
   /testing 0/140, /dev S110 0/~175, /dev S114-W5 25/25 — the heisenbug has
   swung between 0- and full-fire environments before).

Distinguishing (1) from (2) is exactly what /qa must decide before the S115
MODULE_TRACE run is scheduled: if the writer is now quiescent, the
`commit_staging_to_live` instrumentation must be paired with a fire-inducing
schedule (or the structural declared-export-closure gate landed on its own
merits, with the guard riding a synthesised — not recipe-dependent — trigger),
not run once against a recipe that no longer fires. The 0604 file's own
instruction — "preserve THIS record even if the VM state drifts" — is now
active: **the drift has occurred.**

This is EVIDENCE on an existing open /qa defect, not a new stdlib defect. Fold
it into 0604 (or its plan §11 item 1) and delete this file.
