---
number: 0773
target: /testing
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/safety_oracle_lane.rs — the MS-P7 face-3 (`If`-joined
  may-alias container) cells the S115 W4 family fix does NOT cover; repros in
  FIXME 0772
status: open
---

# Face-3 (`If`-joined COW container) repro cells — the order-dependent arm and the let-mediated arm

## Severity

**Important** (the defect is Blocker-class — FIXME 0772 — but the missing
artefact here is the durable record).

## Issue

`/review` probed the S115 W4 MS-P7 family fix adversarially and found two
`--link` UAF aborts in the MS-P7 chained-may-alias family that the fix does not
cover. Per root `CLAUDE.md` ("Reproduced defects join the test suite
permanently") and METHOD §2.2 (repro-before-fix), these need committed
failing-not-ignored cells before `/dev` fixes them.

All programs are `PreludeVariant::PrimitivesOnly`, verified on this VM at
`d4efdf08`, and each is deterministic (2/2).

**Cell A — the order-dependent pair (the decisive shape).** The two programs
execute the same runtime path; only the static `If` arm order differs.

```clojure
;; A1 — cow arm SECOND: --run = 1, --link = 134 "corrupted double-linked list"  [RED]
(defn f [v b] (vec-get (if b v (vec-set v 0 1)) 0))
(defn main [] (Pure (f [9 9 9] false)))

;; A2 — cow arm FIRST (twin): --run = 1, --link = 1                             [GREEN fence]
(defn f [v b] (vec-get (if b (vec-set v 0 1) v) 0))
(defn main [] (Pure (f [9 9 9] true)))
```

A2 is the more valuable cell of the two: it is the **order-symmetry fence**. A1
alone would go green on a fix that merely special-cases the reversed order; the
pair is what pins order-independence.

**Cell B — the let-mediated `If` join (aborts in BOTH orders).**

```clojure
(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b v w) 0)))
(defn main [] (Pure (f [9 9 9] false)))
;; --run = 1, --link = 134 "free(): chunks in smallbin corrupted"
;; the arm-swapped twin (if b w v) with (f [9 9 9] true) ALSO aborts, same signature
```

**Green controls worth committing alongside** (all verified clean at
`d4efdf08`, and the first was RED at `d4efdf08~1` — it is the fix's own
generalization evidence, currently unpinned):

```clojure
;; three-link nested chain — RED at d4efdf08~1, GREEN now
(defn f [v] (vec-get (vec-set (vec-set (vec-set v 0 1) 1 2) 2 3) 0))
;; chain across a function boundary
(defn g [v] (vec-set v 0 1))
(defn f [v] (vec-get (vec-set (g v) 1 2) 0))
;; nested let chain, 3 links
(defn f [v] (let [w (vec-set v 0 1)] (let [x (vec-set w 1 2)] (vec-get (vec-set x 2 3) 0))))
```

## Proposed resolution

Land A1 + A2 + B in `tests/safety_oracle_lane.rs` beside the existing 0706
chained cells, `// defect: class=uaf locus=…::join_origin`, with the tier-4
differential lane treatment the sibling cells use (`--run` + `--link` + REPL).
Land the three green controls as born-green fences — especially the three-link
chain, which is the only evidence the family fix generalizes past the two cells
it was written against.

## Context

- Root cause and one-line-ish fix: FIXME 0772 (`target: /dev`).
- Design: `design/typecheck/ownership-inference.md` §17.4 left face 3
  "probe-first"; the probe has now been run and is RED in one arm order.
- `design/typecheck/ownership-inference.md` §17.7's `/qa`/`/testing` rider
  ("the chain-length axis") should gain an **arm-order** axis — order symmetry
  is the property that actually failed.
