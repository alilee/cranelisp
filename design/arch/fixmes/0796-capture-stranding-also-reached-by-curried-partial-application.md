---
number: 0796
target: /design (backend)
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/arch/fixmes/0760-capture-drop-glue-strands-nested-heap-in-non-closure-captures.md;
  tests/gen_ownership_flows.rs::balance_exclusion; tests/capture_drop_glue_strands_nested_heap_0760.rs
status: open
---

# 0760's capture stranding is also reached by AUTO-CURRIED partial application — a closure the user never wrote

## Severity

Minor as a defect (same seam, same class, same open ruling as 0760 — it adds no
new mechanism). Important as evidence: it widens what the a-vs-b ruling has to
collapse, and it is the first thing the new generative harness found.

## Issue

FIXME 0760 states the stranding face as *"a closure capturing a vec of strings,
or an ADT with a heap field"*, and both its measurement battery (shapes K and L)
and its committed repro file
(`tests/capture_drop_glue_strands_nested_heap_0760.rs`) use an **explicit
`(fn …)`**. The generative flow harness landed in S115 W7
(`tests/gen_ownership_flows.rs`) enumerates *position* independently of *owning
type*, and its `curried_partial_application` position leaks at the **identical
per-iteration rate** as `captured_in_escaping_closure`, for every owning type,
under both ownership toggles:

| owning type | captured_in_escaping_closure | curried_partial_application |
|---|---|---|
| `(Vec String)` | 3 / iteration | 3 / iteration |
| ADT with a `String` field | 1 / iteration | 1 / iteration |
| `(Vec Bx)` (ADT with a heap field) | 4 / iteration | 4 / iteration |

Measured at HEAD `99bd23a8`, `--run`, `CRANELISP_RC_STATS=1`, `PrimitivesOnly`,
at iteration counts 1 and 25. The curried shape is:

```clojure
(deftype Bx (MkBx [:String s]))
(defn bxlen [:Bx b] (match b [(MkBx s) (str-len s)]))
(defn cur [:Bx x :Int y] (add-i64 (bxlen x) y))
(defn cell [] (let [h (cur (MkBx "abcd"))] (h 0)))    ; leaks 1 per call
```

No `fn` appears in the user's source. The auto-curry closure env is minted by
the compiler (§4.6.3), captures `x`, and its release strands the field string
exactly as an explicit capture does.

## Why this matters to the ruling

0760 asks `/design`(backend) to rule between (a) making the type-directed
release borrowed-builder-parameterised and (b) per-type named drop-glue
functions called from every release site. This finding does not change the
options, it changes the **site census** the ruling has to satisfy: the capture
drop glue is reached from a compiler-synthesised capture set as well as a
user-written one, so "fix the `fn` path" is not a scoping option. It is
additional weight behind (b), on the same argument as the
`MAX_DROP_GLUE_DEPTH = 4` cliff 0760 already records.

## Proposed resolution

`/design`(backend): fold the curried-partial-application reaching context into
0760's shape census when ruling. `/testing` will add it to
`capture_drop_glue_strands_nested_heap_0760.rs` as an acceptance cell **when the
fix wave opens** — deliberately NOT now, because 0760 already carries three
failing-not-ignored pins for this one unfixed defect and a fourth buys no signal
while costing a triage cycle every certification run (the FIXME 0745 rider's
discipline). Until then the generative harness records it as a named, measured
`balance_exclusion` with these rates, so removing the exclusion after the fix is
the acceptance check.

## Context

Filed by `/testing` at S115 W7 while landing the generative harness (matrix item
O4). The harness enumerates {owning type × nesting} × {position} rather than a
hand-written shape list precisely so a reaching context nobody enumerated shows
up as a cell; this is that, on its first run.
