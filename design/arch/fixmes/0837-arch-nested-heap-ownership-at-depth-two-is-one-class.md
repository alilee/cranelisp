---
number: 0837
target: /arch
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/arch/fixmes/0835-*.md (nested Sexp ADT, corruption at 2 cells)
  + 0810-*.md (match over an owned ADT temporary; heap payload strands the box
  AND its field) + 0760-*.md (capture drop-glue strands Vec-of-heap /
  ADT-with-heap-field) + 0796-*.md (curried partial application reaches the
  same seam) + tests/capture_drop_glue_strands_nested_heap_0760.rs (the
  MAX_DROP_GLUE_DEPTH cliff, measured at depth 5) +
  design/arch/safety-invariants.md §4 R8
status: open
---

# Five S115 findings are one class: nested heap ownership at depth ≥ 2

## Issue

`/sprint` observation at S115 Phase 6b, offered for `/arch`'s judgment rather
than as an attribution. Five separately-discovered, separately-attributed
findings this sprint share a shape that none of their individual records
names:

| Finding | Shape |
|---|---|
| **0810** (match over an owned ADT temporary) | leaks/over-releases; with a heap payload it strands **2 per iteration — the box AND its field** |
| **0835** (nested `Sexp` construction) | `(SCons (SexpSym "a") (SCons … SNil))` — **two levels** — corrupts the heap; **one cell is fine** |
| **0760** (capture drop-glue) | strands `Vec`-of-heap and ADT-with-heap-**field** captures; scalar captures are exact |
| **0796** (curried partial application) | reaches 0760's seam at an identical rate |
| **depth cliff** (pinned in the 0760 battery) | depths 1–4 balance exactly; **depth 5 leaks 1/iteration, depth 6 leaks 2** — one further object per level, unbounded |

The common factor is not the construct (`match`, capture, curry, constructor)
and not the container (`Vec`, ADT, closure). It is **ownership of heap that
owns further heap**. Every one of these is exact at depth 1 and wrong at
depth ≥ 2, and the depth cliff shows the same failure continuing to deepen
past a fixed limit.

Three corroborating details:

- `/stdlib` retired the S87 `either` SIGBUS note as stale (the test passes),
  then found 0835 aborting **on the same code path at two levels of
  nesting** — its own words: *"the S87 diagnosis had the right seam, wrong
  depth."*
- `/stdlib` reshaped its macro twice and moved the crash **face**
  (hang → panic → silent exit) **without moving the ceiling** — the signature
  of corruption rather than logic.
- The W3c/W4c fixes converged five gates onto ONE type-directed release
  (`Vec` → `vec_drop` + per-element dec; ADT → recursive glue; `Fn` →
  embedded glue). That release exists and is correct at one level. The open
  faces are all about what happens when the thing it releases **owns
  something in turn**.

## Why this is `/arch`'s

The individual fixes are per-seam and correctly attributed where they sit.
The question this raises is whether the seams share a **single unstated
invariant** — something like *"a release must discharge the transitive
ownership of what it releases, at any depth"* — that no register row states,
and whose absence is why the same shape keeps arriving through five different
doors.

If so, the useful outputs are: a `safety-invariants.md` §4 row for it (R8 is
about RC *balance*, not about transitive discharge); a decision on whether
`MAX_DROP_GLUE_DEPTH = 4` is a bound that should exist at all (its own comment
concedes "fields leak" past it, which is a documented unsoundness); and an
opinion on whether the 2-word `HeapHeader` — `{alloc_size, rc}`, **no glue
pointer** — makes transitive discharge expressible at all, which is the same
header question the S115 intrinsics audit raised as its R-6 and tied to the
0745 carry.

That last connection is why this is worth one ruling rather than five fixes:
the audit's R-6 says *no generic release can exist* with the current header,
and four of the five findings above are precisely cases where a generic,
depth-transitive release is what would be needed.

## Proposed resolution

`/arch` judges, at S116 Phase 1 or 2, whether these are one class. If yes:
name the invariant, add its register row, and sequence R-6's header ruling
**before** the individual fixes — otherwise each is fixed at its own seam and
the class reappears through the sixth door. If no, say which axis actually
separates them; that answer is worth as much, and the five records should then
cross-reference it so the next investigator does not re-derive the hypothesis.

No fix is proposed here and no existing attribution is disputed. This is a
grouping question, filed because the grouping is invisible from inside any one
of the five records.
