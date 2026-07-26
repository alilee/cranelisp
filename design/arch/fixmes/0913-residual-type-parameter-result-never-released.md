---
number: 0913
target: /design (typecheck)
filed_by: /repl
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/int/result-owner.md §1.1.1 "Recorded limitation — the lenient-view
  placeholder gap" (:211-227) — the claim whose SCOPE this FIXME corrects;
  MonoExpr::lenient_from_expr (cranelisp-typecheck) — the ruled owner;
  src/repl/commands.rs::handle_mem — the instrument used;
  repl/demos/memory-lifecycle.demo — the committed REPL-surface demonstration
status: open
---

# A program result whose displayed type keeps a residual parameter is never released — and the recorded scope for this is `[]`/`None`, not the `Result` family

## Severity

Important. The leak itself is per-turn and small; what makes it Important is
**which shapes it covers**. `result-owner.md` §1.1.1 records this gap as
"an unpinned `[]` (or a bare polymorphic `None`)" — an exotic corner. Measured
at the prompt, the actual axis is *any* residual type parameter in the result's
displayed type, which includes **`(Ok x)` and `(Err x)`** — the single most
common result shape in the language, produced by every fallible function a user
writes, and leaked on the first try with no annotation in sight.

The design record also has one factually wrong example: **`None` cannot leak.**
It is a nullary constructor (bare i64 tag, no allocation — `HeapAdt` /
`NULLARY_TAG_THRESHOLD`), measured at 0 allocations and 0 deallocations across
three turns. Citing it as a leaking case makes the gap look narrower and
stranger than it is.

## Minimal repro — one variable, at the prompt

Verified at HEAD `4ed43430`, real stdlib, `/mem` snapshot arithmetic. The pair
below is the whole finding: **the same expression, the same value, differing
only in whether an annotation pins the residual parameter.**

```
> /mem
; allocs: 1217  deallocs: 74          live: 1143

> (Err "boom")
:(primitives/Result a primitives/String) (Result.Err "boom")
> (Err "boom")
:(primitives/Result a primitives/String) (Result.Err "boom")

> /mem
; allocs: 1221  deallocs: 74          live: 1147     <-- deallocs +0, live +4

> :(Result String String) (Err "boom")
:(primitives/Result primitives/String primitives/String) (Result.Err "boom")
> :(Result String String) (Err "boom")
:(primitives/Result primitives/String primitives/String) (Result.Err "boom")

> /mem
; allocs: 1225  deallocs: 78          live: 1147     <-- deallocs +4, live flat
```

Unannotated: 2 allocations per turn, **zero** deallocations, `live` grows.
Annotated: 2 allocations per turn, 2 deallocations, `live` flat.

## Measured matrix (3 turns each, bare path, `/mem` snapshots)

| Result | Displayed type | allocs | deallocs | live | Released |
|---|---|---|---|---|---|
| `(Some "boom")` | `(primitives/Option primitives/String)` | +6 | +6 | 0 | yes |
| `"a string literal"` | `primitives/String` | +3 | +3 | 0 | yes |
| `(Box "boxed")` (user product) | `user/Box` | +6 | +6 | 0 | yes |
| `(Node (Leaf 1) (Node (Leaf 2) (Leaf 3)))` | `user/Tree` | +15 | +15 | 0 | yes |
| `:(Result String String) (Err "boom")` | both params pinned | +6 | +6 | 0 | yes |
| **`(Err "boom")`** | `(primitives/Result a primitives/String)` | +6 | **+0** | **+6** | **no** |
| **`(Ok "boom")`** | `(primitives/Result primitives/String a)` | +6 | **+0** | **+6** | **no** |
| **`(Ok 1)`** | `(primitives/Result primitives/Int a)` | +3 | **+0** | **+3** | **no** |
| **`(vec)`** | `(primitives/Vec a)` | +6 | **+0** | **+6** | **no** |
| `None` | `(primitives/Option a)` | 0 | 0 | 0 | n/a — nullary |

Read together: the discriminator is **presence of a residual parameter**, not
which parameter, not whether the payload is heap or scalar, and not `Vec`
specifically. `(Ok 1)` leaks its `Result` box even though its payload is an
`Int`. Fully concrete displayed types release exactly, at every depth measured.

## Attribution — not re-opened, only evidenced

`result-owner.md` §1.1.1 already rules this **out of int's bounded context**:
backend keyed the result root through `lenient_from_expr`'s `ConcreteType::Int`
placeholder and emitted no glue, so the owner cannot release what was never
emitted; the owner is the **lenient view** (`MonoExpr::lenient_from_expr`,
typecheck) and closing it "wants `/qa` cover of its own". `/repl` accepts that
attribution as written and is not re-attributing. This FIXME supplies the two
things the record is missing:

1. **the corrected scope** (the `Result` family, and the parameter-position
   independence) — the recorded scope would not have caused anyone to schedule
   this, and the `None` example would have sent an investigator to a nullary
   value that cannot leak; and
2. **the missing durable trigger.** Per root `CLAUDE.md` §"Usability Findings
   and Defects", a defect is not closed until a narrow failing-not-ignored test
   reproduces it. There is no such test and no FIXME file — the sole record is
   a paragraph in an int design doc pointing at typecheck, which catches no
   regression and triggers no CI. The B-vs-E pair above is the repro, already
   reduced to one variable.

## Proposed resolution

`/qa` schedules the lenient-view row the design record defers to, and routes
`/testing` the B-vs-E pair as a narrow guard (marginal accounting per
`tests/helpers/marginal.rs` makes the ambient prelude residue subtractable, so
the cell can assert an exact marginal 0 rather than a bound). Then
`/design`(typecheck) rules the lenient view, and `result-owner.md` §1.1.1's
scope sentence is corrected in the same window — it is currently the record a
future reader will trust.

Do NOT close this by pinning the annotation in tests or docs. "Annotate your
`Result` and it stops leaking" is not an acceptable user-facing contract, and
the residual-parameter *displays* themselves are spec-required
(`repl/spec.md` §1.5/§4.1) and were deliberately protected by the W4
release-key ratification — the displays are correct; the release behind them
is not.

## `/qa` triage (S118 P6 close) — axis confirmed; scheduled S119; marginal cell lands in the P6 batch

Full record: `tests/plan/s118-test-plan.md` §11.8.3.

- **Axis confirmed as filed:** the discriminator is a residual type parameter
  in the result's displayed type — the `(Err x)`/`(Ok x)` family plus
  `(vec)`, not the recorded `[]`-corner; `None` cannot leak (nullary). The
  one-variable annotation-pin pair is accepted as the reduced repro; the
  `result-owner.md` §1.1.1 attribution (lenient view,
  `MonoExpr::lenient_from_expr`, typecheck) is accepted as ruled — not
  re-opened.
- **Risk rank: Important, leak polarity, REPL-dominant.** Every unannotated
  fallible-result turn — the most common result shape in the language —
  leaks its full result tree (2–6 blocks/turn measured), linear in session
  length; no memory unsafety; batch modes largely unaffected (`main`'s result
  is concrete at the result-owner seam). Not S118-blocking; MUST be
  scheduled: the previously recorded `[]`-scope would never have driven
  scheduling, which is this filing's real weight.
- **Routing:** retargeted `/design`(typecheck), **S119** — this IS the
  lenient-view row owed per the S118 W4+ drain. The `result-owner.md` §1.1.1
  scope correction (the `Result`-family scope; strike the impossible `None`
  example) is `/design`(int)'s side of the same window, per the section
  above. The no-annotation-pinning constraint above is binding on the fix's
  acceptance.
- **Durable record now:** `/testing` lands the marginal cell in the P6 close
  batch (`s118-test-plan.md` §11.8.6 item 4) — REPL-children pair, N
  identical `(Err "boom")` turns, control differing ONLY in the
  `:(Result String String)` annotation, instrument = child exit counters via
  `CRANELISP_ALLOC_PARITY_DUMP` (**not** `/mem` deltas — the `/mem` window
  itself is FIXME 0914), exact marginal 0, intended RED.

## REPL-surface status

`repl/demos/memory-lifecycle.demo` demonstrates the flat concrete cases and
then this leak, side by side with the pinned control, labelled as a filed
defect rather than hidden. That demo's narration cites exact counter values, so
it flips visibly when this closes. It is a demonstration, not the guard —
`/testing` still owns the committed cell.
