---
number: 0914
target: /design (int)
filed_by: /repl
filed_at: 2026-07-26
sprint_filed: 118
refers_to: src/repl/commands.rs::handle_mem:1146-1170 (the counter window);
  repl/spec.md §3.7 (the requirement, tightened this sprint);
  design/int/result-owner.md §2 / src/CLAUDE.md §"Program-result ownership"
  (the observe-then-release order the window sits inside)
status: open
---

# `/mem <expr>`'s delta window closes before the result is released, so it reports a phantom leak for every heap value

## Severity

Important — not for correctness (nothing leaks) but for **instrument
truthfulness**. `/mem` is the REPL's memory instrument; a user debugging their
own ownership reads it and acts on it. It now reports `live +N` for every
heap-valued expression, including expressions whose results the runtime
provably reclaims. It is the one command in the REPL that answers "did my
memory get freed?", and today it answers "no" whenever the answer is "yes".

This is a **W4 consequent**, and the direction matters: before the program-result
owner landed the result genuinely was not released, so `live +N` was truthful.
The owner made the world right and left the instrument reporting the old world.

## Mechanism (read at source, `src/repl/commands.rs:1146-1170`)

```rust
let allocs_before  = cranelisp_intrinsics::alloc_count();
let deallocs_before = cranelisp_intrinsics::dealloc_count();
let bytes_before   = cranelisp_intrinsics::bytes_current();

let eval_outcome = self.eval(expr_src);

let allocs_after  = cranelisp_intrinsics::alloc_count();   // <-- closes here
let deallocs_after = cranelisp_intrinsics::dealloc_count();
let bytes_after   = cranelisp_intrinsics::bytes_current();
```

The window closes immediately after `eval`. But the REPL's contract is
**observe, then release**: `main.rs`'s turn calls
`EvalResult::release_program_result()` after the whole `StyledDoc` is rendered —
and `handle_mem`'s return value, delta line included, *is part of that text*.
So the release is structurally outside the window. No counter is wrong; the
window is in the wrong place.

## Evidence — the release does happen, and the delta cannot see it

Verified at HEAD `4ed43430`. `Box` is `(deftype Box [:String contents])`, two
allocations per value. First, five **bare** turns with snapshots around them:

```
; allocs: 1197  deallocs: 54   live: 1143
(Box "boxed") x5
; allocs: 1207  deallocs: 64   live: 1143      <-- +10 / +10, live FLAT
```

Then five `/mem <expr>` turns on the same expression:

```
/mem (Box "boxed")   -> ; delta: allocs +2  deallocs +0  bytes +61  live +2
   ... x5, each reporting deallocs +0 / live +2 ...
; allocs: 1217  deallocs: 74   live: 1143      <-- +10 / +10, live STILL FLAT
```

Each individual delta claimed `deallocs +0  live +2`. The bracketing snapshots
show `deallocs` advanced by exactly 10 across those same five turns and `live`
never moved. **The releases happened; the delta lines were computed before
them.** `1217 - 74 = 1143` — the session's live count is byte-identical to where
it started, five "leaks" later.

## Requirement

`repl/spec.md` §3.7 now states this normatively: *the delta window MUST include
the program-result release*, because the point of the command is to answer
whether the expression's memory was reclaimed. The spec deliberately does **not**
pick the mechanism, and names two admissible shapes:

- the command takes responsibility for its own turn's release, releasing before
  it computes the closing counters; or
- the delta line is emitted after the release rather than composed with the
  result line.

## Why this is `/design`(int) and not a `/repl` demo note

Either shape touches the observe-then-release **ordering** that
`result-owner.md` §2 makes binding and mode-uniform, and one of them puts a
release call inside a slash-command handler — a second release site, where
`result-owner.md` is emphatic that there is exactly one finalization chokepoint.
Whether `/mem` may drive that chokepoint early for its own turn, or whether the
turn's text assembly must instead be split around the release, is an int design
question. `/repl` has specified the requirement and must not pick the seam.

Note the second shape has a knock-on `/repl` will want to review: if the delta
line is emitted after the release it is no longer part of the same rendered
document as the result line, which touches the §10.3 single-styling-authority
seam. Flag it back if the chosen shape changes what the user sees beyond the
numbers.

## Interim honesty (landed)

- `repl/spec.md` §3.7 records the exclusion as a known non-conformance and names
  the **snapshot** form as the truthful instrument until this closes.
- `repl/demos/memory-lifecycle.demo` is built entirely on snapshot arithmetic
  and closes by showing the delta form reporting `live +2` for a value the demo
  has just proven flat — labelled, not hidden.

No filtering, special-casing, or demo-only spelling was introduced.
