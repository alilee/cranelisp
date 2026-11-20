---
id: ACT-1090
title: Commit planning reads a covered member's table from before its publication, so a trace form compiled while a dependency of a restored module is still compiling omits that dependency's frames
status: open
priority: advisory
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/04-expressions.md §4.12.3
  - spec/04-expressions.md §4.12.9
  - design/int/int.md §7.6.4
  - src/worker.rs::plan_staging_commit_inner
  - src/worker.rs::covered_batch
---

## Origin

`review`, reading commits `a812faaa` to `279cc37f` in source and running
nothing, reported that commit planning copies the module tables and reads
each covered member's readiness from the live scheduler afterwards, so a
member can publish between the two. `qa` reproduced it on 2026-11-20.

## Observation

`qa`, 2026-11-20, the debug binary built from `ee65d9aa`, in scratch
directories, with `CRANELISP_NO_LENIENT=1`, on a 14-processor machine.

```clojure
;; p.cl
(import [primitives [Int add-i64]])
(defn pf [:Int n] n)

;; m.cl
(import [primitives [Int]])
(defn mf [:Int n] (p/pf n))
```

The program traces `(mf 1)` and scores 40, plus 10 for each `m/mf` frame,
plus 1 for each `p/pf` frame. Required: 51 (spec §4.12.3, the whole-program
row; spec §4.12.9).

The cache is built by one complete run. Before each launch `p.o` is removed
from the project's cache, so `m` is restored and `p` compiles in the launch.

**`--run --priority-workers 8`.** `app.cl` imports `m`, and one name from
each bulk module, and traces in `main`. "No gap" counts the launches in
which the entry's planning did not wait for `p`.

| Fixture | Launches | No gap | Scored 50 |
|---|---|---|---|
| No bulk module; `p` padded with 9 definitions so that it publishes about when the entry plans | 600 | 249 | **0** |
| Six restored bulk modules of 200 definitions | 150 | 64 | **8** |
| Twelve such modules; the entry padded with 40 definitions | 52 | 13 | **6** |
| Six such modules, `--priority-workers 1` | 49 | 0 | **0** |

**The REPL prompt, default worker count.** `app.cl` holds the counter and the
bulk imports. One turn traces `(m/mf 1)`.

| Fixture | Launches | Scored 50 |
|---|---|---|
| Six bulk modules | 89 | **19** |
| Six bulk modules; `m` reaches `p` by `(import [p [pf]])` | 67 | **16** |
| The same, `p.o` not removed, so `p` is restored | 55 | **0** |
| No bulk module | 130 | **0** |
| No bulk module, the standard library's prelude loaded | 60 | **0** |

- Every launch that scored 50 printed no diagnostic and exited normally.
- The next `--run` after such a launch scored 51, in 2 of 2 readings.
- A launch that scored 50 never waited for `p`. `p` compiled on another
  thread in each.
- The last two REPL rows were read at one size of `p` each. Whether `p`
  published near the turn's planning in them was not measured.

## Classification: a defect, wrong value, low harm

The form is at the REPL prompt or in the entry file and must cover the whole
program (spec §4.12.3). One launch omits a frame that the same program
records in the next, against spec §4.12.9. The face is a shorter diagnostic
tree. No memory is read or written that should not be.

It is reached only from a cache in which a module is valid and the object of
a module it depends on is absent: a stopped or failed object pass, or a
deleted file. It is run-dependent in that state.

The coverage rule is S124's (B10, `f8c55626`). Whether the opening tree
recorded this frame was not run.

## Attribution: the binary, at commit planning

- **In source.** `plan_staging_commit_inner` copies every module's table
  into the prepared view. `covered_batch` then walks the covered set over
  that copy and asks the live scheduler whether each member has published.
  The backend reads the covered members' slot claims from the same copy
  (`compile_and_publish_prepared`). A member that publishes after its row
  was copied answers as published, and its copied row holds no claim. The
  copy has been made this way since `d1c34699`; the readiness read over it
  arrived with the covered set at `f8c55626`.
- **Entered at design.** [Int §7.6.4](../../design/int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10)
  derives the set "from the prepared view" under the settled-member
  predicate and does not order the two reads. The source follows it.
- **Control.** The fixtures differ in how long the copy takes. With nothing
  beside the program to copy, 249 launches that planned without a gap never
  lost the frame. With six bulk modules 8 of 64 did, and with twelve 6 of
  13.
- **Two other mechanisms are ruled out by observation.**
  - *The predicate answers too early.* Planning waited for `p` in 86 of the
    150 launches of the second row, so the predicate answers an in-flight
    member as unpublished.
  - *A published member's frames are lost.* With one worker `p` always
    publishes before the entry plans again, and every launch scored 51.
- **Not observed at the seam.** No instrument reports the copy or the
  readiness read, and `qa` edited no source. The order of the two reads is
  read in source and supported by the control. `dev`(`src/`) confirms it
  with a module row before correcting.
- **Refuted if** the frame is lost at a comparable rate with no bulk module,
  or in a launch whose planning waited for the member.

The object pass is not affected: it reads the live tables under the same
predicate, and the launch after a miss records the frame.

## Why coverage missed it

Every trace cell restores all of its modules or none. No cell restores one
module while a module it depends on compiles. The settled-member rule's
module rows give the walk a fixed view and a fixed predicate, so the order
of the two reads has no row.

## Evidence allocation

**REPRO-1090**, allocated to `test` in the
[evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
`dev`(`src/`) owes a module row with the correction: a member that publishes
after the view is taken is not read as settled from that view. Its shape
follows `design`(int)'s correction of §7.6.4.

## Completion evidence

REPRO-1090's subject fails on a launch that scores 50, then passes with its
control unchanged, and the module row is observed RED before the correction.
`qa` restores the spec §4.12.3 bands that name this action.
