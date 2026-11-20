---
id: ACT-1102
title: After a refused save the cache holds definitions the backing file does not, and the next cached session ends on a signal when one is called
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - repl/spec/15-session-persistence.md §15.2
  - repl/spec/15-session-persistence.md §15.1
  - src/session_v4/lifecycle.rs
  - sprints/actions/ACT-1101-session-save-refused-after-a-parametric-product-type-is-constructed-intake.md
---

## Origin

`test`, committing T-SAVE-PRODUCT: cached restarts crashed in two of its
subjects, so the cells restart cold. `qa` took it in on 2026-11-20.

## Observation

`qa`, 2026-11-20, the debug binary built from `9bc97297`, no prelude, scratch
directories since removed. Session 1 is ACT-1101's subject:
`(deftype (P2 a b) [:a x :b y])`, `(P2 1 2)`, `(defn f [] 1)`. Its save of
`f` is refused, so `user.cl` holds the `deftype` only. The project's cache
then holds `user.meta.json` and `user.o`.

| Session 2, in the same directory | Observed |
|---|---|
| `(f)` | **The process ends on signal 11** |
| `/list`, `/sig f` | `f` is listed with its signature, though the file does not hold it |
| `(P2 3 4)` | The value; exit 0 |
| `(f)` after the cache directory is removed, or with `--no-cache` | `undefined variable: f`; exit 0 |
| Control: a session saves `f` and `g`, the file is then edited to hold `g` only, cache kept; `(f)`, `(g)` | `undefined variable: f`, then 2; exit 0 |

The function-body subject of ACT-1101 crashes the same way. The seeded
`Pair` subject does not: no backing file exists, and the session starts
empty.

The debug binary built from the sprint's opening commit `3155f47f` gives the
same first four rows.

## Classification: a defect, memory-unsafe

- [REPL §15.2](../../repl/spec/15-session-persistence.md): a session is
  restored from its backing file. A definition the file does not hold is
  not part of the restored session.
- **Severity: memory-unsafe.** A call ends the process on a signal.
- **It predates S124** (the opening-tree reading).

## Attribution: the binary, provisional

- **By control.** An external edit that leaves the file behind the cache is
  detected, and the cache is not used. After a refused save it is used. So
  the session writes a cache generation from its own state under the
  identity of a file that does not hold that state.
- **Not read:** which step writes the cache after the refusal, and why the
  restored `f` has no code to call.
- **Refuted if** the cache after a refused save is byte for byte the cache
  from before the refused definition.

## Relation to ACT-1101

ACT-1101 is the only route `qa` knows to a refused save from user input.
Correcting it removes this face from that route and leaves this defect in
place for any other refusal.

## Routing

- **`qa` holds this action.**
- **`test`:** T-REFUSED-SAVE-CACHE, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(int), then `dev`(`src/`):** the correction, with a module row
  that does not depend on ACT-1101's route.

## Completion evidence

T-REFUSED-SAVE-CACHE is committed and observed RED on its exit clause. The
module row shows a refused regeneration publishes no cache generation ahead
of the file, and was seen to fail first.
