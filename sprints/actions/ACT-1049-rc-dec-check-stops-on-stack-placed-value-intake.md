---
id: ACT-1049
title: The armed release check stops on a stack-placed value's release, which is not a use-after-free
status: open
priority: required
from: qa
to: qa
sprint: 123
filed_at: 2026-11-16
refers_to:
  - crates/cranelisp-intrinsics/src/rc.rs::rc_dec_check
  - crates/cranelisp-backend/src/heap.rs::IMMORTAL_RC
  - design/backend/ownership-codegen.md §4.2
  - tests/plan/s123-evidence-delta.md
---

## Observation

QA measured this program on the U′ tree (`86402bc0…`) and on the checkpoint
compiler (`ee8959c0…`). Both runs used `--run --no-cache`, no prelude and an
empty library directory.

```
(import [primitives [*]])
(deftype Point [:Int x :Int y])
(defn main [] (Pure (match (Point 3 7) [(Point x y) x])))
```

- **Unarmed:** exit 3, 1 alloc and 1 dealloc, `stack_slot=1`.
- **Armed with `CRANELISP_RC_DEC_CHECK=1`:** the process panics with
  `STALE RC DEC (JIT inline): about to dec non-live heap pointer … Freed-value (size, payload@16) = None`
  and aborts.
- **CLIF of `user::main`:** the `Point` lives in `ss0`, and its header
  carries `0x4000_0000_0000_0000` (`IMMORTAL_RC`). The match arm passes
  `stack_addr ss0` to the release.
- **Sibling:** the same match on a heap-placed `Point` inside a loop
  balances under the armed check.

## Attribution

- **Mechanism, observed at its seam.** `rc_dec_check` treats any word at or
  above `NULLARY_TAG_THRESHOLD` that is not a live tracked allocation as
  stale. A stack slot is never tracked. The immortal header makes the
  release harmless, so the stop is a false positive of the check, not a
  product fault.
- **Distinguishing signature.** A true stale release names a freed block
  (`Freed-value … = Some(..)`). This stop reports `None`.
- **Refuted if** the stack slot's header is found to reach zero, or a
  release through it writes outside the slot.

## Consequence for evidence

An armed half that contains a NoEscape constructor stops on its release, so
its pair cannot measure anything. Cells keep such constructors out of armed
halves until this is resolved
([evidence delta](../../tests/plan/s123-evidence-delta.md#39-w2-intake-on-the-u-tree),
M-9).

## Request

Routing, which the coordinator schedules:

- `design`(intrinsics) and `dev`(intrinsics) make the check recognise a
  value it must not judge, for example by exempting an immortal header.
- `dev` adds a unit row with a stack-placed value that stays silent and a
  freed heap value that still fires.

## Completion evidence

- The program above runs armed, exits 3 and prints its counters.
- A planted stale release of a heap value still stops armed.
