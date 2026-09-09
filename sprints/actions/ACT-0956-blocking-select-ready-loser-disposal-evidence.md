---
id: ACT-0956
title: Pin blocking Select ready-loser disposal in the oneshot handoff
status: open
priority: future
from: review
to: test
sprint: 121
filed_at: 2026-09-05
refers_to:
  - crates/cranelisp-intrinsics/src/io.rs
  - crates/cranelisp-intrinsics/src/io/tests.rs
  - spec/10-io.md §10.12.9
---

## Request

Add one deterministic nonzero-disposer test in which a blocking Select loser
has already placed a successful owning result in its oneshot channel, but its
branch future is cancelled before polling that result as ready. Prove that
dropping the remaining Select futures drops the channel payload and invokes the
disposer exactly once.

This is additional evidence for the existing RAII ownership path, not a request
for a new runtime mechanism, public API, ABI or language-specification change.

## Completion evidence

- A barrier controls result publication and loser cancellation without a
  wall-clock-only oracle.
- The nonzero disposer observes the exact returned value exactly once.
- A winner-transfer control remains undisposed until its caller consumes it.
