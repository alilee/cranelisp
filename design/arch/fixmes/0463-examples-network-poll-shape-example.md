---
number: 0463
target: /examples
filed_by: /examples
filed_at: 2026-07-02
sprint_filed: 99
refers_to: examples/plan-examples.md, examples/34-async-io-leaf.cl, examples/32-concurrency-combinators.cl, tests/examples.rs, exemplar/platforms/web/src/lib.rs, platforms/poll-pool/src/lib.rs
status: open
---

# Add a poll-shape network leaf example to the learning sequence

## Current state (verified 2026-09-24)

- The sequence teaches the concurrency combinators (example 32) and the
  async poll-leaf mechanism (example 34), but not the network
  `accept` → `read` → `send` leaf shape. That shape exists only in the exemplar
  web platform, which examples must not depend on (the stdlib-separation
  design principle in root `CLAUDE.md`).
- No shared platform under `platforms/` binds a socket or offers a client
  `connect` leaf. `platforms/poll-pool` arms timers only.
- `tests/examples.rs` runs each example as a bare `--run` subprocess and checks
  its exit code. An idle-armed server never exits under that harness, and the
  harness has no client, deadline or kill driver.

## Remaining obligation

Add one small, free-standing example teaching the network poll-leaf shape at
minimum scale (a single request, not a server), playing green with a
deterministic exit code. It is blocked until either enabling path exists:

- a shared socket platform DLL with poll-shape `accept`/`read`/`send` leaves
  and a client `connect` leaf, so one `--run` can self-drive over loopback
  (platform owner, with `arch` for shared-versus-exemplar placement); or
- an examples-harness driver that runs the example as a server beside a
  client with a readiness deadline and kill-on-drop (`qa`/`test` with
  `training`), as `tests/exemplar_web.rs` does for the exemplar.

This is a learning-sequence gap, not a compiler defect. Re-check the trigger
at each `training` pass rather than restating the blockers here.

## Closure

The example lands in the sequence and plays green in the examples harness.
