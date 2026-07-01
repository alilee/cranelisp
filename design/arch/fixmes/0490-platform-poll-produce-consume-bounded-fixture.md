---
number: 0490
target: /platform
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: platforms/poll-pool/src/lib.rs, tests/fixtures/ (build-link-prereqs.sh), tests/concurrency_v9_abi.rs::produce_consume_descriptor_no_rc_leak (2.4)
status: open
---

# G-C: bounded `poll-produce` / `poll-consume` fixture leaves for the v9 RC-leak guard (2.4)

## Issue

The v9 layout guard `tests/concurrency_v9_abi.rs::produce_consume_descriptor_no_rc_leak` (2.4) is RED because it needs **bounded `poll-produce` / `poll-consume` test-support leaves** that don't exist. The guard asserts a produce→consume→retire cycle over an opaque `Connection [fd]` has ordinary 1-field-ADT alloc/free balance (no leaked region) under the ctx-vtable model — but with no bounded produce/consume fixture leaves it can't drive a deterministic RC-balanced cycle (a real network server's RC trace is non-deterministic). Carried through S97 as `// FIXME(/sprint S97 W3)`.

## Proposed resolution

/platform: add minimal bounded `poll-produce` (Produce role → mints a handle) + `poll-consume` (Consume role → operates on the handle) leaves to `platforms/poll-pool/` (sibling to the existing `poll-no-interest`/`poll-read`/`poll-log` test leaves), wired into `build-link-prereqs.sh`. Then /qa flips 2.4 green (or, if a fixture is genuinely infeasible, 2.4 reduces to the /dev intrinsics RC-balance unit — record which). The 2.4 RED is the durable record.
