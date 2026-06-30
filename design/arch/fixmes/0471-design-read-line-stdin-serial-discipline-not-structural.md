---
number: 0471
target: /design
filed_by: /dev
filed_at: 2026-06-29
sprint_filed: 96
refers_to: design/platform/poll-support.md §3.1, platforms/stdio/src/lib.rs (read-line COMMUTATIVE descriptor)
status: open
---

# `poll-support.md §3.1` over-claims stdin serial discipline — the `read-line` `Commutative` (token 0) descriptor does NOT structurally enforce single-in-flight

## Issue

The stdio `read-line` poll leaf carries a `Commutative` descriptor (`token 0,
cardinality 0, blocking 0`), so the backend injects the `(0, 1)` leading pair and
the admission gate is a **no-op** (`token == 0` ⇒ no permit acquired —
`io.rs::await_poll_node` step 2 / `reactor.rs::TokenPool::acquire`). The
`poll-support.md §3.1` framing — "stdin serial discipline is a host concern, not a
pooled resource" — is therefore an over-claim: with token 0 there is NO admission,
so nothing *structurally* prevents two concurrent in-flight `read-line`s from
racing the shared `STDIN_BUF`. Today that race cannot occur (the only `read-line`
caller is the serial stdio CLI, and the `STDIN_BUF` `Mutex` serialises the actual
byte reads), so it is a latent structural gap, not a live defect.

This is the Wave-B5 "read-line G7" Important. The robust fix would be a
**capacity-1 serial-stdin token** (`{token: !=0, cardinality: 1}`) so admission
enforces single-in-flight. But `read-line :: () -> IO String` takes **no operands**,
so it cannot carry a dynamic token via the leading-pair convention the
`ResourceSerial` leaves use (poll-pool reads its token from the leading cranelisp
arg). Making it serial would require the backend to inject a **fixed** stdin-token +
capacity-1 pair for a tokenless leaf — a new injection convention, not a small clean
change — plus it is a `/platform`-owned descriptor edit. Given the server demo uses
**web, not stdin**, this is off the critical path, and the host `Mutex` already
serialises the real reads.

## Proposed resolution

Pick the smaller sound option: **correct the `poll-support.md §3.1` over-claim** —
state honestly that `read-line` is tokenless (`Commutative`, no admission) and that
its single-in-flight discipline rests on the host `STDIN_BUF` `Mutex` + serial use,
NOT on the admission pool; note the capacity-1 serial-stdin-token alternative
(`{token: !=0, cardinality: 1}` + a fixed-token injection for a tokenless leaf) as
the structural-enforcement upgrade if/when concurrent stdin readers become reachable
(unmet trigger). This is the option `/dev` recommends: smaller, sound, no backend
injection-convention churn, no `/platform` descriptor change, and the latent race is
unreachable today.

## Operational implication / Context

- Off the S96 critical path: the headline server uses the `web` platform, not
  stdin. No acceptance row depends on stdin admission.
- `/dev` did NOT change the `read-line` descriptor — the robust fix (fixed-token
  injection for a tokenless `ResourceSerial` leaf) is neither small nor `/dev`-owned
  (the descriptor lives in `platforms/stdio`, `/platform`'s domain). The doc
  correction is the sound, in-scope resolution; if `/design` instead wants the
  structural token, that cascades to a `/platform` descriptor change + a `/backend`
  fixed-token injection convention.
