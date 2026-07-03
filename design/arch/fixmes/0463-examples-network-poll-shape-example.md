---
number: 0463
target: /examples
filed_by: /examples
filed_at: 2026-07-02
sprint_filed: 99
refers_to: examples/plan-examples.md §2, examples/32-concurrency-combinators.cl, tests/examples.rs, exemplar/platforms/web/src/lib.rs, platforms/poll-pool/src/lib.rs
status: open
---

# Add a poll-shape network/platform leaf example to the learning sequence

## Issue

The learning sequence teaches the concurrency **combinators**
(`examples/32-concurrency-combinators.cl` — `race`/`select`/`timeout`/`sleep`
over the `primitives` builtins) but has **no example of a poll-shape
network/platform leaf** — the "server with no `spawn`" / `accept`→`read`→`send`
shape. That showcase currently lives ONLY in `exemplar/main.cl` (the full
Sudoku web server), which is not in the teaching sequence. A learner following
`examples/` never sees how a poll-shape platform leaf is bound and driven from
cranelisp.

A Sprint-99 close-out feasibility pass concluded a green-playing free-standing
example is **not cheap** — it needs infrastructure that does not exist and
cannot be added under the `examples/`-only edit budget. The three blockers:

1. **No free-standing poll-shape network leaf exists.** The only real
   `accept`/`read`/`send` poll leaves are in `exemplar/platforms/web/`
   (`bind-listener`/`accept-conn`/`read-conn`/`send-conn`). Examples are
   **forbidden to depend on the exemplar** (root `CLAUDE.md` §"Stdlib
   separation": tests/examples are free-standing; only `exemplar/` and
   `src/main.rs` may reach past the language). The shared platform that *looks*
   closest — `platforms/poll-pool` — is armed-**timer** test leaves
   (`poll-read`/`poll-write` `wake_on_timer` then return `ms`); it exercises the
   poll carrier and the token/capacity pool but does **no real socket
   accept/read**, so it does not teach the network shape. No shared
   (non-exemplar) platform binds a socket (`grep TcpListener|accept-conn
   platforms/` → none).

2. **The examples harness cannot drive a server.** `tests/examples.rs` runs
   each example as a bare subprocess `--run examples/NN.cl` and asserts the
   process exit code equals the sum of in-program sub-test pass counts. A real
   `accept`/`read` server needs an **external client** to connect, and a bare
   foreground `--run` on an idle-armed server **hangs forever** (the S98 `0479`
   idle-armed-server-survives caveat — an idle `accept` is armed on its listener
   fd, so the reactor never declares deadlock and never exits). The umbrella has
   no spawn/client/timeout/kill machinery (only signal-exit normalisation), so a
   server example cannot produce a deterministic exit code under it.

3. **Self-driving needs a client-connect leaf that no platform has.** A
   single-process example that binds an ephemeral port AND connects to itself
   (loopback) to stay deterministic would need a **client `connect` leaf** in
   addition to `accept`/`read`. The web platform has no client-connect effect;
   neither does any shared platform. That is new platform-DLL work.

## Proposed resolution

Deferred by design — pick this up only when the enabling infra lands, then add
ONE small example (`examples/33-network-poll-leaf.cl` or similar) teaching the
poll-shape `accept`→`read`→`send` leaf shape at minimum scale (a single-request
echo or fixed-response handler, NOT a full server). It must teach the *shape*,
stay free-standing (zero `stdlib/`, no exemplar dependency), and play green in
the examples harness with a deterministic exit code.

Enabling infra it needs (any one path unblocks it):

- **A free-standing shared network platform DLL** under `platforms/` (e.g.
  `platforms/net-echo`) exposing poll-shape `accept`/`read`/`send` leaves —
  ideally *plus a client `connect` leaf* so a single `--run` can self-drive
  (bind ephemeral port → connect to self → accept → read → send → assert →
  exit N), sidestepping both the external-client and the hangs-forever
  problems. Owner: `/platform` (with `/arch` for the shared-vs-exemplar
  placement call). This DLL would need symlinks into `examples/lib/platforms/`
  the way `stdio`/`test-capture` are wired, or discovery via the same
  `target/debug` platform-search-path `tests/examples.rs` already uses.
- **OR** an examples-harness extension that spawns the example-as-server plus a
  driving client with a readiness deadline and kill-on-drop (the shape
  `tests/exemplar_web.rs` already implements for the exemplar). This is a
  `/qa` + `/examples` harness change, larger than the current exit-code
  umbrella, and would move the example out of the plain `--run` umbrella into a
  bespoke test.

Until one of those exists, the poll-shape network showcase stays in the
exemplar only, and the learning sequence keeps the combinators example (32) as
its concurrency capstone.

## S101 Phase-6a readiness re-check (2026-07-03, /examples)

All three blockers re-verified STANDING at S101 Phase 6a: `platforms/` still
contains no socket leaf (`grep accept|connect|TcpListener platforms/` hits
only comment prose in `poll-pool`/`pool-demo`), no client-connect leaf exists
anywhere, and `tests/examples.rs` remains the bare exit-code umbrella. S101
(redefinition machinery + vec fn-as-value fix) landed nothing enabling. NOT
ready to headline 6b; remains deferred pending `/platform` net-leaf or `/qa`
harness-driver infra per the resolution paths above.

## Operational implication / Context

This is close-out housekeeping, not a headline gap — a learner still meets the
full concurrency *model* via example 32 (control combinators) and examples 28/30
(inferred parallelism); only the platform-leaf *authoring* shape is
exemplar-only. Cost to force it now (new platform DLL + client-connect leaf +
harness driver) far exceeds the "one focused `.cl` + plan entry" budget a
learning-sequence example is meant to be, so it is filed rather than forced.
Natural trigger: the next `/platform` sprint that produces a free-standing
network leaf, or a `/qa` harness sprint that adds server-example driving.
