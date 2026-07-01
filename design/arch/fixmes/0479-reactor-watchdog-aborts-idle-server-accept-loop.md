---
number: 0479
target: /int
filed_by: /port
filed_at: 2026-06-30
sprint_filed: 96
refers_to: crates/cranelisp-intrinsics/src/reactor.rs (block_on_reactor MAX_TOTAL_BLOCK watchdog, ~:1555), design/intrinsics/reactor.md, design/arch/effect-concurrency.md §3 (server = reference workload)
---

# Title — the reactor watchdog aborts a legitimately-idle server accept loop after 30s

## Issue

`block_on_reactor` has a `MAX_TOTAL_BLOCK` watchdog (~`reactor.rs:1555`,
`exceeded 30s — leaf never completed`) intended to catch a STUCK poll leaf (a
deadlock / a leaf that never readies). But a long-running server's `accept` leaf
**legitimately** blocks indefinitely waiting for the next client connection. With
no traffic for 30s the watchdog fires and aborts the server — surfaced by the S96
marquee web server (exemplar + `tests/fixtures/web_fanout`): an idle server dies
at 30s. The e2e rows pass only because the test harness drives traffic and kills
the child well under 30s.

This is **pre-existing** (the `accept` leaf was always a poll leaf, so the old
serial exemplar had it too) and was noted repeatedly across S96 as "the 30s
infinite-server idle-cap backstop." It directly limits the marquee's stated goal
(`effect-concurrency.md §3`: the web server is the reference workload, "what makes
a server survive the open internet") — a server that cannot idle waiting for
connections is not production-shaped.

## Proposed resolution

The watchdog must distinguish "legitimately parked on an external I/O leaf with no
deadlock" from "stuck / no-progress." Options for /int to weigh:
- Make `MAX_TOTAL_BLOCK` a no-progress watchdog (reset the timer whenever ANY
  strand makes progress / any leaf readies), so a server that is merely idle (but
  healthy) never trips it, while a genuine deadlock (no progress anywhere) still
  does.
- Disable / make-configurable the total-block cap for a long-running server/REPL
  drive (vs a one-shot `--run` where a 30s cap is a reasonable hang guard).
- A server-mode signal (the program never terminates by design) that opts out of
  the one-shot cap.
Whichever: a healthy idle server must stay up indefinitely; a real deadlock must
still be caught. Pin the chosen behaviour in `design/intrinsics/reactor.md` and add an
e2e (a server idle > the old cap then served) once it's no longer self-defeating.

## Operational implication / Context

Does not affect any current e2e (all drive traffic < 30s). It is the gap between
"the marquee server fans out + serves + survives faults" (delivered S96) and "the
marquee server can actually run unattended" (this). Filed as the honest-scope
record so the limitation is tracked, not silently shipped as "production server."
