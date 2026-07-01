---
number: 0495
target: /design
filed_by: /dev
filed_at: 2026-07-01
sprint_filed: 98
refers_to: design/intrinsics/reactor.md §2.4 (block_on_reactor doc), §2.12 (supervisor / no-progress cap), §8 (idle-server watchdog)
status: open
---

# reactor.md §2.12/§2.4 supervisor-exemption + backstop-termination need reconciling with §8.3

## Issue

Implementing FIXME 0479 (S98 band C — the idle-server watchdog knob, flips test
`5.1B` `idle_armed_server_survives_then_serves`) surfaced two doc statements that
contradict the §8.3 intent the same doc states:

1. **Supervisor no longer holds off the OneShot wall-clock backstop.**
   `reactor.md §2.12` (≈"the `MAX_TOTAL_BLOCK` no-progress cap must NOT fire while
   the supervisor is non-empty") and the §2.4 `block_on_reactor` doc-comment ("It
   measures only time during which … the supervisor is empty") say a **non-empty
   supervisor exempts the backstop**. But §8.3 states the OPPOSITE for the case
   that actually occurs: "a one-shot **armed-but-hung** still hits the OneShot
   wall-clock backstop." An idle server with a **parked/hung handler strand** (a
   handler reading a peer that never sends — exactly what the `5.1B` readiness
   probe leaves behind) is armed-but-hung: with the §2.12 exemption the backstop
   is suppressed and the server never aborts (`5.1B` Case B stays wrongly alive).

   **As-implemented (S98):** the OneShot no-progress deadline is held off ONLY by
   `pending_bridges > 0` (genuine off-thread blocking work, uncapped to match
   feature-off, §2.6) — NOT by a merely-non-empty supervisor. The supervisor stays
   in the **armed-ness deadlock detector** (`reactor_is_armed`) so a parked strand
   is not mis-read as a deadlock; it is dropped from the **wall-clock backstop**
   hold-off. A finite program whose supervised strands genuinely PROGRESS drains
   and returns before the window; only an armed-but-hung strand reaches the cap.
   The rule is modelled as the pure predicate `oneshot_backstop_action` (which by
   construction takes no supervisor input). Please reconcile §2.12 + the §2.4
   doc-comment to match §8.3 (supervisor exempts the DEADLOCK detector, not the
   wall-clock hang backstop).

2. **The fired backstop now exits cleanly (non-zero) instead of panic→SIGABRT.**
   §8 says the backstop "aborts the drive by ≈backstop" without pinning the
   termination mechanism. The as-built `panic!` propagated into the
   `cannot_unwind` `cranelisp_run_program` boundary, raising `SIGABRT` and
   **core-dumping the (large) process — ~1.1s of latency**, which made a hung
   program linger ~1.1s past its own deadline (measured: backstop 2000 ms → death
   ~3.15s; `5.1B`'s window is idle 3000 − backstop 2000 = 1000 ms, so the coredump
   latency alone blew the budget). Since the backstop firing is a **deliberate
   host-policy termination of a hung batch program — not a bug/crash** — the
   production drive (`block_on_reactor`) now `std::process::exit(70)` cleanly (fast,
   no coredump, diagnostic to stderr). The unit-test seam (`block_on_reactor_capped`
   called directly) keeps `panic!` (via an `OnBackstop::Panic` knob) so
   `#[should_panic]` still observes the trip. Please record the clean-exit
   termination (+ the `70` exit code) in §8 so a future reader does not
   "restore" the panic.

## Proposed resolution

Revise `reactor.md`:
- §2.12 + §2.4 doc-comment: the supervisor exempts the **armed-ness deadlock
  detector** (`reactor_is_armed` — a non-empty supervisor is wakeable, not a
  deadlock), but does **NOT** hold off the **OneShot wall-clock hang backstop**
  (only `pending_bridges > 0` does). Cite §8.3 as the governing rule.
- §8 (or §8.2/§8.3): pin that the fired OneShot backstop **terminates the
  production drive with a clean non-zero `process::exit` (code 70), not a
  panic→SIGABRT/core-dump**; the unit-test seam retains `panic!`.

## Operational implication / Context

Both are already implemented (S98 band C, `crates/cranelisp-intrinsics/src/reactor.rs`
— `oneshot_backstop_action` + `OnBackstop`; unit `oneshot_backstop_action_ignores_supervisor_holds_off_only_on_bridge`; e2e `5.1B` GREEN). This FIXME only asks
`/design` to bring the prose (§2.4/§2.12/§8) into line with the shipped behaviour
so the doc and code agree. No further code change is requested.
