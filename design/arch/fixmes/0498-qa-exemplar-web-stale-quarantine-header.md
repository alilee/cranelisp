---
number: 0498
target: /qa
filed_by: /port
filed_at: 2026-07-01
sprint_filed: 98
refers_to: tests/exemplar_web.rs (the STILL-QUARANTINED / STILL-IGNORED header block above exemplar_web_server_serves_form_solution_and_not_found_over_http)
status: open
---

# `tests/exemplar_web.rs` header still says the test is `#[ignore]`'d / quarantined — but it is un-ignored and GREEN (0494 closed)

## Issue

`tests/exemplar_web.rs` carries a large comment block (≈ lines 209–254) above
`exemplar_web_server_serves_form_solution_and_not_found_over_http` that states
the test is "STILL QUARANTINED (S97, /backend)", "STILL IGNORED (S98 finding,
FIXME 0486)", and `#[ignore]`'d behind the deterministic repro, plus two
`FIXME(/backend)` inline comments describing the launched-strand double-free.

That is now stale. Bug #2 is CLOSED (0494, `5ca6ef2`): the `send-conn`
poll-effect borrowed-arg RC double-free was fixed in `find_var_type_in_expr`
(traverses `LaunchContinue`/`ConstrADT`), FIXME 0486 was deleted, and BOTH
tests in the file are un-ignored and GREEN (verified this sprint: `cargo
nextest run --test exemplar_web` → 2 passed, and the marquee replay in the full
suite is green — 1795 passed). The header now contradicts the actual attributes
(no `#[ignore]` on either `#[test]`).

## Proposed resolution

/qa: rewrite the stale header block to reflect the closed state — the test is
un-ignored, serves the full Sudoku-over-HTTP showcase, and is the real-showcase
end-to-end validation that the 0494 fix holds (complement to the deterministic
guards `tests/launch_grid_corrupt.rs` / `tests/launch_vec_send_corrupt.rs`).
Retire the two old-protocol inline `FIXME(/backend)` comments (bug #2 closed).
Reassess the `FIXME(/qa — DEF-4)` `--link`-variant note against current `--link`
multi-module-platform status.

## Operational implication / Context

Doc-only staleness in a /qa-owned test file surfaced during the S98 Phase-6
exemplar v9 adoption + marquee replay (FIXME 0492). No behaviour change; the
tests pass. Cross-skill file ownership (root CLAUDE.md §Cross-Skill Changes) —
`/port` does not edit /qa's test file, so this is filed for /qa to action.
