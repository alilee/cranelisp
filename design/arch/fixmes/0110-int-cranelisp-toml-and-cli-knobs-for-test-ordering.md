---
number: 0110
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/plan/helpers.md §"Configuration: Cranelisp.toml + CLI options", design/int/cranelisp-toml.md
status: open
---

# Expose worker-count and scheduler-tuning knobs via `Cranelisp.toml` + CLI

## Issue

(Sprint 64 reframe — original framing was "global deterministic output mode"; user feedback rejected that as overdone.)

The e2e harness needs to control event-ordering-affecting binary behaviour for tests that assert on scheduler traces, worker interleaving, or cache-hit races. Test-side exclusion via the regex helper library covers content that is non-deterministic but doesn't matter (timing values, allocation pointers); test-side configuration via `Cranelisp.toml` + CLI flags covers ordering that DOES matter.

The harness exposes builder methods (`workers(n)`, `no_cache()`, etc., per `tests/plan/helpers.md` §"Configuration: Cranelisp.toml + CLI options"). Those methods need a corresponding binary surface to write to.

## Proposed resolution

`/int` confirms / extends `Cranelisp.toml` schema and corresponding CLI flags for at least:

1. **`[scheduler] workers = N`** — pin worker thread count. Setting `workers = 1` gives serial event emission for deterministic scheduler-trace tests.
2. **`[scheduler] quantum_ms = N`** (optional, lower priority) — pin worker scheduling quantum for fine-grained ordering control.
3. **`[cache] enabled = false`** — disable on-disk module cache for tests exercising fresh-compile paths.
4. **`[repl] show_times = false`** (and CLI flag `--no-times-in-prompt`) — suppress timing data from the REPL prompt, slash-command output (`/time`), and any other prompt-adjacent timing surface. Required for stdin-scripted REPL e2e tests using `assert_stdout_eq` — the prompt shape must be byte-stable across runs. The default (timings shown) stays; tests opt into the suppression.
5. **CLI flag equivalents** for the above (e.g., `--workers=1`, `--no-cache`, `--no-times-in-prompt`) for tests that prefer flag-based config to dropping a `Cranelisp.toml`.

Schema decisions are `/int`'s call. The harness adapts to whatever the binary exposes; `tests/plan/helpers.md` is updated when the surface lands.

The original blanket "deterministic output mode" framing (suppressing timing, alloc-pointer hex, worker interleaving from output) is **NOT** required. Tests handle non-determinism via:

- The regex helper library (`compiler::time_line()`, `compiler::alloc_addr()`, etc.) for content that varies in shape but doesn't affect correctness.
- The configuration knobs above for ordering that affects test assertions.

## Operational implication / Context

Bundles naturally with `design/int/cranelisp-toml.md` work — `/int` may already have a partial schema; this confirms the test-required keys land. Adjacent: FIXME 0111 (trace channel separation) and FIXME 0112 (REPL ready sentinel) are the other two `/int`-side dependencies for the e2e harness. All three are independent and can land in any order; per FIXME 0115 they should land before the dedicated test-port sprint begins.

Lower scope than the original 0110 framing — about half a day of `/int` work, not multi-day binary-wide change.
