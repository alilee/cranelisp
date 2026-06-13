---
number: 0021
target: /qa
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint61_observability_io.rs:421, design/backend/io-trampoline-trace.md §9 AC 2
status: open
migrated_from_inline: true
---

# 0021 — Author criterion-style microbenchmark for IO-trace off-path overhead

## Issue

S61 Wave 5 placeholder: author a proper criterion-style microbenchmark alongside `cargo nextest run --ignored` that compares `record_event` filter-off cost against a no-op baseline at nanosecond resolution, yielding the <1% bound per `design/backend/io-trampoline-trace.md §9 AC 2`. Integration-test ceilings cannot substitute for microbenchmark-level measurement.

The current test (`io_trace_off_path_subprocess_completes_within_generous_ceiling`) asserts a much weaker structural property: running the program twice with `CRANELISP_IO_TRACE` unset completes within a generous 5-second ceiling. This proves the "unset" path isn't catastrophically slow but does not bound the actual overhead per AC 2.

## Source location

`tests/sprint61_observability_io.rs:421` (FIXME above `io_trace_off_path_subprocess_completes_within_generous_ceiling`); also referenced in the same test's assertion message at line 443.

## Context

Sprint 61 Slice 0 acceptance criteria require the trace-off overhead to be <1% of baseline. The integration-test ceiling is a placeholder until the microbenchmark harness lands.

## Proposed resolution

`/qa` adds a `criterion`-driven benchmark that toggles `CRANELISP_IO_TRACE` on/off and measures `record_event` cost at nanosecond resolution. Tighten the integration ceiling once the benchmark establishes the actual bound.

## Status (S81 W-H) — BLOCKED on /int FIXME 0336

The user ruled this relocates to a **release-mode bench**. The bench must call
`record_event` **in-process** at nanosecond resolution (a subprocess-driven
measurement gives a weak signal that fails the `<1%` AC — process-spawn + I/O
jitter swamps the nanosecond signal). But `cranelisp` (`src/`) is `[[bin]]`-only,
so a `benches/` criterion bench cannot import `record_event` / the observability
internals.

Filed **FIXME 0336 (`target: /int`)** requesting either a `[lib]` target or a
`pub` bench accessor for `record_event` so the release-mode bench can call it
in-process. This FIXME stays `target: /qa` and `status: open` — the bench
relocation (author the criterion bench, establish the bound, tighten the
integration ceiling) is /qa's once 0336's accessor exists.
