---
number: 0111
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/plan/helpers.md §"Trace toggles", tests/plan/PLAN.md §"Testability gaps in the binary surface", repl/spec.md §5.1
status: open
---

# Trace output channel separation — let the harness assert "stderr is traces only"

## Issue

`repl/spec.md §5.1` is normative: errors go to stdout; stderr is
reserved for traces and diagnostic output. The negative companion
of the spec rule is "no non-trace lines on stderr" — which means the
e2e harness needs to distinguish trace lines from non-trace lines
on the stderr stream.

Today the `CRANELISP_*_TRACE=1` envs all emit to stderr without an
unambiguous tag. A test cannot reliably write
`assert_stderr_traces_only()` because the parser cannot tell a
trace line ("[rc] alloc 0x...") apart from a stray
`eprintln!("warning: ...")` from somewhere in the binary.

The two ways to break the spec rule are:
1. An error message lands on stderr (should be on stdout).
2. A non-trace diagnostic lands on stderr without a trace tag
   (the spec allows it as "diagnostic output" but the harness
   cannot verify the spec rule without a tag convention).

## Proposed resolution

Two workable shapes; either resolves the testability gap:

**Option A — line prefix.** Every trace emission writes lines with
a stable prefix matching `^\[trace:[a-z_]+\]` (e.g.,
`[trace:rc] alloc tok-123 size=24`,
`[trace:scheduler] worker-0 claim user`,
`[trace:io_trampoline] enter print`). The harness can then split
stderr into trace-vs-non-trace by regex match on the prefix. Lines
without the prefix are assumed non-trace and asserted absent under
`assert_stderr_traces_only()`.

**Option B — separate file.** Add an env var `CRANELISP_TRACE_FILE=path`
(or per-channel: `CRANELISP_RC_TRACE_FILE=...`, etc.) that redirects
trace output to the named file. The e2e harness creates a tmpfile,
sets the env, reads the file after the process exits, and is then
free to assert `stderr.is_empty()` for the no-non-trace check.

Option A is lower-impact (no new file plumbing) but requires
auditing every existing trace-emission site to add the prefix.
Option B is more invasive but gives a sharper separation. `/int`
chooses; `/qa` consumes either via the helper API.

## Operational implication / Context

This is the dependency for `CrOutput::assert_stderr_traces_only()`
in the e2e helper API (see `tests/plan/helpers.md`) and for one of
the negative-coverage candidates carried forward from Sprint 61
(`repl/spec.md §5.1` neg promotion — see the legacy
`tests/plan/legacy/neg-coverage-candidates.md` for the original
analysis).

Once landed, `/qa` updates the harness to parse stderr into
`stderr_traces` + `stderr_non_trace` and adds the
`§5.1`-stderr-clean assertion to the relevant e2e tests.

Suggested correlation with FIXME 0103 (trace.rs/io_trace.rs
relocation to int) — if the trace plumbing is being moved as part
of 0103, channel-separation is a natural addition.
