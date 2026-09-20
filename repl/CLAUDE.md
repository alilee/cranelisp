# repl/

REPL experience specification for Cranelisp. The `spec` role owns the
normative specification; `test` owns the demos and harness.

## Authority

This directory contains the **normative REPL experience specification** — what a conforming Cranelisp REPL must do from the user's perspective. This is distinct from:

- `spec/` — language spec (owned by `/spec`): defines language semantics, not REPL behavior
- `design/` — implementation design (owned by `/arch` and developer skills): how the REPL is built

The REPL spec defines the **contract between the REPL and the user**: display formats, commands, error presentation, self-documentation, discoverability, and performance. Implementation plans for meeting this contract live in `design/`.

It encompasses the entire user experience from invoking the repl as well as its associated CLI invocation modes, exit codes, batch output format, and cache lifecycle.

## Files

| Collection | Purpose |
|---|---|
| `repl-specification` | Current REPL and CLI specification, including its compatibility entry point and section index. |

The collection is `spec.md` (compatibility entry point), `spec/index.md`
(front matter, design principle and section map) and the numbered
`spec/*.md` sections.

| File | Contents |
|---|---|
| `showcase` | Top-level showcase script — builds binary, plays demos |
| `demos/` | `.demo` scripts, demo player (`demo-player.py`), and [local ownership and guidance](demos/CLAUDE.md) |

## Conventions

- Requirements use RFC 2119 keywords (MUST, SHOULD, MAY)
- Each requirement is testable — it can be verified by an E2E test or REPL session transcript
- Display format examples show exact expected output (whitespace-significant)
- Performance targets are measurable (wall-clock thresholds)
- Requirements are tagged with the sprint where they become testable (`[S{M}]`; pre-S64 ring tags in older rows are historical)

## For the `spec` role

When REPL behavior needs to change:
1. Update the owning section under `repl/spec/` first (the normative contract)
2. Then update tests and implementation to match

The `qa` and `test` roles consume this specification for REPL experience tests
at the e2e tier.
