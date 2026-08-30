---
id: ACT-0947
title: Dispose of six tracked files at the repo root that nothing references
status: open
priority: advisory
from: sprint
to: sprint
sprint: 120
filed_at: 2026-08-30
refers_to:
  - NOTES.md
  - scratch_other.diff
  - default/test.cl
  - foo/test.cl
  - test1/Cranelisp.toml
  - testing/runner/test.cl
---

## Request

Six files are tracked at the repo root and referenced by nothing in `tests/`,
`src/` or `crates/`. All were committed 2026-07-22.

| Path | What it is |
|---|---|
| `default/test.cl` | probe fixture |
| `foo/test.cl` | probe fixture |
| `test1/Cranelisp.toml` | probe fixture |
| `testing/runner/test.cl` | probe fixture |
| `scratch_other.diff` | a 23KB working diff |
| `NOTES.md` | a personal idea list — REPL, LSP, wasm, browser Cranelift |

Confirm each is genuinely dead before removing it: these look like probe litter,
but `default/`, `foo/` and `test1/` are plausibly module-resolution fixtures
that a manual check exercised, and a fixture nothing automated references is
also a coverage observation rather than only clutter. If any is load-bearing for
a manual procedure, it needs a home and an owner rather than deletion.

Two consequences beyond the clutter:

- **`testing/` at the repo root shadows the `test` role's name**, so "the
  testing directory" is ambiguous in every dispatch that says it.
- This is precisely what METHOD §2.2 probe hygiene now forbids — *never write to
  the repo root; git-ignored is not the same as harmless, these files are
  inputs.* The rule postdates the mess and has never swept it, which makes this
  the rule's first application rather than a new finding.

`NOTES.md` is a separate judgment: it is the user's, not an agent artifact, and
its content is roadmap-shaped. Ask before touching it.

## Completion evidence

- Each of the six either removed, or given a stated owner and purpose.
- If any probe fixture is load-bearing, it moves under `tests/` with the manual
  procedure that uses it named.
- A note on whether `testing/` disappearing resolves the name collision, or
  whether the collision needs stating somewhere.
