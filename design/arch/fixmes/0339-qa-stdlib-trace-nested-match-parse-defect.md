---
number: 0339
target: /qa
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: stdlib/core/trace.cl (format-params, lines ~36-40), stdlib/testing/runner.cl (retired run-tests refs), spec/06-pattern-matching.md (match arm grammar)
status: open
---

# `stdlib/core/trace.cl` nested `match` fails to parse (`match requires scrutinee and arms`)

## Issue (Phase-6a /stdlib finding, S81)

`stdlib/core/trace.cl`'s `format-params` (lines ~36-40) fails to parse:
`parse error: match requires scrutinee and arms` — isolated to that single form. The
flattened bracket-arm `match` form parses fine at one level (verified elsewhere), but this
**nested** `match` (a `match` whose arm expression is itself a `match`) defeats the current
parser's arm-boundary detection — the parser cannot disambiguate where one arm's expression
ends and the next pattern begins when a pattern is a bare symbol used as a mid-arm expression.

**Pre-existing** (predates the S81 0266 trace change; NOT a regression) and **gated** — it
surfaces only when a program explicitly imports `core.trace` / `testing.runner`; the default
REPL + `--run` prelude path is unaffected (prelude loads green, RC=0).

Sibling stale defect (same subtree): `stdlib/testing/runner.cl` (line ~56) calls the **retired
`(run-tests …)` special form** (`compile_run_tests` was deleted) and imports the broken
`core.trace` — it is superseded by the FIXME 0273 in-language runner (`discover-tests` /
`catch-runtime-error`).

## Proposed resolution

1. **/qa authors a minimal failing repro** of the nested-`match` parse failure (the isolated
   `format-params`-shaped form, no stdlib). This decides ownership: if the nested flattened-arm
   form is **valid grammar** the parser mishandles → **`/frontend`** fixes the parser; if the
   form is **invalid as-written** → **`/stdlib`** rewrites it (split helper / non-nested shape).
   `// spec:` → spec/06-pattern-matching.md (match arm grammar).
2. The `testing/runner.cl` retired-`run-tests` issue is subsumed by **FIXME 0273** (/stdlib
   rewrites it as the in-language runner) — no separate FIXME needed.

## Context

Phase-6a /stdlib assessment, S81. 0273 (the in-language test runner) is fully unblocked
(`discover-tests`/`catch-runtime-error`/`Pair`/`Result` all landed + importable); fixing this
parse defect is a prerequisite for any runner that imports `trace-show-tree` and for `core.trace`
display fns to be usable at all.
