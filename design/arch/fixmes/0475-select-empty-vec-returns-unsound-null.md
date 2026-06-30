---
number: 0475
target: /int
filed_by: /sprint
filed_at: 2026-06-29
retargeted_by: /spec
retargeted_at: 2026-06-30
sprint_filed: 96
refers_to: spec/10-io.md §10.12.8 ("Empty `select`"), spec/12-runtime.md §12.4.4, crates/cranelisp-intrinsics/src/io.rs (run_select_node, ~io.rs:496-500)
status: open
---

# Implement the spec-ruled empty-`select` runtime error (currently returns Unit `0`)

## Spec ruling (now normative — actioned by /spec S96)

`/spec` has ruled the empty-`select` behaviour. `spec/10-io.md §10.12.8`
("Empty `select`") and `spec/12-runtime.md §12.4.4` ("Collection and duration
units") now state, normatively:

> `(select [])` over an empty vector has no branch that can win and no value to
> return. It MUST raise a runtime error (§12.7.2) — the same class of
> recoverable fault as match non-exhaustion or division by zero — rather than
> return a value. Returning a synthesised value is non-conforming: at a
> heap-typed `a` an `Int`-`0` placeholder is an unsound null pointer …; a
> "never completes" hang is also non-conforming.

The runtime-error choice was selected over "never completes" (a guaranteed
deadlock) and over the as-built return-`0` (an unsound null at heap-typed `a`).
An empty `select` is a recoverable fault — catchable via `catch-runtime-error`.

## Implementation owed (/int)

The C3 runtime `run_select_node` (`crates/cranelisp-intrinsics/src/io.rs`,
~io.rs:496-500) currently returns Unit `0` for an empty branch `Vec`. Align it
to the ruling: raise a language-level runtime panic — message
**"select over empty collection"** — via the standard `runtime/panic` path
(§12.7.2), so it is recoverable at a `catch-runtime-error` boundary and is
fatal-to-the-evaluation otherwise.

## Test owed (/qa)

A narrow e2e: an empty `select` instantiated at a **heap-typed** `a` (e.g. a
`String`/ADT result) MUST surface the runtime error (catchable, or fatal under
`--run`/`--link`), NOT a `0`/garbage value or a hang. Add per
`memory/feedback_failing_not_ignored.md` — failing-not-ignored until /int lands
the fix, with a `// spec: spec/10-io.md §10.12.8 (Empty select)` annotation.

## Operational implication / Context

Low severity: no current program constructs an empty `select` (race is always
binary; n-ary `select` fixtures are non-empty). The unsoundness is latent until
user code can produce an empty branch list. Forward-routed (A3 precedent).
