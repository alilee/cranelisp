---
number: 0273
target: /stdlib
filed_by: /arch
filed_at: 2026-06-06
sprint_filed: 76
target_sprint: 77
refers_to: design/arch/test-discovery.md §4.3 "the in-language runner over discovered pairs" + §5 "Overloads" + §6 "Stdlib / REPL — the runner and the slash command", stdlib/testing/runner.cl
status: open
---

# Stdlib: in-language test runner over discovered pairs + the `discover-tests` no-arg/single-String sugar

Crate: `stdlib/` (`/stdlib`). Normative spec: `design/arch/test-discovery.md` §4.3/§5/§6.
Depends on FIXMEs 0269–0271 (the `discover-tests` extern + `catch-runtime-error` +
Pair/Result seeds) being available. Free-standing of the compiler — ordinary in-language
code over the discovered pairs.

## Scope

1. **The in-language runner** in `stdlib/testing/runner.cl` — ORDINARY functions (NO
   macro; the fn-value return makes a name→callable macro unnecessary — that is the whole
   point of ruling 1). Over `(Vec (Pair String (Fn [] (Option String))))`:
   - `run-one` folds the THREE-WAY outcome per test: `(catch-runtime-error run)` is
     `(Result (Option String) String)` → `(Err msg)` = PANIC, `(Ok None)` = ok,
     `(Ok (Some why))` = assertion FAIL.
   - `run-all` = `(map run-one (discover-tests))`.
   - `run-matching` = `map run-one` over a `filter` on the pair name — selection in-language,
     fresh every call because the callables are late-bound through the live GOT.
   - Add the present/report helpers (pass/fail tallies, formatting) as plain stdlib code.
2. **The `discover-tests` sugar overloads** — the no-arg `(discover-tests)` (current
   module) and single-`String` `(discover-tests "mod")` shapes normalise to the canonical
   `(discover-tests [<path>…])` `(Vec String)` form via a stdlib macro (q-overload — ONE
   extern + normalising sugar, NOT `DefKind::Overloaded`). The no-arg form bakes the
   caller's module path as a literal `String` arg. The int extern (FIXME 0271) takes only
   the `Vec String`; this sugar is the stdlib half.
3. **Prelude re-export choice** — whether the prelude re-exports `discover-tests` /
   `catch-runtime-error` / `Pair` / `Result` for bare-name convenience (vs. import from
   `primitives`) is a stdlib packaging choice, not a language question — `/stdlib`'s call.

## `/repl` coordination note (no separate FIXME — light touch)

`/run-tests` stays a fast Rust path OR is re-pointed at this in-language runner — that is
**int's call**, not a spec concern (§6). If `/run-tests` becomes sugar over the runner,
`/repl` updates `repl/spec.md` §16 narrative to match (the pairs-and-combinator shape,
the freshness property, the `--link` interim behaviour). Surfaced here so `/stdlib` and
`/repl` coordinate; if it grows beyond a note, `/repl` files its own FIXME.

## Acceptance

- `(run-all)` runs every eligible `test-*` in the current module and folds panic/pass/fail
  three-way; `(run-matching substr)` selects a subset and stays fresh after a new test is
  defined. Demo through the real REPL before declaring done (per `feedback_demos.md`).
- Tests + examples remain free-standing (zero dependency on `stdlib/`) — the runner is
  stdlib, exercised by the exemplar / production binary, NOT by `tests/`.
