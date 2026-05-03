---
number: 0112
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/plan/helpers.md §"Driving the REPL", tests/plan/PLAN.md §"Testability gaps in the binary surface"
status: open
---

# REPL "ready" sentinel — let scripted e2e tests drive request/response

## Issue

Scripted REPL e2e tests today work in a fire-and-forget shape: the
harness writes the entire stdin script, closes the pipe, waits for
the child to exit, then reads the entire stdout. This is sufficient
for one-shot transcripts ("define foo, call foo, expect 42") but not
for tests where the next input depends on the previous output.

Concrete shapes that need the dependency:

1. **Error recovery** — observe that an error appeared on stdout
   (per `repl/spec.md §5.1`'s "must not crash the REPL" clause),
   then send a recovery form and verify the session still works.
2. **Slash command timing** — observe `/list` output before and
   after a `(defn ...)`, asserting that the new defn is now in the
   list. With fire-and-forget the harness can only assert on the
   joined transcript, not on the delta.
3. **Reload tests** — write a `.cl` file, send `/reload`, observe
   the reload completed, then send a form that depends on the
   reloaded definition.

Without a sentinel, the harness has to either send all inputs
up-front (and lose the delta visibility) or rely on
fragile sleeps between sends (which is the `flaky` shape user
directive 2026-04-21 forbids).

## Proposed resolution

The REPL prompt line is the natural ready sentinel. Today its shape
varies (color codes when a TTY is detected, "user> " when not, etc.).
A small commitment makes it usable as a sentinel:

1. **Stable plain-text shape** when stdout is not a TTY — the form
   `<module>> ` with no ANSI escape sequences. (Some of this is
   already true via the `--no-color` mode; confirm and document.)
2. **Flushed before stdin read** — every prompt write does an
   explicit flush so the harness sees the prompt as soon as the
   REPL is ready for the next input, not buffered until the next
   write batch.
3. **No prompt suppression** when stdin is piped — the REPL emits
   prompts even when stdin is not a TTY. (Today's behaviour likely
   already works this way for transcript tests; document and pin
   it.)

The harness reads stdout line-by-line, treats `^[a-zA-Z][a-zA-Z0-9.]*> $`
as the ready sentinel, and uses it to gate stdin sends. Surface in
the helper API:

```rust
Cranelisp::new()
    .repl()
    .stdin_step("(defn f [] 1)")     // wait for prompt, then send
    .stdin_step("(f)")
    .expect_stdout_contains("1")     // before next stdin_step
    .stdin_step("(non-existent-fn)")
    .expect_stdout_contains("error:")
    .stdin_step("(f)")               // recovery
    .expect_stdout_contains("1")
    .output()
    .assert_ok();
```

The single-shot `Cranelisp::stdin(input).output()` shape stays for
transcript tests that don't need the dependency; `stdin_step` opts
into the gated mode.

## Operational implication / Context

This is the dependency for the request/response examples in
`tests/plan/helpers.md §"Usage examples"` (the "REPL session with
stdin script" pattern). Without it, all interactive-error and
interactive-reload e2e tests have to use the join-everything shape.

Estimated implementation: small. The REPL prompt-emit site is
already centralised (per `src/session_v4.rs` REPL eval loop); the
work is documenting the no-TTY plain-text shape and ensuring
flush/no-suppression discipline.

This is independent of FIXME 0109 (`session_v4`/`worker`
decomposition) — wherever the REPL eval loop lands post-0109,
the prompt-shape commitment carries.
