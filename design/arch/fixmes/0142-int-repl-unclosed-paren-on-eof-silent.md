---
number: 0142
target: /int
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: repl/spec.md §5.1, tests/repl_negative.rs::parse_error_unclosed_paren_neg, tests/legacy/ring0.rs::error_parse_error_unclosed_paren
status: open
---

# REPL silently exits on EOF with unclosed form (no parse error reported)

## Issue

When the REPL receives input with an unclosed `(` and then EOF (no
matching close paren follows), the REPL exits silently — no parse-error
diagnostic is printed. Repro:

```
$ printf '(add-i64 1 2\n' | cargo run -- 2>&1 | tail
cranelisp REPL — type /help for help
0+0ms; user>           ...
```

The REPL prints the banner + first prompt, then exits cleanly with no
error message. Expected per repl/spec.md §5.1 (Error Format): a parse
error diagnostic should surface ("parse error", "unclosed `(`",
"unexpected EOF", or similar).

By contrast, an extra closing paren (`)bad`) IS reported as a parse
error — `parse_error_stray_close` and `parse_error_has_location` both
pass. The asymmetry is the bug: only one of the two parser failure
modes (unbalanced opens vs unbalanced closes) produces a diagnostic.

This was discovered during Wave 5.6 file 4 ring0.rs supplement
authoring (`tests/repl_negative.rs::parse_error_unclosed_paren_neg`,
carry-forward from `tests/legacy/ring0.rs::error_parse_error_unclosed_paren`).
The legacy integration-tier test used `assert_parse_error` against the
Rust API, which short-circuits the REPL's continuation logic; the e2e
form exposes the multi-line-continuation + EOF gap.

## Proposed resolution

When the REPL's continuation-prompt accumulator is non-empty at EOF,
flush the accumulated input through the parser and report whatever
diagnostic the parser produces. Currently it appears to silently
discard the partial form on EOF.

Equivalent: at the point where the REPL decides "input ended, exit
cleanly", check whether there is a pending unclosed form; if so, emit
a parse-error message before exit.

## Operational implication / Context

Failing test landed un-ignored at
`tests/repl_negative.rs::parse_error_unclosed_paren_neg`, with
`// FIXME(/int)` annotation pointing here. Ledger entry added in same
commit. Test passes once `/int` resolves the EOF-with-unclosed-form
flush behavior.
