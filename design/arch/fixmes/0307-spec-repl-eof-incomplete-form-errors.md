---
number: 0307
target: /spec
filed_by: /dev
filed_at: 2026-06-10
sprint_filed: 77
refers_to: spec/05-definitions.md §5.13.2 (REPL Input Boundary), repl/spec.md §5.1 (Error Format), tests/repl_negative.rs::parse_error_unclosed_paren_neg, design/arch/fixmes/0142-int-repl-unclosed-paren-on-eof-silent.md
status: open
---

# Spec is silent on EOF-mid-form: an incomplete form at EOF MUST be a parse error

## Issue

The REPL accumulates input across continuation lines until parentheses
balance, then submits the form. If EOF (Ctrl-D / end of piped input) arrives
while a form is still incomplete (unbalanced `(`), the correct behaviour —
per the user ruling 2026-06-09 — is a **parse error**, not a silent discard.

The user ruling: *"a complete form at the prompt is submitted/executed, so an
incomplete form at EOF must error"* (symmetry — you cannot submit an
incomplete form).

The spec does not currently state this:

- `spec/05-definitions.md §5.13.2` says "each input is a single top-level
  form" and covers forward-reference / cluster semantics, but says nothing
  about what happens when input ends mid-form.
- `repl/spec.md §5.1` (Error Format) defines the parse-error display shape and
  mandates errors go to stdout, but does not name the EOF-incomplete-form case
  as one of the conditions that MUST produce a parse error. The stray-close
  case (`)bad`) is implicitly covered; the unbalanced-open-at-EOF case is the
  asymmetric gap that FIXME 0142 reproduced.

## Proposed resolution

`/spec` (spec/05-definitions.md §5.13.2): add a sentence stating that REPL
input that ends (EOF) while a top-level form is still incomplete (unbalanced
delimiters) MUST produce a parse error — an incomplete form cannot be
submitted, mirroring the rule that a complete form at the prompt is submitted.

`/repl` (repl/spec.md §5.1, owned by `/repl` — file a companion FIXME if
`/spec` agrees): name "input ends mid-form (unbalanced delimiters) at EOF" as
a parse-error condition, with the error written to stdout per the existing
§5.1 stdout rule.

## Operational implication / Context

The behaviour is **already implemented** (S77 W-Repl, FIXME 0142 resolved in
`src/main.rs`: at EOF, a pending incomplete buffer is flushed through the
parser and the diagnostic — `parse error … unclosed '('` — is written to
stdout). The test `tests/repl_negative.rs::parse_error_unclosed_paren_neg`
passes. This FIXME only asks `/spec` to record the rule the implementation now
follows so the spec and code agree; it does not block any implementation work.
