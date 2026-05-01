---
number: 0051
target: /docs
filed_by: /docs
filed_at: 2026-05-01
sprint_filed: 64
refers_to: user/plan-docs.md:220
status: open
migrated_from_inline: true
---

# 0051 — Update user/ examples to canonical REPL introspection format

## Issue

S59 Defect 3 formalised the canonical REPL introspection format as `:Type {value|name} ; {classification} - {docstring}` per `repl/spec.md §1.1` line 159 (classification word + dash separator). The examples in `user/plan-docs.md` predate that convergence — they show `; <doc>` only, without classification or dash.

Update to match current output, e.g.: `primitives/Int ; type - Integer numbers between -100 billion and 100 billion`. Confirm against `src/session_v4.rs::append_docstring_comment` output.

## Source location

`user/plan-docs.md:220` (HTML-comment FIXME below the format example).

## Context

The user docs plan describes the docstring format. Sprint 59 Defect 3 (closed by FIXME 0029 fix) made the dash separator canonical; the plan needs alignment.

## Proposed resolution

`/docs` updates the format example in `plan-docs.md` and audits `user/getting-started.md` and other user-facing docs for stale `; <doc>` shapes.
