---
number: 0780
target: /stdlib
filed_by: /arch
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/arch/annotated-sexp-node.md §3 (macro-facing contract);
  stdlib macro-support surface (stdlib/control.cl macros-import area)
status: open
trigger: S116 — after the annotated-Sexp flip wave lands (the `macros/Sexp`
  ADT gains `(SexpAnnotated [:Sexp stype :Sexp sform])`, tag 7)
---

# Stdlib unwrap helpers for the `SexpAnnotated` macro-argument node

## Issue

Per the 0708 user ruling (Reading A-structural), macros receive `:Type <form>`
arguments as a folded `(macros/SexpAnnotated stype sform)` value from S116 on.
Splice-transparent macros need nothing; a macro that structurally inspects an
argument and wants to see through (or read) an annotation currently has to
hand-write the `match` arm each time.

## Request

Provide a small standard trio in the stdlib's macro-support surface (final
names are /stdlib's call, following Clojure conventions — `meta`/`with-meta`
are the nearest analogues):

- a predicate — working name `annotated?` :: `(Fn [macros/Sexp] Bool)`
- the annotation projection — working name `annotation` ::
  `(Fn [macros/Sexp] (Option macros/Sexp))`
- the subject projection (identity on non-annotated forms) — working name
  `unannotate` :: `(Fn [macros/Sexp] macros/Sexp)`

Contract details and the ADT shape: `design/arch/annotated-sexp-node.md` §3.
NOT load-bearing for the S116 mechanism (macros can pattern-match directly);
lands after the flip wave, with doc examples showing both the helper idiom and
the raw `(macros/SexpAnnotated t f)` match arm.

## Closure

/stdlib actions in its own files (helpers + any derive.cl arms it judges its
macros need) and deletes this file.
