---
number: 0389
target: /design
filed_by: /dev
filed_at: 2026-06-16
sprint_filed: 84
refers_to: crates/cranelisp-frontend/src/ast_builder.rs::build_match (:1338), spec/03-types.md §3.11.1 / §4.9, tests/regression.rs::mono_bare_annotated_value_pins_and_compiles_pos
status: open
---

# `:Type form` annotation in `match`-scrutinee position fails to parse — blocks §3.11.1 disambiguation

## Issue

`(match :(Option Int) None [None 0 (Some _) 1])` — a `:Type form` annotation in
match-scrutinee position — fails at PARSE time with:

```
parse error at …: match requires scrutinee and arms
```

`build_match` (`crates/cranelisp-frontend/src/ast_builder.rs:1338`) requires exactly
3 children (`match`, scrutinee, arms-bracket). The `:Type form` reader-macro-style
annotation (`:(Option Int) None`) is NOT grouped into a single scrutinee Sexp before
`build_match` counts children, so `(match :(Option Int) None […])` presents MORE than
3 children and the arity guard rejects it.

By contrast, `:(Option Int) None` in **call-argument** position
(`(is-some :(Option Int) None)`) parses and resolves correctly — only the
`match`-scrutinee position is broken.

Reproduced at baseline (159f544, BEFORE the S84 §3.11.1 / Vec-annotation change-set
landed) — this is a PRE-EXISTING frontend defect, NOT introduced by FIXME 0386/0385.

## Proposed resolution

The `:Type form` annotation must bind the immediately-following form in scrutinee
position the same way it does in every other position (the
`annotation-reader-macro-binds-following-form` model — `memory/`). Either the reader
groups `:Type form` into one annotation Sexp before `build_match` sees it, or
`build_match` recognises and consumes a leading `:Type` + form as the scrutinee. The
fix belongs to the frontend (reader / `ast_builder`), `/design`-owned for the
frontend crate; `/dev(frontend)` lands it.

## Operational implication / Context

- This blocks the Option leg of the S84 acceptance guard
  `tests/regression.rs::mono_bare_annotated_value_pins_and_compiles_pos`
  (`(match :(Option Int) None [None 0 (Some _) 1])`), which /qa committed expecting
  green ("VERIFIED WORKS today" per the test's own comment — the verification was of
  `:(Option Int) None` in *call-arg* position, not match-scrutinee). The Vec leg of
  the same guard (`(vec-len :(Vec Int) [])`) now passes (FIXME 0385 landed). So the
  guard fails ONLY on this frontend parse bug, not on any typecheck/Vec-annotation gap.
- Under the tightened §3.11.1, `:Type form` IS the directed disambiguation remedy; a
  match scrutinee is a codegen-reaching position (the spec's `(identity None)` worked
  example is a runtime value reaching a match). A user who hits the ambiguity on a
  match scrutinee (`(match (Ok 42) …)`, FIXME 0388) and follows the directed remedy
  `(match :(Result Int String) (Ok 42) …)` currently cannot — the annotation does not
  parse there. So this gap compounds 0388's blast radius.
