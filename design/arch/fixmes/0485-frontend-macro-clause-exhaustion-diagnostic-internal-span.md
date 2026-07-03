---
number: 0485
target: /frontend
filed_by: /stdlib
filed_at: 2026-07-03
sprint_filed: 101
refers_to: spec/09-macros.md (multi-clause defmacro), stdlib/control.cl §cond, CLAUDE.md §Design Principles (self-documenting REPL)
status: open
---

# Multi-clause macro arity exhaustion reports an internal span and the recursion bottom, not the user's call

## Issue

Calling stdlib `cond` with an even argument count (a natural Clojure-habit
mistake — pairs with a `:else`-style final pair instead of the mandatory
trailing default) produces:

```
user> (cond (< 2 1) "no" (< 1 2) "yes" true "fallback")
Error: macro error at 1000056..1000056: macro `FQSymbol { module: ModuleFullPath("control"), symbol: Symbol("cond") }` returned malformed sexp at 1000056..1000056: no matching clause for macro `control/cond` with 0 argument(s)
```

Three problems, all frontend-owned diagnostic surface (the stdlib macro
itself is behaving per its design — `(cond t1 b1 … default)` recurses two
args at a time and an even count bottoms out at 0 args):

1. **Internal span** `1000056..1000056` — an expansion-buffer offset, not a
   position in the user's input; nothing for the user (or an editor) to
   anchor on.
2. **Debug-format symbol** — `FQSymbol { module: ModuleFullPath("control"),
   symbol: Symbol("cond") }` leaks the Rust Debug repr instead of
   `control/cond`.
3. **Wrong grain** — "0 argument(s)" describes the *recursion bottom*, not
   the call the user wrote (6 arguments). A user cannot map "0 arguments"
   back to their even-count mistake.

## Proposed resolution

When clause matching fails during (possibly recursive) expansion: report at
the span of the ORIGINAL user call form, name the macro by its display FQ
name, and state the available clause arities (e.g. "no matching clause for
`control/cond` with 0 argument(s); clauses accept 1 or 2+ arguments —
`cond` takes test/body pairs followed by a mandatory default"). The
docstring/arity data is already in the macro definition; surfacing it here
satisfies the self-documenting-REPL principle ("no valid language construct
should produce an opaque error" — and this near-miss of a valid construct
is the highest-traffic error shape the prelude macros have).

## Operational implication / Context

Found during S101 Phase 6a stdlib assessment. Purely diagnostic quality —
no behavior change; correct even-count usage errors are STILL errors.
