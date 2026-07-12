---
number: 0568
target: /dev
filed_by: /repl
filed_at: 2026-07-12
sprint_filed: 108
refers_to: the ambiguity-error message emitted for a top-level polymorphic
  expression whose type cannot be pinned (REPL/typecheck seam); the synthetic
  top-level binder name `__expr` used when wrapping a bare REPL expression.
  Reproduced at S108 Inc3 6a assessment via `(count [])` after
  `(import [collections.vec [count]])`.
status: open
---

# Ambiguity error leaks the internal `__expr` synthetic binder into user-facing output

## Issue

Entering a top-level expression whose type stays polymorphic produces:

```
> (import [collections.vec [count]])
> (count [])
Error: type error at 7..9: ambiguous type; add an annotation to pin the type of the polymorphic value bound in `__expr`
```

The phrase **"bound in `__expr`"** surfaces a compiler-internal synthetic binder
name. The user never wrote `__expr` — it is the name the REPL wraps a bare
expression in — so the reference points at something invisible in their source.

This was flagged as a known minor cosmetic leak in the S108 Inc3 dispatch (E10).

## Assessment (severity: low / cosmetic — NOT an opaque-error blocker)

The message is still **actionable**: "add an annotation to pin the type of the
polymorphic value" tells the user exactly what to do, so it does not violate the
"no valid construct produces an opaque error" Design Principle outright. It DOES
violate the narrower error-quality criterion "no internal names in user-facing
errors" (root `CLAUDE.md` §Design Principles; `.claude/commands/repl.md`
§"Error message quality"). A user reading `bound in \`__expr\`` cannot map it to
anything they typed.

## Proposed resolution (for /dev to weigh)

When the ambiguous binding is the synthetic top-level REPL wrapper (`__expr`),
phrase the message without the internal name — e.g. "add an annotation to pin the
type of this expression" (or "…of the polymorphic result") — reserving the
`bound in \`<name>\`` clause for genuine user-written `let`/`defn` binders where
naming the binding actually helps. A unit test at the message-construction seam
should pin that no `__expr` (or other `__`-prefixed synthetic) leaks into a
user-facing diagnostic.

## Notes

- Not a blocker for Inc3 close; the conflict/ambiguity behaviour itself is
  correct — only the wording leaks an internal name.
- Cross-check whether other synthetic binders (`__`-prefixed) can reach
  user-facing diagnostics through the same message path while fixing.
