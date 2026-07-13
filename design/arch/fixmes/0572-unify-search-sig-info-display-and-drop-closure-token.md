---
number: 0572
target: /repl
filed_by: /repl
filed_at: 2026-07-12
sprint_filed: 108
refers_to: REPL value rendering for a function-valued binding — `primitives/vec-len`
  displays its value as the opaque token `<closure>` — plus the broader ask to
  unify the `/search` result-row, bare-symbol signature, and `/info` display
  formats into one shape (repl/spec.md value-display + §17.19.2). Reproduced
  post-S108 via `primitives/vec-len`.
status: open
---

# Rationalise search / sig / info displays to one format; drop the bogus `<closure>` value token

## Issue

A function-valued binding renders its *value* as the opaque token `<closure>`:

```
> primitives/vec-len
:(Fn [(primitives/Vec a)] primitives/Int) <closure>
```

The type is correct, but `<closure>` is uninformative where a qualified name is
available — bare lookup of other symbols shows the FQ name (e.g.
`:control/when`). More broadly, three display paths present overlapping
"what is this symbol" information in three different shapes:

- `/search` result rows,
- bare-symbol signature display,
- `/info`.

The user wants them **rationalised to a single format**.

## Assessment (severity: low — ergonomics + self-documenting-REPL consistency)

`<closure>` violates the spirit of the self-documenting REPL: the value slot
should carry a meaningful identity (the qualified name) when one exists, not a
placeholder. And three divergent renderers for essentially one question are the
kind of per-path display duplication we otherwise fight — each render path grows
its own shape (cf. the coverage-by-definition-variants lesson: one operation,
many surfaces, one intended format). Not a correctness blocker.

## Proposed resolution (/repl-led design, /dev impl)

- **/repl** — define ONE canonical `:Type value` render, used by `/search` rows,
  bare-symbol lookup, and `/info` (differing only in verbosity / which drawers
  expand), and specify that a function value shows its **qualified name** rather
  than `<closure>`. Pin it in `repl/spec.md` (value-display + §17.19.2).
- **/dev** — implement the single renderer against that spec, retiring the
  divergent per-path formatting.

## Notes

- Pairs with **0569** (macro rows show a bogus `:primitives/Int`) — both are the
  same underlying shape: the search/info row renderer isn't consulting the
  entry's real classification/identity. Consider resolving them together under
  the unified renderer.
- Design finding, not a defect repro; the unification is a `/repl` design task.
  A `/testing` row-byte check follows once the single format is pinned.
