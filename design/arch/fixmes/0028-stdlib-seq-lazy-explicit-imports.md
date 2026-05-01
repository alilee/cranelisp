---
number: 0028
target: /stdlib
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/wave6_demo_repros.rs:219, stdlib/seq/lazy.cl
status: open
migrated_from_inline: true
---

# 0028 — Add explicit imports to `stdlib/seq/lazy.cl`

## Issue

Add explicit imports to `stdlib/seq/lazy.cl`:

```
(import [collections.list [Nil Cons]])
(import [fn.option [None Some]])
```

Spec anchor: `spec/08-modules.md §8.3.6` — module that suppresses prelude glob MUST resolve every name through explicit imports. Stdlib convention (`stdlib/CLAUDE.md`): all stdlib modules use only primitives + explicit imports, never bare prelude symbols.

## Source location

`tests/wave6_demo_repros.rs:219` (FIXME at the demo repro).

## Context

Sprint 58 Wave 6 `/stdlib` audit noted `seq/lazy.cl` was the only at-risk file in the 35-file `(import [prelude []])` audit (others either define the names they reference or qualified-import them). The fix adds the two missing explicit imports.

## Proposed resolution

`/stdlib` edits `stdlib/seq/lazy.cl` to add the two `(import …)` forms; the demo repro test then passes.
