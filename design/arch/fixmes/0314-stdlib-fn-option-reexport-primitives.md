---
number: 0314
target: /stdlib
filed_by: /sprint
filed_at: 2026-06-11
sprint_filed: 78
refers_to: stdlib/fn/option.cl, stdlib/seq/lazy.cl, src/bootstrap.rs (primitives Option seed), design/arch/fixmes/0312-primitives-adt-glob-collision.md
status: open
---

# stdlib `fn.option` should RE-EXPORT `primitives/Option`, not define a second one

## Issue

There are currently **two distinct `Option` ADTs** in the system:
- `primitives/Option` — seeded by `src/bootstrap.rs` (Step 4, `Visibility::Public`)
  because primitive signatures reference it (`parse-int :: (Fn [String] (Option Int))`,
  `discover-tests :: ... (Option String)`) and the no-stdlib path needs bare
  `Some`/`None`. This is newer — primitives did NOT have its own `Option` before.
- `stdlib/fn/option.cl` — **defines its own** `(deftype (Option a) None (Some [:a val]))`.

Once S78 Wave 4 deleted the `is_seeded` name-keyed ambiguity-skip (`src/imports.rs`)
— correct per spec §8.6.4 and the user's ruling that overlapping imports MUST
collide — the two `Option`s collide in any stdlib module that does BOTH
`(import [primitives [*]])` (glob → `primitives/Some/None`) AND
`(import [fn.option [Some None]])` (→ `fn.option/Some/None`). Concretely
`stdlib/seq/lazy.cl` (and peers): `undefined variable: None` → stdlib stops
compiling. `is_seeded` was silently masking this genuine two-Options collision.

## Proposed resolution

`stdlib/fn/option.cl` re-exports `primitives/Option` instead of defining a new
one, e.g.:

```clojure
(import [prelude []])
(import [primitives [Option Some None]])
(export [primitives [Option Some None]])
;; plus stdlib's Option combinators (map, and-then, etc.) over the SAME type
```

Then `fn.option/Option` IS `primitives/Option` (same source), so the
glob+specific overlap **dedups** (spec §8.6.4 "same-source duplicates are NOT
ambiguous") instead of colliding — stdlib compiles, and there is one canonical
`Option`. `/stdlib` audits every module for the same glob-`primitives` +
specific-domain-ADT footgun (the user's ruling: that overlap is a footgun and
SHOULD error — modules must not create it).

## Operational implication / Context

Not blocking S78: QA decoupled its tests from real stdlib (free-standing
fixtures) so the workspace is green with `is_seeded` gone. This is the durable
stdlib fix that makes the two `Option`s one. The deeper "why two Options"
(primitives can't depend on stdlib, so it seeds its own for sigs + no-stdlib) is
an `/arch` note — but the re-export above resolves the user-facing collision
without needing primitives to change.
