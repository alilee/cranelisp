---
number: 0798
target: /testing
filed_by: /qa
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/08-modules.md §8.3.4 (module aliases — "the alias can then be
  used for qualified references") + §8.3.6 (alias-only import — "useful when you
  only want qualified access") + design/arch/fixmes/0787-*.md (the undispositioned
  tail) + tests/dotted_binder_reject_0702.rs (the reference-column cells)
status: open
---

# A module alias is never registered as a qualifier — `(import [(m u) …])` then `(u/name)` fails; spec §8.3.4/§8.3.6 violation

## Severity

**Important.** A documented language feature is non-functional end to end, and
in its alias-ONLY form (§8.3.6) the alias is the entire purpose of the import —
so that form does nothing usable at all. Class: `wrong-reject` (a
spec-conforming program rejected).

## Issue

Probed live at HEAD `9088c82e` (scratchpad cwd, `PrimitivesOnly` prelude):

```clojure
;; main/util.cl
(defn helper [] 7)

;; alias-only import — the spec's own "qualified access only" case
(import [(main.util u) []])
(defn main [] (Pure (u/helper)))
```

```
error: module 'u' referenced by 'u/...' not found (referenced by 't')
exit 1
```

The spec is explicit, twice:

> **§8.3.4** — "…registers `str` as an alias for `core.string`. **The alias can
> then be used for qualified references: `str/split`.**"
>
> **§8.3.6** — "Registers `opt` as an alias for `core.option` without importing
> any bare names. **Useful when you only want qualified access: `opt/Some`.**"

## Discriminating control (one variable at a time, same fixture, same HEAD)

| Program | Result |
|---|---|
| `(import [(main.util u) []])` + `(u/helper)` — alias-only | **exit 1** — alias not found |
| `(import [(main.util u) [helper]])` + `(u/helper)` | **exit 1** — alias not found |
| `(import [(main.util u) [helper]])` + `(helper)` — bare ref | exit 7 ✓ |
| `(import [main.util [helper]])` + `(main.util/helper)` — full path | exit 7 ✓ |

Rows 2 and 3 differ **only** in whether the reference is alias-qualified, and
they use the identical import form. So the alias form imports its *names*
correctly; the alias itself is simply never registered as a referenceable
qualifier.

## Attribution status

**`wrong-reject`, at qualified-name resolution. The owning crate is NOT
attributed here** — I have a discriminating control but **no seam observation**,
and per METHOD §2.2 that is not enough to name an owner. The reduction names the
seam and the seam names the owner. Candidate surfaces to look at first (not a
verdict): whether the `(module alias)` pair writes any alias entry at all at
import registration, vs. whether it writes one that qualified-name resolution
never consults. Note that §8.6.6 requires alias-chain walking for *export mount*
aliases and those work — so the two alias kinds may have diverged, which would
make this a `resolver-mirror` rather than a missing feature. Establish which
before fixing.

## Ask

1. **Reduce and commit the failing repro** — failing-not-ignored, with
   `// spec: spec/08-modules.md §8.3.4` and a `// defect:` line
   (`class=wrong-reject`, `owner=` per what the reduction names). Start from the
   alias-only form: it is the smallest and the most clearly specified.
2. **Author the missing matrix column.** This is a
   coverage-by-definition-variants miss of the standing lens
   (`tests/CLAUDE.md`): the family is **import shape × reference form**, and the
   suite is dense on `(bare import × bare ref)` and `(bare import × full-path
   ref)` while `(alias import × alias-qualified ref)` is **empty**. Cells owed,
   both polarities:

   | import shape | bare ref | alias-qualified ref | full-path ref |
   |---|---|---|---|
   | `[m [name]]` | fenced ✓ | n/a | fenced ✓ |
   | `[(m u) [name]]` | fenced ✓ | **owed** | **owed** |
   | `[(m u) []]` (alias-only) | n/a (imports nothing) | **owed** | **owed** |
   | `[(m u) [*]]` | **owed** | **owed** | **owed** |

   Plus the type-annotation position (`:u/T`) and a dotted-module alias target
   (`(main.util u)` is already dotted — keep that, it composes this with 0787's
   dotted-reference column).
3. **Negative twin**: an *undeclared* alias `(v/helper)` must still be the
   located "module not found" error, so the fix cannot be a blanket
   accept-anything-before-`/`.

## Context

Found by `/qa` at S115 W7 while dispositioning FIXME 0787. `/testing` flagged
`(u/helper)` as "outside this FIXME's ask — `/qa` to route if it is a defect"
rather than dropping it; that routing is what surfaced a spec violation. Worth
noting as method: the 0787 cells were authored against the *dotted-splitter*
hazard, and the alias gap was found in the blast radius around them, not by the
cells themselves. **A whole documented feature sat unexercised because no cell
asked for it** — which is precisely the standing lens's thesis.
