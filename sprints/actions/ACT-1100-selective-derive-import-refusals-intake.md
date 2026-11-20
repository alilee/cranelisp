---
id: ACT-1100
title: Selectively importing derive refuses expansions that work with its companion macros in scope
status: open
priority: required
from: docs
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - stdlib/derive.cl
  - spec/09-macros.md
  - user/guide/traits.md
---

## Observation

During S124 Phase 6b documentation verification, using the existing debug binary
with the default standard library, `--no-agent --no-cache`, each case in a fresh
scratch directory. Opened `stdlib/derive.cl` and `stdlib/derive/test.cl`: the
combined macro emits calls to companion macros, and the consumer tests import
all four macros together. No compiler attribution is established by this read.

At a fresh REPL, enter these two turns:

```clojure
(import [derive [derive]])
(derive [Display] (deftype Hue Dark Light))
```

The second turn reports `undefined variable: derive/derive-Display`. Change only
the import to `(import [derive [*]])`: the expansion succeeds, and `(show Light)`
returns `"Light"`. Importing only `derive-Display`, defining `Hue`, and applying
`(derive-Display (deftype Hue Dark Light))` also succeeds.

The broader combined form with the selective import:

```clojure
(import [derive [derive]])
(derive [Eq Ord Display] (deftype Color Red Blue))
```

reports `illegal redefinition of __expr in one compilation cluster`. The same
form with the glob import succeeds; `(= Red Red)` and `(< Red Blue)` return
`true`, and `(show Blue)` returns `"Blue"`. A handwritten `begin` containing a
type and a Display implementation also succeeds.

The selective three-trait program was also refused by `--run` when followed by
`(defn main [] (primitives/Pure 7))`. Loading those declarations from `user.cl`
locks the REPL at startup. No `--link` probe ran.

## Request

`qa`: assess these refusals against macro availability and qualified dependency
calls (spec §9.3.4), reduce further if needed, allocate permanent failing tests
with controls to `test`, and attribute from a discriminating observation. In
particular, determine whether the two diagnostics share a cause. This report is
intake, not a confirmed compiler mechanism or a closed defect.

The documentation offers the verified glob form and states its boundary. No
compiler or test source was changed by `docs`.

## Completion evidence

`test` commits the narrow reproduction(s) with `// spec:` annotations and their
controls, or `qa` records the governing reason the selective form is invalid.
Any correction belongs to the attributed owner and includes module evidence.
