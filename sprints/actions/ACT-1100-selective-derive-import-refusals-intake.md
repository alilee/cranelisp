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

## Classification: a defect against spec §9.3.4 (qa, 2026-11-20)

Reduced without the standard library, on the debug binary built from
`3c5e41ca`, a scratch directory since removed.

```clojure
;; d.cl, on the library path
(import [primitives [Int add-i64]])
(defmacro inner [x] `(add-i64 ~x 1))
(defmacro outerq [x] `(inner ~x))
```

| Session | Observed |
|---|---|
| `(import [d [outerq]])`, `(outerq 2)` | **`undefined variable: d/inner`, in expansion of `(outerq 2)`** |
| The same with `outer`, which builds the symbol `inner` by hand | The same refusal |
| The same program under `--run` | The same refusal |
| `(import [d [*]])`, `(outerq 2)` | 3 |
| `(import [d [outerq inner]])`, `(outerq 2)` | 3 |
| `(import [d [outerq]])`, then `(d/inner 2)` typed by the user | 3 |
| No import, `(d/inner 2)` | 3 |

- [§9.3.4](../../spec/09-macros.md): a macro's expansion may reference
  "macros, including macros defined earlier in the same module". The
  using module's imports are not a condition.
- **Severity: a legal program refused.** No wrong value and no memory
  hazard.
- **Mechanism, observed by control and not at its seam.** The expansion's
  reference is qualified to the macro's module, and that qualified call is
  not expanded unless the using module has the macro in scope. The same
  spelling typed by the user is expanded with nothing imported. `qa` did
  not read where the two lookups part, so **the module is not attributed.**
  **Refuted if** a user-typed `(d/inner 2)` is refused in some session where
  the expansion's is.
- **The two diagnostics share this cause.** With the companions unexpanded,
  the combined form is a `begin` holding several expressions, and the
  compiler reports any such `begin` as `illegal redefinition of __expr`:
  `(begin (nosuch 1) (nosuch 2))` gives the same text. Whether a `begin` of
  two expressions should be reported in those words is a separate lead,
  not classified here.
- **Lead.** Under `--run` the refusal is reported "in expansion of
  `(import [d [outerq]])`", at the import's span.
- **Not established:** its age. The linked mode was not run.

## Routing

- **`qa` holds this action.**
- **`test`:** T-MACRO-SIBLING, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(int), then `dev`(`src/`):** the correction, carried on
  T-MACRO-SIBLING unless the user schedules it.

## Attribution: the binary's expansion driver (qa, 2026-11-20)

Read in source at `23448d9c`, with the control above.

- `src/process_form/macro_resolution.rs` expands a form recursively and
  recognises every macro head, including one an expansion produced,
  through `expander::recognize_macro_head` against the **using** module's
  scope. A head the using module has not imported is not recognised and
  flows on as an ordinary call.
- Only after the whole expansion does `qualify_expanded_sexp` rewrite the
  expansion's free symbols to the macro's defining module, giving
  `d/inner`. Nothing recognises macro heads again after that rewrite.
- **At the seam:** the refusal names `d/inner`, the qualified and
  unexpanded head, "in expansion of" the outer call.
- **Control:** the same qualified spelling typed by the user is recognised,
  because it is qualified before recognition.
- **Module: `src/`.** The governing designs are
  [expansion qualification](../../design/int/expansion-qualification-scope.md)
  and `arch`'s macro-availability model.
- **Refuted if** recognition of an expansion-produced head is shown to
  consult the defining module.

T-MACRO-SIBLING is committed (`85f32147`): six subjects fail on
`undefined variable: d/inner` at the REPL, under `--run` and linked, and
twelve controls pass. `test` replaces the cells' seam locus with
`src/process_form/macro_resolution.rs`.
