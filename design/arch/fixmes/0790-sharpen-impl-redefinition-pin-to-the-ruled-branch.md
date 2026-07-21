---
number: 0790
target: /testing
filed_by: /dev (src)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/impl_redefinition_dispatch.rs::reimpl_either_dispatches_new_or_notices_not_replaced
  + spec/05-definitions.md §5.4.5 [S115] +
  design/int/impl-redefinition-hot-reload.md §5
status: open
---

# The impl-redefinition pin is still polarity-safe after the ruling — sharpen it, and add the type-changing negative

## Issue

`reimpl_either_dispatches_new_or_notices_not_replaced` was authored polarity-safe
(S114) because the semantics were an open user question: it passes if EITHER the
new impl dispatches (`:primitives/Int 7`) OR a "not-replaced" notice appears. The
question is now **settled** — spec §5.4.5 [S115] rules hot-reload — and the fix
landed in S115 W6 (`src/worker.rs::derive_codegen_batch` now enrolls the impl's
mangled method `Def`s into the forced batch). The pin is GREEN.

But it is green on a **disjunction**: as written it would also pass a future
regression back to "silently ignore + print a notice", and the `not_replaced_notice`
arm matches loose substrings ("exists", "already", "ignored") that unrelated output
could satisfy. `design/int/impl-redefinition-hot-reload.md` §5 anticipates exactly
this: "at flip, /testing sharpens it to the ruled branch … retiring the 'notices
not replaced' alternative arm".

## Proposed resolution

1. **Sharpen** the pin to the ruled branch: after a same-type re-impl,
   `(size (Bx 0))` MUST print `:primitives/Int 7`; delete the notice arm and the
   open-question preamble; re-anchor `// spec:` on `spec/05-definitions.md §5.4.5`.
   Behaviour verified manually at the fix (a THIRD re-impl to `99` also takes, so
   hot-reload is not a one-shot).
2. **Add the negative** the design's §5 names and §4 relies on: a **type-changing**
   re-impl is rejected at the trait-conformance seam, not silently confirmed, and
   the PRIOR impl keeps dispatching. Verified transcript at HEAD-with-fix
   (`--no-cache`, clean cwd):

   ```
   (deftype Box (Bx [:Int v])) (deftrait Sizeable (size [x] Int))
   (impl Sizeable Box (defn size [x] 12))   → 12
   (impl Sizeable Box (defn size [x] "hi")) → Error: type error … type mismatch:
                                              expected primitives/String, got primitives/Int
   (size (Bx 0))                            → :primitives/Int 12
   ```

   (The message's expected/got polarity reads inverted for a conformance failure —
   worth a separate look, but out of scope here.)

Unit-tier coverage already exists at the seam
(`worker::tests::derive_codegen_batch_enrolls_mangled_impl_methods_even_when_compiled`,
fail-on-revert demonstrated). This request is the e2e half.

## Context

`/dev`(src) S115 W6, resolving the impl-redefinition carry RED. The flip is the
last in-scope W6 RED; sharpening does not gate it.
