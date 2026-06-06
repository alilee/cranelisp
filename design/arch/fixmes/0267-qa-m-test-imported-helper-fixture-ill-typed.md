---
number: 0267
target: /qa
filed_by: /sprint
filed_at: 2026-06-05
sprint_filed: 76
refers_to: tests/s76_macro_availability.rs::macro_clause_calls_imported_helper_at_expansion_works, spec/09-macros.md §9.2.2 §9.2.3 §9.2.5, tests/spec_09_macros.rs::cross_module_macro_calls_helper_in_other_module
status: open
---

# M-test `macro_clause_calls_imported_helper_at_expansion_works` fixture is ill-typed — capability verified working; retype the helper

## Issue

The test's dependency helper is `bump :: Int -> Int`, called unquoted in the macro
clause body `(defmacro wrap [a] (bump a))`. Per spec §9.2.2 every macro parameter
is `Sexp` and per §9.2.3 the body MUST return `Sexp` — so the fixture is ill-typed
by the spec's own rules, and the compiler correctly rejects it
(`type mismatch: expected Int, got macros/Sexp` while typechecking module `mac`).
The test fails on its fixture, not on the capability.

**The capability works.** S76 probe (2026-06-05, /sprint, against the live binary,
`PreludeVariant::None` shape): a `Sexp -> Sexp` helper in a dependency module,
called unquoted at expansion time across the `helper -> mac -> main` graph in
`--run`, exits 42. Scheduler dependency-order compilation supplies the
"typechecked-before" guarantee in batch mode without any pause machinery.

```clojure
;; helper.cl
(import [macros [*]])
(defn bump [s] (SexpInt 42))
;; mac.cl
(import [helper [bump]])
(defmacro wrap [a] (bump a))
;; main.cl
(import [mac [wrap]])
(defn main [] (wrap 0))      ; => 42
```

## Proposed resolution

1. Retype the fixture per the probe shape (helper takes/returns `Sexp`). Keep the
   `// spec: spec/09-macros.md §9.2.5` annotation; the test then validates the
   expansion-time dependency-helper rule as intended.
2. **Coverage note**: the test's comment cites
   `spec_09_macros.rs::cross_module_macro_calls_helper_in_other_module` as
   "already green" prior coverage — but that fixture *quasiquotes* the helper call
   (`` `(make-seven) ``), deferring it to **runtime of the expanded code**. It never
   tested expansion-time calling. After this fix, the M-test is the sole
   expansion-time-call coverage; consider a `_neg` sibling asserting that an
   ill-typed helper (the old `Int -> Int` shape) is REJECTED with the §9.2.3/§9.2.2
   type error — turning today's accident into deliberate negative coverage.

## Operational implication / Context

One of the three "macro wall" failures from S76 Wave 2 — dissolved by probing
(the other two: FQ lazy-load = FIXME 0268 real capability gap; M3 diagnostic =
FIXME 0262 message-only). Per `memory/feedback_validate_tests_against_spec.md`.
Natural home: the same /qa fire as FIXMEs 0263/0264 (Wave 3).
