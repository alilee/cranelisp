---
number: 0493
target: /qa
filed_by: /repl
filed_at: 2026-07-03
sprint_filed: 101
refers_to: repl/spec.md §1.5 (List display row), repl/spec.md §3.7 (worked example line), repl/demos/06-modules.demo, tests/repl_introspection.rs::display_user_list_value_shows_elements_and_nil
status: open
---

# Nested parameterized-ADT value display is garbled — type token + unbalanced parens where the nested constructor should open

## Issue

The REPL's `:Type value` rendering of an ADT value garbles whenever a field's
value is itself a **parameterized** ADT instance. Instead of recursing into the
nested constructor, the renderer emits the nested instance's **type argument**
followed by a premature `)`, then the nested rendering follows as a sibling,
leaving the whole line with unbalanced parentheses.

Stdlib-free 3-line repro (REPL, no prelude needed beyond deftype):

```
user> (deftype (Wrap a) (MkWrap [:a v]))
:user/Wrap ; deftype
user> (MkWrap 7)
:(user/Wrap primitives/Int) (Wrap.MkWrap 7)          <- correct
user> (MkWrap (MkWrap 7))
:(user/Wrap (user/Wrap primitives/Int)) (Wrap.MkWrap primitives/Int) (Wrap.MkWrap 7))
```

Expected per §1.5's generic recursive form: `(Wrap.MkWrap (Wrap.MkWrap 7))`.

Trigger characterization (verified live, S101 6b):

- **Garbles**: field value is a parameterized ADT instance — `(MkWrap (MkWrap 7))`,
  `(Some (Some 5))`, `(Some (list 1 2))`, stdlib `(list 1 2 3)`
  (`(List.Cons 1 primitives/Int) (List.Cons 2 primitives/Int) (List.Cons 3 List.Nil)))`),
  inline generic `(MyCons 1 (MyCons 2 MyNil))`.
- **Correct**: primitive payloads (`(Some 7)`), and a **non-generic** ADT payload
  inside a generic wrapper (`(Some (MkPair 1 2))` → `(Option.Some (Pair.MkPair 1 2))`).

The spec's own worked example is violated: `repl/spec.md` §3.7 shows
`(list 1 2 3)` displaying as `(List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))`,
and §1.5's List row pins the generic ADT recursive form as normative.

## Proposed resolution

/qa authors a narrow failing e2e repro (failing-not-ignored, `// spec: repl/spec.md
§1.5`) from the 3-line Wrap shape above, with `FIXME(/int)` (or `/backend` if the
renderer lives in the show/codegen path) as resolver. Note the existing guard
`tests/repl_introspection.rs::display_user_list_value_shows_elements_and_nil` is
too weak to catch this — it asserts element and `List.Nil` **presence** only, not
the nested structure, so it stays green over garbled output. Upgrade candidate:
assert the exact `(List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))` string (or
at minimum balanced parens + absence of type tokens inside the value).

## Operational implication / Context

- Surfaced by the S101 Phase-6b full demo replay: `06-modules.demo`'s
  `(rest (list 1 2 3))` beat displayed the garbled form. The demo has been
  reshaped to avoid demonstrating the bug (match-based tail access); this FIXME +
  the /qa guard are the durable record.
- Regression window unknown — the weak e2e assertion means the suite cannot date
  it. /port's 6a D4 note ("ADT payload display ~0050 class", flagged unfiled) is
  likely the same observation. Distinct from FIXME 0050 (aspirational List/Seq
  pretty-printer): this is malformed output of the *normative generic form*, not
  a missing nicety.

## /qa guard batch (S101 6b, 2026-07-03): guards LANDED — this file is now redundant as a record

`tests/repl_introspection.rs`: new RED guard
`display_nested_parameterized_adt_value_recursive_form` (3-line Wrap shape,
exact `(Wrap.MkWrap (Wrap.MkWrap 7))` + type-token negative) + green control
`display_single_level_parameterized_adt_value_control`; AND the existing
presence-only guard `display_user_list_value_shows_elements_and_nil` is
STRENGTHENED to assert the exact nested `(List.Cons 1 (List.Cons 2
(List.Cons 3 List.Nil)))` string + type-token negative — it is now RED by
design (annotated in-test). Resolver TBD (/int display seam or /backend).
Ledger: `tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set".
