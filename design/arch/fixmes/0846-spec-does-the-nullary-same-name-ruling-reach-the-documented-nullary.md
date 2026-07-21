---
number: 0846
target: /spec
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/05-definitions.md §5.2.1, §5.2.5;
  tests/deftype_constructor_form_rulings_s116.rs::deftype_documented_nullary_sharing_type_name_control_green
status: open
---

# Does "a nullary constructor may not share its type's name" reach the DOCUMENTED nullary spelling?

## The two S115 rulings, and the cell where they meet

- **Ruling 1** — `'(' CTOR ')'` with neither docstring nor field list is a parse
  error; parens on a constructor require content.
- **Ruling 2** — a nullary constructor may not share its type's name; the unit
  type is `(deftype Unit [])`.

Both were pinned this phase in `tests/deftype_constructor_form_rulings_s116.rs`
as intended REDs with an S116 flip trigger. One cell sits at their intersection
and the rulings as stated do not settle it between them:

```clojure
(deftype Flag (Flag "a documented nullary"))
```

- Under **ruling 1** the paren is legal: a docstring is content.
- Under **ruling 2** as worded, this is a nullary constructor sharing its type's
  name — a reject.

If ruling 2 reaches it, a documented nullary that shares its type's name has
**no legal spelling at all**: the bare form `(deftype Flag Flag)` is rejected by
ruling 2, the content-free paren by ruling 1, and the documented paren by
ruling 2. §5.2.5's documented-nullary form would be unavailable at that one
name. If ruling 2 does NOT reach it, the language accepts a documented nullary
sharing its type name while rejecting the undocumented one — a docstring
changing a well-formedness verdict.

## Disposition of the test cell

The Phase-7 dispatch named this cell as a **born-green control**, and it IS
green at HEAD, so it is pinned green — with the tension recorded in the test
comment and pointed at this FIXME. It is a pin awaiting a scribe, not settled
coverage. If `/spec` records that ruling 2 reaches the documented spelling,
`/testing` flips the cell to `assert_rejected` alongside the other ruling-2 RED;
one line, no restructuring.

The question is `/spec`'s to frame for the user — `/testing` states neither
answer.
