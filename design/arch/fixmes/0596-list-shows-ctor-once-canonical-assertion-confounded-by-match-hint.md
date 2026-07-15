---
number: 0596
target: /testing
filed_by: /dev
filed_at: 2026-07-15
sprint_filed: 109
refers_to: tests/repl_introspection.rs::list_shows_ctor_once_canonical — the
  whole-stdout `matches("Some").count() == 1` assertion is confounded by the
  deftype echo's `; match:` hint line, so it fails once `/list` correctly lists
  the constructor under its canonical dotted form.
status: open
---

# `list_shows_ctor_once_canonical` assertion double-counts the deftype `; match:` hint

## Issue

`tests/repl_introspection.rs::list_shows_ctor_once_canonical` (authored
`a919bfd8`, S109 W1.2) evaluates:

```
(deftype (Maybe a) Nil (Some [:a v]))
/list
```

and asserts `out.stdout.matches("Some").count() == 1`, intending "the
constructor `Some` MUST be listed ONCE in `/list`, never duplicated as a
bare-alias second row (§17.19.2b, E4)".

The assertion counts the substring `Some` over the **entire** stdout, which
includes the deftype echo's `; match:` hint line:

```
0+0ms; user> :user/Maybe ; deftype
; match:
;  Nil Some          <-- one "Some" here (the match hint)
7+0ms; user> Types:
  Maybe Maybe.Nil Maybe.Some   <-- one "Some" here (the /list ctor row)
```

At the time the test was written, `/list` listed **zero** constructor rows, so
the only `Some` in the output came from the `; match:` hint and the count was
`1` — the test passed, but for the wrong reason (it never actually observed the
constructor **in `/list`** at all).

S109 Phase 6 target `list_types_includes_constructor_rows_under_canonical_dotted_form`
(committed `e755cce6`) requires `/list` to list each constructor once under its
canonical `Type.Ctor` form (spec `repl/spec.md` §3.3 / §17.19.2b). The `/dev`
fix for that target (S109, `src/repl.rs::handle_list` — the Constructor arm now
buckets ctor `Def`s into Types under their canonical dotted key) makes `/list`
emit `Maybe.Some`. The `Some` count over the whole stdout is now `2` (match hint
+ `/list` row), so `list_shows_ctor_once_canonical` fails.

The **intent** of `list_shows_ctor_once_canonical` is satisfied by the fix: the
constructor is listed exactly once in `/list` (`Maybe.Some`), and the bare `Some`
alias is an `Import` entry that `classify_listing_entry` excludes, so there is
**no** bare-alias second row. Only the assertion's counting method is
mis-scoped.

## Requested change (`/testing`)

Tighten the assertion so it counts the constructor's appearance **in `/list`**,
not across the whole session echo. Either:

- count the canonical dotted form: `out.stdout.matches("Maybe.Some").count() == 1`
  (the `; match:` hint prints bare `Some`, so it no longer contributes); or
- scope the match to the `Types:` block of the `/list` output.

Both keep the E4 no-duplicate-bare-alias guard intact while tolerating the
now-required constructor row. This is the twin of the S109 p6 target
`list_types_includes_constructor_rows_under_canonical_dotted_form`; the two
should agree.
