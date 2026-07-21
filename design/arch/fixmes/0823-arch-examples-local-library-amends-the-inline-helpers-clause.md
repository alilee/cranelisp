---
number: 0823
target: /arch
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: root CLAUDE.md §"Design Principles" → "Stdlib separation" (the
  "define any needed helpers inline" clause) + examples/Cranelisp.toml
  (`lib-dirs = ["./lib"]`, already isolating examples from stdlib/) +
  examples/lib/prelude.cl (60 lines, zero definitions — a re-export
  pass-through) + design/arch/fixmes/0821-*.md (the scope question this
  ruling answers)
status: open
---

# User ruling: examples get their own minimal, lesson-derived library — amend the "inline helpers" clause

## The ruling (user, 2026-07-21)

Answering FIXME 0821. Verbatim intent:

> examples should have its own minimal library which will allow the examples to
> concentrate their attention. its library should follow from earlier lessons.
> the intent isn't to teach how to write applications — just to teach the core
> components of the language so the whole stdlib doesn't need to be available.
> just needs to be suggestive of what can be done with the language. to learn
> the stdlib, a learner would go to the stdlib docs, not the language examples.

Four constraints, all load-bearing:

1. **Examples have their own minimal library.** Not stdlib, not inline
   re-definition per file.
2. **The library follows from earlier lessons** — a helper enters it only after
   the example that teaches its mechanism. The library is *cumulative and
   pedagogically ordered*, which makes it a teaching artifact rather than a
   dependency.
3. **The purpose is the core language, not application-writing.** The library
   exists so examples can concentrate attention on the construct under study;
   it is **suggestive** of what the language can do, deliberately not complete.
4. **Learner routing is explicit**: the stdlib is learned from the stdlib docs;
   `examples/` teaches the language.

## Why this needs `/arch`

Root `CLAUDE.md` §"Stdlib separation" currently reads, for `tests/` and
`examples/` alike: *"They define any needed helpers **inline** using compiler
primitives and special forms."* The ruling supersedes that for `examples/`:
helpers live in the examples' own library instead of inline.

**The principle's purpose is untouched** — the point of stdlib separation is
that the language is validated independently of any particular library code,
and an examples-local library built only from compiler primitives and special
forms satisfies that completely (zero `stdlib/` dependency; `lib-dirs` already
enforces the isolation at `examples/Cranelisp.toml`, per spec §8.11.4). Only
the *placement* of the helpers moves. `tests/` is unaffected and keeps the
inline rule — tests want each file to stand alone.

Requested: amend the clause so it distinguishes the two trees, and record that
the examples-local library is (a) free-standing by construction and (b) a
teaching artifact whose contents are ordered by the lessons that precede them.

## What this dissolves

FIXME 0821 (the Tier-C scope question) is **answered** and should retire on
this ruling. Its evidence stands as the motivation: under the inline rule,
example 19 spends half its lines reimplementing `->`, example 23 opens by
apologising for the missing `do`, and example 20 hand-writes ~250 lines of what
"a derive macro would automate" — while the spec's own Appendix B examples are
all written in prelude vocabulary that the sequence could share with none of
them.

Note the mechanism is already in place and merely unused for this purpose:
`examples/lib/prelude.cl` exists, is on the search path, and today contains
**zero definitions** — it re-exports ~30 primitives and nothing else. The
ruling turns an existing pass-through into the artifact it should have been.

`/examples` owns the library's contents and ordering (it is in its tree); this
FIXME is only the principle amendment.
