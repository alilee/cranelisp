---
number: 0789
target: /arch
filed_by: /dev (src)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-frontend/src/quasiquote.rs::is_quote/is_quasiquote/
  is_unquote/is_unquote_splicing (crate-private) vs src/expander.rs::quote_head
  (the int-side single source, S115 W6 / FIXME 0718 §2.4)
status: open
---

# The reader-quote structural predicate exists in three places; only two can be single-sourced today

## Issue

`design/int/expansion-qualification-scope.md` §2.4 (and FIXME 0718, now resolved)
require the qualify walk's new quote shield to recognize the reader-quote family
with "the SAME `quasiquote.rs::is_quote`/`is_quasiquote` the expander shield +
fold use — never a private copy (Principle 7)".

That could not be done as written: `is_quote`, `is_quasiquote`, `is_unquote` and
`is_unquote_splicing` are **crate-private `fn`s** in
`crates/cranelisp-frontend/src/quasiquote.rs` — not `pub`, not re-exported (the
crate exports only `expand_quasiquotes`/`expand_quote_template`/
`next_synthetic_span`). `src/` cannot call them, so the expander has always
carried its own inline structural test.

What landed instead (S115 W6): the int-side test is hoisted into ONE shared
classifier — `src/expander.rs::quote_head(&[Sexp]) -> Option<QuoteHead>` — and
BOTH int walks now call it (`expand_scoped` + `shield_qq`, and the new
`qualify_scoped` + `qualify_shield_qq`). So the two walks the design was worried
about are genuinely in lockstep, and int holds exactly one copy. The **third**
copy — the frontend fold's own predicates — remains, one crate away.

The coupling is real: the shields exist precisely to hand quoted subtrees to the
fold intact. If the fold's notion of "is a quote" and int's ever diverge, a
subtree is double-desugared, mis-qualified, or expanded-then-desugared
(`quote-shield.md` §5 names this as the durable hazard).

## Proposed resolution

`/arch` rules whether the four predicates become part of `cranelisp-frontend`'s
public surface (a `public-api.txt` delta on that crate) — or whether they belong
in `cranelisp-types` beside `Sexp`, which is where a purely structural,
consumer-agnostic shape test arguably belongs, and which both frontend and int
already depend on. Either way the three copies collapse to one and
`src/expander.rs::quote_head` becomes a thin re-export.

No behavioural change is expected — the tests are byte-identical today
(bare-symbol head + `len() == 2`). This is a Principle-7 consolidation with a
cross-crate surface decision that `/dev` may not take unilaterally.

## Context

`/dev`(src) S115 W6, resolving FIXME 0718 §2.4. The int-side consolidation and
its unit pins landed in that change-set
(`process_form::macro_resolution::tests::qualify_holds_quoted_datum_verbatim`,
`…qualify_quasiquote_holds_template_but_qualifies_live_unquote`,
`…qualify_quasiquote_nested_unquote_is_not_live`).
