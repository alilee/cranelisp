---
number: 0838
target: /dev (frontend + typecheck)
filed_by: /docs
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/07-traits.md §7.1 (one `method_sig` production, S115 user ruling
  2026-07-21, commit `4f09a9f9`) + §7.1.5 (default methods); the parser's
  return-type slot in the `deftrait` reader/parser path
status: open
---

# The settled one-production `method_sig` is not implemented: a default method written per §7.1 is a parse error, and the only spelling that works is the three-element form the spec just deleted

## Severity

Important (spec/implementation divergence on a surface that shipped this sprint;
every default method in the corpus, in `spec/`'s own worked examples, and in any
doc that teaches §7.1 as written, is unwritable at HEAD)

## Issue

`spec/07-traits.md` §7.1 now has **one** production —

```ebnf
method_sig = '(' method_name docstring? '[' param* ']' ( type_expr | expr ) ')'
```

— with exactly one trailing element: a **type expression** ⇒ required method, any
**other expression** ⇒ default method whose body that expression is. There is
explicitly **no** three-element `[params] ret_type body` form; §7.1 says so in
terms, and the implementation note warns that "a parser that commits the trailing
element to a return-type slot before resolution will reject every conforming
default method."

That is exactly what HEAD does. Verified against `target/debug/cranelisp`
(built 2026-07-21 11:22, i.e. at `4f09a9f9`), run from a scratch dir with
`CRANELISP_LIB=…/stdlib`:

**The settled spelling is rejected.**

```clojure
(import [primitives [add-i64 Pure]])
(deftrait Sized
  (size [x] Int)
  (tag [x] (add-i64 (size x) 1000)))          ;; §7.1 default method
(deftype Box [:Int n])
(impl Sized Box (defn size [b] (match b [(Box v) v])))
(defn main [] (Pure (tag (Box 5))))
```

```
d1.cl:3:30: error: module error at 62..66: module 'd1' failed:
  parse error at 62..66: invalid type expression
```

**The deleted spelling is the one that works.** Change line 4 to
`(tag [x] Int (add-i64 (size x) 1000))` and the same program exits `237`
(`1005 mod 256`) — correct. A stray colon in the return slot is also tolerated
(`(tag [x] :Int (add-i64 …))` also exits `237`), which is the separately-tracked
FIXME 0785 surface.

Consequences worth naming:

- **The spec's own worked `Ord` example does not compile.** §7.1 was rewritten so
  that `(<= [a b] (not (> a b)))` is legal *as written*; at HEAD it is a parse
  error. The same holds for §7.1.5's `(<= "…" [a b] :Bool (not (> a b)))` pin
  form and for `(greet [] "hi")`.
- **The discrimination rule is resolution-time, not parse-time.** §7.1 requires a
  *try*-resolve that can answer "this is not a type" without raising; the current
  path raises `invalid type expression` from the parser, before any resolution
  could happen. This is a structural change, not a grammar tweak.
- **FIXME 0832's repro is written in the deleted spelling** (its own closing note
  anticipates this); it will need respelling once this lands, though the defect it
  isolates is independent.

## Impact on `user/`

`user/guide/traits.md` now teaches default methods (S115 Phase 6b) — the inferred
type, the `:Type`-on-the-body pin, and the per-impl-template model. Because
`user/` is as-built, the section's transcripts use the **three-element** spelling
that works today, under an explicit note that §7.1 has no production for it and
that the parser has not caught up, citing this FIXME. When this is resolved,
`/docs` retires that note and respells the two transcripts; the teaching model
around them is unaffected.

## Ask

Implement §7.1's single production: recognise the trailing element by
**resolution** (type expression ⇒ required; anything else ⇒ default body), and
remove the three-element acceptance. Coordinate with 0785 (the tolerated
return-position `:`) and with the S116 `:`-fold, which is what makes
`(zed [] :self)` a located reader error rather than a silently-accepted spelling.
