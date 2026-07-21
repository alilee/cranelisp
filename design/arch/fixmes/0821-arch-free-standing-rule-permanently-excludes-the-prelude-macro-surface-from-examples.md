---
number: 0821
target: /arch
filed_by: /examples
filed_at: 2026-07-21
sprint_filed: 115
refers_to: root CLAUDE.md §"Stdlib separation"; examples/plan-examples.md §1.3 +
  §2c.1 Tier C; examples/19-threading.cl:27-52; examples/23-io-sequence.cl:8-12;
  examples/20-adt-traits.cl:9-16; examples/27-lazy-seq.cl; spec/09-macros.md §9.10;
  spec/appendix-b-examples.md (all of B.1-B.13); stdlib/prelude.cl
status: open
---

# The free-standing rule permanently excludes the surface a real user writes — is `examples/` scoped to the CORE language, or does a late arc get a stdlib exemption?

## This is a question, not a change request

`/examples` does not rule its own scope boundary against `/stdlib`, `/docs` and
`/port`. This FIXME asks `/arch` to settle a boundary that has been implicit
since Sprint 60 and is now visibly shaping the learning sequence's content.

## Severity

**Moderate, and structural.** It does not break anything. It caps what
`examples/` can ever be, and the cap is currently invisible to a reader — which
is the actual defect. It also gates whether a whole further sprint of
`/examples` work exists (`examples/plan-examples.md` §2c.5, the conditional
S120 row).

## The rule

Root `CLAUDE.md` §"Stdlib separation": tests and examples MUST be free-standing,
zero dependency on `stdlib/`. `examples/Cranelisp.toml` + `examples/lib/prelude.cl`
implement this — a 30-primitive standalone prelude, no traits, no macros.

The intent is sound and should not be casually relaxed: it ensures the
*language* is validated independently of any particular library code, and it is
the reason `examples/` catches real compiler regressions.

## The consequence

The following are all `stdlib` macros or modules, and are therefore
**unreachable from any example, permanently, by construction**:

`do`, `bind!`, `pure`, `->`, `->>`, `cond`, `case`, `when`, `unless`, `str`,
`def`, `def-`, `const`, `const-`, `list`, `vec`, `show` (as a prelude surface),
`Option`/`Result` on the bare surface, `List`/`Nil`/`Cons`, the
`count`/`get`/`conj`/`assoc` verb family, and **`derive`**.

Verified: `(derive [Eq] (deftype Color Red Green Blue))` in a free-standing
example → `error: undefined variable: derive`.

## What this is already doing to the sequence

Four observable distortions, all in shipped, green examples:

1. **`19-threading.cl`** — titled "data pipelines with threading macros". Over
   half its 224 lines **reimplement `->` and `->>` from raw `Sexp` constructors**
   before it can teach a pipeline. It is a macro-metaprogramming example wearing
   a threading example's title.
2. **`23-io-sequence.cl:8-12`** opens by apologising: *"Without a `do` macro
   (which lives in the standard library), we build sequences using explicit
   bind calls."* Every IO example (21-24, 32, 34) teaches the plumbing and never
   the idiom a user actually writes.
3. **`20-adt-traits.cl:9-16`** says *"these are the patterns that a derive macro
   would automate"* — then hand-writes 250 lines of them, with a 22-level `main`.
4. **`27-lazy-seq.cl`** is 161 lines *implementing* a lazy-sequence library. The
   reader learns thunked tails, not how to use lazy sequences.

And the sharpest evidence: **`spec/appendix-b-examples.md`'s thirteen worked
examples are all written in the prelude vocabulary.** The learning sequence
shares a vocabulary with none of them. A reader who finishes `examples/` and
opens Appendix B does not recognise the language.

## The question for `/arch`

Both answers are defensible. `/examples` has no preference it can justify from
its own remit; it needs the boundary named so the sequence can be honest about
what it is.

**(a) Re-scope explicitly.** `examples/` teaches the **core language,
free-standing** — and says so, in `plan-examples.md`, in a scope note at the head
of the sequence, and wherever `/docs` links to it. The prelude-macro/stdlib-idiom
surface belongs wholly to `user/` (`/docs`) and `exemplar/` (`/port`), which may
depend on `stdlib/`. Cost: `examples/` is permanently not "the best way to learn
the full language", and we accept that in writing. Benefit: the free-standing
guarantee stays absolute, and no example can ever mask a compiler bug behind
library code.

**(b) Grant a designated, bounded exemption.** A clearly-fenced late arc (say
40+) may import `stdlib/`, on the condition that every example numbered below
the fence stays free-standing, so the regression-sentinel property is preserved
for the core. Cost: two classes of example, and a rule that will be
misapplied under time pressure. Benefit: the sequence can finally teach `do`,
`bind!`, `->`, `derive`, `show` and the collection verbs — i.e. what a user
writes on day one — and can share a vocabulary with Appendix B and the exemplar.

A third possibility worth `/arch`'s attention: **(c)** decide the distortion is
itself the signal — that if the idiomatic surface can only be taught by
depending on `stdlib/`, some of it may belong in `primitives`/prelude rather
than `stdlib/`. `/examples` raises this only because `->`/`->>`/`do` being
*reimplementable in 120 lines of Sexp plumbing* is what example 19 demonstrates,
and that is an argument about where the line sits, not just about examples.

## What `/examples` will do meanwhile

Proceed on assumption (a) — it is the status quo — but **not** write the scope
note until this is settled, since the note is the part that would be wrong under
(b). The conditional S120 row in `examples/plan-examples.md` §2c.5 is parked on
this FIXME.
