---
number: 0785
target: /qa
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/07-traits.md §7.1.1 ("Return position is a bare type_expr; the
  leading `:` is parameter-annotation syntax only … never `(zed [] :self)` /
  `(zed [] :a)`") vs ~25 accepted uses across tests/spec_07_traits.rs,
  tests/spec_05_definitions.rs:1594, tests/spec_qualified_name_sweep.rs:90,
  tests/w2_close_fences.rs:136/174, tests/repl_persist.rs:1229/1268, and
  committed repl/demos/runs/*/user.cl fixtures
status: open
---

# `:Type` in RETURN position is invalid syntax, silently accepted — and the corpus has normalised it (user-found, S115)

## Issue

**User observation (2026-07-21), verified by grep.** §7.1.1 states the rule as
a MUST and even spells the counterexamples. The compiler does not enforce it,
so the invalid form is accepted everywhere and the corpus has adopted it as
the house style:

```
tests/spec_07_traits.rs:1735   (size [:a x] :Int)
tests/spec_07_traits.rs:1803   (add2 [:a x :a y] :a)
tests/spec_07_traits.rs:2009   (dp [x] :Int)          (+ :2029/:2058/:2093)
tests/spec_07_traits.rs:2127   (qb [x] :Int)
tests/spec_07_traits.rs:2137   (qq [x] :primitives/Int)
tests/spec_07_traits.rs:840    (unwrap [:a x] :a)
tests/spec_05_definitions.rs:1594  (v [x] :primitives/Int)
tests/spec_qualified_name_sweep.rs:90 (scale [:primitives/Int x] :primitives/Int)
tests/w2_close_fences.rs:136/174  (dp [x] :Int)
tests/repl_persist.rs:1229/1268   (dp [x] :Int)
repl/demos/runs/*/user.cl         (size [:a x] :Int)   — committed demo fixtures
```

(`tests/spec_07_traits.rs:798/:1006` `(zed [] :a)` are legitimate — they are
the spec's own malformed example used as NEGATIVE fixtures. Everything else in
the list is a POSITIVE fixture written in invalid syntax.)

**Why this matters more than a style nit — it is a corpus-integrity defect.**
This is the same shape as FIXME 0702 (the dotted-binder axis, also an
unenforced §5 MUST): an unenforced MUST lets a wrong shape colonise the
corpus, and the corpus then becomes false evidence in later reasoning. It
already did, twice:

1. **S115 FIXME 0770.** Five "GREEN spec-traceable cells" were cited as
   evidence that §7.1.4 blesses no-`self` trait methods, framing an expensive
   (a)/(b) fork. Those cells are written in invalid return syntax; one of them
   (`impl_bare_type_target_dispatches_control`) *pins* `(add2 3 4)` → `:a 7`,
   i.e. it certifies an unresolved type variable in a result position as
   expected output.
2. The user's standing lesson — *verify the example is well-formed before
   framing a fork* (S109) — recurring exactly.

**Interaction with the S116 0708 implementation (sequencing-critical).** Under
the user's Reading-A-structural ruling, `:` folds onto the following form at
READ time. In `(dp [x] :Int)` the `:Int` has no following form, so it becomes
the trailing-introducer reader error (`annotation missing expression`,
`design/arch/annotated-sexp-node.md` §2). **The 0708 implementation will
therefore light up every fixture in the list above.** Repairing the corpus is
a prerequisite for that wave, not a follow-on — otherwise S116 opens with ~25
"regressions" that are actually pre-existing invalid syntax.

## Proposed resolution

`/qa` owns the attribution + matrix; the mechanical parts route from there:

1. **Attribute the enforcement gap.** Frontend/typecheck signature parsing
   accepts a leading `:` in return position. **Opportunity: S115 W5 is the
   frontend wave already landing the 0702 unenforced-MUST enforcement** — the
   same class, same crate, same shape of fix (one predicate at the signature
   seam). If it fits, land it there; the located-reject requirement matches
   0702's (`assert_err_span_at` precedent).
2. **Draw the matrix cell**: `{parameter, return}` × `{annotated, bare}` ×
   `{deftrait method, defn, deftype field}` — the return-position column has
   never been tested for rejection. This is the coverage-by-definition-variants
   category again.
3. **Repair the corpus** (`/testing`): ~25 positive fixtures rewritten to the
   valid form (`(dp [x] Int)`, `(size [x] Int)`, and for `add2`/`unwrap`
   whatever the 0770 ruling makes well-formed). Keep the two `(zed [] :a)`
   negative fixtures. The committed `repl/demos/runs/*` fixtures are `/repl`'s.
4. **Sweep for the sibling question**: is `:Type` accepted in any OTHER
   position the spec restricts (deftype field returns, `defn` return types,
   match-arm positions)? A single unenforced annotation-position rule is
   cheap to fix once and expensive to keep rediscovering.

## Context

Found by the user while reading S115 W4 evidence, not by any test or sweep —
which is itself the finding: no instrument watches for "the corpus is written
in a form the spec forbids". Candidate standing instrument (route to `/qa`'s
coverage process): a corpus lint that parses every `.cl` fixture and committed
example against the spec's own grammar productions, so an unenforced MUST
cannot silently become the house style.
