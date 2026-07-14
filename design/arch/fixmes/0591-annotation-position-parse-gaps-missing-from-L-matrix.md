---
number: 0591
target: /qa
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: tests/plan/PLAN.md §L position map + crates/cranelisp-frontend/src/ast_builder.rs (build_defn_variant, build_fn, build_match_arms, build_if)
status: open
---

# §L position map is missing the positions where an annotation cannot even parse

## Severity
Important as a matrix gap (the §L family map is the lever against
per-position codepaths); the underlying behaviour is a pre-existing frontend
limitation, NOT introduced by e401cce9.

## Issue

Spec §3.9/§2.3.8: `:Type` binds the immediately-following form in ALL
positions. The §L position axis (defn param / fn param / deftype field /
body-return / let binding) omits four positions where an annotation today
fails at PARSE — verified live at HEAD (e401cce9):

```
(defn g ([:a x] :a x) ([:a x :Int n] x))
  → parse error: defn variant requires params and body
(fn [:a x] :a "s")
  → parse error: fn is single-arity: it takes one [params] bracket and a body
(match 5 [n :Int n])
  → parse error: match arms must have an even number of elements
(if true :Int 1 2)
  → parse error: if requires condition, then, and else branches
```

Mechanism: annotations tokenize as 1–2 EXTRA sexp children; only builders
routed through the annotation-pairing primitive `build_one_expr_at` /
`build_args_with_annotations` can consume them (call args, vec literals, let
binding values, match SCRUTINEE — the FIXME 0389 fix, single-arity defn body).
`build_defn_variant` (exact-2-children + `build_expr`), `build_fn`
(exact-count guard), `build_match_arms` (even-count + `build_expr` bodies),
and `build_if` (exact-4) never adopted it.

Uniformity consequence: the SAME body shape `[:a x] :a x` parses in
single-arity `defn` (FV-6, green) but is a parse error in a multi-arity
clause and in `fn` — an operation (annotation consumption) behaving
non-uniformly across the definition-variant family, the exact
coverage-by-definition-variants class
(memory/feedback_recurring_class_is_coverage_matrix_miss.md). Adjacent:
FIXME 0575/0576 (multi-arity `fn`/`defn` friction).

## Proposed resolution

1. `/qa` adds the four positions as rows in the §L position map with their
   CURRENT verdict (parse error — never `unknown type 'a'`, so the W6 fix's
   uniformity claim is bounded by parseability, not violated), plus a
   spec-conformance judgment: are these §2.3.8/§3.9 violations to schedule, or
   positions `/spec` should carve out?
2. If violations: attribute to frontend (`/dev` narrow-deployed there) — the
   fix shape is adopting `build_one_expr_at` at the four sites; each position
   then also needs its free-var (`:a`) cell so the typecheck seams get
   exercised (they should be covered for free via `Expr::Annotate` →
   `infer_annotate`, but the matrix is the proof).

## Context

Found by `/review` on e401cce9 (S109 W6) while enumerating every annotation
position for the uniformity check. Within everything that PARSES, the W6
seams are uniform: all `Expr::Annotate` positions route to `infer_annotate`
(mint), both param families to their mint seams; `deftype` field /
platform-sig contexts behave per design. The unparseable positions are the
remainder of the sweep.
