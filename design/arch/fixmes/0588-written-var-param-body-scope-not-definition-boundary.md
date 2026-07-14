---
number: 0588
target: /dev
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: crates/cranelisp-typecheck/src/infer.rs::infer_annotate (per-Annotate fresh var_map) + program.rs::register_defn_signature
status: open
---

# Written free-var annotation scope is per-`Annotate`-occurrence, not per-definition-boundary

## Severity
Important — Blocker-candidate if `/spec`/user confirm the strict §3.3 reading
(the shipped code then ACCEPTS programs the spec rejects). `/sprint` disposes.

## Issue

The W6 fix (`e401cce9`) gives `register_defn_signature` ONE shared `var_map`
per signature (param↔param co-reference — FV-8, correct) but `infer_annotate`
builds a FRESH empty `var_map` per `Expr::Annotate` node. Param↔body and
body↔body co-reference of the SAME written identifier therefore holds only
when unification incidentally connects them (i.e. the annotated expression is
the parameter itself, as in FV-6's fixture `(defn id [:a x] :a x)`).

Where unification cannot rescue, the identifier does NOT co-refer. Live repros
(REPL, HEAD = e401cce9):

```
(defn f [:a x] :a "hello")   ; → :(Fn [a] primitives/String) user/f
(f 3)                        ; → :primitives/String "hello"   ← ACCEPTED
```

Under one-var-per-identifier-per-definition-boundary (`a` co-refers): scheme
must be `(Fn [String] String)` and `(f 3)` must be a unification error.

```
(defn h [:a x :b y] (str-concat :a "s" y))  ; → :(Fn [a primitives/String] primitives/String)
```

Body `:a` pinned to String; param `:a` untouched — two variables for one
written identifier inside one definition.

## Normative basis

- spec/03-types.md §3.3 [S109] MUST-1: the written var is "implicitly
  universally quantified **at the function definition boundary**" — an
  identifier cannot be quantified twice at one boundary.
- tests/plan/PLAN.md §L.1 FV-6: "the SAME written var in param annotation and
  body annotation **MUST co-refer within one definition boundary**".
- §L.1 FV-8 citation: "§3.3 (**one definition boundary = one var per
  identifier**)".
- §L unit enumeration u2: "same identifier within ONE definition boundary ⇒
  SAME variable (param↔param FV-8, **param↔body FV-6**)". The landed
  `u2_same_ident_same_var_distinct_ident_fresh` pins only the resolve-seam
  shared-map property; no test pins param↔body at the program seam — and the
  shipped mechanism doesn't share the map there.

**Counter-reading to settle first** (route through `/spec` → user): §3.3 also
says "identically to an inference-generated variable", and inference vars have
no names to co-refer by — under that reading each occurrence mints fresh and
unification is the only linker, which is exactly what shipped. The two
readings are observably different (the repros above). Also settle the nested
boundary: in `(defn f [:a x] (fn [:a y] y))`, is the inner `fn` a NEW
quantification boundary for `a` (fresh) or inside the outer scope
(scoped-type-variables)?

## Proposed resolution

1. `/spec` frames the scope question for the user (definition-boundary named
   scope vs per-occurrence-fresh; nested-`fn` boundary rule).
2. If the shared-scope reading is confirmed: `/dev` threads one
   definition-level var scope from `register_defn_signature` through body
   checking into `infer_annotate` (and `infer_lambda` per the nested ruling),
   instead of a fresh map per Annotate; unit test at the program seam pins
   `(defn f [:a x] :a "hello")` → `(Fn [String] String)`.
3. `/qa` adds the missing §L cells either way: param↔body where unification
   cannot rescue, and body↔body pair (`(defn h [x y] ... :a x ... :a y ...)`).

## Context

Found by `/review` reviewing e401cce9 (S109 W6). The change-set's stated
design ("param↔body co-ref via unification", SPRINT.md W6 /dev row) was
verified and holds for every §L fixture — all 13 FV rows green, PINs hold —
but the mechanism diverges from the plan's stated model one step outside the
fixtures. Principle 20 (model invariants by representation): if the invariant
is "one var per identifier per boundary", represent it as one scope object,
not as an emergent property of unification.
