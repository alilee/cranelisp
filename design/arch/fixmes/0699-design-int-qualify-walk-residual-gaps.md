---
number: 0699
target: /design
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: src/process_form/macro_resolution.rs (qualify_scoped family) +
  design/int/expansion-qualification-scope.md §2.2/§2.3
status: open
---

# Qualify-walk residual gaps vs the "qualify iff free reference" ruling

## Severity
Important (item 1); Minor (items 2–4)

## Issue

The W5 scope-aware rework of `qualify_expanded_sexp` (commit `58ac8e46`,
FIXME 0670) correctly mirrors `expand_scoped`'s binder handling through the ONE
shared enumeration. Three residual asymmetries against the walk's own ruling
("qualification is a resolution-product operation; only a free REFERENCE is
qualified") survive, all pre-existing but now squarely inside the rebuilt walk:

1. **No quote shield (Important).** `expand_scoped` opens with Rule Q / Rule QQ
   (quoted DATA held out of the walk; only a LIVE unquote body re-entered —
   `quote-shield.md`). `qualify_scoped` has neither: it recurses into
   `(quote …)` and `quasiquote` templates as ordinary lists and will rewrite a
   quoted DATUM — e.g. a foreign macro expanding to `'(name)` where `name` is
   in a defining module and absent from the current module yields
   `'(dm/name)`, a different runtime value. A symbol inside quoted data is not
   a reference at all, so the §2.1 rule already excludes it; the design doc's
   §2.2 arm list just never named the quote family. Same defect family as 0613.
   Needs: design ruling + the Rule Q/QQ equivalent in the qualify walk (shared
   structural test, `quasiquote.rs::is_quote`/`is_quasiquote`) + a /qa cell.

2. **defn self-name not in body scope (Minor, ruling wanted).** The design's
   §2.3 table lists the defn NAME as a binder slot, and §2.1 says a local read
   of a bound name is held verbatim — but `qualify_defn` (like `expand_defn`)
   does not add the name to the body scope. Expansion output
   `(defn f [x] (f x))` where the defining module also provides `f` (and the
   current module does not yet — the defn is being defined this instant, so the
   availability skip cannot fire) mis-qualifies the recursive self-call to
   `dm/f`: silent wrong-target resolution, the same class as 0670 itself.
   Both walks share the shape, so the ruling should cover both.

3. **defmacro name/params asymmetry (Minor).** `expand_scoped` holds a
   `defmacro` head+name verbatim (CS-D1 shield); `qualify_scoped` treats a
   macro-emitted `(defmacro name …)` as ordinary children and can qualify the
   NAME/params on collision. The §2.3 legal-skip rationale ("those forms carry
   no value-level binder the pass could mis-qualify") does not hold as stated
   for this shape — either extend the walk or record why it is unreachable.

4. **Doc status refresh (Minor).** `expansion-qualification-scope.md`,
   `macro-marshal-rc-protection.md`, `prelude-table-write-isolation.md` all
   still carry "Status: DESIGN, pre-implementation" banners post-landing (the
   0604 doc's premise correction is 0698's item 3). Also
   `macro-diagnostic-reanchoring.md` §2.1: the landed multi-form fallback is
   the FIRST origin form's span, not "the cluster's own source span" — align
   the doc or the code.

## Proposed resolution

/design(int) rules on 1–3 (1 expected to route `target: /dev` with a /qa cell),
refreshes the doc banners, and aligns §2.1's fallback wording.

## Context

W5 /review of `58ac8e46`. The core 0670 fix is verified sound: shared
enumeration consumed by both walks (no private copy), binder-form coverage
complete against `is_binding_form` (defn/defn-/fn/lambda/let/match), unit
RED→GREEN fixture genuinely defeats the availability skip-guard.
