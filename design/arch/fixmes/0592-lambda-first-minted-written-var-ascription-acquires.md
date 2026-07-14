---
number: 0592
target: /dev
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: crates/cranelisp-typecheck/src/infer.rs::infer_lambda + infer_annotate (rigidity keyed per mint-site, not per written name)
status: open
---

# A written var first minted by a nested `fn` param stays flexible — a later body ascription silently ACQUIRES it

## Severity
Important — **Blocker-candidate**: the ascription face is a MUST-3
(assert-not-acquire) violation live at HEAD `b2bfb760`; it is the exact
acquire class W6.2 exists to kill, resurfacing through one uncovered variant
cell. `/sprint` disposes; the by-use face needs a `/spec`→user ruling first.

## Issue

Rigidity is decided at the **mint site** (`infer_annotate` marks only the ids
*it* mints rigid; `infer_lambda` deliberately leaves its minted ids flexible —
FV-15), but the minted name registers in the **definition-wide**
`written_var_scope` (SCOPE-5 co-reference, correct). A name whose first
occurrence is a nested-`fn` param annotation is therefore flexible for the
whole rest of the definition body — including inside a later `:b e`
**ascription**, which then acquires instead of asserting. Rigidity is
order-dependent for the same program text.

Live repros (REPL, HEAD = b2bfb760, primitives-only prelude):

```
(defn f [x] ((fn [:b y] y) :b "hello"))  ; → :(Fn [a] primitives/String) user/f  ← ACCEPTED
(f 3)                                     ; → :primitives/String "hello"          ← acquired world runs
(defn g [x] ((fn [y] y) :b "hello"))     ; → skolem-escape type error             ← control: same ascription, no lambda mint
```

The only difference between `f` and `g` is that `f`'s lambda wrote `:b`
first. MUST-3 has no first-mint-site exemption: `:b "hello"` ascribes a
concrete `String` to a bare written variable of the definition (u7/SCOPE-5's
own reading — "a fresh identifier first appearing in an inner `fn` still
registers in and is quantified at the enclosing definition's scope") and MUST
be rejected.

**Second face (needs `/spec` ruling before fixing, do NOT fix blind):**
`(defn h [x] ((fn [:b y] y) 3))` is ACCEPTED — the enclosing body pins the
inner-only written var **by use**. Strict SCOPE-5 + MUST-1/MUST-4 reads this
as skolem-escape too, but FV-15's realization *requires* by-use pinning
(top-level `((fn [:a x] x) 3)` is checked inside the synthetic `__expr` defn
wrap, i.e. it IS a nested lambda — making inner-lambda vars rigid breaks
FV-15 as realized). The two faces must be settled together: what is the
rigidity story of a written var whose outermost binder is a nested `fn`
inside a definition — flexible-for-use but assert-on-ascription? fully
rigid (and FV-15 re-realized another way)? fully flexible (spec text then
needs a carve-out from MUST-3)?

## Proposed resolution

1. `/spec` frames the lambda-written-var corner for the user (the W6.2 ruling
   settled co-reference, not the rigidity of inner-first-minted names).
2. `/dev` implements per ruling. If the ascription face is confirmed (likely
   — MUST-3 as written): make the assert semantics hold at the `infer_annotate`
   seam regardless of where the name was first minted (e.g. rigidify-on-assert
   or track per-name rigidity in the written scope), keeping FV-15 green.
   Unit test at the program seam pins the `f`/`g` contrast above.
3. `/qa`: the matrix axis this fell through is "position of FIRST introduction
   of the name" (defn-param / body-annotate / lambda-param) × "later reuse
   site" — FV-20 covers only outer-param-first; FV-15 only standalone. Add the
   lambda-param-first × later-ascription (neg) and lambda-param-first ×
   later-use cells.

## Context

Found by `/review` on b2bfb760 (S109 W6.2) probing the rigid/flexible boundary
adversarially (dispatch priority 5/6). Root cause is representational
(Principle 20): rigidity is a set of TypeIds keyed by mint event, while the
model's unit is the written NAME within its definition scope; the two disagree
exactly when mint-site and use-site rigidity differ. Same seam family as
0588 (per-`Annotate` fresh map) — the scope now threads, but the rigidity
attribute does not thread with the name.
