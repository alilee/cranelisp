---
number: 0825
target: /spec
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/02-grammar.md:200 (`default_method` EBNF) + spec/07-traits.md
  §7.1 ("Disambiguation") + §7.1.5 ("Default Method Implementations") vs
  crates/cranelisp-frontend/src/ast_builder.rs::build_method_sig
status: open
---

# The `default_method` grammar and both worked `Ord` examples do not compile — §7.1's "Disambiguation" prose says the opposite, and the compiler follows the prose

## Severity

Blocker (spec self-contradiction on a shipped surface; every spec-conforming
default method is a compile error, and the surface is taught by no example)

## Issue

Three normative statements disagree about the shape of a default method:

- **`spec/02-grammar.md:200`** — `default_method = '(' method_name docstring? '[' param+ ']' expr ')'`. **No return type.**
- **`spec/07-traits.md` §7.1.5** — "Default methods have a body expression as the last element (**rather than** a return type). The return type of a default method is **inferred from its body**."
- **`spec/07-traits.md` §7.1 "Disambiguation"** — "The element immediately following the parameter bracket is **always the return type**; if a further element follows it, that element is the default body: `(method_name "doc"? [params] ret_type body)`."

The **worked examples in §7.1 and §7.1.5 are both written in the EBNF/§7.1.5
form**, not the Disambiguation form:

```clojure
(deftrait Ord
  (< [a b] Bool)
  (> [a b] Bool)
  (<= [a b] (not (> a b)))       ;; §7.1 AND §7.1.5, verbatim
  (>= [a b] (not (< a b))))
```

The compiler implements the **Disambiguation** reading:
`build_method_sig` (`crates/cranelisp-frontend/src/ast_builder.rs:1256–1262`)
takes `children[next+1]` as the return type unconditionally and only treats a
*further* element as `default_body`. So the spec's own example is parsed with
`(not (> a b))` in **return-type** position and dies in type resolution.

Probed live at `6e4b3612` (`target/debug/cranelisp --run`, names changed only to
avoid the prelude §8.6.4 conflict):

```
;; §7.1 / §7.1.5 / EBNF form — FAILS
(deftrait MyOrd (lt2 [a b] Bool) (ge2 [a b] (not (lt2 a b))))
→ type error: unknown type `not` (from module ``)

;; nullary variant of the same form — FAILS EARLIER, at the reader
(deftrait Greet (greet [] "hi"))
→ parse error at 26..30: invalid type expression

;; Disambiguation form — the ONLY form that works
(deftrait Shw (show2 [x] String) (shout2 [x] String (show2 x)))
→ accepted
```

Corroborating evidence that this surface is unexercised: **no `deftrait` in
`stdlib/`, `examples/`, or `exemplar/` declares a default method at all** — every
trait there is required-methods-only, including the `Ord` that is the spec's own
worked default-method example (`stdlib/compare/ord.cl` declares `<= >=` as
required `Bool` methods and every impl supplies them explicitly). `/examples`
independently reported at S115 Phase-6a that trait default methods are taught by
no example.

## Why this is filed to `/spec` first, not `/testing`

Which reading is normative is a **language question, not an implementation
choice**, and the two readings are not cosmetically different:

- If **§7.1.5 + the EBNF** are normative, the compiler has a frontend defect
  (return-type inference for default bodies is unimplemented) and every existing
  `[params] ret_type body` spelling becomes non-conforming.
- If **§7.1 "Disambiguation"** is normative, then §7.1.5's "rather than a return
  type / inferred from its body" sentence, the `default_method` EBNF production,
  and **both worked `Ord` examples** are wrong and must be repaired — the same
  class as the two spec-example defects already repaired at S115 W5a
  (§7.1.4's `Convertible`, §3.7.1's `fmap`).

A repro cannot be written until the direction is known, so no test is owed yet.

## Requested

1. Bring the question to the user (per `/spec`'s arbitration role) and record the
   ruling at §7.1.5 with a dated `[S115]` tag.
2. Repair whichever of {EBNF `default_method`, §7.1.5 prose, §7.1 Disambiguation,
   the two `Ord` examples} the ruling makes wrong — the three must agree and the
   examples must be in the ruled form.
3. Hand off to `/testing` for a repro cell (and, if the ruling favours §7.1.5, to
   `/dev`(frontend) for the fix). The probes above are the minimal repro.

## Adjacent (do not conflate)

This is **not** a regression from the S115 W8 occurrence-rule widening. The
widened rule reads `TraitMethodSig.ret_type`, which for the *working*
(Disambiguation) form is a genuine declared return type — the predicate does not
read a body. Under the *spec* form the body lands in `ret_type` and can be
scanned, but every such method with a bare parameter is rescued by the parameter
occurrence, so the widening kills nothing the spec form would otherwise allow.
It does mean the reject message's closing clause ("or the return type is `self`")
reads oddly to anyone who wrote a spec-form default method — see the note in
FIXME 0826.
