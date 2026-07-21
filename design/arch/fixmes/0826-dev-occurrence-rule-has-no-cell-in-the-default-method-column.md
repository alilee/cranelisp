---
number: 0826
target: /dev
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/traits/registry/tests.rs
  (`occurrence_decl` fixture, §7.1.1 cell block) + registry.rs:207–221
status: open
---

# The occurrence rule's unit cells have no `default_body: Some(..)` column — the widened reject newly reaches default methods and nothing pins the behaviour

## Severity

Important (coverage-matrix miss in the variant family the S115 W8 widening
enlarged; behaviour is correct today, verified by probe, but unpinned)

## Issue

The S115 W8 widening (`6e4b3612`) changed the guard from
`method.params.is_empty() && !method_mentions_self(method)` to
`!method_mentions_self(method)`. That makes the reject reachable for a
**default** method for the first time: a default method with a non-empty,
all-annotated parameter list was previously rescued by the arity leg and is now
rejected.

Verified live at `6e4b3612`:

```
(deftrait Cv (cv [:Int n] String (int->string n)))
→ type error: trait `Cv` method `cv`: no occurrence of the implementing type
  to dispatch on — …
```

That reject is **correct** under the ruled scope (the method is undispatchable
by construction, exactly as its required-method twin). But the whole
occurrence-rule cell block runs through one fixture,
`occurrence_decl(..)` (`registry/tests.rs:141`), which hard-codes
`default_body: None`. Every one of the seven cells is therefore in the
**required-method column only**. The variant family the rule must behave
uniformly across is `occurrence × {required, default}`, and the second column is
empty at both tiers (there is no e2e default-method cell either — see FIXME 0805
for the required-method arity column, and FIXME 0825 for why the surface is
untaught).

This is the standing coverage-by-definition-variants category: an operation that
must behave uniformly across a variant family, with one variant untested, is how
each variant grows its own codepath. The risk here is concrete and near: the
predicate reads `TraitMethodSig.ret_type`, and for a default method the meaning
of that field is exactly what FIXME 0825 shows the spec contradicts itself
about. If 0825 resolves toward §7.1.5 (return type **inferred from the body**,
no `ret_type` slot), the occurrence predicate's return-position leg loses its
input for default methods and the rule must be re-derived for that column —
with no cell to catch the change.

## Requested

Add to `registry/tests.rs`, in the §7.1.1 block:

1. **Accept** — a default method whose parameters carry the occurrence:
   `(dbl [x] self <body>)` with `default_body: Some(..)`. This is the specific
   over-reach guard: *a default method whose body happens not to mention the
   implementing type must not be rejected on that basis* — the reject must key
   on the signature, never on the body.
2. **Reject** — a default method with an all-annotated non-`self` parameter list
   and a concrete return, carrying the spec-pinned reason substring
   (`(cv [:Int n] String <body>)`).

Both need `occurrence_decl` to take the `default_body` (or a sibling
`occurrence_decl_with_default`); do not add a second fixture copy.

## Secondary (Suggestion, same file)

The reject message's closing clause is "…or the return type is `self`". For a
default method the author wrote a body, and under the spec's §7.1.5 reading
there is no return type at all, so the clause names a move the reader may not
recognise as available. Once 0825 is ruled, consider whether the message needs a
default-method-aware clause — but do **not** split the message into two
variants: the spec-pinned substring "no occurrence of the implementing type"
must stay one string emitted from one site.
