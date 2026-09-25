# Trait and Impl Head Parsing

Interior design for the `deftrait` and `impl` head shapes in
`crates/cranelisp-frontend/src/ast_builder.rs`. Spec: `spec/07-traits.md` §7.2
(the `deftrait` head grammar), §7.3 and §7.3.4 (the `impl` form — slot 1 echoes
the declared head, slot 2 names the target), §7.3.5 (kind matching, a
**typecheck** seam).

## 1. Head shape and written spelling

An `impl`'s slot 1 echoes the `deftrait` head as declared:

```clojure
(impl Display String         …)   ; slot 1 = Display,     conventional
(impl (Functor f) (Functor Option) …)   ; slot 1 = (Functor f), higher-kinded
```

| Slot-1 shape | Trait kind | `head_con_var` |
|---|---|---|
| bare `Display` | conventional (kind `*`) | `None` |
| `(Functor f)` | higher-kinded | `Some("f")` |

Slot 1 is fixed, not inferable (spec §7.1/§7.3), which is why the parser records
it rather than deriving it.

## 2. What the parser does — and the hard line

**Does:**

1. Accept both slot-1 shapes, recording the shape and written constructor-variable spelling.
2. Route the head trait name through `trait_ref_from_name` in **both** shapes, so
   a qualified echoed head splits per spec §8.5 instead of re-rooting under the
   current module. For the parenthesized shape the name is the head element.
3. Leave slot 2 on the existing target path. `(Functor Option)` parses to an
   applied type expression like any other; the parser assigns it no special
   meaning.

**Does not** (Principle 24 — resolve once; one classifier):

- **No kind classification.** The parser does not decide whether the trait is
  conventional or higher-kinded, does not read any trait declaration, and does
  not inspect slot 2 to infer a kind.
- **No echo validation.** Slot 1's shape and constructor-variable spelling
  are checked at typecheck's §7.3.5 seam, the single site that holds the
  declaration. A parser-side echo check would be a second classifier that could
  only ever agree with the kind-driven one.
- **No slot-2 interpretation.** `(Functor Option)`-as-pairing versus
  `(Option a)`-as-application is resolved by the declared kind at that same seam,
  before slot 2 is inspected. The parser emits the same applied shape for both.

The parser's whole contribution is: parse the two shapes into a well-formed
`(TraitRef, Option<Symbol>)`, and surface a located diagnostic for a structurally
malformed slot 1. Everything semantic is downstream.

## 3. One grammar for the head shape

Spec §7.3 states that the slot-1 shape **is** the `deftrait` head shape. If
`parse_impl` carried its own copy of that shape logic, the two could drift — a
head that `deftrait` accepts but `impl` rejects would make a legal echo
unparseable, the precise failure §7.3 forbids.

`parse_trait_head_shape` is therefore the one structural parser: it enforces
`Symbol` or a two-element `(UppercaseSymbol symbol)` list and returns the raw
head name with the con_var, if any.

**Each caller keeps its own name policy, and that divergence is intentional:**

- `build_trait_head` (deftrait) takes the name as a home-module name with no
  split, and folds the con_var into the declared type parameters;
- `parse_impl` routes the name through `trait_ref_from_name` — a qualified echoed
  head is a *reference* — and stores the con_var into `head_con_var`.

So the **shape** grammar is single-sourced while the **name** policy stays where
it belongs. The same split governs the binder reject: the con_var reject lives in
the shared parser (a con_var binds in both forms), the trait-name binder reject
lives in the deftrait caller only (`binder-head-reject.md` §3).

## 4. Malformed slot-1 diagnostics

Every rejection is a located `parse_err` at the span of the offending head,
rendering the form via `Sexp::format_flat` and never `{:?}`, and each names the
fix.

| Written slot 1 | Fault | Fix named |
|---|---|---|
| `(impl (Functor) …)` | head is missing its constructor variable | write `(Functor f)` |
| `(impl (Functor f g) …)` | too many elements | a higher-kinded head is `(Trait con_var)` |
| `(impl () …)` | empty head | write the bare trait name, or `(Trait con_var)` |
| `(impl ((Functor f)) …)` | head element is not a symbol | the trait name must be a bare symbol |
| `(impl (functor f) …)` | trait name must start with uppercase | — |
| `(impl (Functor 3) …)` | constructor variable must be a symbol | write a name, e.g. `(Functor f)` |

Two judgments hold the table together.

**Dispatch order is head-symbol before arity.** The `((Functor f))` row is
subtle: its slot 1 is a one-element list whose sole element is itself a list, not
the "two elements with a non-symbol head" the row's plain reading suggests. A
naive arity-first dispatch would hit the one-element arm and report a missing
constructor variable — misleading, since the real fault is that the head element
is not a bare symbol. The shared parser therefore checks that the head element is
a bare uppercase symbol **first**, and only then dispatches on length. That
ordering is what makes every row report its intended fault.

**The message is phrased neutrally** ("trait head …") so one string reads
correctly for both callers, rather than each caller wrapping the shared error.

**con_var lowercase is enforced at parse.** Spec §7.2 says
`con_var = lowercase_symbol`, and the shared seam is the one place where a single
check covers `deftrait` and `impl` together, so the two forms cannot drift:
`(deftrait (Functor F) …)` and `(impl (Functor F) …)` both reject at parse.

## 5. The carrier

`TraitImpl.head_con_var: Option<Symbol>` carries the written constructor-variable spelling; `None` records a bare head. It is
`#[serde(default)]`, so a bare-head impl parsed fresh sets `None`, which equals
the serde default — the field is additive to the persisted shape and needs no
schema bump of its own. A bare slot 1 flows through the identical name-splitting
and target-building path it always did, with `None` attached.

## 6. Sibling parse and re-emit sites

`parse_impl` is the **sole** parse site for the form. The question that matters
for a grammar change is what else *re-emits* it, and the answer is a genuine
design strength worth stating.

The REPL pretty-printer and the session-persistence regenerator both walk the
`Sexp` tree **structurally**. They render nested lists generically and are
entirely form-agnostic; `"impl"` appears in the printer only to select body
indentation, and neither pattern-matches the internals of an impl form. The
parenthesized head is ordinary nested s-expressions, so:

- `/sexp` and `/source` render it faithfully by construction;
- source regeneration round-trips it — the preferred path re-emits the authored
  bytes verbatim, and the structural fallback re-emits the nested lists — and
  either way the regenerated form re-parses through the same `parse_impl`.

**Because these serialisers never learned the impl grammar, they cannot fall out
of sync with it.** Round-trip fidelity is inherited from the structural design
rather than added; it is a behaviour to verify with an end-to-end test, not code
to write.

The one site that *does* shift under a trait-kind model change is the REPL's
resolved-impl display, which renders from resolved entries rather than the parsed
AST. That is an int display concern downstream of typecheck, not a frontend parse
concern.

## 7. Typecheck validates the echo

The parser preserves the written constructor-variable spelling in
`head_con_var`. Typecheck validates both shape and spelling against the
resolved declaration ([HKT design](../typecheck/hkt.md) §5.4 step 3;
[trait specification](../../spec/07-traits.md) §7.3 and §7.3.5).
The existing guard
`tests/spec_07_traits.rs::hkt_impl_echo_wrong_convar_spelling_rejected_neg`
falsifies a regression that accepts `(Functor g)` for declared `(Functor f)`.

## 8. Principles

- **Principle 7** — one head-shape grammar for `deftrait` and `impl`; the
  form-agnostic serialisers that cannot drift from it (§6).
- **Principle 24** — the parser records the shape and spelling and does no kind
  classification, echo validation or slot-2 interpretation.
- **Principle 5** — `parse_impl` stays a pure `&[Sexp]` → `TraitImpl` function,
  unit-testable with no session.

## Cross-references

- `spec/07-traits.md` §7.2, §7.3, §7.3.5.
- `design/typecheck/hkt.md` §5.4 — the Case-3 seam that reads what this parses.
- `design/frontend/binder-head-reject.md` §3 — the shared-parser versus caller-policy split for the binder reject.
