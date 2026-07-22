# Sprint 116 — syntax and annotation frontend design

> Phase-3 design for `cranelisp-frontend`. This elaborates the master design;
> `design/arch/annotated-sexp-node.md` owns the cross-crate carrier. FIXMEs 0708
> and 0838 remain open until implementation.

## 1. Boundary and migration order

The frontend remains purely structural. It owns four judgments: read-time
`Sexp::Annotated` folding; malformed annotation and constructor-shape rejection;
definition-wide constructor/field uniqueness; and structural parsing of the one
§7.1 method tail without deciding whether it is a type or default body.

The order is binding:

1. Repair FIXME 0785's positive corpus from invalid trailing `:Type` return
   spellings to bare `Type`, preserving genuine negatives.
2. Add the dormant `Sexp::Annotated` carrier and consumers in the coordinated
   schema-23/public-baseline window.
3. Add dormant frontend consumers and constructed-node unit scenarios while the
   old pairing path still produces input.
4. Flip `reader::read_colon_prefix`, then remove sibling-scanning annotation
   mirrors in the same coordinated wave.
5. Gate completion on the macro-argument RED, round-trip, and stale-cache cells.

There is one carrier and one producer (Principles 7, 18, and 20). No metadata
sidecar, macro-only path, top-level path, or second annotation representation is
admissible.

## 2. Read-time annotation fold

`read_colon_prefix` reads the raw annotation half with its colon stripped, then
uses the ordinary recursive form reader for the subject and constructs:

```text
Sexp::Annotated { annotation, subject, span }
```

Recursion makes the fold universal: top-level forms, list/application children,
bracket children, nested expressions, macro arguments, quote, and quasiquote all
receive the same node. `:A :B x` is a nested chain.

Malformed structure rejects at the earliest owner:

- no subject before EOF, `)`, or `]`: located reader error `annotation missing
  expression` at the introducer;
- dangling qualified annotation (`:foo/`, `:a.b/`): ordinary located qualified-
  name reader error, never degradation;
- non-type annotation half: located AST-builder type-expression error;
- `~@` in either single-form half under quasiquote: located splice error.

AST building consumes the node wherever it consumes one expression, converts the
raw half through the existing type-expression production, builds the subject,
and emits the existing `Expr::Annotate`; it never scans siblings. Qualified types
and stacked bounds retain their existing semantics. Quasiquote recurses into both
halves and emits `SexpAnnotated` without flattening or discarding the node.

No frontend public function changes. The Rust public-baseline delta belongs to
`cranelisp-types`; frontend is regenerated only if tooling observes an incidental
re-export delta. The sole persistence window is schema 22→23.

## 3. `deftype` enforcement

`parse_deftype` owns call-local validation state populated in source order. Every
arm first normalizes to one structural description, then checks its binders before
any `ParsedEntry` is appended:

- one set contains constructor names across bare, documented, fielded, and enum
  spellings;
- one set contains field names across the whole `deftype`, including different
  sum arms and product fields.

Insertion failure rejects at the duplicate binder's span: the second occurrence
is the error location. A later symbol-table overwrite never decides uniqueness,
and legal reuse in another `deftype` is unchanged.

The one arm parser enforces the settled spelling vocabulary: bare symbol is the
only nullary spelling; `(Ctor "doc")` is documented nullary when its name differs
from the type; fielded arms require a non-empty field list; `()`, `(Ctor)`,
`(Ctor [])`, nullary/type-name sharing, and trailing forms reject. The zero-field
product remains `(deftype Unit [])` at deftype level. Pattern parsing mirrors the
definition: a nullary constructor pattern is bare, never `(Ctor)`.

## 4. §7.1 one trailing element

`build_method_sig` accepts a name, optional docstring, parameter vector, and
exactly one raw trailing `Sexp`. Frontend validates that shape, preserves the tail
and its span, and does not invoke the type-expression parser merely because the
element follows parameters.

Typecheck owns the try-resolve judgment: resolvable type expression means a
required method; otherwise the same element is a default body. The shared carrier
chosen by `/arch` is the only handoff representation. Frontend must not encode an
early `Result<TypeExpr, Expr>` guess or recover from `invalid type expression`.
The deleted `[params] return-type body` spelling rejects as trailing input. After
the reader flip an annotated default body is one `Sexp::Annotated`, requiring no
special arity case.

## 5. Unit scenarios: submodule × class

Per Principle 23, `/dev(frontend)` locates tests beside each strategy submodule.

| Submodule | Complexity | Edge | Negative |
|---|---|---|---|
| `reader` | nested list/bracket/macro arguments; stacked annotations | top-level; qualified/compound half; quote/quasiquote; spaced colon; full span | EOF/`)`/`]` dangling subject; dangling qualifier; comment-preserving placement |
| `ast_builder` annotation | nested subject and bounds chain | qualified type; application operand; directly constructed node | non-type half; annotated node in a type-half slot |
| `quasiquote` | recurse annotation and subject | unquote in either half; quoted node | `~@` in either half |
| `ast_builder::deftype` | mixed polymorphic sum | documented nullary; distinct names; cross-type reuse; zero-field product | all forbidden spellings; duplicate ctor across spelling pairs; duplicate field same/cross-arm; trailing form; second-span assertion |
| `ast_builder::patterns` | nested binding pattern | bare nullary and fielded controls | `(Ctor)` zero-binding pattern |
| `ast_builder::traits` | application-shaped default body | required bare type; docstring; annotated default | missing tail; deleted three-element form; trailing `:Type` reader error |

E2e acceptance remains `/qa`/`/testing` owned and includes the complete
constructor matrix, duplicate field location, macro fold, round-trip/schema, and
§7.1 mode-equivalence cells.

## 6. Quality attributes

- **Simplicity/maintainability:** one recursive fold and one normalized arm
  parser; no positional mirrors (Principles 6 and 7).
- **Observability:** located introducer, malformed arm, trailing form, and second
  duplicate diagnostics.
- **Concurrency:** unchanged; state is call-local.
- **Performance:** one linear read and expected-linear uniqueness validation.
- **Testability:** constructed dormant nodes prove consumers before the flip
  (Principle 5); the submodule matrix makes omissions visible.

## Next skills

- `/arch` — confirm the method-tail carrier and single schema/public window.
- `/qa` and `/testing` — complete missing REDs and repair 0785 before the flip.
- `/dev` (frontend) — implement serially with the unit matrix.
- `/design` (typecheck) — specify the resolution half without re-parsing shape.
- `/review` (frontend) — reject annotation mirrors, partial entry emission,
  first-occurrence locations, and parse-time tail commitment.
