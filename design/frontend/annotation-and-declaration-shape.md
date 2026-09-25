# Annotation and Declaration Shape

> Interior design for `cranelisp-frontend`, elaborating the master design
> (`frontend.md` §3). `design/arch/annotated-sexp-node.md` owns the cross-crate
> `Sexp::Annotated` carrier.

## 1. Boundary

The frontend is purely structural here. It owns four judgments: read-time
`Sexp::Annotated` folding; malformed annotation and declaration-shape rejection;
definition-wide constructor and field uniqueness with type-parameter closure; and
structural parsing of the one §7.1 method tail **without** deciding whether that
tail is a type or a default body.

There is one annotation carrier and one producer (Principles 7, 18, 20). No
metadata sidecar, macro-only path, top-level path, or second annotation
representation is admissible.

**A trailing `:Type` with nothing to bind is a reader error.** Because the fold is
universal, the introducer in `(dp [x] :Int)` is followed by `)` rather than by a
form and rejects at the introducer span with `annotation missing expression` (spec
§7.1.1). The enforcement is **structural** — the shape does not survive reading —
so no predicate, position table or corpus discipline has to keep holding it.

One residue would otherwise read as design intent. `build_one_expr_at` still
returns `(Expr, usize)` and its callers still do `consumed` arithmetic, but it
always consumes exactly one item: the width belonged to a sibling-scanning
annotation mirror that no longer exists. Collapsing the pair to a plain `Expr` is
an available simplification; it is not a variable-width contract.

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

## 3. `deftype` enforcement

### 3.1 Type parameters and field types are explicit (spec §5.2.4)

The frontend enforces two declaration-head forms:

- a bare head, such as `Box`, declares a monomorphic type with no parameters;
- a parenthesized head, such as `(Box a)`, declares the complete parameter list.

Every product field and sum payload is written `:Type name`. A missing type is
a located error at the field name. A written type variable must be declared by
the parenthesized head; otherwise the error is also located at the field name.
Named and applied concrete types continue to resolve downstream under §8.5.

The parsed representation keeps `TypeParamMode::{Omitted, Written}` so a bare
head cannot be confused with a malformed empty parenthesized head. A parsed
field temporarily carries `Option<TypeExpr>` only to preserve a precise error
for missing syntax. `resolve_type_def` converts that local representation into
the boundary `FieldDef`, which always contains a real `TypeExpr`. There is no
sequential-variable allocator and no empty-string sentinel.

Validation finishes before any `ParsedEntry` is appended. Consequently an
invalid declaration cannot half-register its type, constructors, or product
accessors. Typecheck does not compensate for a missed declaration-shape check;
its responsibility begins with resolution of valid written types.

Examples:

```clojure
(deftype Named [:String name])                    ; legal monomorphic product
(deftype (Pair a b) [:a first :b second])        ; legal polymorphic product
(deftype (Option a) None (Some [:a value]))      ; legal polymorphic sum

(deftype Pair [first second])                    ; error: field type omitted
(deftype Box [:a value])                         ; error: bare head is monomorphic
(deftype (Box a) [:b value])                     ; error: b is undeclared
(deftype (Box) [:Int value])                     ; error: empty written head
```

### 3.2 Binder uniqueness

`parse_deftype` owns call-local validation state populated in source order. Every
arm first normalizes to one structural description, then checks its binders before
any `ParsedEntry` is appended:

- one set contains constructor names across bare, documented, fielded, and enum
  spellings;
- one field-name set is scoped to each constructor. A product has one synthetic
  constructor, so duplicate product fields reject. Distinct sum arms may reuse
  payload labels because those labels mint no callable accessor and are
  extracted only by `match`.

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
required method; otherwise the same element is a default body. The raw tail on the
types-owned method carrier is the only handoff representation. Frontend must not
encode an early `Result<TypeExpr, Expr>` guess or recover from `invalid type
expression` to anticipate that judgment. The three-element
`[params] return-type body` spelling rejects as trailing input. An
annotated default body arrives as one `Sexp::Annotated`, so the tail is always
exactly one element and no special arity case exists.

## 5. Unit scenarios: submodule × class

Module tests sit beside each submodule (Principle 23). Each row names the
scenario classes whose absence would leave a mechanism unpinned.

| Submodule | Complexity | Edge | Negative |
|---|---|---|---|
| `reader` | nested list/bracket/macro arguments; stacked annotations | top-level; qualified/compound half; quote/quasiquote; spaced colon; full span | EOF/`)`/`]` dangling subject; dangling qualifier; comment-preserving placement |
| `ast_builder` annotation | nested subject and bounds chain | qualified type; application operand; directly constructed node | non-type half; annotated node in a type-half slot |
| `quasiquote` | recurse annotation and subject | unquote in either half; quoted node | `~@` in either half |
| `ast_builder::deftype` | mixed polymorphic sum | documented nullary; distinct names; cross-type reuse; zero-field product | all forbidden spellings; duplicate ctor across spelling pairs; duplicate field same/cross-arm; trailing form; second-span assertion |
| `ast_builder::deftype` explicit types (§3.1) | written polymorphic head with reused and concrete parameters | bare monomorphic head with concrete field types | missing field type in product and sum arms; undeclared standalone and nested type variables; parenthesized head with no parameters; every reject asserts the field/head span and emits no `ParsedEntry` |
| `ast_builder::patterns` | nested binding pattern | bare nullary and fielded controls | `(Ctor)` zero-binding pattern |
| `ast_builder::traits` | application-shaped default body | required bare type; docstring; annotated default | missing tail; deleted three-element form; trailing `:Type` reader error |

## 6. Quality attributes

- **Simplicity/maintainability:** one recursive fold, one normalized arm parser,
  and one head mode carried in the type rather than inferred from an empty
  vector; no positional mirrors and no sentinel values (Principles 6 and 7).
- **Observability:** located introducer, malformed arm, trailing form, second
  duplicate, bare-field and unbound-variable diagnostics — each at the span the
  spec names, each naming the fix. All four §5.2.4 rejects share one span rule:
  the **field name**, in both modes and in both product and constructor arms.
- **Concurrency:** unchanged; state is call-local.
- **Performance:** one linear read, expected-linear uniqueness validation, and
  one linear walk of the written field types.
- **Testability:** the submodule matrix makes omissions visible; the §3.1 rejects
  are pinned by span, not merely by message (Principle 5), and the omitted-mode
  pair is chosen to discriminate the mechanism rather than confirm the symptom.

## 7. Boundaries with neighbouring owners

- **Typecheck adds no compensating declaration-shape check for §5.2.4.** Every
  declaration-shape reject is the frontend's and exclusive. A concrete-type
  resolution failure is a different diagnostic at a different seam, and
  duplicating the shape check there would split the rule across two owners.
- **Solution-level evidence is `qa`'s.** The frontend supplies the rejects and
  their unit pins; e2e matrices and any corpus lint are evidence questions
  against a rule the reader already enforces.
- **The §7.1 tail carrier is `arch`'s** (§4).

Five shapes are defects in this surface, and each has been built at least once:
an annotation mirror that scans siblings; partial `ParsedEntry` emission before
validation completes; a duplicate reported at the first occurrence rather than
the second; a reject implemented as a post-hoc scan over already-allocated
parameters; and a type-parameter closure walk that reads the resolved `FieldDef`
rather than the parsed field's written half.
