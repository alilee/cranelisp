# Syntax and annotation — the frontend's declaration and annotation judgments

> Interior design for `cranelisp-frontend`, authored S116 and current at S121.
> It elaborates the master design (`frontend.md` §4);
> `design/arch/annotated-sexp-node.md` owns the cross-crate `Sexp::Annotated`
> carrier.

## 1. Boundary and current state

The frontend remains purely structural. It owns four judgments: read-time
`Sexp::Annotated` folding; malformed annotation and declaration-shape rejection;
definition-wide constructor/field uniqueness and type-parameter closure; and
structural parsing of the one §7.1 method tail without deciding whether it is a
type or default body.

There is one annotation carrier and one producer (Principles 7, 18, and 20). No
metadata sidecar, macro-only path, top-level path, or second annotation
representation is admissible.

**The read-time fold is landed.** `reader::read_colon_prefix` constructs
`Sexp::Annotated` directly, and no annotation mirror scans siblings any more. The
S116 migration order this section once carried — corpus repair, dormant carrier,
dormant consumers, the flip, the completion gates — is spent, and is not
re-stated here; `sprints/archive/sprint-116.md` holds it as a record. Two
consequences are load-bearing and are stated as current facts rather than as
work:

- **A trailing `:Type` with nothing to bind is a reader error.** Because the fold
  is universal, the introducer in `(dp [x] :Int)` is followed by `)` rather than
  by a form, and rejects at the introducer span with `annotation missing
  expression`. §7.1.1 always stated that rule; nothing enforced it, which is what
  let the invalid spelling colonise the corpus. This is the frontend arm of FIXME
  0785, and it is **structural** — the shape does not survive reading, so no
  predicate, position table or corpus discipline has to keep holding it. The
  positive fixtures 0785 listed have been rewritten to the valid bare-`Type`
  spelling; the spec's own malformed `(zed [] :a)` examples remain as negatives.
- **The `repl/demos/runs/` half of 0785 never existed.** Those directories are
  git-ignored per-replay artifacts (FIXME 0801, verified at S115); the tracked
  demo sources were repaired at S114. Nothing in `repl/` is a frontend
  prerequisite, and no frontend record schedules work against them.

What remains of 0785 is **not frontend's**: the `{parameter, return}` ×
`{annotated, bare}` × `{deftrait method, defn, deftype field}` matrix cell and
the proposed tracked-paths-only corpus lint are `qa`'s evidence questions against
a rule the reader now enforces. Frontend supplies the reject and its unit pins;
it does not own the instrument.

One residue of the flip is worth naming because it will read as design intent
otherwise. The annotation-pairing helpers still return `(Expr, usize)` and their
callers still do `consumed` arithmetic, but `build_one_expr_at` now always
consumes exactly one item — the width was the mirror's, and the mirror is gone.
Collapsing that pair to a plain `Expr` is a simplification the crate has earned;
**no S121 obligation schedules it**, and it is recorded here so a later reader
does not mistake vestigial arithmetic for a variable-width contract.

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

No frontend public function changes. The `Sexp::Annotated` baseline delta and its
persistence window belong to `cranelisp-types`; frontend is regenerated only if
tooling observes an incidental re-export delta.

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
required method; otherwise the same element is a default body. The shared carrier
chosen by `/arch` is the only handoff representation. Frontend must not encode an
early `Result<TypeExpr, Expr>` guess or recover from `invalid type expression`.
The deleted `[params] return-type body` spelling rejects as trailing input. An
annotated default body arrives as one `Sexp::Annotated`, so the tail is always
exactly one element and no special arity case exists.

## 5. Unit scenarios: submodule × class

Per Principle 23, `/dev(frontend)` locates tests beside each strategy submodule.

| Submodule | Complexity | Edge | Negative |
|---|---|---|---|
| `reader` | nested list/bracket/macro arguments; stacked annotations | top-level; qualified/compound half; quote/quasiquote; spaced colon; full span | EOF/`)`/`]` dangling subject; dangling qualifier; comment-preserving placement |
| `ast_builder` annotation | nested subject and bounds chain | qualified type; application operand; directly constructed node | non-type half; annotated node in a type-half slot |
| `quasiquote` | recurse annotation and subject | unquote in either half; quoted node | `~@` in either half |
| `ast_builder::deftype` | mixed polymorphic sum | documented nullary; distinct names; cross-type reuse; zero-field product | all forbidden spellings; duplicate ctor across spelling pairs; duplicate field same/cross-arm; trailing form; second-span assertion |
| `ast_builder::deftype` explicit types (§3.1) | written polymorphic head with reused and concrete parameters | bare monomorphic head with concrete field types | missing field type in product and sum arms; undeclared standalone and nested type variables; parenthesized head with no parameters; every reject asserts the field/head span and emits no `ParsedEntry` |
| `ast_builder::patterns` | nested binding pattern | bare nullary and fielded controls | `(Ctor)` zero-binding pattern |
| `ast_builder::traits` | application-shaped default body | required bare type; docstring; annotated default | missing tail; deleted three-element form; trailing `:Type` reader error |

E2e acceptance remains `/qa`/`/testing` owned and includes the complete
constructor matrix, duplicate field location, macro fold, round-trip/schema, and
§7.1 mode-equivalence cells.

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

## 7. Handoffs

- `spec` — **nothing open.** The user-approved §5.2.4 rule is explicit: a bare
  head is monomorphic, a parenthesized head is complete, and every field type is
  written.
- `qa` — the 0785 evidence tail: the `{parameter, return}` × `{annotated, bare}` ×
  `{deftrait method, defn, deftype field}` matrix cell against a rule the reader
  now enforces, and the corpus-lint instrument scoped to **tracked** paths per
  FIXME 0801. Also the spec-side traceability band for §5.2.4's explicit-head
  and explicit-field rules, including located negatives and no partial entry
  emission.
- `dev` (frontend) — landed in S121: no sequential allocator; every missing type
  and undeclared variable rejects before entry emission.
- `design`/`dev` (typecheck) — do not add a compensating declaration-shape check
  for §5.2.4; concrete-type resolution failure is a different diagnostic at a
  different seam.
- `sprint` — migrate active fixtures to explicit generic declarations without
  changing the behavior each fixture exercises.
  `crates/cranelisp-typecheck/src/checker/test_support.rs:547` says it registers
  `(deftype Box [:a v])` and
  `crates/cranelisp-types/src/heap/value_layout_tests.rs:323` says
  `(deftype Box (Box [:a value]))`; both build the AST by hand with `a` as a
  **written head parameter**, so the code is right and only the prose is wrong.
  Corrected spellings are `(deftype (Box a) [:a v])` and
  `(deftype (Box a) (Box [:a value]))`. No behavioural, signature or
  `public-api.txt` consequence, and no frontend edit — these are outside the
  frontend surface and are not part of its one-visit reservation.
- `review` (frontend) — reject annotation mirrors, partial `ParsedEntry` emission,
  first-occurrence locations, parse-time tail commitment, a surviving
  empty-string `TypeExpr::TypeVar`, any reject implemented as a post-hoc scan
  over already-allocated parameters, and — the omitted-mode leg's specific
  failure — a closure walk that reads the resolved `FieldDef` rather than the
  parsed field record's written half.
