# AST Builder

Interior design for `crates/cranelisp-frontend/src/ast_builder.rs` — the
`Sexp`-to-AST translation. It validates structural well-formedness, desugars
syntactic shapes, and produces the parsed AST values every downstream stage
consumes.

```
Vec<Sexp>  --[ast_builder]-->  Vec<TopLevel> / Vec<ParsedEntry> / Expr / TypeExpr
```

## 1. Entry points

Three public entries plus the type-expression entry, and they are the complete
set of AST-entry chokepoints:

| Entry | Shape | Driven by |
|---|---|---|
| `build_forms(&[Sexp]) -> Vec<TopLevel>` | the whole form sequence, including top-level annotated expressions | int's one form-build path (`src/worker.rs`) |
| `build_form(&Sexp) -> Vec<ParsedEntry>` | one top-level form | test helpers only; production reaches the same dispatch through `build_forms` |
| `build_expr(&Sexp) -> Expr` | one expression | the internal recursion primitive, and typecheck's §7.1 method-tail judgment |
| `parse_type_expr(&str) -> TypeExpr` | one type-expression string | the platform loader, REPL `/search`, and typecheck's §7.1 method-tail judgment (§4) |

`build_forms` and `build_form` are the two forms-entry chokepoints, and each
desugars the reader-quote family as its first step so no caller can forget it
(`quasiquote-fold.md` §1). `build_expr` does not fold: folding there would re-walk
each subtree once per level of depth, so it trusts its input and keeps the
surviving-quote-head backstop as the structural guard instead. Typecheck's
direct calls are safe under that contract because the method tail it builds is a
subtree of a form `build_forms` has already desugared.

There is no batch-versus-REPL split at this boundary. One classifier decides what
a top-level head is, and the policy difference — the REPL accepts a bare
expression where batch does not — lives at the rim in int, not in two parallel
builders.

## 2. `build_form` — the per-form shape

### 2.1 Why a vector

`build_form` returns `Vec<ParsedEntry>` because some source shapes yield more
than one entry:

- `(deftype Name … (V₁ f₁) (V₂ f₂))` → one `TypeDef` **plus** one `Constructor`
  per variant, the `TypeDef` first and the constructors in declaration order. A
  three-constructor sum type yields four entries.
- `(defmacro name clause₁ clause₂ …)` → exactly one `Macro` carrying **all**
  clauses inside `DefmacroInfo`. Clause-level `Defn` synthesis is a separate
  later step (`defmacro-synthesis.md`), not a per-clause entry here.
- `(defn name [params] body)` → exactly one `Def`. Multiple `(params body)` arms
  are `DefnVariant`s inside that one entry.
- `(deftrait …)` → one `TraitDecl`; `(impl …)` → one `TraitImpl`.

`ParsedEntry` values are **transient**: they live in orchestrator-local memory for
one cluster, are consumed by signature checking and then body checking, and drop
with the frame. Nothing the frontend produces aliases into a symbol table, and
the values are deliberately not serialisable — the cache stores post-typecheck
shapes, never parsed ones.

### 2.2 Dispatch through one head classifier

`classify_head(head) -> HeadKind` is the single place that answers "what is this
top-level head". It yields `Def { base, visibility }` (folding the `-` private
suffix into a visibility bit rather than a second vocabulary), `Defmacro`,
`Impl`, `Begin`, `StructuralDecl(kind)`, or `Expr`. `build_form` dispatches on
that result to the per-shape parsers; `module_extract`'s peel and the `begin`
recognisers consume the same classification rather than re-listing the vocabulary
(Principle 7). A new top-level form is one classifier arm plus one parser.

### 2.3 What `build_form` does not accept

Three shapes are rejected with a located diagnostic rather than handled, because
each means an orchestration step was skipped:

- **`(begin …)`** — the orchestrator flattens a cluster at the REPL-input
  boundary via `flatten_begin` and calls `build_form` on each inner form
  independently. A `begin` reaching the builder is a caller bug.
- **Structural declarations** (`mod`/`mod-`/`import`/`export`/`platform`) — peeled
  by `extract_module_declarations` before per-form processing (BC §1 invariant 3).
- **Bare expressions** — top-level forms have a defined vocabulary; anything else
  is either an already-peeled declaration or an expression for `build_expr`.

Macro expansion is also a caller precondition, but the builder cannot enforce it:
it consults no symbol table, so it cannot tell a macro call from a function call.
An unexpanded macro call builds as an ordinary `Expr::Apply` and fails later in
typecheck. Keeping expansion ahead of building is int's orchestration contract.

### 2.4 Clusters are the orchestrator's, not the builder's

The frontend is cluster-blind. `is_begin` and `flatten_begin` are recognition
helpers the orchestrator uses to decide what one cluster is; `build_form` sees
only the individual forms. Two `begin` rules therefore live on the orchestrator
side and are named here only so the builder is not expected to validate them:
`begin` is invalid at batch top level (a file's forms are already one cluster),
and module-phase declarations may not appear nested inside a `begin`.

## 3. Head and binder policy

Every declaration head is a **binder**, not a reference: it introduces a new name
into the current module and must be bare. One shared reject enforces that at every
binder position, and `binder-head-reject.md` owns the rule, the predicate and the
site set.

The complementary rule for **reference** positions is the shared name splitter.
`type_ref_from_name` and `trait_ref_from_name` split a written name at the last
`/` into `(Some(module), name)` when both halves are non-empty, leaving a bare
name with `module: None` — the spec §8.5 canonicalisation rule. Every site that
builds a `TypeRef` or `TraitRef` from a written name routes through them. Hand-
rolling `TypeRef::new(None, TypeName::from(name))` instead is the defect shape
that re-roots `primitives/Int` under the current module as a phantom
`user/primitives/Int`; the splitters exist so that shape has one home rather than
one per position.

Dotted names are transported, not resolved. `Box.v`, `Option.Some` and `Num.+`
reach `Expr::Var` with the dot retained and un-split. Resolution — deciding
whether a dotted member is a constructor, a trait method or a field accessor — is
typecheck's, and the frontend crossing that line would mean the frontend
resolving names (Principle 17).

## 4. Type expressions

`build_type_expr` translates a `Sexp` in annotation position:

| Written | Built |
|---|---|
| uppercase symbol | `TypeExpr::Named` |
| lowercase symbol | `TypeExpr::TypeVar` |
| `self` | `TypeExpr::SelfType` |
| `(Fn [params] ret)` | `TypeExpr::FnType` |
| `(Name args…)` | `TypeExpr::Applied` |

A module-qualified lowercase name is **not** a type variable — a type
variable is a bare lowercase identifier — so it routes to `Named` through the
splitter rather than minting a `TypeVar` that carries a `/`. The decision is made
where type-variable-ness is decided, so no downstream capability inherits the
looseness.

`parse_type_expr(source)` is the named string entry: parse, require exactly one
form, build the type expression. It takes `&str` alone — no source id — matching
`parse`'s shape, because a type signature from a DLL descriptor has no meaningful
source file and its spans are byte offsets into the signature string like every
other frontend parse. It returns `TypeExpr` (syntactic) and never `Type`
(resolved): the int platform loader chains it into typecheck's resolution entry,
which does the second half.

Annotations arrive already folded into `Sexp::Annotated` by the reader
(`annotation-and-declaration-shape.md` §2). `build_expr` lowers the node to
`Expr::Annotate`, building its annotation half through `build_type_expr`. In a
parameter binder, a stacked run such as `:Eq :Display a` is peeled as one run
because `:` binds the immediately following form. A run of length one stays the
single `TypeExpr`, so typecheck can try type then trait resolution; a longer run
can only be trait bounds and becomes `TypeExpr::Bounds`.

## 5. Operand positions and bodies

Every single-body operand position — `let` body, impl-method body, trait-default
body, `trace` operand — routes through one `build_body_to_end` seam, which pairs
the body via `build_one_expr_at` and rejects any form left after it.
Multi-operand positions route through `build_args_with_annotations`. A body built
without that tail check silently drops trailing forms, so the routing is the
invariant, not a convention; `enforcement-matrices.md` §1 states it and the
acceptance criterion.

## 6. Docstrings

Docstrings are detected positionally: a `Sexp::Str` at the docstring slot of a
top-level form is consumed as documentation. This is unambiguous rather than
heuristic, because a string in *expression* position is only ever reached through
`build_expr`, which is never called for the docstring slot. A string-valued `let`
binding is an expression and is unaffected.

## 7. `deftype` lowering

`parse_deftype` normalises three body spellings to one constructor list:

1. **enum** — `(deftype Color Red Green Blue)` → one nullary constructor per
   variant;
2. **product** — `(deftype Point [:Int x :Int y])` → one constructor named for the
   type, with typed fields;
3. **sum** — `(deftype (Option a) None (Some [:a val]))` → several constructors,
   some with fields.

The head mode and every field type are explicit: a bare head declares a
monomorphic type, a parenthesized head declares the complete type-parameter list,
and every field is written `:Type name`. A missing field type, or a field type
variable the head does not declare, is a located error before any entry is
emitted — so an invalid declaration can never half-register its type,
constructors or accessors. `annotation-and-declaration-shape.md` §3.1 records the
enforcement design and §3.2 the constructor and field uniqueness rules.

## 8. Patterns

`build_pattern` mirrors the definition shapes: `_` → `Pattern::Wildcard`; an
uppercase symbol → a nullary `Pattern::Constructor`; a lowercase symbol →
`Pattern::Var`; `(Constructor bindings…)` → a constructor pattern with field
bindings. A nullary constructor pattern is bare, never `(Ctor)` — the pattern
vocabulary matches the definition vocabulary exactly, so a reader who can write a
`deftype` can write its patterns.

The constructor-pattern *head* is a reference, so a qualified or dotted spelling
there is legal and splits; the binding symbols are binders and reject.

## Cross-references

- `design/arch/bounded-contexts.md` §1 — invariants 3, 9, 10.
- `crates/cranelisp-types/src/parsed.rs` — `ParsedEntry` and its variants.
- `design/frontend/annotation-and-declaration-shape.md` — annotation fold, `deftype` enforcement, the trait tail specified in [trait declarations](../../spec/07-traits.md#71-trait-declaration-testedneg-testsspec07traitsdeftraitdeclarationsucceeds-testsnondispatchabletraitmethod0709nondispatchablemethodrejectedatdeclarationwithoccurrencereason).
- `design/frontend/binder-head-reject.md` — the binder reject and its sites.
- `design/frontend/enforcement-matrices.md` — the body seam and the reader rejects.
- `design/frontend/trait-impl-head-parse.md` — `deftrait`/`impl` head shape.
- `design/typecheck/typecheck.md` — the resolution side of names this builder transports.
