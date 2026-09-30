# The `Sexp::Annotated` node — read-time annotation fold contract

**Status: current cross-crate contract, delivered.** `:Type <form>` folds at
read time into one structural `Sexp::Annotated` node, so every consumer —
macros included — sees the annotation in the tree. The user ruled this shape
on 2026-07-21 (the "structural" reading); a metadata side-channel
was rejected because an annotation asserts a type and must not be silently
lost (`spec/01-lexical.md` §1.4.5, `spec/02-grammar.md` §2.3.8, and the macro
rows of `spec/09-macros.md`). The residual work is
[the mirror residue below](#7-the-mirrors-the-node-replaces).

## 1. The node shape

`cranelisp_types::Sexp::Annotated { annotation, subject, span }`
(`crates/cranelisp-types/src/sexp.rs`):

- `annotation` is the raw form following `:`, with the colon stripped:
  `Symbol("Int")` for `:Int`, `Symbol("primitives/Int")` for a qualified name,
  the compound `List` for `:(Fn [a] a)`.
- `subject` is the immediately following form the annotation binds.
- `span` runs from the introducer to the end of the subject.

Design rules:

- **Named fields.** It is the only variant with two same-typed slots; naming
  makes annotation/subject transposition unwritable
  ([Principle 20](principles/20-model-invariants-by-representation.md)).
- **The annotation half is a raw `Sexp`, never a `TypeExpr`.**
  - The reader is purely syntactic; type grammar belongs to the AST builder.
  - Macros quote, unquote and destructure the half through the Sexp-shaped
    `macros/Sexp` ADT (§3), and `` `(f : ~t x) `` needs the half to hold an
    arbitrary pre-desugar form.
  - `build_type_expr` remains the sole type-grammar gate. The reader folds
    whatever the half is (`:5 x` folds); the AST builder rejects a non-type
    half with a located error.
- **The node is the colon.** Stripping it makes simple and compound halves
  uniform and removes annotation-ness from symbol text: there is no `:X`
  symbol that could stand alone
  ([Principle 18](principles/18-enforce-invariants-structurally.md)).

## 2. Fold semantics

- **One rule, one site.** The reader's colon-prefix path is the fold. It reads
  the half — the adjacent symbol run including a qualified tail, or for a bare
  `:` the next form — then the subject as the next form. Because form reading
  is recursive, the fold applies in every Sexp-producing context: top level,
  list and bracket interiors (`[:Int x :Int y]` is two nodes), quote and
  quasiquote bodies, and macro-argument position.
- **Nesting.** `:A :B x` is `Annotated(A, Annotated(B, x))`. Stacked bounds
  (`spec/03-types.md` §3.9.3) walk the chain: length above one is
  `TypeExpr::Bounds`; length one is the try-type-then-trait carrier.
- **Spaced bare colon.** `: Int x` and `: (Fn [a] a) x` fold identically to the
  adjacent spellings.
- **Errors.** An introducer with nothing to bind (end of input, before `)` or
  `]`) is a located reader error, `annotation missing expression`. The
  non-type-half reject stays in the AST builder. `:foo/` stays a located
  reject.
- **Quote and quasiquote.** The fold precedes quote handling, so `'(:Int 5)`
  evaluates to a `macros/SexpAnnotated` value. Int's quote shield holds list
  heads and is unaffected.
- **Unquote in either half** is ordinary template expansion:
  `` `(f : ~t x) `` gives `Annotated((unquote t), x)`. **`~@` as a half** is a
  located error naming the annotation slot, because both slots hold one form.
- **Comments** between the introducer and its halves, in the
  comment-preserving reader mode only, are hoisted before the node. Source
  regeneration is source-text-first, so fidelity is unaffected.

## 3. The macro-facing contract

- **Arity is right by construction.** Int counts macro arguments as raw `Sexp`s
  before AST build, so `(def x :Int 5)` presents two arguments: `x` and
  `Annotated(Int, 5)`.
- **The language ADT.** `macros/Sexp` has the appended constructor
  `(SexpAnnotated [:Sexp stype :Sexp sform])` at `TAG_SEXP_ANNOTATED`
  (`crates/cranelisp-types/src/marshal.rs`); earlier tags are stable. The
  production seed (`src/bootstrap.rs`) and typecheck's test-fixture seed
  (`crates/cranelisp-typecheck/src/builtins.rs`) register constructors in the
  same order and change together.
- **Marshalling.** Compile-side `sexp_to_runtime`/`runtime_to_sexp`
  (`src/marshal.rs`) and runtime-side `quote_sexp_build`
  (`crates/cranelisp-primitives/src/marshal.rs`) carry a real arm for the
  two-child cell. Release is intrinsics' `consume_sexp`
  ([macro-turn ownership](../int/macro-turn-ownership.md)).
- **What a macro owes.**
  - A clause that binds an argument and only splices it transports the node
    unexamined, so splice-transparent macros are correct without change.
  - A clause that matches an argument's constructors and receives an
    annotated form hits its ordinary, located match miss. The author adds a
    `(macros/SexpAnnotated t f)` arm or unwraps; the ruling accepted this
    bounded tax.
  - Rebuild through the constructor or through `:` syntax in a quasiquote
    template. The stdlib's `core.syntax` helpers `annotated?`, `annotation`
    and `unannotate` are conveniences, not part of the mechanism
    ([macro-authoring guide](../../user/syntax-cheatsheet-plan.md#macro-authoring-reader-annotations)).
- **Expansion and qualification walks treat the halves alike.** The
  expander's scoped walk and int's qualify walk share one binder model
  ([expansion-qualification scope](../int/expansion-qualification-scope.md)):
  - the **subject** is expression position and is walked normally;
  - a **bare `Symbol` half** is held verbatim;
  - a **compound half** is recursed, which qualifies cross-module type names
    inside compound annotations.

  Namespace-aware qualification of simple annotation names is an unopened
  `spec`/`design` question; the parity rule is complete without it.

## 4. Printing and round-trip

- The Sexp printers render `:{annotation} {subject}`, the colon adjacent to the
  half (`:Int x`, `:(Fn [a] a) x`). The REPL pretty-printer renders the half
  in the type role and the subject by its own kind; verbatim styling works
  over source bytes and is byte-identical by construction.
- The `:Type value` echo envelope (`display::envelope`) renders resolved
  `Type`s, not Sexps, so the fold does not affect it.
- Round-trip law: `read(print(t)) == t` modulo spans for every tree containing
  `Annotated`, and `verbatim_source_slice`'s re-parse consistency gate holds.

## 5. Consumers

- **Compile-forced.** Exhaustive `Sexp` matches — the span and printer
  methods, the frontend quasiquote templates, int's span rewriting and the
  pretty-printer — cannot omit the node.
- **Wildcard or shape-guarded walks must name it.** The AST builder consumes
  the node into `Expr::Annotate`; macro parameter parsing rejects it in a
  binder slot, because macro parameters are untyped; the expansion and
  qualification walks follow §3; marshalling, source regeneration and REPL
  formatting carry explicit arms. A new wildcard walk over expansion input
  must decide the node explicitly; review checks it, because the compiler
  cannot.
- **Typecheck and backend read no `Sexp`.** Typecheck consumes
  `Expr::Annotate`; its only `Sexp` contact is the fixture seed in §3.

## 6. Persistence

- `Sexp` is persisted on cache-carried fields — macro declarations' stored
  Sexp and `ModDecl.inline_body` — so the variant is part of the
  `CACHE_SCHEMA_VERSION` contract
  ([types memory](../../crates/cranelisp-types/CLAUDE.md#the-serde-shape-is-the-cache-contract)).
- Marshal tags are runtime-only and never serialised.

## 7. The mirrors the node replaces

The node replaces every lexical test for annotation-ness: a `starts_with(':')`
or other string-prefix dispatch standing in for `Sexp::Annotated` is a review
reject. Four `src/` mirrors of the pre-fold shape remain —
`worker::leading_annotation_len` (a constant-zero stub),
`save.rs::is_bare_colon`, `expander::is_annotation_symbol`, and
`pretty.rs::is_type_annotation_list` with its helpers. Their disposition and
arming evidence are in [Binary/int §16.0](../int/int.md).
Each replacement must re-express the rule over the node; deleting a test
while leaving the lexical check under another name is a review reject.
