# Operand-Position and Annotation-Lexing Enforcement

Interior design for two frontend enforcement families that are **not** binder
heads (that axis is `binder-head-reject.md`):

1. **Operand-position ascription and trailing forms** — `:Type body` ascription
   (spec §2.3.8) and the rejection of anything left after a body.
2. **Annotation and reference qualified-name lexing** — the dangling-qualifier
   rejects (`:foo/`, `foo/`, `/bar`) and the rule that an annotation's type half
   must be a type expression.

Both are *coverage-by-definition-variants* classes: when each expression-position
parser carries its own subset of the checks, no `variant × {bare, ascribed,
trailing}` matrix forces one codepath. The design names the one codepath, so that
a hole is a routing failure rather than a missing check.

## 1. The operand-position body seam

**Every single-body operand position routes through one `build_body_to_end`
seam.** It builds the trailing body expression through the one-expression
primitive `build_one_expr_at`, then requires that the body consumed everything
left, rejecting any remaining form at its own span.

The positions it serves: the `let` body, the impl-method body, the trait
default-method body, and the `trace` operand. Multi-operand positions route
through `build_args_with_annotations` instead.

**A raw `build_expr` call plus a hand-rolled or missing tail check is the defect
shape.** Where the position is not arity-locked it silently drops trailing forms,
so `(defn name [p] body junk)` inside an `impl` would lose `junk` without a word.
Routing through the one seam closes the class.

**Acceptance is structural, not example-based.** No expression-position parser
calls raw `build_expr` for its *body* or hand-rolls a tail check. A change that
fixes the currently known bad positions but leaves another un-routed has not
closed the class. `parse_defn` and `build_defn_variant` satisfy the criterion
through their own routed tail and may adopt the seam for uniformity without being
required to.

Positions that narrow *deliberately* are unaffected: an impl method legitimately
narrows to single-arity and no docstring per spec §7.3.

## 2. The constructor-tail sibling

A `deftype` constructor's tail is a bracket, not an expression, so it does not
use the body seam — but it shares the discipline. After consuming a valid field
bracket, `build_constructor_def` requires that nothing follows, rejecting the
next form located and naming the fix.

Without it, `(deftype Box (Box [:Int n] extra))` would drop `extra` and yield a
one-field `Box`: the same "a valid body followed by junk is silently dropped"
class as §1, in the one parser whose tail is not an expression.

## 3. Annotation and reference qualified-name lexing

The governing rule: `:` is a reader macro in the `^` style. Whitespace between
`:` and its form is allowed (`: Int` ≡ `:Int`); the annotation half must be a
type expression; `:foo/` errors; bare `foo/` errors anywhere; `/bar` (empty
module half) errors; and bare `/` — division — stands.

### 3.1 One fold for every spelling

`read_colon_prefix` handles the compact (`:Int`), spaced (`: Int`) and compound
(`: (Fn [Int] Int)`) spellings alike: it reads the annotation half, then the
subject, and returns one `Sexp::Annotated` node
(`annotation-and-declaration-shape.md` §2). Space tolerance is therefore part of
the one fold, not a second spelling path, and no bare `:` token reaches the AST
builder to be mistaken for a variable.

### 3.2 The dangling-qualifier reject lives at the reader

The both-halves-non-empty rule is a **lexical** property — whether a `/` has a
non-empty name on each side — and it is decided where the token is formed.

**Why not the AST builder.** `foo/` and `/bar` never form a single `module/name`
string that reaches the name splitters: `/bar` tokenises as two forms and `foo/`
errors before composing. The downstream both-halves-non-empty guards therefore
*cannot* see them. The only site where adjacency and emptiness are both known is
tokenisation. The splitters' guards remain as defence-in-depth for the one
degenerate name that still legally reaches them — bare `/`, the division operator
as a value.

Three reader facts realise it:

1. **One fallible dotted-module-path lexer, `consume_dotted_module_path`,** used
   by both the symbol path and the annotation path. It returns the consumed path
   when a `/` terminated the run, nothing when none did, and a located error on a
   dangling qualifier. One helper means annotation position and value position
   give the same diagnostic by construction; a second copy of the loop is how an
   annotation-side fault can silently degrade `:foo/` to `:foo`.
2. **An empty-module-half guard at `read_operator`.** A lone `/` immediately
   followed, with no whitespace boundary, by a symbol start is a dangling
   qualifier with an empty module half. The guard keys on operator text **exactly
   `"/"`** and on symbol adjacency, so `(/ 6 2)`, `(map / xs)` and a trailing `/`
   stay the division operator, and `*foo`, `<foo`, `->` are untouched
   (Principle 16).
3. **The dangling-qualifier diagnostic names the shape and the remedy** — it
   requires `mod/name` and explains how to write the bare name. A reader unit pin
   owns the exact words; this design relies on the remedy being present, not on a
   duplicated string.

**`(/ 6 2)` evaluating to 3 is the acid test** that the qualifier reject has not
over-reached.

### 3.3 The annotation half must be a type expression

The AST builder converts the annotation half of every `Sexp::Annotated` through
`build_type_expr`. A form that is not a type expression is a **located** error at
that form; nothing falls through to a variable or to an opaque downstream
"unresolved symbol" diagnostic.

Scope fence: this rejects a **non-type form**. A lowercase name after `:` is a
legal type-variable annotation and is routed, not rejected —
`binder-head-reject.md` §5 owns that routing.

## Cross-references

- `spec/02-grammar.md` §2.3.8 — annotation in every expression position.
- `spec/01-lexical.md` §1.4.5, `spec/08-modules.md` §8.5.1 — the qualified-name lexical rules.
- `design/frontend/reader.md` — the reader's structure and the name rules in context.
- `design/frontend/binder-head-reject.md` — the binder family, and §5 for annotation routing.
