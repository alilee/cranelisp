# AST Builder Design

Solution design for `cranelisp-frontend/src/ast_builder.rs`: the Sexp-to-Expr/TopLevel translation phase.

## Overview

The AST builder is the second phase of the frontend pipeline. It receives `Vec<Sexp>` from the reader and produces `Vec<TopLevel>` (batch mode) or `ReplInput` (REPL mode). It validates structural well-formedness, desugars syntactic patterns, and produces typed AST nodes.

```
Source text  --[reader]-->  Vec<Sexp>  --[ast_builder]-->  Vec<TopLevel> / ReplInput
```

## Architecture

### Entry Points

- `build_program(sexps, expander) -> Result<Program>`: batch mode. Each sexp must be a top-level form.
- `build_repl_input(sexp, expander) -> Result<ReplInput>`: REPL mode. Accepts top-level forms and bare expressions.

Both delegate to shared builders via `build_top_level` and `build_expr`.

### Ring-Gated Form Acceptance

Forms are accepted or rejected based on the current ring. Ring 0 provides the core expression forms (let, if, fn/lambda, match, apply, literals, annotations). Later rings add new forms by replacing rejection arms with production code.

| Ring | Forms added |
|------|------------|
| 0 | `defn`, `deftype` (enum-only at first, full fields/type params in code), `let`, `if`, `fn`/`lambda`, `match`, `apply`, int/float/bool literals, type annotations |
| 1 | `StringLit` (string literals as expressions) |
| 2 | `deftrait`, `impl` |
| 3 | `quote`, `quasiquote`, `unquote`, `unquote-splicing`, `anon-fn`, `vec` |
| 4 | `trace`, `run-tests`, `par-let` |

### Docstring Detection

Docstrings are detected positionally by `extract_optional_docstring(children, start)`. A `Sexp::Str` at position `start` in a top-level form's children is consumed as a docstring. This is unambiguous because:

1. Docstrings can only appear at specific positions in `defn` and `deftype` (after the name, before the parameter list or constructors).
2. String literals in expression position are handled by `build_expr`, which is called for the body -- never for the docstring position.
3. String-valued let bindings like `(let [s "hello"] s)` go through `build_expr` for binding values, not through docstring extraction.

### Type Expression Building

`build_type_expr` translates Sexp forms in annotation position to `TypeExpr`:

- Bare uppercase symbol -> `TypeExpr::Named` (e.g., `Int`, `Bool`)
- Bare lowercase symbol -> `TypeExpr::TypeVar` (e.g., `a`, `b`)
- `self` -> `TypeExpr::SelfType`
- `(Fn [params] ret)` -> `TypeExpr::FnType`
- `(Name args...)` -> `TypeExpr::Applied` (e.g., `(Option Int)`, `(Map String Int)`)

Annotation consumption uses `try_consume_annotation` which handles:
- `:Name` -> simple named type or type var
- `: (compound)` -> compound type via `build_type_expr`

### Qualified impl-target type paths — D-qual-impl-target (S91, Thread B)

**Defect.** A module-qualified type path written in **impl-target position**
(`(impl Num primitives/Int …)`, `(impl Tagger user/Widget …)`) is silently
re-rooted under the current module: the impl registers for a phantom
`user/primitives/Int` (or double-rooted `user/user/Widget`), so trait dispatch
never finds a match — while the **bare** target (`impl Num Int`) works. Spec is
CLEAR: spec/08-modules.md §8.5 — a qualified name is **canonical** (a
fully-qualified path denotes the named member directly and bypasses the
current-module/import machinery); spec/07-traits.md §7.3 EBNF
`concrete_target = type_name` carries **no** impl-target exemption. So a
qualified impl target MUST resolve to the same canonical type the bare target
names — bare and qualified impl targets are interchangeable. The human-written
corpus uses bare targets exclusively, so this latent path was never exercised
until the embedded agent mirrored the REPL's `:primitives/Int` self-display and
wrote the qualified form. Failing-not-ignored repros pin it:
`tests/spec_07_traits.rs::impl_qualified_primitive_type_target_resolves_to_canonical`
+ `…_user_type_…` (commit `cbdafd4`), with `…impl_bare_type_target_dispatches_control`
green today pinning the contrast.

**Root cause (the seam).** `build_impl_target` (`ast_builder.rs`) builds the
target's `TypeRef` with the **whole** name string and a `None` module side:

```rust
// concrete target — line ~946
Sexp::Symbol(name, _) if is_uppercase_start(name) =>
    TypeExpr::Named(TypeRef::new(None, TypeName::from(name.as_str())))   // "primitives/Int" stuffed into the bare-name slot, module=None

// applied/parameterised head — line ~1003
TypeExpr::Applied(TypeRef::new(None, TypeName::from(type_name)), type_args)
```

`TypeName::from("primitives/Int")` keeps the slash verbatim as a single bare
name; with `module: None` the downstream typecheck resolver
(`checker.rs::resolve_type` → `resolve_current_or_prelude`) roots that string
under the current module → `user/primitives/Int`. **The same file already has the
correct splitter** — `type_ref_from_name` (line ~1508, the frontend half of
FIXME 0362) splits at the **last** `/` into `(Some(module), name)` only when both
halves are non-empty, leaving a bare name as `module: None`. It is exactly the
§8.5 canonicalisation rule, and `parse_annotation_name` already routes through it
— which is *why* the bare-type-annotation path (`:primitives/Int x`) works while
the impl-target path does not. The defect is that `build_impl_target` alone hand-
rolls `TypeRef::new(None, …)` instead of calling the shared splitter.

**Proposed fix (frontend-only).** Route both impl-target name-building sites
through `type_ref_from_name` instead of `TypeRef::new(None, TypeName::from(name))`:

- concrete target (`Sexp::Symbol` arm, line ~946): `TypeExpr::Named(type_ref_from_name(name))`
- applied head (`Sexp::List` arm, line ~1003): `TypeExpr::Applied(type_ref_from_name(type_name), type_args)`
- applied **type-arg** position (line ~987, the uppercase-arg leg of the `(Type Arg …)`
  loop): same swap — `TypeExpr::Named(type_ref_from_name(s))`. A qualified type *arg*
  (`(impl Display (Option primitives/Int))`, §7.3.2) is the identical re-rooting
  defect class as the head; fix all three sites in one change so the parameterised-
  impl target is consistent with the concrete one. (Not in the two head-only D-qual
  repros, but the same one-line splitter swap and the same root cause — fix the
  mirror now, not later.)

`is_uppercase_start` already accounts for qualified names (it tests the segment
after the final `/`, line ~126), so the uppercase gate is unaffected. After the
fix, `primitives/Int` arrives at typecheck as `TypeRef { module: Some("primitives"),
name: "Int" }` and `user/Widget` as `{ module: Some("user"), name: "Widget" }`.

**Why this is sufficient downstream (no typecheck change needed).** The impl
registration consumes the target through `impl_target_name_or_panic`
(`traits/type_resolve.rs`), which extracts only the **head `TypeName`** (`r.name`)
and hands it to `resolve_type(state, &name, span)`. Post-fix that head name is the
bare `Int` / `Widget` — the *identical* string the bare control test already
resolves canonically (`Int` via the prelude outer-scope fallback; `Widget` in the
current module). The module qualifier is dropped at head-extraction, which is the
right behaviour: a qualified target resolves *as* its canonical bare name in the
resolver's scope, exactly matching the spec's "qualified == canonical" promise and
the bare control's green path. This is the §8.5 fidelity note to keep in mind: the
frontend canonicalises the *shape* (split the path); the typecheck resolver does
the canonical *lookup* (head name in current-or-prelude scope). No typecheck-side
change is in scope for the two D-qual repros.

**Parallel (not in the two repros, coordinate with /qa's 0434 sweep).** The
trait-name side of the same `build_impl` (`TraitRef::new(None, TraitName::from(
trait_name))`, line ~918) has the identical hand-rolled-no-split shape. A qualified
trait in impl position (`(impl primitives/Num Int …)`) would re-root the trait the
same way. It is outside the two failing D-qual repros (which qualify the *target*),
but it is exactly the kind of name-position the FIXME 0434 coverage sweep
(`/qa`, Thread B) generalises. If `/qa`'s sweep adds a qualified-trait-in-impl
repro, the fix is the symmetric one (route the trait name through a `trait_ref_
from_name` splitter mirroring `type_ref_from_name`). Flagged here so `/dev` lands
both splits together while the context is hot rather than re-discovering the
mirror later (Principle: catch the mirror — `memory/feedback_review_root_cause_
and_duplication.md`).

**`/dev` acceptance (the isolating unit test at the seam).** A
`cranelisp-frontend` `#[cfg(test)]` unit test that parses
`(impl Num primitives/Int (defn + [x y] x))` via `parse` + `build_program`, then
asserts the resulting `TraitImpl.target` is
`TypeExpr::Named(TypeRef { module: Some("primitives"), name: "Int" })` — NOT
`TypeRef { module: None, name: "primitives/Int" }`. Add the `user/Widget` companion
(`module: Some("user"), name: "Widget"`) and a bare-target control
(`module: None, name: "Int"`) so the seam is pinned at the AST boundary
independent of typecheck. This is the mandatory unit test per
root `CLAUDE.md` §Testing; the two e2e repros in `tests/spec_07_traits.rs` are the
end-to-end guard (they flip green when this seam is fixed). Unit + e2e answer
different questions: the unit test pins the `TypeRef` shape at the parse seam; the
e2e proves dispatch actually resolves end-to-end across REPL/`--run`/`--link`.

### `Type.member` dotted field accessors — FIXME 0365 frontend half (S91, Thread C)

**Spec ruling (just edited, spec/08-modules.md §8.5.2 + §5.2.6 + §7.3.1).**
`Type.member` now resolves a **field accessor** of `Type`
(`Box.v` → the `v` accessor of `Box`, typed `(Fn [Box] FieldType)`), alongside
the **constructors** (`Option.Some`) and **trait methods** (`Display.show`) the
dotted form already resolves. This is the same-module escape hatch for
duplicate-field-name accessor ambiguity (§8.6.5): given `(deftype Box [:Int v])`
and `(deftype Cup [:Bool v])` in one module, bare `v` is poisoned, but `Box.v`
and `Cup.v` each resolve directly. Casing makes the rule total: constructors are
uppercase, accessors and methods both lowercase, so the only same-name collision
is accessor-vs-method, and §7.3.1 rejects *that* at impl time — leaving
`Type.member` a unique referent in every case.

**Frontend role: pass-through, already syntactically complete — no code change.**
The frontend does **not** resolve dotted names; it transports them verbatim:

- The reader (`reader.rs::read_dotted_symbol`, line ~792) reads `first.member`
  into a single `Sexp::Symbol("Box.v", span)`. The member may be **symbol chars**
  (`Box.v`, `Option.Some`) or **operator chars** (`Num.+`) — the reader is already
  member-**case-agnostic**: a lowercase field-accessor member (`.v`) is read
  exactly as an uppercase constructor member (`.Some`). No new lexical case.
  (Distinct from a dotted *module path* `core.io/pure`, which the surrounding
  `read_symbol_or_keyword` only continues collecting across dots when a `/`
  follows — §8.5.2 dotted *names* vs §8.5.1 dotted *module paths* are already
  disambiguated by the reader.)
- The AST builder (`ast_builder.rs::build_expr`, `Sexp::Symbol` arm, line ~1089)
  emits `Expr::Var { name: "Box.v", … }` **verbatim** — it does not split, rewrite,
  or special-case the dot. `reject_non_ring0_symbol` (line ~383) gates only
  `%`/`$`/`&`/trailing-`#`; it does **not** touch dotted members, so `Box.v` is not
  rejected.

Therefore the frontend half of 0365 requires **no source change** — the dotted
field-accessor form already parses and flows through as an `Expr::Var` carrying the
full dotted string. The resolution semantics (split the trailing `.`, resolve the
parent type, find the accessor `Def`, type it `(Fn [Type] FieldType)`) live
entirely in typecheck (`checker.rs::lookup` / `infer.rs::infer_var`), which is
`/design (cranelisp-typecheck)`'s deliverable, dispatched separately. The
constructor and trait-method dotted cases resolve the same way — verbatim from the
frontend, split-and-resolved in typecheck — so the accessor case is a typecheck
extension of an existing typecheck mechanism, not a frontend grammar change.

**Why no frontend change is the correct answer (not a deferral).** The §8.5.2
ruling adds a new *referent kind* (field accessor) to an existing *syntactic form*
(`Type.member`). The frontend's contract is syntactic (BC §1: frontend is
syntactic-only); the form was already complete for constructors and methods, and a
field accessor is lexically indistinguishable from a trait method (both lowercase
members). Adding frontend handling would mean the frontend *resolving* names —
crossing the syntactic/semantic boundary it deliberately does not cross
(Principle 17 — module-locality resolution is typecheck's; the frontend never
looks names up). The pass-through is the design, confirmed by the same path
already serving `Option.Some` / `Display.show`.

**`/dev` (cranelisp-frontend) acceptance.** A `cranelisp-frontend` `#[cfg(test)]`
unit test asserting the **transport** invariant: parsing `(Box.v b)` via `parse`
yields a call whose head is `Sexp::Symbol("Box.v", …)` (one symbol, dot retained,
member captured), and `build_program` lowers it to a head `Expr::Var { name:
"Box.v" }` — verbatim, un-split, un-rejected. A companion asserting the operator-
member case (`Num.+`) and the constructor case (`Option.Some`) read identically
documents that the field-accessor case rides the existing member-agnostic path.
This pins that the frontend never silently rewrites a dotted accessor, so a future
refactor cannot regress the transport that typecheck's resolver depends on. The
*resolution* test (`Box.v` / `Cup.v` disambiguating a poisoned field, typed
`(Fn [Box] Int)` / `(Fn [Cup] Bool)`) belongs to `/qa` (e2e) + `/design
(cranelisp-typecheck)`'s seam.

### Stacked param annotations (trait bounds) — FIXME 0341

The param slot is `(Symbol, Option<TypeExpr>)` — **one** optional annotation per
binder. But spec/07-traits.md §7.8.2 and spec/03-types.md §3.9.2 admit a *run* of
annotations on a single binder:

```clojure
(defn f [:Eq :Display a :Eq :Display b] a)   ; a, b each bound by BOTH Eq and Display
```

`build_annotated_params` (the param-list builder) currently consumes exactly one
annotation per `try_consume_annotation` call, then treats the **next** item as the
binder name. So in `:Eq :Display a` the `:Eq` is consumed as the bound and
`:Display` is mis-read as a *separate binder* — yielding two params (`:Display`,
`a`) instead of one (`a`). Two such params collide on the repeated `:Display`
token → `duplicate parameter name ':Display'`.

**Correct shape (the binds-the-following-form rule):** a `:Type`/`:Trait`
annotation is reader-macro-like — it binds the **immediately-following form**
(`memory/annotation-reader-macro-binds-following-form.md`). A *run* of such
annotations therefore all attach to the one binder that terminates the run.
`build_annotated_params` must loop `try_consume_annotation` (accumulating the run)
until it hits a non-annotation item — the binder — rather than consuming exactly
one. The single-bound case `[:Eq a]` is the run-of-length-1 and is unchanged.

**Representation tension.** The param slot holds one `Option<TypeExpr>`; a run of
N>1 bounds has no single-TypeExpr home today. The `(impl Eq (Pair :Eq a :Eq b))`
path solved the analogous problem with a **dedicated** `type_constraints:
Vec<(Symbol, TraitRef)>` field on `TraitImpl` (`build_impl_target`) — that
precedent pairs each `:Trait` with its *own* following var, which is a different
grammar from stacking N traits onto one binder. Carrying N param bounds requires
either a multi-bound TypeExpr variant or a separate per-variant constraints field
— a `cranelisp-types` boundary-shape decision (`/arch`). See the FIXME for the
cross-crate split: the **parse-locus** fix (stop emitting bogus binders) is
frontend; the **N-bound carrier + try-type-then-trait constraint semantics**
(§3.9.3) is a types/typecheck concern.

**Edge cases the builder must honour:** a run with no terminating binder
(`[:Eq]`, trailing `:Eq` before `]`) is the existing "annotation missing
parameter name" error; a single concrete annotation `[:Int x]` is unchanged; a
mixed run `[:Int :Display a]` (a concrete type plus a trait) is admitted
syntactically — disambiguation (§3.9.3 try-type-then-trait) is downstream, not the
parser's job.

### Deftype Desugaring

`desugar_type_def` handles three syntactic forms:

1. **Enum**: `(deftype Color Red Green Blue)` -> one nullary constructor per variant
2. **Product**: `(deftype Point [:Int x :Int y])` -> single constructor with typed fields
3. **Sum**: `(deftype (Option a) None (Some [:a val]))` -> multiple constructors, some with fields
4. **Shortcut**: `(deftype Pair [first second])` -> bare field names get sequential type vars (a, b, c, ...)

### Pattern Building

`build_pattern` produces `Pattern` variants from Sexp in match arms:

- `_` -> `Pattern::Wildcard`
- Uppercase-starting symbol -> `Pattern::Constructor` (nullary)
- Lowercase-starting symbol -> `Pattern::Var`
- `(Constructor bindings...)` -> `Pattern::Constructor` with field bindings

## Ring 1 Changes

### StringLit Acceptance

Ring 1 replaced the `Sexp::Str` rejection in `build_expr` with `Expr::StringLit { value, span }` emission. This was a single-arm change: the match arm for `Sexp::Str` now clones the string value and wraps it in the `StringLit` variant instead of returning an error.

The existing `extract_optional_docstring` needed no changes -- it correctly distinguishes docstrings (positional, in top-level forms) from string-valued expressions (in `build_expr` scope).

### No Structural Changes for ADTs or Closures

The full ADT syntax (type parameters, data constructors with fields, shortcut syntax) and constructor patterns with bindings were implemented structurally in Ring 0, even though the typechecker and backend could not yet handle them. Ring 1 required no frontend changes for these features -- the AST builder already produces the correct nodes. The typechecker and backend are responsible for the new semantics.

## Design Decisions

### Why complete AST in Ring 0?

The frontend builds the full structural AST for all rings, rejecting only expression forms that require later-ring semantics. This means:
- `deftype` with fields and type params: fully desugared in Ring 0
- Constructor patterns with bindings: fully built in Ring 0
- `TypeExpr::Applied`: fully parsed in Ring 0

This avoids structural changes to the AST builder in later rings, keeping it stable. Only expression-level gates (like `Sexp::Str` rejection) change ring-by-ring.

### Macro Expansion via Trait

The `MacroExpander` trait is defined in `cranelisp-types` for dependency inversion. The AST builder consults the expander at call sites, allowing Ring 0 to use `NoOpExpander` while later rings provide real expansion. The expander is checked before treating a list form as a function application.
