# Binder-Head Rejection

Interior design for the frontend's binder rule. Spec anchor:
`spec/05-definitions.md` §5 intro — **"Declaration heads are binders"**.

A binder introduces a **new** name into the current module or scope. It must be a
**bare** symbol: a qualified (`fmt/foo`) or dotted (`a.b`) spelling in any binder
position is a located compile-time error. This is the exact dual of the §8.5
reference rules — a reference splits `module/Name` and reaches across modules; a
binder stays bare, because the language has no mechanism for declaring a name
into another module, and no notion of a nested path a dotted binder would name.

## 1. Why reject rather than re-root

Re-rooting a qualified binder under the current module is the plausible
alternative, and each of its outcomes is worse than an error:

- `(defn fmt/foo [x] x)` would bind `user/fmt/foo`: the REPL echoes success <!-- doc-check: literal reason="Illustrative language symbols" -->
  while `--run` fails later at the reference site with an incidental "module
  `fmt` not found" — a **mode-divergent** face.
- `(deftrait fmt/Foo …)` would bind when a module `fmt` exists and fail at a
  degenerate `0..0` span when it does not.
- `(deftype A.B [:Int v])` would declare type `user/A.B` and mint constructor <!-- doc-check: literal reason="Illustrative language symbols" -->
  `user/B`, because the dotted head is re-read downstream as a `Type.Ctor` <!-- doc-check: literal reason="Illustrative language symbols" -->
  member spelling — **constructor identity corruption**, the outcome the rule
  most needs to make unreachable.

The reject turns each into one located parse-time diagnostic that names the fix.

## 2. The seam — one shared reject

`reject_qualified_binder_head(name, span)` sits beside `reject_reserved_binder_name`
and is applied at every binder position. The two are siblings: one gates reserved
names, one gates qualified and dotted spellings, and both are single-sourced so
every site enforces the identical rule (Principle 7; Principle 18 — enforce where
binder-ness is decided). There are **no per-form copies**. Bringing a new binder
position under the rule is a routing onto the helper; adding a predicate at the
site would be a mirror.

**Predicate.** A name is qualified iff splitting at the last `/` yields two
non-empty halves; dotted iff splitting at the last `.` does — the same guard the
reference splitters use.

> **The both-halves-non-empty condition is load-bearing** (Principle 16). A
> coarse `name.contains('/')` rejects the division operator: `Num` declares a
> method **named `/`** (`(deftrait Num … (/ [a b] self))`), so the whole prelude
> would fail to compile. `/`, `foo/` and `/bar` all split to an empty half and
> are therefore **not** qualified — exactly as the reader keeps a bare `/` a bare
> operator name. The same reasoning covers a lone, leading or trailing `.`.

### 2.1 Diagnostic shape

One `parse_err` at the span of the offending name, rendering the form via
`Sexp::format_flat` and never `{:?}`, naming the bare name the user most likely
meant to bind.

The message is **position-neutral**: *"a binder must be a bare (unqualified)
name"*, with no "definition head" noun, so the one shared string reads correctly
at a `let`, `match` or parameter position as well as at a declaration head. Do
not thread a position noun through the call sites.

### 2.2 The `.` (dotted) axis

`.` is reserved for type and trait qualification. **Reference** positions stay
legal — the dotted constructor-pattern head `(Maybe.Some x)`, dotted var, call
and type references — and the line is drawn at binder versus reference, identical
to the `/` rule. Three structural constraints hold it:

1. **`split_qualified_name` stays `/`-only. Do not widen it.** It is the
   *reference* splitter that `type_ref_from_name` and `trait_ref_from_name`
   delegate to; widening it to `.` would corrupt legitimate dotted references
   such as `Maybe.Some` and `core.io/pure`.
2. **One sibling dotted splitter, `split_dotted_name`,** with the same
   both-halves-non-empty discipline, consumed *only* inside the reject helper.
   There is no second `.`-checking predicate anywhere — no scattered
   `name.contains('.')`, no per-position dotted gate.
3. **The helper fires on either split**, checking `/` first so a `module/…`
   binder reports the qualifier fault.

Every binder position inherits the `.` reject, because the reader delivers `a.b`
as a single `Sexp::Symbol` and every position threads that symbol through the one
helper. A site's case check is no substitute: `is_uppercase_start` inspects only
the segment after the separator, so it cannot tell a dotted spelling from a bare
one. `build_type_head` rejects at the head
span before constructor synthesis runs, so the corrupted constructor of §1 never
forms.

## 3. Binder-position coverage against spec §5

| Spec §5 binder case | Covered by |
|---|---|
| `defn`/`defn-` head, and impl-body method-defn head | `get_defn_name` — one shared caller |
| `deftype`/`deftype-` head | `build_type_head`, both arms |
| `deftrait`/`deftrait-` head | `build_trait_head`, both arms |
| `defmacro`/`defmacro-` head | `parse_defmacro` name |
| deftrait method-signature name (§5.3.3) | `build_method_sig` |
| `def`/`const` head (macro route) | post-expansion, with the §4 int re-anchoring for the span |
| con_var (§5.3.2) | `parse_trait_head_shape` con_var arm |
| deftype variant-constructor name (§5.2.2) | `build_constructor_def`, both arms |
| deftype field names (§5.2.6) | `build_field_list`, both arms |
| deftype type parameters (§5.2) | `build_type_head` parameter map |
| value-level locals (params, `let`, `match`) | `build_annotated_params` (covering `defn`, `fn` and `defmacro` parameters), `build_let_bindings`, `build_pattern` var and constructor-binding arms |
| `mod`/`mod-` name (§5.8) | **not this seam** — a module-phase declaration. `module_extract` enforces its own simple-symbol rule, rejecting `/` and `.` because either would corrupt the composed module path |
| `platform` name (§5.10) | **not this seam** — same module-phase rule as `mod` |

Every row is covered on **both** the `/` and `.` axes by the same helper. In a
constructor pattern, `children[0]` is a **reference** and is not a reject site;
the binding symbols are.

The value-level rows rely on int's expansion pass skipping binder slots
(`design/int/expansion-qualification-scope.md`): a bare local binder that
collides with an imported name reaches the builder unqualified, so the reject
fires only on a qualified spelling the user wrote.

Two placement judgments are load-bearing:

- **The trait-name reject lives in `build_trait_head`, not in the shared shape
  parser.** `parse_trait_head_shape` serves both `deftrait` and `impl` slot 1,
  and `impl` slot 1 is a trait *reference*, where a qualified spelling is legal.
  The shared parser stays shape-only; the binder policy is the deftrait caller's
  (`trait-impl-head-parse.md` §3).
- **The con_var reject does live in the shared shape parser,** because a con_var
  is a binder in both `deftrait` and the echoed `impl` head.

## 4. Span provenance across macro expansion

For a macro-route binder — `def`, `const`, or any user macro whose expansion
emits a qualified head — the rejection fires on the **expanded** form, but the
diagnostic must point at the **user's written form**.

**The frontend seam cannot satisfy that alone.** Int's macro pipeline gives macro
output fresh unique synthetic spans. The reject still fires, but its location is
a synthetic offset, and for `def` (which mangles an inner name) the
first-processed head is the synthesised one.

Two alternatives are rejected:

- **Preserving source spans through the marshal boundary** collides with the
  span-**uniqueness** invariant. The span-keyed carriers require every node in an
  expanded body to have a unique span; a node cannot carry both a source-anchored
  span for diagnostics and a unique synthetic span for carriers in one field.
- **A pre-expansion special case for `def`/`const`** would be a second
  binder-reject seam that knows specific stdlib macro names, privileging a module
  by name (Principle 19) and re-opening the per-form drift the shared helper
  closes.

The adopted shape is a **paired int-side re-anchoring**: when int drives the
builders over macro-expansion output and gets back a `ParseError` at a synthetic
location, it relocates that error to the origin form's span, which it already
holds. Span uniqueness stays intact and the diagnostic gets a real location.
`design/int/macro-diagnostic-reanchoring.md` owns that half. A directly written
head is never marshalled and carries its real reader span.

## 5. The annotation path is a sibling seam

A qualified-lowercase annotation (`:user/int`) is the same *family* — a
qualified-name lexical-class decision — but a different seam, and conflating the
two produces the wrong fix. An annotation is a **reference** position, where a
qualifier is meaningful, so the answer is correct routing, not rejection.

`build_type_expr` is the one place type-variable-ness is decided. Its uppercase
test inspects only the segment after the last `/`, so without routing a
lowercase qualified name would become a `TypeVar` carrying a `/` — and a type
variable is a bare lowercase identifier that must never carry one. A symbol
containing `/` therefore routes to `Named` through the reference splitter, which
makes the eventual unknown-type error name the module. Typecheck's own guard
against a slash-carrying type variable is a downstream fence, not the decision
point.

## 6. Testability

Every site is a pure `&Sexp`/`&str` function, unit-testable with no session.
Three classes of assertion, each discriminating something a weaker test would
miss:

- per site, a qualified head → located error with the span on the head and the
  bare fix named, **plus** a bare-head positive twin that still parses;
- the shared-seam property — a qualified head rejects identically whether reached
  through `parse_defn` or `build_impl_method`, which proves no impl-method copy
  grew;
- the division fence — `(deftrait Num … (/ [a b] self))` still parses, and
  `(/ 6 2)` still evaluates. This is the acid test that the predicate has not
  over-reached.

The macro-route span provenance (§4) is an e2e question, and it is the durable
proof of the int seam's obligation.

## Cross-references

- `spec/05-definitions.md` §5 — the binder principle and the per-site notes.
- `spec/08-modules.md` §8.5 — the reference rules this is the dual of.
- `design/frontend/trait-impl-head-parse.md` §3 — the shared-shape-parser versus caller-name-policy split.
- `design/frontend/enforcement-matrices.md` §3 — the reader's dangling-qualifier rejects, a different family.
- `design/int/macro-diagnostic-reanchoring.md` — the paired int seam (§4).
- `design/int/expansion-qualification-scope.md` — int's expansion pass skipping binder slots.
