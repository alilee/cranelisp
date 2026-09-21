# Binder-Head Rejection

Interior design for the frontend's binder rule. Spec anchor:
`spec/05-definitions.md` §5 intro — **"Declaration heads are binders"**.

A binder introduces a **new** name into the current module or scope. It must be a
**bare** symbol: a qualified (`fmt/foo`) or dotted (`a.b`) spelling in any binder
position is a located compile-time error. This is the exact dual of the §8.5
reference rules — a reference splits `module/Name` and reaches across modules; a
binder stays bare, because the language has no mechanism for declaring a name
into another module, and no notion of a nested path a dotted binder would name.

## 1. What the rule prevents

Before the reject, every head-parse site accepted a qualified head and re-rooted
it under the current module. The resulting faces were worse than an error in
three distinct ways, and the variety is the point — none of them was a clean
failure:

- `(defn fmt/foo [x] x)` **silently bound** `user/fmt/foo` and echoed success at
  the REPL, while under `--run` the failure deferred to the reference site as an
  incidental "module `fmt` not found" — a **mode-divergent** face.
- `(deftrait fmt/Foo …)` silently bound with a matching module present, and died
  at a degenerate `0..0` span without one.
- `(deftype A.B [:Int v])` accepted, echoed type `user/A.B`, and minted
  constructor `user/B` — the dotted head is re-read downstream as a `Type.Ctor`
  member spelling, so the **constructor identity was corrupted**. This is the
  sharpest face and the one the rule most needs to make unreachable.

Each becomes a single located parse-time diagnostic that names the fix.

## 2. The seam — one shared reject

`reject_qualified_binder_head(name, span)` sits beside `reject_reserved_binder_name`
and is applied at every binder position. The two are siblings: one gates reserved
names, one gates qualified and dotted spellings, and both are single-sourced so
every site enforces the identical rule (Principle 7, Principle 18 — enforce where
binder-ness is decided). There are **no per-form copies**.

**Predicate.** A name is qualified iff splitting at the last `/` yields two
non-empty halves; dotted iff splitting at the last `.` does. Both use
`rsplit_once` with a both-halves-non-empty filter, the same guard the reference
splitters use.

> **The both-halves-non-empty condition is load-bearing** (Principle 16). A naive
> `name.contains('/')` was falsified in implementation: `Num` declares a method
> **named `/`** (`(deftrait Num … (/ [a b] self))`), and `"/".contains('/')` is
> true, so the coarse predicate rejected the division operator and the whole
> prelude failed to compile. `/`, `foo/` and `/bar` all split to an empty half
> and are therefore **not** qualified — exactly as the reader keeps a bare `/` a
> bare operator name. The same reasoning covers a lone, leading or trailing `.`.

### 2.1 Diagnostic shape

One `parse_err` at the span of the offending name, rendering the form via
`Sexp::format_flat` and never `{:?}`, naming the bare name the user most likely
meant to bind.

The message is **position-neutral**: *"a binder must be a bare (unqualified)
name"*, with no "definition head" noun. That wording reads correctly at a `let`,
`match` or parameter position as well as at a declaration head — telling someone
who wrote `(let [user/x 1] …)` about a "definition head" describes something they
did not type. One shared string keeps it correct everywhere without threading a
position noun through every call site.

### 2.2 The `.` (dotted) axis

`.` is reserved for type and trait qualification. **Reference** positions stay
legal — the dotted constructor-pattern head `(Maybe.Some x)`, dotted var, call
and type references — and the line is drawn at binder versus reference, identical
to the `/` rule.

The dotted axis is enforced by widening the **one** helper, under three
structural constraints:

1. **`split_qualified_name` stays `/`-only. Do not widen it.** It is the
   *reference* splitter that `type_ref_from_name` and `trait_ref_from_name`
   delegate to. Widening it to `.` would corrupt legitimate dotted references —
   `Maybe.Some`, `core.io/pure`. The `.` axis is a binder-reject concern only, so
   it lives in the reject helper and never in the shared splitter.
2. **One sibling dotted splitter, `split_dotted_name`, delegated to.** It applies
   the same both-halves-non-empty discipline and is consumed *only* inside the
   reject helper. There must be no second `.`-checking predicate anywhere — no
   scattered `name.contains('.')`, no per-position dotted gate.
3. **The helper fires on either split**, checking `/` first so a `module/…`
   binder reports the qualifier fault.

Every binder position inherits the `.` reject for free, because the reader
delivers `a.b` as a single `Sexp::Symbol` and every position already threads that
symbol through the one helper. The `deftype A.B` identity corruption is closed at
the root: `build_type_head` rejects at the head span before any constructor
synthesis runs, so the incoherent constructor never forms.

The `mod` and `platform` module-phase guards are **not** this seam and not a
mirror of it — they are a different phase with a different rule (§8).

## 3. The binder sites

Every declaration head, every secondary binder, and every value-level local
routes through the one helper:

| Family | Sites |
|---|---|
| Declaration heads | `get_defn_name` (covering `defn`/`defn-` **and** impl-body method defns through one shared caller), `build_type_head` (both arms), `build_trait_head` (both arms), `parse_defmacro` name, `build_method_sig` name |
| Secondary binders | `deftype` constructor names (both arms), field names (both arms), `deftype` type parameters, `deftrait` con_var |
| Value-level locals | `build_annotated_params` (covering `defn`, `fn` and `defmacro` parameters), `build_let_bindings`, `build_pattern` var and constructor-binding arms |

Two placement judgments are load-bearing:

- **The trait-name reject lives in `build_trait_head`, not in the shared shape
  parser.** `parse_trait_head_shape` serves both `deftrait` and `impl` slot 1,
  and `impl` slot 1 is a trait *reference*, where a qualified spelling is legal.
  The shared parser stays shape-only; the binder policy is the deftrait caller's,
  exactly as its name resolution already is (`trait-impl-head-parse.md` §3).
- **The con_var reject does live in the shared shape parser,** because a con_var
  is a binder in both `deftrait` and the echoed `impl` head.

In a constructor pattern, `children[0]` is a **reference** and is not a reject
site; the binding symbols are.

The type-parameter site is the one that needed a call *added* rather than
inherited — every other position already routed through the helper. That is the
distinction worth preserving: adding a routing is single-sourcing, adding a
predicate is a mirror.

## 4. Span provenance across macro expansion

For a macro-route binder — `def`, `const`, or any user macro whose expansion
emits a qualified head — the rejection fires on the **expanded** form, but the
diagnostic must point at the **user's written form**.

**The frontend seam cannot satisfy that alone.** Int's macro pipeline discards
source provenance from macro output: marshalled results carry synthetic spans,
and span rewriting assigns a fresh unique synthetic span to every node. The
reject still fires — correctness is preserved — but the location degrades to a
synthetic offset, and for `def` (which mangles an inner name) the first-processed
head is the synthesised one.

Two fixes were rejected before the current one:

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
holds. Span uniqueness stays intact and the diagnostic gets a real location. The
frontend states its half; `design/int/macro-diagnostic-reanchoring.md` owns the
other. Native forms are unaffected — a directly-written head is never marshalled
and carries its real reader span.

The frontend reject is inert-safe without the int seam, which is why the two
could land in either order.

## 5. The annotation path is a sibling seam

A qualified-lowercase annotation (`:user/int`) is the same *family* — a
qualified-name lexical-class decision — but a different seam, and conflating the
two produces the wrong fix. An annotation is a **reference** position, where a
qualifier is meaningful, so the answer is correct routing, not rejection.

`parse_annotation_name` decides type-variable-ness. Because the uppercase test
inspects only the segment after the last `/`, a lowercase qualified name would
route to a `TypeVar` carrying a `/` — and a type variable is a bare lowercase
identifier that must never carry one. So a lowercase name containing `/` routes
to `Named` through the reference splitter instead, which makes the eventual
unknown-type error name the module. The decision is made where
type-variable-ness is decided; the typecheck-side mint guard remains as the
structural fence behind it.

## 6. Testability

Every site is a pure `&Sexp`/`&str` function, unit-testable with no session.
Three classes of assertion, each discriminating something a weaker test would
miss:

- per site, a qualified head → located error with the span on the head and the
  bare fix named, **plus** a bare-head positive twin that still parses;
- the shared-seam property — a qualified head rejects identically whether reached
  through `parse_defn` or `build_impl_method`, which is the instrument that
  proves no impl-method copy grew;
- the division fence — `(deftrait Num … (/ [a b] self))` still parses, and
  `(/ 6 2)` still evaluates. This is the acid test that the predicate has not
  over-reached.

The macro-route span provenance (§4) is an e2e question, and it is the durable
proof of the int seam's obligation.

## 7. Principles

- **Principle 7** — one reject at every site; the `.` axis widens that one helper
  plus one delegated-to splitter, never a per-position checker.
- **Principle 18** — the reject fires where binder-ness is decided, not as a
  downstream backstop; §5's routing likewise.
- **Principle 16** — the predicate keys on `/` or `.` under a both-halves-non-empty
  guard, so a bare `/` and a degenerate `.` are not binder rejects.
- **Principle 19** — the macro-route span fix is not a `def`/`const` special case.

## 8. Binder-position coverage against spec §5

| Spec §5 binder case | Covered by |
|---|---|
| `defn`/`defn-` head | `get_defn_name` |
| impl-body method-defn head | `get_defn_name` (same seam) |
| `deftype`/`deftype-` head | `build_type_head`, both arms |
| `deftrait`/`deftrait-` head | `build_trait_head`, both arms |
| `defmacro`/`defmacro-` head | `parse_defmacro` name |
| deftrait method-signature name (§5.3.3) | `build_method_sig` |
| `def`/`const` head (macro route) | post-expansion, with the §4 int re-anchoring for the span |
| con_var (§5.3.2) | `parse_trait_head_shape` con_var arm |
| deftype variant-constructor name (§5.2.2) | `build_constructor_def`, both arms |
| deftype field names (§5.2.6) | `build_field_list`, both arms |
| deftype type parameters (§5.2) | `build_type_head` parameter map |
| value-level locals (params, `let`, `match`) | `build_annotated_params`, `build_let_bindings`, `build_pattern` |
| `mod`/`mod-` name (§5.8) | **not this seam** — a module-phase declaration, not a §5 declaration head. `module_extract` enforces its own simple-symbol rule, rejecting `/` and `.` because either would corrupt the composed module path |
| `platform` name (§5.10) | **not this seam** — same module-phase rule as `mod` |

Every row is covered on **both** the `/` and `.` axes by the same helper; the
widening is orthogonal to the site enumeration, so it adds no row. The two
excluded rows are excluded for a stated reason, not by omission.

## Cross-references

- `spec/05-definitions.md` §5 — the binder principle and the per-site notes.
- `spec/08-modules.md` §8.5 — the reference rules this is the dual of.
- `design/frontend/trait-impl-head-parse.md` §3 — the shared-shape-parser versus caller-name-policy split.
- `design/frontend/enforcement-matrices.md` §3 — the reader's dangling-qualifier rejects, a different family.
- `design/int/macro-diagnostic-reanchoring.md` — the paired int seam (§4).
- `design/int/expansion-qualification-scope.md` — int's expansion pass skipping binder slots, the precondition for the value-level rejects.
