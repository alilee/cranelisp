# Expansion-pass qualification is scope-aware

After a cross-module macro expands, int qualifies the bare references the
macro itself wrote against the macro's defining module, so that the consuming
module's typecheck can resolve them. The walk qualifies the macro's free
references only. It never qualifies a binder, a local read, quoted data or the
caller's own text passed through as an argument (§2.7). The paired frontend
reject is `design/frontend/binder-head-reject.md`.

## Open questions

- **For `spec`, not blocking.** Spec §8.6.1 and §9.3.4 together imply that a
  caller's argument keeps the caller's scope, and §2.7 builds on that reading.
  No clause says so outright, and none defines which output symbols count as
  the caller's. §2.7 counts a symbol as the caller's only when the macro
  passed the caller's own symbol through. A name the macro spells from the
  caller's text is the macro's.

## 1. Context

`src/expander/qualify.rs::qualify_expansion` runs once per expansion of a
macro from another module. It runs as that expansion returns, against the
macro's one defining module and before re-expansion
([the binary clean and green](s125-binary-clean.md) §5.2), so it is the one
qualification site for the compiler and `/expand`. It rewrites a qualifying
bare symbol to `<home>/<name>`.

- **Without scope, it rejects valid programs.** `(defn greet [name] (str "hi"
  name))` would qualify the parameter to `primitives/name`, which the frontend
  rejects as a qualified binder.
- **The ruling.** A binder introduces a name and carries no resolved identity,
  so qualification never applies to it (Principle 24 corollary).

## 2. Design

### 2.1 The rule

Qualify a bare symbol **iff it is a free reference the macro wrote**. A symbol
in the current lexical scope (`shadows`) is either a binder or a local read of
one, and is held verbatim. A free symbol is qualified only when all of these
hold:

- it is not caller text (§2.7);
- it is bare, and not an annotation or `_`;
- a defining module's table has it;
- the current module does not already provide it.

### 2.2 Walk shape

`qualify_scoped` mirrors the expander's `expand_scoped` one-to-one, and the
public entry seeds an empty scope.

- **A symbol** is held verbatim if it is in scope. Otherwise it is qualified by
  §2.1.
- **A quoted list** is shielded (§2.4).
- **A `defmacro` head** is shielded (§2.6).
- **A binding-form head** holds its binder slots verbatim, extends the scope
  with the names they introduce, and qualifies its value and body children
  under the extended scope.
- **Any other list or bracket** recurses under the unchanged scope.

### 2.3 Binder enumeration

| Form | Binder slots (verbatim) | Reference slots |
|---|---|---|
| `defn`, `defn-` | the name; each bare non-annotation parameter | the body, under parameters plus the name (§2.5) |
| `fn`, `lambda` | each parameter | the body |
| `let` | each binding name, added to scope sequentially | each value, under the scope so far; the body |
| `match` | each pattern variable (a bare lowercase symbol, or a constructor pattern's argument symbols); `_` and uppercase symbols bind nothing | the scrutinee, in the outer scope; each arm body, under its pattern scope |

**One enumeration (Principle 7).** Both walks call the expander's shared
predicates: `is_binding_form`, `params_scope`, `pattern_binders`,
`is_annotation_symbol` and `is_defmacro_head`. Adding a binding form updates
both walks at once.

Other declaration forms (`deftype`, `deftrait`, `mod`, `platform`, `import`,
`export`) are walked as ordinary children. Their binder rules are enforced
earlier, and they carry no value-level binder that this pass could
mis-qualify.

### 2.4 Quote shield

A symbol inside quoted data is not a reference. Qualifying `'(name)` would
change a runtime value. The walk classifies quote heads through the shared
`cranelisp_types::quote_head`, the classifier the expander and the frontend fold
also use (`int.md` §6.6).

- **`quote`** is held fully verbatim, with no descent.
- **`quasiquote`** is held verbatim except the body of a live `unquote` or
  `unquote-splicing`, which is ordinary expression position and is re-entered
  under the enclosing scope. Nesting depth is tracked exactly as the expander's
  `shield_qq` tracks it, so an unquote under a nested quasiquote is not live.

### 2.5 `defn` self-name

The body scope of `defn` includes the function's own name. A recursive
self-call in a first definition is otherwise mis-qualified to a colliding
defining-module symbol, because the current module does not yet provide the
name. The expander's `defn` scope has the same shape.

### 2.6 `defmacro` shield

A macro-emitted `(defmacro name …)` has the same binder slots as `defn`.
`qualify_scoped` routes a `defmacro`/`defmacro-` head to the `defn` handling:

- the head, the name and each parameter bracket are held verbatim;
- only clause bodies are qualified.

`defmacro` stays out of `is_binding_form`, because that predicate gates the
expander's binding arms.

### 2.7 Caller text is never qualified

**Status: built in S125 Phase 6b; uncommitted.** It repairs
Defect A ([evidence delta §30.2](../../tests/plan/s125-evidence-delta.md#302-the-replay-intake)).

**The defect.** A macro's output mixes two kinds of text:

- the macro's own text, such as the template of `` `(add-i64 ~x 1) ``;
- the caller's arguments that it passes through, such as `x` in
  `(defmacro pass [x] x)`.

Spans do not cross the marshal boundary: each returned node gets a fresh
synthetic span. Without provenance, the walk would see one undifferentiated
tree, and `(pass (add-i64 1 2))` from a caller that never imported `add-i64`
would come back as `(primitives/add-i64 1 2)` and evaluate.
Spec §8.6.1 says a bare name resolves through the current module's scope.
§9.3.4 extends that only to references the expansion introduces, and the
caller's argument is not one.

**The rule.** An output symbol is **caller text** when its name string is the
very runtime string the marshaller allocated for one of the call's argument
symbols. The walk holds caller text verbatim: it stays bare and resolves in the
caller's module, exactly as if the caller had written it outside the macro.
Every other symbol is the macro's text, and §2.1 applies to it unchanged.

- **Identity, not spelling.** A symbol is the caller's only if the macro passed
  the caller's own symbol through. That holds when it returns the argument
  (`x`), splices it (`~x`, `~@body`), or rebuilds the node around the same
  string (`(match x [(SexpSym s) (SexpSym s)])`). A string the macro
  constructs is the macro's, even when its spelling equals an argument's, for
  example the `case` macro's `(SexpSym "let")` (spec §9.8.2) or a name derived
  with `str`. Comparing spellings could not separate `` `(add-i64 ~x 1) ``
  from an argument `(add-i64 1 2)`, so spelling is not used.
- **The identity is held, so it cannot be reused.** For the extent of one
  `invoke_clause`, the host holds one counted reference on each argument
  symbol's string. A held string can be neither freed nor rewritten in place,
  because its count is never one. Its address therefore names it alone, even
  while other threads allocate. Without the held reference, a freed argument
  string's address could be reused by a template string, which would then be
  read as caller text. The cost is one increment and one decrement per
  argument symbol.
- **Where the provenance travels.** The unmarshal walk also assigns the
  synthetic spans. It collects the span of each caller-text symbol, and
  `qualify_expansion` receives that set beside `shadows`. Then the host
  releases the held strings, on every return path of `invoke_clause`.
- **Nested expansion needs no special case.** Re-expansion marshals afresh,
  so an inner macro of the same home module sees the outer macro's output as
  its own arguments. Caller text stays bare through any depth. The outer
  template's symbols are already qualified, or are left bare by §2.1.
- **Unchanged:** the "current module provides it" skip, which keeps spec §9.8's
  capture of template names; binders, the quote shield and the `defmacro`
  shield; `/expand`, which walks the same path; and S125-Q4's visibility
  check, which applies to the qualified references that remain.
- **Ownership.** The held reference is a real reference with a named holder,
  released exactly once, so [macro-turn ownership](macro-turn-ownership.md)
  Rules 1 and 2 admit it (see Rule 2's provenance exception). Strings have no
  children, so it cannot recreate the 0638 asymmetry.

**Grades.**

| Property | Grade |
|---|---|
| Caller text is never qualified | *Structural* while the reference is held: a held string's address names only that string. *Measured* by E1–E3 |
| The macro's own references are still qualified, including one spelled like an argument | *Measured* by E2 and E4, and T-ARG-SCOPE's template control |
| Caller text stays bare through a nested home-module macro | *Measured* by E5 |
| The held references are released exactly once | *Measured* by E6, together with the drop bomb at this seam (macro-turn ownership D3) and `tests/macro_turn_marshal_leak_0889.rs` |
| Compiled code never copies a string when it moves it into a `Sexp` field | *Asserted, with a named falsifier*: E3 fails, because a rebuilt `(SexpSym s)` is read as the macro's text |

**Risk.** A library or the exemplar may rely on the defect, as two replay
demos did (§30.2). They then gain an "undefined variable" error at a name they
never imported. `qa`'s full run, with the stdlib conformance, exemplar and
`user_samples` cells, is the measurement.

## 3. Evidence

Pure unit cells in `src/expander/qualify.rs`:

- `qualify_skips_value_binders_and_local_reads`;
- `qualify_skips_let_and_match_binders`;
- `qualify_holds_quoted_datum_verbatim`;
- `qualify_quasiquote_holds_template_but_qualifies_live_unquote`;
- `qualify_quasiquote_nested_unquote_is_not_live`;
- `qualify_holds_defmacro_name_and_params_verbatim`.

§2.7 is owed these unit cells by `dev`(`src/`), each observed RED where
marked before the change. E1, E2, E4 and E5 expand through a test session
whose home module imports `add-i64` while the caller does not, through
`expand_form_sexp` as the expander's tests do:

- **E1 (RED).** `(pass (add-i64 1 2))` expands to `(add-i64 1 2)`, bare.
- **E2 (RED), the discriminating cell.** `inc`, with template
  `` `(add-i64 ~x 1) ``, applied to `(add-i64 1 2)` expands to
  `(primitives/add-i64 (add-i64 1 2) 1)`. A repair that stops qualifying
  fails its outer head, and today's walk fails its inner one.
- **E3 (RED).** A clause that rebuilds `(SexpSym s)` around an argument's
  string yields a bare symbol.
- **E4.** A clause that constructs `(SexpSym "add-i64")` while the caller's
  argument also spells `add-i64` yields `primitives/add-i64` for the
  constructed one, and leaves the argument bare.
- **E5 (RED).** An outer macro passes its argument to an inner macro of the
  same home module. The argument stays bare, and the inner template's
  reference is qualified.
- **E6.** A marshal unit row: after one turn, each argument symbol string's
  count is back to its value before the turn, on both the success path and
  the invalid-result path.

T-ARG-SCOPE (`tests/spec_09_macros.rs`, by `test`) carries the end-to-end
refusal and its controls.

`tests/qualified_binder_expansion_0670.rs` carries the end-to-end positives,
where a collision under a macro compiles, and the user-written qualified-binder
negatives.

## 4. Invariant for the frontend

No binder position in this pass's output carries a `/`, so any qualified binder
the frontend sees is user-authored. The frontend's value-level
qualified-binder reject depends on this: were int to emit one, valid programs
would be rejected. `design/arch/bounded-contexts.md` §6 records the invariant.
