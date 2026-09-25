# Expansion-pass qualification is scope-aware

After a cross-module macro expands, int qualifies bare references to the
macro's defining modules so that the consuming module's typecheck can resolve
them. The walk qualifies free references only. It never qualifies a binder,
a local read or quoted data. The paired frontend reject is
`design/frontend/binder-head-reject.md`.

## 1. Context

`process_form/macro_resolution.rs::qualify_expanded_sexp` runs only when a
foreign macro was expanded, that is, when the defining-module list is
non-empty. It rewrites a qualifying bare symbol to `<home>/<name>`.

- **Without scope, it rejects valid programs.** `(defn greet [name] (str "hi"
  name))` would qualify the parameter to `primitives/name`, which the frontend
  rejects as a qualified binder.
- **The ruling.** A binder introduces a name and carries no resolved identity,
  so qualification never applies to it (Principle 24 corollary).

## 2. Design

### 2.1 The rule

Qualify a bare symbol **iff it is a free reference**. A symbol in the current
lexical scope (`shadows`) is either a binder or a local read of one, and is
held verbatim. A free symbol is qualified only when all of these hold:

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

## 3. Evidence

Pure unit cells in `src/process_form/macro_resolution.rs`:

- `qualify_skips_value_binders_and_local_reads`;
- `qualify_skips_let_and_match_binders`;
- `qualify_holds_quoted_datum_verbatim`;
- `qualify_quasiquote_holds_template_but_qualifies_live_unquote`;
- `qualify_quasiquote_nested_unquote_is_not_live`;
- `qualify_holds_defmacro_name_and_params_verbatim`.

`tests/qualified_binder_expansion_0670.rs` carries the end-to-end positives,
where a collision under a macro compiles, and the user-written qualified-binder
negatives.

## 4. Invariant for the frontend

No binder position in this pass's output carries a `/`, so any qualified binder
the frontend sees is user-authored. The frontend's value-level
qualified-binder reject depends on this: were int to emit one, valid programs
would be rejected. `design/arch/bounded-contexts.md` §6 records the invariant.
