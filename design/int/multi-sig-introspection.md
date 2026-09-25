# Multi-signature introspection

How the REPL displays an overloaded (multi-signature) function. The normative
format is `repl/spec/04-self-documentation.md` §4.1.1, with the display rules in
`repl/spec/01-display-format.md` §1.3 and `/sig` in
`repl/spec/03-slash-commands.md` §3.8.

## 1. Rule

An overloaded binding displays one line per arm:
`:<arm type> module/name`. Only the first line carries the `; defn`
classification and the docstring. Each arm's type is that arm's own signature,
including any trait bound it inferred (§4.1.1).

## 2. Design

### 2.1 One builder

`format_definition_symbol_doc` builds the display for every introspection
surface: bare lookup, `/sig` and `/info`. It looks the binding up by its
canonical key and shows the bare member name. For `Decl::Overloaded`,
`format_def_entry_doc` calls `format_type.rs::format_overloaded_variants_doc`
with the declaration's arms and docstring.

### 2.2 Line format

- Each arm renders as the type annotation followed by the fully qualified
  name.
- The first line appends the classification metadata.
- Lines are joined with newlines.

### 2.3 Order

Arms appear in declaration order; nothing sorts them.

### 2.4 Constraints

Each arm renders its own authoritative scheme through
`display::format_scheme_type`. A bound the arm inferred is therefore shown
inline, exactly as for a single-signature constrained function. There is no
lookup of a generated child and no constraint-dropping fallback.

A multi-signature `defn` is inference-equivalent to its clauses written as
separate functions (`spec/05-definitions.md` §5.1.2). A variant shown without
its bound is a `repl/spec/04-self-documentation.md` §4.1.1 non-conformance,
even when the bound is enforced.

### 2.5 `/sig`

`/sig` resolves candidates the same way as bare lookup and uses the same
builder, so its lines are identical by construction.

## 3. Evidence

- `tests/repl_introspection.rs::display_overloaded_fn_shows_all_variants`
  covers one line per variant.
- `tests/multi_sig_variant_display_constraint_drop.rs` covers the inferred
  bound:
  - `multi_sig_variant_display_carries_inferred_num_constraint` shows it
    inline;
  - `multi_sig_variant_bound_still_enforced_neg` shows it is still enforced.
- `src/repl/format_type.rs` unit tests cover:
  - one line per variant;
  - the docstring on the first line only;
  - a single variant;
  - the constrained template scheme.
- `/info` reaches the same builder, but no test pins `/info` on an overloaded
  function (`repl/spec/03-slash-commands.md` §3.6).
