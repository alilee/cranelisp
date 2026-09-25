# Live development — redefining a running session

The REPL keeps the latest **successful** definition of each name. You can edit a
function while callers are already loaded; the result depends on whether its
language type changes. The complete contract, including the exceptional forms,
is [`repl/spec.md §18`](../../repl/spec/18-redefinition.md).

## Edit a body without changing its type

An unchanged language type updates the function's callable slot. Existing
callers use the replacement body the next time they call it; they are not
recompiled and there is no cascade report.

```
user> (import [primitives [add-i64]])
user> (defn f [x] (add-i64 x 1))
user> (defn g [x] (f x))
user> (g 1)
:primitives/Int 2

user> (defn f [x] (add-i64 x 10))
user> (g 1)
:primitives/Int 11
```

This late binding is the normal live-edit loop: change a body, call the same
entry point again, and see the new result.

## Change a type deliberately

Before publishing a different language type, the REPL checks its direct blocking
dependents, including a definition that stores the function as a value. If any
exists, the redefinition is rejected before publication and the old source,
body, and type remain live. For example,
changing `f` from `Int -> Int` to `String -> Int` while `g` still calls it with
an `Int` reports the old and proposed types and names `user/g` as a blocker;
afterward `(g 1)` still returns `11`.

There is no cascade rebuild, broken-symbol state, runtime trap, or frozen older
world to recover from. Retain the old type or introduce a new name. A
caller-free different-type replacement is allowed. The exact blocker rules and
diagnostic shape are in [`repl/spec.md §18.2`](../../repl/spec/18-redefinition.md#182-blocking-dependents-and-caller-discovery).

For `defn` with multiple arities, the whole overload family is one definition:
add, change, or remove a signature only as a family. For a language-type-changing
replacement, every external direct call or value use of a member is a blocker.
Changing a definition's class or
visibility is rejected; choose a new name or restart with revised source.

## Other definitions

- **Macros:** a replacement affects future expansions only. Code already
  expanded keeps its old expansion until you re-enter that code, reload it, or
  restart the session.
- **Types:** re-establish only a structurally identical type. Documentation and
  labels may change; a structural change is rejected rather than partially
  publishing a new layout.
- **Traits:** re-establish only the same interface. A changed default body
  affects future implementation materializations; re-enter an implementation,
  reload, or restart when existing materialization needs the new body.
- **Implementations:** a re-`impl` replaces the entire `(trait, type)` pair
  atomically. It must stand on its own; an omitted required method or other
  rejected replacement leaves the previous pair dispatching.

## Persistence and failed turns

The REPL saves your definitions to the module's backing file (`user.cl` for the
default entry module) after each successful definition. A rejected redefinition
never replaces the live definition or its saved source, and the REPL continues
with unrelated work after the diagnostic. Reload and restart compile the saved
source as it stands; they do not replay your edit history
([`repl/spec.md §18.8`](../../repl/spec/18-redefinition.md#188-persistence-and-reload)).

### When saved source fails at startup

If the saved source no longer compiles when the REPL starts, the REPL reports
the load error and still reaches a prompt. Until you repair the module:

- expressions are refused;
- definitions are accepted, so you can redefine the broken definition at the
  prompt; and
- the broken definition's source stays in the backing file verbatim — even when
  you successfully define a different name — until a successful definition
  replaces it.

A successful repair clears the block. The requirement is
[`repl/spec.md §15.2.3`](../../repl/spec/15-session-persistence.md#1523-startup-load-failure).

## The `def` macro's current boundary

`def` is a standard-library macro rather than a core special form. Its published
implementation currently uses a zero-argument `name-def` function together with
a zero-argument macro named `name`: bare `name` expands to `(name-def)` each
time, while `(name ...)` with arguments is parsed as a macro call and currently
fails its zero-argument clause. Whether a function obtained through `def` can be
applied directly is not yet decided, so this guide offers no workaround; the open
question is tracked in
[FIXME 0800](../../design/arch/fixmes/0800-def-macro-expansion-leaks-internal-thunk-name-and-blocks-call.md).

## See also

- [`getting-started.md`](../getting-started.md) — opening and using the REPL.
- [`guide/traits.md`](traits.md) — traits, defaults, and implementations.
- [`repl/spec.md §18`](../../repl/spec/18-redefinition.md) — the normative redefinition rules.
