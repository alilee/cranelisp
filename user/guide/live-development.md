# Live development — changing a running session

A running REPL session changes in two ways: you enter a definition at the
prompt, or you save a module file it has loaded. Either way the session keeps
only source that compiles. This page covers both, and moving between modules
with `/mod`.

> **About the transcripts.** They were checked against the real binary with the
> standard prelude loaded. The prompt's timing prefix is elided to `user>`.

## Redefining at the prompt

The REPL keeps the latest **successful** definition of each name. You can edit a
function while callers are already loaded; the result depends on whether its
language type changes. The complete contract, including the exceptional forms,
is [`repl/spec.md §18`](../../repl/spec/18-redefinition.md).

### Edit a body without changing its type

An unchanged language type updates the function's callable slot. Existing
callers use the replacement body the next time they call it; they are not
recompiled and there is no cascade report.

<!-- sample: {"kind":"repl"} -->
```
user> (import [primitives [add-i64]])
user> (defn f [x] (add-i64 x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn
user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn
user> (g 1)
:primitives/Int 2

user> (defn f [x] (add-i64 x 10))
:(Fn [primitives/Int] primitives/Int) user/f ; defn
user> (g 1)
:primitives/Int 11
```

This late binding is the normal live-edit loop: change a body, call the same
entry point again, and see the new result.

### Change a type deliberately

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

### Other definitions

- **Macros:** a replacement affects future expansions only. Code already
  expanded keeps its old expansion until you re-enter that code, reload it, or
  restart the session.
- **Types:** re-establish only a structurally identical type. Documentation and
  labels may change. A structural change, such as adding a field, is rejected
  rather than partially publishing a new layout; keep the structure, use a new
  name, or edit the saved source and restart (see
  [Changing a type's structure](#changing-a-types-structure-needs-a-restart)).
- **Traits:** re-establish only the same interface. A changed default body
  affects future implementation materializations; re-enter an implementation,
  reload, or restart when existing materialization needs the new body.
- **Implementations:** a re-`impl` replaces the entire `(trait, type)` pair
  atomically. It must stand on its own; an omitted required method or other
  rejected replacement leaves the previous pair dispatching.

## Editing module files while the REPL runs

The REPL watches every module file it has loaded. When you save one, the REPL
recompiles it, then every module that depends on it, and reports each file at
the next prompt:

<!-- sample: {"kind":"repl","group":"reload","files":{"math.cl":"(defn sq [x] (* x x))\n(defn cube [x] (* x (* x x)))\n","user.cl":"(import [math [sq]])\n(defn f [] (sq 3))\n"}} -->
```
user> (f)
:primitives/Int 9
user> /sh printf '%s\n' '(defn sq [x] (+ x x))' > math.cl
[updated: math.cl]
[updated: user.cl]
user> (f)
:primitives/Int 6
```

Here `user.cl` imports `sq` from `math.cl` and defines `(defn f [] (sq 3))`.
Initially `math.cl` defines `(defn sq [x] (* x x))` and
`(defn cube [x] (* x (* x x)))`. `/sh` makes the saves explicit; an editor
save triggers the same watcher. A module that uses another only
through a fully-qualified reference, such as `math/sq`, is a dependent too and
is recompiled with it.

A save replaces the module as a whole. The session keeps exactly what the saved
file declares, so a definition or `import` you delete from the file is gone
after the reload:

<!-- sample: {"kind":"repl","group":"reload"} -->
```
user> (math/cube 2)
Error: module error at 1..10: module 'math' has no member 'cube'
```

The rules are [`repl/spec/14-file-watching.md`](../../repl/spec/14-file-watching.md)
§14.1–§14.3.

### When a saved file does not compile

If a saved file does not parse or typecheck, the REPL reports the error instead
of `[updated: …]`, and the **session locks**:

- expressions and definitions in every module are refused until the error is
  fixed — there is no fallback to the previous version;
- the REPL does not overwrite the file, so your saved text stays on disk, and a
  definition that would rewrite it is refused;
- dependents wait until the failed dependency compiles, then rebuild; a
  dependent that fails keeps the session locked.

`{{ROOT}}` below stands for your project directory.

<!-- sample: {"kind":"repl","group":"reload"} -->
```
user> /sh printf '%s\n' '(defn sq [x] (* x "a"))' > math.cl
[errors: math.cl]
  module error in {{ROOT}}/math.cl: at 13..22: module 'math' failed: type error: no impl of trait num.num/Num for type primitives/String
user> (f)
Cannot evaluate: the session is locked while these files have errors:
  math.cl — does not compile; fix it and save a version that compiles
user> /mod math
math> (defn h [] 1)
Cannot evaluate: the session is locked while these files have errors:
  math.cl — does not compile; fix it and save a version that compiles
math> /mod
user> /sh printf '%s\n' '(defn sq [x] (* x 10))' > math.cl
[updated: math.cl]
[updated: user.cl]
user> (f)
:primitives/Int 30
```

A compiling save rebuilds the waiting dependents and releases the lock when
no module remains failed. Restarting the REPL does not get around a failure: the new session
compiles the same saved file and reports the same error. See §14.4–§14.6.

### When the entry file appears or disappears

Starting without an entry file creates an empty live module; it does not write
an empty file immediately. If an entry file appears while that session is
running, the REPL loads it **before a later definition can regenerate the file**.
A file that does not compile locks the session and keeps its bytes on disk;
repair and save it as described above.

Deleting a backing file keeps the module's live definitions. The next successful
definition recreates the file from that live source, without a consent prompt.
Deletion is therefore not a way to clear a running session. For example, in a
fresh default-prelude REPL in an empty directory (these are excerpts):

<!-- sample: {"kind":"repl"} -->
```
user> (defn kept [] 17)
:(Fn [] primitives/Int) user/kept ; defn
user> /sh rm user.cl
user> (kept)
:primitives/Int 17
user> (defn added [] 3)
:(Fn [] primitives/Int) user/added ; defn
```

The recreated `user.cl` contains both `kept` and `added`. To remove a definition,
edit the file's contents and save a compiling module; to start empty, open a
fresh directory. See [REPL §14.9](../../repl/spec/14-file-watching.md#149-backing-file-appearance-and-deletion)
and [§15.1](../../repl/spec/15-session-persistence.md#151-source-regeneration).

### Changing a type's structure needs a restart

A save that changes the structure of a type already live in the session — for
example adding a field to a `deftype` — fails, and the error tells you to
restart:

<!-- sample: {"kind":"repl","files":{"shapes.cl":"(deftype Pt [:Int x :Int y])\n"}} -->
```
user> (import [shapes [Pt]])
user> (Pt 1 2)
:shapes/Pt (Pt 1 2)
user> /sh printf '%s\n' '(deftype Pt [:Int x :Int y :Int z])' > shapes.cl
[errors: shapes.cl]
  module error in {{ROOT}}/shapes.cl: at 0..35: module 'shapes' failed: type error: cannot re-establish type shapes/Pt: its structure differs from the live declaration; keep the live structure, use a new name, or edit the saved source and restart the REPL to establish the changed type
  in expansion of `(deftype Pt [:Int x :Int y :Int z])`
```

Modules that use `Pt` wait for the failed dependency. The session is locked
as above, so your edit is kept. Restart the REPL: the
new session compiles the saved file with no older declaration to conflict with,
and the changed type takes effect. A save that changes only a docstring or a
sum variant's payload labels is not a structural change and reloads normally.
See §14.8.

## Moving between modules — `/mod`

`/mod <name>` makes another existing module the current one: the prompt changes,
and definitions you enter belong to that module and are saved to its file. If the
module has a file that is not loaded yet, `/mod` loads it (and the REPL starts
watching it). Bare `/mod` returns to the entry module.

<!-- sample: {"kind":"repl","files":{"geometry.cl":"(defn area [:Int w :Int h] (* w h))\n"}} -->
```
user> /mod geometry
geometry> (area 2 3)
:primitives/Int 6
geometry> (defn perimeter [w h] (* 2 (+ w h)))
:(Fn [primitives/Int primitives/Int] primitives/Int) geometry/perimeter ; defn
geometry> /mod
user> (geometry/perimeter 2 3)
:primitives/Int 10
```

`/mod` never creates a module. A name that resolves to no module is an error,
and the current module stays the same:

<!-- sample: {"kind":"repl"} -->
```
user> /mod nowhere
Error: Module 'nowhere' not found.
```

The name is resolved exactly as a module name in source is. See
[`repl/spec/03-slash-commands.md` §3.9](../../repl/spec/03-slash-commands.md#39-mod--namespace-switch-and-turn-environment-parity).

## Persistence and failed turns

The REPL saves your definitions to the module's backing file (`user.cl` for the
default entry module) after each successful definition. A rejected redefinition
never replaces the live definition or its saved source, and the REPL continues
with unrelated work after the diagnostic. Reload and restart compile the saved
source as it stands; they do not replay your edit history
([`repl/spec.md §18.8`](../../repl/spec/18-redefinition.md#188-persistence-and-reload)).

### When saved source fails at startup

If saved source fails to compile at startup, the REPL reports the load error
and still reaches a prompt. The session is locked: expressions and definitions
are refused, and the failing file stays on disk as saved. Repair the file and
save a version that compiles. Introspection, `/sh`, `/mod` and `/quit` remain
available. The same rule applies to a failed save during the session; see
[REPL §15.2.3](../../repl/spec/15-session-persistence.md#1523-startup-load-failure)
and [§14.5](../../repl/spec/14-file-watching.md#145-module-state-on-error).

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
