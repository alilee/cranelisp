# `examples/lib/` — the examples-local library

`training` owns this library and its rules. `examples/Cranelisp.toml`
(`lib-dirs = ["./lib"]`) puts it on every example's library search path. It
is not the standard library. Root `CLAUDE.md` states the
[separation rule](../../CLAUDE.md#design-principles) it serves.

## Purpose

An example should spend its attention on the one construct it teaches. This
library holds the few definitions later examples reach for repeatedly, so an
example imports them in one line. For instance, 19 re-declares `Num`, `Eq` and
`Ord`, and 20 re-declares `Eq`, although 15 already taught them.

## The earning rule

**A definition may enter this library only after the example that teaches its
mechanism.**

- The library is cumulative and follows the sequence. A reader following the
  examples in order has already seen each definition built from primitives and
  special forms.
- Every module names the lesson that earns it in its header. Reading a module
  is a recap, never a prerequisite.

## What stays out

The library shows what the language can do. It is not a small standard library
and must not grow into one. It excludes:

- anything not yet earned by an example, however useful;
- anything justified only because applications need it;
- general-purpose collection, string, formatting or IO vocabulary;
- helpers defined in terms of other library helpers rather than a taught
  mechanism.

The stdlib is learned from the stdlib docs, not from this directory.

## Mechanics

- **`prelude.cl`** loads implicitly for every example and contains no
  definitions. It only re-exports `primitives` names such as `add-i64`, `:Int`
  and `Pure`. Anything implicitly in scope is in scope for `01-integers.cl`,
  so a definition here would break the cumulative rule.
- **Every other module is imported explicitly by name**, for example
  `(import [operators [Num +]])`. The import line tells the reader which
  earlier lesson the example stands on.
- Modules use compiler primitives and special forms only.

## Current contents

| Module | Provides | Earned by |
|---|---|---|
| `prelude.cl` | Re-exports of the `primitives` names examples use; no definitions | — (name surface) |
| `operators.cl` | `Num` (`+ - * /`) and `Ord` (`< > <= >=`) for `Int` and `Float`; `Eq` (`= !=`) for `Int`, `Float`, `Bool` and `String` | `15-traits.cl` |

Candidate modules and their earning lessons are in
[the examples plan](../plan-examples.md#3-the-examples-local-library).
