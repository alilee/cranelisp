# `examples/lib/` — the examples-local library

This directory is on the library search path for every example
(`examples/Cranelisp.toml`, `lib-dirs = ["./lib"]`). It is **not** the
standard library, and it is not a dependency in the ordinary sense.

## What it is for

Examples teach the **core language**. Each one should be able to spend its
attention on the single construct it is about. Without a shared library,
every example that wants to write `+` has to declare a `Num` trait first —
which is why `15-traits.cl`, `19-threading.cl` and `20-adt-traits.cl` each
declare one, three times over, in files that are not about traits.

This library exists to stop that. It holds the small number of definitions
that examples reach for repeatedly, so an example can import them in one
line and get on with its own subject.

## The rule that governs its contents

> **A definition may enter this library only after the example that teaches
> its mechanism.**

The library is **cumulative and pedagogically ordered**. It is a teaching
artifact whose shape is a function of the sequence: nothing appears here
that a reader following the examples in order has not already been shown
being built, from primitives and special forms, in front of them.

Every module states the lesson that earns it in its header. Reading a
library module should never be a prerequisite — it should be a recap.

## What deliberately stays out

This library is **suggestive of what the language can do, not complete.**
It is not a small standard library and it must not grow into one. It
deliberately excludes:

- anything not yet earned by an example, however useful;
- anything whose only justification is that applications need it — this
  sequence does not teach how to write applications;
- general-purpose collection, string, formatting, or IO vocabulary;
- convenience layered on convenience: a helper defined in terms of other
  library helpers rather than in terms of a taught mechanism.

**To learn the standard library, read the stdlib docs.** `examples/` is not
a tour of the library surface, and the vocabulary here is not the
vocabulary a production program would use. The two are different documents
with different jobs.

## Mechanics

- **`prelude.cl`** is loaded implicitly for every example. It contains
  **no definitions at all** — only re-exports of `primitives` names, so
  that `add-i64`, `:Int`, `Pure` and friends resolve without a per-file
  import. It is a name surface, not teaching material, and it stays that
  way: anything implicitly in scope is in scope for `01-integers.cl` too,
  which would break the cumulative rule.
- **Every other module is imported explicitly**, by name, e.g.
  `(import [operators [Num +]])`. The import line is deliberate: it is the
  reader's cue that this example is standing on an earlier lesson, and it
  names which one.
- Everything here is built from **compiler primitives and special forms
  only**. There is zero dependency on `stdlib/`, so the examples still
  validate the language independently of any particular library code
  (root `CLAUDE.md` §"Stdlib separation").

## Current contents

| Module | Provides | Earned by |
|---|---|---|
| `prelude.cl` | re-export of the `primitives` names examples use (no definitions) | — (name surface) |
| `operators.cl` | `Num` (`+ - * /`), `Eq` (`= !=`), `Ord` (`< > <= >=`) with `Int`/`Float`/`Bool`/`String` impls | `15-traits.cl` |

The build-out is sequenced in `examples/plan-examples.md` §2d.
