# IO typing

How `cranelisp-typecheck` types `IO`, as built. Owned by `design` (typecheck).

## Overview

`IO` is typed as an ordinary algebraic data type,
`Type::ADT(primitives/IO, [a])`, with no dedicated `Type` variant. Effect tracking is
standard Hindley-Milner unification: no special inference rule, annotation or flag.
This crate owns the typing; the `IO` type and `bind` are seeded by `int`'s bootstrap,
`main` is validated by `int`, and the representation is evaluated by the runtime.

**The language position differs from the representation.** `spec/10-io.md` §10.1
(user ruling, 2026-11-22) makes `IO` an opaque built-in type: the language has
`(IO a)` and no constructors for it, user code may neither construct nor match an `IO`
value, and `primitives/pure` is the public way to lift a value. The as-built
representation still exposes the `Pure` and `Effect` constructors to user code, and
`pure` is a standard-library definition over `Pure`. That nonconformance is carried to
the next sprint as compiler work, with failing cells in `tests/spec_10_io.rs`
(ACT-1105, ACT-1106, ACT-1107; ACT-1108 for `pure`). This document describes the code
as built and is not a design for the opaque type.

**Considered: a `Type::IO` variant.** Rejected: it would add a branch to every `match`
on `Type` across all crates, while the ADT form already carries the one type argument
that inference needs. Opacity is a question of which constructors user code can name,
not of the type's representation.

## 1. Internal constructors

A constructor's `internal` flag lives on its callable origin,
`CallableOrigin::Ctor { internal, .. }` (`AdtCtorSpec::internal` when an ADT is built).
Only `Bind` is internal. Typecheck reads the flag at three points:

- **Construction.** `crates/cranelisp-typecheck/src/infer.rs::infer_var` rejects a reference to an internal
  constructor: "cannot construct internal type constructor".
- **Pattern matching.** `crates/cranelisp-typecheck/src/infer.rs::check_constructor_pattern` rejects it: "cannot
  match on internal type constructor".
- **Exhaustiveness.** `crates/cranelisp-typecheck/src/adt.rs::check_exhaustiveness_in_module` excludes internal
  constructors, so user code cannot and need not cover them.

The gate is `crates/cranelisp-typecheck/src/checker.rs::is_internal_constructor`. It follows import and prelude
exposure to the constructor's terminal entry before reading the flag, so a bare `Bind`
exposed into a user module is still refused.

## 2. The `IO` type as seeded

`src/bootstrap.rs::register_io_type` installs `IO` in the `primitives` module through
the standard ADT path, with docstring "Deferred IO computation tree" and one parameter
`a`:

| Constructor | Tag | Field | Scheme | Internal |
|---|---|---|---|---|
| `Pure` | 0 | `ioval : a` | `∀a. (Fn [a] (IO a))` | no |
| `Effect` | 1 | `thunk : a` | `∀a. (Fn [a] (IO a))` | no |
| `Bind` | 2 | `inner`, `cont` (§3) | §3 | yes |

Each sum constructor is keyed `IO.<Name>` (`member_key`), with the bare name a
candidate exposure onto it. `crates/cranelisp-typecheck/src/builtins.rs::register_io_type`
is this crate's test fixture (`FixtureContent::Io`) and mirrors the bootstrap shape;
it is not the production seed.

**Why `Effect`'s `thunk` is typed `a`.** At runtime the field is a host closure, but
the type system records what the effect produces when forced, which is what inference
needs. Platform operations build `Effect` nodes, and the trampoline alone reads the
field.

## 3. The `Bind` constructor

`Bind` has an existential type that HM cannot express:

```
Bind :: ∃b. (IO b, (Fn [b] (IO a))) -> (IO a)
```

The bootstrap therefore builds its scheme by hand with two fresh variables,
`∀a b. (Fn [(IO b) (Fn [b] (IO a))] (IO a))`, appends `Bind` to `IO`'s constructor
list and installs it as an internal, parametric synthesised template. It is listed by
introspection and refused to user code by §1.

## 4. The `bind` primitive

```
bind :: ∀a b. (Fn [(IO a) (Fn [a] (IO b))] (IO b))
```

`src/bootstrap.rs::register_bind_primitive` installs `bind` in `primitives` as a
slot-less host-promised primitive; the backend lowers a call to it inline, allocating a
`Bind` node. It has no special inference rule: application unifies the first argument
with `(IO a)` and the continuation with `(Fn [a] (IO b))`, so the continuation receives
the inner computation's value by ordinary unification.

## 5. `pure`

As built, `pure` is the standard-library definition
`(defn pure "Lift a value into IO" [x] (Pure x))` (`stdlib/io/monad.cl`), and this
crate infers `∀a. (Fn [a] (IO a))` for it by constructor application. The
specification's `primitives/pure` does not exist yet (ACT-1108). Either way `pure`
needs no typechecker rule.

## 6. `main` validation

Typecheck does not designate or validate `main`. `int` does, in
`src/exe.rs::validate_main`: a batch `main` takes no parameters and returns `IO _`
(spec §10.6). Typecheck's contribution is `CheckResult::unresolved_dispatch`, which
`int` applies at that entry. A REPL turn has no `main`.

## 7. Interaction with the rest of the type system

`IO` needs no special rule. Each case below is ordinary inference:

- **Propagation.** A function whose body returns a platform operation's `(IO Int)`
  is inferred to return `(IO Int)`.
- **Conditionals.** Both branches of an `if` unify, so `(IO Int)` against `Int` is a
  type error (spec §10.7.2).
- **Bindings and data.** An `IO` value can be bound, nested (`(IO (IO Int))`) or stored
  in a data structure (`(Option (IO Int))`) by ordinary type-parameter instantiation;
  binding it performs nothing.
- **Higher-order functions.** A closure returning `IO` has a function type with an
  `IO` return.
- **Traits.** `IO` is not a trait. A constraint such as `Display a` in
  `(Fn [a] (IO Int))` comes from the body's other calls.

## 8. Platform operations

A platform operation's type comes from its manifest. `int` requires its return type to
be `IO _` (`src/platform.rs::require_io_return`, spec §8.9.3); typecheck applies no
platform-specific rule.

## 9. Rejected alternatives

- **`bind` as a called function rather than inline.** It would add call overhead to
  every chain step, and inline lowering lets the backend manage the reference counts
  at the call site.
- **`Effect` as internal.** Not adopted in the representation, since platform
  operations construct it outside user code. Under the specification's opaque type
  (Overview) no constructor is user surface; that work is carried.

## Former section numbers

| Former | Now |
|---|---|
| §9 REPL introspection, §10 implementation checklist, §11 sketch references | Removed: delivered plan and retired prototype references (Git retains them) |
| §12 Rejected alternatives | §9, and the Overview for `Type::IO` |
