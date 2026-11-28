# IO typing

How `cranelisp-typecheck` types `IO`. Owned by `design` (typecheck).

## Overview

`IO` is typed as an ordinary defined type, `Type::ADT(primitives/IO, [a])`, with no
dedicated `Type` variant and **no constructors**. Effect tracking is standard
Hindley-Milner unification: no special inference rule, annotation or flag. This
crate owns the typing. `int`'s bootstrap seeds `IO` and the IO built-ins (`pure`,
`bind`, `select`, `sleep`), and validates `main`. The backend builds every IO node,
and the runtime evaluates them.

`spec/10-io.md` §10.1 makes `IO` opaque: the language has `(IO a)` and no
constructors for it, and `primitives/pure` (§10.2) is the public lift. Row IO-T
([opaque `IO`](../arch/interfaces.md#opaque-io-row-io-t)) realises opacity as
absence: `IO`'s constructor list is empty, and no table holds an `IO.*` key or a
bare `Pure`, `Effect` or `Bind`. Every user spelling of an `IO` constructor is
therefore undefined, through the ordinary resolution paths, none of which changes.
This crate keeps no IO-specific gate and no constructor flag.

- §1 constructors and opacity; §2 the `IO` type as seeded;
- §3 the nodes and who builds them; §4 `bind`; §5 `pure`;
- §6 `main`; §7 the rest of the type system; §8 platform operations;
- §9 rejected alternatives; §10 evidence and falsifiers.

**Status.** This crate's part of row IO-T is in source (S125): no constructor gate,
no `internal` flag, name-only exhaustiveness, and a constructorless fixture (§2).
`int`'s bootstrap (§2) and the backend's `pure` lowering (§5) complete the cascade;
defects 1105–1108 (cells in `tests/spec_10_io.rs`) close when it lands.

**A match on `IO` with no constructor arm** is refused by a general rule, not by an
`IO` rule. Spec §6.1 (S125-Q6) requires every `match` to have at least one
constructor-pattern arm, for every scrutinee type. No constructor of `IO` can be
written, so every `match` on `IO` is refused, with no IO-specific mechanism
(spec §10.1.1). The rule is scheduled for S126 and is not yet in source
([`typecheck.md` §12](typecheck.md#12-designed-changes-not-yet-in-source)). Until it
lands, `(match io [_ 0])` and `(match io [x x])` still type.

## 1. Constructors and opacity

Who may name a constructor is decided by visibility, through the one resolution chain
([Principle 24](../arch/principles/24-resolve-once.md)). Every constructor of a
`deftype` carries its type's visibility, and no constructor is marked internal:
`CallableOrigin::Ctor`, `AdtCtorSpec` and this crate's `CtorBuild` carry no such
flag. `infer.rs::infer_var` and `infer.rs::check_constructor_pattern` resolve a
constructor spelling with no gate ahead of the ordinary resolution.

`IO` needs no gate because there is nothing to gate. Each spelling reaches an
ordinary miss:

| Spelling | What it finds |
|---|---|
| Bare, imported or qualified `Pure`, `Effect`, `Bind` | No binding: an undefined name |
| Dotted `IO.Pure`, value or pattern | `IO` resolves; no `IO.Pure` key: a Miss ([dotted outcomes](dotted-ctor-registration.md#31-shared-core--checkerrsdotted_member_identity)) |
| Bare `(Pure x)` arm on an `IO` scrutinee | The scrutinee-picked step finds no `IO.Pure` key and falls through to the bare candidates, which are empty: "unknown constructor in pattern" |

A refusal reads as an ordinary unknown name. That matches spec §10.1, under which the
language has no `IO` constructor to name. A hint such as "use `pure`" was rejected,
because it would be a rule keyed on `IO`'s name (Principle 19).

### 1.1 Exhaustiveness

`crates/cranelisp-typecheck/src/adt.rs::check_exhaustiveness_in_module` covers every
constructor that `TypeDefInfo.constructors` lists, by name. The per-constructor probe
for a flag and its scope-resolve fallback are deleted. For `IO` the set is empty, so
every match on `IO` is exhaustive. No constructor arm can be written on an `IO`
scrutinee. The constructor-arm rule (S126, Overview) refuses such a match before
coverage matters.

## 2. The `IO` type as seeded

`src/bootstrap.rs::register_io_type` installs `IO` in `primitives` as a defined type
with one parameter `a` and an empty constructor list, like `Vec`. `IO` keeps its
parameter, so `(IO a)` unifies argument-wise as any parameterised ADT does.

This crate's unit fixture (`builtins.rs::with_io`, `FixtureContent::Io`) mirrors the
bootstrap. It seeds a constructorless `IO`, with `bind` and `pure` as host-promised
primitives. The fixture's `Pure` and `Effect` entries and its bind-constructor helper
are deleted, along with the fixture tests that read them. The fixture is a hand mirror
of `int`'s seed, as it is today, so a divergence shows only as a fixture test that
disagrees with an e2e cell.

## 3. IO nodes

Every IO node (`Pure`, `Effect`, bind, and the scheduler's kinds) is built by the
backend, the runtime or a platform, by tag (`cranelisp_platform::IO_TAG_*`). This
crate never names a node kind. A platform operation takes its `(IO a)` result type
from its manifest (§8). Each built-in takes its type from its primitive scheme (§4,
§5). Removing the `Effect` entry also removes its false scheme,
`∀a. (Fn [a] (IO a))` over a field that holds a thunk (defect 1106).

## 4. The `bind` primitive

```
bind :: ∀a b. (Fn [(IO a) (Fn [a] (IO b))] (IO b))
```

`src/bootstrap.rs::register_bind_primitive` installs `bind` in `primitives` as a
slot-less host-promised primitive; the backend lowers a call to it inline, allocating a
bind node. It has no special inference rule: application unifies the first argument
with `(IO a)` and the continuation with `(Fn [a] (IO b))`, so the continuation receives
the inner computation's value by ordinary unification.

## 5. `pure`

```
primitives/pure :: ∀a. (Fn [a] (IO a))
```

`pure` is a public host-promised primitive installed beside `bind`, and this crate
treats it exactly as it treats `bind`. Its type is its scheme. A call resolves to
`ResolvedCall::BuiltinFn`. It has no body, so it mints no instances and its typing
reads no constructor. It needs no rule here: typecheck keys nothing on `bind`'s name
either. The backend lowers it inline to the `Pure` node. Value use (spec §10.2.3) is
the backend's first-class wrapper for host-promised primitives.

Ownership inference classifies a `pure` call as `Summarised("pure")`
(`ownership/classify.rs`). Without a seeded summary, that reads as ⊤ (Decision 24).
⊤ is the treatment `(Pure e)` receives today as a pinned constructor boundary, so
the move keeps the conservative reference semantics
([Principle 25](../arch/principles/25-narrowing-carries-its-check.md)). A narrower
summary would be a narrowing, and would need its own check.

The standard library re-exports `primitives/pure`. It does not define a second
`pure` (Principle 07).

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

- **A `Type::IO` variant.** It would add a branch to every `match` on `Type` across
  all crates, while the ADT form already carries the one type argument inference
  needs. Opacity is a question of whether a constructor can be named, not of the
  type's representation.
- **Re-keying the internal-constructor gate on the resolved identity.** It would keep
  a flag and a gate beside visibility, the mirror class of Principle 24, and the
  false `Effect` scheme would stay.
- **A module-private `Pure` as `pure`'s typing carrier.** It needed a constructor-access
  mode, a member read that applies visibility, and an asserted staging-view residual,
  and it still listed `Pure` as a member of `IO`. A `pure` typed from its scheme, as
  `bind` is, needs no constructor (row IO-T, "Why not private constructors").
- **`bind` as a called function rather than inline.** It would add call overhead to
  every chain step. Inline lowering lets the backend manage the reference counts at
  the call site.

## 10. Evidence and falsifiers

The refusal is structural: no binding exists to resolve, in any module's committed or
staged view. The residual is a bootstrap that seeds an `IO` constructor again.
`design`(int) measures it in the bootstrap's unit tier, and this crate's fixture
mirrors the same shape. Leads for `qa`:

- **Each spelling, both positions.** A bare, imported, qualified (`primitives/Pure`,
  `primitives/IO.Pure`), dotted (`IO.Pure`) and scrutinee-picked `Pure`, `Effect` or
  `Bind` is refused in an expression and in a pattern. The control: a user
  `deftype`'s constructors still resolve in every spelling.
- **`pure`.** `(pure 1)`, a value use such as `(map pure xs)`, and a partial
  application each type and run. A typecheck unit test records `BuiltinFn` for a
  `pure` call against the fixture.
- **Exhaustiveness.** A user sum type passes with every arm covered and fails with one
  missing. These are the same cells as before. The deleted test that IO matching is
  exhaustive without `Bind` has no successor.
- **Defects 1105–1108.** Their cells in `tests/spec_10_io.rs` flip to green when the
  cascade lands.

## Former section numbers

| Former | Now |
|---|---|
| §9 REPL introspection, §10 implementation checklist, §11 sketch references | Removed (Git retains them); §10 is now Evidence and falsifiers |
| §12 Rejected alternatives | §9 |
