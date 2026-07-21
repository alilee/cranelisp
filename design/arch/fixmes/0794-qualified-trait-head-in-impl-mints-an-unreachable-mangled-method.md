---
number: 0794
target: /qa
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/traits/impl_check.rs:1029
  (mangle_trait_method(&impl_.trait_name.to_string(), …) — the AS-WRITTEN
  TraitRef Display) vs the dispatch-side mint and the backend resolved_target
  composition; spec/07-traits.md §7.3.
status: open
---

# `(impl mod/Trait Type …)` — a QUALIFIED trait head mints a mangled method nobody can call

## Severity
Important (spec-supported syntax; hard codegen error at the first call, not a
silent wrong answer; PRE-EXISTING — not introduced by S115 W6)

## Issue

Writing the `impl` head with the trait **qualified** produces a three-way name
mismatch and every dispatch through it fails codegen.

`check_impl_method` mints the method symbol from
`impl_.trait_name.to_string()` (`impl_check.rs:1029`), and `TraitRef`'s
`Display` (`crates/cranelisp-types/src/newtype.rs:160`) emits the **as-written**
qualification. So `(impl tlib/Show Widget (defn sh [x] 5))` defines
`tlib/Show.sh$user/Widget`, while the call site composes `Show.sh$user/Widget`
and the backend resolves it to `user/Show.sh$user/Widget`. (The default-method
synthesis path at `impl_check.rs:1127` uses `decl.name.as_ref()` — the BARE
trait name — so the two mints inside typecheck already disagree with each other
on this axis.)

## Repro (verbatim, HEAD `7a09e86b`, scratch cwd, `PrimitivesOnly` prelude)

`tlib.cl`: `(deftrait Show (sh [self] Int))`

REPL:
```
(import [tlib [Show sh]])
(deftype Widget (MkW [:Int n]))
(impl tlib/Show Widget (defn sh [x] 5))
(sh (MkW 0))
```
gives
```
impl tlib/Show for user/Widget
Error: codegen error at 0..12: codegen failed for /: codegen error at 0..12:
resolved_target 'user/Show.sh$user/Widget' for call 'Show.sh$user/Widget'
fetched no symbol-table entry (S110 W1 entry-miss; backend-keyed-consumer.md §1.3)
```

The **bare** head is fine — the identical program with `(impl Show Widget …)`
after `(import [tlib [Show sh]])` dispatches `:primitives/Int 5` and re-impls
cleanly to `9`.

## Proposed resolution

`/qa` attribution triage, then a `/testing` repro. The visible error is a
backend entry-miss but the root looks like the typecheck-side mint reading an
**as-written** `TraitRef` where every consumer reads a resolved identity — the
P24 "resolve once" class, and the same lossy-head family
`impl_check.rs`'s own S102 comments cite. The likely cure is to mint from the
trait's RESOLVED home (or its bare canonical name, matching the default-method
path), never from the syntactic `TraitRef`, and to make the two typecheck mints
agree by construction.

## Context

Found by `/review`(src) S115 W6 while probing the impl-redefinition fix's
cross-module boundary (the D45-amended writer/trait-home split). **Not caused by
`fab0b9ac`**: the FIRST impl already fails, and `derive_codegen_batch`'s
enrollment arm only affects a re-impl of an already-compiled `Def`. The W6 arm
derives its prefix from the same `impl_.trait_name` field the `:1029` mint uses,
so enrollment stays in lockstep with the (broken) mint — fixing the mint must
update the arm in the same change-set.
