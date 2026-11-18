---
id: ACT-1076
title: A conventional trait method call selects its implementation from the first argument, not from the position of the implementing type
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/07-traits.md §7.1.1
  - spec/07-traits.md §7.1.4
  - crates/cranelisp-typecheck/src/traits/dispatch.rs::try_resolve_trait_method_decl
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on the debug build of `84719eb6`, 2026-11-18. Each program
ran with `--run --no-cache` in its own fresh directory, with no prelude and
`(import [primitives [*]])`. Reported by `dev`(typecheck); `design`(typecheck)
could not support the behaviour against the specification.

| Leg | Trait and implementations | Call | Required | Observed |
|---|---|---|---|---|
| Subject A | `(f [:Int d self] Int)`; `(impl T Bool …)` | `(f 1 true)` | 2 | refused: `no impl of trait user/T for type primitives/Int` |
| Control A | `(f [self :Int d] Int)`; `(impl T Bool …)` | `(f true 1)` | 2 | 2 |
| Subject B | Subject A plus `(impl T Int (defn f [d b] (add-i64 d 100)))` | `(f 1 true)` | 2 | 101: the `Int` implementation runs |
| Subject C | `(f [:String s self] Int)`; `(impl T Int …)` adds `n` to `(str-len s)`; `(impl T String …)` returns `(add-i64 100 (str-len n))` | `(f "abc" 2000)` | 2003 (exit 211) | signal 11 |
| Control C | The same two implementations with `self` first | `(f 2000 "abc")` | exit 211 | exit 211 |
| Subject D, the shape of §7.1.4's `map-val` | `(map-val [:(Fn [a] b) f x] self)`; `(impl Mappable Wrap …)` returns `x` | `(map-val inc (MkWrap 7))` | 7 | `codegen error: undefined function: map-val` |
| Control D | `(map-val [x :(Fn [a] b) f] self)` | `(map-val (MkWrap 7) inc)` | 7 | 7 |
| Subject E, the shape of §7.1.4's `convert` | `(convert [:String s] self)`; `(impl Convertible Int …)` returns `(str-len s)` | `(add-i64 (convert "abc") 1)` | 4 | refused: `no impl of trait user/Convertible for type primitives/String` |
| Declaration only | Subject A with `main` returning `(Pure 0)` | none | accepted | accepted |

- Subjects A, B and C give the same results under `--link` and at the REPL
  (the REPL leg of C ends the session on signal 11).
- The release build of 00:11 on 2026-11-18, before wave W3, gives the same
  results for A to D.

## Classification: a defect, memory-unsafe

- **Requirement.** Spec §7.1.4: an annotated parameter may have any type,
  and a bare parameter has the implementing type wherever it stands. Spec
  §7.1.1: the implementing type is substituted for `self` and for every bare
  parameter. The implementation a call selects is therefore the one for the
  type at the implementing-type position. Subjects D and E are the
  specification's own examples.
- **Faces.**
  - A legal program is refused (A, E).
  - A legal program is refused with a codegen error (D).
  - Another type's implementation runs with an argument of the wrong type:
    a wrong value (B), or a scalar read as a heap pointer (C).
- **Class:** `projection-mirror`. Implementation checking places the
  implementing type where the declaration puts it; call dispatch derives the
  position separately and takes index 0.
- **Not an S124 regression.** The index default in
  `try_resolve_trait_method_decl` dates from 2026-06-21 and 2026-09-09.

## Attribution

- **Mechanism, read at its seam.** `try_resolve_trait_method_decl` takes the
  dispatch argument at `hkt_param_index`, and for a conventional method that
  index defaults to 0. The type of argument 0 names the implementation. The
  return-type path is taken only when there is no argument at that index.
- **Controls differing only in the claimed cause.** Each control moves
  `self` to the first position and changes nothing else; each yields the
  required value.
- **Owner:** typecheck.
- **Refuted if** a method with `self` first selects the wrong
  implementation, or a method with `self` later selects the right one when
  its first argument's type has an implementation of the trait.
- **Why coverage missed it.** §7.1.4 carries no coverage annotation. Every
  committed cell with an annotated parameter before `self` gives that
  parameter a type whose head has an implementation of the trait. ACT-1072's
  fixture is one: its first argument is an `(Opt …)` and the implementation
  is for `(Opt a)`.
- **Not probed.** A method whose only occurrence of the implementing type is
  nested in an applied type (`:(Option self)`); a default method; an imported
  trait; a method called as a function value.

## Evidence allocation

`test`, in `tests/spec_07_traits.rs`, citing
`// spec: spec/07-traits.md §7.1.4` and
`// defect: class=projection-mirror locus=crates/cranelisp-typecheck/src/traits/dispatch.rs::try_resolve_trait_method_decl found=S124 owner=/dev`:

1. Subject C and control C in `--run`, `--link` and the REPL. The subject
   asserts exit 211 (the REPL leg, the value 2003).
2. Subject B and its `self`-first twin, every mode, value 2.
3. Subjects A, D and E with controls A and D, every mode. Each subject
   asserts its value and the absence of `no impl of trait` and
   `undefined function`.

`dev`(typecheck) owes a module row at the dispatch seam: two implementations,
the implementing type at index 1, the selected implementation asserted.

## Disposition

Subject C ends a legal program on a signal. Correcting it in S124 or
carrying it is the user's decision
([METHOD §2.5](../METHOD.md#25-mid-sprint-adjustment)). `qa` retains this
intake.

## Completion evidence

Each subject fails as tabled before the correction and yields its required
value after it, in every mode; the controls pass throughout. `qa` then reads
the "Not probed" shapes on the corrected tree and annotates §7.1.4.
