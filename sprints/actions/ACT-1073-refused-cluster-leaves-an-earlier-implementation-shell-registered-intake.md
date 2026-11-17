---
id: ACT-1073
title: A refused cluster leaves an earlier implementation of the cluster registered without its methods
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/05-definitions.md §5.4.5
  - repl/spec/18-redefinition.md §18.7
  - crates/cranelisp-typecheck/src/traits/impl_check.rs::check_pending_trait_impls
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` built from `24c42430`, 2026-11-18. No
prelude. Found by `review` of W3 from source, for an imported trait.

```clojure
(deftype A MkA)
(deftype B MkB)
(deftrait Size (size [self] Int))
(begin (impl Size A (defn size [x] 1))
       (impl Size B (defn size [x] "bad")))   ; refused: type mismatch, as required
(size MkA)
```

| Leg | Observed |
|---|---|
| Subject, `(size MkA)` after the refused `begin` | a `codegen error`: the resolved target of the call to `size` at `A` "fetched no symbol-table entry" |
| The same with the types and trait imported from a module | the same codegen error |
| After the refusal, `(impl Size B (defn size [x] 2))` | accepted, with `Warning: failed to save …/user.cl: no recorded source for Size.A; the file keeps its previous content` (local trait) |
| After the refusal, `(impl Size A (defn size [x] 5))`, then `(size MkA)` | 5 |
| Control: `(size MkA)` with no `impl Size A` entered | a type error: no impl of the trait |

## Classification: a defect

A refused input changes nothing (spec §5.4.5; REPL §18.7). Here the session
reports `A` as implementing `Size`, fails at codegen, and stops saving the
session file until `A` is implemented again.

## Attribution

- **Predates S124 W3, and is wider than reviewed.** `target/release/cranelisp`
  built at 00:11 on 2026-11-18, before T1, gives the same codegen error with
  the trait local and with it imported. The save warning was read on the
  current build only.
- **Locus, a source reading:** each implementation's shell is committed as
  its bodies pass; a later failure in the cluster restores the failing
  implementation and the ones after it, not the ones before.
  Class `partial-record-update`. Owner typecheck, provisional: `dev` probes
  whether the cluster's rollback is `src/`'s to drive.
- **Why coverage missed it:** the refusal rows enter one implementation per
  cluster. The module row `impl_body_dispatch_with_no_impl_in_cluster_is_still_refused`
  (`crates/cranelisp-typecheck/src/traits/impl_check/tests.rs`)
  states "the refused implementation is not left visible" and asserts the
  message only.

## Evidence allocation

- **`test`:** in `tests/spec_05_definitions.rs`, citing
  `// spec: spec/05-definitions.md §5.4.5` and
  `// defect: class=partial-record-update locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::check_pending_trait_impls found=S124 owner=/dev`.
  The REPL subject with the trait local and imported: after the refused
  `begin`, `(size MkA)` is a type error and not a codegen error, and a
  following definition saves with no warning. The same pair of
  implementations in a file under `--run` and `--link` is refused once, with
  the second implementation's error (control, green today).
- **`dev`(typecheck):** a module row: two implementations in one cluster,
  the first conforming and the second refused, leave no shell, method or
  written record for the first.

## Completion evidence

The subject fails on the codegen error before the correction and reports the
type error after it; the save warning is gone; the control passes throughout.
