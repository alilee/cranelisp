---
id: ACT-1072
title: The instantiation depth chain counts sibling members at one implementation instantiation when an earlier parameter has the implementing type's head
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/03-types.md §3.10
  - spec/07-traits.md §7.1.4
  - crates/cranelisp-typecheck/src/traits/monomorphise.rs::receiver_in
  - design/typecheck/monomorphisation.md §3.10.3
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` built from `24c42430`, 2026-11-18. No
prelude. Found by `review` of W3 from source.

A trait with members `m0` … `m64`, each declared
`(mI [:(Opt MI) d self] Int)` over 65 distinct nullary types `M0` … `M64`.
One `(impl Size (Opt a) …)` in which `mI` is `(m{I+1} Nope o)` and `m64` is
`7`. `main` is `(Pure (m0 Nope (Yep 3)))`. Required: 7. The program has one
implementation instantiation, at `(Opt Int)`.

| Leg | Observed |
|---|---|
| Subject, 65 members | refused: `type error: the instantiation of m64 … exceeds the instantiation depth limit of 64` |
| Boundary: 64 members | 7 |
| Control: 65 members, each declared `(mI [self :(Opt MI) d] Int)` | 7 |

## Classification: a defect (`wrong-reject`), introduced by S124 T4

Spec §3.10 counts a chain of implementation instantiations and sets a floor
of 64. Spec §7.1.4 admits an annotated parameter of any type. The subject is
refused at one instantiation.

## Attribution

- **Mechanism, read at its seam and consistent with every leg.**
  `receiver_in` takes the first type in the instance's signature whose head
  is the implementing type. With `(Opt MI)` before `self` each sibling gets
  its own counting identity, so each counts.
- **The control differs only in parameter order.**
- **No undercount was found.** A growing re-entry with a fixed
  `:(Opt Int)` parameter before `self` is still refused at depth 64, as its
  parameter-after-`self` twin is.
- `design`(typecheck) recorded the signature reading in
  `monomorphisation.md` §3.10.3 before this was observed; the design text
  follows the correction.

## Evidence allocation

- **`test`:** the subject, the 64-member boundary and the control in
  `tests/spec_07_traits.rs`, `--run`, `--link` and the REPL, generated as
  T-DEPTH's fixtures are. Cite `// spec: spec/03-types.md §3.10` and
  `// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/traits/monomorphise.rs::receiver_in found=S124 owner=/dev`.
- **`dev`(typecheck):** a module row in `successor_tests.rs` for two sibling
  members at one instantiation whose signatures differ in an earlier
  parameter with the implementing type's head.

## Completion evidence

The subject fails on the depth refusal before the correction and yields 7
after it, in every mode; the boundary and the control pass throughout.
