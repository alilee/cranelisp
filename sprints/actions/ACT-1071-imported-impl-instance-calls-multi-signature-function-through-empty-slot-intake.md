---
id: ACT-1071
title: An instance of an imported parametric implementation calls a multi-signature function through a slot that holds no function
status: open
priority: blocking
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/07-traits.md §7.3.3
  - spec/05-definitions.md §5.1.2
  - crates/cranelisp-typecheck/src/traits/monomorphise.rs::record_successor
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` built from `24c42430`, 2026-11-18. No
prelude. Found while probing the W3 review's redirect finding.

```clojure
;; h.cl
(import [primitives [*]])
(export [primitives [*]])
(deftype (Opt a) Nope (Yep [:a v]))
(deftrait Size (size [self] Int))
(impl Size Int (defn size [n] n))
(defn helper ([x] 7) ([x k] (add-i64 k 41)))
;; lib.cl
(import [h [*]])
(export [h [*]])
(impl Size (Opt :Size a) (defn size [o] (match o [Nope 0 (Yep x) (helper x 1)])))
;; p.cl
(import [lib [*]])
(defn main [] (Pure (size (Yep 41))))   ; required: 42
```

| Leg | Observed |
|---|---|
| Subject, `--run` | signal 11: a call through a slot holding 0 |
| Subject, REPL (`(import [lib [*]])`, then `(size (Yep 41))`) | signal 11 |
| Subject, `--link` | 42 |
| Control: `helper` with one signature, `(defn helper [x k] …)` | 42 in `--run`, `--link` and the REPL |
| Control: the `impl` in `p.cl` instead of `lib.cl` | 42 |
| Variant: `helper`'s body dispatches `(size x)`, in its own module beside a `base.cl` | signal 11 under `--run` and the REPL; 42 under `--link` (the committed cell, `f775478e` and `8667a868`) |
| The variant with a back-edge, `(helper (if false o Nope) 0)` | signal 11 under `--run` and the REPL; `--link` is refused before the system linker: `cannot link: the object pass for \`lib\` stopped at its object` (since `79a8c94c`; see *Attribution*) |

## Classification: a defect, memory-unsafe; a mode divergence

A legal program jumps to address 0 under `--run` and the REPL and yields its
value under `--link`.

## Attribution: provisional

- **Predates S124 W3.** `target/release/cranelisp` built at 00:11 on
  2026-11-18, before T1, ends the subject on signal 11 and passes both
  controls.
- **W3 widened its reach.** The dispatching variant was refused before T4
  with `undefined function` (ACT-1034) and now reaches the fault.
- **Observed:** the instance is emitted in the importing module `p` and its
  call goes through the library module's slot table.
- **Hypothesis, from `review`'s reading:** the multi-signature callee's
  instance is recorded under the library module while it is installed in the
  importing module (`record_successor` and the overload drain under an
  imported recheck). Not observed at that seam. `dev`(typecheck) probes
  before implementing; if typecheck publishes the importing module's key,
  the attribution returns to `qa` for the backend and `src/`.
- **Observed at the object pass, back-edge variant under `--link`**
  (`qa`, `79a8c94c`). The pass for `lib` cannot compile the instance
  `lib/(h/helper [(base/Opt Int) Int] Int)`: its call carries the resolved
  target `lib/(lib/Size.size$base/Opt [(base/Opt Int)] Int)`, and `lib`'s
  symbol table holds no such entry. A target is published under the
  library module for an instance that is not installed there, which is
  what the hypothesis above predicts for this variant. Before `79a8c94c`
  the pass stopped without a report, the link went on without `lib.o`,
  and the system linker failed on `__cranelisp_got_lib`; that linker error
  was a consequence, not a second defect. The subject and the dispatching
  variant still link and give 42, so this observation is of the back-edge
  variant only. Under `--run` and the REPL the process ends on the signal
  before the pass reports.
- **`review`'s back-edge redirect is not separated from this defect.** Every
  shape that reaches the overload drain under an imported recheck fails this
  way first. The back-edge variant is a leg of this filing's cell.
- **Why coverage missed it:** no cell calls a multi-signature function from
  an implementation defined in an imported module.

## Evidence allocation

`test`, in `tests/spec_07_traits.rs`, citing
`// spec: spec/07-traits.md §7.3.3` and
`// defect: class=null-got-slot locus=crates/cranelisp-typecheck/src/traits/monomorphise.rs::record_successor found=S124 owner=/dev`
(locus provisional):

- the subject in `--run`, `--link` and the REPL, value 42;
- the dispatching variant and its back-edge twin, every mode;
- both controls, every mode.

`dev`(typecheck) owes a module row at the seam its probe names.
`successor_tests.rs::template_references` cannot serve: it passes a target
that names no table entry.

## Completion evidence

Each subject leg fails by signal, or by the link's refusal, before the correction
and yields its value after it in every mode; the controls pass throughout.
