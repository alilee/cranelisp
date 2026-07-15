---
number: 0614
target: /stdlib
filed_by: /qa
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S111 (uninvoked module; the ergonomic path depends on FIXME 0613)
refers_to: SG-1 attribution, LAYER 2 — `stdlib/derive.cl` is structurally
  nonconforming to spec §9.3.4 and stays broken even after the layer-1
  quasiquote defect (FIXME 0613) is fixed. Attribution record
  `tests/plan/s110-attribution-sg1-sg2.md`.
status: open
---

# derive.cl violates §9.3.4 — its macros reference ~30 same-module `defn-` helpers

## The violation

`derive-Eq` / `derive-Ord` / `derive-Display` / `derive`
(`stdlib/derive.cl:243/340/387/393`) all call private helpers defined in the
SAME module (`slength`, `snth`, `smap`, the `dt-*` introspectors, the
`build-*` template builders — ~30 functions). Spec §9.3.4: "A macro's
expansion MUST NOT reference a same-module non-macro definition … a macro
that needs a helper MUST place that helper in a dependency module."

**Enforcement verified on HEAD** (2026-07-15, probe: dependency module with
`(defn- helper …)` + `(defmacro m [x] (helper x))`, invoked cross-module):

```
type error … undefined variable: helper — macro expansion may not reference
same-module non-macro definitions; define `helper` in a dependency module
(or import it)
```

So once FIXME 0613 lands (quasiquote-in-`defn-` desugaring), derive.cl will
STILL fail — at this diagnostic instead. The SG-1 gate
(`tests/stdlib_conformance.rs`) stays RED on `derive` until BOTH layers land.

## Restructure options (owner's call)

1. **Helpers → dependency module** (e.g. fold into `core.syntax` or a new
   sibling) — keeps the quasiquote templates, so this path is **blocked-by
   0613**. Spec §9.4 (the `core.syntax` note) already anticipates exactly
   this shape.
2. **Raw-ctor rewrite in place** — replace the ~15 quasiquote templates with
   explicit `SexpList`/`SCons` construction (the module already does this in
   half its helpers). Unblocked today, but does not cure the §9.3.4
   violation — the helpers must STILL move out of the module. So option 1's
   move is needed regardless; option 2 only decides whether the moved helpers
   wait for 0613.

## Also fix the stale S87 tail comment

`derive.cl:405–421` attributes the S87 `(mod test)` failure to "same-module
macro rejection … the quasiquote-bearing expansion never runs and the raw
template leaks to the parser". That mechanism claim is wrong: an unexpanded
`(derive …)` call contains no quasiquote. The actual first failure is the
layer-1 parse error at line 166 (byte 5306) — the module never compiles AT
ALL, invocation or not, and there is no evidence it ever compiled on the v4
pipeline. Correct the comment during the restructure.

## Closure

The SG-1 gate going green on `derive` is the failing-test record for this
defect (no separate narrow repro owed — the gate discriminates per module).
Consumer-side derive-invocation coverage (actually calling
`(derive [Eq Ord Display] (deftype …))` from a downstream module) is the
0605 tier-2 follow-on, sized separately.
