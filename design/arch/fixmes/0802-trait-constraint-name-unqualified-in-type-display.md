---
number: 0802
target: /qa
filed_by: /repl
filed_at: 2026-07-21
sprint_filed: 115
refers_to: repl/spec.md §1.4 "Constrained variable | `:core.numerics/Num a`"
  and its `[Tested tests/repl_negative::display_neg_type_always_qualified]`
  annotation; §1.4's worked example `:(Fn [:core.numerics/Num a :a] a)
  core.numerics/+`
status: open
---

# Trait names in constraint position display unqualified (`:Num a`) where §1.4 pins the fully-qualified form — and the row is annotated `[Tested]`

## Issue

`repl/spec.md` §1.4 carries a `Constrained variable` row whose normative display
is `:core.numerics/Num a`, a worked example reading
`:(Fn [:core.numerics/Num a :a] a) core.numerics/+`, and the flat requirement
*"Type names MUST always be fully qualified with their module path."* Probed at
HEAD (2026-07-21):

```
user> +
:(Fn [:Num a :Num a] a) num.num/+ ; defn

user> (defn addi [x y z] (+ x (+ y z)))
:(Fn [:Num a :Num a :Num a] a) user/addi ; defn

user> (deftrait Sizeable (size [x] Int))
user> (impl Sizeable Shape (defn size [s] 12))
user> /sig size
:(Fn [:Sizeable a] primitives/Int) user/size ; defn
```

Two independent deviations from the row:

1. **The constraint's trait name is bare** — `:Num a`, `:Sizeable a` — in both
   the prelude-trait and user-trait cases. The *subject* name is correctly
   qualified in the same line (`num.num/+`, `user/size`), so this is specific to
   the constraint position, not a general qualification failure.
2. **The spec's module path is stale prose** — `core.numerics` no longer exists;
   the operator's real home is `num.num`. That half is `/repl`'s to fix and it
   will land in the Phase-6b spec pass regardless of the ruling below.

## The question for `/qa` — which side is wrong

This is a genuine two-sided call, not a defect report:

- **If the display is wrong**, §1.4 is clear and the fix is at the type-renderer
  seam. Note that a bare trait name is genuinely ambiguous once two modules
  declare a same-named trait, which is the argument the "always qualified"
  principle rests on everywhere else.
- **If the spec is wrong**, then a constraint carries a *trait* name, not a
  *type* name, and §1.4's "type names MUST always be fully qualified" never
  reached it; the terse `:Num a` is then a deliberate readability choice for the
  most common line in the REPL and the spec row should say so.

`/repl` owns the requirement prose either way but will not rule on it alone: the
row is currently annotated `[Tested
tests/repl_negative::display_neg_type_always_qualified]`, which asserts coverage
that the probe contradicts. **The coverage claim is the part `/qa` must settle
first** — either that test does not exercise the constraint position (a
traceability gap on a `[Tested]` row, the standing coverage-by-definition-variants
category: `{primitive, ADT, fn, type var, constrained var}` × `{qualified,
bare}`), or it does and passes, in which case the annotation and the row
disagree about what the row says.

## Proposed resolution

1. `/qa` reads `display_neg_type_always_qualified` and reports which of the six
   §1.4 rows it actually covers; correct the annotation band accordingly (that
   band is `/qa`'s to edit in place).
2. Route the qualified-vs-bare constraint question for a ruling — spec-prose
   change (`/repl` scribes) or renderer change (attributed by `/qa`).
3. `/repl` fixes the stale `core.numerics` → `num.num` prose in Phase 6b
   independently; it is not gated on 1 or 2.

## Context

Found by `/repl` during the S115 Phase-6a delta-surface probe — the
impl-redefinition beat renders `/sig size` on a user trait, which is what put a
user-defined constraint name beside a qualified subject name on the same line
and made the asymmetry visible. Long-standing, low-severity, but it sits on a
`[Tested]` row, which is the reason it is filed rather than absorbed.
