---
number: 0709
target: /qa
filed_by: /repl
filed_at: 2026-07-20
sprint_filed: 114
refers_to: spec/07-traits.md §7.11.2 (no-impl dispatch = located error naming the
  owning trait) — non-dispatchable-method corner of the F-D2-10 check-gate-leak family
status: open
---

# Non-dispatchable nullary trait method with no impl leaks to codegen "undefined function"

## Severity
Important (check-gate-leak class — the F-D2 family the S114 anchor drained)

## Issue

The S114 F-D2-10 work made no-impl trait-method calls produce a **located typecheck
error naming the owning trait**, verified working for the reachable shapes:
```
user> (deftype W [:Int w]) (deftrait Show (sh [x] Int)) (impl Show Int (defn sh [x] 1)) (sh (W 5))
Error: type error at ...: no impl of trait user/Show for type user/W          ; correct
user> (deftrait Zero (z [] self)) (defn g [] :primitives/Int (z))
Error: type error at ...: no impl of trait user/Zero for type primitives/Int   ; correct (nullary return-dispatch)
```

But a **non-dispatchable** trait method — nullary, no `self`, concrete return type
— with **no impl** leaks past the typecheck gate to a raw codegen error:
```
user> (deftrait Zeroable (zed [] Int))     ; accepted
user> (zed)
Error: codegen error at ...: codegen failed for /: codegen error at ...: undefined function: zed
```
`zed` has nothing to dispatch on (no argument, no `self`-typed return), so there is
no `(method, type)` pair for the no-impl check to key on; the call falls through to
codegen, which fails with an internal-sounding "undefined function: zed" instead of
a located typecheck error. This is the check-gate-leak SYMPTOM class the F-D2 anchor
fought — surviving in the degenerate corner.

Two candidate correct behaviours (a semantics question, hence /qa + /spec):
1. **`deftrait` rejects at declaration** — a trait method with no dispatch position
   (no `self`, no trait-parameter mention, concrete return) is non-dispatchable and
   arguably ill-formed; reject it where it is written, with a located error.
2. **The call is a located typecheck error** naming the trait (`no impl of trait
   user/Zeroable ...` / `zed has no dispatchable impl`), never a codegen
   "undefined function".

Either way the current outcome (opaque codegen error) violates §7.11.2's intent and
the self-documenting-REPL principle.

## Proposed resolution

`/qa` attributes (frontend deftrait validation vs typecheck no-impl gate) and rules
which of the two behaviours is correct (with `/spec` on whether a non-dispatchable
trait method is well-formed), then `/testing` lands a narrow failing repro per the
defect protocol. Minimal repro is the three-line transcript above.

## Context

`/repl` S114 Phase-6a assessment. The reachable F-D2 shapes are conformant; this is
the residual non-dispatchable-method corner.
